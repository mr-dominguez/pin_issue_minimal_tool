#include <execinfo.h>
#include <stdio.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <iostream>
#include <random>
#include <string>
#include <utility>
#include <fstream>
#include <vector>
#include <cmath>
#include <set>
#if defined(TARGET_MAC)
#include <sys/syscall.h>
#else
#include <syscall.h>
#endif

#include "pin.H"

#define ADDRESS_SIZE 4

std::ofstream Logfile;
std::string logfile_name = "/home/log";
std::string filename = "/mnt/pmem0/copy";
ADDRINT alloc_size;
bool found_alloc = false;
int mmap_count = 1; // from previous experience we need the second instrumented mmap so we count them
int merkle_tree_depth = 8;

std::string simulateHash(const std::string& input) {
    return input.substr(0, 4);
}

struct MerkleNode {
    MerkleNode* left = nullptr;
    MerkleNode* right = nullptr;
    std::string hash;

    MerkleNode(std::string hash)
        : hash(hash) {}
};

class MerkleTree {
    private:
        int _blockSize = 1000;
        int _maxDepth = 8;
        MerkleNode* _root = nullptr;
        long unsigned int _currentMappingStartAddress;
        int _currentMappingSize;

        std::vector<std::string> readAllBlocksFromFile(const std::string& filename) {
            std::vector<std::string> blocks;
            std::ifstream file(filename, std::ios::binary);

            // Round up the number of blocks to account for possible incomplete last block
            int numBlocks = std::pow(2, _maxDepth);

            // Read the file in chunks and store them as blocks
            for (int blockNumber = 0; blockNumber < numBlocks; blockNumber++) {
                int remainingSize = static_cast<int>(_currentMappingSize - file.tellg());
                int currentBlockSize = std::min(_blockSize, remainingSize);
                std::string block(currentBlockSize, '\0'); // Initialize a string with null characters
                file.read(&block[0], currentBlockSize);
                blocks.push_back(simulateHash(block));
            }

            file.close();
            return blocks;
        }

        std::vector<std::string> readBlocksFromFile(const std::string& filename, std::set<int> blockNumbers) {
            std::vector<std::string> hashes;
            std::ifstream file(filename, std::ios::binary);

            if (!_currentMappingSize)
                _currentMappingSize = 10000; // ignore, just hot fix for minimal test!

            for (int blockNumber : blockNumbers) {
                // Calculate the offset to read the specific block
                std::streampos offset = static_cast<std::streampos>(_blockSize) * blockNumber;

                // Determine the actual block size to read (might be smaller for the last block)
                int actualBlockSize = _blockSize;
                int offsetInt = _blockSize * blockNumber;
                if (offsetInt + _blockSize > _currentMappingSize) {
                    actualBlockSize = static_cast<int>(_currentMappingSize - offsetInt);
                }

                // Read the block from the file into memory and save its hash
                std::string block(std::string(actualBlockSize, '\0'));
                file.seekg(offset, std::ios::beg);
                file.read(&block[0], actualBlockSize);
                hashes.push_back(simulateHash(block));
            }
            file.close();

            return hashes;
        }

        void buildTree(const std::string& filePath) {
            std::vector<MerkleNode*> nodes;
    
            // Create leaf nodes
            for (std::string blockHash : readAllBlocksFromFile(filePath)) {
                MerkleNode* node = new MerkleNode(blockHash);
                nodes.push_back(node);
            }
            
            // Build the tree from leaf nodes
            while (nodes.size() > 1) {
                std::vector<MerkleNode*> parents;
                for (size_t i = 0; i < nodes.size(); i += 2) {
                    MerkleNode* left = nodes[i];
                    MerkleNode* right = (i + 1 < nodes.size()) ? nodes[i + 1] : nullptr;
                    std::string data = left->hash + (right ? right->hash : "");
                    MerkleNode* parent = new MerkleNode(simulateHash(data));
                    parent->left = left;
                    parent->right = right;
                    parents.push_back(parent);
                }
                nodes = parents;
            }
        
            _root = nodes[0];
        }

        MerkleNode* findBlockNode(int blockNumber, int currentDepth) {
            MerkleNode* current = _root;
            while (currentDepth != _maxDepth && current) {
                // Get the bit at the current depth
                int bit = (blockNumber >> (_maxDepth - currentDepth - 1)) & 1; 
                if (!bit) 
                    current = current->left;
                else 
                    current = current->right;
                currentDepth++;
            }
            return current;
        }

        MerkleNode* findSiblingNode(int blockNumber, int currentDepth) {
            MerkleNode* current = _root;
            int bit;
            while (currentDepth != _maxDepth && current) {
                // Return sibling if we're at the previous depth
                if (currentDepth == _maxDepth - 1) {
                    bit = (blockNumber >> (_maxDepth - currentDepth - 1)) & 1;
                    if (!bit)
                        return current->right;
                    else
                        return current->left;
                }
                // Get the bit at the current depth
                bit = (blockNumber >> (_maxDepth - currentDepth - 1)) & 1; 
                if (!bit) 
                    current = current->left;
                else 
                    current = current->right;
                currentDepth++;
            }
            return current;
        }

        std::vector<int> intToBits(int num, int N) {
            std::vector<int> bits(N, 0); // Initialize the vector with N zeros

            for (int i = 0; i < N; ++i) {
                bits[i] = num & 1; // Extract the least significant bit and store it in the vector
                num >>= 1; // Right-shift num to move to the next bit
            }

            return bits;
        }

        void updateTree(int blockNumber, std::string leafHash) {
            // Update leaf node hash
            MerkleNode* leafNode = findBlockNode(blockNumber, 0);
            leafNode->hash = leafHash;

            std::vector<int> bits = intToBits(blockNumber, _maxDepth);
            MerkleNode* previousNode = leafNode;
            MerkleNode* siblingNode;

            // Go upperwards from leaf node, updating each node's hash in the merkle path
            for (int i = 1; i <= _maxDepth; i++) {
                MerkleNode* parent = findBlockNode(blockNumber, i);
                siblingNode = findSiblingNode(blockNumber, i-1);

                // Check bit at corresponding depth to hash in the correct order => hash(childLeft + childRight)
                if (!bits.at(i-1))
                    parent->hash = simulateHash(previousNode->hash + siblingNode->hash);
                else
                    parent->hash = simulateHash(siblingNode->hash + previousNode->hash);

                previousNode = parent;
            }
        }

        bool isAddressInNextBlock(long unsigned int address, int blockNumber) {
            int nextBlockStart = _currentMappingStartAddress + _blockSize * (blockNumber + 1) ;
            int distance = nextBlockStart - address;
            
            return (distance < ADDRESS_SIZE && distance > 0);
        }

    public:
        void freeMerkleTree(MerkleNode* node) {
            if (!node) 
                return;
            
            // Recursively free left and right subtrees
            freeMerkleTree(node->left);
            freeMerkleTree(node->right);

            // Free the current node
            delete node;
        }

        // Change mapping each time we intercept a mmap instruction
        void setNewMapping(long unsigned int startAddress, int sizeBytes, int treeDepth) {
            _currentMappingStartAddress = startAddress;
            _currentMappingSize = sizeBytes;
            _maxDepth = treeDepth;
            int numBlocks = std::pow(2, _maxDepth);
            int remainder = (sizeBytes / numBlocks) % ADDRESS_SIZE;
            if (remainder == 0)
                _blockSize = (sizeBytes / numBlocks);
            else {
                _blockSize = (sizeBytes / numBlocks) + ADDRESS_SIZE - remainder; // ensures better memory alignment
                while (_blockSize * numBlocks < sizeBytes)
                    _blockSize += ADDRESS_SIZE;
            }
            freeMerkleTree(_root);
            _root = nullptr;
        }


        std::string applyChange(const std::string& filename, std::vector<long unsigned int> addresses) {

            if (!_root) {
                buildTree(filename);
                return _root->hash;
            }

            // 1. Calculate and get set of block numbers
            std::set<int> blockNumbers;
            if (_currentMappingStartAddress) {
                for (long unsigned int addr : addresses) {
                    int blockNumber = (addr - _currentMappingStartAddress) / _blockSize;
                    blockNumbers.insert(blockNumber);
                    // Check if address overflows into next block
                    if (isAddressInNextBlock(addr, blockNumber))
                        blockNumbers.insert(blockNumber+1);
                }
            } else { // ignore, just hot fix for minimal test!
                blockNumbers.insert(1);
            }

            // 2. For each block, compute its hash
            std::vector<std::string> hashes = readBlocksFromFile(filename, blockNumbers);

            // 3. Compute root hash
            int size = blockNumbers.size();
            auto it = blockNumbers.begin();
            for (int i=0; i<size; i++, it++)
                updateTree(*it, hashes.at(i));

            return _root->hash;
        }
};

MerkleTree _merkleTree;

void FPWriteHandler(ADDRINT address, uint32_t size, CONTEXT *ctxt) {
    _merkleTree.applyChange(filename, {address});
}

VOID InstrumentStores(INS ins, VOID *v) {
    if (INS_IsMemoryWrite(ins)) {
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)FPWriteHandler,
                       IARG_MEMORYWRITE_EA, IARG_MEMORYWRITE_SIZE,
                       IARG_CONST_CONTEXT, IARG_END);
    }
}

VOID SysBefore(ADDRINT ip, ADDRINT num, ADDRINT size, ADDRINT flags,
               ADDRINT fd) {
    if (num == SYS_mmap &&
        (((flags & 0x01) == 0x01) || ((flags & 0x03) == 0x03))) {
        alloc_size = size;
        found_alloc = true;
    }
}

// Save the returned memory address for each allocation
VOID SysAfter(ADDRINT return_value) {
    if (found_alloc == true) {
        if (mmap_count == 2) {
            _merkleTree.setNewMapping(return_value, alloc_size, merkle_tree_depth);
        }
        mmap_count++;
        found_alloc = false;
    }
}

VOID SyscallEntry(THREADID thread, CONTEXT *ctxt, SYSCALL_STANDARD std,
                  VOID *v) {
    SysBefore(PIN_GetContextReg(ctxt, REG_INST_PTR),
              PIN_GetSyscallNumber(ctxt, std),
              PIN_GetSyscallArgument(ctxt, std, 1),
              PIN_GetSyscallArgument(ctxt, std, 3),
              PIN_GetSyscallArgument(ctxt, std, 4));
}

VOID SyscallExit(THREADID thread, CONTEXT *ctxt, SYSCALL_STANDARD std,
                 VOID *v) {
    SysAfter(PIN_GetSyscallReturn(ctxt, std));
}

static int rand_value = 0;
// Wrapper function for the rand() function to a set a constant value
int RandWrapper() { return ++rand_value; }

// Instrumentation of the image, consisting of the routines
VOID ReplaceNonDeterministicRoutines(IMG img, VOID *v) {
    RTN rand_rtn = RTN_FindByName(img, "rand");
    if (RTN_Valid(rand_rtn)) {
        RTN_ReplaceSignature(rand_rtn, AFUNPTR(RandWrapper), IARG_END);
    }
}

int main(int argc, char *argv[]) {
    PIN_InitSymbols();
    PIN_Init(argc, argv);

    INS_AddInstrumentFunction(InstrumentStores, 0);
    PIN_AddSyscallEntryFunction(SyscallEntry, 0);
    PIN_AddSyscallExitFunction(SyscallExit, 0);
    IMG_AddInstrumentFunction(ReplaceNonDeterministicRoutines, 0);

    PIN_StartProgram();
    return 0;
}
