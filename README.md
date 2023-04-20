# Treap implementation and verification in Dafny

This project aims to implement and verify a treap data structure using the Dafny programming language. The treap data structure is a randomized binary search tree that maintains both the binary search tree property and the heap property. Our implementation supports several methods, including build, insert, delete, search, split, and merge. We aim to rigorously verify the correctness of our implementation using formal verification techniques provided by Dafny.

---

## Installation

To use this project, you will need to have the following software installed on your machine:

- [Visual Studio Code](https://code.visualstudio.com/)
- [Dafny extension for Visual Studio Code](https://marketplace.visualstudio.com/items?itemName=correctnessLab.dafny-vscode)

Before using the Dafny extension, please ensure that you have set the extension settings as follows:

- Dafny version: 4.0.0
- Verification time limit: 120 seconds

To configure these settings, open the Visual Studio Code settings (press `Ctrl` + `,`), search for "Dafny", and update the settings as required.

Once you have installed the required software and configured the Dafny extension settings, you can clone this repository and open the project in Visual Studio Code to get started.

---

## Usage

To use this project, you can explore and modify the provided implementation of the treap data structure in the `Treap.dfy` file. A sample main method is provided at the end of the file, which demonstrates example usages of the implemented methods. You are free to edit this function to test out the behavior of the methods and customize the treap data structure to your needs.

Additionally, we have provided two static methods, `InorderTraversal(TreapNode)` and `PreorderTraversal(TreapNode)`, which can be used to print the inorder and preorder traversal of a given TreapNode, respectively. These methods can be used at any time to visualize the structure of the treap and aid in debugging.

To run the sample main method or any other Dafny program in this project, simply open the `Treap.dfy` file in Visual Studio Code, (press `Ctrl` + `Shift` + `P`), and select "Dafny: Run"

---

## Project Status

This project was last updated on 21/4/2023 and is not planned to receive any future updates. The currently implemented and verified methods include:

- build
- insert
- delete
- search
- split
- merge

There is a known issue with the merge method, which cannot be called in the main method due to a potential violation of the context modifies clause. Future work is needed to address this issue.
