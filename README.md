# Treap implementation and verification in Dafny

This project aims to implement and verify a treap data structure using Dafny programming language. Treap data structure is a randomized binary search tree that maintains both binary search tree and heap properties. Our implementation supports several methods, including build, insert, delete, search, split, and merge. We aim to rigorously verify the correctness of our implementation using formal verification techniques provided by Dafny.

---

## Installation

This project uses Dafny version `4.0.*`. You may find errors when attempting to run the program using older versions. For convenience, we recommend using Visual Studio Code as we can easily change Dafny versions. To do so, we will need to have the following software installed on our machine:

- [Visual Studio Code](https://code.visualstudio.com/)
- [Dafny extension for Visual Studio Code](https://marketplace.visualstudio.com/items?itemName=correctnessLab.dafny-vscode)

After installing Dafny extension, please ensure that the following configurations are set in the extension settings:

- Dafny version: `4.0.*`
- Verification time limit: 120 seconds or more*

To configure these, open Visual Studio Code settings (press `Ctrl` + `,` for Windows or `Command` + `,` for Mac), search for `Dafny`, and update the settings as required. To change the verification time limit, we may need to configure that in `settings.json` file. To open the file, press `Ctrl` / `Command` + `shift` + `P` and search using keyword `Open User Settings`. We can now append the time limit in the file as follows.
```json
{
    ...
    "dafny.verificationTimeLimit": 120
}
```

We need to restart VS Code after reconfiguration. Once we have installed the required software and configured the Dafny extension settings, we must have no problem to run the project in Visual Studio Code.

***IMPORTANT**: Verification time limit may vary depending on the computer. However, the cuprits of the long verification time are `SplitNode` and `MergeNode` method. They have more properties to verify such that Dafny requires more time. Without these two methods, Dafny can verify the whole program in less than 20 seconds (default). Having said that, two minutes should be enough as Dafny can verify the program within 60 seconds based on our attempts. You may want to comment them out for your convenience or let Dafny finish its task without time constraints.

---

## Usage

All implementations of Treap Data Structure are available in `Treap.dfy` file. A sample main method is provided at the end of the file, which demonstrates example usages of the implemented methods. You are free to edit this function to test out the behavior of the methods and customize the treap data structure to your needs.

Additionally, we have provided two static methods, `InorderTraversal(TreapNode)` and `PreorderTraversal(TreapNode)`, which can be used to print the inorder and preorder traversal of a given TreapNode, respectively. These methods can be used at any time to visualize the structure of the treap and aid in debugging.

To run the sample main method or any other Dafny program in this project, simply open the `Treap.dfy` file in Visual Studio Code, (press `Ctrl` / `Command` + `Shift` + `P`), and select `Dafny: Run`

---

## Project Status

This project was last updated on 21/4/2023 and is not planned to receive any future updates. The currently implemented and verified methods include:

- `Build`
- `Insert`
- `Delete`
- `Search`
- `Split`
- `Merge`

**NOTES**: We provided a demo for `Merge` implementation in `Main` method. However, we currently comment it out because Dafny takes very long time to verify the `Main` method with `Merge` test in it. We were not successful to run the program with the following test even after providing 5 minutes duration for verification.
```JavaScript
print "------- Merge -------\n";
print "Left Tree: {17, 4, 3, 11, 35}\n";
print "Right Tree: {75, 38, 93, 54, 92}\n";
var arr1 := new int[5][17, 4, 3, 11, 35];
var arr2 := new int[5][75, 38, 93, 54, 92];
var tree1 := Treap.Build(arr1);
var tree2 := Treap.Build(arr2);
var merged := Treap.Merge(tree1, tree2);

print "In Order Traversal\n";
Treap.InOrderTraversal(merged.root);
print "Pre Order Traversal\n";
Treap.PreOrderTraversal(merged.root);
print "---------------------\n";
```
