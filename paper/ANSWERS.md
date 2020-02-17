Hello,

Type is a property of data, and *type flattening* aims to protect this property from to be reversed.

Beside type, data has also other properties (e.g. layout, size, concrete values). Some obfuscation techniques are already used to protect these properties, a very concrete example is hiding a string "You win " in a crackme, we may xor the characters of the string with some value, this technique is for protecting **values** of data.

Type flattening is a new because there are currently no research on protecting types of data.

MBA is proposed initially (in the paper of Zhou et al.) to hide **constants** (i.e. data values) from static analysis (and algorithms from dynamic analysis). It was not proposed to protect data types.

Actually, MBA is a general technique which can be used for other purposes. For example, MBA can be used also to generate opaque predicates, and then it's useful for control flow obfuscation.

Similarly, type flattening obfuscation uses MBA to generate pointer aliases, and then to hide data flow which is essential in binary type inference algorithms. But type flattening is not MBA, it can use other techniques for its purpose (i.e. hiding data type).

Concretely, in the implemented code, there are more than MBA. You may see the function `split_and_merge` (in `FunctionTranslator` implementation) which is used to obfuscate data flow, or function `create_entry_block` which is used to create a trampoline to hide data size.

Moreover, while MBA has been proposed since long time but as far as I known, there is no open source code obfuscation projects implements it (Tigress uses a very simple variant of MBA). In `uCc` the algorithm of Zhou et al. is implemented completely.
