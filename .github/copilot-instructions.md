
# When working on shift/reset

---
applyTo: 'UecInLean/shift_reset/'
---

The user is working on implementing shift/reset control operators in Lean.
When assisting with code related to this topic, please keep the following guidelines in mind:

## 1. Understand the Domain
There are pdfs, called "Asai2011" and "Ishio2022", which explain shift/reset and their implementation in Agda.
You cannot refer another files except above two PDF and UecInLean/shift_reset/Basic.lean .


## 2. Instructions
### a. "What is the purpose of ..." question
When the user asks about the purpose of a specific function, theorem, or construct related to shift/reset, you should:
1. Refer to the relevant sections in the "Asai2011" and "Ishio2022" PDFs to understand the theoretical background.
2. Explain the purpose in the context of shift/reset control operators, ensuring clarity and conciseness.
3. If you can, you may provide the TYPE of the function, theorem, or construct to give additional context, with clear reasons.

### b. "Complete implementation of the ..." task
When the user asks to complete the implementation of a specific function or feature related to shift/reset, you should think through the following steps:
1. Review the existing code in UecInLean/shift_reset/Basic.lean to understand the current state of the implementation.
2. Refer to the relevant sections in the "Asai2011" and "Ishio2022" PDFs to understand the theoretical background and expected behavior of the feature.
3. You should not search the file; you can ask the user for the relative content of the feature.
4. Try to fill up the missing parts of the code, up to 3 line.
5. If you miss the context, need more information, or the task is too complex, politely ask the user for clarification or additional details before proceeding.
6. Ensure that the code adheres to Lean's syntax and conventions, and is consistent with the existing codebase.
