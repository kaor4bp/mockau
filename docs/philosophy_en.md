![MINOW logo](logo.png)

# MINOW
## A Smart Router for Functional Testing

Minow is a smart router designed to solve one of the key problems of functional testing: **the instability and unpredictability of external services**. It helps you manage load restrictions and easily reproduce rare, elusive errors, such as 429 (Too Many Requests) or other unexpected situations.

Minow doesn't replace your code; it helps you orchestrate your test scenarios by providing precise and controlled data at the right moment.

---

## 🎯 The Minow Philosophy

Our philosophy is simple: **mocking is nice, but orchestration wins.**

Minow ensures the stability and predictability of external services during testing, saving you from writing complex and unreliable stubs. It allows you to **reproduce specific behaviors** of third-party systems that are nearly impossible to replicate in real conditions, for example, getting a 429 error on the second request or a 500 after a series of successful ones.

Minow is a **smart router with storage**, not a data generator. We believe your data should be prepared in advance, and our job is to deliver it efficiently and reliably to the right place.

### What Minow does:
✅ Stores your test data in an isolated space
✅ Extracts keys and variables from incoming requests
✅ Routes requests based on your data
✅ Transforms requests and responses
✅ **Allows you to reproduce unexpected situations and errors**

### What Minow does NOT do:
❌ Does not generate complex data
❌ Does not implement business logic
❌ Does not perform complex calculations
❌ Does not replace your code

---

## ⚙️ Architectural Principles

Minow is designed with principles of simplicity and predictability in mind.

### Linear Pipeline
Request processing is broken down into sequential stages, eliminating circular dependencies. Variables created in one stage can only be used in subsequent ones, creating a one-way data flow.

### Linear Order of Variable Computation
A variable can only reference variables that have been declared above it in the configuration. This simple rule guarantees there are no loops.

### Principle of Minimum Sufficiency
Each function performs exactly one task. We don't add features "just in case"—only those that solve real testing problems.

---

## 🚀 Key Advantages

### Predictability
Thanks to the linear architecture, the system's behavior can always be predicted. There are no hidden dependencies or unexpected side effects, and **your tests become stable and independent of external factors**.

### Debugging Simplicity
The linear processing flow makes diagnosing problems a trivial task. You know exactly **why and how a particular response was returned**, even if it was a rare case.

### Simplicity and Scalability
Configurations remain readable and manageable as projects grow. New team members quickly understand the system thanks to its simple and consistent principles.

---

## 🎪 The Orchestration Philosophy

Think of testing as a symphony orchestra:
- **Your code** is the musicians.
- **External services** are the other sections of the orchestra.
- **Minow** is the conductor who ensures all parts interact correctly.

The conductor doesn't play the instruments, but a cohesive performance is impossible without them. Similarly, Minow doesn't replace your code but ensures all components interact correctly during testing.

---

## 🔄 Request Lifecycle

1. **Reception** -> Minow receives a request from your application.
2. **Analysis** -> It extracts key data.
3. **Decision** -> It determines the appropriate route.
4. **Transformation** -> It modifies the request or response as needed.
5. **Delivery** -> It returns the prepared data.

---

## 🎯 Mission

To build a convenient tool for QA Automation. Period. No pretense of saving the world.

We aren't revolutionizing the industry. We're simply solving a specific technical problem: how to make your functional tests run predictably and ensure their maintenance doesn't become a nightmare. Minow just does its job well and stays out of your way.