**Analysis**

**Lecture 1 (Abbot 1.2, 1.3, 1.4):**

  * **Preliminaries** on Real numbers
  * **The Axiom of Completeness** and its consequences, e.g. Archimedean Property, Nested Interval Property
  * **Upper and lower bounds**, supremum (sup), infimum (inf) and their properties
  * **The absolute value** and its properties, including triangle and reverse triangle inequalities

**Tutorial 1**

  * Explain in your own words what is an axiom. How does it differ from a theorem? What axioms have you used in previous courses (perhaps without realizing it)?
  * Why do we need to introduce the Axiom Of Completeness? Come up with some examples of sets of rational numbers for which this axiom does not hold, can you show that it does not hold?
  * Let \\(A \subseteq \mathbb{R}\\) bounded and let \\(s\\) be an upper bound of \\(A\\). In class we proved \\(s = \sup A\\) if and only if \\(\forall \epsilon >0,\; \exists a \in A\\) such that \\(s-\epsilon < a\\). Show that this is also equivalent to \\(\forall \epsilon >0,\; \exists a \in A\\) such that \\(s-\epsilon \leq a\\) (with 'less or equal').

**Lecture 2 (Abbott 2.2, 2.3):**

  * **Motivation of limits through Newton's method:** Introducing the concept of limits using the iterative process of Newton's root-finding method.
  * **Sequences** defined as functions with domain N, and examples.
  * **Limits of Sequences** using ε-neighborhoods. Examples of limit calculations.
  * **Standard Limits** used frequently in analysis.
  * **Divergent Sequences:** Definition of a divergent sequence and how to prove divergence.
  * **Bounded Sequences:** Definition of a bounded sequence, and the theorem that a convergent sequence is bounded (but not vice versa). Examples.
  * **Algebraic Properties of Limits.**
  * **Order Properties of Limits**.

**Tutorial 2**

  * Explain in your own words (and without looking at them) the two definitions of limit of a sequence that we gave in class. Use these explanations to reconstruct (without looking at them) the two definitions in formal mathematical language. Did you get the same statement? If not, is it equivalent to one of those statements? (try to prove it or to find a counterexample)
  * Work together to show, using the definiton, that given a,b,c,d natural numbers, the sequence with elements (a n +b)/(c n + d) converges to a/c.
  * How can you modify the proof to show the convergence of (6x + 5)/(3x - 1)?
  * What are some common patterns or behaviors that indicate a sequence is divergent?
  * Consider a sequence that is dense in some interval (a,b). Can this sequence converge? Can it be the full interval? _Hint: what is the cardinality of the interval? And of the set of elements of the sequence?___

**Lecture 3 (Abbott 2.4, 2.5):**

  * **Monotone Sequences:** Definition of increasing and decreasing sequences, and examples.
  * **Monotone Convergence Theorem:** Any bounded monotone sequence converges.
  * **Subsequences:** Definition of a subsequence, properties and examples.
  * **Bolzano-Weierstrass Theorem:** Every bounded sequence has a convergent subsequence; with proof using a halving process and the nested interval property.
  * **Introduction to Infinite Series:** Definition of infinite series, partial sums, and convergence of a series based on the limit of the partial sums.
  * **Euler's Example:** Illustration of the convergence of Σ(1/k²).
  * **The Harmonic Series:** Proof of the divergence of the harmonic series Σ(1/k).
  * **The Integral Test for Convergence** and examples illustrating its application.

**Tutorial 3**

  * What is the Bolzano-Weierstrass Theorem, and why is it significant in the study of sequences?
  * Can you walk through the proof of the theorem using the halving process and the nested interval property?
  * How do a sequence differ from a series?
  * How can we study divergence or convergence of an infinite series only knowing theorems about sequences?

**Lecture 4 (Abbot 2.6, 2.7):**

  * **Cauchy criterion**: Definition and properties of Cauchy sequences
  * **Properties of infinite series**: Convergence criteria, geometric series, telescoping series, and some of their applications

**Tutorial 4**

  * What is the relationship between the Cauchy criterion and the definition of convergence of a sequence? Can you prove that they are equivalent?
  * How does the convergence of a series relate to the convergence of its sequence of partial sums? Can you provide a proof?

**Lecture 5 (Abbot 3.2):**

  * **Open sets and their properties**: Definition of open sets, examples of open and non-open sets, unions and intersections of open sets
  * **Closed sets and their properties**: Relationship between open and closed sets, and limits of sequences, complements of open and closed sets
  * **Unions and intersections**: Properties of unions and intersections of open/closed sets

**Tutorial 5**

  * What is the relationship between the closure of a set and its complement? Can you describe the closure of an open set and a closed set?
  * Can you think of a situation where the intersection of infinitely many open sets is not open?
  * Can you provide an example of a set that is neither open nor closed? What are its properties?

**Lecture 6 (Abbott §3.3):**

  * **Compact sets:** Sequential definition, characterization as closed and bounded, examples, and counterexamples
  * Nested Interval Property (NIP) and its generalization to compact sets
  * **Open covers:** Definition, examples, and the characterization of compact sets using open covers
  * **Heine-Borel Theorem:** Equivalence of compactness, closed and bounded sets, and sets with finite subcovers for any open cover

**Tutorial 6**

  * What alternative characterizations of compact sets can you remember? Make bounded and unbounded examples of non-compact sets, and check how the characterizations fail.
  * What is an open cover? What is the relation between an open cover and a compact set?
  * At some point, to discuss what happens as we cover \\([0,1]\\) and explain the last proof, I (Marcello) wrote on the board the family of open sets \\(O_n = (-1, \frac{n}{n+1})\\). However at some point I started using it (incorrectly!) as a cover for the set. Let’s use this question to fix the mishap: s_how that the family of \\(O_n\\) is an open cover for \\((0,1)\\) and for \\([0, 1)\\) but it can _**_not_**_ be an open cover for \\([0,1]\\). How can you make it a open cover for \\([0,1]\\)? _This is the whole point of the theorem we were trying to prove: any cover of a compact set must have a finite subcover :)

**Lecture 7 (Abbott §4.2, §4.3):**

  * **Limits of functions**: ϵ and δ definition, examples, and sequential characterization
  * **Continuity**: ϵ and δ definition, examples, and sequential characterization
  * Algebraic properties of limits
  * **Special functions**: Dirichlet's function, Modified Dirichlet's function, and Thomae's function, and their properties

**Tutorial 7**

  * How do we define the limit of a function using sequences?
  * Can you reconstruct the epsilon-delta definition by reasoning from the above definition?
  * Use this to recover the epsilon-delta definition of continuity.
  * Can you give an example of a function discontinuous at all points? What is Thomae's function and what about it is peculiar?

**Lecture 8 (Abbott §4.4, §4.5)**:

  * **Continuity and compactness**: compact sets and continuous functions, maxima and minima
  * **Uniform continuity**
  * **Intermediate Value Theorem**: Statement, proof, and examples of its application

**Tutorial 8**

  * What is the difference between a continuous function and a uniformly continuous one? Can you provide an example and an example of continuous but non uniformly continuous function?
  * What is the intermediate value theorem about? Can you find a function and an interval where the Intermediate Value Theorem does not hold? Explain why.

**Lecture 9 (Abbott §5.2, §5.3, §5.4)**:

  * **Derivatives**: definition, differentiability vs continuity, Interior extremum theorem and Darboux' theorem
  * **Mean Value Theorem**: Rolle's theorem, Mean Value Theorem, and applications
  * **Pathological example**: a continuous, nowhere differentiable function

**Tutorial 9**

  * What is differentiability? Why is it a stronger condition than continuity?
  * Can you recover the statements of the various intermediate value theorems that we saw in the lectures by describing their meanings? Try it in group

**Lecture 10 (Abbott §6.2):**

  * **Pointwise convergence**
  * **Uniform convergence**
  * **Convergence types**: characterizations and examples
  * **Preservation of continuity** under uniform convergence

**Tutorial 10**

  * Explain in your own words the meaning of pointwise and uniform convergence and how they differ.
  * Does uniform convergence imply pointwise convergence? Does pointwise convergence imply uniform convergence? Justify the statement with a proof or a counterexample.
  * How does continuity behave in the limit? Provide an example of a sequence of continuous functions that converges pointwise to a discontinuous function. Can you find a different example than the one in the lecture?

**Lecture 11 (Abbott §6.3, §6.4):**

  * **Uniform convergence** reprise: Cauchy criterion, **preservation of differentiability**
  * **Series of functions**: Cauchy criterion, Weierstrass test, and **preservation of continuity and differentiability**

**Tutorial 11**

  * Under what conditions does the uniform convergence of a sequence of differentiable functions imply that the limit function is differentiable?
  * Provide an example of a sequence of differentiable functions that converges uniformly to a function that is not differentiable.
  * How do all these concepts extend to series? Provide an example of a series of continuous functions that converges uniformly to a continuous function

**Lecture 12 (Abbott §6.5):**

  * **Power Series**: general form and convergence
  * **Pointwise Convergence**: theorem and proof, including the comparison test
  * **Radius of Convergence**: definition, methods for computing (root test, ratio test), and examples
  * **Uniform Convergence**: theorem and proof, continuity of the limit
  * **Summation by Parts** and **Abel's Lemma**
  * **Abel's Theorem**: uniform convergence on intervals
  * **Differentiation**: term-by-term differentiation of power series

**Tutorial 12**

  * Explain in your own words the difference between pointwise and uniform convergence. How are they related? Justify your answers with examples and couterexamples
  * Under what conditions can we differentiate a power series term-by-term? Can you provide an example to illustrate this?
  * Show that \\(nc^n\\) with \\(|c| < 1\\) is bounded

**Lecture 13 (Abbott §6.6):**

  * **Taylor Series**: definition, Taylor's formula, and convergence to functions
  * **Lagrange Remainder**: definition, lemma, theorem, and proof
  * **Examples and a counter example**: a function whose Taylor series does not converge to the function
  * **Approximating Square Roots and Integrals**: using Taylor series and remainder terms

**Tutorial 13**

  * Can you prove L'Hopital rule using Taylor series? What more do you get from using Taylor series?
  * Can you provide an example of a function whose Taylor series does not converge to the function itself? What are the implications of this?

**Lecture 14 (Abbott §7.2, §7.3):**

  * **Partitions and refinements**
  * **Riemann Integral**: definition with lower and upper sums, criterion for integrability
  * **Continuous Functions**: proof of integrability
  * **Integrals of Discontinuous Functions**: examples of integrable and non-integrable functions

**Tutorial 14**

  * How does refining a partition affect the lower and upper sums?
  * How does the definition of Riemann integral done in class relate to the one you saw in Calculus 1?
  * Can you provide examples of discontinuous functions that are integrable and others that are not? What characteristics make a discontinuous function non-integrable?

**Lecture 15 (Abbott §7.4, §7.5):**

  * **Split, Algebraic and Order Properties** of Riemann integrals
  * **Fundamental Theorem of Calculus**:
    * Part 1: proof and example
    * Part 2: proof, uniform continuity, and differentiability at points of continuity

**Tutorial 15**

  * Name 3 takeaway messages of the analysis course and compare them with the ones from the other members of the group.
  * Name at least a memorable thing from the course and compare it with the ones from the other members of the group.
  * What did you find the hardest topic in the course was? Compare your answers in the group.
  * What are the statements that appear in the Fundamental Theorem of Calculus?
  * What happens if the function integrated is discontinuous?
