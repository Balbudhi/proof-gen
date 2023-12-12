import mathlib.tactic
import Aesop


noncomputable section
open Classical

/-
In Tarski's geometric system, the hierarchy of types involves three main levels:

Individuals (Type 0): This level includes basic geometric objects such as points, lines, and planes. Individuals are entities that can be referred to by specific names or variables.

Regions (Type 1): This level introduces entities that can be thought of as collections of individuals. A region might represent a set of points or a portion of a line or plane.

Relations (Type 2): This level involves relationships between regions. Relations can describe properties such as incidence or betweenness. They involve more complex combinations of individuals and regions.
-/

@[ext]
structure Point : Type where
  x : ℝ
  y : ℝ

structure Segment: Type := (p1 p2 : Point)
infixl:56  "⬝" => Segment.mk

-- Equidistance relation
structure equidistance (s1 s2 : Segment) : Prop
infixl:55  " ≃ " => equidistance

-- Betweenness relation
structure Betweenness (a b c : Point) : Prop

-- TODO ADD 2D COORDINATES

-- TARKSKI'S AXIOMS (https://proofwiki.org/wiki/Axiom:Tarski%27s_Axioms)

-- Axiom 1: Reflexivity Axiom for Equidistance
@[aesop unsafe 50% apply, symm] axiom axiom_one (a b : Point) : a⬝b ≃ b⬝a

-- Axiom 2: Transitivity Axiom for Equidistance
@[aesop unsafe 50% apply, trans] axiom axiom_two (a b p q r s: Point) : (a⬝b ≃ p⬝q) → (a⬝b ≃ r⬝s) → (p⬝q ≃ r⬝s)

-- Axiom 3: Identity Axiom for Equidistance
@[aesop unsafe 50% apply, symm] axiom axiom_three (a b c : Point) : (a⬝b ≃ c⬝c) → a = b

-- Axiom 4: Axiom of Segment Construction
@[aesop unsafe 50% apply] axiom axiom_four (a b c q : Point) : ∃ (x : Point), (Betweenness q a x) ∧ (a⬝x ≃ b⬝c)

-- Axiom 5: Five-Segment Axiom
@[aesop unsafe 50% apply] axiom axiom_five (a b c d a' b' c' d' : Point) : ¬(a = b) ∧ ((Betweenness a b c) ∧ (Betweenness a' b' c')) ∧ ((a⬝b ≃ a'⬝b') ∧ (b⬝c ≃ b'⬝c') ∧ (a⬝d ≃ a'⬝d') ∧ (b⬝d ≃ b'⬝d')) → (c⬝d ≃ c'⬝d')

-- Axiom 6: Identity Axiom for Betweenness
@[aesop unsafe 50% apply, symm] axiom axiom_six (a b : Point) : Betweenness a b a → a = b

-- Axiom 7 : Pasch Axiom
@[aesop unsafe 50% apply] axiom axiom_seven (a b c p q : Point) : ∃ (x : Point), (Betweenness a p c) ∧ (Betweenness b q c) → (Betweenness p x b ∧ Betweenness q x a)

-- Axiom 8: Lower 2-Dimensional Axioms
@[aesop unsafe 50% apply] axiom axiom_eight (a b c : Point) : (¬ Betweenness a b c ) ∧ (¬ Betweenness b c a) ∧ (¬ Betweenness c a b)

-- Axiom 9: Upper 2-Dimensional Axioms
@[aesop unsafe 50% apply] axiom axiom_nine (a b c p1 p2: Point) : ¬(p1 = p2) ∧ (a⬝p1 ≃ a⬝p2) ∧ (b⬝p1 ≃ b⬝p2) ∧ (c⬝p1 ≃ c⬝p2) → (Betweenness a b c ) ∨ (Betweenness b c a) ∨ (Betweenness c a b)

-- Axiom 10: Euclid's Axiom
@[aesop unsafe 50% apply] axiom axiom_ten (a b c d t : Point) : ∃ (x y : Point), (Betweenness a d t) ∧ (Betweenness b d c) ∧ ¬(a = d) → Betweenness a b x ∧ Betweenness a c y ∧ Betweenness x t y

-- Axiom 11: Axiom of Continuity
def separates (X Y : Set Point) (a : Point) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, Betweenness a x y

@[aesop unsafe 50% apply] axiom axiom_eleven (X Y : Set Point) (a : Point):
  separates X Y a → ∃ b : Point, ∀ x ∈ X, ∀ y ∈ Y, Betweenness x b y

-- Axiom 12: Reflexivity Axiom for Betweenness
@[aesop unsafe 50% apply] axiom axiom_twelve_a (a b : Point) :  Betweenness a b b
@[aesop unsafe 50% apply] axiom axiom_twelve_b (a b : Point) :  Betweenness a a b
@[aesop unsafe 50% apply] axiom axiom_twelve_c (a b : Point) :  Betweenness b b a
@[aesop unsafe 50% apply] axiom axiom_twelve_D (a b : Point) :  Betweenness b a a

-- Axiom 13: Unnamed
@[aesop unsafe 50% apply, symm] axiom axiom_thirteen (a b : Point) :  a = b → Betweenness a b a

-- Axiom 14: Symmetry Axiom for Betweenness
@[aesop unsafe 50% apply, symm] axiom axiom_fourteen (a b c : Point) :  Betweenness a b c → Betweenness c b a

-- Axiom 15: Inner Transitivity Axiom for Betweenness
@[aesop unsafe 50% apply, trans] axiom axiom_fifteen (a b c d : Point) :  Betweenness a b d → Betweenness b c d → Betweenness a b c

-- Axiom 16: Outer Transitivity Axiom for Betweenness
@[aesop unsafe 50% apply, trans] axiom axiom_sixteen (a b c d : Point) :  Betweenness a b c → Betweenness b c d ∧ ¬(b=c) → Betweenness a b d

-- Axiom 17: Inner Connectivity Axiom for Betweenness
@[aesop unsafe 50% apply] axiom axiom_seventeen (a b c d : Point) :  Betweenness a b d ∧ Betweenness a c d → (Betweenness a b c ∨ Betweenness a c b)

-- Axiom 18: Outer Connectivity Axiom for Betweenness
@[aesop unsafe 50% apply] axiom axiom_eighteen (a b c d : Point) :  Betweenness a b c ∧ Betweenness a b d ∧ ¬(a=b) → (Betweenness a c d ∨ Betweenness a d c)

-- Axiom 19: Unnamed
@[aesop unsafe 50% apply] axiom axiom_nineteen (a b c : Point) : a = b → a⬝c ≃ b⬝c

-- Axiom 20 : Uniqueness Axiom for Triangle Construction
@[aesop unsafe 50% apply] axiom axiom_twenty (a b c c' d : Point) : ¬(a = b) ∧ (a⬝c ≃ a⬝c') ∧ (b⬝c ≃ b⬝c') ∧ (Betweenness b d c') ∧ ((Betweenness a d c) ∨ (Betweenness a c d)) → c = c'

-- Axiom 21: Existence Axiom for Triangle Construction
@[aesop unsafe 50% apply] axiom axiom_twenty_one (a a' b b' c' p : Point) : a⬝b ≃ a'⬝b' → ∃ (c x : Point), ((a⬝c ≃ a'⬝c') ∧ (b⬝c ≃ b'⬝c') ∧ (Betweenness c x p)) ∧ ((Betweenness a b x) ∨ (Betweenness b x a) ∨ (Betweenness x a b))

-- Axiom 22: Density Axiom for Betweenness
@[aesop unsafe 50% apply] axiom axiom_twenty_two (a b : Point) : ¬(a = b) → ∃ (c : Point), ¬(c = a) ∧ ¬(c = b) ∧ Betweenness a c b

-- -- Axiom 23: Unnamed
@[aesop unsafe 50% apply] axiom axiom_twenty_three (x y z x' y' z' : Point) : ((Betweenness x y z) ∧ (Betweenness x' y' z') ∧ (x⬝y ≃ x'⬝y') ∧ (y⬝z ≃ y'⬝z')) → (x⬝z ≃ x'⬝z')



set_option trace.aesop true


-- Testing Axioms:
theorem transitivity_of_betweenness (a b c d : Point)
  : Betweenness a b c → Betweenness b c d → b ≠ c → Betweenness a b d :=
by
  intro a_1 a_2 a_3
  simp_all only [ne_eq]
  apply axiom_sixteen
  exact a_1
  simp_all only [not_false_eq_true, and_self]
  -- aesop?

theorem symmetry_of_betweenness (a b c : Point) : Betweenness a b c → Betweenness c b a :=
  λ h => axiom_fourteen a b c h


-- Using the Axiom of Continuity in a proof
example (X Y : Set Point) (a : Point) (h : separates X Y a) : ∃ b : Point, ∀ x ∈ X, ∀ y ∈ Y, Betweenness x b y :=
  axiom_eleven X Y a h


-- Generating shapes
structure Circle : Type := (c : Point) (r : ℝ)

structure Triangle : Type := (a b c : Point)

structure Rectangle : Type := (a b c d : Point)

@[aesop unsafe 50% apply] axiom rectangle_def (r : Rectangle) : ¬(r.a = r.b) ∧ ¬(r.a = r.c) ∧ ¬(r.a = r.d) ∧ ¬(r.b = r.c) ∧ ¬(r.b = r.d) ∧ ¬(r.c = r.d)

@[aesop unsafe 50% apply] axiom triangle_def (t : Triangle) : ¬(t.a = t.b) ∧ ¬(t.a = t.c) ∧ ¬(t.b = t.c)

-- Expanstion of axiom 1
@[aesop unsafe 50% apply, symm] axiom segment_order_commute (a b : Point) : a⬝b = b⬝a
@[aesop unsafe 50% apply] axiom equidistance_order_commute_a (a b c d: Point) : (a⬝b ≃ c⬝d) → (a⬝b ≃ d⬝c)
@[aesop unsafe 50% apply] axiom equidistance_order_commute_b (a b c d: Point) : (a⬝b ≃ c⬝d) → (b⬝a ≃ c⬝d)
@[aesop unsafe 50% apply] axiom equidistance_order_commute_c (a b c d: Point) : (a⬝b ≃ c⬝d) → (b⬝a ≃ d⬝c)


--  ¬(p1 = p2) ∧ (a⬝p1 ≃ a⬝p2) ∧ (b⬝p1 ≃ b⬝p2) ∧ (c⬝p1 ≃ c⬝p2) → (Betweenness a b c ) ∨ (Betweenness b c a) ∨ (Betweenness c a b)

set_option maxRecDepth 100000

theorem bisect_triangle (t1 t2 t3 : Triangle) :
  t1.a ≠ t1.b → t2.a ≠ t2.b → t3.a ≠ t3.b → t1.a = t2.a → t1.a = t3.a → t1.b = t2.b → t1.b = t3.b → t1.a⬝t1.c ≃ t1.b⬝t1.c → t1.a⬝t2.c ≃ t1.b⬝t2.c → t1.a⬝t3.c ≃ t1.b⬝t3.c
   → (Betweenness t1.c t2.c t3.c ∨ Betweenness t2.c t3.c t1.c ∨ Betweenness t3.c t1.c t2.c) :=
by
  aesop?
  (options := { maxRuleApplications := 1000 })
