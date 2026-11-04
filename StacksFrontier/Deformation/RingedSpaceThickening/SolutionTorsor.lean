module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationDiagram
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentLiftingObstruction

/-!
# Torsor formalism for isomorphism classes of deformations (towards Stacks 08UC)

Fix a first order thickening `t : S ⟶ S'` with ideal `𝒥`, a morphism `f : X ⟶ S`, an
`𝒪_X`-module `𝒢` and a map `c : f^* t^* 𝒥 ⟶ 𝒢`. A *solution* of the deformation problem
(91.7.0.1) is a `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution t ht f G c`, and
**Stacks 08UC** says that if a solution exists then the set of isomorphism classes of solutions
is principal homogeneous under `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)`.

**This file does not prove that tag and does not claim it**; the tag is proved in
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionClasses.lean`
(`AlgebraicGeometry.RingedSpaceThickening.solutionClassesAddTorsor`), which builds the two
inputs below and feeds them to `SolutionObstruction.addTorsor`. It supplies the torsor *formalism*
the tag needs, on top of two inputs which are themselves the assertion of the tag and are
therefore hypotheses here: the obstruction class `o(X'₁, X'₂)` of **Stacks 08U8** as a *cocycle*
in a pair of solutions, and the construction, for a solution `X'` and a class `ξ`, of a second
solution `X'_ξ` with `o(X', X'_ξ) = ξ`. "Principal homogeneous" means precisely that there is an
`Ext¹`-valued difference of any two solutions and that it is realized by an action, so assuming
the two is assuming the two halves of 08UC. They are bundled as the fields of
`SolutionObstruction`; the implementation notes list them and the further prerequisites, and say
which are genuinely separate tags' content.

What *is* proved here, from those inputs, is everything else: the vanishing of a cocycle
obstruction is an equivalence relation on solutions — the isomorphism relation, by
**Stacks 08U8**, clause (1), which is applied as a theorem — isomorphism classes are a real
`Quotient` of it, the construction `X' ↦ X'_ξ` descends to that quotient, and the resulting
action is simply transitive. The source's "if there exists a solution" is the `Nonempty` field
of Mathlib's `AddTorsor`.

The missing mathematics that this formalism will be fed, when it exists, is the pushout of a
square-zero extension of a sheaf of rings along a map of modules, together with the sheaf
`𝒪_{S'}[ℰ]` and its ideals; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.SolutionObstruction`: the obstruction data of the
  source's proof — a cocycle `o` of obstruction classes on a type of solutions, and the
  construction `X' ↦ X'_ξ` realizing every class as an obstruction.
* `SolutionObstruction.setoid`: isomorphism of solutions, as the vanishing of the obstruction
  class, and `SolutionObstruction.IsomorphismClasses`, the set of isomorphism classes.
* `SolutionObstruction.vaddClass` and `SolutionObstruction.vsubClass`: the action of
  `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` on isomorphism classes, and the class separating two of them.
* `SolutionObstruction.addTorsor`: the principal homogeneous space structure on isomorphism
  classes, as Mathlib's `AddTorsor`.
* `AlgebraicGeometry.RingedSpaceThickening.liftingObstructionSolution`: the obstruction data
  assembled from the class of **Stacks 08U8**, so that the acting group is literally
  `Ext¹(NL(α), 𝒢)`.
* `AlgebraicGeometry.RingedSpaceThickening.deformationSolutionAddTorsor`: the same, specialized
  to the solutions `DeformationSolution` of the problem (91.7.0.1) itself.

## Main results

* `SolutionObstruction.isoClass_eq_isoClass_iff`: the obstruction class separates the
  isomorphism classes of solutions.
* `SolutionObstruction.zero_vaddClass`, `SolutionObstruction.add_vaddClass`: the action is an
  action.
* `SolutionObstruction.existsUnique_vaddClass`: the action is simply transitive — any
  isomorphism class is carried to any other by exactly one class in `Ext¹`.
* `AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_add`: the class of **Stacks 08U8**
  is additive in the conormal homomorphism it is the class of, which is what makes the
  obstruction a cocycle.
* `AlgebraicGeometry.RingedSpaceThickening.setoid_iff_nonempty_lift` and
  `AlgebraicGeometry.RingedSpaceThickening.isoClass_eq_isoClass_iff_nonempty_lift`: through
  **Stacks 08U8**, clause (1), the equivalence relation used here is the existence of a morphism
  between the two solutions fitting into the source's diagram.

## Implementation notes

`Ext¹(X, 𝒢)` is the group `X ⟶ 𝒢⟦1⟧` of the ambient triangulated category, as in
`StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentLiftingObstruction`.

Isomorphism classes are a genuine `Quotient`: the setoid is `fun Q₁ Q₂ => o Q₁ Q₂ = 0`, whose
reflexivity, symmetry and transitivity are proved from the cocycle identity, and the action is
`Quotient.liftOn` of the construction `X' ↦ X'_ξ` together with a proof that it respects the
relation. No representative is ever chosen: that is why the construction is a field of
`SolutionObstruction` and not the content of an existence statement — the source exhibits
`X'_ξ`, and an existence statement would need choice to act on a class at all.

Two of the carried inputs are the assertion of **Stacks 08UC** itself, which is why the tag is
not claimed on anything in this file.

* The obstruction class and its cocycle identity, as the fields `o` and `o_add` of
  `SolutionObstruction`. Step 1 of the proof of **Stacks 08U8** builds the class as the class of
  a difference of two restrictions `ℐ' ⟶ 𝒢` of algebra maps out of the sheaf of polynomial
  algebras `𝒪_{S'}[ℰ]`, and the cocycle identity is the additivity of that difference. Both
  objects do exist in the library — `𝒪_{S'}[ℰ]` is
  `Stacks.Sites.FreeAlgebra.freeAlgebraSheaf` and `ℐ'/(ℐ')²` is
  `Stacks.Sites.Conormal.conormalSheaf` of the generators presentation — and so does the
  difference and its additivity:
  `AlgebraicGeometry.RingedSpaceThickening.PresentedSquareZeroExtension.obstruction` and
  `PresentedSquareZeroExtension.obstruction_add_obstruction` of
  `StacksFrontier/Deformation/RingedSpaceThickening/ExtensionPresentationClass.lean`. What they
  need, and what is missing here, is that the two extensions be presented over **one shared,
  prescribed** family of generators: the obstruction there is the descent of the difference of
  two restriction data for the *same* `generatorsPresentation`, whereas a pair of solutions in
  the sense of this file arrives with no common presentation. Producing one is **Stacks 08UB**
  followed by **Stacks 08TL**, which is the gap recorded two bullets below. So the class as a
  function of an arbitrary pair of solutions, and its additivity, are still carried; **Stacks
  08U8** as formalized takes the conormal homomorphism as an input too. An `Ext¹`-valued
  difference of two solutions is one half of "principal homogeneous", so this is part of the tag.
* The construction `X' ↦ X'_ξ`, as the fields `twist` and `o_twist`. It is the pushout of the
  square-zero extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` along `ψ = φ|_{ℐ'} + δ ∘ (ℐ' ⟶ ℐ/ℐ²)`,
  and `o_twist` is the source's "a calculation (omitted)". The library has only the *trivial*
  square-zero extension `𝒪 ⋉ 𝒩` of `StacksFrontier.Topology.Sheaves.Modules.SquareZeroExtension`,
  a direct sum; the pushout of a square-zero extension of a sheaf of rings along a map of
  modules does not exist in it. Realizing every class as a difference is the other half of
  "principal homogeneous", so this too is part of the tag.

The remaining carried inputs are separate tags' content, carried the way the library already
carries them.

* The two-term structure of `NL(α)`, as the distinguished triangle in the field `distinguished`
  of `NaiveCotangentTwoTerm`. Inherited from **Stacks 08U8**: the library builds `NL(α)` with
  `HomologicalComplex.double`, which nothing relates to its two terms by a triangle.
* Surjectivity of `Hom(ℐ/ℐ², 𝒢) ⟶ Ext¹(NL(α), 𝒢)`, as the hypothesis `rep` of
  `liftingObstructionSolution`. This is **Stacks 08UB**, but 08UB produces the conormal
  homomorphism only after *enlarging* the sheaf of generators `ℰ`, and the identification of
  `Ext¹(NL(α'), 𝒢)` with `Ext¹(NL(α), 𝒢)` under that enlargement is **Stacks 08TL**, which the
  library does not have. So surjectivity for the one fixed presentation is carried.
* The bijection between morphisms of solutions and factorizations of the difference map through
  the degree `0` term, as the hypothesis `e` of `setoid_iff_nonempty_lift`. Inherited verbatim
  from **Stacks 08U8**, where it carries Steps 1 to 3 of the source's proof.
* The source's remark that a morphism of solutions is automatically an isomorphism — "clearly,
  this element is the obstruction to the existence of an isomorphism". `setoid_iff_nonempty_lift`
  identifies the relation used here with the existence of a morphism of solutions, which is
  **Stacks 08U8**, clause (1); that such a morphism is invertible is the five-lemma comparison of
  the two ideal sequences `0 ⟶ 𝒢 ⟶ 𝒪_{X'ⱼ} ⟶ 𝒪_X ⟶ 0` of the two solutions, and is not proved
  here.

Three scope limitations are inherited from **Stacks 08U8** as well. The acting group is the
`Ext¹` of the presentation, `Ext¹(NL(α), 𝒢)`; its identification with `Ext¹(NL_{X/S}, 𝒢)` is
again **Stacks 08TL** and is not proved. The underlying spaces of the two solutions being
compared are identified, as in the source's own reduction, so that a morphism of solutions is a
homomorphism of sheaves of rings. And **Stacks 08U8** is stated there over an abstract functor
`single : M ⥤ D` into an abstract pretriangulated category, with neither `DeformationCube` nor
`DeformationIdealDiagram` ever appearing, so it is not instantiated at ringed spaces anywhere;
only `deformationSolutionAddTorsor` below puts the solution type back at
`DeformationSolution`.

## References

* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UB](https://stacks.math.columbia.edu/tag/08UB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe w v u v' u'

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### The obstruction data of the source's proof -/

/-- The obstruction data attached by the proof of [Stacks 08UC] to the deformation problem
(91.7.0.1): on a type `Sol` of solutions, the obstruction class `o Q₁ Q₂` to a morphism from
`Q₁` to `Q₂` of [Stacks 08U8], which is a cocycle, and the construction `Q ↦ Q_ξ` of a solution
whose obstruction class against `Q` is a prescribed class `ξ`.

Both are data rather than existence statements, as in the source: `o` is the class of Step 1 of
the proof of [Stacks 08U8] and `twist Q ξ` is the pushout construction of the proof of
[Stacks 08UC]. -/
structure SolutionObstruction (Sol : Type u) (E : Type v) [AddCommGroup E] where
  /-- The obstruction class to a morphism from the first solution to the second. -/
  o : Sol → Sol → E
  /-- The obstruction class is a cocycle: the obstruction from `Q₁` to `Q₃` is the sum of the
  obstructions from `Q₁` to `Q₂` and from `Q₂` to `Q₃`. -/
  o_add : ∀ Q₁ Q₂ Q₃ : Sol, o Q₁ Q₂ + o Q₂ Q₃ = o Q₁ Q₃
  /-- The construction `Q ↦ Q_ξ` of the source's proof. -/
  twist : Sol → E → Sol
  /-- The obstruction class from `Q` to `Q_ξ` is `ξ`. -/
  o_twist : ∀ (Q : Sol) (ξ : E), o Q (twist Q ξ) = ξ

namespace SolutionObstruction

variable {Sol : Type u} {E : Type v} [AddCommGroup E] (T : SolutionObstruction Sol E)

/-- There is no obstruction from a solution to itself. -/
theorem o_self (Q : Sol) : T.o Q Q = 0 := by
  simpa using T.o_add Q Q Q

/-- Reversing the direction negates the obstruction class. -/
theorem o_swap (Q₁ Q₂ : Sol) : T.o Q₂ Q₁ = -T.o Q₁ Q₂ :=
  eq_neg_of_add_eq_zero_right ((T.o_add Q₁ Q₂ Q₁).trans (T.o_self Q₁))

/-- The obstruction from `Q₁` to `Q₃` when `Q₁` and `Q₂` have no obstruction between them. -/
theorem o_eq_of_eq_zero_left {Q₁ Q₂ : Sol} (h : T.o Q₁ Q₂ = 0) (Q₃ : Sol) :
    T.o Q₁ Q₃ = T.o Q₂ Q₃ := by
  rw [← T.o_add Q₁ Q₂ Q₃, h, zero_add]

/-- The obstruction from `Q_ξ` back to `Q` is `-ξ`. -/
private theorem o_twist_left (Q : Sol) (ξ : E) : T.o (T.twist Q ξ) Q = -ξ := by
  rw [T.o_swap, T.o_twist]

/-- Isomorphism of solutions, as the vanishing of the obstruction class between them. By
[Stacks 08U8], clause (1), this is the existence of a morphism from the one to the other fitting
into the source's diagram; see `setoid_iff_nonempty_lift`. -/
def setoid : Setoid Sol where
  r Q₁ Q₂ := T.o Q₁ Q₂ = 0
  iseqv :=
    { refl := T.o_self
      symm := fun {_ _} h => by rw [T.o_swap, h, neg_zero]
      trans := fun {Q₁ Q₂ Q₃} h₁ h₂ => by rw [← T.o_add Q₁ Q₂ Q₃, h₁, h₂, add_zero] }

/-- The set of isomorphism classes of solutions. -/
abbrev IsomorphismClasses : Type u := Quotient T.setoid

/-- The isomorphism class of a solution. -/
abbrev isoClass (Q : Sol) : T.IsomorphismClasses := Quotient.mk T.setoid Q

/-- The obstruction class separates the isomorphism classes of solutions: two solutions have the
same class exactly when the obstruction between them vanishes.

By `setoid_iff_nonempty_lift` the relation is, through [Stacks 08U8] clause (1), the existence
of a morphism between the two solutions fitting into the source's diagram; that such a morphism
is automatically invertible — the source's "clearly, this element is the obstruction to the
existence of an isomorphism" — is the five lemma for the two ideal sequences and is not proved
here. -/
theorem isoClass_eq_isoClass_iff (Q₁ Q₂ : Sol) :
    T.isoClass Q₁ = T.isoClass Q₂ ↔ T.o Q₁ Q₂ = 0 :=
  Quotient.eq_iff_equiv

/-! ### The action of the Ext group on isomorphism classes -/

/-- The action of a class `ξ` on an isomorphism class of solutions: the class of `Q_ξ`, for `Q`
any representative. It is well defined because the obstruction from `Q₁_ξ` to `Q₂_ξ` is
`-ξ + o Q₁ Q₂ + ξ`. -/
def vaddClass (ξ : E) (q : T.IsomorphismClasses) : T.IsomorphismClasses :=
  Quotient.liftOn q (fun Q => T.isoClass (T.twist Q ξ)) <| by
    intro Q₁ Q₂ h
    refine Quotient.sound ?_
    change T.o (T.twist Q₁ ξ) (T.twist Q₂ ξ) = 0
    have h₁ : T.o (T.twist Q₁ ξ) Q₁ = -ξ := by rw [T.o_swap, T.o_twist]
    have h₂ : T.o Q₁ (T.twist Q₂ ξ) = ξ := by
      rw [T.o_eq_of_eq_zero_left h, T.o_twist]
    rw [← T.o_add (T.twist Q₁ ξ) Q₁ (T.twist Q₂ ξ), h₁, h₂, neg_add_cancel]

/-- The action of `ξ` on the isomorphism class of `Q` is the isomorphism class of `Q_ξ`. -/
@[simp]
theorem vaddClass_isoClass (ξ : E) (Q : Sol) :
    T.vaddClass ξ (T.isoClass Q) = T.isoClass (T.twist Q ξ) :=
  rfl

/-- The zero class acts trivially on isomorphism classes of solutions. -/
theorem zero_vaddClass (q : T.IsomorphismClasses) : T.vaddClass 0 q = q :=
  Quotient.inductionOn q fun Q =>
    show T.isoClass (T.twist Q 0) = T.isoClass Q from Quotient.sound <| by
      show T.o (T.twist Q 0) Q = 0
      rw [T.o_twist_left, neg_zero]

/-- The action of the Ext group on isomorphism classes of solutions is additive. -/
theorem add_vaddClass (ξ η : E) (q : T.IsomorphismClasses) :
    T.vaddClass (ξ + η) q = T.vaddClass ξ (T.vaddClass η q) :=
  Quotient.inductionOn q fun Q =>
    show T.isoClass (T.twist Q (ξ + η)) = T.isoClass (T.twist (T.twist Q η) ξ) from
      Quotient.sound <| by
        show T.o (T.twist Q (ξ + η)) (T.twist (T.twist Q η) ξ) = 0
        have h₂ : T.o Q (T.twist (T.twist Q η) ξ) = η + ξ := by
          rw [← T.o_add Q (T.twist Q η) (T.twist (T.twist Q η) ξ), T.o_twist, T.o_twist]
        rw [← T.o_add (T.twist Q (ξ + η)) Q (T.twist (T.twist Q η) ξ), T.o_twist_left, h₂,
          add_comm η ξ,
          neg_add_cancel]

/-- The class in the Ext group separating two isomorphism classes of solutions: the obstruction
class between any two representatives. -/
def vsubClass (q₁ q₂ : T.IsomorphismClasses) : E :=
  Quotient.liftOn₂ q₁ q₂ (fun Q₁ Q₂ => T.o Q₂ Q₁) <| by
    intro a₁ a₂ b₁ b₂ h₁ h₂
    rw [T.o_eq_of_eq_zero_left h₂, ← T.o_add b₂ a₁ b₁, show T.o a₁ b₁ = 0 from h₁, add_zero]

/-- The class separating the isomorphism classes of `Q₁` and `Q₂` is the obstruction class
`o Q₂ Q₁`. -/
@[simp]
theorem vsubClass_isoClass (Q₁ Q₂ : Sol) :
    T.vsubClass (T.isoClass Q₁) (T.isoClass Q₂) = T.o Q₂ Q₁ :=
  rfl

/-- Acting by the separating class of two isomorphism classes carries the one to the other. -/
theorem vsubClass_vaddClass (q₁ q₂ : T.IsomorphismClasses) :
    T.vaddClass (T.vsubClass q₁ q₂) q₂ = q₁ :=
  Quotient.inductionOn₂ q₁ q₂ fun Q₁ Q₂ =>
    show T.isoClass (T.twist Q₂ (T.o Q₂ Q₁)) = T.isoClass Q₁ from Quotient.sound <| by
      show T.o (T.twist Q₂ (T.o Q₂ Q₁)) Q₁ = 0
      rw [← T.o_add (T.twist Q₂ (T.o Q₂ Q₁)) Q₂ Q₁, T.o_twist_left, neg_add_cancel]

/-- The class separating the translate of an isomorphism class from the class itself is the
translating class. -/
theorem vaddClass_vsubClass (ξ : E) (q : T.IsomorphismClasses) :
    T.vsubClass (T.vaddClass ξ q) q = ξ :=
  Quotient.inductionOn q fun Q => show T.o Q (T.twist Q ξ) = ξ from T.o_twist Q ξ

/-- Given obstruction data on a nonempty type of solutions, the isomorphism classes are a
principal homogeneous space under the coefficient group, as Mathlib's `AddTorsor`: the group
acts on isomorphism classes, the action is simply transitive, and the set of classes is
nonempty.

This is the *formalism* of [Stacks 08UC] and not the tag: the difference cocycle and the action
are the fields `o` and `twist` of `SolutionObstruction`, i.e. inputs. The hypothesis
`[Nonempty Sol]` is the source's "if there exists a solution". -/
noncomputable instance addTorsor [Nonempty Sol] : AddTorsor E T.IsomorphismClasses where
  vadd := T.vaddClass
  zero_vadd := T.zero_vaddClass
  add_vadd := T.add_vaddClass
  vsub := T.vsubClass
  nonempty := Nonempty.map T.isoClass ‹Nonempty Sol›
  vsub_vadd' := T.vsubClass_vaddClass
  vadd_vsub' := T.vaddClass_vsubClass

/-- The action on isomorphism classes is simply transitive: any isomorphism class is carried to
any other by exactly one element of the coefficient group. Stated without the bundling of
`addTorsor`. -/
theorem existsUnique_vaddClass (q₁ q₂ : T.IsomorphismClasses) :
    ∃! ξ : E, T.vaddClass ξ q₂ = q₁ :=
  ⟨T.vsubClass q₁ q₂, T.vsubClass_vaddClass q₁ q₂, fun ξ hξ => by rw [← hξ, T.vaddClass_vsubClass]⟩

end SolutionObstruction

/-! ### The obstruction data built from the class of Stacks 08U8 -/

section Ext

variable {M : Type u} [Category.{v} M] [Abelian M] {D : Type u'} [Category.{v'} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] {single : M ⥤ D} [single.Full] [single.Faithful] [single.Additive]

omit [single.Full] [single.Faithful] in
/-- The class in `Ext¹(NL(α), 𝒢)` of a homomorphism out of the conormal module is additive in
that homomorphism. -/
theorem conormalExtClass_add (P : NaiveCotangentTwoTerm single) (G : M)
    (f g : P.conormal ⟶ G) :
    P.conormalExtClass G (f + g) = P.conormalExtClass G f + P.conormalExtClass G g := by
  simp only [NaiveCotangentTwoTerm.conormalExtClass, single.map_add,
    (shiftFunctor D (1 : ℤ)).map_add, Preadditive.comp_add]

omit [single.Full] [single.Faithful] in
/-- The obstruction class of Step 1 of the proof of [Stacks 08U8] is additive in the conormal
homomorphism `ξ` it is the class of. This is what makes the obstruction of [Stacks 08UC] a
cocycle on solutions. -/
theorem liftingObstruction_add (P : NaiveCotangentTwoTerm single) (G : M)
    (f g : P.conormal ⟶ G) :
    liftingObstruction P G (f + g) = liftingObstruction P G f + liftingObstruction P G g :=
  conormalExtClass_add P G f g

/-- The obstruction data of [Stacks 08UC] assembled from the obstruction class of
[Stacks 08U8]: the acting group is `Ext¹(NL(α), 𝒢) = (NL(α) ⟶ 𝒢⟦1⟧)` and the obstruction
between two solutions is the class of the difference homomorphism `ℐ/ℐ² ⟶ 𝒢` of Step 1 of the
proof of [Stacks 08U8].

The difference homomorphism `xi` with its additivity, the representation `rep` of every class
by a conormal homomorphism (which is [Stacks 08UB]) and the pushout construction `pushout` of
the proof of [Stacks 08UC] are the inputs; see the implementation notes of this file. -/
def liftingObstructionSolution (P : NaiveCotangentTwoTerm single) (G : M) {Sol : Type w}
    (xi : Sol → Sol → (P.conormal ⟶ G))
    (hxi : ∀ Q₁ Q₂ Q₃ : Sol, xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ξ : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ G // liftingObstruction P G δ = ξ })
    (pushout : ∀ (Q : Sol) (δ : P.conormal ⟶ G), { Q' : Sol // xi Q Q' = δ }) :
    SolutionObstruction Sol (P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧) where
  o Q₁ Q₂ := liftingObstruction P G (xi Q₁ Q₂)
  o_add Q₁ Q₂ Q₃ := by
    rw [← liftingObstruction_add P G (xi Q₁ Q₂) (xi Q₂ Q₃), hxi Q₁ Q₂ Q₃]
  twist Q ξ := (pushout Q (rep ξ).1).1
  o_twist Q ξ := by rw [(pushout Q (rep ξ).1).2, (rep ξ).2]

omit [single.Full] [single.Faithful] in
/-- The obstruction class of `liftingObstructionSolution` between two solutions is the class
`liftingObstruction P G (xi Q₁ Q₂)` of their difference homomorphism. -/
@[simp]
theorem liftingObstructionSolution_o (P : NaiveCotangentTwoTerm single) (G : M) {Sol : Type w}
    (xi : Sol → Sol → (P.conormal ⟶ G))
    (hxi : ∀ Q₁ Q₂ Q₃ : Sol, xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ξ : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ G // liftingObstruction P G δ = ξ })
    (pushout : ∀ (Q : Sol) (δ : P.conormal ⟶ G), { Q' : Sol // xi Q Q' = δ })
    (Q₁ Q₂ : Sol) :
    (liftingObstructionSolution P G xi hxi rep pushout).o Q₁ Q₂ =
      liftingObstruction P G (xi Q₁ Q₂) :=
  rfl

/-- Through [Stacks 08U8], clause (1), the equivalence relation of
`SolutionObstruction.setoid` is the existence of a morphism between the two solutions fitting
into the source's diagram: that is what makes the quotient the set of *isomorphism* classes.

The equivalence `e` is the hypothesis of `liftingObstruction_eq_zero_iff`, carrying Steps 1
to 3 of the proof of [Stacks 08U8]. -/
theorem setoid_iff_nonempty_lift (P : NaiveCotangentTwoTerm single) (G : M) {Sol : Type w}
    (xi : Sol → Sol → (P.conormal ⟶ G))
    (hxi : ∀ Q₁ Q₂ Q₃ : Sol, xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ξ : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ G // liftingObstruction P G δ = ξ })
    (pushout : ∀ (Q : Sol) (δ : P.conormal ⟶ G), { Q' : Sol // xi Q Q' = δ })
    {Lift : Sol → Sol → Type*}
    (e : ∀ Q₁ Q₂ : Sol, Lift Q₁ Q₂ ≃ { θ : P.base ⟶ G // P.d ≫ θ = xi Q₁ Q₂ })
    (Q₁ Q₂ : Sol) :
    (liftingObstructionSolution P G xi hxi rep pushout).setoid.r Q₁ Q₂ ↔
      Nonempty (Lift Q₁ Q₂) :=
  liftingObstruction_eq_zero_iff P G (xi Q₁ Q₂) (e Q₁ Q₂)

/-- The quotient on which `Ext¹(NL(α), 𝒢)` acts is the set of classes of solutions under the
existence of a morphism of solutions: two solutions have the same class exactly when a morphism
between them fitting into the source's diagram exists. This is
`SolutionObstruction.isoClass_eq_isoClass_iff` combined with [Stacks 08U8], clause (1). -/
theorem isoClass_eq_isoClass_iff_nonempty_lift (P : NaiveCotangentTwoTerm single) (G : M)
    {Sol : Type w} (xi : Sol → Sol → (P.conormal ⟶ G))
    (hxi : ∀ Q₁ Q₂ Q₃ : Sol, xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ξ : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ G // liftingObstruction P G δ = ξ })
    (pushout : ∀ (Q : Sol) (δ : P.conormal ⟶ G), { Q' : Sol // xi Q Q' = δ })
    {Lift : Sol → Sol → Type*}
    (e : ∀ Q₁ Q₂ : Sol, Lift Q₁ Q₂ ≃ { θ : P.base ⟶ G // P.d ≫ θ = xi Q₁ Q₂ })
    (Q₁ Q₂ : Sol) :
    (liftingObstructionSolution P G xi hxi rep pushout).isoClass Q₁ =
        (liftingObstructionSolution P G xi hxi rep pushout).isoClass Q₂ ↔
      Nonempty (Lift Q₁ Q₂) :=
  ((liftingObstructionSolution P G xi hxi rep pushout).isoClass_eq_isoClass_iff Q₁ Q₂).trans
    (liftingObstruction_eq_zero_iff P G (xi Q₁ Q₂) (e Q₁ Q₂))

end Ext

/-! ### The formalism for the solutions of the deformation problem -/

section Deformation

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {single : SheafOfModules.{u} (structureSheafRing X) ⥤ D} [single.Full] [single.Faithful]
  [single.Additive]

/-- The torsor formalism of this file, specialized to the solutions `DeformationSolution` of the
deformation problem (91.7.0.1) of [Stacks 08U7]: if a solution exists, their isomorphism classes
are a principal homogeneous space under `Ext¹(NL(α), 𝒢) = (NL(α) ⟶ 𝒢⟦1⟧)`, where isomorphism of
solutions is the vanishing of the obstruction class of [Stacks 08U8] and the action is the
construction `X' ↦ X'_ξ`.

This is **not** [Stacks 08UC]: the difference cocycle `xi`, `hxi` and the action `pushout` are
hypotheses, and together they are the assertion of the tag. See the implementation notes. -/
@[instance_reducible]
noncomputable def deformationSolutionAddTorsor (P : NaiveCotangentTwoTerm single)
    (xi : DeformationSolution t ht f G c → DeformationSolution t ht f G c →
      (P.conormal ⟶ G))
    (hxi : ∀ Q₁ Q₂ Q₃ : DeformationSolution t ht f G c, xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ξ : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ G // liftingObstruction P G δ = ξ })
    (pushout : ∀ (Q : DeformationSolution t ht f G c) (δ : P.conormal ⟶ G),
      { Q' : DeformationSolution t ht f G c // xi Q Q' = δ })
    (hne : Nonempty (DeformationSolution t ht f G c)) :
    AddTorsor (P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧)
      (liftingObstructionSolution P G xi hxi rep pushout).IsomorphismClasses :=
  letI := hne
  (liftingObstructionSolution P G xi hxi rep pushout).addTorsor

end Deformation

end AlgebraicGeometry.RingedSpaceThickening

end
