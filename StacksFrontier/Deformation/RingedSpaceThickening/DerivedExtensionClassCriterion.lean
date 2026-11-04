module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentLiftingObstruction
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionExtensionFibre
import StacksCore.Tactic.StacksAttribute

/-!
# The criterion on extension classes for the derived pullback, and the fibre of Stacks 0GQ3

Fix the deformation problem of **Stacks 08U7**: a first order thickening `t : (S, 𝒪_S) ⟶
(S', 𝒪_{S'})` with ideal `𝒥`, a morphism `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, an `𝒪_X`-module `𝒢` and a
map `c : f^*𝒥 ⟶ 𝒢`.  **Stacks 0GQ1** says a square-zero extension `𝒪_{X'}` of
`f^{-1}𝒪_{S'}`-algebras admits the morphism compatible with `f` and `c` exactly when its class
agrees with the image of the class `ξ` of `𝒪_{S'}`; **Stacks 0GQ3** turns that criterion into a
bijection between the isomorphism classes of solutions and a fibre.

Both statements are about the **derived** pullback `Lf^*𝖭𝖫_{S/S'}` of **Stacks 06YJ**.  This
file states and proves the criterion in the derived group, with the image of `ξ` the map
`pullbackExtClass`, and deduces 0GQ3 from `solutionsEquivExtFibre`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.SolutionInClass`: the solutions of **Stacks 08U7**
  lying in a prescribed isomorphism class of square-zero extensions of `f^{-1}𝒪_{S'}`-algebras.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.exists_compatibleLift_iff_eq_pullbackExtClass`:
  **Stacks 0GQ1** for the derived pullback — a compatible lift exists exactly when the
  constructed image of `ξ` in `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)` equals the restriction of the
  class of the extension.
* `AlgebraicGeometry.RingedSpaceThickening.isSolutionClass_iff_eq_pullbackExtClass`: the same
  criterion read on isomorphism classes of extensions.
* `AlgebraicGeometry.RingedSpaceThickening.solutionsEquivDerivedExtFibre`: **Stacks 0GQ3**, the
  canonical bijection from the isomorphism classes of solutions of **Stacks 08U7** to the fibre
  of `Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)` over the image of `ξ`, with
  `solutionsEquivDerivedExtFibre_apply` identifying it with the map `[X'] ↦ E [𝒪_{X'}]` and
  `nonempty_derivedExtFibre_of_nonempty` saying the fibre is nonempty as soon as a solution is.

## Implementation notes

The criterion takes as hypotheses a two-term structure `P` of `Lf^*𝖭𝖫_{S/S'}` with its
identification `hP`, a bijection `e` between the compatible lifts and the factorizations of the
difference homomorphism `δ` (Steps 1 to 3 of the proof of **Stacks 08U8**), and `hcompat`, the
compatibility between the constructions in the proofs of **Stacks 0GPZ** and **Stacks 08U8**: the
difference of the two classes is the obstruction class.  The comparison
`q : Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}` and, for 0GQ3, the bijection `E` of **Stacks 0GPZ** are
arguments.

`SolutionInClass` is the subtype of solutions whose underlying extension lies in the given class,
so that `Nonempty (SolutionInClass …)` is `ExtensionOverBase.IsSolutionClass` by
`nonempty_solutionInClass_iff_isSolutionClass`.

## References

* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}}

/-! ### Stacks 0GQ1 for the derived pullback -/

/-- For the derived pullback `Lf^*𝖭𝖫_{S/S'}`: a lift compatible with `f` and the prescribed map `c`
exists if and only if the class of the extension `𝒪_{X'}`, restricted along a comparison
`q : Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`, agrees with the image `pullbackExtClass f t c xi` of
`ξ ∈ Ext¹_{𝒪_S}(𝖭𝖫_{S/S'}, 𝒥)` in `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)`.  The compatible lifts are the
type `Lift`, identified by `e` with the factorizations of the difference homomorphism `δ` through
the degree `0` term, and `hcompat` says that the difference of the two classes is the
obstruction class. -/
@[stacks 0GQ1 "the criterion for the DERIVED pullback Lf^*𝖭𝖫_{S/S'} of the source's statement, \
with the image of ξ the constructed map pullbackExtClass. Carried, exactly as in the degreewise \
form: the two-term structure P with hP, the bijection e of Steps 1 to 3 of 08U8, and hcompat, \
the 0GPZ/08U8 compatibility whose statement and proof the source omits"]
theorem exists_compatibleLift_iff_eq_pullbackExtClass {f : X ⟶ S} {t : S ⟶ S'}
    {J : SheafOfModules.{u} (structureSheafRing S)} {G : SheafOfModules.{u} (structureSheafRing X)}
    (c : (modulePullback f).obj J ⟶ G)
    (q : derivedPullbackNaiveCotangent f t ⟶ relativeNaiveCotangentObj (f ≫ t))
    (P : NaiveCotangentTwoTerm
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0))
    (hP : P.obj = derivedPullbackNaiveCotangent f t)
    (δ : P.conormal ⟶ G) {Lift : Type*}
    (e : Lift ≃ {θ : P.base ⟶ G // P.d ≫ θ = δ})
    (xi : extOneNaiveCotangent t J) (ζ : extOneNaiveCotangent (f ≫ t) G)
    (hcompat : eqToHom hP ≫ (pullbackExtClass f t c xi - restrictDerivedExtClass q ζ) =
      P.conormalExtClass G δ) :
    Nonempty Lift ↔ pullbackExtClass f t c xi = restrictDerivedExtClass q ζ := by
  rw [← liftingObstruction_eq_zero_iff P G δ e, liftingObstruction, ← hcompat,
    Preadditive.IsIso.comp_left_eq_zero, sub_eq_zero]

/-! ### The criterion on isomorphism classes, and Stacks 0GQ3 -/

section Classes

variable {t : S ⟶ S'} (ht : IsFirstOrderThickening t) {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  (c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G)
  (r : Setoid (ExtensionOverBase f t G))

/-- The solutions of **Stacks 08U7** whose underlying square-zero extension of
`f^{-1}𝒪_{S'}`-algebras lies in the class `p`.  A solution carries its morphism to `S'` and the
compatibility equation for `c` as data, so this is the source's set of lifts of the extension
compatible with `f` and `c`, read on the class `p`. -/
abbrev SolutionInClass (p : Quotient r) : Type _ :=
  {Q : DeformationSolution t ht f G c // Quotient.mk r (toExtensionOverBase Q) = p}

/-- A class of extensions of `f^{-1}𝒪_{S'}`-algebras is a class of solutions of
**Stacks 08U7** exactly when it admits a compatible lift, i.e. when `SolutionInClass` is
nonempty. -/
theorem nonempty_solutionInClass_iff_isSolutionClass (p : Quotient r) :
    Nonempty (SolutionInClass ht c r p) ↔ ExtensionOverBase.IsSolutionClass ht c r p :=
  ⟨fun h => h.elim fun Q => ⟨Q.1, Q.2⟩, fun h => h.elim fun Q hQ => ⟨⟨Q, hQ⟩⟩⟩

/-- Read on isomorphism classes: a class of square-zero extensions of `f^{-1}𝒪_{S'}`-algebras is
a class of solutions of **Stacks 08U7** exactly when its image under `E` restricts, along a
comparison `q : Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`, to the image of `ξ` in
`Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)`.  Here `P` with `hP` is a two-term structure of
`Lf^*𝖭𝖫_{S/S'}`, `e` and `hcompat` are the per-class bijections and compatibilities of
`exists_compatibleLift_iff_eq_pullbackExtClass`, and `E` is the bijection of **Stacks 0GPZ**. -/
@[stacks 0GQ1 "the criterion for the DERIVED pullback, read on isomorphism classes of \
extensions: this is the hcrit hypothesis of solutionsEquivExtFibre, proved rather than \
assumed. Carried are the two-term structure P with hP, the per-class bijections e of Steps 1 \
to 3 of 08U8, the per-class 0GPZ/08U8 compatibilities, and the 0GPZ bijection E"]
theorem isSolutionClass_iff_eq_pullbackExtClass
    (E : Quotient r ≃ extOneNaiveCotangent (f ≫ t) G)
    (q : derivedPullbackNaiveCotangent f t ⟶ relativeNaiveCotangentObj (f ≫ t))
    (xi : extOneNaiveCotangent t (baseIdealOnReduction t))
    (P : NaiveCotangentTwoTerm
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0))
    (hP : P.obj = derivedPullbackNaiveCotangent f t)
    (δ : Quotient r → (P.conormal ⟶ G))
    (e : ∀ p : Quotient r, SolutionInClass ht c r p ≃
      {θ : P.base ⟶ G // P.d ≫ θ = δ p})
    (hcompat : ∀ p : Quotient r, eqToHom hP ≫
      (pullbackExtClass f t c xi - restrictDerivedExtClass q (E p)) =
        P.conormalExtClass G (δ p))
    (p : Quotient r) :
    ExtensionOverBase.IsSolutionClass ht c r p ↔
      restrictDerivedExtClass q (E p) = pullbackExtClass f t c xi :=
  (nonempty_solutionInClass_iff_isSolutionClass ht c r p).symm.trans
    ((exists_compatibleLift_iff_eq_pullbackExtClass c q P hP (δ p) (e p) xi (E p)
      (hcompat p)).trans eq_comm)

/-- In the situation of **Stacks 08U7**, with `ξ` the class of the extension `𝒪_{S'}` of `𝒪_S`
by `𝒥`, the isomorphism classes of solutions are canonically bijective to the fibre of

`Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)`

over the image of `ξ`, by the map `[X'] ↦ E [𝒪_{X'}]`.  Here `E` is the bijection of
**Stacks 0GPZ**, `q` the comparison of naive cotangent complexes, and `P`, `hP`, `δ`, `e`,
`hcompat` the inputs of `isSolutionClass_iff_eq_pullbackExtClass`. -/
@[stacks 0GQ3 "the canonical bijection from isomorphism classes of solutions of 08U7 to the \
fibre of Ext¹(𝖭𝖫_{X/S'}, 𝒢) ⟶ Ext¹(Lf^*𝖭𝖫_{S/S'}, 𝒢) over the image of ξ, by the constructed \
map [X'] ↦ E [𝒪_{X'}]. Carried: the 0GPZ bijection E, the comparison q, and the inputs P, hP, \
δ, e, hcompat of the 0GQ1 criterion — which is proved here, not assumed"]
def solutionsEquivDerivedExtFibre
    (E : Quotient r ≃ extOneNaiveCotangent (f ≫ t) G)
    (q : derivedPullbackNaiveCotangent f t ⟶ relativeNaiveCotangentObj (f ≫ t))
    (xi : extOneNaiveCotangent t (baseIdealOnReduction t))
    (P : NaiveCotangentTwoTerm
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0))
    (hP : P.obj = derivedPullbackNaiveCotangent f t)
    (δ : Quotient r → (P.conormal ⟶ G))
    (e : ∀ p : Quotient r, SolutionInClass ht c r p ≃
      {θ : P.base ⟶ G // P.d ≫ θ = δ p})
    (hcompat : ∀ p : Quotient r, eqToHom hP ≫
      (pullbackExtClass f t c xi - restrictDerivedExtClass q (E p)) =
        P.conormalExtClass G (δ p)) :
    Quotient (solutionSetoid ht c r) ≃
      {z : extOneNaiveCotangent (f ≫ t) G //
        restrictDerivedExtClass q z = pullbackExtClass f t c xi} :=
  solutionsEquivExtFibre ht c (restrictDerivedExtClass q) (pullbackExtClass f t c xi) r E
    (isSolutionClass_iff_eq_pullbackExtClass ht c r E q xi P hP δ e hcompat)

/-- The bijection `solutionsEquivDerivedExtFibre` sends the class of a solution `X'` to
`E [𝒪_{X'}]`. -/
@[stacks 0GQ3 "the canonicity of the bijection: it is the constructed map [X'] ↦ E [𝒪_{X'}], \
sending the class of a solution to the class of its underlying extension read through the \
0GPZ bijection, rather than an unspecified bijection of the two sides"]
theorem solutionsEquivDerivedExtFibre_apply
    (E : Quotient r ≃ extOneNaiveCotangent (f ≫ t) G)
    (q : derivedPullbackNaiveCotangent f t ⟶ relativeNaiveCotangentObj (f ≫ t))
    (xi : extOneNaiveCotangent t (baseIdealOnReduction t))
    (P : NaiveCotangentTwoTerm
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0))
    (hP : P.obj = derivedPullbackNaiveCotangent f t)
    (δ : Quotient r → (P.conormal ⟶ G))
    (e : ∀ p : Quotient r, SolutionInClass ht c r p ≃
      {θ : P.base ⟶ G // P.d ≫ θ = δ p})
    (hcompat : ∀ p : Quotient r, eqToHom hP ≫
      (pullbackExtClass f t c xi - restrictDerivedExtClass q (E p)) =
        P.conormalExtClass G (δ p))
    (s : Quotient (solutionSetoid ht c r)) :
    (solutionsEquivDerivedExtFibre ht c r E q xi P hP δ e hcompat s).1 =
      solutionClassToExtClass ht c r E s :=
  solutionsEquivExtFibre_apply ht c (restrictDerivedExtClass q)
    (pullbackExtClass f t c xi) r E
    (isSolutionClass_iff_eq_pullbackExtClass ht c r E q xi P hP δ e hcompat) s

/-- The fibre of `Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)` over the image of `ξ`
is nonempty as soon as a solution of **Stacks 08U7** exists. -/
theorem nonempty_derivedExtFibre_of_nonempty
    (E : Quotient r ≃ extOneNaiveCotangent (f ≫ t) G)
    (q : derivedPullbackNaiveCotangent f t ⟶ relativeNaiveCotangentObj (f ≫ t))
    (xi : extOneNaiveCotangent t (baseIdealOnReduction t))
    (P : NaiveCotangentTwoTerm
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0))
    (hP : P.obj = derivedPullbackNaiveCotangent f t)
    (δ : Quotient r → (P.conormal ⟶ G))
    (e : ∀ p : Quotient r, SolutionInClass ht c r p ≃
      {θ : P.base ⟶ G // P.d ≫ θ = δ p})
    (hcompat : ∀ p : Quotient r, eqToHom hP ≫
      (pullbackExtClass f t c xi - restrictDerivedExtClass q (E p)) =
        P.conormalExtClass G (δ p))
    (hne : Nonempty (DeformationSolution t ht f G c)) :
    Nonempty {z : extOneNaiveCotangent (f ≫ t) G //
      restrictDerivedExtClass q z = pullbackExtClass f t c xi} :=
  nonempty_extFibre_of_nonempty ht c (restrictDerivedExtClass q)
    (pullbackExtClass f t c xi) r E
    (isSolutionClass_iff_eq_pullbackExtClass ht c r E q xi P hP δ e hcompat) hne

end Classes

end AlgebraicGeometry.RingedSpaceThickening

end
