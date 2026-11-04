module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentTowerConeMap
public import StacksFrontier.Deformation.ToposThickening.LiftingBetweenThickenings
import StacksCore.Tactic.StacksAttribute

/-!
# Comparing the classes of two square-zero extensions of ringed topoi (Stacks 0GQ7)

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi, `ℱ` an `𝒪_𝒞`-module, `𝒢` an `𝒪_𝒟`-module and `c : g^*ℱ ⟶ 𝒢` an `𝒪_𝒟`-linear map.
A class `ξ ∈ Ext¹_{𝒪_𝒞}(NL_{𝒪_𝒞/𝒪_ℬ}, ℱ)` classifying an extension `0 → ℱ → 𝒪_{𝒞'} → 𝒪_𝒞 → 0`
of `f⁻¹𝒪_ℬ`-algebras and a class `ζ ∈ Ext¹_{𝒪_𝒟}(NL_{𝒪_𝒟/𝒪_ℬ}, 𝒢)` classifying an extension
`0 → 𝒢 → 𝒪_{𝒟'} → 𝒪_𝒟 → 0` of `g⁻¹f⁻¹𝒪_ℬ`-algebras are compared in
`Ext¹_{𝒪_𝒟}(g^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`, and a morphism `g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` of
ringed topoi over `(Sh(ℬ), 𝒪_ℬ)` compatible with `g` and `c` exists exactly when the two images
agree.

Following the reduction of **Stacks 08UG** used throughout
`StacksFrontier/Deformation/ToposThickening/LiftingBetweenThickenings.lean` — "we will identify the
underlying topoi for every thickening in sight" — the data are a
`Deformation.ToposThickening.LiftDiagram` on one site, so the sought morphism `g'` is the
concrete type `LiftDiagram.Lift` of homomorphisms `𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}` of sheaves of rings over
the base inducing `c` on the two square-zero ideals, and the map along which `ζ` is read is
precomposition with the canonical comparison `g^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}` built from the
base-change map and the relative map of **Stacks 0E1Y** for `f⁻¹𝒪_ℬ ⟶ 𝒪_𝒞 ⟶ 𝒪_𝒟` and
`f⁻¹𝒪_ℬ ⟶ g⁻¹f⁻¹𝒪_ℬ ⟶ 𝒪_𝒟`.

## Main definitions

* `Deformation.ToposThickening.LiftDiagram.pulledNaiveCotangentComplex` and
  `LiftDiagram.relativeNaiveCotangentComplex`: the complexes `g^*NL_{𝒪_𝒞/𝒪_ℬ}` and
  `NL_{𝒪_𝒟/𝒪_ℬ}` of the diagram.
* `Deformation.ToposThickening.LiftDiagram.pulledNaiveCotangentComparison`: the canonical
  comparison `g^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}`.
* `Deformation.ToposThickening.LiftDiagram.pulledExtGroup` and `LiftDiagram.relativeExtGroup`:
  the groups `Ext¹_{𝒪_𝒟}(g^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)` and `Ext¹_{𝒪_𝒟}(NL_{𝒪_𝒟/𝒪_ℬ}, 𝒢)`.
* `Deformation.ToposThickening.LiftDiagram.restrictExtClass`: the map
  `Ext¹_{𝒪_𝒟}(NL_{𝒪_𝒟/𝒪_ℬ}, 𝒢) ⟶ Ext¹_{𝒪_𝒟}(g^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`, precomposition with that
  comparison, and `LiftDiagram.restrictExtClassHom`, the same map as a homomorphism of the two
  `Ext` groups.

## Main results

* `Deformation.ToposThickening.LiftDiagram.nonempty_lift_iff_eq_restrictExtClass`:
  **Stacks 0GQ7**, the equivalence, deduced from clause (1) of **Stacks 08UG**.

## Implementation notes

The comparison of naive cotangent complexes is built, not quantified over: an arbitrary
morphism between those two objects would change the asserted equivalence. With the underlying
topoi identified it is the base-change map `NL_{𝒪_𝒞/f⁻¹𝒪_ℬ} ⊗_{𝒪_𝒞} 𝒪_𝒟 ⟶ NL_{𝒪_𝒟/f⁻¹𝒪_ℬ}`
followed by the relative map `NL_{𝒪_𝒟/f⁻¹𝒪_ℬ} ⟶ NL_{𝒪_𝒟/g⁻¹f⁻¹𝒪_ℬ}`, both of **Stacks 0E1Y**;
no inverse-image theorem is needed, because the identification of the topoi has already turned
`g⁻¹𝒪_𝒞` into `𝒪_𝒞`.

Two inputs of the source's proof are hypotheses, exactly as in the ringed-space twin
`AlgebraicGeometry.RingedSpaceThickening.exists_compatibleLift_iff_eq_restrictExtClass` of
**Stacks 0GQ1**. The comparison group is the `Ext¹` of the degreewise pullback
`g^*NL_{𝒪_𝒞/𝒪_ℬ}` rather than of the derived pullback `Lg^*NL_{𝒪_𝒞/𝒪_ℬ}`, and the class read
off from `ξ` is taken as its image in that group: the first of the two maps the source's proof
constructs, which goes through the derived pullback of **Stacks 06YY** and the map
`Lg^*ℱ ⟶ g^*ℱ ⟶ 𝒢`, is not built here, since degreewise extension of scalars is only right
exact and so does not descend to the derived category. And the compatibility between the
constructions in the proofs of **Stacks 0GQ5** and **Stacks 08UG**, whose statement and proof
the source omits — referring instead to **Stacks 0GQ8**, which is nowhere in this library — is
the hypothesis `hcompat` identifying the difference of the two classes with the obstruction
class of **Stacks 08UG**. What is proved from them is the source's conclusion.

The two-term structure `P` of `g^*NL_{𝒪_𝒞/𝒪_ℬ}` and the bijection `e` between the compatible
morphisms and the factorizations of the difference homomorphism through the degree `0` term —
Steps 1 to 3 of the proof of **Stacks 08UG** — are the remaining hypotheses. The vanishing
criterion `Deformation.ToposThickening.LiftDiagram.liftingObstruction_eq_zero_iff` of
**Stacks 08UG**, clause (1), no longer assumes that bijection: it is stated for the
factorizations themselves, so `e` is what transports it to the lifts of the diagram here.

The diagram is a general `LiftDiagram`, whose two base thickenings need not be trivial; the
situation of **Stacks 0GQ7**, where the two extensions are extensions of `f⁻¹𝒪_ℬ`-algebras and
of `g⁻¹f⁻¹𝒪_ℬ`-algebras, is the case in which both base reductions are invertible, as in
`Deformation.ToposThickening.RingedToposExtensionProblem.classesEquivExt`.

## References

* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7)
* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8), the remark the source
  defers the omitted compatibility to.
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1), the ringed-space twin.
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the base-change map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpaceThickening (NaiveCotangentTwoTerm)
open Stacks.SheafOfModules (naiveCotangentComplex baseChangeNaiveCotangentComplex
  baseChangeNaiveCotangentMap relativeNaiveCotangentComplexMap)

universe v u w

namespace Deformation.ToposThickening.LiftDiagram

variable {S : Type u} [Category.{v} S] {J : GrothendieckTopology S}
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (D : LiftDiagram.{v, u, max u v w} J)

/-! ### The two naive cotangent complexes and the comparison between them -/

/-- `g^*NL_{𝒪_𝒞/𝒪_ℬ}`, the degreewise pullback of the naive cotangent complex of the front
layer: the extension of scalars `NL_{𝒪_𝒞/f⁻¹𝒪_ℬ} ⊗_{𝒪_𝒞} 𝒪_𝒟` along the comparison `g`. -/
def pulledNaiveCotangentComplex :
    CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.back.O)) ℤ :=
  baseChangeNaiveCotangentComplex.{v, u, w} J D.front.OB D.front.O D.back.O D.front.f D.g

/-- `NL_{𝒪_𝒟/𝒪_ℬ}`, the naive cotangent complex of the back layer: that of `𝒪_𝒟` over the base
`g⁻¹f⁻¹𝒪_ℬ` of the back layer. -/
def relativeNaiveCotangentComplex :
    CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.back.O)) ℤ :=
  naiveCotangentComplex.{v, u, max u v w, max u v w} J D.back.OB D.back.O D.back.f

/-- The canonical comparison `g^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ NL_{𝒪_𝒟/𝒪_ℬ}`: the base-change map for
`f⁻¹𝒪_ℬ ⟶ 𝒪_𝒞 ⟶ 𝒪_𝒟` followed by the relative map for `f⁻¹𝒪_ℬ ⟶ g⁻¹f⁻¹𝒪_ℬ ⟶ 𝒪_𝒟`. -/
@[stacks 0GQ7 "the canonical comparison `g^*NL_{O_C/O_B} ⟶ NL_{O_D/O_B}` along which `ζ` is
read, for the DEGREEWISE pullback, built from the base-change and relative maps of Tag 0E1Y with
the topoi identified as in 08UG's own reduction. The derived pullback `Lg^*NL_{O_C/O_B}` of the
source's statement is NOT used: the LEFT-DERIVED extension of scalars along `O_C ⟶ O_D` is
absent from the library, degreewise extension of scalars being only right exact. Tag 08TZ is
NOT the missing input and is NOT absent from the library: it is carried as
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`, and it is about the inverse image
along a morphism of TOPOI, whereas both layers here live on the one site `J`"]
def pulledNaiveCotangentComparison :
    D.pulledNaiveCotangentComplex ⟶ D.relativeNaiveCotangentComplex :=
  baseChangeNaiveCotangentMap.{v, u, w} J D.front.OB D.front.O D.back.O D.front.f D.g ≫
    eqToHom (congrArg
      (naiveCotangentComplex.{v, u, max u v w, max u v w} J D.front.OB D.back.O)
      D.g_comm.symm) ≫
    relativeNaiveCotangentComplexMap.{v, u, w} J D.front.OB D.back.OB D.back.O D.gB D.back.f

/-! ### The two Ext groups and the map between them -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- `Ext¹_{𝒪_𝒟}(g^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`, the group in which the two classes are compared. -/
abbrev pulledExtGroup : Type _ :=
  DerivedCategory.Q.obj D.pulledNaiveCotangentComplex ⟶
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.back.O))
        0).obj D.back.G)⟦(1 : ℤ)⟧

/-- `Ext¹_{𝒪_𝒟}(NL_{𝒪_𝒟/𝒪_ℬ}, 𝒢)`, the group the class `ζ` of the extension of `𝒪_𝒟` lives
in. -/
abbrev relativeExtGroup : Type _ :=
  DerivedCategory.Q.obj D.relativeNaiveCotangentComplex ⟶
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.back.O))
        0).obj D.back.G)⟦(1 : ℤ)⟧

/-- The map `Ext¹_{𝒪_𝒟}(NL_{𝒪_𝒟/𝒪_ℬ}, 𝒢) ⟶ Ext¹_{𝒪_𝒟}(g^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`: precomposition
with the canonical comparison of the two naive cotangent complexes. -/
@[stacks 0GQ7 "the map `Ext¹(NL_{O_D/O_B}, G) ⟶ Ext¹(g^*NL_{O_C/O_B}, G)` in which `ζ` is read,
the second of the two maps the source's proof constructs. The first, through the derived pullback
of Tag 06YY and `Lg^*F ⟶ g^*F ⟶ G`, is NOT constructed here"]
def restrictExtClass (ζ : D.relativeExtGroup) : D.pulledExtGroup :=
  DerivedCategory.Q.map D.pulledNaiveCotangentComparison ≫ ζ

/-- The map in which `ζ` is read, as a homomorphism of the two `Ext` groups. -/
@[stacks 0GQ7 "the same map as an additive homomorphism; the first of the source's two maps is
not constructed here"]
def restrictExtClassHom : D.relativeExtGroup →+ D.pulledExtGroup where
  toFun := D.restrictExtClass
  map_zero' := Limits.comp_zero
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _

/-- The value of the homomorphism of `Ext` groups is the image of the class. -/
@[simp]
theorem restrictExtClassHom_apply (ζ : D.relativeExtGroup) :
    D.restrictExtClassHom ζ = D.restrictExtClass ζ := rfl

/-! ### Stacks 0GQ7 -/

/-- **Stacks Project, Tag 0GQ7.** A morphism `g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` of ringed
topoi over `(Sh(ℬ), 𝒪_ℬ)` compatible with `g` and the prescribed map `c` on the square-zero
ideals exists if and only if the classes of the two extensions have the same image in
`Ext¹_{𝒪_𝒟}(g^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)`.

Those morphisms are the concrete type `LiftDiagram.Lift` of the diagram, identified by `e` with
the factorizations of the difference homomorphism `δ` of Step 1 of the proof of **Stacks 08UG**
through the degree `0` term of `g^*NL_{𝒪_𝒞/𝒪_ℬ}`; the hypothesis `hcompat` is the compatibility
between the constructions in the proofs of **Stacks 0GQ5** and **Stacks 08UG**, which the source
omits and defers to **Stacks 0GQ8**: the difference of the two classes is the obstruction class
of **Stacks 08UG**. -/
@[stacks 0GQ7 "the equivalence, from clause (1) of Tag 08UG: a morphism of ringed topoi over the
base compatible with `g` and `c` exists exactly when the two Ext¹ classes agree. THIS IS THE
DEGREEWISE ANALOGUE, NOT THE SOURCE'S STATEMENT: the comparison group is `Ext¹(g^*NL, G)` rather
than `Ext¹(Lg^*NL, G)`, the LEFT-DERIVED extension of scalars being absent from the library (NOT
Tag 08TZ, which is carried as
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso` and is about inverse images along a
morphism of topoi, not about `Lg^*` on one site), and `ξ` is taken as its image there rather than
mapped in. Carried: the two-term structure `P` with its identification `hP`, the bijection `e`
(Steps 1 to 3 of the proof of 08UG), the Step 1 homomorphism `δ`, and `hcompat` -- the
compatibility between the constructions in the proofs of Tags 0GQ5 and 08UG whose statement and
proof THE SOURCE ITSELF OMITS, deferring to Tag 0GQ8. The same concession is made by the
ringed-space twin Tag 0GQ1"]
theorem nonempty_lift_iff_eq_restrictExtClass
    (P : NaiveCotangentTwoTerm (DerivedCategory.singleFunctor
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.back.O)) 0))
    (hP : P.obj = DerivedCategory.Q.obj D.pulledNaiveCotangentComplex)
    (δ : P.conormal ⟶ D.back.G)
    (e : D.Lift ≃ {θ : P.base ⟶ D.back.G // P.d ≫ θ = δ})
    (ξ : D.pulledExtGroup) (ζ : D.relativeExtGroup)
    (hcompat : eqToHom hP ≫ (ξ - D.restrictExtClass ζ) = P.conormalExtClass D.back.G δ) :
    Nonempty D.Lift ↔ ξ = D.restrictExtClass ζ := by
  refine Iff.trans (e.nonempty_congr.trans
    (liftingObstruction_eq_zero_iff P D.back.G δ).symm) ?_
  -- `liftingObstruction` is the conormal class of `hcompat` by definition, but only up to
  -- unfolding `Stacks.SheafOfModules.Tensor.ringSheaf D.back.O` against the spelling of the
  -- ring sheaf carried by `D.back.G`, so the equation is supplied rather than unfolded.
  rw [show AlgebraicGeometry.RingedSpaceThickening.liftingObstruction P D.back.G δ =
      eqToHom hP ≫ (ξ - D.restrictExtClass ζ) from hcompat.symm]
  constructor
  · intro h
    refine sub_eq_zero.1 ((cancel_epi (eqToHom hP)).1 ?_)
    rw [h, Limits.comp_zero]
  · intro h
    exact (congrArg (eqToHom hP ≫ ·) (sub_eq_zero.2 h)).trans Limits.comp_zero

end Derived

end Deformation.ToposThickening.LiftDiagram

end
