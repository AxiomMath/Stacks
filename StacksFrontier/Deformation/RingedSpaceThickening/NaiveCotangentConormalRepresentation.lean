module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentationClass
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExtClassRepresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Every class of `Ext¹(𝖭𝖫_{X/S}, 𝒢)` is the class of a conormal homomorphism (Stacks 08UB)

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module.
**Stacks 08UB** says every class of `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` becomes, over a suitable family
of generators `α : ℰ ⟶ 𝒪_X`, the class of a homomorphism `𝒥/𝒥² ⟶ 𝒢` out of the conormal sheaf
of the presentation of `𝒪_X` by `ℰ`. The tag is proved in the library as
`Stacks.SheafOfModules.ConormalRepresentative.exists_enlargement_conormalExtClass`, whose
conclusion is stated with `Stacks.SheafOfModules.presentationConormalExtClass`; this file
restates it in the two-term idiom of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionPresentationClass.lean`, where the class
of a conormal homomorphism is
`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.conormalExtClass` of
`PresentedSquareZeroExtension.twoTerm` and is transported to `𝖭𝖫_{X/S}` through
`PresentedSquareZeroExtension.naiveCotangentIso`.

The two spellings of the class are not identified here. What is used instead is that the
`presentationConormalExtClass` spelling has *vanishing obstruction* — vanishing restriction
along the inclusion of the degree `0` term `Ω` — and that
`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.obstruction_eq_zero_iff` then
produces a conormal homomorphism in the other spelling. The obstruction vanishes for a cheap
reason: `presentationConormalExtClass` is, by construction, a chain map out of `𝖭𝖫(α)` into `𝒢`
placed in degree `-1`, composed with an identification of shifts; restricting it to the degree
`0` term gives a chain map from a complex concentrated in degree `0` to one concentrated in
degree `-1`, and there is only one such map.

## Main results

* `CochainComplex.eq_zero_of_single_hom_single`: a chain map between single complexes
  concentrated in two different degrees is zero.
* `AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.obstruction_ofDouble_Q_map_comp`:
  **the obstruction of a class presented by a chain map into the degree `i₀` term vanishes.**
* `Stacks.SheafOfModules.obstruction_presentationConormalExtClass`: the same for the class of a
  conormal homomorphism of a polynomial presentation, at a general site.
* `AlgebraicGeometry.RingedSpaceThickening.exists_conormalRepresentative`: **Stacks 08UB in the
  two-term idiom** — every class of `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is
  `(naiveCotangentIso f ℰ α).inv ≫ (twoTerm f ℰ α).conormalExtClass 𝒢 δ` for some surjective
  family of generators `α : ℰ ⟶ 𝒪_X` and some `δ : 𝒥/𝒥² ⟶ 𝒢`.

## Implementation notes

`Stacks.SheafOfModules.ConormalRepresentative.exists_enlargement_conormalExtClass` ties the
universe of the derived category to the universe of the sheaves, which over a ringed space
`X : RingedSpace.{u, u}` would force the structure sheaf into `CommRingCat.{u + 1}`:
`HasDerivedCategory.standard` for `SheafOfModules.{u} (ringSheaf X.sheaf)` has
universe `u + 1`, since the objects of that category live in `Type (u + 1)`. The theorem the
tag's statement wraps, `Stacks.SheafOfModules.exists_presentation_conormalExtClass`
(**Stacks 08UJ**), keeps the two universes separate, so it is the one instantiated below.

`Stacks.SheafOfModules.obstruction_presentationConormalExtClass` is stated at a general site and
instantiated, rather than being proved over the opens of a topological space: there the
structure sheaf arrives in the two definitionally equal spellings `X.sheaf` and
`Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat`, and a `rw` whose motive mentions one
of them fails on the other — the same reason
`Stacks.SheafOfModules.presentationConormalExtClass_eq` of
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentPresentationExtClass.lean` is kept
general. For the same reason the instantiation below composes `congrArg` and `Eq.trans` instead
of rewriting.

`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.obstruction_ofDouble_Q_map_comp`
takes the identification of shifts as an opaque morphism `s`: nothing about it is used beyond
the composite being zero on the left, so the lemma applies to any class of that shape and the
`shiftIso` of `presentationConormalExtClass` never has to be unfolded.

## References

* [Stacks Project, Tag 08UB](https://stacks.math.columbia.edu/tag/08UB)
* [Stacks Project, Tag 08UJ](https://stacks.math.columbia.edu/tag/08UJ)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpaceThickening (NaiveCotangentTwoTerm)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe t w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **A chain map between single complexes concentrated in two different degrees is zero.** In
every degree one of the two complexes is a zero object: the source away from `i`, the target
away from `j`. -/
theorem eq_zero_of_single_hom_single {A B : C} {i j : ℤ} (hij : i ≠ j)
    (m : (HomologicalComplex.single C (ComplexShape.up ℤ) i).obj A ⟶
      (HomologicalComplex.single C (ComplexShape.up ℤ) j).obj B) : m = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun k ↦ ?_
  by_cases hk : k = i
  · subst hk
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j B k hij).eq_of_tgt _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i A k hk).eq_of_src _ _

variable [HasDerivedCategory.{w} C]

/-- **The inclusion of the degree `i₁` term of a two-term complex kills every chain map into the
degree `i₀` term.** The inclusion is, in the derived category, the image of the inclusion of the
target in the mapping cone, so the composite is the image of a chain map from a complex
concentrated in degree `i₁` to one concentrated in degree `i₀`, and `i₀ ≠ i₁`. -/
theorem doubleInclQ_comp_Q_map {X₀ X₁ : C} (d : X₀ ⟶ X₁) {i₀ i₁ : ℤ}
    (hi₀₁ : (ComplexShape.up ℤ).Rel i₀ i₁) (G : C)
    (m : HomologicalComplex.double d hi₀₁ ⟶
      (HomologicalComplex.single C (ComplexShape.up ℤ) i₀).obj G) :
    doubleInclQ d hi₀₁ ≫ DerivedCategory.Q.map m = 0 := by
  have hne : i₁ ≠ i₀ := by
    rintro rfl
    exact (ComplexShape.up ℤ).not_rel_self _ hi₀₁
  have hz : mappingCone.inr ((HomologicalComplex.single C (ComplexShape.up ℤ) i₁).map d) ≫
      ((doubleIsoMappingCone d hi₀₁).inv ≫ m) = 0 :=
    eq_zero_of_single_hom_single hne _
  rw [doubleInclQ, Functor.mapIso_inv, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    hz, Functor.map_zero]

end CochainComplex

namespace AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **A class of a `double`-built two-term complex presented by a chain map into its degree `i₀`
term has vanishing obstruction.** The obstruction is the restriction along the inclusion of the
degree `i₁` term, and that inclusion kills every such chain map by
`CochainComplex.doubleInclQ_comp_Q_map`; the identification of shifts `s` the class is composed
with plays no role. -/
theorem obstruction_ofDouble_Q_map_comp {X₀ X₁ G' : C} (d : X₀ ⟶ X₁) {i₀ i₁ : ℤ}
    (hi₀₁ : (ComplexShape.up ℤ).Rel i₀ i₁) (G : C)
    (m : HomologicalComplex.double d hi₀₁ ⟶
      (HomologicalComplex.single C (ComplexShape.up ℤ) i₀).obj G')
    (s : DerivedCategory.Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) i₀).obj G') ⟶
      ((DerivedCategory.singleFunctor C i₁).obj G)⟦(1 : ℤ)⟧) :
    (ofDouble d hi₀₁).obstruction G (DerivedCategory.Q.map m ≫ s) = 0 := by
  show CochainComplex.doubleInclQ d hi₀₁ ≫ DerivedCategory.Q.map m ≫ s = 0
  rw [← Category.assoc, CochainComplex.doubleInclQ_comp_Q_map, Limits.zero_comp]

end AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{max w u v}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})]
  (A B : Sheaf J CommRingCat.{max w u v}) (a : A ⟶ B)
  (E : Functor Cᵒᵖ (Type (max w u v))) (α : E ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]
  [HasSheafify J AddCommGrpCat.{max w u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v}]
  [HasDerivedCategory.{t} (_root_.SheafOfModules.{max w u v} (ringSheaf B))]
  (G : _root_.SheafOfModules.{max w u v} (ringSheaf B))

omit [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})] in
/-- **The class of a conormal homomorphism of a polynomial presentation has vanishing
obstruction**: its restriction to the degree `0` term `Ω` of `𝖭𝖫(α)` is zero. The class is by
construction a chain map into `𝒢` placed in degree `-1`, so this is
`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.obstruction_ofDouble_Q_map_comp`
read at the conormal sequence of the presentation. -/
theorem obstruction_presentationConormalExtClass
    (δ : (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).X₁ ⟶ G) :
    (NaiveCotangentTwoTerm.ofDoubleNegOne
          (presentationConormalSequence.{v, u, max w u v, w} J A B a E α).f).obstruction G
        (presentationConormalExtClass.{v, u, w, t} J A B a E α G δ) = 0 :=
  NaiveCotangentTwoTerm.obstruction_ofDouble_Q_map_comp _ _ _ _ _

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSpaceThickening

open PresentedSquareZeroExtension

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 08UB.** Every class of `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is the class of a
homomorphism `δ : 𝒥/𝒥² ⟶ 𝒢` out of the conormal sheaf of a suitable family of generators
`α : ℰ ⟶ 𝒪_X` of `𝒪_X` over `f⁻¹𝒪_S`, transported to `𝖭𝖫_{X/S}` through the quasi-isomorphism
of **Stacks 08TL**.

The family of generators comes with the class and is not a refinement of a prescribed one; that
is all the source gives, and it is all that is needed where the acting group of the torsor of
**Stacks 08UC** is the presentation-free `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`. -/
@[stacks 08UB "over a ringed space, in the two-term idiom of NaiveCotangentTwoTerm: the class \
of a conormal homomorphism of a family of generators produced with it, transported to 𝖭𝖫_{X/S}"]
theorem exists_conormalRepresentative (ξ : relativeObj f ⟶ shiftedSingleObj G) :
    ∃ (E : Functor (Opens X.carrier)ᵒᵖ (Type u))
      (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
      (hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
        (generatorsPresentation f E α).hom),
      letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
        (generatorsPresentation f E α).hom := hsurj
      ∃ δ : (twoTerm f E α).conormal ⟶ G,
        (naiveCotangentIso f E α).inv ≫ (twoTerm f E α).conormalExtClass G δ = ξ := by
  obtain ⟨E, α, hsurj, δ₀, heq⟩ := Stacks.SheafOfModules.exists_presentation_conormalExtClass
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
    (structureRingMap f) G ξ
  refine ⟨E.obj, α, hsurj, ?_⟩
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation f E.obj α).hom := hsurj
  have hobst : (twoTerm f E.obj α).obstruction G
      (DerivedCategory.Q.map (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
          (structureRingMap f) E.obj α) ≫ ξ) = 0 :=
    (congrArg ((twoTerm f E.obj α).obstruction G) heq).trans
      (Stacks.SheafOfModules.obstruction_presentationConormalExtClass
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
        (structureRingMap f) E.obj α G δ₀)
  obtain ⟨δ, hδ⟩ := ((twoTerm f E.obj α).obstruction_eq_zero_iff G _).1 hobst
  refine ⟨δ, ?_⟩
  have h1 : (naiveCotangentIso f E.obj α).inv ≫ (twoTerm f E.obj α).conormalExtClass G δ =
      (naiveCotangentIso f E.obj α).inv ≫ ((naiveCotangentIso f E.obj α).hom ≫ ξ) :=
    congrArg ((naiveCotangentIso f E.obj α).inv ≫ ·) hδ.symm
  exact h1.trans (Iso.inv_hom_id_assoc _ _)

end Derived

end AlgebraicGeometry.RingedSpaceThickening

end
