module

public import StacksFrontier.AlgebraicGeometry.Bridge.SchemeBridge
public import StacksFrontier.AlgebraicGeometry.Constructions.PullbackTwistSectionMul
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist
public import StacksFrontier.AlgebraicGeometry.RegularSectionSequence.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneDegreeOneSurjective
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneSequenceEveryTwist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical hyperplane restriction arrows

Let `j : ℙᵐ ⟶ ℙᵐ⁺¹` present a hyperplane, `ℱ` a sheaf of modules on `ℙᵐ⁺¹` and `𝒢 = j^*ℱ`. This
file defines the restriction arrows `ℱ(d) ⟶ j_*(𝒢(d))` in every degree by the single formula

`res d = (unit of j^* ⊣ j_*)_{ℱ(d)} ≫ j_*(c d)`,   `c d : j^*(ℱ(d)) ≅ 𝒢(d)`,

and proves the restriction sequences of [Stacks, Tag 08A0] and [Stacks, Tag 0EGK] for this
family, with multiplication by a section `s` of `𝒪(1)` as the first arrow.

## Main definitions

* `AlgebraicGeometry.pullbackTwistIso`: the isomorphism `j^*(ℱ(d)) ≅ (j^*ℱ)(d)`, the comparison of
  [Stacks, Tag 01CD] followed by an identification `θ d : j^*𝒪(d) ≅ 𝒪(d)` of the twists.
* `AlgebraicGeometry.pullbackTwistUnitRes`: the restriction arrow `ℱ(d) ⟶ j_*((j^*ℱ)(d))`, the
  unit of `j^* ⊣ j_*` followed by the direct image of `AlgebraicGeometry.pullbackTwistIso`.

## Main results

* `AlgebraicGeometry.mono_twistSectionMul_of_nonvanishing`,
  `AlgebraicGeometry.twistSectionMul_comp_hyperplaneUnit` and
  `AlgebraicGeometry.isIso_unit_app_cokernel_twistSectionMul`: the three inputs of
  [Stacks, Tag 08A0] for multiplication by `s` as the arrow `ℱ(d) ⟶ ℱ(d + 1)`.
* `AlgebraicGeometry.exists_shortExact_twistSectionMul_unit`: the short exact sequence
  `0 ⟶ ℱ(d) ⟶ ℱ(d+1) ⟶ j_*j^*(ℱ(d+1)) ⟶ 0` whose second arrow is the unit of `j^* ⊣ j_*`, for a
  `j` factoring the hyperplane inclusion through an isomorphism.
* `AlgebraicGeometry.exists_restrictionSequences_pullbackRes_forall`: over an infinite field `k`
  and for a coherent sheaf `𝒜` on `ℙᵐ⁺¹_k`, there are a hyperplane `j : ℙᵐ_k ⟶ ℙᵐ⁺¹_k`, a section
  `s` of `𝒪(1)` and an identification `θ1 : j^*𝒪(1) ≅ 𝒪(1)` such that restriction of degree-one
  forms along `j` is surjective and, for every coherent `ℱ` whose associated points are among
  those of `𝒜`, the sequence `0 ⟶ ℱ(d) ⟶ ℱ(d+1) ⟶ j_*((j^*ℱ)(d+1)) ⟶ 0` with arrows
  `twistSectionMul` and `AlgebraicGeometry.pullbackTwistUnitRes` is short exact in every degree.
* `AlgebraicGeometry.exists_restrictionSequences_pullbackRes`: the same statement for a single
  coherent sheaf `ℱ`.

## Implementation notes

The three inputs of [Stacks, Tag 08A0] are proved from the factorisation
`twistSectionMul n S ℱ s d = mulSectionOne n S (ℱ(d)) s ≫ twistAssocIso n S ℱ d`
(`AlgebraicGeometry.twistSectionMul_eq_mulSectionOne_comp`), in which the first factor is
multiplication by `s` on the module `ℱ(d)` and the second is an isomorphism. This avoids reading
the sequence with first arrow `twistSectionMulNegOne n S ℳ s : ℳ(-1) ⟶ ℳ` at `ℳ = ℱ(d+1)`, which
agrees with `twistSectionMul n S ℱ s d` only up to the coherence of the regrouping isomorphisms
`𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a+b)`.

The hypothesis on `s` is the same at every `d`, because `Ass(ℱ(d)) = Ass(ℱ)`
(`AlgebraicGeometry.associatedPoints_projectiveTwist`).

The sequence is transported from the hyperplane inclusion `i` to the composite `j = φ ≫ i` with
the identification `φ : ℙᵐ_k ≅ H` of [Stacks, Tag 089Z]:
`AlgebraicGeometry.pullback_eq_zero_of_isoComp` carries `i^*a = 0` to `j^*a = 0`, and
`AlgebraicGeometry.isIso_unit_app_of_isoComp` carries the cokernel condition across, the
essential images of `i_*` and `j_*` being equal because `φ_*φ^* ≅ 𝟭`.

## References

* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.RelativeVeryAmple

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The adjunction along a morphism factoring through an isomorphism -/

/-- **A pullback that kills an arrow still kills it after the source is reparametrised.** If
`i^*a = 0` and `j = φ ≫ i` with `φ` an isomorphism of schemes then `j^*a = 0`: the comparison
`AlgebraicGeometry.Scheme.Modules.pullbackComp` is a natural isomorphism and `φ^*` preserves zero
morphisms. -/
theorem pullback_eq_zero_of_isoComp {Pm Hy Y : Scheme.{u}} (φ : Pm ≅ Hy) (i : Hy ⟶ Y)
    {A B : Y.Modules} (a : A ⟶ B) (h : (Scheme.Modules.pullback i).map a = 0) :
    (Scheme.Modules.pullback (φ.hom ≫ i)).map a = 0 := by
  have h2 : (Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback φ.hom).map a = 0 := by
    rw [Functor.comp_map, h, (Scheme.Modules.pullback φ.hom).map_zero]
  rw [← NatIso.naturality_1 (Scheme.Modules.pullbackComp φ.hom i) a, h2, zero_comp, comp_zero]

/-- **The unit of `j^* ⊣ j_*` is an isomorphism wherever the unit of `i^* ⊣ i_*` is**, for
`j = φ ≫ i` with `φ` an isomorphism of schemes. Both units are isomorphisms at exactly the
objects in the essential image of the right adjoint, and the two essential images agree:
`j_*(φ^*𝒩) ≅ i_*(φ_*φ^*𝒩) ≅ i_*𝒩`, the unit of `φ^* ⊣ φ_*` being invertible for an isomorphism.
-/
theorem isIso_unit_app_of_isoComp {Pm Hy Y : Scheme.{u}} (φ : Pm ≅ Hy) (i : Hy ⟶ Y)
    [(Scheme.Modules.pushforward i).Full] [(Scheme.Modules.pushforward i).Faithful]
    [(Scheme.Modules.pushforward (φ.hom ≫ i)).Full]
    [(Scheme.Modules.pushforward (φ.hom ≫ i)).Faithful] (C : Y.Modules)
    (h : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app C)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (φ.hom ≫ i)).unit.app C) := by
  obtain ⟨N, ⟨e⟩⟩ := (Adjunction.isIso_unit_app_iff_mem_essImage
    (Scheme.Modules.pullbackPushforwardAdjunction i)).mp h
  refine (Adjunction.isIso_unit_app_iff_mem_essImage
    (Scheme.Modules.pullbackPushforwardAdjunction (φ.hom ≫ i))).mpr
      ⟨(Scheme.Modules.pullback φ.hom).obj N, ⟨?_⟩⟩
  exact ((Scheme.Modules.pushforwardComp φ.hom i).app
      ((Scheme.Modules.pullback φ.hom).obj N)).symm ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (Scheme.Modules.pushforwardObjIsoOfPullbackIso φ (Iso.refl _)) ≪≫ e

/-- Alias of
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.isIso_unit_app_of_isoSource`. -/
private alias isIso_unit_app_of_iso_source :=
  Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.isIso_unit_app_of_isoSource

/-! ### [Stacks, Tag 08A0] with `twistSectionMul` as its first arrow -/

section Sequence

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open CategoryTheory.MonoidalCategory
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication

variable (n : ℕ) (S : Scheme.{u})

/-- **Multiplication by `s` is a monomorphism `ℱ(d) ⟶ ℱ(d + 1)`** as soon as `s` does not vanish
near any associated point of `ℱ(d)`. -/
theorem mono_twistSectionMul_of_nonvanishing [IsLocallyNoetherian (projectiveSpaceOver n S)]
    (F : (projectiveSpaceOver n S).Modules) (s : (twistOver n S 1).sections) (d : ℤ)
    [(Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
      (twistOver n S d)).IsQuasicoherent]
    [(Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d) ⊗
        twistOver n S 1).IsQuasicoherent]
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d)),
      ∃ W : (projectiveSpaceOver n S).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (projectiveSpaceOver n S).toRingedSpace) (twistOver n S 1) s) :
    Mono (twistSectionMul n S F s d) := by
  have hpsi : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(projectiveSpaceOver n S).toRingedSpace.presheaf,
        (projectiveSpaceOver n S).toRingedSpace.IsSheaf⟩).obj (twistOver n S 1)).obj
        (twistOver n S (-1)) ≅ _root_.SheafOfModules.unit _ :=
    twistOverMulIso n S 1 (-1) ≪≫ eqToIso (congrArg (twistOver n S) (add_neg_cancel (1 : ℤ))) ≪≫
      twistZeroIsoUnit n S
  have hs : Stacks.SectionProduct.monoidalUnitHomEquiv (twistOver n S 1)
      (Stacks.SectionProduct.ofUnitHom (sectionHom (twistOver n S 1) s)) = s :=
    Stacks.SectionProduct.monoidalUnitHomEquiv_ofUnitHom_unitHomEquiv_symm (twistOver n S 1) s
  have heq : twistSectionMul n S F s d =
      Stacks.TensorSectionNonvanishing.mulRight
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d))
          (Stacks.SectionProduct.ofUnitHom (sectionHom (twistOver n S 1) s)) ≫
        (Stacks.AmplePullbackPart1.tensorIsoTensorModules (projectiveSpaceOver n S)
            (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d))
            (twistOver n S 1) ≪≫ twistAssocIso n S F d).hom := by
    rw [twistSectionMul_eq_mulSectionOne_comp, mulSectionOne_eq_mulRight_comp]
    simp only [Iso.trans_hom, Category.assoc]
  rw [heq]
  refine Stacks.SectionProduct.mono_mulRight_comp_of_associatedPoints
    (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d)) hpsi _ _
    fun x hx => ?_
  obtain ⟨W, hxW, hWL⟩ := hW x hx
  refine ⟨W, hxW, fun y hy => ?_⟩
  rw [hs]
  exact hWL y hy

/-- **The composite `ℱ(d) ⟶ ℱ(d + 1) ⟶ i_* i^* ℱ(d + 1)` vanishes**, for an arbitrary
`𝒪`-module `ℱ` on `ℙⁿ_S`: multiplication by `s` lands in `ℱ(d) ⊗ 𝒪(1)`, where the vanishing is
`AlgebraicGeometry.tensorSection_comp_unit_zeroScheme_eq_zero'`, and the identification of
`ℱ(d) ⊗ 𝒪(1)` with `ℱ(d + 1)` is carried across by naturality of the unit. -/
theorem twistSectionMul_comp_hyperplaneUnit (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) (d : ℤ) :
    twistSectionMul n S F s d ≫
        hyperplaneUnit n S
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
            (twistOver n S (d + 1))) s = 0 := by
  have h0 : mulSectionOne n S
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d)) s ≫
      (Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.app
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S)
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d))
          (twistOver n S 1)) = 0 := by
    rw [mulSectionOne_eq_rightUnitor_inv_comp]
    exact AlgebraicGeometry.tensorSection_comp_unit_zeroScheme_eq_zero' (projectiveSpaceOver n S)
      (twistOver n S 1) s
      (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d))
  calc twistSectionMul n S F s d ≫
        hyperplaneUnit n S
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
            (twistOver n S (d + 1))) s
      = mulSectionOne n S
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d)) s ≫
          ((twistAssocIso n S F d).hom ≫
            hyperplaneUnit n S
              (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
                (twistOver n S (d + 1))) s) := by
        rw [twistSectionMul_eq_mulSectionOne_comp, Category.assoc]
    _ = (mulSectionOne n S
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d)) s ≫
          (Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.app
            (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S)
              (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d))
              (twistOver n S 1))) ≫
          (Scheme.Modules.pushforward (hyperplaneι n S s)).map
            ((Scheme.Modules.pullback (hyperplaneι n S s)).map
              (twistAssocIso n S F d).hom) := by
        rw [Category.assoc, (Scheme.Modules.pullbackPushforwardAdjunction
          (hyperplaneι n S s)).unit_naturality (twistAssocIso n S F d).hom]
    _ = 0 := by rw [h0, zero_comp]

set_option synthInstance.maxHeartbeats 200000 in
/-- **The unit of `i^* ⊣ i_*` is an isomorphism at the cokernel of `ℱ(d) ⟶ ℱ(d + 1)`**, for an
arbitrary `𝒪`-module `ℱ` on `ℙⁿ_S`. That cokernel is the cokernel of multiplication by `s` into
`ℱ(d) ⊗ 𝒪(1)`, where the assertion is
`AlgebraicGeometry.isIso_unit_app_cokernel_tensorSection'`. -/
theorem isIso_unit_app_cokernel_twistSectionMul (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) (d : ℤ) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.app
      (cokernel (twistSectionMul n S F s d))) :=
  isIso_unit_app_of_iso_source _
    ((cokernelCompIsIso (mulSectionOne n S
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d)) s)
      (twistAssocIso n S F d).hom).symm ≪≫
      cokernelIsoOfEq (twistSectionMul_eq_mulSectionOne_comp n S F s d).symm)
    (isIso_unit_app_of_iso_source _
      (cokernelIsoOfEq (mulSectionOne_eq_rightUnitor_inv_comp n S
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
          (twistOver n S d)) s).symm)
      (AlgebraicGeometry.isIso_unit_app_cokernel_tensorSection' (projectiveSpaceOver n S)
        (twistOver n S 1) s
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d))))

/-! ### The sequence with the unit of `j^* ⊣ j_*` as its second arrow -/

/-- Post-composing the second arrow of a short exact sequence with an isomorphism gives a short
exact sequence with the same first arrow. -/
private theorem shortExact_comp_iso {C : Type*} [Category C] [Abelian C] {X₁ X₂ X₃ A₃ : C}
    {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {w : f ≫ g = 0}
    (hS : (ShortComplex.mk f g w).ShortExact) (e : X₃ ≅ A₃) :
    ∃ w' : f ≫ (g ≫ e.hom) = 0, (ShortComplex.mk f (g ≫ e.hom) w').ShortExact := by
  have w' : f ≫ (g ≫ e.hom) = 0 := by rw [← Category.assoc, w, zero_comp]
  exact ⟨w', ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := ShortComplex.mk f g w) (S₂ := ShortComplex.mk f (g ≫ e.hom) w')
      (Iso.refl _) (Iso.refl _) e (by simp) (by simp)) hS⟩

/-- **[Stacks, Tag 08A0] at the twist `ℱ(d)`, with the unit of `j^* ⊣ j_*` as its second arrow**,
for `j = φ ≫ i` the hyperplane inclusion composed with an identification `φ` of the hyperplane
with another scheme — on `ℙᵐ_k` that identification is [Stacks, Tag 089Z]. The sequence is

`0 ⟶ ℱ(d) ⟶ ℱ(d + 1) ⟶ j_* j^* (ℱ(d + 1)) ⟶ 0`,

with first arrow `…ProjectiveSpaceSectionMultiplication.twistSectionMul` and second arrow the
unit. -/
theorem exists_shortExact_twistSectionMul_unit [IsLocallyNoetherian (projectiveSpaceOver n S)]
    (F : (projectiveSpaceOver n S).Modules) (s : (twistOver n S 1).sections) (d : ℤ)
    [(Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
      (twistOver n S d)).IsQuasicoherent]
    [(Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d) ⊗
        twistOver n S 1).IsQuasicoherent]
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F (twistOver n S d)),
      ∃ W : (projectiveSpaceOver n S).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (projectiveSpaceOver n S).toRingedSpace) (twistOver n S 1) s)
    {Pm : Scheme.{u}} (φ : Pm ≅ (hyperplane n S s).subscheme) :
    ∃ w : twistSectionMul n S F s d ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (φ.hom ≫ hyperplaneι n S s)).unit.app
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
            (twistOver n S (d + 1))) = 0,
      (ShortComplex.mk (twistSectionMul n S F s d)
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (φ.hom ≫ hyperplaneι n S s)).unit.app
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
            (twistOver n S (d + 1)))) w).ShortExact := by
  have := mono_twistSectionMul_of_nonvanishing n S F s d hW
  have hz : twistSectionMul n S F s d ≫
      (Scheme.Modules.pullbackPushforwardAdjunction (φ.hom ≫ hyperplaneι n S s)).unit.app
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOver n S) F
          (twistOver n S (d + 1))) = 0 :=
    comp_unit_eq_zero_of_pullback_eq_zero _ _
      (pullback_eq_zero_of_isoComp φ (hyperplaneι n S s) _
        (pullback_eq_zero_of_comp_unit_eq_zero (hyperplaneι n S s) _
          (twistSectionMul_comp_hyperplaneUnit n S F s d)))
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (φ.hom ≫ hyperplaneι n S s)).unit.app (cokernel (twistSectionMul n S F s d))) :=
    isIso_unit_app_of_isoComp φ (hyperplaneι n S s) _
      (isIso_unit_app_cokernel_twistSectionMul n S F s d)
  exact Stacks.RegularSectionSequence.shortExact_of_mono_of_exists_cokernelIso _ _
    (Stacks.RegularSectionSequence.exists_cokernelIso_of_isIso_unit_app
      (Scheme.Modules.pullbackPushforwardAdjunction (φ.hom ≫ hyperplaneι n S s))
      (twistSectionMul n S F s d) hz)

end Sequence

/-! ### The canonical restriction arrows -/

section Res

variable {R : Type u} [CommRing R] {m : ℕ}
  (j : projectiveSpaceOverRing m (CommRingCat.of R) ⟶
    projectiveSpaceOverRing (m + 1) (CommRingCat.of R))
  (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of R)).Modules)
  (θ : ∀ d : ℤ, (Scheme.Modules.pullback j).obj
      (twistOver (m + 1) (Spec (CommRingCat.of R)) d) ≅
    twistOver m (Spec (CommRingCat.of R)) d)

/-- **The restriction of a twist to the hyperplane, `j^*(ℱ(d)) ≅ 𝒢(d)` with `𝒢 = j^*ℱ`**: the
comparison of [Stacks, Tag 01CD] followed by an identification `θ d : j^*𝒪(d) ≅ 𝒪(d)` of the
twists. -/
def pullbackTwistIso (d : ℤ) :
    (Scheme.Modules.pullback j).obj (projectiveTwist (m + 1) F d) ≅
      projectiveTwist m ((Scheme.Modules.pullback j).obj F) d :=
  Stacks.RelativeVeryAmple.pullbackTensorModulesIso j F
      (twistOver (m + 1) (Spec (CommRingCat.of R)) d) ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso (projectiveSpaceOverRing m (CommRingCat.of R))
      (Iso.refl ((Scheme.Modules.pullback j).obj F)) (θ d)

/-- **The canonical restriction arrow `ℱ(d) ⟶ j_*(𝒢(d))` of [Stacks, Tag 08A7]**, for
`𝒢 = j^*ℱ`: the unit of `j^* ⊣ j_*` followed by the direct image of
`AlgebraicGeometry.pullbackTwistIso`. -/
def pullbackTwistUnitRes (d : ℤ) :
    projectiveTwist (m + 1) F d ⟶
      (Scheme.Modules.pushforward j).obj
        (projectiveTwist m ((Scheme.Modules.pullback j).obj F) d) :=
  (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app (projectiveTwist (m + 1) F d) ≫
    ((Scheme.Modules.pushforward j).mapIso (pullbackTwistIso j F θ d)).hom

end Res

/-! ### The restriction sequences with the canonical arrows -/

section Field

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open CategoryTheory.MonoidalCategory
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.AlgebraicGeometry.ProjectiveSpaceHyperplaneSection
  (mono_twistSectionMulNegOne_of_nonvanishing)

/-- For a coherent `ℱ` on `ℙⁿ_k`, the module `ℱ(d) ⊗ 𝒪(1)` is quasi-coherent. -/
theorem isQuasicoherent_tensorModules_twistOver_tensor (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent] (d : ℤ) :
    (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (CommRingCat.of k)) F
        (twistOver n (Spec (CommRingCat.of k)) d) ⊗
      twistOver n (Spec (CommRingCat.of k)) 1).IsQuasicoherent := by
  have : (projectiveTwist n F d).IsCoherent := isCoherent_projectiveTwist n F d
  have : (projectiveTwist n (projectiveTwist n F d) 1).IsCoherent :=
    isCoherent_projectiveTwist n (projectiveTwist n F d) 1
  exact (SheafOfModules.isQuasicoherent
      (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf).prop_of_iso
    (Stacks.AmplePullbackPart1.tensorIsoTensorModules
      (projectiveSpaceOverRing n (CommRingCat.of k))
      (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (CommRingCat.of k)) F
        (twistOver n (Spec (CommRingCat.of k)) d))
      (twistOver n (Spec (CommRingCat.of k)) 1)).symm
    (isQuasicoherent_of_isCoherent (projectiveTwist n (projectiveTwist n F d) 1))

/-- If the associated points of `ℱ` lie in the nonvanishing locus of a section `s` of `𝒪(1)`, then
every associated point of `ℱ(d)` has an open neighbourhood on which `s` does not vanish. -/
theorem exists_isOpen_nonvanishing_of_associatedPoints_subset (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (s : (twistOver n (Spec (CommRingCat.of k)) 1).sections)
    (hF : Stacks.Divisors.associatedPoints F ⊆
      Stacks.Ample.nonvanishingLocus (twistOver n (Spec (CommRingCat.of k)) 1)
        (PresheafOfModules.sections.eval s (op ⊤))) (d : ℤ) :
    ∀ x ∈ Stacks.Divisors.associatedPoints
      (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (CommRingCat.of k)) F
        (twistOver n (Spec (CommRingCat.of k)) d)),
      ∃ W : (projectiveSpaceOverRing n (CommRingCat.of k)).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (twistOver n (Spec (CommRingCat.of k)) 1) s := by
  intro x hx
  have hA : Stacks.Divisors.associatedPoints
      (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (CommRingCat.of k)) F
        (twistOver n (Spec (CommRingCat.of k)) d))
      = Stacks.Divisors.associatedPoints F :=
    associatedPoints_projectiveTwist n F d
  refine ⟨Stacks.NonvanishingOpen.nonvanishingOpen
    (projectiveSpaceOverRing n (CommRingCat.of k))
    (twistOver n (Spec (CommRingCat.of k)) 1)
    (PresheafOfModules.sections.eval s (op ⊤)), hF (hA.subset hx), fun y hy => ?_⟩
  rwa [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq
    (projectiveSpaceOverRing n (CommRingCat.of k))
    (twistOver n (Spec (CommRingCat.of k)) 1) s]

/-- **One hyperplane for every coherent sheaf whose associated points it avoids: the restriction
sequences of [Stacks, Tag 08A0] and [Stacks, Tag 0EGK] with the canonical restriction arrows, over
an infinite field.**

Let `k` be an infinite field and `𝒜` a coherent sheaf on `ℙ^{m+1}_k`. Then there are a morphism
`j : ℙᵐ_k ⟶ ℙ^{m+1}_k` that is affine, a closed immersion and a morphism over `Spec k`, a global
section `s` of `𝒪(1)` cutting out a hyperplane that `j` presents as `ℙᵐ_k` — the factorisation
`j = φ ≫ i` through the hyperplane inclusion is reported, `φ` being the identification of
[Stacks, Tag 089Z] — and an identification `θ1 : j^*𝒪(1) ≅ 𝒪(1)`, such that for **every** coherent
`ℱ` whose associated points are among those of `𝒜`, multiplication by `s` is a monomorphism
`ℱ(-1) ⟶ ℱ` and, for every family `θ` of identifications of the twists and every `d : ℤ`,

`0 ⟶ ℱ(d) ⟶ ℱ(d + 1) ⟶ j_*(𝒢(d + 1)) ⟶ 0`,  `𝒢 = j^*ℱ`,

is short exact with first arrow `…ProjectiveSpaceSectionMultiplication.twistSectionMul` and
second arrow `AlgebraicGeometry.pullbackTwistUnitRes j ℱ θ (d + 1)`. Moreover, restriction along
`j` followed by `θ1` is surjective on global sections of `𝒪(1)`. -/
@[sga "6 XIII 1.3" "partial"]
theorem exists_restrictionSequences_pullbackRes_forall (k : Type u) [Field k] [Infinite k]
    (m : ℕ) (A : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules)
    (hAc : A.IsCoherent) :
    ∃ (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶
        projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) (_ : IsAffineHom j)
      (_ : IsClosedImmersion j)
      (_ : j ≫ (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘
          Spec (CommRingCat.of k)) =
        projectiveSpaceOverRing m (CommRingCat.of k) ↘ Spec (CommRingCat.of k))
      (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections)
      (φ : projectiveSpaceOverRing m (CommRingCat.of k) ≅
        (hyperplane (m + 1) (Spec (CommRingCat.of k)) s).subscheme)
      (θ1 : (Scheme.Modules.pullback j).obj (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) ≅
        twistOver m (Spec (CommRingCat.of k)) 1),
      j = φ.hom ≫ hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s ∧
      (Function.Surjective fun x : Γ(twistOver (m + 1) (Spec (CommRingCat.of k)) 1, ⊤) =>
          θ1.hom.app ⊤ (pullbackGlobalSections j
            (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) x)) ∧
      ∀ (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules) (_ : F.IsCoherent),
        Stacks.Divisors.associatedPoints F ⊆ Stacks.Divisors.associatedPoints A →
        Mono (twistSectionMulNegOne (m + 1) (Spec (CommRingCat.of k)) F s) ∧
        ∀ (θ : ∀ d : ℤ, (Scheme.Modules.pullback j).obj
              (twistOver (m + 1) (Spec (CommRingCat.of k)) d) ≅
            twistOver m (Spec (CommRingCat.of k)) d) (d : ℤ),
          ∃ w : twistSectionMul (m + 1) (Spec (CommRingCat.of k)) F s d ≫
              pullbackTwistUnitRes j F θ (d + 1) = 0,
            (ShortComplex.mk (twistSectionMul (m + 1) (Spec (CommRingCat.of k)) F s d)
              (pullbackTwistUnitRes j F θ (d + 1)) w).ShortExact := by
  have : IsLocallyNoetherian (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian (m + 1) (Spec (CommRingCat.of k))
  obtain ⟨f, hf, v, hf0, hv, hsub⟩ := exists_form_section_nonvanishing k (m + 1) A
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv
    (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
    (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)).symm v with hs
  have hsv : PresheafOfModules.sections.eval s (op ⊤) = v := by
    rw [hs, ← Stacks.NonvanishingSpelling.sectionsEquiv_apply, Equiv.apply_symm_apply]
  rw [← hsv] at hv hsub
  obtain ⟨φ, ⟨eφ⟩, hφover⟩ := exists_iso_zeroScheme_projectiveSpaceOverRing k m f hf hf0
    (PresheafOfModules.sections.eval s (op ⊤)) hv
  set i := hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s with hi
  set j := φ.hom ≫ i with hj
  have : IsAffineHom j := by rw [hj]; infer_instance
  have : IsClosedImmersion j := by rw [hj]; infer_instance
  have hjover : j ≫ (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘
        Spec (CommRingCat.of k)) =
      projectiveSpaceOverRing m (CommRingCat.of k) ↘ Spec (CommRingCat.of k) := by
    rw [hj, hi, Category.assoc]
    exact hφover
  refine ⟨j, inferInstance, inferInstance, hjover, s, φ, eφ, hj,
    surjective_restriction_zeroScheme k m f hf hf0
      (PresheafOfModules.sections.eval s (op ⊤)) hv φ eφ, fun F hFc hAss => ?_⟩
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hq (d : ℤ) : (projectiveTwist (m + 1) F d).IsQuasicoherent :=
    have := isCoherent_projectiveTwist (m + 1) F d
    isQuasicoherent_of_isCoherent _
  have hW := exists_isOpen_nonvanishing_of_associatedPoints_subset k (m + 1) F s (hAss.trans hsub)
  refine ⟨?_, fun θ d => ?_⟩
  · have := hq (-1)
    have := isQuasicoherent_tensorModules_twistOver_tensor k (m + 1) F (-1)
    exact mono_twistSectionMulNegOne_of_nonvanishing (m + 1) (Spec (CommRingCat.of k)) F s
      (hW (-1))
  · have := hq d
    have := isQuasicoherent_tensorModules_twistOver_tensor k (m + 1) F d
    obtain ⟨w0, hSE⟩ := exists_shortExact_twistSectionMul_unit (m + 1)
      (Spec (CommRingCat.of k)) F s d (hW d) φ
    exact shortExact_comp_iso hSE
      ((Scheme.Modules.pushforward j).mapIso (pullbackTwistIso j F θ (d + 1)))

/-- **The hyperplane restriction sequences of [Stacks, Tag 08A0] and [Stacks, Tag 0EGK] with the
canonical restriction arrows, over an infinite field.**

For a coherent sheaf `ℱ` on `ℙ^{m+1}_k` there are a closed immersion `j : ℙᵐ_k ⟶ ℙ^{m+1}_k` over
`Spec k`, along which `ℱ` pulls back to a coherent sheaf, a section `s` of `𝒪(1)` and an
identification `θ1 : j^*𝒪(1) ≅ 𝒪(1)` such that restriction along `j` followed by `θ1` is
surjective on global sections of `𝒪(1)` and, for every family `θ` of identifications of the twists
and every `d : ℤ`, the sequence `0 ⟶ ℱ(d) ⟶ ℱ(d + 1) ⟶ j_*((j^*ℱ)(d + 1)) ⟶ 0` with arrows
`twistSectionMul` and `AlgebraicGeometry.pullbackTwistUnitRes j ℱ θ (d + 1)` is short exact. -/
theorem exists_restrictionSequences_pullbackRes (k : Type u) [Field k] [Infinite k] (m : ℕ)
    (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules) (hFc : F.IsCoherent) :
    ∃ (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶
        projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) (_ : IsAffineHom j)
      (_ : IsClosedImmersion j)
      (_ : j ≫ (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘
          Spec (CommRingCat.of k)) =
        projectiveSpaceOverRing m (CommRingCat.of k) ↘ Spec (CommRingCat.of k))
      (_ : ((Scheme.Modules.pullback j).obj F).IsCoherent)
      (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections)
      (θ1 : (Scheme.Modules.pullback j).obj (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) ≅
        twistOver m (Spec (CommRingCat.of k)) 1),
      (Function.Surjective fun x : Γ(twistOver (m + 1) (Spec (CommRingCat.of k)) 1, ⊤) =>
          θ1.hom.app ⊤ (pullbackGlobalSections j
            (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) x)) ∧
      ∀ (θ : ∀ d : ℤ, (Scheme.Modules.pullback j).obj
            (twistOver (m + 1) (Spec (CommRingCat.of k)) d) ≅
          twistOver m (Spec (CommRingCat.of k)) d) (d : ℤ),
        ∃ w : twistSectionMul (m + 1) (Spec (CommRingCat.of k)) F s d ≫
            pullbackTwistUnitRes j F θ (d + 1) = 0,
          (ShortComplex.mk (twistSectionMul (m + 1) (Spec (CommRingCat.of k)) F s d)
            (pullbackTwistUnitRes j F θ (d + 1)) w).ShortExact := by
  obtain ⟨j, hjaff, hjci, hjover, s, φ, θ1, -, hres, hall⟩ :=
    exists_restrictionSequences_pullbackRes_forall k m F hFc
  have : IsLocallyNoetherian (projectiveSpaceOverRing m (CommRingCat.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian m (Spec (CommRingCat.of k))
  exact ⟨j, hjaff, hjci, hjover, isCoherent_pullback j F, s, θ1, hres,
    (hall F hFc (subset_refl _)).2⟩

end Field

end AlgebraicGeometry

end
