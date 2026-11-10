module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSuccessor
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalRightUnitorCompare
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoNonvanishingTwist

/-!
# Multiplication by a section is a monomorphism on the punctured-spectrum member of a twist

The second clause of `Stacks.Algebraization.HasHilbertInductionStep` — the short exact sequences
of the induction step of [Stacks, Tag 0F27] — owes the monicity of both members of
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`. This file discharges it on the
punctured-spectrum member.

## The gap this closes, and the one bridge it needed

`Stacks.SectionProduct.mono_mulRight_of_associatedPoints` already proves monicity of
`Stacks.TensorSectionNonvanishing.mulRight` at an *arbitrary* quasi-coherent domain, and
`Stacks.Algebraization.whiskerLeft_mulSectionPowScheme` already writes the member of
`mulSectionTwistZ` as `(ρ_ _).inv ≫ _ ◁ σ`, which is the body of `mulRight`. What kept the two
apart is that they are written in **two different localizations of the sectionwise tensor product
of presheaves of modules**, and those differ in the unit datum alone:

* the twists of a coherent triple are written in `Stacks.SheafOfModules.Strict.monoidalCategory`,
  whose tensor product is `Stacks.RelativeVeryAmple.tensorModules` and whose unit is
  `Stacks.Ample.unitModule` — both on the nose, which is why a section of `L` appears there as
  `σ : Stacks.Ample.unitModule X ⟶ L`;
* `mulRight` is written in `Stacks.SheafInternalHom.monoidalCategory`, whose unit is the
  *sheafification* of the presheaf unit, so it takes a section as `f : 𝟙_ X.Modules ⟶ L`.

Elaborating `mulRight M σ` is therefore an application type mismatch, and the two right unitors
are not the same morphism. `Stacks.SectionProduct.ofUnitHom` repairs the section's type;
`Stacks.Algebraization.rightUnitor_inv_comp_whiskerLeft` below repairs the unitor, and it is
three short steps, not the construction inside `CategoryTheory.Localization.Monoidal` an earlier
reading of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertInduction` expected:

* the left whiskering of the strict structure is the sheafified presheaf whiskering, by
  `Stacks.SheafOfModules.sheafifyWhiskerLeft_eq_comparison`;
* its right unitor is the fixed unit constraint of [Stacks, Tag 01CU], by
  `Stacks.SheafOfModules.tensorProductRightUnitor_eq_comparison` together with
  `Stacks.SheafOfModules.Strict.rightUnitor_hom_aux`, which absorbs the one identity factor by
  which the two statements differ;
* and the composite of those two *is* `mulRight` of the re-seated section, which is already
  proved: `AlgebraicGeometry.tensorProductRightUnitor_inv_comp_sheafifyWhiskerLeft`, whose own
  proof is where the comparison of the two localized right unitors
  (`AlgebraicGeometry.rightUnitor_sheafOfModulesMonoidal_hom`) is paid.

## Main results

* `Stacks.Algebraization.rightUnitor_inv_comp_whiskerLeft`: **multiplication of a module by a
  global section in the strict monoidal structure is `Stacks.TensorSectionNonvanishing.mulRight`
  of the re-seated section**, followed by the comparison of the two tensor products.
* `Stacks.Algebraization.tensorModulesMap_id_eq_whiskerLeft`: the bifunctor `.map` spelling of
  the tensor product that the twists use is left whiskering.
* `Stacks.Algebraization.mono_tensorModulesMap_id_mulSectionPowScheme`: **multiplication of
  `F ⊗ L^{⊗ n}` by a section of `L` nonvanishing near every associated point of `F` is a
  monomorphism**, in the spelling the twists of a coherent triple are written in.
* `Stacks.Algebraization.CoherentTriple.mono_onPunctured_mulSectionTwistZ`: **the
  punctured-spectrum member of `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` is a
  monomorphism**, which is the clause of the induction step this file is for.

## What is still owed

**The closed-fibre member.** Nothing *here* addresses `onClosedFibre`: it is the same statement
for `closedFibre A f` and `σ₀`, and it is the second corollary of
`mono_tensorModulesMap_id_mulSectionPowScheme`, taken in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleMonoClosedFibre` as
`Stacks.Algebraization.CoherentTriple.mono_onClosedFibre_mulSectionTwistZ`. Its nonvanishing
hypothesis about `Ass(T.F₀)` is supplied at the closed point, and the supplier is the *opening
reduction* of the induction step rather than the section pair:
`Stacks.Algebraization.CoherentTriple.not_isAssociatedPoint_closedPoint_quotientTriple`. What is
genuinely owed there is the nonvanishing of `σ₀` over the punctured closed fibre, carried from
the `σ` of `Stacks.Algebraization.exists_section_nonvanishing_on_associatedPoints` across
`T.alpha`.

**The hypothesis is stated at the shape `mono_mulRight_of_associatedPoints` consumes**, namely one
open neighbourhood per associated point inside
`Stacks.SheafOfModules.nonvanishingLocus`. `exists_section_nonvanishing_on_associatedPoints`
produces its nonvanishing open as `Stacks.NonvanishingOpen.nonvanishingOpen` and its section as an
element of `Γ(L.F, ⊤)` rather than through
`AlgebraicGeometry.SheafOfModules.unitHomEquiv`; identifying those two spellings is not done here
and is what stands between this file and a hypothesis-free statement.

**Quasi-coherence is taken as a hypothesis**, following the precedent of
`Stacks.SectionProduct.mono_mulRight_tensorPowScheme_of_associatedPoints`: the members of a twist
are coherent by construction, but deriving quasi-coherence of the *monoidal* tensor product from
that needs the general-site instance whose sheafification hypotheses are not shown to specialise
to a scheme's Zariski site.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory IsLocalRing
open Stacks.RelativeVeryAmple
open Stacks.SectionProduct (hStruct ofUnitHom monoidalUnitHomEquiv)
open Stacks.SheafOfModules (sheafifyWhiskerLeft sheafifyTensorHom sheafifyFunctor)
open Stacks.SheafOfModules.Invertible (tensorProductRightUnitor)
open Stacks.TensorSectionNonvanishing (mulRight)

universe u

namespace Stacks.Algebraization

/-! The monoidal structure every statement below is written in is
`Stacks.Algebraization.strictModulesMonoidal`, the one the twists of a coherent triple use: the
tensor product sheaf of [Stacks, Tag 01CA] with `Stacks.RelativeVeryAmple.tensorModules` as its
tensor product and `Stacks.Ample.unitModule` as its unit, both on the nose. It is re-registered
here as a `local instance`, as in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSuccessor` where it is
declared. -/

attribute [local instance] strictModulesMonoidal

variable {X : Scheme.{u}}

/-- Congruence for a two-fold composite. Isolated as a lemma because the statements below mention
two monoidal structures at once, and such a goal is not type-correct at the reducible
transparency at which `rw` checks its motive; inside this lemma only one spelling occurs. -/
private theorem comp_congr {C : Type*} [Category C] {A B D : C} {a a' : A ⟶ B} {b b' : B ⟶ D}
    (h1 : a = a') (h2 : b = b') : a ≫ b = a' ≫ b' := by rw [h1, h2]

/-! ### The strict structure's unitor and whiskering, against `mulRight` -/

/-- Left whiskering in the strict monoidal structure is the sheafification of left whiskering of
presheaves of modules. -/
theorem whiskerLeft_eq_sheafifyWhiskerLeft (M : X.Modules) {N N' : X.Modules} (g : N ⟶ N') :
    M ◁ g = sheafifyWhiskerLeft X.presheaf (hStruct X) M g :=
  (Stacks.SheafOfModules.sheafifyWhiskerLeft_eq_comparison X.presheaf (hStruct X) M g).symm

/-- The right unitor of the strict monoidal structure is the fixed right unit constraint of the
tensor product sheaf, [Stacks, Tag 01CU]. Both are the localized right unitor precomposed with
`Stacks.SheafOfModules.tensorObjIso`; the statements differ by the identity factor
`Stacks.SheafOfModules.Strict.rightUnitor_hom_aux` absorbs. -/
theorem rightUnitor_eq_tensorProductRightUnitor (M : X.Modules) :
    (ρ_ M) = tensorProductRightUnitor X.presheaf (hStruct X) M :=
  Iso.ext ((Stacks.SheafOfModules.Strict.rightUnitor_hom_aux X.presheaf (hStruct X) M).symm.trans
    (Stacks.SheafOfModules.tensorProductRightUnitor_eq_comparison X.presheaf (hStruct X) M).symm)

/-- **Multiplication by a global section, across the two localized monoidal structures.** In the
strict structure a global section of `L` is a morphism `σ : 𝒪_X ⟶ L` and multiplication by it is
`(ρ_ M).inv ≫ M ◁ σ`; that morphism is `Stacks.TensorSectionNonvanishing.mulRight` of the
section re-seated out of the sheafified unit by `Stacks.SectionProduct.ofUnitHom`, followed by the
comparison of the two tensor products.

This is the bridge the monicity of the induction step of [Stacks, Tag 0F27] was waiting on. -/
theorem rightUnitor_inv_comp_whiskerLeft (M : X.Modules) {L : X.Modules}
    (σ : Stacks.Ample.unitModule X ⟶ L) :
    (ρ_ M).inv ≫ M ◁ σ =
      mulRight M (ofUnitHom σ) ≫ (Stacks.AmplePullbackPart1.tensorIsoTensorModules X M L).hom :=
  (comp_congr (congrArg Iso.inv (rightUnitor_eq_tensorProductRightUnitor M))
      (whiskerLeft_eq_sheafifyWhiskerLeft M σ)).trans
    (AlgebraicGeometry.tensorProductRightUnitor_inv_comp_sheafifyWhiskerLeft X M σ)

/-- The tensor product of the identity with a morphism, in the bifunctor `.map` spelling the
twists of a coherent triple use, is left whiskering in the strict monoidal structure.

`tensorModulesMap X (𝟙 F) b` is *not* definitionally
`sheafifyTensorHom X.presheaf (hStruct X) (𝟙 F) b`: the first is
`CategoryTheory.Functor.uncurry` of `Stacks.SheafOfModules.Tensor.sheafTensor` at a pair, hence
the composite of the bifunctor's two legs, and the second is a single
`Stacks.SheafOfModules.sheafifyFunctor.map`. They are identified by
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`, which is where the functoriality that
separates them is paid; the tensor product of the two morphisms is then the left whiskering by
`CategoryTheory.MonoidalCategory.id_tensorHom`. -/
theorem tensorModulesMap_id_eq_whiskerLeft (F : X.Modules) {N N' : X.Modules} (b : N ⟶ N') :
    tensorModulesMap X (𝟙 F) b = F ◁ b :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
        (R := ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩) (𝟙 F) b).trans
      (Stacks.SheafOfModules.tensorHom_eq_sheafify_map X.presheaf (hStruct X)
        (𝟙 F) b).symm).trans
    (MonoidalCategory.id_tensorHom F b)

/-- The global section carried by a re-seated morphism out of `𝒪_X` is the global section the
morphism already carried. -/
theorem monoidalUnitHomEquiv_ofUnitHom {L : X.Modules}
    (σ : Stacks.Ample.unitModule X ⟶ L) :
    monoidalUnitHomEquiv L (ofUnitHom σ) = L.unitHomEquiv σ :=
  congrArg L.unitHomEquiv (Stacks.SectionProduct.toUnitHom_ofUnitHom σ)

/-! ### Monicity of multiplication by a section on a twist -/

/-- **Multiplication of `F ⊗ L^{⊗ n}` by a global section of `L` nonvanishing near every
associated point of `F` is a monomorphism**, in the spelling the twists of a coherent triple are
written in.

The nonvanishing hypothesis is about `Ass(F)` with no reference to `n`, since
`Ass(F ⊗ L^{⊗ n}) = Ass(F)` for `L^{⊗ n}` invertible
(`Stacks.Divisors.associatedPoints_tensorObj_tensorPowScheme_eq`); the conclusion is then
`Stacks.SectionProduct.mono_mulRight_of_associatedPoints` at the domain `F ⊗ L^{⊗ n}`, read
across `rightUnitor_inv_comp_whiskerLeft` and
`Stacks.Algebraization.whiskerLeft_mulSectionPowScheme`. -/
theorem mono_tensorModulesMap_id_mulSectionPowScheme [IsLocallyNoetherian X] (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {N : X.Modules} (n : ℤ)
    (σ : Stacks.Ample.unitModule X ⟶ L)
    (hq : (tensorModules X F (tensorPowScheme X L n)).IsQuasicoherent)
    (hq' : (tensorModules X (tensorModules X F (tensorPowScheme X L n)) L).IsQuasicoherent)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints F, ∃ W : X.Opens, x ∈ W ∧ ∀ y ∈ W,
      y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L (L.unitHomEquiv σ)) :
    Mono (tensorModulesMap X (𝟙 F) (mulSectionPowScheme X L σ n)) := by
  have : (tensorModules X F (tensorPowScheme X L n)).IsQuasicoherent := hq
  have := (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Stacks.AmplePullbackPart1.tensorIsoTensorModules X
      (tensorModules X F (tensorPowScheme X L n)) L).symm hq'
  have : Mono (mulRight (tensorModules X F (tensorPowScheme X L n)) (ofUnitHom σ)) := by
    refine Stacks.SectionProduct.mono_mulRight_of_associatedPoints _ ψ (ofUnitHom σ) ?_
    intro x hx
    rw [monoidalUnitHomEquiv_ofUnitHom]
    refine hW x ?_
    rwa [← Stacks.Divisors.associatedPoints_tensorObj_tensorPowScheme_eq F L n]
  rw [tensorModulesMap_id_eq_whiskerLeft, whiskerLeft_mulSectionPowScheme,
    rightUnitor_inv_comp_whiskerLeft]
  exact mono_comp _ _

/-- **The punctured-spectrum member of
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` is a monomorphism**, given a section of
the invertible triple's punctured-spectrum member that does not vanish near any associated point
of `T.F`. This is the half of the second clause of
`Stacks.Algebraization.HasHilbertInductionStep` that concerns the punctured spectrum; the
closed-fibre half is not addressed, see the module docstring. -/
theorem CoherentTriple.mono_onPunctured_mulSectionTwistZ {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {f : A} (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (n : ℤ) {N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    (hq : ((T.twistZ L hL n).F).IsQuasicoherent)
    (hq' : (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme
      ((T.twistZ L hL n).F) L.F).IsQuasicoherent)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).presheaf,
          (((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).IsSheaf⟩).obj
        (L.F)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints T.F,
      ∃ W : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace) L.F
          (L.F.unitHomEquiv σ)) :
    Mono (T.mulSectionTwistZ L hL σ σ₀ hcompat n).onPunctured :=
  let := hL.invertible_F
  have : IsLocallyNoetherian (Stacks.Divisors.puncturedSpectrum A).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (Stacks.Divisors.puncturedSpectrum A).ι
  mono_tensorModulesMap_id_mulSectionPowScheme T.F L.F n σ hq hq' ψ hW

end Stacks.Algebraization

end
