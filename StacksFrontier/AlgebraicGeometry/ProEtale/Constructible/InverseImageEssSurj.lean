module

public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleLift
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenImmersion

/-!
# Every pro-étale sheaf of modules on a locally closed subscheme is an inverse image

Let `Λ` be a ring and `i : Z ⟶ X` a morphism of schemes. Inverse image of pro-étale sheaves of
`Λ`-modules along `i` is essentially surjective, that is, every sheaf of `Λ`-modules on `Z_proét`
is the inverse image of one on `X_proét`, in each of the following cases:

* `i` is an open immersion: the right adjoint of restriction has invertible counit
  (Stacks 09BN);
* `i` is a closed immersion of affine schemes: direct image along `i` is fully faithful
  (Stacks 09BL), so the counit `i⁻¹ i_* ⟶ id` is invertible;
* `i` is a composite of two morphisms of the above kinds.

In each case a sheaf `𝓕` on `Z_proét` is `i⁻¹` of a direct image of `𝓕`. This is how a statement
about inverse images of sheaves on `X`, such as the Tor amplitude of a restricted complex tested
against all sheaves, is carried to a locally closed subscheme.

## Main results

* `AlgebraicGeometry.ProEtale.essSurj_proetaleModuleInverseImage_of_isOpenImmersion`
* `AlgebraicGeometry.ProEtale.essSurj_proetaleModuleInverseImage_of_isClosedImmersion`
* `AlgebraicGeometry.ProEtale.essSurj_proetaleModuleInverseImage_comp`

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BN](https://stacks.math.columbia.edu/tag/09BN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] proetalePostcompose_isContinuous

variable (Λ : Type v) [CommRing Λ]

/-- A left adjoint whose counit is invertible is essentially surjective: every object is the
image of its image under the right adjoint. -/
theorem _root_.CategoryTheory.Adjunction.essSurj_of_isIso_counit {C D : Type*} [Category* C]
    [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.counit] : L.EssSurj :=
  ⟨fun F => ⟨R.obj F, ⟨asIso (adj.counit.app F)⟩⟩⟩

/-- **Every pro-étale sheaf of modules on an open subscheme is an inverse image.** Inverse image
along an open immersion is restriction, whose right adjoint has invertible counit. -/
instance essSurj_proetaleModuleInverseImage_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (proetaleModuleInverseImage.{u, v, w} j Λ).EssSurj := by
  obtain ⟨⟨R, adj⟩⟩ := exists_directImage_modules.{u, v, max v w} j Λ
  have := directImage_counit_isIso_modules.{u, v, max v w} j Λ R adj
  have h : (Modules.proetaleRestriction.{u, v, max v w} j Λ).EssSurj := adj.essSurj_of_isIso_counit
  exact @Functor.essSurj_of_iso _ _ _ _ _ _ h
    (proetaleModuleInverseImageIsoRestriction.{u, v, w} Λ j).symm

/-- **Every pro-étale sheaf of modules on a closed subscheme of an affine scheme is an inverse
image.** Direct image along a closed immersion of affine schemes is fully faithful
(Stacks 09BL), so the counit of the inverse image/direct image adjunction is invertible. -/
instance essSurj_proetaleModuleInverseImage_of_isClosedImmersion {Z X : Scheme.{u}}
    [IsAffine X] [IsAffine Z] (i : Z ⟶ X) [IsClosedImmersion i] :
    (proetaleModuleInverseImage.{u, v, w} i Λ).EssSurj := by
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{max (u + 1) v w} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, max (u + 1) v w, v}
  obtain ⟨hff⟩ := proetaleDirectImage_fullyFaithful i (ModuleCat.{max (u + 1) v w} Λ)
  have := hff.full
  have := hff.faithful
  have := (proetaleModuleInverseImageAdjunction.{u, v, w} Λ i).counit_isIso_of_R_fully_faithful
  exact (proetaleModuleInverseImageAdjunction.{u, v, w} Λ i).essSurj_of_isIso_counit

/-- Inverse image along a composite is essentially surjective when inverse image along each
factor is. -/
theorem essSurj_proetaleModuleInverseImage_comp {Y Z X : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ X)
    [(proetaleModuleInverseImage.{u, v, w} a Λ).EssSurj]
    [(proetaleModuleInverseImage.{u, v, w} b Λ).EssSurj] :
    (proetaleModuleInverseImage.{u, v, w} (a ≫ b) Λ).EssSurj :=
  Functor.essSurj_of_iso (proetaleModuleInverseImageCompIso.{u, v, w} Λ a b)

/-- **An immersion is, locally on its source, one along which inverse image is essentially
surjective.** Restricted to the preimage of an affine open `V` of the open subscheme in which `i`
is closed, `i` is a closed immersion of affine schemes followed by the open immersion of `V`
into `X`. -/
theorem exists_isOpenImmersion_cover_essSurj_proetaleModuleInverseImage {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] :
    ∃ (ι : Type u) (W : ι → Scheme.{u}) (j : ∀ a, W a ⟶ Z), (∀ a, IsOpenImmersion (j a)) ∧
      (∀ z, ∃ a, z ∈ Set.range (j a)) ∧
      ∀ a, (proetaleModuleInverseImage.{u, v, w} (j a ≫ i) Λ).EssSurj := by
  let c := i.liftCoborder
  let j (a : (i.coborderRange : Scheme).affineOpens) : (c ⁻¹ᵁ a.1 : Scheme) ⟶ Z := (c ⁻¹ᵁ a.1).ι
  refine ⟨_, _, j, fun a => inferInstance, fun z => ?_, fun a => ?_⟩
  · obtain ⟨V, hV, hzV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (i.coborderRange : Scheme).isBasis_affineOpens
      (show c z ∈ (⊤ : (i.coborderRange : Scheme).Opens) from trivial)
    exact ⟨⟨V, hV⟩, by rwa [Scheme.Opens.range_ι]⟩
  · have : IsAffine (a.1 : Scheme) := a.2
    let t := c ∣_ a.1
    let o := a.1.ι ≫ i.coborderRange.ι
    have : IsAffine (c ⁻¹ᵁ a.1 : Scheme) := isAffine_of_isAffineHom t
    have hfac : j a ≫ i = t ≫ o := by
      calc j a ≫ i = (c ⁻¹ᵁ a.1).ι ≫ c ≫ i.coborderRange.ι := by
            rw [Scheme.Hom.liftCoborder_ι i]
        _ = t ≫ o := by rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    rw [hfac]
    exact essSurj_proetaleModuleInverseImage_comp Λ t o

end AlgebraicGeometry.ProEtale

end
