module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Homology.RightDerivedDelta

/-!
# The essential image of a fully faithful exact left adjoint

Let `L ⊣ R` be an adjunction between abelian categories, with `L` exact and the unit `𝟭 ⟶ R ∘ L` an
isomorphism, so that `L` is fully faithful. Suppose moreover that the first right derived functor
of `R` vanishes on the image of `L`. Then the essential image of `L` is a weak Serre subcategory
(and more generally whenever the right adjoint carries short exact sequences starting in the image
of `L` to short exact sequences): it contains `0`, is closed under isomorphisms, kernels and
cokernels because `L` is exact and fully faithful, and it is closed under extensions. The last
point is the argument of the source: if `0 ⟶ L A ⟶ G ⟶ L B ⟶ 0` is exact, then so is
`0 ⟶ R L A ⟶ R G ⟶ R L B ⟶ R¹R (L A) = 0`, so applying the exact functor `L` and comparing with the
original sequence by the counit, the five lemma shows that `L R G ⟶ G` is an isomorphism.

## Main results

* `CategoryTheory.Adjunction.shortExact_map_of_isZero_rightDerived_one`: a left exact functor
  carries a short exact sequence to a short exact sequence when its first right derived functor
  vanishes on the first term.
* `CategoryTheory.Adjunction.mem_essImage_of_shortExact`: the essential image is closed under
  extensions, as soon as the right adjoint is exact on short exact sequences starting in it;
  `CategoryTheory.Adjunction.shortExact_map_of_isZero_rightDerived_one` supplies that from the
  vanishing of the first right derived functor of the right adjoint on the image.
* `CategoryTheory.Adjunction.isWeakSerreClass_essImage`: the essential image is a weak Serre
  subcategory.

## References

* [Stacks Project, Tag 09B1](https://stacks.math.columbia.edu/tag/09B1)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- A left exact additive functor `R` carries a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` to
a short exact sequence as soon as `R¹R X₁` vanishes: the long exact sequence of right derived
functors continues `R X₂ ⟶ R X₃ ⟶ R¹R X₁ = 0`. -/
theorem Functor.shortExact_map_of_isZero_rightDerived_one {D : Type u₁} [Category.{v₁} D]
    [Abelian D] [EnoughInjectives D] {C : Type u₂} [Category.{v₂} C] [Abelian C]
    (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R] {S : ShortComplex D} (hS : S.ShortExact)
    (h : IsZero ((R.rightDerived 1).obj S.X₁)) : (S.map R).ShortExact := by
  obtain ⟨δ, -, hex⟩ := Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅
    hS R
  have h₀ : Epi ((R.rightDerived 0).map S.g) := by
    have hsc := (hex 0).exact 1
    exact (ShortComplex.exact_iff_epi _ (h.eq_of_tgt _ _)).1 hsc
  have hg : Epi (R.map S.g) := by
    have hnat := R.toRightDerivedZero.naturality S.g
    have : Epi (R.map S.g ≫ R.toRightDerivedZero.app S.X₃) := by
      rw [hnat]
      infer_instance
    have e : R.map S.g = (R.map S.g ≫ R.toRightDerivedZero.app S.X₃) ≫
        CategoryTheory.inv (R.toRightDerivedZero.app S.X₃) := by simp
    rw [e]
    infer_instance
  have := hS.mono_f
  exact { exact := hS.exact.map_of_mono_of_preservesKernel R inferInstance
            inferInstance
          mono_f := by dsimp; infer_instance
          epi_g := hg }

namespace Adjunction

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

include adj in
/-- **The essential image of a fully faithful exact left adjoint is closed under extensions**,
provided the right adjoint carries a short exact sequence whose first term lies in that image to
a short exact sequence. -/
theorem mem_essImage_of_shortExact [IsIso adj.unit] [R.Additive] [PreservesFiniteLimits L]
    (hR : ∀ S : ShortComplex D, S.ShortExact → L.essImage S.X₁ → (S.map R).ShortExact)
    {S : ShortComplex D} (hS : S.ShortExact) (h₁ : L.essImage S.X₁) (h₃ : L.essImage S.X₃) :
    L.essImage S.X₂ := by
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  have : L.Full := hff.full
  have : L.Faithful := hff.faithful
  have : PreservesFiniteColimits L := by
    have := adj.leftAdjoint_preservesColimits
    infer_instance
  have hRS := hR S hS h₁
  have hLRS : ((S.map R).map L).ShortExact := hRS.map_of_exact L
  let φ : (S.map R).map L ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := (adj.counit.naturality S.g).symm }
  have : IsIso φ.τ₁ := (adj.isIso_counit_app_iff_mem_essImage).2 h₁
  have : IsIso φ.τ₃ := (adj.isIso_counit_app_iff_mem_essImage).2 h₃
  have : IsIso φ.τ₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hLRS hS
  exact (adj.isIso_counit_app_iff_mem_essImage).1 this

include adj in
/-- **Stacks 09B1 (1), abstractly.** The essential image of a fully faithful exact left adjoint
`L` is a weak Serre subcategory as soon as the right adjoint carries a short exact sequence whose
first term lies in that image to a short exact sequence. -/
theorem isWeakSerreClass_essImage [IsIso adj.unit] [L.Additive] [R.Additive]
    [PreservesFiniteLimits L]
    (hR : ∀ S : ShortComplex D, S.ShortExact → L.essImage S.X₁ → (S.map R).ShortExact) :
    L.essImage.IsWeakSerreClass := by
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  have : L.Full := hff.full
  have : L.Faithful := hff.faithful
  have : PreservesFiniteColimits L := by
    have := adj.leftAdjoint_preservesColimits
    infer_instance
  have hker : ∀ {X Y : D} (f : X ⟶ Y), L.essImage X → L.essImage Y → L.essImage (kernel f) := by
    intro X Y f hX hY
    obtain ⟨A, ⟨eA⟩⟩ := hX
    obtain ⟨B, ⟨eB⟩⟩ := hY
    obtain ⟨g, hg⟩ := L.map_surjective (eA.hom ≫ f ≫ eB.inv)
    exact ⟨kernel g, ⟨PreservesKernel.iso L g ≪≫ kernel.mapIso _ _ eA eB (by rw [hg]; simp)⟩⟩
  have hcok : ∀ {X Y : D} (f : X ⟶ Y), L.essImage X → L.essImage Y →
      L.essImage (cokernel f) := by
    intro X Y f hX hY
    obtain ⟨A, ⟨eA⟩⟩ := hX
    obtain ⟨B, ⟨eB⟩⟩ := hY
    obtain ⟨g, hg⟩ := L.map_surjective (eA.hom ≫ f ≫ eB.inv)
    exact ⟨cokernel g, ⟨PreservesCokernel.iso L g ≪≫ cokernel.mapIso _ _ eA eB
      (by rw [hg]; simp)⟩⟩
  have : L.essImage.ContainsZero :=
    ⟨⟨L.obj (0 : C), L.map_isZero (isZero_zero C), L.obj_mem_essImage (0 : C)⟩⟩
  have : L.essImage.IsClosedUnderKernels :=
    ⟨by
      rintro _ ⟨f, k, hk, hf⟩
      exact L.essImage.prop_of_iso (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
        (hker f hf.1 hf.2)⟩
  have : L.essImage.IsClosedUnderCokernels :=
    ⟨by
      rintro _ ⟨f, k, hk, hf⟩
      exact L.essImage.prop_of_iso (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
        (hcok f hf.1 hf.2)⟩
  have : L.essImage.IsClosedUnderExtensions :=
    ⟨fun hS h₁ h₃ ↦ adj.mem_essImage_of_shortExact hR hS h₁ h₃⟩
  exact { }

include adj in
/-- The hypothesis of `CategoryTheory.Adjunction.isWeakSerreClass_essImage` holds when the first
right derived functor of the right adjoint vanishes on the image of `L`. -/
theorem shortExact_map_of_isZero_rightDerived_one [EnoughInjectives D] [R.Additive]
    (hR : ∀ A : C, IsZero ((R.rightDerived 1).obj (L.obj A))) (S : ShortComplex D)
    (hS : S.ShortExact) (h₁ : L.essImage S.X₁) : (S.map R).ShortExact := by
  have : PreservesFiniteLimits R := by
    have := adj.rightAdjoint_preservesLimits
    infer_instance
  obtain ⟨A, ⟨e⟩⟩ := h₁
  exact R.shortExact_map_of_isZero_rightDerived_one hS
    ((hR A).of_iso ((R.rightDerived 1).mapIso e).symm)

end Adjunction

end CategoryTheory

end
