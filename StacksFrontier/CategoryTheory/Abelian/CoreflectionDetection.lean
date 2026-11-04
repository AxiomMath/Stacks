module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# A coreflective subcategory detected by an exact functor

Let `i : 𝒬 ⥤ 𝒜` be a fully faithful functor between abelian categories with a right adjoint `Q`,
and let `r : 𝒜 ⥤ ℬ` be an exact functor to a third abelian category.  Assume

* every object `F` of `𝒜` receives a morphism `g : i G ⟶ F` from an object of `𝒬` with `r g`
  invertible, and
* `i ⋙ r` reflects zero objects.

Then `r` inverts the counit `i (Q F) ⟶ F`, an object is killed by `Q` exactly when it is killed
by `r`, and `Q` is exact.

This is the formal content of **Stacks 0779**: there `𝒬 = QCoh(𝒪_𝒳)`, `𝒜 = LQCoh^fbc(𝒪_𝒳)`,
`Q` is the coherator of **Stacks 0778** and `r` is restriction to the small étale site of a
smooth chart `U → 𝒳`; the first hypothesis is the descent of `𝓕|_{U_étale}` to a quasi-coherent
module mapping to `𝓕`, and the second that a quasi-coherent module vanishing on a chart is zero.

## Main results

* `Stacks.CategoryTheory.CoreflectionDetection.isIso_map_counit`: `r` inverts the counit.
* `Stacks.CategoryTheory.CoreflectionDetection.isZero_obj_iff`: `Q F = 0 ↔ r F = 0`.
* `Stacks.CategoryTheory.CoreflectionDetection.preservesFiniteColimits`: `Q` is right exact.
* `Stacks.CategoryTheory.CoreflectionDetection.adjunctionOfEquivalence`: a right adjoint of `i`
  built from a functor `r` with `r ∘ i` an equivalence and `r` bijective on morphisms out of the
  image of `i`; this is how the coherator of Stacks 0778 is obtained from Stacks 076S and 06WT.

## References

* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryTheory.CoreflectionDetection

variable {𝒬 𝒜 ℬ : Type*} [Category 𝒬] [Category 𝒜] [Category ℬ] [Abelian 𝒬] [Abelian 𝒜]
  [Abelian ℬ] {i : 𝒬 ⥤ 𝒜} {Q : 𝒜 ⥤ 𝒬} (adj : i ⊣ Q) [i.Full] [i.Faithful] (r : 𝒜 ⥤ ℬ)
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]

section

/-- A functor preserving finite limits is additive. -/
private instance additive_of_preservesFiniteLimits : r.Additive :=
  r.additive_of_preserves_binary_products

variable (hchart : ∀ F : 𝒜, ∃ (G : 𝒬) (g : i.obj G ⟶ F), IsIso (r.map g))

include adj hchart in
omit [i.Full] [i.Faithful] [PreservesFiniteLimits r] [PreservesFiniteColimits r] in
/-- An object `K` with `Q K = 0` is killed by `r`: the morphism `i G ⟶ K` that `r` inverts
corresponds under the adjunction to a morphism `G ⟶ Q K = 0`, so it is zero. -/
theorem isZero_map_obj_of_isZero [i.PreservesZeroMorphisms] [r.PreservesZeroMorphisms]
    {K : 𝒜} (hK : IsZero (Q.obj K)) : IsZero (r.obj K) := by
  obtain ⟨G, g, hg⟩ := hchart K
  have hg0 : g = 0 := (adj.homEquiv G K).injective (hK.eq_of_tgt _ _)
  rw [hg0, Functor.map_zero] at hg
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← IsIso.inv_hom_id (0 : r.obj (i.obj G) ⟶ r.obj K)]
  exact comp_zero

include adj hchart in
omit [PreservesFiniteColimits r] in
/-- **`r` inverts the counit** `i (Q F) ⟶ F`.  It is a split epimorphism after `r`, because the
morphism `i G ⟶ F` that `r` inverts factors through it; and its kernel is killed by `Q`, the
counit being invertible after `Q` and `Q` preserving kernels, hence by `r`, so it is a
monomorphism after `r`. -/
theorem isIso_map_counit (F : 𝒜) : IsIso (r.map (adj.counit.app F)) := by
  have : Q.IsRightAdjoint := adj.isRightAdjoint
  obtain ⟨G, g, hg⟩ := hchart F
  have hfac : r.map (i.map ((adj.homEquiv G F) g)) ≫ r.map (adj.counit.app F) = r.map g := by
    rw [← Functor.map_comp, ← adj.homEquiv_counit G F, Equiv.symm_apply_apply]
  have hepi : Epi (r.map (adj.counit.app F)) := epi_of_epi_fac hfac
  have hK : IsZero (Q.obj (kernel (adj.counit.app F))) := by
    have : PreservesLimitsOfSize.{0, 0} Q := adj.rightAdjoint_preservesLimits
    exact KernelFork.IsLimit.isZero_of_mono
      (KernelFork.mapIsLimit _ (kernelIsKernel (adj.counit.app F)) Q)
  have hmono : Mono (r.map (adj.counit.app F)) :=
    Preadditive.mono_of_isZero_kernel' _
      (KernelFork.mapIsLimit _ (kernelIsKernel (adj.counit.app F)) r)
      (isZero_map_obj_of_isZero adj r hchart hK)
  exact isIso_of_mono_of_epi _

variable (hzero : ∀ G : 𝒬, IsZero (r.obj (i.obj G)) → IsZero G)

include adj hchart hzero in
omit [PreservesFiniteColimits r] in
/-- **The kernel of `Q` is the kernel of `r`.** -/
theorem isZero_obj_iff (F : 𝒜) : IsZero (Q.obj F) ↔ IsZero (r.obj F) := by
  refine ⟨isZero_map_obj_of_isZero adj r hchart, fun hF => hzero _ ?_⟩
  have := isIso_map_counit adj r hchart F
  exact hF.of_iso (asIso (r.map (adj.counit.app F)))

include adj hchart hzero in
/-- **`Q` preserves epimorphisms.**  The cokernel of `Q f` is sent by `i` and then `r` to the
cokernel of `r (i (Q f))`, which `r` applied to the counit identifies with the cokernel of
`r f`, zero when `f` is an epimorphism. -/
theorem preservesEpimorphisms : Q.PreservesEpimorphisms where
  preserves {F F'} f _ := by
    have : PreservesColimitsOfSize.{0, 0} i := adj.leftAdjoint_preservesColimits
    have : PreservesFiniteColimits i := PreservesColimitsOfSize.preservesFiniteColimits i
    have h1 := isIso_map_counit adj r hchart F
    have h2 := isIso_map_counit adj r hchart F'
    refine Preadditive.epi_of_isZero_cokernel _ (hzero _ ?_)
    refine (isZero_cokernel_of_epi (r.map f)).of_iso ?_
    refine (PreservesCokernel.iso (i ⋙ r) (Q.map f)) ≪≫
      cokernel.mapIso _ _ (asIso (r.map (adj.counit.app F)))
        (asIso (r.map (adj.counit.app F'))) ?_
    show r.map (i.map (Q.map f)) ≫ r.map (adj.counit.app F') =
      r.map (adj.counit.app F) ≫ r.map f
    exact (r.map_comp _ _).symm.trans ((congrArg r.map (adj.counit_naturality f)).trans
      (r.map_comp _ _))

include adj hchart hzero in
/-- **`Q` is exact**: it is left exact as a right adjoint, and it preserves epimorphisms. -/
theorem preservesFiniteColimits : PreservesFiniteColimits Q := by
  have : Q.IsRightAdjoint := adj.isRightAdjoint
  have := preservesEpimorphisms adj r hchart hzero
  have : Q.Additive := Q.additive_of_preserves_binary_products
  refine (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi Q).2 fun T hT => ?_
  have : Epi T.g := hT.epi_g
  exact ⟨((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono Q).1 inferInstance T hT).1,
    inferInstance⟩

end

end Stacks.CategoryTheory.CoreflectionDetection

namespace Stacks.CategoryTheory.CoreflectionDetection

section Equivalence

variable {𝒬 𝒜 𝒟 : Type*} [Category 𝒬] [Category 𝒜] [Category 𝒟]
  (i : 𝒬 ⥤ 𝒜) (r : 𝒜 ⥤ 𝒟) (Φ : 𝒬 ≌ 𝒟) (e : i ⋙ r ≅ Φ.functor)
  (h : ∀ G F, Function.Bijective (fun f : i.obj G ⟶ F => r.map f))

/-- The bijection `Hom(i G, F) ≃ Hom(G, Φ⁻¹ r F)` sending `f` to the transpose, along `Φ`, of
`e⁻¹_G ≫ r f : Φ G ⟶ r F`. -/
noncomputable def homEquivOfEquivalence (G : 𝒬) (F : 𝒜) :
    (i.obj G ⟶ F) ≃ (G ⟶ Φ.inverse.obj (r.obj F)) where
  toFun f := Φ.toAdjunction.homEquiv G (r.obj F) (e.inv.app G ≫ r.map f)
  invFun g := (Equiv.ofBijective _ (h G F)).symm
    (e.hom.app G ≫ (Φ.toAdjunction.homEquiv G (r.obj F)).symm g)
  left_inv f := by
    apply (Equiv.ofBijective _ (h G F)).injective
    simp
  right_inv g := by
    simp only [Equiv.ofBijective_apply_symm_apply, Iso.inv_hom_id_app_assoc]
    exact Equiv.apply_symm_apply _ _

/-- `homEquivOfEquivalence` sends `f` to the transpose along `Φ` of `e⁻¹_G ≫ r f`. -/
theorem homEquivOfEquivalence_apply (G : 𝒬) (F : 𝒜) (f : i.obj G ⟶ F) :
    homEquivOfEquivalence i r Φ e h G F f =
      Φ.toAdjunction.homEquiv G (r.obj F) (e.inv.app G ≫ r.map f) := rfl

/-- `homEquivOfEquivalence` is natural in `G`: precomposing with `i g` corresponds to
precomposing with `g`. -/
theorem homEquivOfEquivalence_naturality_left {G G' : 𝒬} {F : 𝒜} (g : G ⟶ G')
    (f : i.obj G' ⟶ F) :
    homEquivOfEquivalence i r Φ e h G F (i.map g ≫ f) =
      g ≫ homEquivOfEquivalence i r Φ e h G' F f := by
  rw [homEquivOfEquivalence_apply, homEquivOfEquivalence_apply, r.map_comp,
    ← Adjunction.homEquiv_naturality_left]
  congr 1
  exact (e.inv.naturality_assoc g _).symm

/-- **A right adjoint through an equivalence.**  If `r ∘ i` is an equivalence `Φ` and `r` is
bijective on morphisms out of the image of `i`, then `r` followed by the inverse of `Φ` is right
adjoint to `i`:
`Hom(i G, F) ≅ Hom(r i G, r F) ≅ Hom(Φ G, r F) ≅ Hom(G, Φ⁻¹ r F)`. -/
noncomputable def adjunctionOfEquivalence : i ⊣ r ⋙ Φ.inverse :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquivOfEquivalence i r Φ e h
      homEquiv_naturality_left_symm {G G' F} g f := by
        apply (homEquivOfEquivalence i r Φ e h G F).injective
        rw [Equiv.apply_symm_apply, homEquivOfEquivalence_naturality_left, Equiv.apply_symm_apply]
      homEquiv_naturality_right {G F F'} f g := by
        rw [homEquivOfEquivalence_apply, homEquivOfEquivalence_apply, r.map_comp,
          ← Category.assoc, Adjunction.homEquiv_naturality_right]
        rfl }

/-- The counit of `Stacks.CategoryTheory.CoreflectionDetection.adjunctionOfEquivalence`, after
`r`, is `e` followed by the counit of `Φ`. -/
theorem map_adjunctionOfEquivalence_counit_app (F : 𝒜) :
    r.map ((adjunctionOfEquivalence i r Φ e h).counit.app F) =
      e.hom.app _ ≫ Φ.counit.app (r.obj F) := by
  have h1 : (adjunctionOfEquivalence i r Φ e h).counit.app F =
      (homEquivOfEquivalence i r Φ e h _ F).symm (𝟙 _) := by
    simp [adjunctionOfEquivalence]
  rw [h1]
  show (Equiv.ofBijective _ (h _ F)) ((Equiv.ofBijective _ (h _ F)).symm _) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_counit]
  simp

/-- The counit of `Stacks.CategoryTheory.CoreflectionDetection.adjunctionOfEquivalence` is
inverted by `r`. -/
theorem isIso_map_adjunctionOfEquivalence_counit_app (F : 𝒜) :
    IsIso (r.map ((adjunctionOfEquivalence i r Φ e h).counit.app F)) := by
  rw [map_adjunctionOfEquivalence_counit_app]
  infer_instance

end Equivalence

end Stacks.CategoryTheory.CoreflectionDetection
