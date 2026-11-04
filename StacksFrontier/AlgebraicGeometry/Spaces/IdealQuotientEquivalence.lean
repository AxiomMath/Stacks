module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealMultipleModule

/-!
# Quotients `M / J M` are carried by equivalences compatible with the scalars

Let `X₁`, `X₂` be algebraic spaces, possibly over different base schemes, let `φ₁`, `φ₂` be ring
maps from a ring `A` to their global functions, and let `Φ : Mod(𝒪_{X₁}) ≌ Mod(𝒪_{X₂})` be an
equivalence of module categories carrying multiplication by `φ₁ a` to multiplication by
`φ₂ a`.  Then `Φ` carries the quotient `M / J M` of an `𝒪_{X₁}`-module by an ideal `J ⊆ A` to
the quotient `Φ M / J Φ M`, compatibly with the projections.

The quotient `M / J M` is the cokernel of the map `∐_{a ∈ J} M ⟶ M` whose components are the
multiplications by `φ₁ a`, through its image, so it is defined by colimits and by the scalar
multiplications only; an equivalence preserves both.

## Main definitions

* `AlgebraicGeometry.Space.idealQuotientEquivalenceIso`: `Φ(M / J M) ≅ Φ M / J Φ M`.
* `AlgebraicGeometry.Space.idealQuotientCompIso`: for a surjective ring map `σ : A → R`, the
  quotient `M / J M` along `φ ∘ σ` is isomorphic to `M / σ(J) M` along `φ`.

## Main results

* `AlgebraicGeometry.Space.map_idealQuotientπ_idealQuotientEquivalenceIso_hom`: the isomorphism
  is compatible with the projections from `Φ M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S₁ S₂ : Scheme.{u}} {hS₁ : B.Contains S₁} {hS₂ : B.Contains S₂}
  {X₁ : (BigFppfOver B S₁ hS₁)ᵒᵖ ⥤ Type u} {hX₁ : IsAlgebraicSpace B S₁ hS₁ X₁}
  {X₂ : (BigFppfOver B S₂ hS₂)ᵒᵖ ⥤ Type u} {hX₂ : IsAlgebraicSpace B S₂ hS₂ X₂}
  {A : Type u} [CommRing A]
  (φ₁ : A →+* ↥(GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S₁ hS₁ X₁ hX₁).O))))
  (φ₂ : A →+* ↥(GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S₂ hS₂ X₂ hX₂).O))))
  (Φ : Modules.{u, u} B S₁ hS₁ X₁ hX₁ ⥤ Modules.{u, u} B S₂ hS₂ X₂ hX₂)
  [Φ.IsEquivalence]
  (hΦ : ∀ (a : A) (M : Modules.{u, u} B S₁ hS₁ X₁ hX₁),
    Φ.map (globalSmul _ (φ₁ a) M) = globalSmul _ (φ₂ a) (Φ.obj M))
  (M : Modules.{u, u} B S₁ hS₁ X₁ hX₁) (J : Ideal A)

include hΦ in
/-- `Φ` applied to multiplication by `φ₁ a` followed by the projection onto `Φ M / J Φ M`
vanishes for `a ∈ J`. -/
theorem map_idealMultipleι_comp_idealQuotientπ :
    Φ.map (idealMultipleι φ₁ M J) ≫ idealQuotientπ φ₂ (Φ.obj M) J = 0 := by
  have hepi : Epi (Φ.map (Abelian.factorThruImage (idealMultipleHom φ₁ M J))) := inferInstance
  refine (cancel_epi (Φ.map (Abelian.factorThruImage (idealMultipleHom φ₁ M J)))).1 ?_
  rw [comp_zero, ← Category.assoc, ← Φ.map_comp, Abelian.image.fac]
  refine (cancel_epi (sigmaComparison Φ (fun _ : ↥J => M))).1 (Sigma.hom_ext _ _ fun a => ?_)
  rw [comp_zero, comp_zero, ← Category.assoc, ι_comp_sigmaComparison, ← Φ.map_comp_assoc,
    ι_idealMultipleHom, hΦ, ← idealMultipleFactor_ι φ₂ _ J a.2, Category.assoc,
    idealMultipleι_idealQuotientπ, comp_zero]

include hΦ in
/-- The projection `Φ M ⟶ Φ(M / J M)` kills `J Φ M`. -/
theorem idealMultipleι_comp_map_idealQuotientπ :
    idealMultipleι φ₂ (Φ.obj M) J ≫ Φ.map (idealQuotientπ φ₁ M J) = 0 := by
  refine idealMultiple_hom_ext φ₂ (Φ.obj M) J fun a ha => ?_
  rw [comp_zero, ← Category.assoc, idealMultipleFactor_ι, ← hΦ, ← Φ.map_comp,
    ← idealMultipleFactor_ι φ₁ M J ha, Category.assoc, idealMultipleι_idealQuotientπ, comp_zero,
    Φ.map_zero]

include hΦ in
/-- **`Φ(M / J M) ≅ Φ M / J Φ M`** for an equivalence carrying multiplication by
`φ₁ a` to multiplication by `φ₂ a`. -/
def idealQuotientEquivalenceIso :
    Φ.obj (idealQuotient φ₁ M J) ≅ idealQuotient φ₂ (Φ.obj M) J where
  hom := (PreservesCokernel.iso Φ (idealMultipleι φ₁ M J)).hom ≫
    cokernel.desc _ (idealQuotientπ φ₂ (Φ.obj M) J)
      (map_idealMultipleι_comp_idealQuotientπ φ₁ φ₂ Φ hΦ M J)
  inv := cokernel.desc _ (Φ.map (idealQuotientπ φ₁ M J))
    (idealMultipleι_comp_map_idealQuotientπ φ₁ φ₂ Φ hΦ M J)
  hom_inv_id := by
    have hepi : Epi (Φ.map (idealQuotientπ φ₁ M J)) := inferInstance
    refine (cancel_epi (Φ.map (idealQuotientπ φ₁ M J))).1 ?_
    rw [Category.comp_id, ← Category.assoc, ← Category.assoc, PreservesCokernel.π_iso_hom,
      cokernel.π_desc, cokernel.π_desc]
  inv_hom_id := by
    refine (cancel_epi (idealQuotientπ φ₂ (Φ.obj M) J)).1 ?_
    rw [Category.comp_id, ← Category.assoc, cokernel.π_desc, ← Category.assoc,
      PreservesCokernel.π_iso_hom, cokernel.π_desc]

include hΦ in
/-- The isomorphism `Φ(M / J M) ≅ Φ M / J Φ M` is compatible with the projections. -/
@[reassoc (attr := simp)]
theorem map_idealQuotientπ_idealQuotientEquivalenceIso_hom :
    Φ.map (idealQuotientπ φ₁ M J) ≫ (idealQuotientEquivalenceIso φ₁ φ₂ Φ hΦ M J).hom =
      idealQuotientπ φ₂ (Φ.obj M) J := by
  rw [idealQuotientEquivalenceIso, ← Category.assoc, PreservesCokernel.π_iso_hom,
    cokernel.π_desc]

include hΦ in
/-- The inverse isomorphism is compatible with the projections. -/
@[reassoc (attr := simp)]
theorem idealQuotientπ_idealQuotientEquivalenceIso_inv :
    idealQuotientπ φ₂ (Φ.obj M) J ≫ (idealQuotientEquivalenceIso φ₁ φ₂ Φ hΦ M J).inv =
      Φ.map (idealQuotientπ φ₁ M J) :=
  cokernel.π_desc _ _ _

section Reindex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
  {A R : Type u} [CommRing A] [CommRing R]
  (φ : R →+* ↥(GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))))
  (σ : A →+* R) (hσ : Function.Surjective σ) (M : Modules.{u, u} B S hS X hX) (J : Ideal A)

/-- If every `φ' a`, `a ∈ J'`, is some `φ b` with `b ∈ J`, then `J' M` along `φ'` maps to zero in
`M / J M` along `φ`. -/
private theorem idealMultipleι_comp_idealQuotientπ_eq_zero {A₁ A₂ : Type u} [CommRing A₁]
    [CommRing A₂]
    (φ : A₁ →+* ↥(GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))))
    (φ' : A₂ →+* ↥(GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))))
    (J : Ideal A₁) (J' : Ideal A₂) (h : ∀ a ∈ J', ∃ b ∈ J, φ' a = φ b) :
    idealMultipleι φ' M J' ≫ idealQuotientπ φ M J = 0 := by
  refine idealMultiple_hom_ext φ' M J' fun a ha => ?_
  obtain ⟨b, hb, hab⟩ := h a ha
  rw [comp_zero, ← Category.assoc, idealMultipleFactor_ι, hab,
    ← idealMultipleFactor_ι φ M J hb, Category.assoc, idealMultipleι_idealQuotientπ, comp_zero]

include hσ in
/-- The projection onto `M / J M` along `φ ∘ σ` kills `σ(J) M`. -/
theorem idealMultipleι_map_comp_idealQuotientπ_comp :
    idealMultipleι φ M (Ideal.map σ J) ≫ idealQuotientπ (φ.comp σ) M J = 0 :=
  idealMultipleι_comp_idealQuotientπ_eq_zero M _ _ _ _ fun _ hb => by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective σ hσ).1 hb
    exact ⟨a, ha, rfl⟩

/-- The projection onto `M / σ(J) M` along `φ` kills `J M` along `φ ∘ σ`. -/
theorem idealMultipleι_comp_idealQuotientπ_map :
    idealMultipleι (φ.comp σ) M J ≫ idealQuotientπ φ M (Ideal.map σ J) = 0 :=
  idealMultipleι_comp_idealQuotientπ_eq_zero M _ _ _ _ fun a ha =>
    ⟨σ a, Ideal.mem_map_of_mem σ ha, rfl⟩

include hσ in
/-- **`M / J M` along `φ ∘ σ` is `M / σ(J) M` along `φ`**, for a surjective ring map `σ`. -/
def idealQuotientCompIso :
    idealQuotient (φ.comp σ) M J ≅ idealQuotient φ M (Ideal.map σ J) where
  hom := cokernel.desc _ (idealQuotientπ φ M (Ideal.map σ J))
    (idealMultipleι_comp_idealQuotientπ_map φ σ M J)
  inv := cokernel.desc _ (idealQuotientπ (φ.comp σ) M J)
    (idealMultipleι_map_comp_idealQuotientπ_comp φ σ hσ M J)
  hom_inv_id := by
    refine (cancel_epi (idealQuotientπ (φ.comp σ) M J)).1 ?_
    rw [Category.comp_id, ← Category.assoc, cokernel.π_desc, cokernel.π_desc]
  inv_hom_id := by
    refine (cancel_epi (idealQuotientπ φ M (Ideal.map σ J))).1 ?_
    rw [Category.comp_id, ← Category.assoc, cokernel.π_desc, cokernel.π_desc]

/-- The isomorphism `M / J M ≅ M / σ(J) M` is compatible with the projections from `M`. -/
@[reassoc (attr := simp)]
theorem idealQuotientπ_idealQuotientCompIso_hom :
    idealQuotientπ (φ.comp σ) M J ≫ (idealQuotientCompIso φ σ hσ M J).hom =
      idealQuotientπ φ M (Ideal.map σ J) :=
  cokernel.π_desc _ _ _

end Reindex

end AlgebraicGeometry.Space

end
