module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ConnectedComponentCurves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapFixedPointTrace
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion

/-!
# A self-map of a smooth proper scheme of dimension one on its connected components

Let `f : Y ⟶ Spec k` be proper and smooth of relative dimension one and `φ : Y ⟶ Y`. Each
connected component `C_i` is sent by `φ` into itself or into another component. On the
components sent into themselves `φ` restricts to `φ_i : C_i ⟶ C_i`; the fixed sections of `φ`
are the disjoint union of the fixed sections of the `φ_i`; and an automorphism `Ψ` with
`φ ∘ Ψ = id` on points restricts to such a component as well.

## Main definitions

* `AlgebraicGeometry.IsSelfComponent`: the `i`-th component is sent into itself by `φ`.
* `AlgebraicGeometry.componentSelfMap`: the restriction of `φ` to such a component.
* `AlgebraicGeometry.fixedSectionsEquivSigma`: the fixed sections of `φ` are the disjoint union
  of the fixed sections of the restrictions.
* `AlgebraicGeometry.componentPsi`: the restriction of `Ψ` to a component sent into itself.

## Main results

* `AlgebraicGeometry.exists_componentMove`: a component not sent into itself is sent into another.
* `AlgebraicGeometry.range_comp_subset_of_isSelfComponent`: an inverse of `φ` on points sends a
  component sent into itself by `φ` into itself.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsProper f]
  [SmoothOfRelativeDimension 1 f] (φ : Y ⟶ Y)

/-- The `i`-th component is sent into itself by `φ`. -/
def IsSelfComponent (i : Fin (componentCount Y)) : Prop :=
  Set.range (componentι f i ≫ φ).base ⊆ Set.range (componentι f i).base

/-- The restriction of `φ` to a component sent into itself. -/
def componentSelfMap (i : Fin (componentCount Y)) (h : IsSelfComponent f φ i) :
    (componentOpens f i).toScheme ⟶ (componentOpens f i).toScheme :=
  IsOpenImmersion.lift (componentι f i) (componentι f i ≫ φ) h

omit [SmoothOfRelativeDimension 1 f] in
/-- The restriction of `φ` to a component, followed by the inclusion, is the inclusion followed
by `φ`. -/
@[reassoc (attr := simp)]
theorem componentSelfMap_comp (i : Fin (componentCount Y)) (h : IsSelfComponent f φ i) :
    componentSelfMap f φ i h ≫ componentι f i = componentι f i ≫ φ :=
  IsOpenImmersion.lift_fac _ _ _

omit [SmoothOfRelativeDimension 1 f] in
/-- A point lies in the `i`-th component iff its connected component is that of the base point
of the `i`-th component. -/
theorem mem_range_componentι_iff (y : Y) (i : Fin (componentCount Y)) :
    y ∈ Set.range (componentι f i).base ↔
      connectedComponent y = connectedComponent (componentPoint f i) := by
  rw [range_componentι]
  exact ⟨fun h => (connectedComponent_eq h).symm,
    fun h => h ▸ mem_connectedComponent⟩

omit [SmoothOfRelativeDimension 1 f] in
/-- Every point lies in some component. -/
theorem exists_mem_range_componentι (y : Y) : ∃ i, y ∈ Set.range (componentι f i).base := by
  have hy : y ∈ ⋃ i, Set.range (componentι f i).base := by
    rw [iUnion_range_componentι]; trivial
  exact Set.mem_iUnion.mp hy

omit [SmoothOfRelativeDimension 1 f] in
/-- A point lies in at most one component. -/
theorem eq_of_mem_range_componentι {y : Y} {i i' : Fin (componentCount Y)}
    (h : y ∈ Set.range (componentι f i).base) (h' : y ∈ Set.range (componentι f i').base) :
    i = i' := by
  by_contra hne
  exact Set.disjoint_left.mp (pairwise_disjoint_range_componentι f hne) h h'

omit [SmoothOfRelativeDimension 1 f] in
/-- **A component not sent into itself is sent into another component.** -/
theorem exists_componentMove (i : Fin (componentCount Y)) (h : ¬ IsSelfComponent f φ i) :
    ∃ m, m ≠ i ∧ ∃ ψ : (componentOpens f i).toScheme ⟶ (componentOpens f m).toScheme,
      ψ ≫ componentι f m = componentι f i ≫ φ := by
  have := locallyConnectedSpace_of_isProper_smooth f
  obtain ⟨m, hm⟩ := exists_mem_range_componentι f (φ.base (componentPoint f i))
  have hsub : Set.range (componentι f i ≫ φ).base ⊆ Set.range (componentι f m).base := by
    rw [mem_range_componentι_iff] at hm
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_componentι,
      range_componentι, ← hm]
    exact φ.base.hom.continuous.image_connectedComponent_subset _
  refine ⟨m, fun hmi => h (hmi ▸ hsub), IsOpenImmersion.lift _ _ hsub,
    IsOpenImmersion.lift_fac _ _ _⟩

omit [SmoothOfRelativeDimension 1 f] in
/-- **An inverse of `φ` on points preserves the components sent into themselves.** -/
theorem range_comp_subset_of_isSelfComponent (Ψ : Y ⟶ Y) (hΨ : ∀ y, Ψ.base (φ.base y) = y)
    (i : Fin (componentCount Y)) (h : IsSelfComponent f φ i) :
    Set.range (componentι f i ≫ Ψ).base ⊆ Set.range (componentι f i).base := by
  have := locallyConnectedSpace_of_isProper_smooth f
  have hpt : φ.base (componentPoint f i) ∈ Set.range (componentι f i).base := by
    apply h
    obtain ⟨z0, hz0⟩ : componentPoint f i ∈ Set.range (componentι f i).base := by
      rw [range_componentι]; exact mem_connectedComponent
    exact ⟨z0, by simp [hz0]⟩
  obtain ⟨z, hz⟩ := hpt
  have hmem : componentPoint f i ∈ Ψ.base '' connectedComponent (componentPoint f i) := by
    refine ⟨φ.base (componentPoint f i), ?_, hΨ _⟩
    rw [← range_componentι, ← hz]
    exact ⟨z, rfl⟩
  have hc := Ψ.base.hom.continuous.image_connectedComponent_subset _ hmem
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_componentι]
  exact (Ψ.base.hom.continuous.image_connectedComponent_subset _).trans
    (connectedComponent_eq hc).subset

/-- The fixed section of `φ` attached to a fixed section of a restricted self-map. -/
def sigmaToFixedSections :
    (Σ i : {i : Fin (componentCount Y) // IsSelfComponent f φ i},
      fixedSections (componentι f i.1 ≫ f) (componentSelfMap f φ i.1 i.2)) → fixedSections f φ :=
  fun z => ⟨z.2.1 ≫ componentι f z.1.1, by rw [Category.assoc]; exact z.2.2.1, by
    rw [Category.assoc, ← componentSelfMap_comp f φ z.1.1 z.1.2, ← Category.assoc, z.2.2.2]⟩

omit [SmoothOfRelativeDimension 1 f] in
/-- `sigmaToFixedSections` is a bijection. -/
theorem sigmaToFixedSections_bijective : Function.Bijective (sigmaToFixedSections f φ) := by
  constructor
  · rintro ⟨⟨i, hi⟩, y, hy⟩ ⟨⟨i', hi'⟩, y', hy'⟩ h
    have h1 : y ≫ componentι f i = y' ≫ componentι f i' := congrArg Subtype.val h
    obtain rfl : i = i' := eq_of_mem_range_componentι f ⟨y.base default, rfl⟩
      (show (y ≫ componentι f i).base default ∈ _ by rw [h1]; exact ⟨y'.base default, rfl⟩)
    obtain rfl := (cancel_mono (componentι f i)).1 h1
    rfl
  · intro x
    obtain ⟨i, t, ht⟩ := exists_mem_range_componentι f (x.1.base default)
    have hself : IsSelfComponent f φ i := by
      refine (range_comp_subset_or_disjoint f φ i).resolve_right fun hd => ?_
      refine Set.disjoint_left.mp hd ⟨t, ?_⟩ ⟨t, ht⟩
      rw [Scheme.Hom.comp_base, TopCat.comp_app, ht]
      exact congrArg (fun z : Spec (.of k) ⟶ Y => z.base default) x.2.2
    have hrange : Set.range x.1.base ⊆ Set.range (componentι f i).base := by
      rintro _ ⟨s, rfl⟩
      exact ⟨t, ht.trans (congrArg x.1.base (Subsingleton.elim _ _))⟩
    have hg : IsOpenImmersion.lift (componentι f i) x.1 hrange ≫ componentι f i = x.1 :=
      IsOpenImmersion.lift_fac _ _ _
    refine ⟨⟨⟨i, hself⟩, ⟨IsOpenImmersion.lift (componentι f i) x.1 hrange,
      by rw [← Category.assoc, hg]; exact x.2.1, ?_⟩⟩, Subtype.ext hg⟩
    apply (cancel_mono (componentι f i)).1
    rw [Category.assoc, componentSelfMap_comp, ← Category.assoc, hg, x.2.2]

/-- **The fixed sections split over the components sent into themselves.** -/
def fixedSectionsEquivSigma :
    fixedSections f φ ≃ Σ i : {i : Fin (componentCount Y) // IsSelfComponent f φ i},
      fixedSections (componentι f i.1 ≫ f) (componentSelfMap f φ i.1 i.2) :=
  (Equiv.ofBijective _ (sigmaToFixedSections_bijective f φ)).symm

section Frobenius

open Stacks.Frobenius

/-- The `n`-fold absolute Frobenius is the identity on points. -/
theorem absoluteFrobeniusPow_base_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (e : ℕ) (x : X) : (absoluteFrobeniusPow X p hX e).base x = x := by
  induction e with
  | zero => rw [absoluteFrobeniusPow_zero]; rfl
  | succ e ih =>
    rw [absoluteFrobeniusPow_succ_eq_comp, Scheme.Hom.comp_base, TopCat.comp_app]
    exact ih

variable (p : ℕ) [Fact p.Prime] (hY : IsInCharacteristic Y p) (e : ℕ) (Ψ : Y ≅ Y)
  (hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow Y p hY e) (hΨ' : φ ≫ Ψ.hom = absoluteFrobeniusPow Y p hY e)

include hΨ' in
/-- `Ψ` is a left inverse of `φ` on points. -/
theorem psi_base_phi_base (y : Y) : Ψ.hom.base (φ.base y) = y := by
  have := congrArg (fun g : Y ⟶ Y => g.base y) hΨ'
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  rw [this, absoluteFrobeniusPow_base_apply]

include hΨ' in
/-- The inverse of `Ψ` agrees with `φ` on points. -/
theorem psi_inv_base (y : Y) : Ψ.inv.base y = φ.base y := by
  have h1 := congrArg (fun g : Y ⟶ Y => g.base (φ.base y)) Ψ.hom_inv_id
  simp only [Scheme.Hom.comp_base, TopCat.comp_app, psi_base_phi_base φ p hY e Ψ hΨ'] at h1
  exact h1

include hΨ' in
/-- **The restriction of `Ψ` to a component sent into itself by `φ`**, an automorphism. -/
def componentPsi (i : Fin (componentCount Y)) (h : IsSelfComponent f φ i) :
    (componentOpens f i).toScheme ≅ (componentOpens f i).toScheme where
  hom := IsOpenImmersion.lift (componentι f i) (componentι f i ≫ Ψ.hom)
    (range_comp_subset_of_isSelfComponent f φ Ψ.hom (psi_base_phi_base φ p hY e Ψ hΨ') i h)
  inv := IsOpenImmersion.lift (componentι f i) (componentι f i ≫ Ψ.inv) (by
    have : Set.range (componentι f i ≫ Ψ.inv).base = Set.range (componentι f i ≫ φ).base := by
      ext y
      simp only [Scheme.Hom.comp_base, TopCat.comp_app, Set.mem_range,
        psi_inv_base φ p hY e Ψ hΨ']
    exact this ▸ h)
  hom_inv_id := by
    apply (cancel_mono (componentι f i)).1
    simp
  inv_hom_id := by
    apply (cancel_mono (componentι f i)).1
    simp

omit [SmoothOfRelativeDimension 1 f] in
/-- The restriction of `Ψ` to a component, followed by the inclusion, is the inclusion followed
by `Ψ`. -/
@[reassoc (attr := simp)]
theorem componentPsi_hom_comp (i : Fin (componentCount Y)) (h : IsSelfComponent f φ i) :
    (componentPsi f φ p hY e Ψ hΨ' i h).hom ≫ componentι f i = componentι f i ≫ Ψ.hom :=
  IsOpenImmersion.lift_fac _ _ _

omit [SmoothOfRelativeDimension 1 f] in
include hΨ in
/-- **On a component sent into itself, `Ψ_i ≫ φ_i` is the absolute Frobenius power.** -/
theorem componentPsi_comp_componentSelfMap (i : Fin (componentCount Y))
    (h : IsSelfComponent f φ i) :
    (componentPsi f φ p hY e Ψ hΨ' i h).hom ≫ componentSelfMap f φ i h =
      absoluteFrobeniusPow _ p (isInCharacteristic_of_hom (componentι f i) p hY) e := by
  apply (cancel_mono (componentι f i)).1
  rw [Category.assoc, componentSelfMap_comp, componentPsi_hom_comp_assoc, hΨ,
    absoluteFrobeniusPow_naturality]

include hΨ' in
/-- `φ` is injective on points. -/
theorem phi_base_injective : Function.Injective φ.base := fun a b hab => by
  rw [← psi_base_phi_base φ p hY e Ψ hΨ' a, ← psi_base_phi_base φ p hY e Ψ hΨ' b, hab]

end Frobenius

end AlgebraicGeometry

end
