module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.IrreducibleComponentsBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.FiniteExtension

/-!
# The Galois action on geometric irreducible components is continuous with finite orbits

Let `K` be a separable closure of a field `k` and let `X` be locally of finite type over `k`.
Because every irreducible component of the base change `X_K` is already defined over a finite
subextension, its stabilizer in the absolute Galois group is open; hence the action of the Galois
group on the discrete set of geometric irreducible components is continuous, every orbit is
finite, and the inverse image of an irreducible component of `X` is the union of one such orbit.

## Main results

* `AlgebraicGeometry.continuous_galoisActionOnGeometricIrreducibleComponents` states continuity
  of the canonical action on geometric irreducible components.
* `AlgebraicGeometry.exists_finite_single_orbit_decomposition` gives the finite decomposition of
  the inverse image of a component of `X` and its single-orbit property.

## Implementation notes

The Galois group carries the Krull topology and the component set carries the discrete topology;
continuity is therefore equivalent to openness of every stabilizer.

The base change is represented by a categorical pullback. The components of the inverse image of
a component of `X` are collected in a finite set; the displayed equality identifies their union
with that inverse image, while the final clause states directly that any two members differ by
the canonical Galois action.

## References

* [Stacks Project, Tag 04KZ](https://stacks.math.columbia.edu/tag/04KZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A map which factors through a finite type has finite range. -/
private lemma finite_range_of_factors_through_finite
    {G A B : Type*} [Finite B] (f : G → A) (q : G → B)
    (h : ∀ g g', q g = q g' → f g = f g') : (Set.range f).Finite := by
  classical
  have hsub : Set.range f ⊆
      (fun b : ↥(Set.range q) => f b.2.choose) '' (Set.univ : Set ↥(Set.range q)) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨⟨q g, g, rfl⟩, Set.mem_univ _, ?_⟩
    exact h _ _ (Exists.choose_spec (⟨g, rfl⟩ : ∃ x, q x = q g))
  exact Set.Finite.subset ((Set.finite_univ (α := ↥(Set.range q))).image _) hsub

/-- A union over the finset of values of a map with finite range is a union over the domain. -/
private lemma biUnion_toFinset_range {ι α β : Type*} {f : ι → α} (hf : (Set.range f).Finite)
    (g : α → Set β) : ⋃ a ∈ hf.toFinset, g a = ⋃ i, g (f i) := by
  ext
  simp

/-- The union of the orbit of a set under a group action is invariant. -/
private lemma preimage_iUnion_images_mulAction
    {G Y : Type*} [Group G] [MulAction G Y] (g : G) (V : Set Y) :
    (fun y ↦ g • y) ⁻¹' (⋃ h : G, (fun y ↦ h • y) '' V) =
      ⋃ h : G, (fun y ↦ h • y) '' V := by
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨h, z, hz, heq⟩
    exact ⟨g⁻¹ * h, z, hz, by simpa [mul_smul] using congrArg (g⁻¹ • ·) heq⟩
  · rintro ⟨h, z, hz, rfl⟩
    exact ⟨g * h, z, hz, by simp [mul_smul]⟩

/-- **Stacks Project, Tag 04KZ.** The Galois action on the geometric irreducible components
of a locally finite-type scheme is continuous when the component set is discrete. -/
@[stacks 04KZ "continuous_action"]
public theorem continuous_galoisActionOnGeometricIrreducibleComponents
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    letI : TopologicalSpace (galoisActionOnGeometricIrreducibleComponents k K X).V := ⊥
    Continuous (fun p : MulOpposite (K ≃ₐ[k] K) ×
        (galoisActionOnGeometricIrreducibleComponents k K X).V =>
      ConcreteCategory.hom
        ((galoisActionOnGeometricIrreducibleComponents k K X).ρ p.1) p.2) := by
  let A := galoisActionOnGeometricIrreducibleComponents k K X
  let G := MulOpposite (K ≃ₐ[k] K)
  let : IsGalois k K :=
    { to_isSeparable := IsSepClosure.isSeparable, to_normal := IsGalois.to_normal }
  let : TopologicalSpace A.V := ⊥
  have : DiscreteTopology A.V := discreteTopology_bot A.V
  let : MulAction G A.V := Action.instMulAction A
  show Continuous (fun p : G × A.V => p.1 • p.2)
  have hcont : ContinuousSMul G A.V := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro T
    obtain ⟨E, hEfin, hfix⟩ :=
      exists_finite_subextension_stabilizing_irreducible_component X T
    apply Subgroup.isOpen_mono (H₁ := E.fixingSubgroup.op)
      (H₂ := MulAction.stabilizer G T)
    · intro g hg
      show ConcreteCategory.hom (A.ρ g) T = T
      apply hfix (MulOpposite.unop g)
      intro x
      exact (IntermediateField.mem_fixingSubgroup_iff E (MulOpposite.unop g)).mp hg x x.2
    · show IsOpen (MulOpposite.unop ⁻¹' (E.fixingSubgroup : Set (K ≃ₐ[k] K)))
      exact MulOpposite.continuous_unop.isOpen_preimage _ E.fixingSubgroup_isOpen
  exact hcont.continuous_smul

/-- A geometric irreducible component fixed by the Galois automorphisms that fix a finite
subextension pointwise has a finite Galois orbit. -/
public theorem finite_range_galoisAction_of_stabilizing
    {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
    (Z : (galoisActionOnGeometricIrreducibleComponents k K X).V)
    (E : IntermediateField k K) [FiniteDimensional k E]
    (hfix : ∀ σ : K ≃ₐ[k] K, (∀ x : E, σ x = x) →
      ConcreteCategory.hom
        ((galoisActionOnGeometricIrreducibleComponents k K X).ρ (MulOpposite.op σ)) Z = Z) :
    (Set.range fun σ : MulOpposite (K ≃ₐ[k] K) ↦
      ConcreteCategory.hom
        ((galoisActionOnGeometricIrreducibleComponents k K X).ρ σ) Z).Finite := by
  let : MulAction (MulOpposite (K ≃ₐ[k] K))
      (galoisActionOnGeometricIrreducibleComponents k K X).V :=
    Action.instMulAction (galoisActionOnGeometricIrreducibleComponents k K X)
  refine finite_range_of_factors_through_finite _
    (fun σ : MulOpposite (K ≃ₐ[k] K) ↦ σ.unop.symm.toAlgHom.comp E.val) fun σ τ hστ ↦ ?_
  have hstab := hfix (τ.unop * σ.unop.symm) fun x ↦ by
    have hx := DFunLike.congr_fun hστ x
    change σ.unop.symm x = τ.unop.symm x at hx
    simpa using congrArg τ.unop hx
  change (MulOpposite.op (τ.unop * σ.unop.symm)) • Z = Z at hstab
  show (MulOpposite.op σ.unop) • Z = (MulOpposite.op τ.unop) • Z
  calc
    (MulOpposite.op σ.unop) • Z =
        (MulOpposite.op σ.unop) • ((MulOpposite.op (τ.unop * σ.unop.symm)) • Z) := by rw [hstab]
    _ = (MulOpposite.op τ.unop) • Z := by
      rw [← mul_smul]
      congr 1
      show σ * (σ⁻¹ * τ) = τ
      simp

/-- The Galois action on the base change commutes with the projection to the original scheme. -/
public theorem galoisActionOnBaseChange_ρ_comp_fst
    {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
    (σ : MulOpposite (K ≃ₐ[k] K)) :
    (galoisActionOnBaseChange k K X).ρ σ ≫
        pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  show (pullback.lift _ _ _) ≫ _ = _
  rw [pullback.lift_fst]
  simp

/-- Galois-conjugate geometric irreducible components have the same image in the original
scheme. -/
public theorem image_fst_galoisAction_component
    {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
    (σ : MulOpposite (K ≃ₐ[k] K))
    (Z : Set (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hZ : Z ∈ irreducibleComponents
      (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme)) :
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base ''
        (ConcreteCategory.hom ((galoisActionOnGeometricIrreducibleComponents k K X).ρ σ)
          ⟨Z, hZ⟩).1 =
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base '' Z := by
  show _ '' ((galoisActionOnBaseChange k K X).ρ σ).base '' Z = _
  have hfun : (fun x ↦ (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base
      (((galoisActionOnBaseChange k K X).ρ σ).base x)) =
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base := by
    funext x
    simpa [Scheme.Hom.comp_base, TopCat.coe_comp] using
      congrArg (fun r ↦ r.base x) (galoisActionOnBaseChange_ρ_comp_fst X σ)
  rw [Set.image_image, hfun]

/-- The union of the Galois orbit of a geometric irreducible component is invariant under the
Galois action on the base change. -/
public theorem preimage_galoisBaseChangeMap_iUnion_orbit
    {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
    (Z : (galoisActionOnGeometricIrreducibleComponents k K X).V) (σ : K ≃ₐ[k] K) :
    galoisBaseChangeMap k K X.left X.hom σ ⁻¹' (⋃ τ : MulOpposite (K ≃ₐ[k] K),
        (ConcreteCategory.hom ((galoisActionOnGeometricIrreducibleComponents k K X).ρ τ) Z).1) =
      ⋃ τ : MulOpposite (K ≃ₐ[k] K),
        (ConcreteCategory.hom ((galoisActionOnGeometricIrreducibleComponents k K X).ρ τ) Z).1 := by
  let B := (Scheme.forgetToTop.mapAction (MulOpposite (K ≃ₐ[k] K))).obj
    (galoisActionOnBaseChange k K X)
  let : MulAction (MulOpposite (K ≃ₐ[k] K)) B.V := Action.instMulAction B
  have hU : (⋃ τ : MulOpposite (K ≃ₐ[k] K),
      (ConcreteCategory.hom ((galoisActionOnGeometricIrreducibleComponents k K X).ρ τ) Z).1) =
        ⋃ τ : MulOpposite (K ≃ₐ[k] K), (fun x : B.V ↦ τ • x) '' Z.1 := by
    congr 1 with τ
  rw [hU]
  exact preimage_iUnion_images_mulAction (MulOpposite.op σ) Z.1

/-- **Stacks Project, Tag 04KZ.** Over a separable closure, the inverse image of an irreducible
component is a finite union of irreducible components forming a single Galois orbit. -/
@[stacks 04KZ "finite_single_orbit_decomposition"]
public theorem exists_finite_single_orbit_decomposition
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    (T : irreducibleComponents X.left) :
    ∃ s : Finset (galoisActionOnGeometricIrreducibleComponents k K X).V,
      s.Nonempty ∧
        ((pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base ⁻¹'
              (T : Set X.left) =
            ⋃ Z ∈ s, Z.1) ∧
          ∀ Z ∈ s, ∀ Z' ∈ s,
            ∃ σ : MulOpposite (K ≃ₐ[k] K),
              ConcreteCategory.hom
                  ((galoisActionOnGeometricIrreducibleComponents k K X).ρ σ) Z = Z' := by
  classical
  let A := galoisActionOnGeometricIrreducibleComponents k K X
  let : MulAction (MulOpposite (K ≃ₐ[k] K)) A.V := Action.instMulAction A
  let p := pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  obtain ⟨Z₀, hZ₀, hZT⟩ := surjOn_irreducibleComponents_baseChange k K X.left X.hom T.2
  let Z : A.V := ⟨Z₀, hZ₀⟩
  obtain ⟨E, hE, hfix⟩ := exists_finite_subextension_stabilizing_irreducible_component X Z
  have horbit := finite_range_galoisAction_of_stabilizing X Z E hfix
  let s := horbit.toFinset
  let U : Set (pullback X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme) := ⋃ W ∈ s, W.1
  have hUclosed : IsClosed U :=
    isClosed_biUnion_finset fun W _ ↦ isClosed_of_mem_irreducibleComponents W.1 W.2
  have hUorbit : U = ⋃ σ : MulOpposite (K ≃ₐ[k] K), (σ • Z : A.V).1 :=
    biUnion_toFinset_range horbit fun W ↦ W.1
  have hZsubsetU : Z.1 ⊆ U := by
    simpa only [hUorbit, one_smul] using
      Set.subset_iUnion (fun σ : MulOpposite (K ≃ₐ[k] K) ↦ (σ • Z : A.V).1) 1
  obtain ⟨W, hWclosed, hWU⟩ :=
    exists_closed_subset_with_preimage_eq_of_galois_invariant
      k K X.left X.hom U hUclosed fun σ ↦ by
        rw [hUorbit]
        exact preimage_galoisBaseChangeMap_iUnion_orbit X Z σ
  have himageU : p.base '' U = (T : Set X.left) := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [hUorbit] at hx
      obtain ⟨σ, hxσ⟩ := Set.mem_iUnion.mp hx
      exact ((image_fst_galoisAction_component X σ Z₀ hZ₀).trans hZT).subset ⟨x, hxσ, rfl⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hZT.symm.subset hy
      exact ⟨x, hZsubsetU hx, rfl⟩
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k K))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  have hWT : W = (T : Set X.left) := by
    rw [← Set.image_preimage_eq W p.surjective, hWU, himageU]
  refine ⟨s, ?_, ?_, ?_⟩
  · refine ⟨Z, horbit.mem_toFinset.mpr ⟨1, ?_⟩⟩
    show (1 : MulOpposite (K ≃ₐ[k] K)) • Z = Z
    simp
  · show p.base ⁻¹' (T : Set X.left) = U
    rwa [← hWT]
  · intro W hW W' hW'
    obtain ⟨σ, rfl⟩ := horbit.mem_toFinset.mp hW
    obtain ⟨τ, rfl⟩ := horbit.mem_toFinset.mp hW'
    refine ⟨τ * σ⁻¹, ?_⟩
    show (τ * σ⁻¹) • (σ • Z) = τ • Z
    simp [mul_smul]

end AlgebraicGeometry
