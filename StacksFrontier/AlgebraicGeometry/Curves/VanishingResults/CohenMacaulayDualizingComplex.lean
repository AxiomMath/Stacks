module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveMorphismDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleMaximalDimension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FlatPullbackStalk
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# The dualizing complex of a Cohen–Macaulay curve is `ω_X[1]`

Let `X` be a proper scheme over a field `k` which is Cohen–Macaulay and equidimensional of
dimension one, let `ω_X^• = f^×(𝒪_{Spec k})` be its dualizing complex and
`ω_X = H^{-1}(ω_X^•)` the dualizing sheaf of [Stacks, Tag 0BS2]. This file proves that
`ω_X^•` has no cohomology outside degree `-1`, hence `ω_X^• ≅ ω_X[1]`, and that `ω_X` has
support `X`.

## Main results

* `Stacks.Duality.nontrivial_stalk_dualizingSheafOverField_of_isCohenMacaulay` — `ω_X` has
  nonzero stalk at every point of `X`.
* `Stacks.Duality.isZero_homology_dualizingComplexOverField_of_isCohenMacaulay` —
  `H^i(ω_X^•) = 0` for `i ≠ -1`.
* `Stacks.Duality.isLE_dualizingComplexOverField_of_isCohenMacaulay` — `ω_X^• ∈ D^{≤ -1}`.
* `Stacks.Duality.dualizingSheafShiftOneIsoOfIsCohenMacaulay` — `ω_X[1] ≅ ω_X^•`.

## References

* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0AWT](https://stacks.math.columbia.edu/tag/0AWT)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace Stacks.Duality

/-! ### Cohen–Macaulay schemes: the loci of the cohomology sheaves are open and closed -/

/-- **Some cohomology sheaf of a dualizing complex has a nonzero stalk at every point.** -/
theorem exists_nontrivial_stalk_homology_of_isDualizingComplex {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) :
    ∃ i : ℤ,
      Nontrivial (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk x) := by
  obtain ⟨d, hd⟩ := exists_natCast_ringKrullDim_stalk x
  refine ⟨-(d : ℤ) - associatedShiftFunction K x, ?_⟩
  have h := not_isZero_stalk_homology_of_isDualizingComplex hK x d hd
  rwa [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial] at h

/-- If the cohomology sheaves of `K` vanish stalkwise on `V` outside degree `m`, a degree with
nonzero stalk at a point of `V` is `m`. -/
private theorem eq_of_nontrivial_stalk_homology {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
    {K : DerivedCategory X.Modules} {V : X.Opens} {m n : ℤ} {y : X} (hyV : y ∈ V)
    (hm : ∀ i : ℤ, i ≠ m → ∀ y ∈ V,
      Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk y))
    (h : Nontrivial (((DerivedCategory.homologyFunctor X.Modules n).obj K).presheaf.stalk y)) :
    n = m := by
  by_contra hne
  exact not_nontrivial_iff_subsingleton.mpr (hm n hne y hyV) h

/-- **On a Cohen–Macaulay scheme, the locus where a given cohomology sheaf of a dualizing complex
is nonzero is open and closed.** -/
theorem isClopen_setOf_nontrivial_stalk_homology_of_isCohenMacaulay {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (hX : AlgebraicGeometry.IsCohenMacaulay X) (n : ℤ) :
    IsClopen {x : X |
      Nontrivial (((DerivedCategory.homologyFunctor X.Modules n).obj K).presheaf.stalk x)} := by
  have hloc := (isCohenMacaulay_iff_locally_unique_homology K hK).mp hX
  have key : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      ((∀ y ∈ V, Nontrivial (((DerivedCategory.homologyFunctor X.Modules n).obj K).presheaf.stalk
        y)) ∨
      (∀ y ∈ V, ¬ Nontrivial (((DerivedCategory.homologyFunctor X.Modules n).obj K).presheaf.stalk
        y))) := by
    intro x
    obtain ⟨V, hxV, m, hm⟩ := hloc x
    refine ⟨V, hxV, ?_⟩
    by_cases hmn : m = n
    · subst hmn
      refine Or.inl fun y hy => ?_
      obtain ⟨i, hi⟩ := exists_nontrivial_stalk_homology_of_isDualizingComplex hK y
      obtain rfl := eq_of_nontrivial_stalk_homology hy hm hi
      exact hi
    · exact Or.inr fun y hy h => hmn (eq_of_nontrivial_stalk_homology hy hm h).symm
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨V, hxV, hV | hV⟩ := key x
    · exact absurd (hV x hxV) hx
    · exact ⟨V, hV, V.2, hxV⟩
  · rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨V, hxV, hV | hV⟩ := key x
    · exact ⟨V, hV, V.2, hxV⟩
    · exact absurd hx (hV x hxV)

/-! ### Dimension -/

/-- **A space of dimension at least one has an irreducible component of dimension at least
one.** -/
theorem exists_mem_irreducibleComponents_one_le_topologicalKrullDim {T : Type*}
    [TopologicalSpace T] (h : 1 ≤ topologicalKrullDim T) :
    ∃ W ∈ irreducibleComponents T, 1 ≤ topologicalKrullDim W := by
  have h1 : 1 ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds T) := by
    rwa [← topologicalKrullDim]
  obtain ⟨A, B, hAB⟩ := Order.one_le_krullDim_iff.mp h1
  obtain ⟨W, hW, hBW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible (B : Set T)
    B.isIrreducible
  refine ⟨W, hW, ?_⟩
  have hAB₁ : (A : Set T) ⊆ B := le_of_lt hAB
  have hAW : (A : Set T) ⊆ W := hAB₁.trans hBW
  let pre : ∀ C : TopologicalSpace.IrreducibleCloseds T, (C : Set T) ⊆ W →
      TopologicalSpace.IrreducibleCloseds W := fun C hC =>
    { carrier := (Subtype.val : W → T) ⁻¹' C
      isIrreducible' := by
        have : IrreducibleSpace (C : Set T) := Subtype.irreducibleSpace C.isIrreducible
        have he : Set.inclusion hC '' (Set.univ : Set (C : Set T)) =
            (Subtype.val : W → T) ⁻¹' C := by
          ext x
          refine ⟨?_, fun hx => ⟨⟨x.1, hx⟩, Set.mem_univ _, rfl⟩⟩
          rintro ⟨y, -, rfl⟩
          exact y.2
        rw [← he]
        exact (IrreducibleSpace.isIrreducible_univ (C : Set T)).image _
          (continuous_inclusion hC).continuousOn
      isClosed' := C.isClosed.preimage continuous_subtype_val }
  refine Order.one_le_krullDim_iff.mpr ⟨pre A hAW, pre B hBW, ?_⟩
  refine lt_of_le_of_ne (fun x hx => hAB₁ hx) fun heq => ?_
  have hset : ((Subtype.val : W → T) ⁻¹' A) = (Subtype.val : W → T) ⁻¹' B :=
    congrArg (fun C : TopologicalSpace.IrreducibleCloseds W => (C : Set W)) heq
  refine (ne_of_lt hAB) (TopologicalSpace.IrreducibleCloseds.ext (hAB₁.antisymm fun x hx => ?_))
  have : (⟨x, hBW hx⟩ : W) ∈ (Subtype.val : W → T) ⁻¹' B := hx
  rwa [← hset] at this

/-- **A nonempty open and closed subset of an equidimensional space of dimension one has
dimension at least one.** -/
theorem one_le_topologicalKrullDim_of_isClopen {T : Type*} [TopologicalSpace T]
    (hequi : TopologicalSpace.Equidimensional T) (hdim : topologicalKrullDim T = 1) {U : Set T}
    (hU : IsClopen U) (hne : U.Nonempty) : 1 ≤ topologicalKrullDim U := by
  obtain ⟨W, hWc, hWd⟩ := exists_mem_irreducibleComponents_one_le_topologicalKrullDim hdim.ge
  obtain ⟨x, hx⟩ := hne
  have hZU : irreducibleComponent x ⊆ U :=
    (isIrreducible_irreducibleComponent (x := x)).2.isPreconnected.subset_isClopen hU
      ⟨x, mem_irreducibleComponent, hx⟩
  have hZd : 1 ≤ topologicalKrullDim (irreducibleComponent x) := by
    rwa [hequi _ (irreducibleComponent_mem_irreducibleComponents x) W hWc]
  exact hZd.trans (Topology.IsEmbedding.inclusion hZU).isInducing.topologicalKrullDim_le

/-- **An affine scheme proper over a field has dimension zero.** -/
theorem topologicalKrullDim_nonpos_of_isAffine_of_isProper {k : Type u} [Field k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) [IsProper g] [IsAffine Y] :
    topologicalKrullDim Y ≤ 0 := by
  have : IsFinite g := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have hfin : g.appTop.hom.Finite := g.finite_appTop
  let φ : k →+* Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom
  have hφ : φ.Finite := by
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom.Finite
    rw [CommRingCat.hom_comp]
    exact hfin.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  let := φ.toAlgebra
  have : Module.Finite k Γ(Y, ⊤) := hφ
  have : IsArtinianRing Γ(Y, ⊤) := IsArtinianRing.of_finite k _
  have h1 : topologicalKrullDim Y = topologicalKrullDim (PrimeSpectrum Γ(Y, ⊤)) :=
    IsHomeomorph.topologicalKrullDim_eq _ Y.isoSpec.hom.homeomorph.isHomeomorph
  rw [h1, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have := (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp ‹_›).2
  exact_mod_cast (Ring.krullDimLE_iff (n := 0)).mp this

/-! ### The dualizing sheaf of a Cohen–Macaulay curve has full support -/

/-- A vector space over a field whose dual is trivial is trivial. -/
theorem subsingleton_of_subsingleton_dual_field {k : Type*} [Field k] {V : Type*}
    [AddCommGroup V] [Module k V] (h : Subsingleton (V →ₗ[k] k)) : Subsingleton V :=
  ⟨fun a b => by
    have key : ∀ v : V, v = 0 := fun v =>
      (Module.forall_dual_apply_eq_zero_iff k v).mp fun φ => by
        rw [Subsingleton.elim φ 0, LinearMap.zero_apply]
    rw [key a, key b]⟩

/-- A morphism from the pushforward of a module along a closed open immersion `U.ι` to a module
whose stalks vanish on `U` is zero. -/
theorem eq_zero_of_subsingleton_stalk_of_mem {X : Scheme.{u}} (U : X.Opens)
    [IsClosedImmersion U.ι] {F : X.Modules} (hF : ∀ y ∈ U, Subsingleton (F.presheaf.stalk y))
    (G : U.toScheme.Modules) (φ : (Scheme.Modules.pushforward U.ι).obj G ⟶ F) : φ = 0 := by
  refine (AlgebraicGeometry.SheafOfModules.eq_zero_iff_stalkMap_apply_eq_zero _ φ).mpr
    fun y m => ?_
  by_cases hy : y ∈ U
  · exact @Subsingleton.elim _ (hF y hy) _ _
  · have hsub := subsingleton_stalk_pushforward_of_notMemRange' U.ι G y
      (by rwa [Scheme.Opens.range_ι])
    have hm : m = (0 : ↑(SheafOfModules.stalkObj X.ringCatSheaf y
        ((Scheme.Modules.pushforward U.ι).obj G))) := @Subsingleton.elim _ hsub _ _
    rw [hm, map_zero]

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **The dualizing sheaf of a proper Cohen–Macaulay scheme over a field, equidimensional of
dimension one, has nonzero stalk at every point.** -/
theorem nontrivial_stalk_dualizingSheafOverField_of_isCohenMacaulay
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (x : X) :
    Nontrivial ((dualizingSheafOverField f).presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hK := isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one f hdim.le
  have hS := isClopen_setOf_nontrivial_stalk_homology_of_isCohenMacaulay hK hcm (-1)
  by_contra hx
  let U : X.Opens := ⟨_, hS.isClosed.isOpen_compl⟩
  have hUc : IsClosed (U : Set X) := hS.isOpen.isClosed_compl
  have : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  have hzero := eq_zero_of_subsingleton_stalk_of_mem U (F := dualizingSheafOverField f)
    fun y hy => not_nontrivial_iff_subsingleton.mp hy
  have hvan : ∀ G : U.toScheme.Modules, G.IsQuasicoherent →
      Subsingleton (cohomologyOverField k (U.ι ≫ f) G 1) := by
    intro G hG
    have hFq := ProperCoherentFiniteType.isQuasicoherent_pushforward U.ι G hG
    have hhom : Subsingleton
        ((Scheme.Modules.pushforward U.ι).obj G ⟶ dualizingSheafOverField f) :=
      ⟨fun a b => (hzero G a).trans (hzero G b).symm⟩
    have hdual : Subsingleton (cohomologyOverField k f
        ((Scheme.Modules.pushforward U.ι).obj G) 1 →ₗ[k] k) :=
      (clauseFiveAddEquiv f hdim.le _ hFq).symm.injective.subsingleton
    have := subsingleton_of_subsingleton_dual_field hdual
    exact (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k U.ι f G 1).toLinearEquiv.toEquiv
      |>.subsingleton
  have : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ f)
  have : IsAffine U.toScheme :=
    Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal U.toScheme fun I hI =>
      @ModuleCat.isZero_of_subsingleton _ _ _ (hvan _ hI)
  have h0 := topologicalKrullDim_nonpos_of_isAffine_of_isProper (U.ι ≫ f)
  have h1 := one_le_topologicalKrullDim_of_isClopen hequi hdim ⟨hUc, U.2⟩ ⟨x, hx⟩
  exact absurd (h1.trans h0 : (1 : WithBot ℕ∞) ≤ 0) (by decide)

/-- **The dualizing complex of a proper Cohen–Macaulay scheme over a field, equidimensional of
dimension one, has no cohomology outside degree `-1`.** -/
theorem isZero_homology_dualizingComplexOverField_of_isCohenMacaulay
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (i : ℤ) (hi : i ≠ -1) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      (dualizingComplexOverField f).obj) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hK := isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one f hdim.le
  have hloc := (isCohenMacaulay_iff_locally_unique_homology _ hK).mp hcm
  refine (AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj
    X.ringCatSheaf _).mpr fun y => ModuleCat.isZero_iff_subsingleton.mpr ?_
  obtain ⟨V, hyV, m, hm⟩ := hloc y
  have hω := nontrivial_stalk_dualizingSheafOverField_of_isCohenMacaulay f hcm hequi hdim y
  obtain rfl := eq_of_nontrivial_stalk_homology hyV hm hω
  exact hm i hi y hyV

/-- **`ω_X^• ∈ D^{≤ -1}`** for a proper Cohen–Macaulay scheme over a field, equidimensional of
dimension one. -/
theorem isLE_dualizingComplexOverField_of_isCohenMacaulay
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    (dualizingComplexOverField f).obj.IsLE (-1) :=
  (DerivedCategory.isLE_iff _ (-1)).mpr fun i hi =>
    isZero_homology_dualizingComplexOverField_of_isCohenMacaulay f hcm hequi hdim i (by omega)

/-- **`ω_X[1] ≅ ω_X^•`** for a proper Cohen–Macaulay scheme `X` over a field `k`, equidimensional
of dimension one, where `ω_X^• = f^×(𝒪_{Spec k})` and `ω_X = H^{-1}(ω_X^•)` are as in
[Stacks, Tag 0BS2]. It is the identification `ω_X[1] ≅ τ^{≤ -1}(ω_X^•)` followed by the
truncation morphism `τ^{≤ -1}(ω_X^•) ⟶ ω_X^•`, which is invertible since `ω_X^• ∈ D^{≤ -1}`. -/
def dualizingSheafShiftOneIsoOfIsCohenMacaulay
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f))⟦(1 : ℤ)⟧ ≅
      (dualizingComplexOverField f).obj :=
  haveI := isLE_dualizingComplexOverField_of_isCohenMacaulay f hcm hequi hdim
  singleShiftOneIsoTruncLE f hdim.le ≪≫
    asIso ((DerivedCategory.TStructure.t.truncLEι (-1)).app (dualizingComplexOverField f).obj)

end Stacks.Duality

end
