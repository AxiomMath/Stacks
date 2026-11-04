module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagChart
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerNondivisibleReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineStalkCount

/-!
# The Kummer flag class of an étale chart is a purity class of its centre

Let `K` be algebraically closed, `ℓ` a prime invertible in `K` and `ζ` a primitive `ℓ`-th root of
unity. For `U` affine irreducible over `K` and an étale `ψ : U ⟶ 𝔸^d_K` whose coordinates vanish
simultaneously exactly at one point `y`, the Kummer flag class of the divisor data of the
coordinates is a purity class of the fibre `T = ψ⁻¹(0)` of `ψ` over the origin, which is a single
`K`-point: this is `Stacks.EtaleCohomology.KummerFlag.KummerFlagPurity`, proved here as
`Stacks.EtaleCohomology.KummerFlag.kummerFlagPurity`.

* `T ⟶ Spec K` is étale with one point over an algebraically closed field, hence an isomorphism
  (`isIso_of_etale_of_subsingleton`).
* `k : T ⟶ U` has a purity class of degree `2d`: `T` is the pullback of the coordinate flag
  `𝔸^0 ⊆ 𝔸^d` of principal smooth divisors along the étale `ψ`
  (`exists_purityClassFun_fibre_origin`, from
  `Stacks.EtaleCohomology.Purity.exists_purityClass_of_isPrincipalFlag`).
* The flag sheaf is `k_* Λ_T` and the canonical map is nonzero
  (`Stacks.EtaleCohomology.KummerFlag.nonempty_flagSheaf_iso`,
  `Stacks.EtaleCohomology.KummerFlag.flagUnit_ne_zero`).
* The Kummer flag class is nonzero: it is the inverse image along `ψ` (after reversing the order
  of the coordinates) of the Kummer flag class of the coordinates of `𝔸^d_K`, which is nonzero
  (`Stacks.EtaleCohomology.KummerFlag.kummerFlagClass_stdDatum_ne_zero`), and the inverse image
  along the étale neighbourhood `ψ` of the origin is injective on `Ext` out of sheaves supported
  at the origin
  (`Stacks.EtaleCohomology.Purity.injective_mapExactFunctor_inverseImage_of_isPullback`).
* A nonzero class of degree `2d` is a purity class, the point `T` being irreducible
  (`Stacks.EtaleCohomology.KummerFlag.isPurityClassFun_of_ne_zero`).

## Main results

* `Stacks.EtaleCohomology.KummerFlag.kummerFlagPurity`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.ExtTransport

universe u

namespace Stacks.EtaleCohomology.KummerFlag

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

section PointFibre

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **An étale scheme with one point over an algebraically closed field is the field itself.** -/
theorem isIso_of_etale_of_subsingleton {T : Scheme.{u}} [IsAffine T] [Subsingleton T]
    [Nonempty T] (p : T ⟶ Spec (.of K)) [Etale p] : IsIso p := by
  let e : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let f : K →+* Γ(T, ⊤) := p.appTop.hom.comp e.toRingHom
  let : Algebra K Γ(T, ⊤) := f.toAlgebra
  have : Algebra.Etale K Γ(T, ⊤) := RingHom.Etale.respectsIso.right p.appTop.hom e
    ((HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 inferInstance)
  have : Nontrivial Γ(T, ⊤) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨t⟩ := ‹Nonempty T›
    have : IsEmpty (Spec Γ(T, ⊤)) := inferInstanceAs (IsEmpty (PrimeSpectrum Γ(T, ⊤)))
    exact this.false (T.isoSpec.hom.base t)
  have : IsLocalRing Γ(T, ⊤) := by
    refine IsLocalRing.of_unique_max_ideal ?_
    obtain ⟨I, hI⟩ := Ideal.exists_maximal Γ(T, ⊤)
    refine ⟨I, hI, fun J hJ => ?_⟩
    let pI : Spec Γ(T, ⊤) := ⟨I, hI.isPrime⟩
    let pJ : Spec Γ(T, ⊤) := ⟨J, hJ.isPrime⟩
    have h : T.isoSpec.inv.base pJ = T.isoSpec.inv.base pI := Subsingleton.elim _ _
    have h' := congrArg T.isoSpec.hom.base h
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.inv_hom_id] at h'
    exact congrArg PrimeSpectrum.asIdeal h'
  have hbij' : Function.Bijective p.appTop := by
    have : (p.appTop : Γ(Spec (.of K), ⊤) → Γ(T, ⊤)) = f ∘ e.symm := by
      funext x
      simp [f]
    rw [this]
    exact (Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing K Γ(T, ⊤)).comp
      e.symm.bijective
  have : IsIso p.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hbij'
  have hp : p = T.isoSpec.hom ≫ Spec.map p.appTop ≫ (Spec (.of K)).isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality p, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [hp]
  infer_instance

end PointFibre

section FlagPurity

attribute [local instance] moduleCat_hasLimitsOfSize

variable (K : Type u) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime]

omit [IsAlgClosed K] in
/-- The coordinate subspace `𝔸^0 ⊆ 𝔸^{0+n}` is the origin. -/
theorem coordinateSubspaceEmbedding_zero_left (n : ℕ) :
    Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding (Spec (.of K)) 0 n =
      (𝔸(ULift.{u} (Fin 0); Spec (.of K)) ↘ Spec (.of K)) ≫
        AlgebraicGeometry.GoodNeighbourhood.origin (k := K) (0 + n) := by
  ext1
  · rw [Category.assoc, AffineSpace.homOfVector_over, Category.comp_id]
    exact Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_over _ 0 n
  · rename_i j
    obtain ⟨j⟩ := j
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, goodNeighbourhoodOrigin_appTop_coord,
      map_zero]
    induction j using Fin.addCases with
    | left i => exact i.elim0
    | right i => exact Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_lastCoordinate _ 0 n i

/-- **The fibre over the origin of an étale chart has a purity class of degree `2d`.** -/
theorem exists_purityClassFun_fibre_origin (hℓ : IsUnit (ℓ : K)) (d : ℕ)
    {U T : Scheme.{u}} (ψ : U ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K))) [Etale ψ] (k : T ⟶ U)
    [IsClosedImmersion k] (p : T ⟶ Spec (.of K))
    (h : IsPullback k p ψ (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) d)) :
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) k).obj (unitSheaf (X := T) ℓ))
        (unitSheaf (X := U) ℓ) (2 * d),
      Purity.IsPurityClassFun ℓ (etaleModuleDirectImage.{u, 0} (ZMod ℓ) k)
        (unitSheaf (X := U) ℓ) γ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : IsIso (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) 0 ≫
        (𝔸(ULift.{u} (Fin 0); Spec (.of K)) ↘ Spec (.of K))) := by
      rw [AffineSpace.homOfVector_over]
      infer_instance
    have : IsIso (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) 0) :=
      IsIso.of_isIso_comp_right _ (𝔸(ULift.{u} (Fin 0); Spec (.of K)) ↘ Spec (.of K))
    have : IsIso k := h.isIso_fst_of_isIso
    exact Purity.exists_purityClassFun_of_isIso k
  · obtain ⟨n, rfl⟩ : ∃ n, d = 0 + n := ⟨d, (Nat.zero_add d).symm⟩
    have hpb : IsPullback k (p ≫ inv (𝔸(ULift.{u} (Fin 0); Spec (.of K)) ↘ Spec (.of K))) ψ
        (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding (Spec (.of K)) 0 n) :=
      h.of_iso (Iso.refl _) (Iso.refl _) (asIso (𝔸(ULift.{u} (Fin 0); Spec (.of K)) ↘
        Spec (.of K))).symm (Iso.refl _) (by simp) (by simp) (by simp)
        (by rw [coordinateSubspaceEmbedding_zero_left]; simp)
    have : Smooth ψ := inferInstance
    have hflag :=
      (Purity.isPrincipalFlag_coordinateSubspaceEmbedding K 0 n (by omega)).of_isPullback K hpb
    obtain ⟨γ, hγ⟩ := Purity.exists_purityClass_of_isPrincipalFlag (ℓ := ℓ) hℓ hflag
    rw [Nat.zero_add]
    exact ⟨γ, hγ⟩

omit [IsAlgClosed K] in
/-- Two morphisms to the affine line agree if they agree over `K` and on the coordinate. -/
theorem affineLine_hom_ext {S : Scheme.{u}} {f g : S ⟶ Purity.affineLine K}
    (h₁ : f ≫ (Purity.affineLine K ↘ Spec (.of K)) = g ≫ (Purity.affineLine K ↘ Spec (.of K)))
    (h₂ : f.appTop (Purity.coordinate K) = g.appTop (Purity.coordinate K)) : f = g := by
  ext1
  · exact h₁
  · rename_i j
    obtain ⟨j⟩ := j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact h₂

omit [IsAlgClosed K] in
/-- The coordinate of the affine line pulls back to `0` along any map through the origin. -/
theorem comp_origin_appTop_coordinate {S : Scheme.{u}} (g : S ⟶ Spec (.of K)) :
    (g ≫ Purity.origin K).appTop (Purity.coordinate K) = 0 := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Purity.origin_appTop_coordinate, map_zero]

/-- Reversing the order of the coordinates of `𝔸^d_S` is an involution. -/
private theorem reindex_rev_comp_self (S : Scheme.{u}) (d : ℕ) :
    AffineSpace.reindex (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) S ≫
      AffineSpace.reindex (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) S =
        𝟙 _ := by
  rw [Stacks.Chow.affineSpace_reindex_comp, ← AffineSpace.reindex_id]
  congr 1
  funext j
  simp

/-- Reversing the order of the coordinates of `𝔸^d_S` is an isomorphism. -/
private theorem isIso_reindex_rev (S : Scheme.{u}) (d : ℕ) :
    IsIso (AffineSpace.reindex
      (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) S) :=
  ⟨⟨_, reindex_rev_comp_self S d, reindex_rev_comp_self S d⟩⟩

/-- After reversing the order of the coordinates, the `m.rev`-th coordinate pulls back to the
`m`-th one. -/
private theorem reindex_rev_appTop_coord (S : Scheme.{u}) {d : ℕ} {U : Scheme.{u}}
    (ψ : U ⟶ 𝔸(ULift.{u} (Fin d); S)) (m : Fin d) :
    (ψ ≫ AffineSpace.reindex (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d)))
      S).appTop (AffineSpace.coord S ⟨m.rev⟩) = ψ.appTop (AffineSpace.coord S ⟨m⟩) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord]
  simp

omit [IsAlgClosed K] in
/-- The fibre over the origin of an étale chart, after reversing its coordinates, is the common
zero `y` of the coordinates. -/
private theorem range_eq_singleton_of_isPullback_reindex_origin {d : ℕ} {U T : Scheme.{u}}
    (ψ : U ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K))) (y : U)
    (hy : ∀ x : U, (∀ m : Fin d, x ∉ U.basicOpen
      (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) ↔ x = y) (k : T ⟶ U)
    (p : T ⟶ Spec (.of K))
    (sq : IsPullback k p (ψ ≫ AffineSpace.reindex
      (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) (Spec (.of K)))
      (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) d)) :
    Set.range k.base = {y} := by
  let ψ' := ψ ≫ AffineSpace.reindex
    (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) (Spec (.of K))
  have hmem : ∀ (x : U) (c : Γ(𝔸(ULift.{u} (Fin d); Spec (.of K)), ⊤)),
      ψ'.base x ∈ (𝔸(ULift.{u} (Fin d); Spec (.of K))).basicOpen c ↔
        x ∈ U.basicOpen (ψ'.appTop c) := fun x c => by
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  rw [Stacks.Cohomology.ClosedImmersionBaseChange.range_eq_preimage_range_of_isPullback sq,
    range_goodNeighbourhoodOrigin]
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [← hy x]
  constructor
  · intro h m
    have := h ⟨m.rev⟩
    rwa [hmem, reindex_rev_appTop_coord] at this
  · rintro h ⟨j⟩
    rw [hmem, ← Fin.rev_rev j, reindex_rev_appTop_coord]
    exact h _

/-- **The fibre over the origin of an étale chart centred at a point is a single `K`-point.** -/
private theorem isIso_pullback_snd_reindex_origin {d : ℕ} {U : Scheme.{u}} [IsAffine U]
    (ψ : U ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K))) [Etale ψ] (y : U)
    (hy : ∀ x : U, (∀ m : Fin d, x ∉ U.basicOpen
      (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) ↔ x = y) :
    IsIso (pullback.snd (ψ ≫ AffineSpace.reindex
      (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) (Spec (.of K)))
        (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) d)) := by
  let R := AffineSpace.reindex (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d)))
    (Spec (.of K))
  have : IsIso R := isIso_reindex_rev _ d
  let T := pullback (ψ ≫ R) (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) d)
  let k : T ⟶ U := pullback.fst _ _
  have hrange : Set.range k.base = {y} :=
    range_eq_singleton_of_isPullback_reindex_origin K ψ y hy k _ (IsPullback.of_hasPullback _ _)
  have : Nonempty T := ⟨(hrange ▸ Set.mem_singleton y : y ∈ Set.range k.base).choose⟩
  have : Subsingleton T := ⟨fun t₁ t₂ => k.isClosedEmbedding.injective (by
    have h₁ : k.base t₁ ∈ Set.range k.base := ⟨t₁, rfl⟩
    have h₂ : k.base t₂ ∈ Set.range k.base := ⟨t₂, rfl⟩
    rw [hrange] at h₁ h₂
    exact h₁.trans h₂.symm)⟩
  have : IsAffine T := isAffine_of_isAffineHom k
  exact isIso_of_etale_of_subsingleton _

omit [IsAlgClosed K] in
/-- Away from the common zero `y` of the coordinates of a chart, some coordinate is invertible. -/
private theorem exists_mem_range_functionDatum_j_of_ne {d : ℕ} {U : Scheme.{u}} [IsAffine U]
    (ψ : U ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K))) (y : U)
    (hy : ∀ x : U, (∀ m : Fin d, x ∉ U.basicOpen
      (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) ↔ x = y) (x : U)
    (hx : x ≠ y) : ∃ m : Fin d, x ∈ Set.range
      (functionDatum (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩))).j.base := by
  obtain ⟨m, hm⟩ := not_forall_not.1 (mt (hy x).1 hx)
  refine ⟨m, ?_⟩
  show x ∈ Set.range (U.basicOpen _).ι
  rw [Scheme.Opens.range_ι]
  exact hm

omit [IsAlgClosed K] in
/-- The flag sheaf of the coordinates of `𝔸^d_K` is the direct image of the constant sheaf of
the origin. -/
private theorem nonempty_flagSheaf_stdDatum_iso (N d : ℕ) :
    Nonempty (flagSheaf (N := N) (stdDatum K d) ≅
      (etaleModuleDirectImage.{u, 0} (ZMod N)
        (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) d)).obj
          (unitSheaf (X := Spec (.of K)) N)) := by
  have := Purity.isClosedImmersion_origin K
  refine nonempty_flagSheaf_iso (stdDatum K d) _ (fun m => ⟨pullback.lift
    (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) d) (𝟙 _) ?_, pullback.lift_fst _ _ _⟩)
    fun x hx => ?_
  · apply affineLine_hom_ext K
    · rw [Category.assoc, coordProj_over, AffineSpace.homOfVector_over, Category.assoc,
        Purity.origin_over, Category.comp_id]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coordProj_appTop_coordinate,
        goodNeighbourhoodOrigin_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Purity.origin_appTop_coordinate, map_zero]
  · rw [range_goodNeighbourhoodOrigin] at hx
    simp only [Set.mem_setOf_eq, not_forall, not_not] at hx
    obtain ⟨⟨j⟩, hj⟩ := hx
    refine ⟨j.rev, ?_⟩
    show x ∈ Set.range (Scheme.Opens.ι _)
    rw [Scheme.Opens.range_ι]
    show x ∈ (𝔸(ULift.{u} (Fin d); Spec (.of K))).basicOpen
      ((coordProj K ⟨j.rev.rev⟩).appTop (Purity.coordinate K))
    rw [coordProj_appTop_coordinate, Fin.rev_rev]
    exact hj

omit [IsAlgClosed K] in
/-- **The inverse image along an étale neighbourhood of the origin of `𝔸^d_K` is injective** on
`Ext` out of the flag sheaf of the coordinates. -/
private theorem eq_zero_of_mapExactFunctor_inverseImage_stdDatum {d : ℕ} {U T : Scheme.{u}}
    (ψ : U ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K))) [Etale ψ] (k : T ⟶ U) [IsClosedImmersion k]
    (p : T ⟶ Spec (.of K)) [IsIso p]
    (sq : IsPullback k p ψ (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) d))
    (w : Ext (flagSheaf (N := ℓ) (stdDatum K d))
      (unitSheaf (X := 𝔸(ULift.{u} (Fin d); Spec (.of K))) ℓ) (2 * d))
    (hw : w.mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod ℓ) ψ) = 0) : w = 0 := by
  obtain ⟨eA⟩ := nonempty_flagSheaf_stdDatum_iso K ℓ d
  let G := etaleModuleInverseImage.{u, 0} (ZMod ℓ) ψ
  let w' := (Ext.mk₀ eA.inv).comp w (zero_add _)
  have hw' : w = (Ext.mk₀ eA.hom).comp w' (zero_add _) := by
    simp only [w', Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp]
  have h1 : w'.mapExactFunctor G = 0 := by
    have : (Ext.mk₀ (G.map eA.hom)).comp (w'.mapExactFunctor G) (zero_add _) = 0 := by
      rw [← Ext.mapExactFunctor_mk₀, ← Ext.mapExactFunctor_comp, ← hw', hw]
    exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (G.map eA.hom) _).1
      (this.trans (map_zero _).symm)
  have h2 : w' = 0 :=
    Purity.injective_mapExactFunctor_inverseImage_of_isPullback (ZMod ℓ) ψ _ k p sq
      (unitSheaf (X := Spec (.of K)) ℓ) _ (2 * d) (h1.trans (G.mapExtAddHom _ _ _).map_zero.symm)
  rw [hw', h2, Ext.comp_zero]

omit [IsAlgClosed K] in
/-- The Kummer flag class of the coordinates of an étale chart is the inverse image of that of
the coordinates of `𝔸^d_K`, after reversing their order, read through isomorphisms. -/
private theorem exists_kummerFlagClass_functionDatum_eq_transport {U : Scheme.{u}} [IsAffine U]
    [IrreducibleSpace U] (fU : U ⟶ Spec (.of K)) {d : ℕ}
    (ψ : U ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K)))
    (hψ : ψ ≫ (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K)) = fU) {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : IsUnit (ℓ : K)) :
    ∃ (a : flagSheaf (N := ℓ) (fun m => functionDatum
          (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩))) ⟶
        (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (ψ ≫ AffineSpace.reindex
          (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) (Spec (.of K)))).obj
            (flagSheaf (N := ℓ) (stdDatum K d)))
      (b : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (ψ ≫ AffineSpace.reindex
          (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) (Spec (.of K)))).obj
            (unitSheaf (X := 𝔸(ULift.{u} (Fin d); Spec (.of K))) ℓ) ⟶ unitSheaf (X := U) ℓ),
      IsIso a ∧ IsIso b ∧
      kummerFlagClass hζ hℓ fU (fun m => functionDatum
          (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩))) =
        transport (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (ψ ≫ AffineSpace.reindex
          (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) (Spec (.of K))))
          a b (2 * d) (kummerFlagClass hζ hℓ (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K))
            (stdDatum K d)) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have := Purity.isClosedImmersion_origin K
  let ψ' := ψ ≫ AffineSpace.reindex
    (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) (Spec (.of K))
  have hψ' : ψ' ≫ (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K)) = fU := by
    rw [Category.assoc, AffineSpace.reindex_over, hψ]
  have hRcoord : ∀ m : Fin d, ψ'.appTop (AffineSpace.coord (Spec (.of K)) ⟨m.rev⟩) =
      ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩) := reindex_rev_appTop_coord _ ψ
  have hgW : ∀ m : Fin d, (zeroSchemeι (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩)) ≫ ψ') ≫
      coordProj K ⟨m.rev⟩ = (zeroSchemeι (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩)) ≫ fU) ≫
        Purity.origin K := fun m => by
    apply affineLine_hom_ext K
    · rw [Category.assoc, Category.assoc, coordProj_over, hψ', Category.assoc, Category.assoc,
        Purity.origin_over, Category.comp_id]
    · have l : ((zeroSchemeι (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩)) ≫ ψ') ≫
          coordProj K ⟨m.rev⟩).appTop (Purity.coordinate K) =
          (zeroSchemeι (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩))).appTop
            (ψ'.appTop ((coordProj K ⟨m.rev⟩).appTop (Purity.coordinate K))) := rfl
      rw [l, coordProj_appTop_coordinate, hRcoord, zeroSchemeι_appTop_self]
      exact (comp_origin_appTop_coordinate K _).symm
  have hf : ∀ m : Fin d, ψ'.appTop (stdFun K d m) =
      ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩) := fun m => by
    show ψ'.appTop ((coordProj K ⟨m.rev⟩).appTop (Purity.coordinate K)) = _
    rw [coordProj_appTop_coordinate, hRcoord]
  let gW : ∀ m : Fin d, Spec (.of (Γ(U, ⊤) ⧸ Ideal.span
      {ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩)})) ⟶ stdW K d m :=
    fun m => pullback.lift _ _ (hgW m)
  have hW : ∀ m : Fin d, zeroSchemeι (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩)) ≫ ψ' =
      gW m ≫ stdι K d m := fun m => (pullback.lift_fst _ _ _).symm
  exact exists_kummerFlagClass_ofFunction_eq hζ hℓ
    (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K)) fU ψ' hψ'
    (fun m : Fin d => stdFun K d m) (fun m => stdι K d m) (fun m => stdRange K d m)
    (fun m : Fin d => ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩))
    (fun m => zeroSchemeι (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩)))
    (fun m => range_basicOpen_ι_eq_compl (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩)))
    hf gW hW fun m => preconnectedSpace_basicOpen _

/-- **The Kummer flag class of the coordinates of an étale neighbourhood of the origin is
nonzero.** -/
private theorem kummerFlagClass_functionDatum_ne_zero {U T : Scheme.{u}} [IsAffine U]
    [IrreducibleSpace U] (fU : U ⟶ Spec (.of K)) {d : ℕ}
    (ψ : U ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K))) [Etale ψ]
    (hψ : ψ ≫ (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K)) = fU) {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : IsUnit (ℓ : K)) (k : T ⟶ U) [IsClosedImmersion k]
    (p : T ⟶ Spec (.of K)) [IsIso p]
    (sq : IsPullback k p (ψ ≫ AffineSpace.reindex
      (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d))) (Spec (.of K)))
      (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) d)) :
    kummerFlagClass hζ hℓ fU
      (fun m => functionDatum (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩))) ≠ 0 := by
  let R := AffineSpace.reindex (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d)))
    (Spec (.of K))
  have : IsIso R := isIso_reindex_rev _ d
  obtain ⟨a, b, ha, hb, htr⟩ := exists_kummerFlagClass_functionDatum_eq_transport K fU ψ hψ hζ hℓ
  intro h0
  apply kummerFlagClass_stdDatum_ne_zero hζ hℓ d
  apply eq_zero_of_mapExactFunctor_inverseImage_stdDatum K (ψ ≫ R) k p sq
  rw [htr, transport_apply, sandwich_apply] at h0
  have h1 : ((kummerFlagClass hζ hℓ (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K))
      (stdDatum K d)).mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (ψ ≫ R))).comp
        (Ext.mk₀ b) (add_zero _) = 0 :=
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso a _).1 (h0.trans (map_zero _).symm)
  exact (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso b _).1
    (h1.trans (map_zero _).symm)

/-- **The Kummer flag class of an étale chart centred at a point is a purity class of the
point**, `Stacks.EtaleCohomology.KummerFlag.KummerFlagPurity`. -/
theorem kummerFlagPurity (ℓ : ℕ) [Fact ℓ.Prime] : KummerFlagPurity K ℓ := by
  intro U _ _ fU d ψ hψe hψ y hy ζ hζ hℓ
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have : Fact (1 < ℓ) := ⟨hp.one_lt⟩
  have : Etale ψ := hψe
  let R := AffineSpace.reindex (fun j : ULift.{u} (Fin d) => (⟨j.down.rev⟩ : ULift.{u} (Fin d)))
    (Spec (.of K))
  let ψ' := ψ ≫ R
  let z := AlgebraicGeometry.GoodNeighbourhood.origin (k := K) d
  let T := pullback ψ' z
  let k : T ⟶ U := pullback.fst _ _
  let pT : T ⟶ Spec (.of K) := pullback.snd _ _
  have sq : IsPullback k pT ψ' z := IsPullback.of_hasPullback _ _
  have : IsIso R := isIso_reindex_rev _ d
  have hψ' : ψ' ≫ (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K)) = fU := by
    rw [Category.assoc, AffineSpace.reindex_over, hψ]
  have hRcoord : ∀ m : Fin d, ψ'.appTop (AffineSpace.coord (Spec (.of K)) ⟨m.rev⟩) =
      ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩) := reindex_rev_appTop_coord _ ψ
  have hrange : Set.range k.base = {y} :=
    range_eq_singleton_of_isPullback_reindex_origin K ψ y hy k pT sq
  have : Nonempty T := ⟨(hrange ▸ Set.mem_singleton y : y ∈ Set.range k.base).choose⟩
  have : IsIso pT := isIso_pullback_snd_reindex_origin K ψ y hy
  have : IrreducibleSpace T :=
    Function.Surjective.irreducibleSpace (inv pT).continuous (inv pT).surjective
  let D := fun m : Fin d => functionDatum (ψ.appTop (AffineSpace.coord (Spec (.of K)) ⟨m⟩))
  have hkW : ∀ m, ∃ g' : T ⟶ (D m).W, g' ≫ (D m).i = k := fun m =>
    exists_comp_zeroSchemeι_eq k _ (by
      rw [← hRcoord m, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, sq.w,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, goodNeighbourhoodOrigin_appTop_coord,
        map_zero])
  obtain ⟨eU⟩ := nonempty_flagSheaf_iso (N := ℓ) D k hkW fun x hx =>
    exists_mem_range_functionDatum_j_of_ne K ψ y hy x (by rwa [hrange] at hx)
  have hsmooth : k ≫ fU = pT := by
    rw [← hψ', ← Category.assoc, sq.w, Category.assoc, AffineSpace.homOfVector_over,
      Category.comp_id]
  refine ⟨flagUnit_ne_zero D k hkW, T, k, inferInstance, inferInstance, ?_, eU, ?_⟩
  · rw [hsmooth]
    infer_instance
  · obtain ⟨γ, hγ⟩ := exists_purityClassFun_fibre_origin K (ℓ := ℓ) hℓ d ψ' k pT sq
    refine Purity.IsPurityClassFun.isPurityClass (isPurityClassFun_of_ne_zero hγ ?_)
    intro h0
    apply kummerFlagClass_functionDatum_ne_zero K fU ψ hψ hζ hℓ k pT sq
    have : kummerFlagClass hζ hℓ fU D = (Ext.mk₀ eU.hom).comp ((Ext.mk₀ eU.inv).comp
        (kummerFlagClass hζ hℓ fU D) (zero_add _)) (zero_add _) := by
      rw [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp]
    rw [this, h0, Ext.comp_zero]

end FlagPurity

end Stacks.EtaleCohomology.KummerFlag

end
