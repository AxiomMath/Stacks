module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllFiltration

/-!
# The cover of Tag 0A3R is connected

Let `S` be a connected scheme, `ℓ` a prime and `F` a finite type locally constant sheaf of
`F_ℓ`-vector spaces on `S_étale`. The cover `f : T → S` constructed in the proof of Tag 0A3R
(`Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_relSeries_constantRankOneStep`) is the
cover attached to the open subgroup `ρ̄⁻¹(H)` of `π₁(S, s̄)`, for `H` an `ℓ`-Sylow subgroup of the
monodromy group: `π₁(S, s̄)` acts transitively on its geometric fibre, so `T` is connected.
This file records that, together with the rest of the conclusion of Tag 0A3R.

## Main results

* `Stacks.EtaleCohomology.exists_connected_primeToEll_finiteEtale_relSeries_constantRankOneStep`:
  Tag 0A3R with a connected cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

/-- **Tag 0A3R with a connected cover.** Let `S` be a connected scheme, `ℓ` a prime number and
`F` a finite type locally constant sheaf of `F_ℓ`-vector spaces on `S_étale`. Then there is a
finite étale morphism `f : T → S` of degree prime to `ℓ`, with `T` connected, such that `f⁻¹F`
has a finite filtration whose successive quotients are isomorphic to `Z/ℓZ_T`. -/
theorem exists_connected_primeToEll_finiteEtale_relSeries_constantRankOneStep {ℓ : ℕ}
    (hℓ : ℓ.Prime) {S : Scheme.{u}} [ConnectedSpace S]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
    (hF : IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology F) :
    ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧ ConnectedSpace T ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ X : RelSeries (ConstantRankOneStep.{0} ℓ ((smallEtalePullbackZMod.{0} ℓ f).obj F)),
        IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨p⟩ : Nonempty S := inferInstance
  obtain ⟨s⟩ : Nonempty (GeometricPoint S) := ⟨S.algClosedPoint p⟩
  let B := BigEtaleSite.containing S
  let XS : B.Scheme := ⟨S, BigEtaleSite.contains_containing S⟩
  have : ConnectedSpace XS.1 := inferInstanceAs (ConnectedSpace S)
  let Xc : FiniteEtaleOver S := (representingCover B XS).obj (zmodFibreSetSheaf ℓ B XS ⟨F, hF⟩)
  have : Finite ((finiteEtaleFiberFunctor s).obj Xc) := finite_finiteEtaleFiber s Xc
  let := etaleFundamentalGroupMulAction S s Xc
  let ρ : EtaleFundamentalGroup S s →* Equiv.Perm ((finiteEtaleFiberFunctor s).obj Xc) :=
    MulAction.toPermHom _ _
  let Gρ := ρ.range
  let H : Sylow ℓ Gρ := Classical.arbitrary _
  let rb := ρ.rangeRestrict
  have hrbsurj : Function.Surjective rb := ρ.rangeRestrict_surjective
  have hker : IsOpen ((ρ.ker : Subgroup (EtaleFundamentalGroup S s)) :
      Set (EtaleFundamentalGroup S s)) := by
    have : ((ρ.ker : Subgroup (EtaleFundamentalGroup S s)) : Set (EtaleFundamentalGroup S s)) =
        ⋂ y : (finiteEtaleFiberFunctor s).obj Xc,
          ((MulAction.stabilizer (EtaleFundamentalGroup S s) y :
            Subgroup (EtaleFundamentalGroup S s)) : Set (EtaleFundamentalGroup S s)) := by
      ext τ
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, MulAction.mem_stabilizer_iff]
      exact ⟨fun h y ↦ congrArg (fun g : Equiv.Perm _ ↦ g y) h, fun h ↦ Equiv.ext h⟩
    rw [this]
    exact isOpen_iInter_of_finite fun y ↦
      EtaleFundamentalGroup.isOpen_coe_of_isOpenSubgroup ⟨Xc, y, rfl⟩
  have hle : ρ.ker ≤ (H : Subgroup Gρ).comap rb := fun τ hτ ↦ by
    have : rb τ = 1 := Subtype.ext hτ
    simp [Subgroup.mem_comap, this]
  let U : OpenSubgroup (EtaleFundamentalGroup S s) :=
    ⟨(H : Subgroup Gρ).comap rb, Subgroup.isOpen_mono hle hker⟩
  obtain ⟨T, φ, hφ⟩ := exists_finiteEtaleOver_quotient_fiber_equiv s U
  set y₀ := φ.symm ((1 : EtaleFundamentalGroup S s) : EtaleFundamentalGroup S s ⧸ U.toSubgroup)
  have hφy₀ : φ y₀ = ((1 : EtaleFundamentalGroup S s) :
      EtaleFundamentalGroup S s ⧸ U.toSubgroup) := φ.apply_symm_apply _
  have hφσ : ∀ σ : EtaleFundamentalGroup S s,
      φ (σ • y₀) = (σ : EtaleFundamentalGroup S s ⧸ U.toSubgroup) := by
    intro σ
    rw [hφ, hφy₀]
    show ((σ * 1 : EtaleFundamentalGroup S s) : EtaleFundamentalGroup S s ⧸ U.toSubgroup) = _
    rw [mul_one]
  have htrans : ∀ z, ∃ σ : EtaleFundamentalGroup S s, σ • y₀ = z := fun z ↦ by
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (φ z)
    exact ⟨a, φ.injective ((hφσ a).trans ha)⟩
  have hstab : ∀ σ : EtaleFundamentalGroup S s, σ • y₀ = y₀ → rb σ ∈ H := by
    intro σ hσ
    have h := hφσ σ
    rw [hσ, hφy₀] at h
    have h3 : σ ∈ U.toSubgroup := by simpa using QuotientGroup.eq.mp h
    exact h3
  have : IsGaloisCategory (setValuedFiberFunctor (finiteEtaleFiberFintypeFunctor S s)) :=
    Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor s
  have : ConnectedSpace T.left := by
    have : Nonempty ((finiteEtaleFiberFintypeFunctor S s).obj T) := ⟨y₀⟩
    have : MulAction.IsPretransitive (Aut (finiteEtaleFiberFintypeFunctor S s))
        ((finiteEtaleFiberFintypeFunctor S s).obj T) := ⟨fun a b ↦ by
      obtain ⟨σa, rfl⟩ := htrans a
      obtain ⟨σb, rfl⟩ := htrans b
      refine ⟨(autMulEquivEtaleFundamentalGroup S s).symm (σb * σa⁻¹), ?_⟩
      have h := congrArg (fun τ : EtaleFundamentalGroup S s ↦ τ • σa • y₀)
        ((autMulEquivEtaleFundamentalGroup S s).apply_symm_apply (σb * σa⁻¹))
      simp only [smul_smul, inv_mul_cancel_right] at h
      exact h⟩
    exact connectedSpace_left_of_isConnected T
      (CategoryTheory.isConnected_of_fiber_pretransitive (finiteEtaleFiberFintypeFunctor S s) T)
  have hfixs : ∀ τ : EtaleFundamentalGroup S s, (τ.app T).hom y₀ = y₀ → ∃ k : ℕ,
      ∀ q : (finiteEtaleFiberFunctor s).obj Xc, ((τ ^ (ℓ ^ k)).app Xc).hom q = q := by
    intro τ hτ
    obtain ⟨k, hk⟩ := H.isPGroup' ⟨rb τ, hstab τ hτ⟩
    refine ⟨k, fun q ↦ ?_⟩
    have h1 : rb (τ ^ (ℓ ^ k)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    exact congrArg (fun g : Equiv.Perm _ ↦ g q) (congrArg Subtype.val h1 : ρ (τ ^ (ℓ ^ k)) = 1)
  let t : GeometricPoint T.left := { residueField := s.residueField, hom := y₀.1 }
  have hts : s = t.map T.hom := by
    show s = GeometricPoint.mk s.residueField (y₀.1 ≫ T.hom)
    rw [y₀.2]
    rfl
  have key : ∀ (s' : GeometricPoint S) (h : s = s') (τ : EtaleFundamentalGroup S s'),
      (τ.app T).hom (h ▸ y₀) = h ▸ y₀ → ∃ k : ℕ,
        ∀ q : (finiteEtaleFiberFunctor s').obj Xc, ((τ ^ (ℓ ^ k)).app Xc).hom q = q :=
    fun s' h ↦ by subst h; exact hfixs
  have hval : ∀ (s₁ s₂ : GeometricPoint S) (h : s₁ = s₂) (y : (finiteEtaleFiberFunctor s₁).obj T),
      HEq (h ▸ y : (finiteEtaleFiberFunctor s₂).obj T).1 y.1 :=
    fun s₁ s₂ h y ↦ by subst h; rfl
  have hy : (hts ▸ y₀ : (finiteEtaleFiberFunctor (t.map T.hom)).obj T) = ⟨t.hom, rfl⟩ :=
    Subtype.ext (eq_of_heq (hval _ _ hts y₀))
  have key' := key _ hts
  rw [hy] at key'
  refine ⟨T.left, T.hom, Nat.card ((finiteEtaleFiberFunctor s).obj T), T.prop.1, T.prop.2,
    ‹ConnectedSpace T.left›,
    isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber s T, ?_,
    exists_relSeries_constantRankOneStep_of_stabilizer hℓ XS F hF T t key'⟩
  have hcardfib : Nat.card ((finiteEtaleFiberFunctor s).obj T) =
      Nat.card (EtaleFundamentalGroup S s ⧸ U.toSubgroup) := Nat.card_congr φ
  rw [hcardfib, ← Subgroup.index_eq_card]
  show ¬ ℓ ∣ ((H : Subgroup Gρ).comap rb).index
  rw [Subgroup.index_comap_of_surjective _ hrbsurj]
  exact H.not_dvd_index

end Stacks.EtaleCohomology

end
