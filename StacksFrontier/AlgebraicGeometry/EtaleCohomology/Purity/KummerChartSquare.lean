module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerBaseChangeStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveUnitIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.LocallyConstantCoefficients

/-!
# The degree-one base change map on constant torsion coefficients over a square of charts

Let `h ≫ f' = e ≫ g` be a commutative square with `g : T ⟶ S` and `h : Y ⟶ X'` quasi-compact open
immersions, where `T` is the inverse image of the punctured line under a smooth `φ : S ⟶ 𝔸¹_k` and
`Y` that under a smooth `φ' : X' ⟶ 𝔸¹_{k'}`, and `f'^*(φ^* x) = φ'^* x` for the coordinate `x`.
Let `N` be invertible in `k` and in `k'` and suppose `T` lies over a field containing a primitive
`N`-th root of unity. Then for every finite abelian group `A` killed by `N`, the degree-one base
change map `f'⁻¹ R¹ g_* A ⟶ R¹ h_* e⁻¹ A` of the constant sheaf `A` is an isomorphism.

## Main results

* `Stacks.TorsionDevissage.isIso_app_of_finite_of_dvd`: a natural transformation between additive
  functors on abelian groups is invertible at every finite group killed by `N` once it is
  invertible at the cyclic groups `ℤ/n` with `n ∣ N`.
* `Stacks.EtaleCohomology.Purity.range_eq_basicOpen_of_isPullback_punctured`: the pullback of the
  punctured line along `φ` is the basic open of `φ^* x`.
* `Stacks.EtaleCohomology.Purity.isUnit_puncturedFunction_of_isPullback_punctured`: `φ^* x` is
  invertible on the pullback of the punctured line along `φ`.
* `Stacks.EtaleCohomology.Purity.isIso_higherBaseChangeMapAb_one_rootsOfUnity_of_charts`: the
  degree-one base change map on `μ_n` over a square of charts is an isomorphism.
* `Stacks.EtaleCohomology.Purity.isIso_higherBaseChangeMapAb_one_constantSheaf_of_charts`: the
  degree-one base change map on the constant sheaf of a finite abelian group killed by `N` over a
  square of charts is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe w u

namespace Stacks.TorsionDevissage

section Divisors

variable {𝒟 : Type*} [Category 𝒟] {G H : AddCommGrpCat.{w} ⥤ 𝒟} (η : G ⟶ H)
  [Preadditive 𝒟] [HasBinaryBiproducts 𝒟] [G.Additive] [H.Additive]

/-- The iso-locus contains every finite product of cyclic groups of order dividing `N`, as soon
as it contains these cyclic groups. -/
theorem isIso_app_piFin_of_dvd {N : ℕ}
    (hzmod : ∀ n : ℕ, 0 < n → n ∣ N → IsIso (η.app (AddCommGrpCat.of (ULift.{w} (ZMod n))))) :
    ∀ (n : ℕ) (q : Fin n → ℕ), (∀ j, 0 < q j) → (∀ j, q j ∣ N) →
      IsIso (η.app (AddCommGrpCat.of (ULift.{w} (∀ j : Fin n, ZMod (q j))))) := by
  intro n
  induction n with
  | zero =>
      intro q _ _
      refine isIso_app_of_iso η ?_ (hzmod 1 Nat.one_pos (one_dvd N))
      exact (subsingletonAddEquiv (ULift.{w} (ZMod 1))
        (ULift.{w} (∀ j : Fin 0, ZMod (q j)))).toAddCommGrpIso
  | succ n ih =>
      intro q hq hc
      have h0 : IsIso (η.app (AddCommGrpCat.of (ULift.{w} (ZMod (q 0))))) :=
        hzmod (q 0) (hq 0) (hc 0)
      have htail : IsIso (η.app (AddCommGrpCat.of
          (ULift.{w} (∀ j : Fin n, ZMod (q j.succ))))) :=
        ih (fun j => q j.succ) (fun j => hq _) (fun j => hc _)
      refine isIso_app_of_iso η ?_ (isIso_app_biprod η h0 htail)
      refine uliftProdBiprodIso _ _ ≪≫ ?_
      exact (AddEquiv.ulift.trans
        ((piFinSuccAddEquiv n (fun j => ZMod (q j))).trans AddEquiv.ulift.symm)).toAddCommGrpIso

/-- **The iso-locus contains every finite abelian group killed by `N`**, as soon as it contains
the cyclic groups of order dividing `N`. -/
theorem isIso_app_of_finite_of_dvd {N : ℕ}
    (hzmod : ∀ n : ℕ, 0 < n → n ∣ N → IsIso (η.app (AddCommGrpCat.of (ULift.{w} (ZMod n)))))
    (A : AddCommGrpCat.{w}) [Finite A] (hA : ∀ a : A, N • a = 0) :
    IsIso (η.app A) := by
  classical
  obtain ⟨ι, _, m, hm, ⟨f0⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (A : Type w)
  have f : (A : Type w) ≃+ ∀ i, ZMod (m i) := f0.trans (DirectSum.addEquivProd _)
  have hdvd : ∀ i, m i ∣ N := by
    intro i
    have h := congrFun (congrArg f (hA (f.symm (Pi.single (M := fun i => ZMod (m i)) i 1)))) i
    exact (ZMod.natCast_eq_zero_iff _ _).1 (by simpa using h)
  have key : IsIso (η.app (AddCommGrpCat.of
      (ULift.{w} (∀ j : Fin (Fintype.card ι), ZMod (m ((Fintype.equivFin ι).symm j)))))) :=
    isIso_app_piFin_of_dvd η hzmod _ _ (fun j => lt_trans Nat.one_pos (hm _)) (fun j => hdvd _)
  refine isIso_app_of_iso η ?_ key
  exact (AddEquiv.ulift.trans
    ((piCongrLeftAddEquiv (fun i => ZMod (m i)) (Fintype.equivFin ι)).symm.trans
      f.symm)).toAddCommGrpIso

end Divisors

end Stacks.TorsionDevissage

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k]

/-- **The pullback of the punctured line along `φ` is the basic open of `φ^* x`**, for `x` the
coordinate. -/
theorem range_eq_basicOpen_of_isPullback_punctured {V V₀ : Scheme.{u}} (φ : V ⟶ affineLine k)
    (j : V₀ ⟶ V) (φ₀ : V₀ ⟶ (punctured k).toScheme) (sq : IsPullback j φ₀ φ (punctured k).ι) :
    Set.range j.base = (V.basicOpen (φ.appTop (coordinate k)) : Set V) := by
  ext v
  rw [mem_range_iff_of_isPullback_punctured φ j φ₀ sq v, ← Scheme.preimage_basicOpen_top]
  rfl

/-- **`φ^* x` is invertible on the pullback of the punctured line along `φ`.** -/
theorem isUnit_puncturedFunction_of_isPullback_punctured {V V₀ : Scheme.{u}}
    (φ : V ⟶ affineLine k) (j : V₀ ⟶ V) [IsOpenImmersion j] (φ₀ : V₀ ⟶ (punctured k).toScheme)
    (sq : IsPullback j φ₀ φ (punctured k).ι) :
    IsUnit (puncturedFunction j ⊤ (φ.appTop (coordinate k))) := by
  have hr := range_eq_basicOpen_of_isPullback_punctured φ j φ₀ sq
  have hi : Set.range (pullback.fst φ (origin k)).base =
      ((V.basicOpen (φ.appTop (coordinate k)) : Set V))ᶜ := by
    rw [Scheme.Pullback.range_fst, range_origin, ← Scheme.preimage_basicOpen_top]
    rfl
  refine isUnit_puncturedFunction j (i := pullback.fst φ (origin k)) ?_ ?_
  · rw [hi, hr, compl_compl]
  · intro x hx
    have := hx.2
    rwa [hi, Set.notMem_compl_iff] at this

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g) [IsOpenImmersion g] [IsOpenImmersion h] [QuasiCompact g] [QuasiCompact h]

/-- **The degree-one base change map on `μ_n` over a square of charts.** For smooth charts
`φ : S ⟶ 𝔸¹_k`, `φ' : X' ⟶ 𝔸¹_{k'}` with `T`, `Y` the pullbacks of the punctured lines and
`f'^*(φ^* x) = φ'^* x`, and `n` invertible in `k` and `k'`, the base change map
`f'⁻¹ R¹ g_* μ_n ⟶ R¹ h_* e⁻¹ μ_n` is an isomorphism. -/
theorem isIso_higherBaseChangeMapAb_one_rootsOfUnity_of_charts {k' : Type u} [Field k']
    (φ : S ⟶ affineLine k) [Smooth φ] (φ₀ : T ⟶ (punctured k).toScheme)
    (sqS : IsPullback g φ₀ φ (punctured k).ι)
    (φ' : X' ⟶ affineLine k') [Smooth φ'] (φ₀' : Y ⟶ (punctured k').toScheme)
    (sqX : IsPullback h φ₀' φ' (punctured k').ι)
    (hcoord : f'.appTop (φ.appTop (coordinate k)) = φ'.appTop (coordinate k'))
    (n : ℕ) [NeZero n] (hn : IsUnit (n : k)) (hn' : IsUnit (n : k')) :
    IsIso ((higherBaseChangeMapAb f' g h e w (0 + 1)).app (kummerSequence.{u, 0} T n).X₁) := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have hU : ∀ {V : Scheme.{u}} {κ : Type u} [Field κ] (p : V ⟶ affineLine κ),
      IsUnit (n : κ) → IsUnit ((n : ℕ) : Γ(V, ⊤)) := fun p hκ =>
    isUnit_natCast_globalSections_of_over (p ≫ (affineLine _ ↘ Spec (.of _))) hκ
  have hNT := hU (g ≫ φ) hn
  have hNY := hU (h ≫ φ') hn'
  have hNS : IsUnit ((n : ℤ) : Γ(S, ⊤)) := by exact_mod_cast hU φ hn
  have hNX : IsUnit ((n : ℤ) : Γ(X', ⊤)) := by exact_mod_cast hU φ' hn'
  have ht := isUnit_puncturedFunction_of_isPullback_punctured φ g φ₀ sqS
  have ht'' := isUnit_puncturedFunction_of_isPullback_punctured φ' h φ₀' sqX
  have ht' : IsUnit (puncturedFunction h ⊤ (f'.appTop (φ.appTop (coordinate k)))) := by
    rwa [hcoord]
  have hσ : IsIsoStalksOver (Set.range g.base)ᶜ
      (torsionSectionSheafHom (localKummerClass g hn0 hNT ⊤ (φ.appTop (coordinate k)) ht)
        (nsmul_localKummerClass g hn0 hNT ⊤ (φ.appTop (coordinate k)) ht)) :=
    isIsoStalksOver_torsionSectionSheafHom_of_isPullback_affineLine φ g φ₀ sqS hn hNT ht
  have key : ∀ (s : Γ(X', ⊤)) (hs : φ'.appTop (coordinate k') = s)
      (hs' : IsUnit (puncturedFunction h ⊤ s)),
      IsIsoStalksOver (Set.range h.base)ᶜ
        (torsionSectionSheafHom (localKummerClass h hn0 hNY ⊤ s hs')
          (nsmul_localKummerClass h hn0 hNY ⊤ s hs')) := by
    rintro s rfl hs'
    exact isIsoStalksOver_torsionSectionSheafHom_of_isPullback_affineLine φ' h φ₀' sqX hn' hNY hs'
  have hσ' : IsIsoStalksOver (Set.range h.base)ᶜ
      (torsionSectionSheafHom
        (localKummerClass h hn0 hNY ⊤ (f'.appTop (φ.appTop (coordinate k))) ht')
        (nsmul_localKummerClass h hn0 hNY ⊤ (f'.appTop (φ.appTop (coordinate k))) ht')) :=
    key _ hcoord.symm ht'
  have hrange : f'.base '' (Set.range h.base)ᶜ ⊆ (Set.range g.base)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hg
    refine hx ?_
    rw [range_eq_basicOpen_of_isPullback_punctured φ g φ₀ sqS] at hg
    rwa [range_eq_basicOpen_of_isPullback_punctured φ' h φ₀' sqX, ← hcoord,
      ← Scheme.preimage_basicOpen_top]
  have hK := isIso_kummerBaseChangeMap_of_isIsoStalksOver f' g h e w hNT hNY hNS hNX
    (φ.appTop (coordinate k)) ht ht' hσ hσ' hrange
  have : IsIso (rootsOfUnityInverseImageComparison.{u, 0} e n) :=
    isIso_rootsOfUnityInverseImageComparison e n hNT
  have : IsIso (kummerSequencePullbackMap e n).τ₁ := by
    change IsIso (((smallEtalePullbackAbIsoEtaleAbelianInverseImage e).hom.app _) ≫
      rootsOfUnityInverseImageComparison.{u, 0} e n)
    infer_instance
  unfold kummerBaseChangeMap at hK
  exact IsIso.of_isIso_comp_right _
    (((smallEtalePushforwardAb h).rightDerived (0 + 1)).map (kummerSequencePullbackMap e n).τ₁)

/-- **The degree-one base change map on constant torsion coefficients over a square of charts.**
For smooth charts `φ : S ⟶ 𝔸¹_k`, `φ' : X' ⟶ 𝔸¹_{k'}` with `T`, `Y` the pullbacks of the punctured
lines and `f'^*(φ^* x) = φ'^* x`, `N` invertible in `k` and `k'`, and `T` over a field containing a
primitive `N`-th root of unity, the base change map `f'⁻¹ R¹ g_* A ⟶ R¹ h_* e⁻¹ A` is an
isomorphism for the constant sheaf of every finite abelian group `A` killed by `N`. -/
theorem isIso_higherBaseChangeMapAb_one_constantSheaf_of_charts {k' K : Type u} [Field k']
    [Field K] (φ : S ⟶ affineLine k) [Smooth φ] (φ₀ : T ⟶ (punctured k).toScheme)
    (sqS : IsPullback g φ₀ φ (punctured k).ι)
    (φ' : X' ⟶ affineLine k') [Smooth φ'] (φ₀' : Y ⟶ (punctured k').toScheme)
    (sqX : IsPullback h φ₀' φ' (punctured k').ι)
    (hcoord : f'.appTop (φ.appTop (coordinate k)) = φ'.appTop (coordinate k'))
    (N : ℕ) (hN : IsUnit (N : k)) (hN' : IsUnit (N : k'))
    (pK : T ⟶ Spec (.of K)) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (A : AddCommGrpCat.{u + 1}) [Finite A] (hA : ∀ a : A, N • a = 0) :
    IsIso ((higherBaseChangeMapAb f' g h e w (0 + 1)).app
      ((constantSheaf (smallEtaleTopology T) Ab.{u + 1}).obj A)) := by
  classical
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  let adj := constantSheafAdj (smallEtaleTopology T) Ab.{u + 1}
    (IsTerminal.ofUniqueHom toEtaleMkId fun _ a ↦ toEtaleMkId_unique a)
  have : (constantSheaf (smallEtaleTopology T) Ab.{u + 1}).Additive := adj.left_adjoint_additive
  have hG : (constantSheaf (smallEtaleTopology T) Ab.{u + 1} ⋙
      ((smallEtalePushforwardAb g).rightDerived (0 + 1) ⋙ smallEtalePullbackAb f')).Additive :=
    inferInstance
  have hH : (constantSheaf (smallEtaleTopology T) Ab.{u + 1} ⋙
      (smallEtalePullbackAb e ⋙ (smallEtalePushforwardAb h).rightDerived (0 + 1))).Additive :=
    inferInstance
  refine Stacks.TorsionDevissage.isIso_app_of_finite_of_dvd
    (Functor.whiskerLeft (constantSheaf (smallEtaleTopology T) Ab.{u + 1})
      (higherBaseChangeMapAb f' g h e w (0 + 1))) ?_ A hA
  intro n hn hnN
  have : NeZero n := ⟨hn.ne'⟩
  have hnk : IsUnit (n : k) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hnN) hN
  have hnk' : IsUnit (n : k') := isUnit_of_dvd_unit (Nat.cast_dvd_cast hnN) hN'
  have hμ := isIso_higherBaseChangeMapAb_one_rootsOfUnity_of_charts f' g h e w φ φ₀ sqS φ' φ₀' sqX
    hcoord n hnk hnk'
  have hζn : IsPrimitiveRoot (ζ ^ (N / n)) n := by
    have := hζ.pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hnN) hn).ne'
      (Nat.div_dvd_of_dvd hnN)
    rwa [Nat.div_div_self hnN hN0] at this
  have c : (kummerSequence.{u, 0} T n).X₁ ≅
      (constantSheaf (smallEtaleTopology T) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) :=
    (rootsOfUnityConstantIso pK hζn hn.ne').symm
  change IsIso ((higherBaseChangeMapAb f' g h e w (0 + 1)).app
    ((constantSheaf (smallEtaleTopology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))))
  exact isIso_app_of_iso_of_isIso (higherBaseChangeMapAb f' g h e w (0 + 1)) c hμ

end Stacks.EtaleCohomology.Purity

end
