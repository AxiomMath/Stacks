module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.DepthSubsingleton
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.CohenMacaulay.Bridges
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay

/-!
# Cohen–Macaulay coherent modules on a regular scheme

On a regular scheme a coherent module is Cohen–Macaulay with support the whole space exactly
when it is finite locally free of positive rank at every point.  This is
[Stacks, Tag 0B3K].

Both directions are stalkwise, and over a regular local ring `R` they are the two halves of the
relation between maximal Cohen–Macaulayness and freeness.  If every Serre condition holds at a
point and the support of the stalk is the whole of `Spec R`, then the support dimension of the
stalk is `dim R`, so its depth is `dim R` as well and the stalk is maximal Cohen–Macaulay, hence
free ([Stacks, Tag 00NT]).  Conversely a finite free module has the depth of the ring, which for
a regular local ring is `dim R` ([Stacks, Tag 00NQ]), and that dominates the support dimension,
so every Serre condition holds.

## Main results

* `AlgebraicGeometry.sheafIsCohenMacaulay_and_supp_eq_univ_iff_isFiniteLocallyFree` is
  [Stacks, Tag 0B3K].
* `AlgebraicGeometry.support_stalk_eq_univ_of_supp_eq_univ`: a module with full support has
  stalks whose support is the whole spectrum of the local ring.

## Implementation notes

The support of the sheaf is `SheafOfModules.supp`, the set of points with nonzero stalk; full
support is therefore the statement that every stalk is nonzero.  Passing from that to
`Module.support R_x F_x = Set.univ` is the one genuinely geometric step: a prime `q` of `𝒪_{X,x}`
is the image of a point `y ⤳ x` under `Spec 𝒪_{X,x} ⟶ X`, the localization of `F_x` at `q` is
the stalk `F_y`, and `F_y ≠ 0`.

Positivity of the fibre rank is read off the stalk: for a module of finite type with free stalk
the fibre rank is the rank of the stalk
(`AlgebraicGeometry.Scheme.Modules.fiberRank_eq_finrank_stalk`), so it is positive exactly when
the stalk is nonzero.

Serre's condition is `AlgebraicGeometry.SheafHasPropertySk`, which is stated in the stalk module
structure of [Stacks, Tag 01CB]; the pointwise work happens in the structure instance search
finds, and the two transports are
`Stacks.AlgebraicGeometry.ReflexiveModules.sheafHasPropertySk_of_forall` and
`min_supportDim_le_depth_of_sheafHasPropertySk`.

## References

* [Stacks Project, Tag 0B3K](https://stacks.math.columbia.edu/tag/0B3K)
* [Stacks Project, Tag 0343](https://stacks.math.columbia.edu/tag/0343)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
* [Stacks Project, Tag 00NT](https://stacks.math.columbia.edu/tag/00NT)
* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry

/-! ### Depth of a finite free module over a Noetherian local ring -/

/-- A finite free module of rank `n` has depth at least that of the ring. -/
@[ega "0 16.4.5" "prof(A) ≤ prof(A^k)"]
public lemma depth_le_depth_piFin {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (n : ℕ) : Module.depth R I R ≤ Module.depth R I (Fin n → R) := by
  induction n with
  | zero =>
      have : Subsingleton (Fin 0 → R) := ⟨fun f g => funext fun i => i.elim0⟩
      rw [Module.depth_eq_top_of_subsingleton I (M := (Fin 0 → R))]
      exact le_top
  | succ n ih =>
      calc Module.depth R I R
          ≤ min (Module.depth R I R) (Module.depth R I (Fin n → R)) := le_min le_rfl ih
        _ ≤ Module.depth R I (R × (Fin n → R)) :=
            (Module.min_depth_le_depth_of_exact I
              (f := LinearMap.inl R R (Fin n → R)) (g := LinearMap.snd R R (Fin n → R))
              Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective).1
        _ = Module.depth R I (Fin (n + 1) → R) :=
            Module.depth_eq_depth_of_linearEquiv I (Fin.consLinearEquiv R fun _ => R)

/-- The depth of a finite free module is at least the depth of the ring. -/
@[sga "2 X 2.1" "inequality depth O_{U"]
public lemma depth_le_depth_of_free {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] : Module.depth R I R ≤ Module.depth R I M := by
  classical
  have : Fintype (Module.Free.ChooseBasisIndex R M) := Fintype.ofFinite _
  have e : M ≃ₗ[R] (Fin (Fintype.card (Module.Free.ChooseBasisIndex R M)) → R) :=
    (Module.Free.chooseBasis R M).equivFun.trans
      (LinearEquiv.piCongrLeft' R _ (Fintype.equivFin _))
  rw [Module.depth_eq_depth_of_linearEquiv I e]
  exact depth_le_depth_piFin I _

/-- **Serre's conditions for a finite free module over a regular local ring.** Its depth is the
depth of the ring, which is `dim R`, and that dominates the support dimension. -/
@[sga "2 IV 5.3" "dim A ≤ depth A"]
private lemma min_le_depth_of_free {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M] (k : ℕ) :
    min (k : WithBot ℕ∞) (Module.supportDim R M) ≤
      (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) :=
  have hR : (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) = ringKrullDim R :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      R).2
  (min_le_right _ _).trans ((Module.supportDim_le_ringKrullDim R M).trans
    (hR.ge.trans (WithBot.coe_le_coe.mpr (depth_le_depth_of_free _ M))))

/-! ### Freeness from the Serre conditions -/

/-- **A finite module over a regular local ring with full support satisfying every Serre
condition is free.** Full support makes its support dimension `dim R`, so the Serre condition at
`k = dim R` forces the depth to be `dim R` too; the module is then maximal Cohen–Macaulay, hence
free by [Stacks, Tag 00NT]. -/
@[ega "0 17.3.5" "(i), sufficiency"]
private lemma free_of_forall_min_le_depth {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hsupp : Module.support R M = Set.univ)
    (hS : ∀ k : ℕ, min (k : WithBot ℕ∞) (Module.supportDim R M) ≤
      (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞)) :
    Module.Free R M := by
  have hproper : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := fun h =>
    top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top
      (le_of_eq h.symm)
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).symm))
  have hdim : Module.supportDim R M = ringKrullDim R :=
    le_antisymm (Module.supportDim_le_ringKrullDim R M)
      (Order.krullDim_le_of_strictMono
        (fun p => (⟨p, hsupp ▸ Set.mem_univ p⟩ : Module.support R M)) fun _ _ h => h)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ringKrullDim R = (N : WithBot ℕ∞) := by
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
    have hdtop : d ≠ ⊤ := fun h => ringKrullDim_ne_top (R := R) (by rw [← hd, h]; rfl)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hdtop
    exact ⟨n, by rw [← hd, ← hn]; norm_cast⟩
  have hge : ringKrullDim R ≤ (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) := by
    have h := hS N
    rw [hdim, hN, min_self] at h
    exact hN.trans_le h
  have hle : (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) ≤ ringKrullDim R :=
    (Module.depth_le_supportDim R _ M hproper).trans hdim.le
  have hsup : Module.depthSup R (IsLocalRing.maximalIdeal R) M =
      Module.depth R (IsLocalRing.maximalIdeal R) M := by
    rw [Module.depth, ite_eq_right hproper, Module.depthSup_eq_iSup]
  exact regular_mcm_free R M
    (isMaxCM_iff_depth_eq_ringKrullDim.2 (by rw [hsup]; exact le_antisymm hle hge))

/-! ### Support of the stalks of a module with full support -/

variable {X : Scheme.{u}}

/-- **The stalks of a module with full support have full support.** If every stalk of `F` is
nonzero then, at each point `x`, every prime of `𝒪_{X,x}` lies in the support of `F_x`: the
prime is the image of a point `y ⤳ x` under `Spec 𝒪_{X,x} ⟶ X` ([Stacks, Tag 01J7]) and the
localization of `F_x` at it is the stalk `F_y`, which is nonzero. -/
public theorem support_stalk_eq_univ_of_supp_eq_univ (F : X.Modules) [F.IsQuasicoherent]
    (hsupp : _root_.SheafOfModules.supp F = Set.univ) (x : X) :
    Module.support (X.presheaf.stalk x) (F.presheaf.stalk x) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro q
  obtain ⟨y, hyx, rfl⟩ : ∃ (y : X) (hyx : y ⤳ x),
      PrimeSpectrum.comap (X.presheaf.stalkSpecializes hyx).hom
        (IsLocalRing.closedPoint (X.presheaf.stalk y)) = q := by
    have hyx : X.fromSpecStalk x q ⤳ x := by
      have hmem : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at hmem
    refine ⟨X.fromSpecStalk x q, hyx, (X.fromSpecStalk x).isEmbedding.injective ?_⟩
    show (Spec.map (X.presheaf.stalkSpecializes hyx) ≫ X.fromSpecStalk x)
      (IsLocalRing.closedPoint (X.presheaf.stalk (X.fromSpecStalk x q))) = _
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.fromSpecStalk_closedPoint
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes hyx).hom.toAlgebra
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  let := Stacks.ModuleStalkSpecialization.stalkModule F y
  let := Stacks.ModuleStalkSpecialization.stalkSpecializesModule F hyx
  have hloc : IsLocalizedModule
      (PrimeSpectrum.comap (X.presheaf.stalkSpecializes hyx).hom
        (IsLocalRing.closedPoint (X.presheaf.stalk y))).asIdeal.primeCompl
      (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F hyx) :=
    Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes F hyx
  exact Module.mem_support_iff.mpr ((IsLocalizedModule.iso _
    (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F hyx)).toEquiv.nontrivial_congr.mpr
      ((_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk F y).mp (hsupp ▸ Set.mem_univ y)))

/-! ### Tag 0B3K -/

private lemma fiberRank_pos_iff_nontrivial_stalk (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [F.IsFiniteType] (x : X)
    (hfree :
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    0 < Scheme.Modules.fiberRank F x ↔ Nontrivial (F.presheaf.stalk x) := by
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    Scheme.Modules.finite_stalk_of_isCoherent F x
  have : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) := hfree
  rw [Scheme.Modules.fiberRank_eq_finrank_stalk F x hfree]
  exact Module.finrank_pos_iff_of_free ..

/-- **Stacks Project, Tag 0B3K.** Let `X` be a regular scheme and `F` a coherent
`𝒪_X`-module. Then `F` is Cohen–Macaulay with support all of `X` if and only if it is finite
locally free of positive rank at every point. -/
@[stacks 0B3K, ega "0 17.3.5" "(i)"]
public theorem sheafIsCohenMacaulay_and_supp_eq_univ_iff_isFiniteLocallyFree
    (hX : IsRegular X) (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] :
    (SheafIsCohenMacaulay X F ∧ _root_.SheafOfModules.supp F = Set.univ) ↔
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F ∧
        ∀ x : X, 0 < Scheme.Modules.fiberRank F x := by
  obtain ⟨hNoeth, hstalk⟩ := ((isRegular_tfae X).out 1 2).mp hX
  have : IsLocallyNoetherian X := hNoeth
  have hfp : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
      F hfp
  have : F.IsQuasicoherent := hqc
  have : F.IsFiniteType := hft
  have hfin := Scheme.Modules.finite_stalk_of_isCoherent F
  constructor
  · rintro ⟨hCM, hsupp⟩
    have hnt : ∀ x : X, Nontrivial (F.presheaf.stalk x) := fun x =>
      (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mp (hsupp ▸ Set.mem_univ x)
    have hfree : ∀ x : X,
        let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) F.val x
        Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) := by
      intro x
      have : IsRegularLocalRing (X.presheaf.stalk x) := hstalk x
      have := hfin x
      have := hnt x
      exact free_of_forall_min_le_depth (F.presheaf.stalk x)
        (support_stalk_eq_univ_of_supp_eq_univ F hsupp x)
        fun k => min_supportDim_le_depth_of_sheafHasPropertySk F k (hCM k) x
    exact ⟨((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae F).out 2 4).mp
      (And.intro hfp hfree), fun x =>
        (fiberRank_pos_iff_nontrivial_stalk F x (hfree x)).mpr (hnt x)⟩
  · rintro ⟨hflf, hrank⟩
    obtain ⟨-, hfree⟩ :=
      ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae F).out 4 2).mp hflf
    have hnt : ∀ x : X, Nontrivial (F.presheaf.stalk x) := fun x =>
      (fiberRank_pos_iff_nontrivial_stalk F x (hfree x)).mp (hrank x)
    refine ⟨fun k => sheafHasPropertySk_of_forall F k fun x => ?_, ?_⟩
    · have : IsRegularLocalRing (X.presheaf.stalk x) := hstalk x
      have := hfin x
      have : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) := hfree x
      exact min_le_depth_of_free (F.presheaf.stalk x) k
    · exact Set.eq_univ_iff_forall.mpr fun x =>
        (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mpr (hnt x)

end AlgebraicGeometry

end
