module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingKernel
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.TwoTermResolution
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericFreeNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpen
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod

/-!
# The cohomology of a bounded complex of finite locally free modules near the generic point

Let `W` be an integral scheme and let `P` be a bounded complex of finite locally free
`𝒪_W`-modules. Then there is a nonempty open subscheme of `W` on which every cohomology module of
`P` is finite locally free of some constant rank. This is the existence of the open `U` in
[Stacks, Tag 0ESR], which the source asks the reader to prove for themselves; the argument here
needs no Noetherian hypothesis.

The proof is a descending induction on the degree, shrinking the open at each step. Over an open
on which the cycles `Zᵏ⁺¹` are finite locally free, the cohomology `Hᵏ⁺¹`, being the cokernel of
`Pᵏ ⟶ Zᵏ⁺¹`, is of finite presentation ([Stacks, Tag 0H96]); its stalk at the generic point is a
finite-dimensional vector space over the function field, so it is finite free near the generic
point ([Stacks, Tag 0B8J]). On that smaller open the two short exact sequences
`0 ⟶ Im(Pᵏ → Zᵏ⁺¹) ⟶ Zᵏ⁺¹ ⟶ Hᵏ⁺¹ ⟶ 0` and `0 ⟶ Zᵏ ⟶ Pᵏ ⟶ Im(Pᵏ → Zᵏ⁺¹) ⟶ 0` exhibit first the image
and then `Zᵏ` as kernels of surjections between finite locally free modules, hence finite locally
free (flat by Tag 08CJ, of finite presentation by the local splitting, finite locally free by
Tag 05P2).

## Main results

* `AlgebraicGeometry.isFiniteLocallyFree_kernel_of_epi_of_isFiniteLocallyFree`: the kernel of a
  surjection between finite locally free modules is finite locally free.
* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_restrict_genericPoint`: a module of finite
  presentation on an integral scheme is finite free of some rank near the generic point.
* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_homology_of_isFiniteLocallyFree`: the
  cohomology modules of a bounded complex of finite locally free modules on an integral scheme
  are finite locally free of constant ranks on a nonempty open subscheme.

## References

* [Stacks Project, Tag 0ESR](https://stacks.math.columbia.edu/tag/0ESR)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Finite local freeness: zero modules and kernels -/

/-- A zero module is finite locally free of rank `0`: so is the free module on an empty index
type, and the two are isomorphic. -/
theorem isFiniteLocallyFreeOfRank_zero_of_isZero {Y : Scheme.{u}} {M : Y.Modules}
    (hM : IsZero M) : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 0 := by
  have hfree : IsZero (SheafOfModules.free.{u} (R := Y.ringCatSheaf) (ULift.{u} (Fin 0))) := by
    rw [IsZero.iff_id_eq_zero]
    exact (SheafOfModules.free.{u} (R := Y.ringCatSheaf) (ULift.{u} (Fin 0))).freeHomEquiv.injective
      (funext fun j => (IsEmpty.false j).elim)
  exact Scheme.Modules.isFiniteLocallyFreeOfRankSheaf_of_iso (hfree.iso hM)
    (SheafOfModules.isFiniteLocallyFreeOfRank_free.{u, u, u} (R := Y.ringCatSheaf) 0)

/-- **The kernel of a surjection between finite locally free modules is finite locally free.**
The kernel is of finite presentation by the local splitting of the surjection
(`AlgebraicGeometry.isFinitePresentation_kernel_of_isFiniteLocallyFree`), the target has Tor
amplitude in `[0, 0]`, and a finitely presented kernel of a surjection from a finite locally free
module onto a module of Tor amplitude in `[-1, 0]` is finite locally free
(`AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude`). -/
theorem isFiniteLocallyFree_kernel_of_epi_of_isFiniteLocallyFree {Y : Scheme.{u}}
    {M N : Y.Modules} (g : M ⟶ N) [Epi g]
    (hM : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hN : SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (kernel g) := by
  have := hM
  have := hN
  have : M.IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree M hM
  have : M.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M
  let S : ShortComplex Y.Modules := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have h₃ : Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₃) (-1) 0 :=
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
      (AlgebraicGeometry.hasTorAmplitude_singleFunctor_of_isFiniteLocallyFree Y S.X₃
        hN)
      (by omega) le_rfl
  exact AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude S
    { exact := ShortComplex.exact_kernel g } hM h₃
    (AlgebraicGeometry.isFinitePresentation_kernel_of_isFiniteLocallyFree g)

/-- In a short exact sequence `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒞 ⟶ 0` of modules on a scheme with `ℬ` and `𝒞`
finite locally free, `𝒜` is finite locally free: it is the kernel of `ℬ ⟶ 𝒞`. -/
theorem isFiniteLocallyFree_X₁_of_shortExact {Y : Scheme.{u}} {S : ShortComplex Y.Modules}
    (hS : S.ShortExact) (h₂ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₂)
    (h₃ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁ := by
  have := hS.epi_g
  exact SheafOfModules.IsFiniteLocallyFree.of_iso
    (h := isFiniteLocallyFree_kernel_of_epi_of_isFiniteLocallyFree S.g h₂ h₃)
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hS.fIsKernel)

/-- A module which is finite locally free of rank `r` in the pointwise sense is finite locally
free. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank {Y : Scheme.{u}} {M : Y.Modules}
    {r : ℕ} (h : Scheme.Modules.IsFiniteLocallyFreeOfRank M r) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  have := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff M r).1 h
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r

/-- The restriction of a finite locally free module along an open immersion is finite locally
free. -/
private theorem isFiniteLocallyFree_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M : Y.Modules} (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((Scheme.Modules.restrictFunctor f).obj M) :=
  (Scheme.Modules.isFiniteLocallyFree_iff _).1
    (((Scheme.Modules.isFiniteLocallyFree_iff _).2 h).restrict f)

/-- Restricting along a composite of open immersions is restricting twice, for finite local
freeness. -/
theorem isFiniteLocallyFree_restrictFunctor_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] {M : Z.Modules}
    (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((Scheme.Modules.restrictFunctor g).obj M)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((Scheme.Modules.restrictFunctor (f ≫ g)).obj M) :=
  SheafOfModules.IsFiniteLocallyFree.of_iso (h := isFiniteLocallyFree_restrictFunctor f h)
    ((Scheme.Modules.restrictFunctorComp f g).app M).symm

/-- Restricting along a composite of open immersions is restricting twice, for finite local
freeness of a fixed rank. -/
theorem isFiniteLocallyFreeOfRank_restrictFunctor_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] {M : Z.Modules} {r : ℕ}
    (h : Scheme.Modules.IsFiniteLocallyFreeOfRank ((Scheme.Modules.restrictFunctor g).obj M) r) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank ((Scheme.Modules.restrictFunctor (f ≫ g)).obj M) r :=
  (h.restrict f).of_iso ((Scheme.Modules.restrictFunctorComp f g).app M).symm

/-! ### Finite presentation near the generic point -/

open Stacks.AlgebraicGeometry.IrreducibleDevissage in
/-- **A module of finite presentation on an integral scheme is finite free near the generic
point**, of some rank `q`. This is [Stacks, Tag 0B8J] at the generic point, whose local ring is
the function field. -/
theorem exists_isFiniteLocallyFreeOfRank_restrict_genericPoint {Z : Scheme.{u}} [IsIntegral Z]
    (G : Z.Modules) [G.IsFinitePresentation] :
    ∃ (q : ℕ) (V : Z.Opens), genericPoint Z ∈ V ∧
      Scheme.Modules.IsFiniteLocallyFreeOfRank ((Scheme.Modules.restrictFunctor V.ι).obj G) q := by
  obtain ⟨q, V, hV, ⟨e⟩⟩ :=
    exists_isIso_restrictFunctor_free_near_genericPoint_of_isFinitePresentation
      G (genericPoint Z) (genericPoint_spec Z)
  have hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank
      (SheafOfModules.free.{u} (R := Z.ringCatSheaf) (ULift.{u} (Fin q))) q :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ q).2
      (SheafOfModules.isFiniteLocallyFreeOfRank_free.{u, u, u} (R := Z.ringCatSheaf) q)
  exact ⟨q, V, hV, (hfree.restrict V.ι).of_iso e⟩

/-! ### The two short exact sequences of a complex in a degree -/

variable {W : Scheme.{u}} (P : CochainComplex W.Modules ℤ)

/-- The short complex `Im(Pᵏ → Zᵏ⁺¹) ⟶ Zᵏ⁺¹ ⟶ Hᵏ⁺¹`. -/
abbrev scImageCyclesHomology (k : ℤ) : ShortComplex W.Modules :=
  ShortComplex.mk (image.ι (P.toCycles k (k + 1))) (P.homologyπ (k + 1))
    ((cancel_epi (factorThruImage (P.toCycles k (k + 1)))).1 (by simp))

/-- `0 ⟶ Im(Pᵏ → Zᵏ⁺¹) ⟶ Zᵏ⁺¹ ⟶ Hᵏ⁺¹ ⟶ 0` is short exact, `Hᵏ⁺¹` being the cokernel of
`Pᵏ ⟶ Zᵏ⁺¹`. -/
theorem shortExact_scImageCyclesHomology (k : ℤ) : (scImageCyclesHomology P k).ShortExact := by
  let t := P.toCycles k (k + 1)
  let S₀ := ShortComplex.mk t (P.homologyπ (k + 1)) (P.toCycles_comp_homologyπ k (k + 1))
  let φ₁ : S₀ ⟶ scImageCyclesHomology P k :=
    { τ₁ := factorThruImage t
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [t, S₀] }
  exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₁).1
            (ShortComplex.exact_of_g_is_cokernel _ (P.homologyIsCokernel k (k + 1) (by simp))) }

/-- The short complex `Zᵏ ⟶ Pᵏ ⟶ Im(Pᵏ → Zᵏ⁺¹)`. -/
abbrev scCyclesXImage (k : ℤ) : ShortComplex W.Modules :=
  ShortComplex.mk (P.iCycles k) (factorThruImage (P.toCycles k (k + 1)))
    ((cancel_mono (image.ι (P.toCycles k (k + 1)) ≫ P.iCycles (k + 1))).1 (by simp))

/-- `0 ⟶ Zᵏ ⟶ Pᵏ ⟶ Im(Pᵏ → Zᵏ⁺¹) ⟶ 0` is short exact, `Zᵏ` being the kernel of `dᵏ`. -/
theorem shortExact_scCyclesXImage (k : ℤ) : (scCyclesXImage P k).ShortExact := by
  let S₃ := ShortComplex.mk (P.iCycles k) (P.d k (k + 1)) (P.iCycles_d k (k + 1))
  let φ₂ : scCyclesXImage P k ⟶ S₃ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := image.ι (P.toCycles k (k + 1)) ≫ P.iCycles (k + 1)
      comm₂₃ := by simp [scCyclesXImage, S₃] }
  exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₂).2
            (ShortComplex.exact_of_f_is_kernel _ (P.cyclesIsKernel k (k + 1) (by simp))) }

/-! ### The descending induction -/

/-- **One step of the descending induction.** Let `ι : V ⟶ W` be an open immersion from an
integral scheme along which `Zᵏ⁺¹` and `Pᵏ` restrict to finite locally free modules. Then there is
a nonempty open `V' ⊆ V` along which `Hᵏ⁺¹` restricts to a finite locally free module of some rank
and `Zᵏ` to a finite locally free module. -/
theorem exists_isFiniteLocallyFreeOfRank_homology_step {V : Scheme.{u}} [IsIntegral V]
    (ι : V ⟶ W) [IsOpenImmersion ι] (k : ℤ)
    (hZ : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.restrictFunctor ι).obj (P.cycles (k + 1))))
    (hX : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.restrictFunctor ι).obj (P.X k))) :
    ∃ (V' : V.Opens) (q : ℕ), genericPoint V ∈ V' ∧
      Scheme.Modules.IsFiniteLocallyFreeOfRank
        ((Scheme.Modules.restrictFunctor (V'.ι ≫ ι)).obj (P.homology (k + 1))) q ∧
      SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Scheme.Modules.restrictFunctor (V'.ι ≫ ι)).obj (P.cycles k)) := by
  let F := Scheme.Modules.restrictFunctor ι
  let t := P.toCycles k (k + 1)
  -- The restricted cohomology is the cokernel of the restricted map `Pᵏ ⟶ Zᵏ⁺¹`.
  let e : F.obj (P.homology (k + 1)) ≅ cokernel (F.map t) :=
    F.mapIso ((P.homologyIsCokernel k (k + 1) (by simp)).coconePointUniqueUpToIso
      (colimit.isColimit _)) ≪≫ PreservesCokernel.iso F t
  have : (F.obj (P.cycles (k + 1))).IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree _ hZ
  have : (F.obj (P.X k)).IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree _ hX
  have : (F.obj (P.X k)).IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
      _ inferInstance).2
  have : (cokernel (F.map t)).IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_cokernel (F.map t)
  have : (F.obj (P.homology (k + 1))).IsFinitePresentation :=
    (_root_.SheafOfModules.isFinitePresentation V.ringCatSheaf).prop_of_iso e.symm
      inferInstance
  obtain ⟨q, V', hV', hq⟩ :=
    exists_isFiniteLocallyFreeOfRank_restrict_genericPoint (F.obj (P.homology (k + 1)))
  have hH : Scheme.Modules.IsFiniteLocallyFreeOfRank
      ((Scheme.Modules.restrictFunctor (V'.ι ≫ ι)).obj (P.homology (k + 1))) q :=
    hq.of_iso ((Scheme.Modules.restrictFunctorComp V'.ι ι).app _).symm
  refine ⟨V', q, hV', hH, ?_⟩
  let G := Scheme.Modules.restrictFunctor (V'.ι ≫ ι)
  exact isFiniteLocallyFree_X₁_of_shortExact ((shortExact_scCyclesXImage P k).map_of_exact G)
    (isFiniteLocallyFree_restrictFunctor_comp V'.ι ι hX)
    (isFiniteLocallyFree_X₁_of_shortExact ((shortExact_scImageCyclesHomology P k).map_of_exact G)
      (isFiniteLocallyFree_restrictFunctor_comp V'.ι ι hZ)
      (isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank hH))

/-- **The cohomology of a bounded complex of finite locally free modules on an integral scheme is
finite locally free of constant ranks on a nonempty open subscheme.** Let `P` be a complex of
finite locally free modules on an integral scheme `W` with `Pⁿ = 0` for `n < a` and for `b < n`.
Then there is a nonempty scheme `V` with an open immersion `ι : V ⟶ W` along which every `Hⁿ(P)`
restricts to a finite locally free module of some rank `qₙ`.

Descending induction on the degree with
`AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_homology_step`, starting above `b`, where the
cycles vanish; below `a` the cohomology vanishes and has rank `0` on any open. -/
theorem exists_isFiniteLocallyFreeOfRank_homology_of_isFiniteLocallyFree [IsIntegral W]
    (a b : ℤ) (hP : ∀ n : ℤ, (n < a ∨ b < n) → IsZero (P.X n))
    (hterm : ∀ n : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P.X n)) :
    ∃ (V : Scheme.{u}) (ι : V ⟶ W) (_ : IsOpenImmersion ι), Nonempty V ∧
      ∀ n : ℤ, ∃ q : ℕ, Scheme.Modules.IsFiniteLocallyFreeOfRank
        ((Scheme.Modules.restrictFunctor ι).obj (P.homology n)) q := by
  have hHzero : ∀ n, IsZero (P.X n) → IsZero (P.homology n) := fun n hn => by
    simpa [HomologicalComplex.homology] using
      ShortComplex.isZero_homology_of_isZero_X₂ (P.sc n) hn
  have hrank0 : ∀ {V : Scheme.{u}} (ι : V ⟶ W) [IsOpenImmersion ι] (M : W.Modules), IsZero M →
      Scheme.Modules.IsFiniteLocallyFreeOfRank ((Scheme.Modules.restrictFunctor ι).obj M) 0 :=
    fun ι _ M hM => (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ 0).2
      (isFiniteLocallyFreeOfRank_zero_of_isZero
        (Functor.map_isZero (Scheme.Modules.restrictFunctor ι) hM))
  have key : ∀ d : ℕ, ∃ (V : Scheme.{u}) (ι : V ⟶ W) (_ : IsOpenImmersion ι), Nonempty V ∧
      SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Scheme.Modules.restrictFunctor ι).obj (P.cycles (b + 1 - d))) ∧
      ∀ n : ℤ, b + 1 - d < n → ∃ q : ℕ, Scheme.Modules.IsFiniteLocallyFreeOfRank
        ((Scheme.Modules.restrictFunctor ι).obj (P.homology n)) q := by
    intro d
    induction d with
    | zero =>
      refine ⟨W, 𝟙 W, inferInstance, inferInstance, ?_, fun n hn =>
        ⟨0, hrank0 _ _ (hHzero n (hP n (Or.inr (by omega))))⟩⟩
      exact isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
        (hrank0 _ _ (IsZero.of_mono (P.iCycles _) (hP _ (Or.inr (by omega)))))
    | succ d ih =>
      obtain ⟨V, ι, _, hV, hZ, hH⟩ := ih
      have : IsIntegral V := isIntegral_of_isOpenImmersion ι
      obtain ⟨V', q, hV', hHk, hZk⟩ :=
        exists_isFiniteLocallyFreeOfRank_homology_step P ι (b + 1 - ((d + 1 : ℕ) : ℤ))
        (by rwa [show b + 1 - ((d + 1 : ℕ) : ℤ) + 1 = b + 1 - (d : ℤ) by omega])
        (isFiniteLocallyFree_restrictFunctor ι (hterm _))
      refine ⟨V', V'.ι ≫ ι, inferInstance, ⟨⟨genericPoint V, hV'⟩⟩, hZk, fun n hn => ?_⟩
      obtain h | h : b + 1 - ((d + 1 : ℕ) : ℤ) + 1 = n ∨ b + 1 - ((d + 1 : ℕ) : ℤ) + 1 < n := by
        omega
      · exact ⟨q, h ▸ hHk⟩
      · obtain ⟨q', hq'⟩ := hH n (by omega)
        exact ⟨q', isFiniteLocallyFreeOfRank_restrictFunctor_comp V'.ι ι hq'⟩
  obtain ⟨V, ι, _, hV, -, hH⟩ := key (b + 2 - a).toNat
  refine ⟨V, ι, inferInstance, hV, fun n => ?_⟩
  by_cases hn : b + 1 - ((b + 2 - a).toNat : ℤ) < n
  · exact hH n hn
  · exact ⟨0, hrank0 _ _ (hHzero n (hP n (Or.inl (by omega))))⟩

end AlgebraicGeometry

end
