module

public import StacksFrontier.AlgebraicGeometry.AffineExtend.Pair
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.Affine
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.Localization.FiniteOfAwayAndAtPrime

/-!
# Coherence from finite type off a point and a finite stalk at it

Let `X` be a locally Noetherian scheme, `w ∈ X` a point, `U ⊆ X` an open containing every
point other than `w`, and `M` a quasi-coherent `𝒪_X`-module such that `M|_U` is of finite type
and the stalk `M_w` is a finite `𝒪_{X,w}`-module. Then `M` is of finite type, hence coherent.

On an affine open `V = Spec R ∋ w` with `w ↔ 𝔭`, the elements `r ∈ R` with `D(r) ⊆ U` form an
ideal, finitely generated since `R` is Noetherian; every maximal ideal other than `𝔭` misses one
of its generators. The sections `Γ(V, M)` localize to the finite modules `Γ(D(r), M)` and to the
finite module `M_w`, so `Γ(V, M)` is finite by
`Module.Finite.of_isLocalizedModule_away_of_isLocalizedModule_atPrime`.

## Main results

* `Stacks.AlgebraicGeometry.FiniteStalkAtPuncture.module_finite_sections`: `Γ(V, M)` is finite.
* `Stacks.AlgebraicGeometry.FiniteStalkAtPuncture.isFiniteType`: `M` is of finite type.
* `Stacks.AlgebraicGeometry.FiniteStalkAtPuncture.isCoherent`: `M` is coherent.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.ModuleStalkSpecialization Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.FiniteTypeSubmodule

namespace Stacks.AlgebraicGeometry.FiniteStalkAtPuncture

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
  (U : X.Opens) (hU : (M.restrict U.ι).IsFiniteType) (w : X) (hw : ∀ x, x ∉ U → x = w)
  (hfin : letI := stalkModule M w; Module.Finite (X.presheaf.stalk w) (M.presheaf.stalk w))

omit [IsLocallyNoetherian X] in
include hw in
/-- On an affine open `V` containing `w`, every maximal ideal of `Γ(X, V)` other than the one at
`w` omits some section whose basic open lies in `U`. -/
private theorem exists_basicOpen_le_and_notMem {V : X.Opens} (hV : IsAffineOpen V) (hwV : w ∈ V)
    {q : Ideal Γ(X, V)} (hq : q.IsMaximal) (hqp : q ≠ (hV.primeIdealOf ⟨w, hwV⟩).asIdeal) :
    ∃ r : Γ(X, V), X.basicOpen r ≤ U ∧ r ∉ q := by
  let y := hV.fromSpec ⟨q, hq.isPrime⟩
  by_cases hyU : y ∈ U
  · have hyV : y ∈ V := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]
      exact ⟨_, rfl⟩
    obtain ⟨r, hrU, hyr⟩ := hV.exists_basicOpen_le (V := U) ⟨y, hyU⟩ hyV
    have : (⟨q, hq.isPrime⟩ : PrimeSpectrum Γ(X, V)) ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen r := hyr
    rw [hV.fromSpec_preimage_basicOpen] at this
    exact ⟨r, hrU, this⟩
  · have : (⟨q, hq.isPrime⟩ : PrimeSpectrum Γ(X, V)) = hV.primeIdealOf ⟨w, hwV⟩ :=
      hV.fromSpec.isOpenEmbedding.injective
        ((hw y hyU).trans (hV.fromSpec_primeIdealOf ⟨w, hwV⟩).symm)
    exact absurd (congrArg PrimeSpectrum.asIdeal this) hqp

include hU hw hfin in
/-- On an affine open `V` containing `w`, the sections of `M` form a finite module. -/
theorem module_finite_sections {V : X.Opens} (hV : IsAffineOpen V) (hwV : w ∈ V) :
    Module.Finite Γ(X, V) Γ(M, V) := by
  classical
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let J : Ideal Γ(X, V) :=
    { carrier := {r | X.basicOpen r ≤ U}
      add_mem' := fun {a b} ha hb => (X.basicOpen_add_le a b).trans (sup_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Scheme.basicOpen_mul]
        exact inf_le_right.trans ha }
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian J : J.FG)
  have htJ : ∀ r ∈ t, X.basicOpen r ≤ U := fun r hr => (ht ▸ Ideal.subset_span hr : r ∈ J)
  set p := (hV.primeIdealOf ⟨w, hwV⟩).asIdeal
  have hmax : ∀ q : Ideal Γ(X, V), q.IsMaximal → q ≠ p → ∃ r ∈ t, r ∉ q := by
    intro q hq hqp
    obtain ⟨r, hrU, hrq⟩ := exists_basicOpen_le_and_notMem U w hw hV hwV hq hqp
    by_contra! hall
    exact hrq ((ht ▸ Ideal.span_le.2 fun r hr => hall r hr : J ≤ q) hrU)
  let _ : ∀ g : t, Algebra Γ(X, V) Γ(X, X.basicOpen (g : Γ(X, V))) :=
    fun g => algebraOfLE X (X.basicOpen_le (g : Γ(X, V)))
  let _ : ∀ g : t, IsLocalization.Away (g : Γ(X, V)) Γ(X, X.basicOpen (g : Γ(X, V))) :=
    fun _ => hV.isLocalization_basicOpen _
  let _ : ∀ g : t, Module Γ(X, V) Γ(M, X.basicOpen (g : Γ(X, V))) :=
    fun g => moduleOfLE M (X.basicOpen_le (g : Γ(X, V)))
  let _ : ∀ g : t, IsScalarTower Γ(X, V) Γ(X, X.basicOpen (g : Γ(X, V)))
      Γ(M, X.basicOpen (g : Γ(X, V))) :=
    fun g => isScalarTowerOfLE M (X.basicOpen_le (g : Γ(X, V)))
  let _ : ∀ g : t, IsLocalizedModule.Away (g : Γ(X, V))
      (restrictₗ M (X.basicOpen_le (g : Γ(X, V)))) :=
    fun _ => isLocalizedModule_restrictₗ M hV _ rfl _
  let _ := (X.presheaf.germ V w hwV).hom.toAlgebra
  let _ := stalkModule M w
  let _ := sectionsStalkModule M hwV
  have := isScalarTower_sectionsStalk M hwV
  have : IsLocalization.AtPrime (X.presheaf.stalk w) p := hV.isLocalization_stalk ⟨w, hwV⟩
  have := isLocalizedModule_germₗ M hV hwV
  exact Module.Finite.of_isLocalizedModule_away_of_isLocalizedModule_atPrime p t hmax
    (fun g => restrictₗ M (X.basicOpen_le (g : Γ(X, V))))
    (fun g => module_finite_sections_of_isFiniteType_restrict M (hV.basicOpen _)
      (Tag01PFAffineExtend.isFiniteType_restrict_of_le M (htJ g.1 g.2) hU))
    (X.presheaf.stalk w) (germₗ M hwV) hfin

include hU hw hfin in
/-- **A quasi-coherent module of finite type off a point, with a finite stalk at the point, is
of finite type.** -/
theorem isFiniteType : M.IsFiniteType := by
  obtain ⟨V, hV, hwV, -⟩ :=
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show w ∈ (⊤ : X.Opens) from trivial)
  let ι := Option {Z : X.affineOpens // (Z : X.Opens) ≤ U}
  let W : ι → X.Opens := fun i => i.elim V fun Z => Z.1.1
  have hW : ∀ i, IsAffineOpen (W i) := fun i => by
    cases i with
    | none => exact hV
    | some Z => exact Z.1.2
  refine CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn M W (IsOpenCover.mk ?_) hW
    fun i => FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections M ⟨W i, hW i⟩ ?_
  · refine top_le_iff.1 fun x _ => ?_
    by_cases hxU : x ∈ U
    · obtain ⟨Z, hZ, hxZ, hZU⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hxU
      exact Opens.mem_iSup.2 ⟨some ⟨⟨Z, hZ⟩, hZU⟩, hxZ⟩
    · exact Opens.mem_iSup.2 ⟨none, hw x hxU ▸ hwV⟩
  · cases i with
    | none => exact module_finite_sections M U hU w hw hfin hV hwV
    | some Z =>
      exact module_finite_sections_of_isFiniteType_restrict M Z.1.2
        (Tag01PFAffineExtend.isFiniteType_restrict_of_le M Z.2 hU)

include hU hw hfin in
/-- **A quasi-coherent module of finite type off a point, with a finite stalk at the point, is
coherent** (the scheme being locally Noetherian). -/
theorem isCoherent : M.IsCoherent :=
  have := isFiniteType M U hU w hw hfin
  CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType M

end Stacks.AlgebraicGeometry.FiniteStalkAtPuncture
