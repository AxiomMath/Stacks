module

public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.RingTheory.Coherent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence over Noetherian and coherent rings

Let `R` be a ring and let `K` be an object of the derived category `D(R)`. When `R` is
Noetherian, `m`-pseudo-coherence of `K` says exactly that the cohomology of `K` vanishes in all
sufficiently large degrees and that `Hⁱ(K)` is a finite `R`-module for every `i ≥ m`;
pseudo-coherence says the same with finiteness in every degree; and a module is pseudo-coherent
exactly when it is finite. When `R` is a coherent commutative ring and the cohomology of `K`
vanishes in all sufficiently large degrees, `m`-pseudo-coherence says exactly that `Hᵐ(K)` is
finite and `Hⁱ(K)` is coherent — equivalently finitely presented — for every `i > m`, and
pseudo-coherence says exactly that every cohomology module of `K` is coherent.

## Main results

* `StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology`: the three
  Noetherian characterizations of pseudo-coherence, Stacks 066E.
* `StacksDraft.PseudoCoherence.pseudoCoherentFrom_iff_finite_and_coherent_homology`: the
  cohomological characterizations of pseudo-coherence over a coherent ring, Stacks 0EWZ.

## Implementation notes

Complexes are represented by objects of the derived category, and membership in the
bounded-above derived category is expressed by eventual vanishing of the homology objects.
In both characterizations the interesting direction is reduced to Stacks 066B, so the work is
to show that each individual cohomology module is pseudo-coherent in the relevant degree. That
is done once, by a syzygy induction over a class of modules which consists of finite modules
and is closed under kernels of finite free covers: finite modules over a Noetherian ring for
Stacks 066E, coherent modules over a coherent ring for Stacks 0EWZ. Rings are commutative in
Stacks 0EWZ, following the convention of Stacks 05CX.

## References

* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 0EWZ](https://stacks.math.columbia.edu/tag/0EWZ)
-/

@[expose] public section

-- Needed so that the `singleFunctor` and `HomologicalComplex.sc` normalisations below close
-- by `rfl`.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

-- We use the standard construction of the derived category of an abelian category, which
-- supplies the triangulated structure and the cohomology functors `Hⁱ`.
attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.PseudoCoherence

universe u v

/-! ### A syzygy induction shared by the Noetherian and the coherent case -/

/-- A finite free module is `m`-pseudo-coherent for every `m`: it is its own finite free
approximation. -/
private theorem modulePseudoCoherentFrom_finiteFree {R : Type u} [Ring R]
    (N : ModuleCat.{v} R) [Module.Finite R N] [Module.Free R N] (m : ℤ) :
    IsModulePseudoCoherentFrom (R := R) N m := by
  refine ⟨(CochainComplex.singleFunctor _ 0).obj N, isBoundedFiniteFree_single N 0,
    𝟙 _, ?_, ?_⟩
  · intro i _
    change IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map (𝟙 _))
    infer_instance
  · change Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map (𝟙 _))
    infer_instance

/-- Let `Q` be a class of `R`-modules consisting of finite modules and closed under taking the
kernel of a surjection from a finite free module. Then every module in `Q` is
`(-n)`-pseudo-coherent, for every natural number `n`: iterate the syzygy construction and use
the two-out-of-three property of Stacks 064R (3) in the form of Stacks 064R (1). -/
private theorem modulePseudoCoherentFrom_neg_natCast {R : Type u} [Ring R] [Small.{v} R]
    {Q : ModuleCat.{v} R → Prop}
    (hfinite : ∀ M : ModuleCat.{v} R, Q M → Module.Finite R M)
    (hkernel : ∀ (M N : ModuleCat.{v} R) (p : N ⟶ M), Q M → Module.Finite R N →
      Module.Free R N → Q (kernel p))
    (n : ℕ) :
    ∀ M : ModuleCat.{v} R, Q M → IsModulePseudoCoherentFrom (R := R) M (-(n : ℤ)) := by
  induction n with
  | zero =>
    intro M hM
    have := hfinite M hM
    change IsModulePseudoCoherentFrom (R := R) M (0 : ℤ)
    exact (modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
      (R := R) (M : Type v)).1.mpr inferInstance
  | succ n ih =>
    intro M hM
    have := hfinite M hM
    obtain ⟨N, hNfin, hNfree, p, hp⟩ := exists_finite_free_epi M
    have := hNfin
    have := hNfree
    have := hp
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact := ⟨ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p)⟩
    apply _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_one (-(↑(n + 1)))
      hS.singleTriangle hS.singleTriangle_distinguished
    · rw [show -(↑(n + 1) : ℤ) + 1 = -(n : ℤ) by omega]
      exact ih (kernel p) (hkernel M N p hM hNfin hNfree)
    · exact modulePseudoCoherentFrom_finiteFree N _

/-- A module concentrated in degree `0` is `m`-pseudo-coherent for every `m > 0`, because its
cohomology vanishes in all degrees at least `m`. -/
private theorem modulePseudoCoherentFrom_of_pos {R : Type u} [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] (m : ℤ) (hm : 0 < m) :
    IsModulePseudoCoherentFrom (R := R) M m :=
  isPseudoCoherentFrom_of_homology_isZero
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R M)) m
    fun i hi => DerivedCategory.isZero_of_isLE _ 0 i (by omega)

/-- An object with bounded-above cohomology is `n`-pseudo-coherent as soon as `Hⁱ` is
`(n - i)`-pseudo-coherent for every `i ≥ n`; below `n` this is automatic. -/
private theorem pseudoCoherentFrom_of_forall_le {R : Type u} [Ring R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    (n : ℤ) (h : ∀ i : ℤ, n ≤ i → IsModulePseudoCoherentFrom (R := R)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) (n - i)) :
    IsPseudoCoherentFrom K n :=
  (pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove_cohomology K hK).1 n fun i => by
    by_cases hi : n ≤ i
    · exact h i hi
    · exact modulePseudoCoherentFrom_of_pos _ (n - i) (by omega)

/-- The target of an epimorphism from a finite module is finite. -/
private theorem finite_of_epi {R : Type u} [Ring R] {A B : ModuleCat.{v} R}
    [Module.Finite R A] (f : A ⟶ B) [Epi f] : Module.Finite R B :=
  Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Over a Noetherian ring, the source of a monomorphism into a finite module is finite. -/
private theorem finite_of_mono {R : Type u} [Ring R] [IsNoetherianRing R] {A B : ModuleCat.{v} R}
    [Module.Finite R B] (f : A ⟶ B) [Mono f] : Module.Finite R A :=
  Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-! ### Pseudo-coherence over a Noetherian ring -/

/-- Over a Noetherian ring, the cohomology of a cochain complex in a degree whose term is
finite is finite.

Published rather than sealed: five further modules had each re-declared this, and this is the
most general of the six statements -- the others all assume `CommRing`. -/
public theorem finite_homology_of_finite_X {R : Type u} [Ring R] [IsNoetherianRing R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) [Module.Finite R (E.X i)] :
    Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
        (ComplexShape.up ℤ) i).obj E) := by
  change Module.Finite R (E.homology i)
  have : Module.Finite R (E.cycles i) := finite_of_mono (E.iCycles i)
  exact finite_of_epi (E.homologyπ i)

/-- Over a Noetherian ring, every cohomology module of a bounded complex of finite free modules
is finite. -/
private theorem finite_homology_of_isBoundedFiniteFree {R : Type u} [Ring R]
    [IsNoetherianRing R] (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hE : IsBoundedFiniteFree E) (i : ℤ) :
    Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
        (DerivedCategory.Q.obj E)) := by
  have : Module.Finite R (E.X i) := (hE.finiteFree i).1
  have := finite_homology_of_finite_X E i
  exact Module.Finite.equiv (bridgeIso E i).symm.toLinearEquiv

/-- Over a Noetherian ring, a finite module is `(-n)`-pseudo-coherent for every natural number
`n`: the syzygies of a finite module are finite. -/
@[sga "6 I 5.0" "partial"]
private theorem modulePseudoCoherentFrom_neg_natCast_of_finite {R : Type u} [Ring R]
    [IsNoetherianRing R] [Small.{v} R] (n : ℕ) (M : ModuleCat.{v} R) [Module.Finite R M] :
    IsModulePseudoCoherentFrom (R := R) M (-(n : ℤ)) := by
  refine modulePseudoCoherentFrom_neg_natCast (Q := fun N => Module.Finite R N)
    (fun _ h => h) ?_ n M inferInstance
  intro _ N p _ hN _
  have := hN
  exact finite_of_mono (kernel.ι p)

/-- Over a Noetherian ring, a module is pseudo-coherent exactly when it is finite. -/
@[sga "6 I 5.0" "more general"]
private theorem modulePseudoCoherent_iff_finite {R : Type u} [Ring R] [IsNoetherianRing R]
    [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] :
    IsModulePseudoCoherent (R := R) M ↔ Module.Finite R M := by
  constructor
  · intro h
    exact (modulePseudoCoherent_iff_finiteness_and_resolutions_of_small (R := R) M).1.1
      ((pseudoCoherent_iff_all ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
        (ModuleCat.of R M))).1 h 0)
  · intro hM
    have := hM
    refine (pseudoCoherent_iff_all ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
      (ModuleCat.of R M))).2 fun m => ?_
    exact IsPseudoCoherentFrom.mono
      (modulePseudoCoherentFrom_neg_natCast_of_finite (-m).toNat (ModuleCat.of R M)) (by omega)

/-- Over a Noetherian ring, pseudo-coherence from degree `n` means bounded-above cohomology which
is finite in degrees at least `n`. -/
private theorem pseudoCoherentFrom_iff_boundedAbove_finite_homology_of_noetherian
    {R : Type u} [Ring R] [IsNoetherianRing R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (n : ℤ) :
    IsPseudoCoherentFrom K n ↔
      (∃ b : ℤ, ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) ∧
      ∀ i : ℤ, n ≤ i →
        Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
  constructor
  · rintro ⟨E, hE, α, hiso, hepi⟩
    obtain ⟨b, _⟩ := hE.upperBound
    refine ⟨⟨max b n, ?_⟩, ?_⟩
    · intro i hi
      have := hiso i (lt_of_le_of_lt (le_max_right _ _) hi)
      have hEi : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
          (DerivedCategory.Q.obj E)) :=
        DerivedCategory.isZero_of_isLE _ b i (lt_of_le_of_lt (le_max_left _ _) hi)
      exact hEi.of_iso (asIso ((DerivedCategory.homologyFunctor
        (ModuleCat.{v} R) i).map α)).symm
    · intro i hi
      have := finite_homology_of_isBoundedFiniteFree E hE i
      rcases hi.eq_or_lt with rfl | hi
      · exact finite_of_epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map α)
      · have := hiso i hi
        exact Module.Finite.equiv
          (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α)).toLinearEquiv
  · rintro ⟨hbounded, hfinite⟩
    refine pseudoCoherentFrom_of_forall_le K hbounded n fun i hi => ?_
    have hp := (modulePseudoCoherent_iff_finite (R := R)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)).2 (hfinite i hi)
    exact (pseudoCoherent_iff_all
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))).1 hp (n - i)

/-- **Stacks 066E.** Over a Noetherian ring, pseudo-coherence from degree `m` means
bounded-above finite homology in degrees at least `m`; pseudo-coherence means bounded-above
finite homology in all degrees; and pseudo-coherence of a module is equivalent to its
finiteness. -/
@[stacks 066E]
theorem pseudoCoherent_iff_boundedAbove_finite_homology
    {R : Type u} [Ring R] [IsNoetherianRing R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ)
    (M : Type v) [AddCommGroup M] [Module R M] :
    (IsPseudoCoherentFrom K m ↔
      (∃ b : ℤ, ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) ∧
      ∀ i : ℤ, m ≤ i →
        Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) ∧
    (IsPseudoCoherent K ↔
      (∃ b : ℤ, ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) ∧
      ∀ i : ℤ,
        Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) ∧
    (IsModulePseudoCoherent (R := R) M ↔ Module.Finite R M) := by
  have hfrom := pseudoCoherentFrom_iff_boundedAbove_finite_homology_of_noetherian K
  refine ⟨hfrom m, ?_, modulePseudoCoherent_iff_finite (R := R) M⟩
  constructor
  · intro hK
    have hall := (pseudoCoherent_iff_all K).1 hK
    obtain ⟨E, hE, ⟨e⟩⟩ := hK
    obtain ⟨b, _⟩ := hE.upperBound
    refine ⟨⟨b, ?_⟩, fun i ↦ ((hfrom i).mp (hall i)).2 i le_rfl⟩
    intro i hi
    exact (DerivedCategory.isZero_of_isLE _ b i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e).symm
  · rintro ⟨hbounded, hfinite⟩
    exact (pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove_cohomology
      K hbounded).2 (fun i ↦ (modulePseudoCoherent_iff_finite
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)).2 (hfinite i))

/-! ### Pseudo-coherence over a coherent ring -/

/-- Over a coherent commutative ring a module is coherent exactly when it is finitely
presented, by Stacks 05CX. -/
private theorem isCoherent_iff_finitePresentation {R : Type u} [CommRing R] [IsCoherentRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module.IsCoherent R M ↔ Module.FinitePresentation R M :=
  coherent_iff_finitePresentation_of_coherentRing R IsCoherentRing.isCoherent M

/-- The homology of a short complex whose middle and right terms are coherent and whose left
term is finite is coherent: it is a quotient of the coherent kernel of `g` by the finitely
generated image of `f`. -/
private theorem isCoherent_homology {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v} R))
    [Module.Finite R S.X₁] [Module.IsCoherent R S.X₂] [Module.IsCoherent R S.X₃] :
    Module.IsCoherent R S.homology := by
  have : Module.IsCoherent R (LinearMap.ker S.g.hom) :=
    (coherent_ker_and_coker_of_coherent S.g.hom).1
  have : Module.IsCoherent R S.moduleCatLeftHomologyData.H :=
    isCoherent_quotient_of_fg _ (Submodule.fg_range S.moduleCatToCycles)
  exact isCoherentModule_of_linearEquiv R S.moduleCatHomologyIso.symm.toLinearEquiv
    inferInstance

/-- Over a coherent commutative ring, every cohomology module of a complex of finite free
modules is coherent. -/
@[sga "6 IV 2.4" "partial"]
private theorem isCoherent_homology_of_finiteFree {R : Type u} [CommRing R] [IsCoherentRing R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (hE : ∀ i, IsFiniteFree (E.X i)) (i : ℤ) :
    Module.IsCoherent R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
        (DerivedCategory.Q.obj E)) := by
  have hcoh (j : ℤ) : Module.IsCoherent R (E.X j) := by
    obtain ⟨_, _⟩ := hE j
    exact (isCoherent_iff_finitePresentation _).mpr
      (Module.finitePresentation_of_projective R (E.X j))
  have : Module.Finite R (E.sc i).X₁ := (hE _).1
  have : Module.IsCoherent R (E.sc i).X₂ := hcoh _
  have : Module.IsCoherent R (E.sc i).X₃ := hcoh _
  have : Module.IsCoherent R
      ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i).obj E) :=
    isCoherent_homology (E.sc i)
  exact isCoherentModule_of_linearEquiv R (bridgeIso E i).symm.toLinearEquiv inferInstance

/-- Over a coherent commutative ring, an `m`-pseudo-coherent object has finite degree-`m`
cohomology and coherent cohomology in every higher degree. -/
private theorem finite_and_isCoherent_homology_of_pseudoCoherentFrom {R : Type u} [CommRing R]
    [IsCoherentRing R] {K : DerivedCategory (ModuleCat.{v} R)} {m : ℤ}
    (hK : IsPseudoCoherentFrom K m) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K) ∧
      ∀ i : ℤ, m < i →
        Module.IsCoherent R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
  obtain ⟨E, hE, α, hi, he⟩ := hK
  constructor
  · have := isCoherent_homology_of_finiteFree E hE.finiteFree m
    have := Module.IsCoherent.finite (R := R)
      (M := (DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj
        (DerivedCategory.Q.obj E))
    exact finite_of_epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map α)
  · intro i hmi
    have := isCoherent_homology_of_finiteFree E hE.finiteFree i
    have := hi i hmi
    exact isCoherentModule_of_linearEquiv R
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α)).toLinearEquiv
      inferInstance

/-- Over a coherent commutative ring, a coherent module is `(-n)`-pseudo-coherent for every
natural number `n`: the syzygies of a coherent module are coherent. -/
private theorem modulePseudoCoherentFrom_neg_natCast_of_isCoherent {R : Type u} [CommRing R]
    [IsCoherentRing R] [Small.{v} R] (n : ℕ) (M : ModuleCat.{v} R) [Module.IsCoherent R M] :
    IsModulePseudoCoherentFrom (R := R) M (-(n : ℤ)) := by
  refine modulePseudoCoherentFrom_neg_natCast (Q := fun N => Module.IsCoherent R N)
    (fun _ h => by have := h; exact Module.IsCoherent.finite) ?_ n M inferInstance
  intro _ N p hM hNfin hNfree
  have := hM
  have := hNfin
  have := hNfree
  -- Naming the projectivity of the free module `N` keeps instance search off the general
  -- `Module.Projective` hierarchy, which is expensive here.
  have : Module.Projective R N := Module.Projective.of_free
  have : Module.IsCoherent R N := (isCoherent_iff_finitePresentation _).mpr
    (Module.finitePresentation_of_projective R N)
  have : Module.IsCoherent R (LinearMap.ker p.hom) :=
    (coherent_ker_and_coker_of_coherent p.hom).1
  exact isCoherentModule_of_linearEquiv R (ModuleCat.kernelIsoKer p).symm.toLinearEquiv
    inferInstance

/-- Over a coherent commutative ring, a coherent module is `m`-pseudo-coherent for every `m`. -/
private theorem modulePseudoCoherentFrom_of_isCoherent {R : Type u} [CommRing R]
    [IsCoherentRing R] [Small.{v} R] (M : ModuleCat.{v} R) [Module.IsCoherent R M] (m : ℤ) :
    IsModulePseudoCoherentFrom (R := R) M m :=
  IsPseudoCoherentFrom.mono
    (modulePseudoCoherentFrom_neg_natCast_of_isCoherent (-m).toNat M) (by omega)

/-- The characterizations of Stacks 0EWZ for module carriers which already contain the ring. -/
private theorem pseudoCoherentFrom_iff_finite_and_coherent_homology_of_small {R : Type u}
    [CommRing R] [IsCoherentRing R] [Small.{v} R] (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    (m : ℤ) :
    let H := fun i : ℤ =>
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K
    let finiteAndCoherent :=
      Module.Finite R (H m) ∧ ∀ i : ℤ, m < i → Module.IsCoherent R (H i)
    let finiteAndFinitePresentation :=
      Module.Finite R (H m) ∧ ∀ i : ℤ, m < i → Module.FinitePresentation R (H i)
    (IsPseudoCoherentFrom K m ↔ finiteAndCoherent) ∧
      (finiteAndCoherent ↔ finiteAndFinitePresentation) ∧
      (IsPseudoCoherent K ↔ ∀ i : ℤ, Module.IsCoherent R (H i)) := by
  dsimp only
  have from_cohomology (m : ℤ)
      (hfin : Module.Finite R
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K))
      (hcoh : ∀ i : ℤ, m < i → Module.IsCoherent R
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
      IsPseudoCoherentFrom K m := by
    refine pseudoCoherentFrom_of_forall_le K hK m fun i hmi => ?_
    rcases hmi.eq_or_lt with rfl | hi
    · simpa only [sub_self] using
        (modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
          (R := R) ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K)).1.mpr hfin
    · have := hcoh i hi
      exact modulePseudoCoherentFrom_of_isCoherent _ _
  refine ⟨⟨finite_and_isCoherent_homology_of_pseudoCoherentFrom,
    fun h => from_cohomology m h.1 h.2⟩, ?_, ?_⟩
  · exact and_congr_right fun _ => forall_congr' fun i =>
      imp_congr_right fun _ => isCoherent_iff_finitePresentation _
  · constructor
    · intro h i
      exact (finite_and_isCoherent_homology_of_pseudoCoherentFrom
        ((pseudoCoherent_iff_all K).mp h (i - 1))).2 i (by omega)
    · intro h
      apply (pseudoCoherent_iff_all K).mpr
      intro m
      have := h m
      exact from_cohomology m Module.IsCoherent.finite (fun i _ => h i)

/-- **Stacks 0EWZ.** Over a coherent ring, a bounded-above derived object is
`m`-pseudo-coherent exactly when its degree-`m` cohomology is finite and its higher cohomology
modules are coherent, equivalently finitely presented. It is pseudo-coherent exactly when all
its cohomology modules are coherent. -/
@[stacks 0EWZ, sga "6 I 3.5" "b), coherent ring", sga "6 I 2.11" "Part b), special case"]
theorem pseudoCoherentFrom_iff_finite_and_coherent_homology
    {R : Type u} [CommRing R] [IsCoherentRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K))
    (m : ℤ) :
    let H := fun i : ℤ =>
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K
    let finiteAndCoherent :=
      Module.Finite R (H m) ∧ ∀ i : ℤ, m < i → Module.IsCoherent R (H i)
    let finiteAndFinitePresentation :=
      Module.Finite R (H m) ∧ ∀ i : ℤ, m < i → Module.FinitePresentation R (H i)
    (IsPseudoCoherentFrom K m ↔ finiteAndCoherent) ∧
      (finiteAndCoherent ↔ finiteAndFinitePresentation) ∧
      (IsPseudoCoherent K ↔ ∀ i : ℤ, Module.IsCoherent R (H i)) :=
  pseudoCoherentFrom_iff_finite_and_coherent_homology_of_small K hK m

end StacksDraft.PseudoCoherence
