module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedPushforwardPreservesComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The bounded below edge isomorphism

Let `F : A ⥤ B` be a left exact additive functor of abelian categories and let
`R : D(A) ⥤ D(B)` be a right derived functor of `F` on the unbounded derived category.
The imported `HypercohomologyEdge.EdgeMorphismOnARingedSite` module constructs the edge
morphism
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison : R ⋙ H^q ⟶ H^q
  ⋙ F` and reduces its invertibility at
a K-injective complex to invertibility of the complex level comparison
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparison`.  This file supplies
  that complex level input in the bounded
below case and assembles the resulting statement about an arbitrary bounded below object of
`D(A)` whose cohomology objects are right acyclic for `F`.

The argument is the elementary one; it uses no spectral sequence.  Let `I` be a cochain complex
of injectives concentrated in degrees `≥ n` with every cohomology object right acyclic for `F`.
Write `Z^q` for the cycles and `B^q` for the kernel of `Z^q ⟶ H^q`, the boundaries.  There are
two short exact sequences,

* `0 ⟶ Z^{q-1} ⟶ I^{q-1} ⟶ B^q ⟶ 0` (`cyclesSC`), and
* `0 ⟶ B^q ⟶ Z^q ⟶ H^q ⟶ 0` (`homologySC`).

Right acyclicity of every `Z^q` follows by induction upward from degree `n`, where `Z^n = H^n`
because the incoming differential vanishes: the first sequence propagates acyclicity from
`Z^{q-1}` and the injective object `I^{q-1}` to `B^q`, and the second from `B^q` and `H^q` to
`Z^q`.  This is the two out of three closure of [Stacks, Tag 015D],
`CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact`, which also returns the
short exactness of the `F`-image of each sequence.

Those two short exactnesses are what identifies `H^q(F I)` with `F(H^q I)`.  The image of the
second sequence exhibits `F(H^q)` as a cokernel of `F(B^q) ⟶ F(Z^q)`; the image of the first
makes `F(I^{q-1}) ⟶ F(B^q)` an epimorphism, so that cokernel is also a cokernel of
`F(I^{q-1}) ⟶ F(Z^q)`, which is `H^q(F I)` once `Z^q(F I)` is identified with `F(Z^q)` by the
already available
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.isIso_cyclesComparison`. The inverse of
the comparison is written down directly from that cokernel property, so no transport of colimits is
needed.

## Main results

* `Stacks.BoundedBelowEdge.rightAcyclic_of_injective`: an injective object is right acyclic.
* `Stacks.BoundedBelowEdge.rightAcyclic_cycles`: the cycles of a bounded below complex of
  injectives with right acyclic cohomology are right acyclic.
* `Stacks.BoundedBelowEdge.isIso_homologyComparison_of_isStrictlyGE`: the complex level
  comparison `H^q(F I) ⟶ F(H^q I)` is invertible for such a complex.
* `Stacks.BoundedBelowEdge.isIso_derivedHomologyComparison_app_of_isGE`: **the edge morphism is
  invertible at a bounded below object of `D(A)` whose cohomology objects are right acyclic.**

## Implementation notes

**Nothing here carries a Stacks attribute.**  Stacks 015J is the statement about the two
spectral sequences of a Cartan--Eilenberg resolution, and it is already registered on
`CochainComplex.CartanEilenbergResolution.exists_homologyIso_rightDerivedPlus`
(`StacksFrontier/Algebra/Homology/CartanEilenbergResolutions.lean`).  The results below are the
degenerate consequence of its second spectral sequence, reached without any spectral sequence,
and they are not a clause of that tag.  In particular the 015J statement in this development
produces `Nonempty` isomorphisms of objects with no comparison morphism identified, so it could
not have been used here even if it were a clause: the target below is `IsIso` of a specific
natural transformation.

Right acyclicity of an injective object is obtained from [Stacks, Tag 015C] part (2) together
with the vanishing of Mathlib's `Functor.rightDerived` on injectives, the two being compared by
`Stacks.DerivedIndexing.rightDerivedIso`.

The three short complexes are `abbrev`s rather than `def`s on purpose.  As `def`s, `rw` cannot
see that `(bdrySC I q).X₁` is `I.X (q - 1)`, and every rewrite through an associativity in these
composites fails with an ill-typed motive; making them reducible removes that failure
everywhere at once.

The priority bump via `attribute [local instance 2000]` on
`HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso` follows the precedent of
`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective.lean`.
Without it, the instance
`(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor _` needed merely
to *state* `Functor.rightAcyclic` exhausts the instance search budget, so no declaration
mentioning right acyclicity elaborates at all.

All universes are independent and auto-bound; no narrowing to a common universe is inherited.

## References

* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.BoundedBelowEdge

open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type*} [Category* A] [Abelian A]

section ShortComplexes

variable (I : CochainComplex A ℤ)

/-- The short complex `I^{q-1} ⟶ Z^q ⟶ H^q`, whose cycles are the `q`-boundaries of `I`. -/
public abbrev bdrySC (q : ℤ) : ShortComplex A :=
  ShortComplex.mk (I.toCycles (q - 1) q) (I.homologyπ q) (by simp)

/-- The first map of `bdrySC I q` is `I.toCycles (q - 1) q`. -/
@[simp] public lemma bdrySC_f (q : ℤ) : (bdrySC I q).f = I.toCycles (q - 1) q := rfl

/-- The second map of `bdrySC I q` is the projection `I.homologyπ q`. -/
@[simp] public lemma bdrySC_g (q : ℤ) : (bdrySC I q).g = I.homologyπ q := rfl

/-- `H^q` is a cokernel of `I^{q-1} ⟶ Z^q`, so that short complex is exact. -/
public lemma exact_bdrySC (q : ℤ) : (bdrySC I q).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (I.homologyIsCokernel (q - 1) q (by simp))

/-- The map from `I^{q-1}` onto the `q`-boundaries is an epimorphism. -/
public instance epi_bdrySC_toCycles (q : ℤ) : Epi (bdrySC I q).toCycles :=
  (ShortComplex.exact_iff_epi_toCycles _).1 (exact_bdrySC I q)

/-- The map `I.toCycles (q - 1) q` factors through the `q`-boundaries. -/
public lemma bdrySC_toCycles_iCycles (q : ℤ) :
    @Eq (I.X (q - 1) ⟶ I.cycles q)
      ((bdrySC I q).toCycles ≫ (bdrySC I q).iCycles) (I.toCycles (q - 1) q) :=
  ShortComplex.toCycles_i (bdrySC I q)

/-- Cycles in degree `q - 1` are killed by the differential into degree `q`. -/
public lemma iCycles_comp_toCycles (q : ℤ) :
    I.iCycles (q - 1) ≫ I.toCycles (q - 1) q = 0 := by
  rw [← cancel_mono (I.iCycles q)]
  simp

/-- The short complex `0 ⟶ Z^{q-1} ⟶ I^{q-1} ⟶ B^q ⟶ 0`. -/
public abbrev cyclesSC (q : ℤ) : ShortComplex A :=
  ShortComplex.mk (I.iCycles (q - 1)) (bdrySC I q).toCycles
    ((cancel_mono (bdrySC I q).iCycles).1 (by
      have h : (I.iCycles (q - 1) ≫ (bdrySC I q).toCycles) ≫ (bdrySC I q).iCycles =
          I.iCycles (q - 1) ≫ ((bdrySC I q).toCycles ≫ (bdrySC I q).iCycles) :=
        Category.assoc _ _ _
      rw [h, bdrySC_toCycles_iCycles, iCycles_comp_toCycles, zero_comp]))

/-- The first map of `cyclesSC I q` is the inclusion `I.iCycles (q - 1)`. -/
@[simp] public lemma cyclesSC_f (q : ℤ) : (cyclesSC I q).f = I.iCycles (q - 1) := rfl

/-- The second map of `cyclesSC I q` is the map of `I^{q-1}` onto the `q`-boundaries. -/
@[simp] public lemma cyclesSC_g (q : ℤ) : (cyclesSC I q).g = (bdrySC I q).toCycles := rfl

/-- The short complex `0 ⟶ B^q ⟶ Z^q ⟶ H^q ⟶ 0`. -/
public abbrev homologySC (q : ℤ) : ShortComplex A :=
  ShortComplex.mk (bdrySC I q).iCycles (I.homologyπ q) ((bdrySC I q).iCycles_g)

/-- The first map of `homologySC I q` is the inclusion of the `q`-boundaries into the
`q`-cycles. -/
@[simp] public lemma homologySC_f (q : ℤ) : (homologySC I q).f = (bdrySC I q).iCycles := rfl

/-- The second map of `homologySC I q` is the projection `I.homologyπ q`. -/
@[simp] public lemma homologySC_g (q : ℤ) : (homologySC I q).g = I.homologyπ q := rfl

/-- `Z^{q-1}` is a kernel of `I^{q-1} ⟶ B^q`: the boundaries map and the differential have the
same kernel, the inclusion of the boundaries into the cycles being a monomorphism. -/
public lemma shortExact_cyclesSC (q : ℤ) : (cyclesSC I q).ShortExact := by
  have : Mono (cyclesSC I q).f := by rw [cyclesSC_f]; infer_instance
  have : Epi (cyclesSC I q).g := by rw [cyclesSC_g]; infer_instance
  refine ShortComplex.ShortExact.mk
    (ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ ?_))
  intro W k hk
  have h0 : k ≫ I.toCycles (q - 1) q = 0 := by
    rw [← bdrySC_toCycles_iCycles I q, ← Category.assoc, hk, zero_comp]
  have hk' : k ≫ I.d (q - 1) q = 0 := by
    rw [← I.toCycles_i (q - 1) q, ← Category.assoc, h0, zero_comp]
  exact ⟨I.liftCycles k q (by simp) hk', by simp⟩

/-- `H^q` is a cokernel of `B^q ⟶ Z^q`: it is a cokernel of `I^{q-1} ⟶ Z^q`, which factors
through the boundaries by an epimorphism. -/
public lemma shortExact_homologySC (q : ℤ) : (homologySC I q).ShortExact := by
  have : Mono (homologySC I q).f := by rw [homologySC_f]; infer_instance
  have : Epi (homologySC I q).g := by rw [homologySC_g]; infer_instance
  refine ShortComplex.ShortExact.mk
    (ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ' _ _ ?_))
  intro W k hk
  refine CokernelCofork.IsColimit.desc' (I.homologyIsCokernel (q - 1) q (by simp)) k ?_
  rw [← bdrySC_toCycles_iCycles I q, Category.assoc, hk, comp_zero]

end ShortComplexes

section Acyclic

variable {B : Type*} [Category* B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (I : CochainComplex A ℤ)

/-- An injective object is right acyclic for any left exact additive functor: its higher
classical right derived functors vanish, and those compute `Functor.rightDerivedPlus`. -/
public lemma rightAcyclic_of_injective (X : A) [Injective X] : F.rightAcyclic X :=
  ((F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus X).2 ‹_›).2 fun i hi => by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = ((m + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
    exact IsZero.of_iso (F.isZero_rightDerived_obj_injective_succ m X)
      ((Stacks.DerivedIndexing.rightDerivedIso F (m + 1)).app X).symm

/-- **The inductive step.**  With `Z^{q-1}` right acyclic, `I^{q-1}` injective and `H^q` right
acyclic, the cycles `Z^q` are right acyclic, and the `F`-image of each of the two short exact
sequences around the boundaries is again short exact. -/
public lemma rightAcyclic_cycles_and_shortExact_map (q : ℤ)
    (hinj : ∀ j, Injective (I.X j)) (hH : F.rightAcyclic (I.homology q))
    (hprev : F.rightAcyclic (I.cycles (q - 1))) :
    F.rightAcyclic (I.cycles q) ∧ ((cyclesSC I q).map F).ShortExact ∧
      ((homologySC I q).map F).ShortExact := by
  have := hinj (q - 1)
  obtain ⟨hB, hSE1⟩ :=
    (F.rightAcyclic_and_shortExact_map_of_shortExact (cyclesSC I q)
      (shortExact_cyclesSC I q)).2.1 hprev (rightAcyclic_of_injective F (I.X (q - 1)))
  obtain ⟨hZ, hSE2⟩ :=
    (F.rightAcyclic_and_shortExact_map_of_shortExact (homologySC I q)
      (shortExact_homologySC I q)).1 hB hH
  exact ⟨hZ, hSE1, hSE2⟩

/-- The cycles of a cochain complex of injectives concentrated in degrees `≥ n` whose
cohomology objects are right acyclic are themselves right acyclic, in every degree. -/
public lemma rightAcyclic_cycles (n : ℤ) [I.IsStrictlyGE n]
    (hinj : ∀ j, Injective (I.X j)) (hH : ∀ j, F.rightAcyclic (I.homology j)) (j : ℤ) :
    F.rightAcyclic (I.cycles j) := by
  have hbase : F.rightAcyclic (I.cycles n) := by
    have hd : I.d (n - 1) n = 0 :=
      (I.isZero_of_isStrictlyGE n (n - 1) (by omega)).eq_of_src _ _
    have := I.isIso_homologyπ (n - 1) n (by simp) hd
    exact F.rightAcyclic.prop_of_iso (asIso (I.homologyπ n)).symm (hH n)
  have hstep : ∀ k : ℕ, F.rightAcyclic (I.cycles (n + (k : ℤ))) := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
      have he : n + ((k + 1 : ℕ) : ℤ) - 1 = n + (k : ℤ) := by push_cast; ring
      exact (rightAcyclic_cycles_and_shortExact_map F I (n + ((k + 1 : ℕ) : ℤ)) hinj
        (hH _) (by rwa [he])).1
  rcases lt_or_ge j n with hj | hj
  · have hzX : IsZero (I.X j) := I.isZero_of_isStrictlyGE n j hj
    have := hinj j
    exact F.rightAcyclic.prop_of_iso (hzX.iso (IsZero.of_mono (I.iCycles j) hzX))
      (rightAcyclic_of_injective F (I.X j))
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = n + (k : ℤ) := ⟨(j - n).toNat, by omega⟩
    exact hstep k

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] in
/-- `toCycles` of the image complex, followed by the cycles comparison, is `F` applied to
`toCycles`. -/
@[reassoc]
public lemma toCycles_comp_cyclesComparison (q : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).toCycles (q - 1) q ≫
        cyclesComparison F I q = F.map (I.toCycles (q - 1) q) := by
  have := mono_map_iCycles F I q
  rw [← cancel_mono (F.map (I.iCycles q)), Category.assoc, cyclesComparison_comp_map_iCycles,
    ← F.map_comp, I.toCycles_i]
  exact ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).toCycles_i (q - 1) q

/-- **The complex level comparison `H^q(F I) ⟶ F(H^q I)` is invertible** for a cochain complex
`I` of injective objects concentrated in degrees `≥ n` whose cohomology objects are right
acyclic for `F`. -/
public theorem isIso_homologyComparison_of_isStrictlyGE (n : ℤ) [I.IsStrictlyGE n]
    (hinj : ∀ j, Injective (I.X j)) (hH : ∀ j, F.rightAcyclic (I.homology j)) (q : ℤ) :
    IsIso (homologyComparison F I q) := by
  obtain ⟨-, hSE1, hSE2⟩ := rightAcyclic_cycles_and_shortExact_map F I q hinj (hH q)
    (rightAcyclic_cycles F I n hinj hH (q - 1))
  have := hSE2.epi_g
  have : Epi (F.map (I.homologyπ q)) := hSE2.epi_g
  have : Epi (F.map (bdrySC I q).toCycles) := hSE1.epi_g
  have hvan : F.map (bdrySC I q).iCycles ≫ inv (cyclesComparison F I q) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homologyπ q = 0 := by
    rw [← cancel_epi (F.map (bdrySC I q).toCycles), comp_zero, ← Category.assoc,
      ← F.map_comp, bdrySC_toCycles_iCycles, ← toCycles_comp_cyclesComparison F I q,
      Category.assoc, IsIso.hom_inv_id_assoc]
    simp
  obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' hSE2.exact.gIsCokernel
    (inv (cyclesComparison F I q) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homologyπ q) hvan
  have hg' : F.map (I.homologyπ q) ≫ g = inv (cyclesComparison F I q) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homologyπ q := hg
  refine ⟨g, ?_, ?_⟩
  · rw [← cancel_epi (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homologyπ q),
      Category.comp_id, ← Category.assoc, homologyπ_comp_homologyComparison, Category.assoc,
      hg', IsIso.hom_inv_id_assoc]
  · rw [← cancel_epi (F.map (I.homologyπ q)), Category.comp_id, ← Category.assoc, hg',
      Category.assoc, homologyπ_comp_homologyComparison, IsIso.inv_hom_id_assoc]

/-- **The bounded below edge isomorphism.**  The edge morphism
`H^q(R E) ⟶ F(H^q E)` of a right derived functor `R` of `F` on the unbounded derived category is
invertible at an object `E` of `D(A)` which is cohomologically bounded below and all of whose
cohomology objects are right acyclic for `F`.

`E` is represented by a cochain complex of injectives concentrated in degrees `≥ n`, which is
K-injective, so `Tag0BKZ.isIso_derivedHomologyComparison_app_of_isKInjective` reduces the claim
to the complex level comparison for that representative. -/
public theorem isIso_derivedHomologyComparison_app_of_isGE
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (f : K ⟶ J),
      J.IsKInjective ∧ QuasiIso f)
    (q : ℤ) (E : DerivedCategory A) (n : ℤ) [E.IsGE n]
    (hH : ∀ j, F.rightAcyclic ((DerivedCategory.homologyFunctor A j).obj E)) :
    IsIso ((derivedHomologyComparison F R α hA q).app E) := by
  obtain ⟨K, _, ⟨e⟩⟩ := E.exists_iso_Q_obj_of_isGE n
  obtain ⟨L, i, hqi, hLinj, hLGE⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n
  have : QuasiIso i := hqi
  have : L.IsStrictlyGE n := hLGE
  have : ∀ j, Injective (L.X j) := hLinj
  have : IsIso (DerivedCategory.Q.map i) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  have eE : E ≅ DerivedCategory.Q.obj L := e ≪≫ asIso (DerivedCategory.Q.map i)
  have hH' : ∀ j, F.rightAcyclic (L.homology j) := fun j =>
    F.rightAcyclic.prop_of_iso ((DerivedCategory.homologyFunctor A j).mapIso eE ≪≫
      (DerivedCategory.homologyFunctorFactors A j).app L) (hH j)
  have := isIso_homologyComparison_of_isStrictlyGE F L n hLinj hH' q
  have eE' : E ≅ DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) :=
    eE ≪≫ ((DerivedCategory.quotientCompQhIso A).app L).symm
  exact (NatTrans.isIso_app_iff_of_iso _ eE').2
    (isIso_derivedHomologyComparison_app_of_isKInjective F R α hA q L
      (CochainComplex.isKInjective_of_injective L n))

end Acyclic

end Stacks.BoundedBelowEdge

end
