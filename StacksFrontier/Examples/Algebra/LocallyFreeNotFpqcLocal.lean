module

public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.PicardGroup
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneModule.Basic
public import StacksFrontier.RingTheory.Flat.DirectLimit
public import StacksFrontier.RingTheory.LocalProperties.Projective
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Local freeness is not an fpqc-local property of modules

Let `R` be a commutative ring and `L : ℕ → Type u` a family of rank one locally free
`R`-modules. The direct sum `M = ⨁ n, L n` becomes free after a faithfully flat base change
`R → S`, while `M` itself need not be locally free. Local freeness of a module therefore does
not descend along faithfully flat ring maps, that is, it is not an fpqc-local property.

## Main results

* `Stacks.Examples.exists_faithfullyFlat_free_baseChange_directSum`: a countable direct sum of
  rank one locally free modules is projective and becomes free over a faithfully flat algebra.
* `Stacks.Examples.exists_faithfullyFlat_free_baseChange_not_isLocallyFree`: if such a direct
  sum is moreover not locally free, local freeness fails to descend along the faithfully flat
  map constructed above.

## Implementation notes

Both statements are conditional on the hypotheses of the source: that the summands are rank one
locally free, and — for the second — that the sum is not locally free. That a direct sum of rank
one locally free modules which is not locally free exists at all is **Stacks 05WL**, which the
source cites rather than proves and which is not formalized here; so the second statement is an
implication and does not on its own establish that some module fails to descend. Rank one local
freeness is the predicate `Module.IsFiniteLocallyFreeOfRank R (L n) 1`, which is the source's
wording; it is converted internally to `Module.Invertible R (L n)` by
`Module.isFiniteLocallyFreeOfRank_one_iff_invertible`. Projectivity of the sum, a hypothesis in
the source, is proved rather than assumed: an invertible module is projective and projectivity
passes to direct sums. The failing descent property is `Module.IsLocallyFree`, the affine-cover
notion, matching the sibling counterexample for Tag 05WJ.

The witness `S` is not the graded algebra `⨁_{i ∈ ℤ} L_1^{⊗i} ⊗ … ⊗ L_m^{⊗i_m}` displayed in
the source: integer tensor powers of a module, and the associated integer-graded algebra, are
available neither in Mathlib nor here. Instead `S` is built from localizations. An invertible
module is free on a finite cover of `Spec R` by basic opens, so for each `n` there is a finite
family `s n ⊆ R` generating the unit ideal with `L n` free over each `R_r`, `r ∈ s n`. The
`m`-th stage is the finite product `∏_{f} R_{f_0 ⋯ f_{m-1}}` over all choices `f` of one element
of `s n` for each `n < m`; it is faithfully flat over `R` because the products `f_0 ⋯ f_{m-1}`
again generate the unit ideal, and `L n ⊗ R_{f_0 ⋯ f_{m-1}}` is free for `n < m` since `f n`
divides `f_0 ⋯ f_{m-1}`. The transition maps are the localization maps along divisibility, and
`S` is the colimit of the resulting system; it is faithfully flat over `R` by Tag 090N, and every
`L n` is trivialized in it. Freeness is transported along the structure maps through the Picard
group: triviality of the class of `L n` in `Pic` of a stage implies triviality of its class in
`Pic S`, by functoriality of `CommRing.Pic.mapRingHom`.

The source also records a question it leaves open: if `A → B` is a faithfully flat ring map of
finite presentation and `M` is an `A`-module with `M ⊗_A B` free, must `M` be locally free over
`A`? The source states that the answer is unknown in general, and that it is affirmative for
Noetherian `A` by results of Bass. Neither the question nor the Noetherian case is formalized
here: the question is open in the source, so it is recorded in prose only, and the Noetherian
case is a bibliography reference rather than a tag of the source.

## References

* [Stacks Project, Tag 05VF](https://stacks.math.columbia.edu/tag/05VF)
* [H. Bass, *Big projective modules are free*][Bass], the Noetherian case of the open question
-/

@[expose] public section

namespace Stacks.Examples

open TensorProduct DirectSum CommRing

universe u

/-! ### Trivializing an invertible module over a localization -/

section Localization

variable {R : Type u} [CommRing R]

/-- The localization map `R_r → R_a` attached to a divisibility `r ∣ a`. -/
private noncomputable def awayLift {r a : R} (hra : r ∣ a) :
    Localization.Away r →+* Localization.Away a :=
  IsLocalization.Away.lift r (g := algebraMap R (Localization.Away a))
    (isUnit_of_dvd_unit (map_dvd _ hra) (IsLocalization.Away.algebraMap_isUnit a))

private theorem awayLift_comp {r a : R} (hra : r ∣ a) :
    (awayLift hra).comp (algebraMap R (Localization.Away r)) =
      algebraMap R (Localization.Away a) :=
  IsLocalization.lift_comp _

private theorem awayLift_apply_algebraMap {r a : R} (hra : r ∣ a) (x : R) :
    awayLift hra (algebraMap R (Localization.Away r) x) =
      algebraMap R (Localization.Away a) x :=
  DFunLike.congr_fun (awayLift_comp hra) x

private theorem awayLift_comp_awayLift {r a b : R} (hra : r ∣ a) (hab : a ∣ b) :
    (awayLift hab).comp (awayLift hra) = awayLift (hra.trans hab) :=
  IsLocalization.ringHom_ext (Submonoid.powers r) <| by
    rw [RingHom.comp_assoc, awayLift_comp, awayLift_comp, awayLift_comp]

private theorem awayLift_id {r : R} (hr : r ∣ r) : awayLift hr = RingHom.id _ :=
  IsLocalization.ringHom_ext (Submonoid.powers r) <| by
    rw [awayLift_comp, RingHom.id_comp]

/-- The class of the base change `A ⊗[R] M` in the Picard group of `A` is the image of the
class of `M` under the map of Picard groups induced by the structure morphism. -/
private theorem pic_mk_baseChange (A : Type u) [CommRing A] [Algebra R A]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    Pic.mk A (A ⊗[R] M) = Pic.mapRingHom (algebraMap R A) (Pic.mk R M) := by
  rw [Pic.mapRingHom_algebraMap, Pic.mapAlgebra_apply]
  exact Pic.mk_eq_mk_iff.mpr
    ⟨AlgebraTensorModule.congr (LinearEquiv.refl A A) (Pic.mk.linearEquiv R M).symm⟩

/-- Freeness of the base change of an invertible module transfers along a ring map compatible
with the structure maps, via the map of Picard groups. -/
private theorem free_tensor_of_comp_eq {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →+* B) (hf : f.comp (algebraMap R A) = algebraMap R B)
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Invertible R M]
    (h : Module.Free A (A ⊗[R] M)) : Module.Free B (B ⊗[R] M) := by
  rw [← Pic.mk_eq_one_iff_free, pic_mk_baseChange, ← hf, ← Pic.mapRingHom_comp_mapRingHom,
    MonoidHom.comp_apply, ← pic_mk_baseChange, Pic.mk_eq_one_iff_free.mpr h, map_one]

/-- An invertible module which is free over the localization away from `r` is free over the
localization away from any multiple of `r`. -/
private theorem free_tensor_awayLocalization {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Invertible R M] {r a : R} (hra : r ∣ a)
    (hr : Module.Free (Localization.Away r) (LocalizedModule.Away r M)) :
    Module.Free (Localization.Away a) (Localization.Away a ⊗[R] M) := by
  have := hr
  have hbase : Localization.Away r ⊗[R] M ≃ₗ[Localization.Away r] LocalizedModule.Away r M :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M)).equiv
  exact free_tensor_of_comp_eq (awayLift hra) (awayLift_comp hra) (Module.Free.of_equiv hbase.symm)

end Localization

/-! ### Products of localizations -/

section Pi

/-- A family of linear equivalences `N i ≃ₗ[A i] A i` assembles into a linear equivalence
over the product ring. -/
private def piLinearEquivOfComponents {ι : Type*} (A : ι → Type*) [∀ i, CommRing (A i)]
    (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module (A i) (N i)]
    (e : ∀ i, N i ≃ₗ[A i] A i) :
    (∀ i, N i) ≃ₗ[∀ i, A i] (∀ i, A i) where
  toFun x i := e i (x i)
  invFun y i := (e i).symm (y i)
  left_inv x := funext fun i => (e i).symm_apply_apply (x i)
  right_inv y := funext fun i => (e i).apply_symm_apply (y i)
  map_add' x y := funext fun i => (e i).map_add (x i) (y i)
  map_smul' a x := funext fun i => (e i).map_smul (a i) (x i)

/-- A product of invertible modules, each free over its own factor, is free over the product
ring. -/
private theorem free_pi_of_forall_free {R : Type u} [CommRing R] {ι : Type u} [Finite ι]
    (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Invertible R M]
    (hfree : ∀ i, Module.Free (A i) (A i ⊗[R] M)) :
    Module.Free (∀ i, A i) ((∀ i, A i) ⊗[R] M) := by
  have : Fintype ι := Fintype.ofFinite ι
  have e : ∀ i, (A i ⊗[R] M) ≃ₗ[A i] A i := fun i =>
    (Module.Invertible.free_iff_linearEquiv.mp (hfree i)).some
  exact Module.Free.of_equiv
    ((TensorProduct.piLeftOfPiRing R A M).trans
      (piLinearEquivOfComponents A (fun i => A i ⊗[R] M) e)).symm

end Pi

/-! ### The faithfully flat algebra trivializing a countable family -/

section Witness

variable {R : Type u} [CommRing R] (s : ℕ → Finset R)

/-- A choice of one element of `s n` for every `n < m`. -/
private abbrev Choice (m : ℕ) : Type u := ∀ n : Fin m, {x : R // x ∈ s (n : ℕ)}

/-- The product of the elements selected by a choice. -/
private def choiceProd {m : ℕ} (f : Choice s m) : R := ∏ n, (f n : R)

/-- The restriction of a choice to a shorter initial segment. -/
private abbrev restrictChoice {m m' : ℕ} (h : m ≤ m') (f : Choice s m') : Choice s m :=
  fun n => f (Fin.castLE h n)

/-- The `m`-th stage of the system: the product, over all choices for the indices below `m`,
of the localizations away from the product of the selected elements. -/
private abbrev Stage (m : ℕ) : Type u := ∀ f : Choice s m, Localization.Away (choiceProd s f)

private theorem choiceProd_dvd {m m' : ℕ} (h : m ≤ m') (f : Choice s m') :
    choiceProd s (restrictChoice s h f) ∣ choiceProd s f := by
  classical
  rw [choiceProd, choiceProd, ← Finset.prod_image (f := fun n : Fin m' => ((f n : R)))
    (g := Fin.castLE h) (s := Finset.univ) ((Fin.castLE_injective h).injOn)]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

/-- The transition map from the `m`-th to the `m'`-th stage, given by the localization maps
along the divisibilities between the products of selected elements. -/
private noncomputable def stageMap {m m' : ℕ} (h : m ≤ m') : Stage s m →+* Stage s m' :=
  RingHom.pi fun f =>
    (awayLift (choiceProd_dvd s h f)).comp (Pi.evalRingHom _ (restrictChoice s h f))

private instance stageDirectedSystem :
    DirectedSystem (Stage s) (fun m m' h => (stageMap s h : Stage s m → Stage s m')) where
  map_self := by
    intro m x
    funext f
    exact DFunLike.congr_fun (awayLift_id (choiceProd_dvd s le_rfl f)) (x f)
  map_map := by
    intro k j i hij hjk x
    funext f
    exact DFunLike.congr_fun
      (awayLift_comp_awayLift (choiceProd_dvd s hij (restrictChoice s hjk f))
        (choiceProd_dvd s hjk f)) (x (restrictChoice s (hij.trans hjk) f))

private theorem stageMap_comp_algebraMap {m m' : ℕ} (h : m ≤ m') :
    (stageMap s h).comp (algebraMap R (Stage s m)) = algebraMap R (Stage s m') :=
  RingHom.ext fun x => funext fun f => awayLift_apply_algebraMap (choiceProd_dvd s h f) x

/-- The products of selected elements generate the unit ideal at every stage. -/
private theorem span_range_choiceProd (hs : ∀ n, Ideal.span (s n : Set R) = ⊤) (m : ℕ) :
    Ideal.span (Set.range (choiceProd s (m := m))) = ⊤ := by
  induction m with
  | zero =>
    have h1 : (choiceProd s (m := 0)) = fun _ => (1 : R) := by
      funext f; simp [choiceProd]
    rw [h1, Set.range_const, Ideal.span_singleton_one]
  | succ m ih =>
    refine top_le_iff.mp ?_
    have h1 : Ideal.span (Set.range (choiceProd s (m := m))) * Ideal.span (s m : Set R) = ⊤ := by
      rw [ih, hs m, Ideal.top_mul]
    have h2 : Ideal.span (Set.range (choiceProd s (m := m))) * Ideal.span (s m : Set R) ≤
        Ideal.span (Set.range (choiceProd s (m := m + 1))) := by
      rw [Ideal.span_mul_span]
      refine Ideal.span_mono ?_
      rintro x hx
      obtain ⟨a, ⟨g, rfl⟩, b, hb, rfl⟩ := Set.mem_mul.mp hx
      refine ⟨(Fin.snoc g ⟨b, hb⟩ : Choice s (m + 1)), ?_⟩
      rw [choiceProd, Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rfl
    exact h1 ▸ h2

/-- Every stage is faithfully flat over the base ring. -/
private theorem faithfullyFlat_stage (hs : ∀ n, Ideal.span (s n : Set R) = ⊤) (m : ℕ) :
    Module.FaithfullyFlat R (Stage s m) :=
  Module.FaithfullyFlat.pi_localizationAway (choiceProd s) (span_range_choiceProd s hs m) _

/-- An invertible module free over each `R_r`, `r ∈ s n`, becomes free over every stage
beyond `n`. -/
private theorem free_tensor_stage {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Invertible R M] {n m : ℕ} (hnm : n < m)
    (hfree : ∀ r ∈ s n, Module.Free (Localization.Away r) (LocalizedModule.Away r M)) :
    Module.Free (Stage s m) (Stage s m ⊗[R] M) := by
  refine free_pi_of_forall_free _ M fun f => ?_
  refine free_tensor_awayLocalization (r := (f ⟨n, hnm⟩ : R)) ?_ (hfree _ (f ⟨n, hnm⟩).2)
  exact Finset.dvd_prod_of_mem (fun i => (f i : R)) (Finset.mem_univ _)

/-- The colimit of the system of stages. -/
private abbrev Colim : Type u :=
  Ring.DirectLimit (Stage s) (fun m m' h => (stageMap s h : Stage s m → Stage s m'))

private noncomputable instance colimAlgebra : Algebra R (Colim s) :=
  ((Ring.DirectLimit.of (Stage s) (fun m m' h => (stageMap s h : Stage s m → Stage s m'))
    (Classical.arbitrary ℕ)).comp (algebraMap R (Stage s (Classical.arbitrary ℕ)))).toAlgebra

/-- The structure morphism of the colimit factors through every stage. -/
private theorem algebraMap_colim (m : ℕ) :
    algebraMap R (Colim s) =
      (Ring.DirectLimit.of (Stage s) (fun m m' h => (stageMap s h : Stage s m → Stage s m'))
        m).comp (algebraMap R (Stage s m)) := by
  have key : ∀ i j : ℕ, i ≤ j →
      (Ring.DirectLimit.of (Stage s) (fun m m' h => (stageMap s h : Stage s m → Stage s m'))
        j).comp (algebraMap R (Stage s j)) =
      (Ring.DirectLimit.of (Stage s) (fun m m' h => (stageMap s h : Stage s m → Stage s m'))
        i).comp (algebraMap R (Stage s i)) := by
    intro i j hij
    rw [← stageMap_comp_algebraMap s hij, ← RingHom.comp_assoc]
    exact congrArg (fun g : Stage s i →+* Colim s => g.comp (algebraMap R (Stage s i)))
      (RingHom.ext fun x => Ring.DirectLimit.of_f hij x)
  rw [show algebraMap R (Colim s) =
    (Ring.DirectLimit.of (Stage s) (fun m m' h => (stageMap s h : Stage s m → Stage s m'))
      (Classical.arbitrary ℕ)).comp (algebraMap R (Stage s (Classical.arbitrary ℕ))) from rfl,
    ← key _ _ (le_max_left (Classical.arbitrary ℕ) m), key _ _ (le_max_right _ m)]

/-- The colimit is faithfully flat over the base ring. -/
private theorem faithfullyFlat_colim (hs : ∀ n, Ideal.span (s n : Set R) = ⊤) :
    Module.FaithfullyFlat R (Colim s) := by
  rw [← RingHom.faithfullyFlat_algebraMap_iff]
  exact faithfullyFlat_directLimit_of_faithfullyFlat R (Stage s) (fun m m' h => stageMap s h)
    (fun i j h => stageMap_comp_algebraMap s h)
    (fun m => RingHom.faithfullyFlat_algebraMap_iff.mpr (faithfullyFlat_stage s hs m))

/-- Every member of the family becomes free over the colimit. -/
private theorem free_tensor_colim {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Invertible R M] (n : ℕ)
    (hfree : ∀ r ∈ s n, Module.Free (Localization.Away r) (LocalizedModule.Away r M)) :
    Module.Free (Colim s) (Colim s ⊗[R] M) := by
  refine free_tensor_of_comp_eq (Ring.DirectLimit.of (Stage s)
    (fun m m' h => (stageMap s h : Stage s m → Stage s m')) (n + 1))
    (algebraMap_colim s (n + 1)).symm (free_tensor_stage s (Nat.lt_succ_self n) hfree)

/-- The direct sum of the family becomes free over the colimit. -/
private theorem free_tensor_directSum (L : ℕ → Type u) [∀ n, AddCommGroup (L n)]
    [∀ n, Module R (L n)] (hinv : ∀ n, Module.Invertible R (L n))
    (hfree : ∀ n, ∀ r ∈ s n, Module.Free (Localization.Away r) (LocalizedModule.Away r (L n))) :
    Module.Free (Colim s) (Colim s ⊗[R] (⨁ n, L n)) := by
  have hn : ∀ n, Module.Free (Colim s) (Colim s ⊗[R] L n) := fun n =>
    have := hinv n
    free_tensor_colim s n (hfree n)
  have := hn
  exact Module.Free.of_equiv (TensorProduct.directSumRight R (Colim s) (Colim s) L).symm

end Witness

/-! ### The remark -/

/-- **Stacks 05VF.** A countable direct sum of rank one locally free modules is projective and
becomes free after a faithfully flat base change. -/
@[stacks 05VF "a countable direct sum of rank one locally free modules becomes free after a \
faithfully flat base change"]
theorem exists_faithfullyFlat_free_baseChange_directSum {R : Type u} [CommRing R]
    (L : ℕ → Type u) [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
    (hL : ∀ n, Module.IsFiniteLocallyFreeOfRank R (L n) 1) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Projective R (⨁ n, L n) ∧ Module.FaithfullyFlat R S ∧
        Module.Free S (S ⊗[R] (⨁ n, L n)) := by
  have hinv : ∀ n, Module.Invertible R (L n) := fun n =>
    Module.isFiniteLocallyFreeOfRank_one_iff_invertible.mp (hL n)
  have hcover : ∀ n, ∃ t : Finset R, Ideal.span (t : Set R) = ⊤ ∧
      ∀ r ∈ t, Module.Free (Localization.Away r) (LocalizedModule.Away r (L n)) := fun n =>
    have := hinv n
    Module.Invertible.exists_finset_free_localization R (L n)
  choose s hs hfree using hcover
  refine ⟨Colim s, inferInstance, inferInstance, ?_, faithfullyFlat_colim s hs,
    free_tensor_directSum s L hinv hfree⟩
  refine Module.Projective.directSum_iff.mpr fun n => ?_
  have := hinv n
  infer_instance

/-- **Stacks 05VF.** Being locally free does not descend along faithfully flat ring maps: a
countable direct sum of rank one locally free modules which is not locally free still becomes
free after a faithfully flat base change. -/
@[stacks 05VF "being locally free does not descend along a faithfully flat ring map: a countable \
direct sum of rank one locally free modules which is not locally free still becomes free after \
the faithfully flat base change built here. That such a direct sum exists is Stacks 05WL, which \
the source cites and which is not formalized, so failure of local freeness is a hypothesis here \
and not a conclusion"]
theorem exists_faithfullyFlat_free_baseChange_not_isLocallyFree {R : Type u} [CommRing R]
    (L : ℕ → Type u) [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
    (hL : ∀ n, Module.IsFiniteLocallyFreeOfRank R (L n) 1)
    (hM : ¬ Module.IsLocallyFree R (⨁ n, L n)) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Projective R (⨁ n, L n) ∧ Module.FaithfullyFlat R S ∧
        Module.Free S (S ⊗[R] (⨁ n, L n)) ∧ ¬ Module.IsLocallyFree R (⨁ n, L n) := by
  obtain ⟨S, hring, halg, hproj, hff, hfr⟩ :=
    exists_faithfullyFlat_free_baseChange_directSum L hL
  exact ⟨S, hring, halg, hproj, hff, hfr, hM⟩

end Stacks.Examples
