module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.InverseLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim

/-!
# The Mittag-Leffler condition and the vanishing of the first derived inverse limit

An inverse system of abelian groups indexed by the natural numbers is Mittag-Leffler exactly when
its first derived inverse limit vanishes both for the system itself and for the countable direct
sum of copies of it. This is Emmanouil's criterion, and it turns a condition on the transition
maps into one on `R¹lim`. The Mittag-Leffler condition is moreover closed under short exact
extensions, which is what makes Mittag-Leffler systems a usable class of right-acyclic objects
for the inverse-limit functor.

## Main definitions

There are no new definitions. The Mittag-Leffler condition itself is Mathlib's
`CategoryTheory.Functor.IsMittagLeffler`, applied to the underlying system of sets.

## Main results

* `Rlim.isMittagLeffler_iff_isZero_rightDerivedLim_one_and_countable_coproduct`: Emmanouil's
  characterization of the Mittag-Leffler condition (Tag 0CQA).
* `isMittagLeffler_of_shortExact` (in `StacksFrontier.Algebra.Homology.InverseLimit`): the
  Mittag-Leffler condition is closed under short exact extensions of inverse systems of abelian
  groups. This file records that it realizes Stacks Tag 0CQB.

## Implementation notes

The countable direct sum is the coproduct indexed by `Discrete ℕ` in the functor category
`ℕᵒᵖ ⥤ Ab`, with no restriction on the universe of the abelian groups; concretely it is computed
by the finitely supported diagram, whence the finite-support bookkeeping in the proof. Vanishing
of the first derived limit is stated for every right derived functor of the inverse limit, which
makes the assertion independent of a chosen construction; it is converted into surjectivity of
`Rlim.delta` through the cokernel description
`Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor`.

Tag 0CQB is already proved in the inverse-limit library, where it is used to propagate the
Mittag-Leffler condition along the cycles-boundaries filtration of a tower of complexes; only the
tag registration is new here, so that no second provider of the same statement is created.

## References

* [Emmanouil]
* [Stacks Project, Tag 0CQA](https://stacks.math.columbia.edu/tag/0CQA)
* [Stacks Project, Tag 0CQB](https://stacks.math.columbia.edu/tag/0CQB)
-/

add_to_stacks 0CQB "In a short exact sequence of inverse systems of abelian groups indexed by the
  natural numbers, if the outer two systems are Mittag-Leffler, then the middle system is
  Mittag-Leffler." isMittagLeffler_of_shortExact


section

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace Rlim

universe u v w t

private abbrev finsuppDiagram {J : Type u} [Category.{w} J] (ι : Type t)
    (A : J ⥤ Ab.{max v t}) : J ⥤ Ab.{max v t} where
  obj j := AddCommGrpCat.of (ι →₀ A.obj j)
  map f := AddCommGrpCat.ofHom (Finsupp.mapRange.addMonoidHom (A.map f).hom)
  map_id j := by
    ext x i
    simp
  map_comp f g := by
    ext x i
    simp

private lemma finsuppDiagram_map_apply {J : Type u} [Category.{w} J]
    (ι : Type t) (A : J ⥤ Ab.{max v t}) {j k : J} (f : j ⟶ k)
    (x : ι →₀ A.obj j) (i : ι) :
    (finsuppDiagram ι A |>.map f) x i = A.map f (x i) := rfl

private def finsuppDiagramι {J : Type u} [Category.{w} J] (ι : Type t)
    (A : J ⥤ Ab.{max v t}) (i : ι) : A ⟶ finsuppDiagram ι A where
  app j := AddCommGrpCat.ofHom (Finsupp.singleAddHom i)
  naturality {j k} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change Finsupp.single i ((A.map f).hom x) =
      Finsupp.mapRange (A.map f).hom (map_zero _) (Finsupp.single i x)
    exact Finsupp.mapRange_single.symm

private def finsuppDiagramDesc {J : Type u} [Category.{w} J] (ι : Type t)
    {A B : J ⥤ Ab.{max v t}} (f : ι → (A ⟶ B)) : finsuppDiagram ι A ⟶ B where
  app j := AddCommGrpCat.ofHom (Finsupp.liftAddHom (fun i => (f i).app j |>.hom))
  naturality {j k} g := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro i x
    simp [finsuppDiagram, Finsupp.mapRange_single]

private lemma finsuppDiagramι_desc {J : Type u} [Category.{w} J] (ι : Type t)
    {A B : J ⥤ Ab.{max v t}} (f : ι → (A ⟶ B)) (i : ι) :
    finsuppDiagramι ι A i ≫ finsuppDiagramDesc ι f = f i := by
  apply NatTrans.ext
  funext j
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact Finsupp.liftAddHom_apply_single _ _ _

private lemma finsuppDiagram_hom_ext {J : Type u} [Category.{w} J] (ι : Type t)
    {A B : J ⥤ Ab.{max v t}} {f g : finsuppDiagram ι A ⟶ B}
    (h : ∀ i, finsuppDiagramι ι A i ≫ f = finsuppDiagramι ι A i ≫ g) : f = g := by
  apply NatTrans.ext
  funext j
  apply AddCommGrpCat.hom_ext
  apply Finsupp.addHom_ext
  intro i x
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.app j) (h i)) x

private def finsuppDiagramIsoCoproduct {J : Type u} [Category.{w} J] (ι : Type t)
    (A : J ⥤ Ab.{max v t}) : finsuppDiagram ι A ≅ ∐ (fun _ : Discrete ι => A) where
  hom := finsuppDiagramDesc ι (fun i => Sigma.ι (fun _ : Discrete ι => A) ⟨i⟩)
  inv := Sigma.desc (fun i => finsuppDiagramι ι A i.as)
  hom_inv_id := by
    apply finsuppDiagram_hom_ext ι
    intro i
    simp [← Category.assoc, finsuppDiagramι_desc]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro i
    simp [finsuppDiagramι_desc]

private lemma finsuppDiagram_isMittagLeffler {J : Type u} [Category.{w} J]
    (ι : Type t) (A : J ⥤ Ab.{max v t}) (hA : (A ⋙ forget Ab).IsMittagLeffler) :
    (finsuppDiagram ι A ⋙ forget Ab).IsMittagLeffler := by
  classical
  intro j
  obtain ⟨k, f, hf⟩ := hA j
  refine ⟨k, f, fun l g => ?_⟩
  rintro _ ⟨x, rfl⟩
  change ∃ y : ι →₀ A.obj l,
    Finsupp.mapRange (A.map g) (map_zero _) y =
      Finsupp.mapRange (A.map f) (map_zero _) x
  have hlift : ∀ x : A.obj k, ∃ y : A.obj l, A.map g y = A.map f x :=
    fun x => hf g ⟨x, rfl⟩
  induction x using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | @single_add i a x hi ha ih =>
    obtain ⟨b, hb⟩ := hlift a
    obtain ⟨y, hy⟩ := ih
    refine ⟨Finsupp.single i b + y, ?_⟩
    rw [Finsupp.mapRange_add (map_add (A.map g).hom),
      Finsupp.mapRange_add (map_add (A.map f).hom),
      Finsupp.mapRange_single, Finsupp.mapRange_single, hb, hy]

private abbrev transition (A : Rlim.InvSystemAb.{v}) {m n : ℕ} (h : m ≤ n) :
    A.obj (Opposite.op n) →+ A.obj (Opposite.op m) :=
  (A.map (homOfLE h).op).hom

private lemma transition_self (A : Rlim.InvSystemAb.{v}) (n : ℕ)
    (x : A.obj (Opposite.op n)) : transition A (le_refl n) x = x := by
  simp [transition]

private lemma transition_comp (A : Rlim.InvSystemAb.{v}) {l m n : ℕ}
    (h : l ≤ m) (h' : m ≤ n) (x : A.obj (Opposite.op n)) :
    transition A h (transition A h' x) = transition A (h.trans h') x := by
  change (A.map (homOfLE h').op ≫ A.map (homOfLE h).op) x = _
  rw [← A.map_comp]
  rfl

private lemma isMittagLeffler_iff_ranges (A : Rlim.InvSystemAb.{v}) :
    (A ⋙ forget Ab).IsMittagLeffler ↔
      ∀ m : ℕ, ∃ n : ℕ, ∃ h : m ≤ n, ∀ k : ℕ, ∀ h' : n ≤ k,
        Set.range (transition A h) ⊆ Set.range (transition A (h.trans h')) := by
  rw [Functor.isMittagLeffler_iff_subset_range_comp]
  constructor
  · intro h m
    obtain ⟨n, f, hf⟩ := h (Opposite.op m)
    refine ⟨n.unop, leOfHom f.unop, fun k h' => ?_⟩
    exact hf (homOfLE h').op
  · intro h m
    obtain ⟨n, hn, h⟩ := h m.unop
    refine ⟨Opposite.op n, (homOfLE hn).op, fun k g => ?_⟩
    exact h k.unop (leOfHom g.unop)

private lemma delta_surjective_equations (A : Rlim.InvSystemAb.{v})
    (h : Epi (Rlim.delta A)) (x : ∀ n : ℕ, A.obj (Opposite.op n)) :
    ∃ z : ∀ n : ℕ, A.obj (Opposite.op n), ∀ n,
      z n - transition A (Nat.le_succ n) (z (n + 1)) = x n := by
  let p : AddCommGrpCat.of (∀ n : ℕ, A.obj (Opposite.op n)) ⟶ Rlim.product A :=
    Pi.lift (fun n => AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ n))
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective _).mp h (p x)
  refine ⟨fun n => Pi.π (fun n : ℕ => A.obj (Opposite.op n)) n z, fun n => ?_⟩
  have hz' := congrArg (fun y => Pi.π (fun n : ℕ => A.obj (Opposite.op n)) n y) hz
  have hp : p ≫ Pi.π (fun n : ℕ => A.obj (Opposite.op n)) n =
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ n) := Pi.lift_comp_π _ _
  have hd : Rlim.delta A ≫ Pi.π (fun n : ℕ => A.obj (Opposite.op n)) n =
      Pi.π (fun n : ℕ => A.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ => A.obj (Opposite.op n)) (n + 1) ≫
          A.map (homOfLE (Nat.le_succ n)).op := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro y
    change (Pi.π (fun n : ℕ => A.obj (Opposite.op n)) n).hom
      (y - (Rlim.shift A).hom y) =
        (Pi.π (fun n : ℕ => A.obj (Opposite.op n)) n).hom y -
          (A.map (homOfLE (Nat.le_succ n)).op).hom
            ((Pi.π (fun n : ℕ => A.obj (Opposite.op n)) (n + 1)).hom y)
    erw [map_sub]
    congr 1
    exact ConcreteCategory.congr_hom (Pi.lift_comp_π
      (fun n => Pi.π (fun n : ℕ => A.obj (Opposite.op n)) (n + 1) ≫
        A.map (homOfLE (Nat.le_succ n)).op) n) y
  change ((Rlim.delta A ≫ Pi.π _ n) z) = ((p ≫ Pi.π _ n) x) at hz'
  rw [hd, hp] at hz'
  exact hz'

private lemma transition_eq_of_compatible (A : Rlim.InvSystemAb.{v})
    (z : ∀ n : ℕ, A.obj (Opposite.op n)) {m k : ℕ} (h : m ≤ k)
    (hz : ∀ n, m ≤ n → n < k →
      z n = transition A (Nat.le_succ n) (z (n + 1))) :
    z m = transition A h (z k) := by
  induction k, h using Nat.le_induction with
  | base => exact (transition_self A m (z m)).symm
  | succ k hmk ih =>
    rw [ih (fun n hn hn' => hz n hn (Nat.lt_succ_of_lt hn')),
      hz k hmk (Nat.lt_succ_self k), transition_comp]

private lemma isMittagLeffler_of_epi_delta_finsupp
    (A : Rlim.InvSystemAb.{v})
    (hδ : Epi (Rlim.delta (finsuppDiagram ℕ A))) :
    (A ⋙ forget Ab).IsMittagLeffler := by
  classical
  by_contra hA
  rw [isMittagLeffler_iff_ranges] at hA
  simp only [not_forall, not_exists] at hA
  obtain ⟨m, hm⟩ := hA
  have bad : ∀ n : ℕ, ∃ x : A.obj (Opposite.op n),
      ∀ hn : m ≤ n, ∃ k : ℕ, ∃ hk : n ≤ k,
        transition A hn x ∉ Set.range (transition A (hn.trans hk)) := by
    intro n
    by_cases hn : m ≤ n
    · obtain ⟨k, hk, hbad⟩ := hm n hn
      obtain ⟨a, ⟨x, rfl⟩, hx⟩ := Set.not_subset.mp hbad
      exact ⟨x, fun _ => ⟨k, hk, hx⟩⟩
    · exact ⟨0, fun h => (hn h).elim⟩
  choose x hx using bad
  obtain ⟨z, hz⟩ := delta_surjective_equations (finsuppDiagram ℕ A) hδ
    (fun n => Finsupp.single n (x n))
  have hcoord : ∀ n i : ℕ, z n i - transition A (Nat.le_succ n) (z (n + 1) i) =
      Finsupp.single n (x n) i := fun n i =>
    congrArg (fun t : ℕ →₀ A.obj (Opposite.op n) => t i) (hz n)
  have step : ∀ n i : ℕ, n ≠ i →
      z n i = transition A (Nat.le_succ n) (z (n + 1) i) := by
    intro n i hni
    apply sub_eq_zero.mp
    simpa [Finsupp.single_apply, hni, Ne.symm hni] using hcoord n i
  let i := max m ((z m).support.sup id + 1)
  have hmi : m ≤ i := le_max_left _ _
  have hzero : z m i = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hi
    have hb : i ≤ (z m).support.sup id := Finset.le_sup (f := id) hi
    have hi' : (z m).support.sup id + 1 ≤ i := le_max_right _ _
    omega
  obtain ⟨k, hik, hbad⟩ := hx i hmi
  have hik' : i < k := by
    by_contra hn
    have : k = i := by omega
    subst k
    exact hbad ⟨x i, rfl⟩
  have hbefore : z m i = transition A hmi (z i i) :=
    transition_eq_of_compatible A (fun n => z n i) hmi
      (fun n _ hni => step n i (ne_of_lt hni))
  have hafter : z (i + 1) i = transition A (Nat.succ_le_of_lt hik') (z k i) :=
    transition_eq_of_compatible A (fun n => z n i) (Nat.succ_le_of_lt hik')
      (fun n hn _ => step n i (by omega))
  have hmiddle := hcoord i i
  rw [Finsupp.single_eq_same, hafter, transition_comp] at hmiddle
  have h := congrArg (transition A hmi) hmiddle
  rw [map_sub, ← hbefore, hzero, zero_sub, transition_comp] at h
  apply hbad
  exact ⟨-(z k i), by simpa only [map_neg] using h⟩

noncomputable local instance proofHasDerivedCategoryAb : HasDerivedCategory Ab.{v} :=
  HasDerivedCategory.standard _

noncomputable local instance proofHasDerivedCategoryInvSystemAb :
    HasDerivedCategory Rlim.InvSystemAb.{v} :=
  HasDerivedCategory.standard _

noncomputable local instance proofLimAdditive :
    (lim : Rlim.InvSystemAb.{v} ⥤ Ab.{v}).Additive :=
  Functor.additive_of_preserves_binary_products _

private lemma isZero_homology_one_iff_epi_delta
    (RF : DerivedCategory Rlim.InvSystemAb.{v} ⥤ DerivedCategory Ab.{v})
    (α : (lim : Rlim.InvSystemAb.{v} ⥤ Ab.{v}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{v} (ComplexShape.up ℤ)))
    (A : Rlim.InvSystemAb.{v}) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{v} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{v} 0).obj A))) ↔
        Epi (Rlim.delta A) := by
  obtain ⟨e⟩ := Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor RF α hRF A
  exact e.isZero_iff.trans (Preadditive.epi_iff_isZero_cokernel _).symm

private lemma epi_delta_of_isMittagLeffler (A : Rlim.InvSystemAb.{v})
    (hA : (A ⋙ forget Ab).IsMittagLeffler) : Epi (Rlim.delta A) := by
  obtain ⟨RF, α, hRF, _, _, hML, _⟩ :=
    Rlim.lim_hasRightDerivedFunctor_and_computations.{v}
  exact (isZero_homology_one_iff_epi_delta RF α hRF A).mp (hML A hA)

/-- **Stacks 0CQA (Emmanouil).** An inverse system of abelian groups is Mittag--Leffler if and
only if the first derived inverse limit vanishes for it and for the countable direct sum of
copies of it. -/
@[stacks 0CQA]
public theorem isMittagLeffler_iff_isZero_rightDerivedLim_one_and_countable_coproduct
    (A : Rlim.InvSystemAb.{v}) :
    let F : Rlim.InvSystemAb.{v} ⥤ Ab.{v} := lim
    ∀ (RF : DerivedCategory Rlim.InvSystemAb.{v} ⥤ DerivedCategory Ab.{v})
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF),
      RF.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso Rlim.InvSystemAb.{v} (ComplexShape.up ℤ)) →
        ((A ⋙ forget Ab).IsMittagLeffler ↔
          (IsZero ((DerivedCategory.homologyFunctor Ab.{v} 1).obj
            (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{v} 0).obj A))) ∧
          IsZero ((DerivedCategory.homologyFunctor Ab.{v} 1).obj
            (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{v} 0).obj
              (∐ fun _ : Discrete ℕ => A)))))) := by
  intro F RF α hRF
  let e := finsuppDiagramIsoCoproduct ℕ A
  let eH := (DerivedCategory.homologyFunctor Ab.{v} 1).mapIso
    (RF.mapIso ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{v} 0).mapIso e))
  constructor
  · intro hA
    refine ⟨(isZero_homology_one_iff_epi_delta RF α hRF A).mpr
      (epi_delta_of_isMittagLeffler A hA), ?_⟩
    apply eH.isZero_iff.mp
    exact (isZero_homology_one_iff_epi_delta RF α hRF _).mpr
      (epi_delta_of_isMittagLeffler _ (finsuppDiagram_isMittagLeffler ℕ A hA))
  · intro h
    apply isMittagLeffler_of_epi_delta_finsupp A
    exact (isZero_homology_one_iff_epi_delta RF α hRF _).mp (eH.isZero_iff.mpr h.2)

end Rlim

end

end
