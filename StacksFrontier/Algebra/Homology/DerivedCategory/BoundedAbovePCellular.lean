module

public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes

/-!
# A bounded above complex with terms in `P` is `P`-cellular

Let `A` be an abelian category and `P` a class of objects of `A` containing a zero object, stable
under binary direct sums and such that every object is a quotient of an object of `P`. A complex
`K` vanishing in degrees above some `a` and with all terms in `P` is `P`-cellular in the sense of
`StacksDraft.UnboundedLeftDerivedFunctor.IsPCellular`: it is the colimit of a sequence `Q n` of
complexes vanishing above `n`, with terms in `P`, whose structure maps are isomorphisms on `H^i`
for `i ≤ n`.

For `a ≤ 0` the constant sequence on `K` does it. In general the sequence is the ladder of
resolutions of the canonical truncations `τ_{≤ n} K` of Stacks 06XX for `n` below `a`, and the
constant sequence on `K` from `a` on: the ladder maps into `K` through `τ_{≤ n} K ⟶ K`, which is
an isomorphism on `H^i` for `i ≤ n`, and a sequence which is constant from some index on has that
term as its colimit.

## Main results

* `StacksDraft.UnboundedLeftDerivedFunctor.isPCellular_of_isStrictlyLE_of_biprod_of_epi`: for
  `P` containing zero, stable under binary biproducts and covering every object by an
  epimorphism, a bounded above complex with terms in `P` is `P`-cellular. For a bound `a ≤ 0`
  and no hypothesis on `P` this is
  `StacksDraft.UnboundedLeftDerivedFunctor.isPCellular_of_isStrictlyLE`.

## References

* [Stacks Project, Tag 06XX](https://stacks.math.columbia.edu/tag/06XX)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public section

open CategoryTheory Limits

namespace StacksDraft.UnboundedLeftDerivedFunctor

universe v₁ u₁

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]


section Ladder

variable (K : CochainComplex A ℤ) (N : ℕ) (Q : ℕ → CochainComplex A ℤ)
  (f : ∀ n : ℕ, Q n ⟶ K.truncLE (n : ℤ)) (g : ∀ n : ℕ, Q n ⟶ Q (n + 1))

/-- The terms of the ladder, truncated at `N`: the ladder below `N`, and `K` from `N` on. -/
noncomputable def ladderObj (n : ℕ) : CochainComplex A ℤ := if n < N then Q n else K

variable {K N Q}

/-- Below `N` the truncated ladder is the ladder. -/
noncomputable def ladderObjIsoBelow {n : ℕ} (h : n < N) : ladderObj K N Q n ≅ Q n :=
  eqToIso (if_pos h)

/-- From `N` on the truncated ladder is `K`. -/
noncomputable def ladderObjIsoAbove {n : ℕ} (h : ¬ n < N) : ladderObj K N Q n ≅ K :=
  eqToIso (if_neg h)

/-- The transition maps of the truncated ladder. -/
noncomputable def ladderMap (n : ℕ) : ladderObj K N Q n ⟶ ladderObj K N Q (n + 1) :=
  if h₁ : n + 1 < N then
    (ladderObjIsoBelow (by omega : n < N)).hom ≫ g n ≫ (ladderObjIsoBelow h₁).inv
  else if h₂ : n < N then
    (ladderObjIsoBelow h₂).hom ≫ f n ≫ K.ιTruncLE (n : ℤ) ≫ (ladderObjIsoAbove h₁).inv
  else (ladderObjIsoAbove h₂).hom ≫ (ladderObjIsoAbove h₁).inv

/-- The maps of the truncated ladder into `K`. -/
noncomputable def ladderToObj (n : ℕ) : ladderObj K N Q n ⟶ K :=
  if h : n < N then (ladderObjIsoBelow h).hom ≫ f n ≫ K.ιTruncLE (n : ℤ)
  else (ladderObjIsoAbove h).hom

variable {f g}

/-- The maps `ladderToObj` of the truncated ladder into `K` commute with its transition maps
`ladderMap`. -/
lemma ladderMap_comp_ladderToObj
    (hladder : ∀ n : ℕ, g n ≫ f (n + 1) ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      f n ≫ K.ιTruncLE ((n : ℕ) : ℤ)) (n : ℕ) :
    ladderMap f g n ≫ ladderToObj (N := N) f (n + 1) = ladderToObj f n := by
  by_cases h₁ : n + 1 < N
  · have h₂ : n < N := by omega
    simp only [ladderMap, ladderToObj, dif_pos h₁, dif_pos h₂, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [hladder n]
  · by_cases h₂ : n < N
    · simp only [ladderMap, ladderToObj, dif_neg h₁, dif_pos h₂, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    · simp only [ladderMap, ladderToObj, dif_neg h₁, dif_neg h₂, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]

/-- The cocone of the truncated ladder with vertex `K`. -/
noncomputable def ladderCocone
    (hladder : ∀ n : ℕ, g n ≫ f (n + 1) ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      f n ≫ K.ιTruncLE ((n : ℕ) : ℤ)) :
    Cocone (Functor.ofSequence (ladderMap (N := N) f g)) where
  pt := K
  ι := NatTrans.ofSequence (F := Functor.ofSequence (ladderMap (N := N) f g))
    (G := (Functor.const ℕ).obj K) (fun n => ladderToObj f n) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ]
      exact (ladderMap_comp_ladderToObj (N := N) hladder n).trans (Category.comp_id _).symm)

/-- The components of `ladderCocone` are the maps `ladderToObj`. -/
@[simp]
lemma ladderCocone_ι_app
    (hladder : ∀ n : ℕ, g n ≫ f (n + 1) ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      f n ≫ K.ιTruncLE ((n : ℕ) : ℤ)) (n : ℕ) :
    (ladderCocone (N := N) hladder).ι.app n = ladderToObj f n := rfl

/-- From `N` on the components of `ladderCocone` are isomorphisms. -/
lemma isIso_ladderCocone_ι_app
    (hladder : ∀ n : ℕ, g n ≫ f (n + 1) ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      f n ≫ K.ιTruncLE ((n : ℕ) : ℤ)) {n : ℕ} (h : ¬ n < N) :
    IsIso ((ladderCocone (N := N) hladder).ι.app n) := by
  simp only [ladderCocone_ι_app, ladderToObj, dif_neg h]
  exact Iso.isIso_hom _

/-- The truncated ladder is constant from `N` on. -/
lemma isEventuallyConstantFrom_ladder
    (hladder : ∀ n : ℕ, g n ≫ f (n + 1) ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      f n ≫ K.ιTruncLE ((n : ℕ) : ℤ)) :
    (Functor.ofSequence (ladderMap (N := N) f g)).IsEventuallyConstantFrom N := by
  intro j φ
  have := isIso_ladderCocone_ι_app (N := N) hladder (not_lt.2 (leOfHom φ))
  have := isIso_ladderCocone_ι_app (N := N) hladder (lt_irrefl N)
  exact IsIso.of_isIso_fac_right ((ladderCocone (N := N) hladder).w φ)

omit g in
/-- If every `f n` is a quasi-isomorphism, then `ladderToObj f n` is an isomorphism on `H^i` for
`i ≤ n`. -/
lemma quasiIsoAt_ladderToObj (hf : ∀ n, QuasiIso (f n)) (n : ℕ) (i : ℤ) (hi : i ≤ (n : ℤ)) :
    QuasiIsoAt (ladderToObj (N := N) f n) i := by
  by_cases h : n < N
  · simp only [ladderToObj, dif_pos h]
    have := hf n
    have : QuasiIsoAt (K.ιTruncLE (n : ℤ)) i := CochainComplex.quasiIsoAt_ιTruncLE K _ _ hi
    infer_instance
  · simp only [ladderToObj, dif_neg h]
    infer_instance

end Ladder

/-- **A bounded above complex with terms in `P` is `P`-cellular.** For `P` containing a zero
object, stable under binary direct sums and covering every object, a complex vanishing in
degrees above `a` with all terms in `P` is the colimit of the ladder of resolutions of its
canonical truncations, cut off at `a` and continued by the complex itself. -/
public lemma isPCellular_of_isStrictlyLE_of_biprod_of_epi (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (K : CochainComplex A ℤ) (a : ℤ) [K.IsStrictlyLE a] (hK : ∀ i, P (K.X i)) :
    IsPCellular P K := by
  obtain ⟨Q, f, g, hf, hle, hQ, -, hladder⟩ := exists_sequence_quasiIso_truncLE P hsum hP K
  let N : ℕ := a.toNat
  let c := ladderCocone (N := N) hladder
  have : IsIso (c.ι.app N) := isIso_ladderCocone_ι_app (N := N) hladder (lt_irrefl N)
  have hc : IsColimit c :=
    (isEventuallyConstantFrom_ladder (N := N) hladder).isColimitOfIsIso c
  refine ⟨ladderObj K N Q, ladderMap f g, c, hc, Iso.refl _, fun n => ?_, fun n i => ?_,
    fun n i hi => ?_⟩
  · by_cases h : n < N
    · rw [ladderObj, if_pos h]
      exact hle n
    · rw [ladderObj, if_neg h]
      exact CochainComplex.isStrictlyLE_of_le K a n (by omega)
  · by_cases h : n < N
    · rw [ladderObj, if_pos h]
      exact hQ n i
    · rw [ladderObj, if_neg h]
      exact hK i
  · exact (quasiIsoAt_iff_comp_right (c.ι.app n) (Iso.refl c.pt).hom i).2
      (quasiIsoAt_ladderToObj (N := N) (f := f) hf n i hi)

end StacksDraft.UnboundedLeftDerivedFunctor
