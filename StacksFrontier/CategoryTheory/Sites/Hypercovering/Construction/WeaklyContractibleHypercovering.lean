module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.DisjointUnions
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.FiniteDisjointUnions
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.FiniteConstruction
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Objects
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible

/-!
# Hypercoverings whose every term is a single weakly contractible object

Let `C` be a site with fibre products in which every object admits a one-element covering by a
weakly contractible object. Then every object `X` of `C` admits a hypercovering each of whose
terms is a one-element family on a weakly contractible object covering `X`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.exists_singleton_hypercovering_objects_in`: for a class
  `B` of objects supplying finite coverings, a hypercovering whose term in every degree is the
  one-element family on a finite disjoint union of objects of `B`.
* `Stacks.CategoryTheory.Hypercovering.exists_singleton_weaklyContractible_hypercovering`: the
  same with `B` the weakly contractible objects, so that every term is a single weakly
  contractible object covering the base.
* `Stacks.CategoryTheory.Hypercovering.exists_singleton_weaklyContractible_hypercovering_of_prop`:
  the variant carrying a further property of objects, such as affineness, along the
  construction.

## Implementation notes

The construction is the source's. A hypercovering which is degreewise a *finite* family of
objects of `B` is produced by `exists_finite_hypercovering` (Tag 094K), and the terms are then
replaced by their disjoint unions by `isHypercovering_whiskerLift` (Tag 0DB2), run on the
finitely indexed semi-representable objects over `X`. Of the three hypotheses of Tag 0DB2 two
are then automatic: finitely indexed families are closed under finite limits, and taking their
disjoint unions commutes with finite limits as soon as finite coproducts in `Over X` are van
Kampen, which is the instance hypothesis `FinitaryExtensive (Over X)`. The third, that taking
disjoint unions preserves coverings, is carried as the hypothesis `hunions`, as is the statement
that the disjoint union of finitely many objects of `B` is again in `B`; for the weakly
contractible objects of a site the latter is the usual "a product of surjections of sets is
surjective" argument.

Running the construction on the finitely indexed families rather than on all summable ones is
what makes it applicable to a site whose underlying category is not cocomplete, such as a big
pro-étale site: there the categorical coproduct of an infinite family of objects is not their
disjoint union, so the two hypotheses just discharged are false for the summable families.

That each term covers `X`, which is part of the source's conclusion and not of the definition of
a hypercovering, comes from the degree-zero clause: the summands of the degree-zero term cover
`X` and each of them maps into the term in degree `n` along the simplicial structure, so the
one-element family on that term generates a larger sieve. This is the only place where the
pretopology is required to be the one attached to a Grothendieck topology.

Both shapes are stated.
`Stacks.CategoryTheory.Hypercovering.exists_singleton_hypercovering_objects_in` and the two
Tag 09A1 statements take the disjoint unions of all summable semi-representable objects, under the
three hypotheses of Tag 0DB2 on them; the `...finiteDisjointUnions` forms of the same three names
take the disjoint unions of the finitely indexed ones only, which is what needs no cocompleteness.

## References

* [Stacks Project, Tag 09A1](https://stacks.math.columbia.edu/tag/09A1)
* [Stacks Project, Tag 094K](https://stacks.math.columbia.edu/tag/094K)
* [Stacks Project, Tag 0DB2](https://stacks.math.columbia.edu/tag/0DB2)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The converse of `isCoveringOver_terminal_of_hom_mem`: if a semi-representable object over
`X` covers the terminal one, its summands cover `X`. -/
theorem ofArrows_hom_mem_of_isCoveringOver_terminal (J : Pretopology C) {X : C}
    (Z : FormalCoproduct.{w} (Over X)) (hZ : IsCoveringOver J (terminal.from Z)) :
    Presieve.ofArrows (fun i : Z.I ↦ (Z.obj i).left) (fun i ↦ (Z.obj i).hom) ∈ J X := by
  let T : FormalCoproduct.{w} (Over X) := ⟨PUnit.{w + 1}, fun _ ↦ Over.mk (𝟙 X)⟩
  have hT : IsTerminal T := FormalCoproduct.isTerminalIncl (Over.mk (𝟙 X)) Over.mkIdTerminal
  let e : (⊤_ (FormalCoproduct.{w} (Over X))) ⟶ T := hT.from _
  have he : IsIso e := ⟨terminalIsTerminal.from _, terminal.hom_ext _ _, hT.hom_ext _ _⟩
  have h := hZ.comp_isIso J e
  have hg : terminal.from Z ≫ e =
      (⟨fun _ ↦ PUnit.unit, fun i ↦ Over.homMk (Z.obj i).hom (by simp [T])⟩ : Z ⟶ T) :=
    hT.hom_ext _ _
  rw [hg] at h
  have h2 := h PUnit.unit
  simp only [eqToHom_refl, Category.comp_id, Over.homMk_left] at h2
  rw [← ofArrows_reindex (Equiv.subtypeUnivEquiv fun _ ↦ rfl) (fun i : Z.I ↦ (Z.obj i).left)
    (fun i ↦ (Z.obj i).hom)]
  exact h2

/-- If the summands of a semi-representable object over `X` cover `X` and all map to a single
object `W` over `X`, then `W` alone covers `X`. -/
theorem singleton_mem_toPretopology_of_factorsThrough (T : GrothendieckTopology C) {X : C}
    (Z : FormalCoproduct.{w} (Over X))
    (hZ : IsCoveringOver T.toPretopology (terminal.from Z))
    (W : Over X) (g : ∀ i, Z.obj i ⟶ W) :
    Presieve.singleton W.hom ∈ T.toPretopology X := by
  have h := ofArrows_hom_mem_of_isCoveringOver_terminal T.toPretopology Z hZ
  rw [GrothendieckTopology.mem_toPretopology] at h ⊢
  refine T.superset_covering ?_ h
  rw [Sieve.generate_le_iff]
  rintro Y _ ⟨i⟩
  exact ⟨_, (g i).left, W.hom, Presieve.singleton_self _, Over.w (g i)⟩

omit [HasPullbacks C] in
/-- A one-element family of arrows generates the same presieve as the single arrow, at any
universe level for the index type. -/
theorem ofArrows_pUnit' {X Y : C} (h : Y ⟶ X) :
    Presieve.ofArrows (fun _ : PUnit.{w + 1} ↦ Y) (fun _ ↦ h) = Presieve.singleton h := by
  funext Z
  ext k
  constructor
  · rintro ⟨_⟩
    exact Presieve.singleton_self _
  · rintro ⟨⟩
    exact Presieve.ofArrows.mk PUnit.unit

/-- In a hypercovering whose terms have disjoint unions, the disjoint union of the degree `n` term
alone covers `X`. -/
private theorem singleton_mem_toPretopology_of_isHypercovering (T : GrothendieckTopology C)
    {X : C} (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hK : IsHypercovering T.toPretopology K) (n : ℕ)
    [HasCoproduct (K.obj (op ⦋n⦌)).obj] :
    Presieve.singleton (∐ (K.obj (op ⦋n⦌)).obj : Over X).hom ∈ T.toPretopology X := by
  refine singleton_mem_toPretopology_of_factorsThrough T (K.obj (op ⦋0⦌)) hK.1 _ (fun i ↦ ?_)
  let F := K.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
  exact F.φ i ≫ Sigma.ι (K.obj (op ⦋n⦌)).obj (F.f i)

/-- An object with a one-element covering by an object of `B` has a finite covering by objects
of `B`. -/
private theorem exists_finite_cover_of_singleton (J : Pretopology C) (B : Set C)
    (h : ∀ Y : C, ∃ (V : C) (f : V ⟶ Y), V ∈ B ∧ Presieve.singleton f ∈ J Y) (Y : C) :
    ∃ (I : Type w) (V : I → C) (f : ∀ i, V i ⟶ Y),
      Finite I ∧ (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J Y := by
  obtain ⟨V, f, hV, hf⟩ := h Y
  exact ⟨PUnit.{w + 1}, fun _ ↦ V, fun _ ↦ f, inferInstance, fun _ ↦ hV,
    (ofArrows_pUnit'.{w} f).symm ▸ hf⟩

/-- Run a construction for the objects of `B := {V | V ∈ P ∧ weakly contractible}` on a
one-element covering by objects of `B`, and split the membership in `B`. -/
private theorem exists_singleton_of_prop (T : GrothendieckTopology C) (P : Set C) (X : C)
    (H : (∀ Y : C, ∃ (I : Type w) (V : I → C) (f : ∀ i, V i ⟶ Y), Finite I ∧
        (∀ i, V i ∈ {V : C | V ∈ P ∧ T.IsWeaklyContractible V}) ∧
          Presieve.ofArrows V f ∈ T.toPretopology Y) →
      ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
        IsHypercovering T.toPretopology K ∧
          ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
            (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
              ((K.obj (op ⦋n⦌)).obj i).left ∈ {V : C | V ∈ P ∧ T.IsWeaklyContractible V} ∧
              Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈ T.toPretopology X)
    (exists_singleton_cover : ∀ Y : C, ∃ (V : C) (f : V ⟶ Y),
      V ∈ P ∧ T.IsWeaklyContractible V ∧ Presieve.singleton f ∈ T.toPretopology Y) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering T.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            ((K.obj (op ⦋n⦌)).obj i).left ∈ P ∧
            T.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈ T.toPretopology X := by
  obtain ⟨K, hK, hterm⟩ := H (exists_finite_cover_of_singleton T.toPretopology _ fun Y ↦
    let ⟨V, f, hVP, hV, hf⟩ := exists_singleton_cover Y; ⟨V, f, ⟨hVP, hV⟩, hf⟩)
  exact ⟨K, hK, fun n ↦ (hterm n).imp fun _ ⟨hi, hB, hcov⟩ ↦ ⟨hi, hB.1, hB.2, hcov⟩⟩

section Construction

variable (T : GrothendieckTopology C) (B : Set C) (X : C)
  [HasFiniteCoproducts (Over X)]
  [ObjectProperty.IsClosedUnderFiniteLimits
    (fun U : FormalCoproduct.{w} (Over X) ↦ HasCoproduct U.obj)]
  [PreservesFiniteLimits (takeUnions.{w, v, max u v} (C := Over X))]

/-- The hypothesis of Tag 0DB2 that taking disjoint unions degreewise preserves coverings. -/
abbrev TakeUnionsPreservesCoverings : Prop :=
  ∀ ⦃U V : SummableFormalCoproduct.{w} (Over X)⦄ (f : U ⟶ V),
    IsCoveringOver T.toPretopology ((summableInclusion (C := Over X)).map f) →
      IsCoveringOver T.toPretopology ((takeUnions (C := Over X)).map f)

/-- The hypothesis that a finite disjoint union of objects of `B` over `X` lies again in `B`. -/
abbrev SumMem : Prop :=
  ∀ (A : FormalCoproduct.{w} (Over X)) [Finite A.I] [HasCoproduct A.obj],
    (∀ k, (A.obj k).left ∈ B) → ((∐ A.obj : Over X)).left ∈ B

/-- The second hypothesis of Tag 094K: a finite covering by objects of `B` stays covering after
one further morphism out of an object of `B` is adjoined. -/
abbrev CoverOfAdjoin : Prop :=
  ∀ {Y : C} {I : Type w} (V : I → C) (f : ∀ i, V i ⟶ Y),
    Finite I → (∀ i, V i ∈ B) → Presieve.ofArrows V f ∈ T.toPretopology Y →
    ∀ (W : C) (g : W ⟶ Y), W ∈ B →
      Presieve.ofArrows
        (fun i : Sum I PUnit.{w + 1} ↦ match i with | Sum.inl i => V i | Sum.inr _ => W)
        (fun i : Sum I PUnit.{w + 1} ↦ match i with | Sum.inl i => f i | Sum.inr _ => g)
          ∈ T.toPretopology Y

omit [HasFiniteCoproducts (Over X)] in
/-- In the pretopology of a Grothendieck topology a covering family stays covering after any
further morphism is adjoined, because the sieve it generates only grows. -/
theorem coverOfAdjoin_toPretopology : CoverOfAdjoin.{w} T B := by
  intro Y I V f _ _ hcov W g _
  rw [GrothendieckTopology.mem_toPretopology] at hcov ⊢
  refine T.superset_covering ?_ hcov
  rw [Sieve.generate_le_iff]
  rintro Z _ ⟨i⟩
  exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (Sum.inl i))

/-- **The construction behind Stacks Project, Tag 09A1.** If a class `B` of objects supplies a
finite covering of every object, if such a covering stays covering after one further morphism
out of an object of `B` is adjoined, and if disjoint unions of semi-representable objects over
`X` behave as in Tag 0DB2 and carry `B` into itself, then `X` has a hypercovering whose term in
every degree is the one-element family on an object of `B` covering `X`. -/
theorem exists_singleton_hypercovering_objects_in
    (hunions : TakeUnionsPreservesCoverings.{w} T X)
    (sum_mem : SumMem.{w} B X)
    (exists_finite_cover : ∀ Y : C, ∃ (I : Type w) (V : I → C) (f : ∀ i, V i ⟶ Y),
      Finite I ∧ (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ T.toPretopology Y) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering T.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            ((K.obj (op ⦋n⦌)).obj i).left ∈ B ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈ T.toPretopology X := by
  classical
  obtain ⟨K, hK, hfin⟩ :=
    exists_finite_hypercovering T.toPretopology B exists_finite_cover
      (coverOfAdjoin_toPretopology T B) X
  have hsum : ∀ n, HasCoproduct (K.obj n).obj := by
    intro n
    have : Finite (K.obj n).I := (hfin n.unop.len).1
    infer_instance
  refine ⟨takeUnionsSimplicial K hsum,
    isHypercovering_takeUnionsSimplicial T.toPretopology hunions K hsum hK, ?_⟩
  intro n
  have : Finite (K.obj (op ⦋n⦌)).I := (hfin n).1
  refine ⟨PUnit.unit, fun j ↦ Subsingleton.elim (α := PUnit.{w + 1}) j PUnit.unit, ?_, ?_⟩
  · change ((∐ (K.obj (op ⦋n⦌)).obj : Over X)).left ∈ B
    exact sum_mem (K.obj (op ⦋n⦌)) (hfin n).2
  · exact singleton_mem_toPretopology_of_isHypercovering T K hK n

/-- **Stacks Project, Tag 09A1 (1).** On a site with fibre products in which every object has a
one-element covering by a weakly contractible object, every object `X` admits a hypercovering
each of whose terms is a single weakly contractible object covering `X`.

The disjoint unions taken degreewise are governed by the hypotheses of Tag 0DB2 and by the fact
that a finite disjoint union of weakly contractible objects is weakly contractible. -/
theorem exists_singleton_weaklyContractible_hypercovering
    (hunions : TakeUnionsPreservesCoverings.{w} T X)
    (sum_weaklyContractible : SumMem.{w} {V : C | T.IsWeaklyContractible V} X)
    (exists_singleton_cover : ∀ Y : C, ∃ (V : C) (f : V ⟶ Y),
      T.IsWeaklyContractible V ∧ Presieve.singleton f ∈ T.toPretopology Y) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering T.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            T.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈ T.toPretopology X :=
  exists_singleton_hypercovering_objects_in T _ X hunions sum_weaklyContractible
    (exists_finite_cover_of_singleton T.toPretopology _ exists_singleton_cover)

/-- **Stacks Project, Tag 09A1 (2).** The same construction run with a further property `P` of
objects stable under the disjoint unions taken, such as affineness on the site of quasi-compact
and quasi-separated objects: every object `X` admits a hypercovering each of whose terms is a
single object satisfying `P`, weakly contractible, and covering `X`. -/
theorem exists_singleton_weaklyContractible_hypercovering_of_prop (P : Set C)
    (hunions : TakeUnionsPreservesCoverings.{w} T X)
    (sum_mem : SumMem.{w} {V : C | V ∈ P ∧ T.IsWeaklyContractible V} X)
    (exists_singleton_cover : ∀ Y : C, ∃ (V : C) (f : V ⟶ Y),
      V ∈ P ∧ T.IsWeaklyContractible V ∧ Presieve.singleton f ∈ T.toPretopology Y) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering T.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            ((K.obj (op ⦋n⦌)).obj i).left ∈ P ∧
            T.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈ T.toPretopology X := by
  exact exists_singleton_of_prop T P X
    (exists_singleton_hypercovering_objects_in T _ X hunions sum_mem) exists_singleton_cover

end Construction

section ConstructionFin

variable (T : GrothendieckTopology C) (B : Set C) (X : C) [FinitaryExtensive (Over X)]

/-- The hypothesis of Tag 0DB2 that taking finite disjoint unions degreewise preserves
coverings. -/
abbrev TakeUnionsFinPreservesCoverings : Prop :=
  ∀ ⦃U V : FiniteFormalCoproduct.{w} (Over X)⦄ (f : U ⟶ V),
    IsCoveringOver T.toPretopology
        ((ObjectProperty.ι (fun A : FormalCoproduct.{w} (Over X) ↦ Finite A.I)).map f) →
      IsCoveringOver T.toPretopology ((takeUnionsFin (C := Over X)).map f)

/-- **The hypothesis of Tag 0DB2 on coverings, from the one fact about the site it needs.** If
the summands of a finite disjoint union of objects over `X` cover it, then taking finite disjoint
unions turns a covering morphism of semi-representable objects into a covering one: the single
morphism of disjoint unions is covering because the composites of the summand inclusions of the
source with it factor through the summands of the target, which cover it. -/
theorem takeUnionsFinPreservesCoverings_of_ofArrows_sigmaι
    (hcofan : ∀ {I : Type w} [Finite I] (A : I → Over X),
      Sieve.ofArrows (fun i ↦ (A i).left) (fun i ↦ (Sigma.ι A i).left) ∈
        T ((∐ A : Over X)).left) :
    TakeUnionsFinPreservesCoverings.{w} T X := by
  intro V W f hf
  have hV : Finite V.obj.I := V.property
  have hW : Finite W.obj.I := W.property
  have key : Sieve.generate (Presieve.singleton
      ((Sigma.map' f.hom.f f.hom.φ : (∐ V.obj.obj : Over X) ⟶ ∐ W.obj.obj).left)) ∈
      T ((∐ W.obj.obj : Over X)).left := by
    refine T.superset_covering ?_ (T.bindOfArrows (hcofan W.obj.obj) (fun j ↦ hf j))
    rw [Sieve.generate_le_iff]
    rintro Y a ⟨j, g, ⟨i⟩⟩
    obtain ⟨i, rfl⟩ := i
    refine ⟨_, (Sigma.ι V.obj.obj i).left, _, Presieve.singleton_self _, ?_⟩
    simpa only [eqToHom_refl, Category.comp_id, Over.comp_left, ObjectProperty.ι_obj,
      ObjectProperty.ι_map] using
      congrArg Over.Hom.left (Sigma.ι_comp_map' f.hom.f f.hom.φ i)
  have hVu : Unique ((takeUnionsFin (C := Over X)).obj V).I := by
    change Unique PUnit.{w + 1}
    infer_instance
  have hWu : Unique ((takeUnionsFin (C := Over X)).obj W).I := by
    change Unique PUnit.{w + 1}
    infer_instance
  intro j
  have : Unique { i : ((takeUnionsFin (C := Over X)).obj V).I //
      ((takeUnionsFin (C := Over X)).map f).f i = j } :=
    ⟨⟨default, Subsingleton.elim _ _⟩, fun i ↦ Subtype.ext (Subsingleton.elim _ _)⟩
  have harrow : (fun i : { i : ((takeUnionsFin (C := Over X)).obj V).I //
        ((takeUnionsFin (C := Over X)).map f).f i = j } ↦
      (((takeUnionsFin (C := Over X)).map f).φ i.1).left ≫
        eqToHom (congrArg (fun k ↦ (((takeUnionsFin (C := Over X)).obj W).obj k).left) i.2)) =
      fun _ ↦ (Sigma.map' f.hom.f f.hom.φ : (∐ V.obj.obj : Over X) ⟶ ∐ W.obj.obj).left :=
    funext fun i ↦ Category.comp_id _
  rw [harrow, GrothendieckTopology.mem_toPretopology]
  refine T.superset_covering (fun Y a ha ↦ ?_) key
  obtain ⟨_, g, _, ⟨⟩, hcomp⟩ := ha
  exact ⟨_, g, _, Presieve.ofArrows.mk default, hcomp⟩

/-- The hypothesis that a finite disjoint union of objects of `B` over `X` lies again in `B`. -/
abbrev SumMemFin : Prop :=
  ∀ (A : FormalCoproduct.{w} (Over X)) [Finite A.I],
    (∀ k, (A.obj k).left ∈ B) → ((∐ A.obj : Over X)).left ∈ B

/-- **The construction behind Stacks Project, Tag 09A1.** If a class `B` of objects supplies a
finite covering of every object, if such a covering stays covering after one further morphism
out of an object of `B` is adjoined, and if disjoint unions of semi-representable objects over
`X` behave as in Tag 0DB2 and carry `B` into itself, then `X` has a hypercovering whose term in
every degree is the one-element family on an object of `B` covering `X`. -/
theorem exists_singleton_hypercovering_objects_in_finiteDisjointUnions
    (hunions : TakeUnionsFinPreservesCoverings.{w} T X)
    (sum_mem : SumMemFin.{w} B X)
    (exists_finite_cover : ∀ Y : C, ∃ (I : Type w) (V : I → C) (f : ∀ i, V i ⟶ Y),
      Finite I ∧ (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ T.toPretopology Y) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering T.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            ((K.obj (op ⦋n⦌)).obj i).left ∈ B ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈ T.toPretopology X := by
  classical
  obtain ⟨K, hK, hfin⟩ :=
    exists_finite_hypercovering T.toPretopology B exists_finite_cover
      (coverOfAdjoin_toPretopology T B) X
  have hsum : ∀ n, Finite (K.obj n).I := fun n ↦ (hfin n.unop.len).1
  refine ⟨((SimplicialObject.whiskering _ _).obj (takeUnionsFin (C := Over X))).obj
      (ObjectProperty.lift (fun A : FormalCoproduct.{w} (Over X) ↦ Finite A.I) K hsum),
    isHypercovering_whiskerLift T.toPretopology _ (takeUnionsFin (C := Over X)) hunions K hsum hK,
    ?_⟩
  intro n
  have : Finite (K.obj (op ⦋n⦌)).I := (hfin n).1
  refine ⟨PUnit.unit, fun j ↦ Subsingleton.elim (α := PUnit.{w + 1}) j PUnit.unit, ?_, ?_⟩
  · change ((∐ (K.obj (op ⦋n⦌)).obj : Over X)).left ∈ B
    exact sum_mem (K.obj (op ⦋n⦌)) (hfin n).2
  · exact singleton_mem_toPretopology_of_isHypercovering T K hK n

/-- **Stacks Project, Tag 09A1 (1).** On a site with fibre products in which every object has a
one-element covering by a weakly contractible object, every object `X` admits a hypercovering
each of whose terms is a single weakly contractible object covering `X`.

The disjoint unions taken degreewise are governed by the hypotheses of Tag 0DB2 and by the fact
that a finite disjoint union of weakly contractible objects is weakly contractible. -/
@[stacks 09A1 "(1), for a general site: the one-element weakly contractible covering is the \
hypothesis exists_singleton_cover (Tag 0F4P), and hunions is the remaining hypothesis of the \
library's Tag 0DB2, propagated"]
theorem exists_singleton_weaklyContractible_hypercovering_finiteDisjointUnions
    (hunions : TakeUnionsFinPreservesCoverings.{w} T X)
    (sum_weaklyContractible : SumMemFin.{w} {V : C | T.IsWeaklyContractible V} X)
    (exists_singleton_cover : ∀ Y : C, ∃ (V : C) (f : V ⟶ Y),
      T.IsWeaklyContractible V ∧ Presieve.singleton f ∈ T.toPretopology Y) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering T.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            T.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈ T.toPretopology X :=
  exists_singleton_hypercovering_objects_in_finiteDisjointUnions T _ X hunions
    sum_weaklyContractible
    (exists_finite_cover_of_singleton T.toPretopology _ exists_singleton_cover)

/-- **Stacks Project, Tag 09A1 (2).** The same construction run with a further property `P` of
objects stable under the disjoint unions taken, such as affineness on the site of quasi-compact
and quasi-separated objects: every object `X` admits a hypercovering each of whose terms is a
single object satisfying `P`, weakly contractible, and covering `X`. -/
@[stacks 09A1 "(2), with the object property P as a parameter: the source states it for \
affineness on the quasi-compact quasi-separated pro-etale site, which is constructed in \
StacksFrontier/AlgebraicGeometry/ProEtale/Site/Qcqs.lean, and (2) itself is proved at a chosen big \
pro-etale site as \
AlgebraicGeometry.ProEtale.exists_singleton_affine_weaklyContractible_hypercovering. That \
instantiation runs exists_singleton_hypercovering_objects_in_finiteDisjointUnions \
rather than this lemma, because the \
weak contractibility carried here is that of the site being worked in, while the source's — and \
the library statement's — is that of the ambient pro-etale site. Instantiating this lemma at the \
big site with P := affine would be vacuous, since a non-quasi-compact object has no one-element \
affine cover. Same carried hypotheses as (1)"]
theorem exists_singleton_weaklyContractible_hypercovering_of_prop_finiteDisjointUnions (P : Set C)
    (hunions : TakeUnionsFinPreservesCoverings.{w} T X)
    (sum_mem : SumMemFin.{w} {V : C | V ∈ P ∧ T.IsWeaklyContractible V} X)
    (exists_singleton_cover : ∀ Y : C, ∃ (V : C) (f : V ⟶ Y),
      V ∈ P ∧ T.IsWeaklyContractible V ∧ Presieve.singleton f ∈ T.toPretopology Y) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering T.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            ((K.obj (op ⦋n⦌)).obj i).left ∈ P ∧
            T.IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈ T.toPretopology X := by
  exact exists_singleton_of_prop T P X
    (exists_singleton_hypercovering_objects_in_finiteDisjointUnions T _ X hunions sum_mem)
    exists_singleton_cover

end ConstructionFin

end Stacks.CategoryTheory.Hypercovering

end
