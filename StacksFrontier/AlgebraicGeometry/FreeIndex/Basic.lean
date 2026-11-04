module

public import StacksFrontier.AlgebraicGeometry.FreeIndex.Diagram
public import StacksFrontier.AlgebraicGeometry.Card09ZNResidue.Basic

/-!
# Tag 09ZM fails for a cofiltered index category in a larger universe

[Stacks, Tag 09ZM] says that in a *directed* inverse system of quasi-compact quasi-separated
schemes over a quasi-compact quasi-separated base, with affine transition morphisms, affineness of
the structure morphism descends from the limit to all sufficiently late stages.  This file shows
that the same statement over an arbitrary cofiltered index category in `Type (u+1)`, with schemes
in `Scheme.{u}` and no smallness or cofinality hypothesis on the index category, is false.

The witness is the system of punctured planes `Stacks.Refute09ZM.diagram`: a cofiltered category
in `Type (u+1)`, a diagram of quasi-compact quasi-separated schemes in `Scheme.{u}` with affine
transition morphisms, whose limit is the *empty* scheme.  The base is the terminal scheme, so the
structure morphism out of the limit is a morphism of affine schemes and therefore affine, while no
stage is affine, so no stage's structure morphism over an affine base can be.

## Main definitions

* `Stacks.Refute09ZM.StatementEventuallyAffine`: eventual affineness of the structure morphisms of
  a directed system with affine and finite transition morphisms.

## Main results

* `Stacks.Refute09ZM.not_card_09ZM`: the statement of Tag 09ZM over a cofiltered index category in
  `Type (u+1)` and schemes in `Scheme.{u}` is **false**.
* `Stacks.Refute09ZM.not_statement09ZM`: the proposition
  `Stacks.Card09ZNResidue.Statement09ZM.{u + 1, u}` is false.
* `Stacks.Refute09ZM.statement09ZN_of_statement09ZM_vacuous`: the implication
  `Stacks.Card09ZNResidue.statement09ZN_of_statement09ZM` has a false hypothesis at the universes
  `u + 1, u`.
* `Stacks.Refute09ZM.not_exists_isAffine_of_isLimit_free_index`: the analogue of [Stacks, Tag 01Z6]
  for a cofiltered index category in `Type (u+1)` is false.
* `Stacks.Refute09ZM.card_09ZM_hypotheses`: the counterexample satisfies every hypothesis of that
  statement, and its conclusion fails at every index.

## Implementation notes

The base is the terminal scheme `Spec (ULift ℤ)`, so the natural transformation to the constant
diagram, the morphism out of the limit, and the compatibility equation between them are all
unique, hence given by `CategoryTheory.IsTerminal.hom_ext`.

## References

* [The Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
* [The Stacks Project, Tag 06AC](https://stacks.math.columbia.edu/tag/06AC)
-/


@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe w u

namespace Stacks.Refute09ZM

open Stacks.LimitConeSmallness (base)

/-- The ground field of the counterexample: a field in `Type (u+1)` which is not `u`-small. -/
abbrev bigField : Type (u + 1) := Stacks.EmptyLimitCounterexample.bigField.{u}

/-- The index category of the counterexample: the finite subsets of `bigField` ordered by
inclusion, read contravariantly.  It is cofiltered, and its objects and morphisms live one
universe above the schemes. -/
abbrev Index : Type (u + 1) := (Finset bigField.{u})ᵒᵖ

/-- The counterexample diagram `diagram bigField`: the punctured planes over the stage rings of
`bigField`. -/
abbrev system : Index.{u} ⥤ Scheme.{u} := diagram bigField.{u}

/-- The base scheme `Spec (ULift ℤ)` is a terminal object of `Scheme`. -/
def isTerminal_base : IsTerminal base.{u} := specULiftZIsTerminal

/-- The structure morphisms of the system over the terminal base: the unique natural
transformation to the constant diagram. -/
def toBase : system.{u} ⟶ (Functor.const Index.{u}).obj base.{u} where
  app _ := isTerminal_base.from _
  naturality _ _ _ := isTerminal_base.hom_ext _ _

/-- The limit cone of the system, whose vertex is the empty scheme. -/
def limitCone : Cone system.{u} := emptyCone bigField.{u}

/-- `limitCone` is a limit cone. -/
def isLimitLimitCone : IsLimit limitCone.{u} :=
  isLimitEmptyCone _ Stacks.EmptyLimitCounterexample.not_small_bigField

/-- The vertex of `limitCone` is the empty scheme. -/
theorem limitCone_pt : limitCone.{u}.pt = (∅ : Scheme.{u}) := rfl

/-- The vertex of `limitCone` is empty. -/
instance isEmpty_limitCone_pt : IsEmpty limitCone.{u}.pt :=
  inferInstanceAs (IsEmpty (∅ : Scheme.{u}))

/-- The vertex of `limitCone` is an affine scheme. -/
instance isAffine_limitCone_pt : IsAffine limitCone.{u}.pt :=
  isAffine_of_isEmpty

/-- The unique morphism from the vertex of `limitCone` to the terminal base. -/
def limitToBase : limitCone.{u}.pt ⟶ base.{u} := isTerminal_base.from _

/-- **The morphism `limitToBase` out of the limit is affine.** -/
instance isAffineHom_limitToBase : IsAffineHom limitToBase.{u} :=
  isAffineHom_of_isAffine _

/-- The projections of `limitCone` followed by `toBase` agree with the constant natural
transformation induced by `limitToBase`. -/
theorem limitCone_fac :
    limitCone.{u}.π ≫ toBase.{u} = (Functor.const Index.{u}).map limitToBase.{u} :=
  NatTrans.ext (funext fun _ => isTerminal_base.hom_ext _ _)

/-- No stage's structure morphism `toBase.app i` over the terminal base is affine. -/
private theorem not_isAffineHom_toBase_app (i : Index.{u}) : ¬ IsAffineHom (toBase.{u}.app i) :=
  fun hi ↦ by
    have : IsAffine (((Functor.const Index.{u}).obj base.{u}).obj i) :=
      inferInstanceAs (IsAffine base.{u})
    exact not_isAffine_diagram_obj bigField.{u} i (isAffine_of_isAffineHom (toBase.{u}.app i))

/-- **Every hypothesis of the statement refuted by `not_card_09ZM` holds for the counterexample.**

The index category is cofiltered; every stage is quasi-compact and quasi-separated; every
transition morphism is affine; the cone is limiting; the morphism out of the limit is affine; and
it is compatible with the structure morphisms.  **And no stage's structure morphism is affine**,
so the conclusion fails at every index. -/
theorem card_09ZM_hypotheses :
    IsCofiltered Index.{u} ∧
      (∀ i : Index.{u}, CompactSpace (system.{u}.obj i)) ∧
      (∀ i : Index.{u}, QuasiSeparatedSpace (system.{u}.obj i)) ∧
      (∀ (i j : Index.{u}) (g : i ⟶ j), IsAffineHom (system.{u}.map g)) ∧
      Nonempty (IsLimit limitCone.{u}) ∧
      IsAffineHom limitToBase.{u} ∧
      limitCone.{u}.π ≫ toBase.{u} = (Functor.const Index.{u}).map limitToBase.{u} ∧
      ∀ i : Index.{u}, ¬ IsAffineHom (toBase.{u}.app i) := by
  exact ⟨inferInstance, fun _ => inferInstance, fun _ => inferInstance, fun _ _ _ =>
    inferInstance, ⟨isLimitLimitCone⟩, inferInstance, limitCone_fac,
    not_isAffineHom_toBase_app⟩

/-- **[Stacks, Tag 09ZM] is false over a cofiltered index category in `Type (u+1)`**: there are a
cofiltered category `I` in `Type (u+1)`, a quasi-compact quasi-separated scheme `S`, a diagram
`D : I ⥤ Scheme.{u}` of quasi-compact quasi-separated schemes with affine transition morphisms,
structure morphisms `t : D ⟶ (Functor.const I).obj S`, and a limit cone of `D` whose compatible
morphism to `S` is affine, such that there is no index `i` with `t.app j` affine for every
`j ⟶ i`. -/
theorem not_card_09ZM :
    ¬ ∀ {I : Type (u + 1)} [Category.{u + 1} I] [IsCofiltered I]
        {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
        (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
        (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ S)
        (_hf : c.π ≫ t = (Functor.const I).map f)
        [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
        [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)] [IsAffineHom f],
      ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsAffineHom (t.app j) := by
  intro h
  obtain ⟨i, hi⟩ := @h Index.{u} _ _ base.{u} _ _ system.{u} toBase.{u} limitCone.{u}
    isLimitLimitCone limitToBase.{u} limitCone_fac (fun _ => inferInstance)
    (fun _ => inferInstance) (fun _ => inferInstance) inferInstance
  exact not_isAffineHom_toBase_app i (hi (𝟙 i))

/-- **[Stacks, Tag 01Z6] is false once the index universe is freed from the scheme universe**:
there are a cofiltered category `I` in `Type (u+1)` and a diagram `D : I ⥤ Scheme.{u}` of
quasi-compact quasi-separated schemes with affine transition morphisms and a limit cone with
affine vertex, none of whose stages is affine.

Mathlib's `AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit` states Tag 01Z6 for an index
category in the scheme universe: `{I : Type u}` with `Category.{u} I` over `Scheme.{u}`. -/
theorem not_exists_isAffine_of_isLimit_free_index :
    ¬ ∀ {I : Type (u + 1)} [Category.{u + 1} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
        (c : Cone D) (_hc : IsLimit c)
        [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
        [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
        [IsAffine c.pt],
      ∃ i : I, IsAffine (D.obj i) := by
  intro h
  obtain ⟨i, hi⟩ := @h Index.{u} _ _ system.{u} limitCone.{u} isLimitLimitCone
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance) inferInstance
  exact not_isAffine_diagram_obj bigField.{u} i hi

/-- **`Stacks.Card09ZNResidue.Statement09ZM` is false at the universes `u + 1, u`.** -/
theorem not_statement09ZM : ¬ Stacks.Card09ZNResidue.Statement09ZM.{u + 1, u} :=
  not_card_09ZM.{u}

/-- **The implication `Stacks.Card09ZNResidue.statement09ZN_of_statement09ZM` is vacuous at the
universes `u + 1, u`**: `Stacks.Card09ZNResidue.Statement09ZM.{u + 1, u}` is false, and it implies
`Stacks.Card09ZNResidue.Statement09ZN.{u + 1, u}`. -/
theorem statement09ZN_of_statement09ZM_vacuous :
    ¬ Stacks.Card09ZNResidue.Statement09ZM.{u + 1, u} ∧
      (Stacks.Card09ZNResidue.Statement09ZM.{u + 1, u} →
        Stacks.Card09ZNResidue.Statement09ZN.{u + 1, u}) :=
  ⟨not_statement09ZM, Stacks.Card09ZNResidue.statement09ZN_of_statement09ZM⟩

section Residue

/-- **Eventual affineness of the structure morphisms**: for every directed system `F` of
quasi-compact quasi-separated schemes over a quasi-compact quasi-separated scheme `S`, with affine
and finite transition morphisms and structure morphisms `q` locally of finite type, and every
limit cone of `F` whose compatible morphism `f` to `S` is integral, the structure morphisms
`q.app (op i)` are affine for all sufficiently large `i`. -/
def StatementEventuallyAffine : Prop :=
  ∀ {I : Type w} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (F : Iᵒᵖ ⥤ Scheme.{u}) (q : F ⟶ (Functor.const Iᵒᵖ).obj S)
    (c : Cone F) (_hc : IsLimit c) (f : c.pt ⟶ S)
    (_hf : ∀ i, f = c.π.app (op i) ≫ q.app (op i))
    [IsIntegralHom f]
    [∀ i, CompactSpace (F.obj (op i))]
    [∀ i, QuasiSeparatedSpace (F.obj (op i))]
    (_haffine : ∀ {i j : I} (h : i ≤ j), IsAffineHom (F.map (homOfLE h).op))
    (_hfinite : ∀ {i j : I} (h : i ≤ j), IsFinite (F.map (homOfLE h).op))
    [∀ i, LocallyOfFiniteType (q.app (op i))],
    ∀ᶠ i in Filter.atTop, IsAffineHom (q.app (op i))

/-- **`StatementEventuallyAffine` implies `Stacks.Card09ZNResidue.Statement09ZN`**, at an arbitrary
pair of universes. -/
theorem statement09ZN_of_statementEventuallyAffine
    (h : StatementEventuallyAffine.{w, u}) : Stacks.Card09ZNResidue.Statement09ZN.{w, u} := by
  intro I _ _ _ S _ _ F q c hc f hf _ _ _ haffine hfinite _
  exact eventually_isFinite_of_isLimit_of_isIntegral_of_eventually_isAffineHom F q c hc f hf
    (fun h ↦ haffine h) (fun h ↦ hfinite h)
    (@h I _ _ _ S _ _ F q c hc f hf _ _ _ (fun h ↦ haffine h) (fun h ↦ hfinite h) _)

/-- **`Stacks.Card09ZNResidue.Statement09ZM` implies `StatementEventuallyAffine`**, at an arbitrary
pair of universes. -/
theorem statementEventuallyAffine_of_statement09ZM
    (h : Stacks.Card09ZNResidue.Statement09ZM.{w, u}) : StatementEventuallyAffine.{w, u} := by
  intro I _ _ _ S _ _ F q c hc f hf _ _ _ haffine _ _
  have hcpt : ∀ k : Iᵒᵖ, CompactSpace (F.obj k) := fun k ↦
    inferInstanceAs (CompactSpace ↥(F.obj (op k.unop)))
  have hqs : ∀ k : Iᵒᵖ, QuasiSeparatedSpace (F.obj k) := fun k ↦
    inferInstanceAs (QuasiSeparatedSpace ↥(F.obj (op k.unop)))
  have haff : ∀ {k l : Iᵒᵖ} (g : k ⟶ l), IsAffineHom (F.map g) := by
    intro k l g
    rw [show g = (homOfLE (leOfHom g.unop)).op from rfl]
    exact haffine _
  have hnat : c.π ≫ q = (Functor.const Iᵒᵖ).map f := by
    refine NatTrans.ext (funext fun k ↦ ?_)
    obtain ⟨i⟩ := k
    simpa using (hf i).symm
  exact Stacks.Tag09ZNAffineReduction.eventually_isAffineHom_of_exists F q
    (@h Iᵒᵖ _ _ S _ _ F q c hc f hnat hcpt hqs haff inferInstance)

/-- At the universes `u + 1, u`: `StatementEventuallyAffine` implies
`Stacks.Card09ZNResidue.Statement09ZN`, `Stacks.Card09ZNResidue.Statement09ZM` implies
`StatementEventuallyAffine`, and `Stacks.Card09ZNResidue.Statement09ZM` is false. -/
theorem card09ZN_route :
    (StatementEventuallyAffine.{u + 1, u} → Stacks.Card09ZNResidue.Statement09ZN.{u + 1, u}) ∧
      (Stacks.Card09ZNResidue.Statement09ZM.{u + 1, u} → StatementEventuallyAffine.{u + 1, u}) ∧
      ¬ Stacks.Card09ZNResidue.Statement09ZM.{u + 1, u} :=
  ⟨statement09ZN_of_statementEventuallyAffine, statementEventuallyAffine_of_statement09ZM,
    not_statement09ZM⟩

end Residue

end Stacks.Refute09ZM

end

end
