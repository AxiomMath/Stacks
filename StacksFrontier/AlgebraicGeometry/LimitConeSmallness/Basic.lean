module

public import StacksFrontier.AlgebraicGeometry.LimitIndexUniverseEventualFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.EventualFinitenessUniverse.Basic
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.SetTheory.Ordinal.Family

/-!
# A limit cone does not force the index of an inverse system to be initially small

Tag 09ZN is stated for an index type whose universe is independent of the scheme universe, and
the only proof known in this repository
(`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall`)
carries exactly one hypothesis the
source statement does not: `CategoryTheory.InitiallySmall.{u} Iᵒᵖ`, a `u`-small cofinal set of
indices.  The obvious hope is that the hypothesis is redundant *because the tag hypothesises a
limit cone*: the large systems that visibly violate initial smallness tend to have no limit at
all, as `StacksFrontier/AlgebraicGeometry/LimitConeBound/Basic.lean` shows for one of them, so
one might hope that a limit cone, finite transition morphisms and quasi-compact
quasi-separated stages together force a `u`-small cofinal part of the index.

**They do not, and the refutation is as cheap as possible.**  Take the *constant* system with
value a fixed affine base, indexed by the opposite of the ordinals of the scheme universe.  Every
transition morphism is an identity, hence finite; every stage is the base, hence quasi-compact
and quasi-separated; the structure morphisms are identities, hence locally of finite type; the
morphism from the limit is an identity, hence integral; the identity cone *is* a limit cone,
because the opposite of a nonempty directed preorder is connected; and the conclusion of Tag 09ZN
holds, every structure morphism being finite.  The ordinals of `Type u` have no `u`-small cofinal
subset, so the index is not initially small.  That is
`exists_limitCone_and_not_initiallySmall`: the whole hypothesis bundle of Tag 09ZN *and* its
conclusion are compatible with the failure of `InitiallySmall.{u} Iᵒᵖ`.

So initial smallness of the index is not derivable from the tag's hypotheses, and no amount of
work on the limit cone will make it so.  A proof of Tag 09ZN at a free index universe must use a
condition which constant systems satisfy, and the hypothesis actually used by the known proof is
not one.

## The weaker hypothesis that does the same work

What the known proof really needs is not that the *index* has a small cofinal part, but that the
*given cone* is already a limit of a small part of the system.  That is strictly weaker, and it
is what `eventually_isFinite_of_isLimit_of_isIntegral_of_smallLimitingSubsystem` assumes: a
`u`-small nonempty directed subset `J` of the index such that the restriction of the given cone
along `J` is a limit cone of the restricted system.

Both halves of "strictly weaker" are checked here.  Initial smallness supplies the new hypothesis
(`exists_smallLimitingSubsystem_of_initiallySmall`): a `u`-small cofinal set may be replaced by a
`u`-small *directed* cofinal set (`exists_small_directed_cofinal`, where cofinality itself is what
produces the directedness), whose inclusion is then an initial functor
(`initial_op_subsetInclusion`), along which a limit cone restricts to a limit cone.  So the
reduction subsumes `..._of_initiallySmall`.  And it does not reverse: the constant
system above satisfies the new hypothesis with `J` a singleton
(`ordIsLimit_whiskerSingleton`) while its index has no `u`-small cofinal set at all.  So the
reduction proves Tag 09ZN in cases where `..._of_initiallySmall` provably cannot
apply.

Note that the reduction does not even assume that the given cone is a limit cone of the *whole*
system: being a limit of a small part of it is enough, and implies the rest.

## What remains open

Whether the hypothesis of a small limiting subsystem is derivable from the tag's hypotheses is
open, and it is the precise residue of Tag 09ZN at a free index universe.  This file settles
only that the stronger hypothesis — initial smallness of the index — is *not* derivable.
Nothing here bears on the truth of Tag 09ZN: the witness system satisfies the tag's conclusion.

## Main results

* `exists_small_cofinal_of_initiallySmall_op`: initial smallness of `Iᵒᵖ` for a preorder `I` is a
  `u`-small cofinal set of indices.
* `exists_limitCone_and_not_initiallySmall`: every hypothesis of Tag 09ZN, together with its
  conclusion, holds for a system whose index is not initially small.
* `AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_smallLimitingSubsystem`:
  Tag 09ZN at two independent universes, assuming a `u`-small limiting subsystem rather than a
  `u`-small cofinal set of indices.
* `exists_small_directed_cofinal`: a `u`-small cofinal set in a nonempty directed preorder may be
  taken directed.
* `initial_op_subsetInclusion`: the inclusion of a cofinal subset of a nonempty directed preorder
  is an initial functor of the opposite categories.
* `exists_smallLimitingSubsystem_of_initiallySmall`: initial smallness of the index plus a limit
  cone supplies a `u`-small limiting subsystem, so the reduction subsumes
  `..._of_initiallySmall`.
* `ordIsLimit_whiskerSingleton`: the witness system has a singleton limiting subsystem, so the
  reduction applies to it and `..._of_initiallySmall` does not.

## References

* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w v u u₁

namespace Stacks.LimitConeSmallness

/-- Initial smallness of the opposite of a preorder is a `u`-small cofinal set of indices. -/
theorem exists_small_cofinal_of_initiallySmall_op (I : Type w) [Preorder I]
    [InitiallySmall.{u} Iᵒᵖ] :
    ∃ (s : Set I) (_ : Small.{u} s), ∀ i : I, ∃ j ∈ s, i ≤ j := by
  obtain ⟨s, hs, hcof⟩ := InitiallySmall.exists_small_weakly_initial_set.{u} Iᵒᵖ
  refine ⟨Opposite.unop '' s, inferInstance, fun i => ?_⟩
  obtain ⟨j, hjs, ⟨g⟩⟩ := hcof (op i)
  exact ⟨j.unop, ⟨j, hjs, rfl⟩, leOfHom g.unop⟩

/-- The base of the witness system: the spectrum of the integers, in the scheme universe. -/
abbrev base : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℤ))

/-- The witness system: the constant inverse system with value `base`, indexed by the opposite
of the ordinals of the scheme universe.  Every transition morphism is an identity. -/
abbrev ordDiagram : (Ordinal.{u})ᵒᵖ ⥤ Scheme.{u} :=
  (Functor.const (Ordinal.{u})ᵒᵖ).obj base.{u}

/-- The structure morphisms of the witness system over its base: all identities. -/
abbrev ordStruct : ordDiagram.{u} ⟶ (Functor.const (Ordinal.{u})ᵒᵖ).obj base.{u} := 𝟙 _

/-- The identity cone on the witness system. -/
abbrev ordCone : Cone ordDiagram.{u} := constCone (Ordinal.{u})ᵒᵖ base.{u}

/-- **The witness system has a limit cone**, the opposite of a nonempty directed preorder being
a connected category. -/
def ordIsLimit : IsLimit ordCone.{u} := isLimitConstCone _ _

/-- **Every hypothesis Tag 09ZN imposes on its system, and the conclusion of Tag 09ZN too, hold
for a system whose index is not `InitiallySmall.{u}`.**

The binders are those of the statement of Tag 09ZN, with its strict-implicit hypotheses on the
transition morphisms spelled explicitly.  Consequently `CategoryTheory.InitiallySmall.{u} Iᵒᵖ` —
the single hypothesis that
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall` carries beyond
the tag — is **not** a consequence of the tag's hypotheses, not even of the tag's hypotheses
together with the existence of a limit cone, which is what one might have hoped would force it.

The witness is the constant system of `ordDiagram`; it satisfies the tag's conclusion, so it is
in no way a counterexample to Tag 09ZN. -/
theorem exists_limitCone_and_not_initiallySmall :
    ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (S : Scheme.{u}) (_ : CompactSpace S) (_ : QuasiSeparatedSpace S)
      (F : Iᵒᵖ ⥤ Scheme.{u}) (p : F ⟶ (Functor.const Iᵒᵖ).obj S) (c : Cone F) (_ : IsLimit c)
      (f : c.pt ⟶ S) (_ : ∀ i : I, f = c.π.app (op i) ≫ p.app (op i)) (_ : IsIntegralHom f)
      (_ : ∀ i : I, CompactSpace (F.obj (op i)))
      (_ : ∀ i : I, QuasiSeparatedSpace (F.obj (op i)))
      (_ : ∀ (i j : I) (h : i ≤ j), IsAffineHom (F.map (homOfLE h).op))
      (_ : ∀ (i j : I) (h : i ≤ j), IsFinite (F.map (homOfLE h).op))
      (_ : ∀ i : I, LocallyOfFiniteType (p.app (op i)))
      (_ : ∀ᶠ i in Filter.atTop, IsFinite (p.app (op i))),
      ¬ InitiallySmall.{u} Iᵒᵖ :=
  ⟨Ordinal.{u}, inferInstance, inferInstance, inferInstance, base.{u}, inferInstance,
    inferInstance, ordDiagram.{u}, ordStruct.{u}, ordCone.{u}, ordIsLimit.{u}, 𝟙 _,
    fun _ => (Category.comp_id (𝟙 base.{u})).symm,
    inferInstanceAs (IsIntegralHom (𝟙 base.{u})),
    fun _ => inferInstanceAs (CompactSpace base.{u}),
    fun _ => inferInstanceAs (QuasiSeparatedSpace base.{u}),
    fun _ _ _ => inferInstanceAs (IsAffineHom (𝟙 base.{u})),
    fun _ _ _ => inferInstanceAs (IsFinite (𝟙 base.{u})),
    fun _ => inferInstance,
    Filter.Eventually.of_forall fun _ => inferInstance, not_initiallySmall_op_ordinal.{u}⟩

/-- The inclusion of a subset of a preorder, as a functor of the associated categories. -/
def subsetInclusion {I : Type w} [Preorder I] (J : Set I) : (↥J) ⥤ I :=
  Monotone.functor (f := (Subtype.val : J → I)) fun _ _ h => h

/-- The inclusion of a subset of a preorder is a full functor. -/
instance full_subsetInclusion {I : Type w} [Preorder I] (J : Set I) :
    (subsetInclusion J).Full :=
  ⟨fun {_ _} f => ⟨homOfLE (leOfHom f), Subsingleton.elim _ _⟩⟩

/-- The inclusion of a subset of a preorder is a faithful functor. -/
instance faithful_subsetInclusion {I : Type w} [Preorder I] (J : Set I) :
    (subsetInclusion J).Faithful :=
  ⟨fun _ => Subsingleton.elim _ _⟩

/-- **The inclusion of a cofinal subset of a nonempty directed preorder is an initial functor**
of the opposite categories, so a limit over the whole index restricts to a limit over the
subset. -/
theorem initial_op_subsetInclusion {I : Type w} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (J : Set I) (hcof : ∀ i : I, ∃ j ∈ J, i ≤ j) :
    ((subsetInclusion J).op).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun d => ?_
  obtain ⟨j, hjJ, hij⟩ := hcof d.unop
  exact ⟨op ⟨j, hjJ⟩, ⟨(homOfLE hij).op⟩⟩

/-- **A `u`-small cofinal set in a nonempty directed preorder may be taken directed.**  The
upper bounds of the finite subsets of a `u`-small cofinal set form a `u`-small cofinal set which
is directed in its own right.  It is the cofinality of the original set that makes the new one
directed: an upper bound of a finite set is below some member of the original set, and then
below the chosen upper bound of that singleton. -/
theorem exists_small_directed_cofinal {I : Type w} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (s : Set I) [Small.{u} s] (hcof : ∀ i : I, ∃ j ∈ s, i ≤ j) :
    ∃ (J : Set I) (_ : Small.{u} ↥J) (_ : Nonempty ↥J) (_ : IsDirected ↥J (· ≤ ·)),
      ∀ i : I, ∃ j ∈ J, i ≤ j := by
  classical
  have hfs : Small.{u} (Finset ↥s) :=
    small_of_injective (f := Finset.map (equivShrink ↥s).toEmbedding) (Finset.map_injective _)
  choose! σ hσ using fun A : Finset s => Finset.exists_le (A.image Subtype.val)
  have hcofr : ∀ i : I, ∃ j ∈ Set.range σ, i ≤ j := by
    intro i
    obtain ⟨j, hjs, hij⟩ := hcof i
    exact ⟨σ {⟨j, hjs⟩}, ⟨_, rfl⟩, hij.trans (hσ _ _ (by simp))⟩
  refine ⟨Set.range σ, inferInstance, ⟨⟨σ ∅, ⟨_, rfl⟩⟩⟩, ⟨fun a b => ?_⟩, hcofr⟩
  obtain ⟨a', ha's, haa'⟩ := hcof (a : I)
  obtain ⟨b', hb's, hbb'⟩ := hcof (b : I)
  exact ⟨⟨σ {⟨a', ha's⟩, ⟨b', hb's⟩}, ⟨_, rfl⟩⟩,
    haa'.trans (hσ _ _ (by simp)), hbb'.trans (hσ _ _ (by simp))⟩

/-- **Initial smallness of the index, together with a limit cone, supplies a `u`-small limiting
subsystem**: a `u`-small nonempty directed subset of the index along which the restriction of the
cone is still a limit cone.  So the hypothesis of
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_smallLimitingSubsystem` is
implied by the hypotheses of
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall`, and
`ordIsLimit_whiskerSingleton` with `CategoryTheory.not_initiallySmall_op_ordinal` shows the
implication does not
reverse. -/
theorem exists_smallLimitingSubsystem_of_initiallySmall {I : Type w} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] [InitiallySmall.{u} Iᵒᵖ] {C : Type u₁} [Category.{v} C]
    {F : Iᵒᵖ ⥤ C} (c : Cone F) (hc : IsLimit c) :
    ∃ (J : Set I) (_ : Small.{u} ↥J) (_ : Nonempty ↥J) (_ : IsDirected ↥J (· ≤ ·)),
      Nonempty (IsLimit (c.whisker (subsetInclusion J).op)) := by
  obtain ⟨s, hs, hcof⟩ := exists_small_cofinal_of_initiallySmall_op.{w, u} I
  obtain ⟨J, hJs, hJne, hJd, hJcof⟩ := exists_small_directed_cofinal.{w, u} s hcof
  have := initial_op_subsetInclusion J hJcof
  exact ⟨J, hJs, hJne, hJd, ⟨(Functor.Initial.isLimitWhiskerEquiv _ c).symm hc⟩⟩

end Stacks.LimitConeSmallness

namespace AlgebraicGeometry

open Stacks.LimitConeSmallness in
/-- **Stacks 09ZN at two independent universes, from a `u`-small limiting subsystem.**

In a directed inverse system of qcqs schemes over a qcqs scheme, if the transition morphisms are
finite, the stages are locally of finite type over the base, and the morphism to the base from
the vertex of a cone which is a limit cone *of the restriction of the system to some `u`-small
nonempty directed subset of the index* is integral, then the stages are eventually finite over
the base.

This is the statement of Tag 09ZN at its own two independent universes, save that
the hypothesis `IsLimit c` on the whole system is replaced by the hypothesis that the restriction
of `c` to a `u`-small nonempty directed subset `J` of the index is a limit cone of the restricted
system.  That hypothesis is strictly weaker than the
`CategoryTheory.InitiallySmall.{u} Iᵒᵖ` carried by
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall`: initial
smallness plus `IsLimit c` supplies it, while
`Stacks.LimitConeSmallness.ordIsLimit_whiskerSingleton` exhibits a system satisfying it whose
index is provably not initially small.

Whether it is derivable from the tag's own hypotheses is open; it is the precise residue of Tag
09ZN at a free index universe. -/
theorem eventually_isFinite_of_isLimit_of_isIntegral_of_smallLimitingSubsystem
    {I : Type w} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (F : Iᵒᵖ ⥤ Scheme.{u}) (p : F ⟶ (Functor.const Iᵒᵖ).obj S)
    (c : Cone F) (f : c.pt ⟶ S)
    (hf : ∀ i, f = c.π.app (Opposite.op i) ≫ p.app (Opposite.op i))
    [IsIntegralHom f]
    [∀ i, CompactSpace (F.obj (Opposite.op i))]
    [∀ i, QuasiSeparatedSpace (F.obj (Opposite.op i))]
    (haffine : ∀ {i j : I} (h : i ≤ j),
      IsAffineHom (F.map (homOfLE h).op))
    (hfinite : ∀ {i j : I} (h : i ≤ j),
      IsFinite (F.map (homOfLE h).op))
    [∀ i, LocallyOfFiniteType (p.app (Opposite.op i))]
    (J : Set I) [Small.{u} ↥J] [Nonempty ↥J] [IsDirected ↥J (· ≤ ·)]
    (hJ : IsLimit (c.whisker (subsetInclusion J).op)) :
    ∀ᶠ i in Filter.atTop, IsFinite (p.app (Opposite.op i)) := by
  have hcpt : ∀ a : ↥J, CompactSpace (((subsetInclusion J).op ⋙ F).obj (Opposite.op a)) :=
    fun a => inferInstanceAs (CompactSpace (F.obj (Opposite.op (a : I))))
  have hqs : ∀ a : ↥J, QuasiSeparatedSpace (((subsetInclusion J).op ⋙ F).obj (Opposite.op a)) :=
    fun a => inferInstanceAs (QuasiSeparatedSpace (F.obj (Opposite.op (a : I))))
  have hlft : ∀ a : ↥J,
      LocallyOfFiniteType ((Functor.whiskerLeft (subsetInclusion J).op p).app (Opposite.op a)) :=
    fun a => inferInstanceAs (LocallyOfFiniteType (p.app (Opposite.op (a : I))))
  have key := eventually_isFinite_of_isLimit_of_isIntegral_of_small
    ((subsetInclusion J).op ⋙ F) (Functor.whiskerLeft (subsetInclusion J).op p)
    (c.whisker (subsetInclusion J).op) hJ f (fun a => hf (a : I))
    (fun h => haffine h) (fun h => hfinite h)
  rw [Filter.eventually_atTop] at key ⊢
  obtain ⟨a, ha⟩ := key
  refine ⟨(a : I), fun j hj => ?_⟩
  have hfin : IsFinite (p.app (Opposite.op (a : I))) := ha a le_rfl
  have htrans : IsFinite (F.map (homOfLE hj).op) := hfinite hj
  have hnat : F.map (homOfLE hj).op ≫ p.app (Opposite.op (a : I)) = p.app (Opposite.op j) := by
    simp
  rw [← hnat]
  infer_instance

end AlgebraicGeometry

namespace Stacks.LimitConeSmallness

/-- The singleton `{0}` of ordinals is a nonempty subset of the index of the witness system. -/
instance nonempty_singletonZero : Nonempty (↥({0} : Set Ordinal.{u})) := ⟨⟨0, rfl⟩⟩

/-- Any two elements of a singleton subset are bounded by one another. -/
instance isDirected_singletonZero : IsDirected (↥({0} : Set Ordinal.{u})) (· ≤ ·) :=
  ⟨fun a b => ⟨b, le_of_eq (Subtype.ext (a.2.trans b.2.symm)), le_rfl⟩⟩

/-- **The witness system has a singleton limiting subsystem.**  So
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_smallLimitingSubsystem`
applies to the witness system, while
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall` provably
cannot: the index is not initially small by
`CategoryTheory.not_initiallySmall_op_ordinal`. -/
def ordIsLimit_whiskerSingleton :
    IsLimit (ordCone.{u}.whisker (subsetInclusion ({0} : Set Ordinal.{u})).op) :=
  isLimitConstCone _ _

end Stacks.LimitConeSmallness

end

end
