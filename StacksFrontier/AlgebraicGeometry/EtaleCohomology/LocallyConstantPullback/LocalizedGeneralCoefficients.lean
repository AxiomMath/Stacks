module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.CoverCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.GeneralCoefficients

/-!
# Localization and local constancy, for an arbitrary coefficient category

Let `J` be a Grothendieck topology on a category `C` with pullbacks. Restriction of sheaves along
`CategoryTheory.Over.map f`, for a morphism `f : X ⟶ Y` of `C`, carries the constant sheaf on an
object `E` of the coefficient category to the constant sheaf on that same `E`. Consequently a
trivialization of a sheaf over `Y`, with value `E`, restricts to a trivialization over any `X`
lying over `Y` with the same value, so one covering of the final object of the site trivializes
the sheaf over every object.

Both statements are already in this directory for sheaves of *sets*, in
`LocallyConstantPullback/OverMapConstant.lean` and `LocallyConstantPullback/CoverCriterion.lean`.
Their proofs go through the corepresentability of sections by the constant sheaf on a one-element
set and therefore do not reach sheaves of abelian groups or of modules. This file proves them for
an arbitrary coefficient category, by the route of
`Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal`: restriction along `Over.map f` is a left
adjoint of restriction along `Over.pullback f`, which is a right adjoint and so carries the final
object of `Over Y` to the final object of `Over X`; sections over a final object are the two
global-sections functors, and uniqueness of left adjoints finishes it. Nothing in the argument
constrains the coefficients.

The refinement lemma is stated once, for an arbitrary predicate `Q` on the coefficient category,
in `Stacks.ConstantSheaf.Localization.exists_trivializing_cover`. Specializing `Q` recovers the
three criteria the constructibility chain uses: plain local constancy, finite local constancy for
a concrete coefficient category, and — since the statement is about an arbitrary `Q` — local
constancy with finitely generated module values.

## Main results

* `Stacks.ConstantSheaf.Localization.overMapPullbackConstantSheafIso` — restriction along a
  morphism of the site commutes with the constant sheaf functor.
* `Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap` — a trivialization over `Y` with value
  `E` restricts to a trivialization over any `X` over `Y`, with the same value.
* `Stacks.ConstantSheaf.Localization.exists_trivializing_cover` — one covering of the final object
  on which the sheaf is trivialized, with values satisfying a predicate `Q`, yields such a
  covering of every object.
* `Stacks.ConstantSheaf.Localization.isLocallyConstant_iff_isConstant_cover` and
  `Stacks.ConstantSheaf.Localization.isFiniteLocallyConstant_iff_finite_cover` — local constancy
  and finite local constancy are each equivalent to trivializability on one covering of the final
  object.

## Implementation notes

The declarations live in the namespace `Stacks.ConstantSheaf.Localization` rather than in
`Stacks.ConstantSheaf`, where the `Type w` versions are: the general statements subsume them, but
replacing them would change the types of declarations already consumed elsewhere in the
directory, so the two sets coexist under distinct names.

No `@[stacks]` attribute appears in this file. Tag 093R is the assertion for locally constant
sheaves under the inverse image of a morphism of topoi; what is proved here is its localization
case, for the morphisms of topoi internal to one site, which is an input to that tag rather than
the tag itself.

## References

* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u t

namespace Stacks.ConstantSheaf.Localization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasPullbacks C]
  (A : Type w) [Category.{t} A] [∀ U : C, HasWeakSheafify (J.over U) A]

omit [HasPullbacks C] in
/-- Pulling back the final object of `Over Y` along `f : X ⟶ Y` gives the final object of
`Over X`, given only the base changes of `f` itself, `CategoryTheory.Limits.HasPullbacksAlong f`:
`CategoryTheory.Over.pullback f` is a right adjoint, so it preserves the final object, and final
objects are unique up to isomorphism.  This is the form needed on a site which has base change
only along a distinguished class of arrows, as in
`Stacks.ComparingTopologies.CohomologyComparison`. -/
public def overPullbackObjTerminalIsoOfHasPullbacksAlong {X Y : C} (f : X ⟶ Y)
    [HasPullbacksAlong f] :
    (Over.pullback f).obj (Over.mk (𝟙 Y)) ≅ Over.mk (𝟙 X) :=
  (Over.mkIdTerminal.isTerminalObj (Over.pullback f)).uniqueUpToIso Over.mkIdTerminal

/-- Pulling back the final object of `Over Y` along `f : X ⟶ Y` gives the final object of
`Over X`: `CategoryTheory.Over.pullback f` is a right adjoint, so it preserves the final
object, and final objects are unique up to isomorphism. -/
public def overPullbackObjTerminalIso {X Y : C} (f : X ⟶ Y) :
    (Over.pullback f).obj (Over.mk (𝟙 Y)) ≅ Over.mk (𝟙 X) :=
  overPullbackObjTerminalIsoOfHasPullbacksAlong f

/-- **Restriction of a constant sheaf along a morphism of the site is constant**, with the same
value, for an arbitrary coefficient category. -/
public def overMapPullbackConstantSheafIso {X Y : C} (f : X ⟶ Y) :
    constantSheaf (J.over Y) A ⋙ J.overMapPullback A f ≅ constantSheaf (J.over X) A :=
  have hadj : J.overMapPullback A f ⊣
      (Over.pullback f).sheafPushforwardContinuous A (J.over Y) (J.over X) :=
    (Over.mapPullbackAdj f).sheafPushforwardAdjunction A
  have : ((Over.pullback f).sheafPushforwardContinuous A
      (J.over Y) (J.over X)).IsRightAdjoint := ⟨_, ⟨hadj⟩⟩
  (((constantSheafAdj (J.over Y) A Over.mkIdTerminal).comp hadj).ofNatIsoRight
    (pushforwardSectionsIsoOfTerminal (Over.pullback f) A (J.over Y) (J.over X)
      (overPullbackObjTerminalIso f))).leftAdjointUniq
    (constantSheafAdj (J.over X) A Over.mkIdTerminal)

/-- Restriction along a morphism of the site preserves constant sheaves, for an arbitrary
coefficient category. -/
public lemma isConstant_overMapPullback {X Y : C} (f : X ⟶ Y) (G : Sheaf (J.over Y) A)
    [Sheaf.IsConstant (J.over Y) G] :
    Sheaf.IsConstant (J.over X) ((J.overMapPullback A f).obj G) := by
  obtain ⟨E, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant (J.over Y) G
  exact Sheaf.isConstant_of_iso (J.over X)
    ((J.overMapPullback A f).mapIso e.symm ≪≫ (overMapPullbackConstantSheafIso J A f).app E)

/-- **A trivialization survives refinement**, for an arbitrary coefficient category: if the
restriction of `G` to `Y` is the constant sheaf on `E`, its restriction to any `X` over `Y` is
the constant sheaf on the *same* `E`. Keeping the value unchanged is what makes the statement
usable for *finite* local constancy: any property of the constant value is carried along. -/
public def overPullbackIsoOfMap {X Y : C} (f : X ⟶ Y) (G : Sheaf J A) (E : A)
    (e : (constantSheaf (J.over Y) A).obj E ≅ (J.overPullback A Y).obj G) :
    (constantSheaf (J.over X) A).obj E ≅ (J.overPullback A X).obj G :=
  (overMapPullbackConstantSheafIso J A f).symm.app E ≪≫
    (J.overMapPullback A f).mapIso e ≪≫ G.pushforwardOverMapIso f

/-- The `Prop`-valued form of `Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap`: a sheaf
which becomes constant after restriction to `Y` becomes constant after restriction to any `X`
over `Y`. -/
public lemma isConstant_over_of_isConstant_over {X Y : C} (f : X ⟶ Y) (G : Sheaf J A)
    [Sheaf.IsConstant (J.over Y) ((J.overPullback A Y).obj G)] :
    Sheaf.IsConstant (J.over X) ((J.overPullback A X).obj G) :=
  have := isConstant_overMapPullback J A f ((J.overPullback A Y).obj G)
  Sheaf.isConstant_congr (J.over X) (G.pushforwardOverMapIso f)

/-- **One covering of the final object trivializes over every object.** The covering of `U` is
the pullback of the given covering of the final object; each of its members maps to a member of
the given covering, over which the sheaf is already trivialized, and the value is unchanged, so
whatever predicate `Q` the given values satisfy the produced ones satisfy too. -/
public lemma exists_trivializing_cover {T : C} (hT : IsTerminal T) (G : Sheaf J A) (Q : A → Prop)
    {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T} (hf : Sieve.ofArrows X f ∈ J T)
    (hc : ∀ i, ∃ E : A, Q E ∧ Nonempty
      ((constantSheaf (J.over (X i)) A).obj E ≅ (J.overPullback A (X i)).obj G))
    (U : C) :
    ∃ (I' : Type (max u v)) (X' : I' → C) (f' : ∀ i, X' i ⟶ U),
      Sieve.ofArrows X' f' ∈ J U ∧ ∀ i, ∃ E : A, Q E ∧ Nonempty
        ((constantSheaf (J.over (X' i)) A).obj E ≅ (J.overPullback A (X' i)).obj G) := by
  refine ⟨Σ V : C, {g : V ⟶ U // (Sieve.pullback (hT.from U) (Sieve.ofArrows X f)).arrows g},
    fun p => p.1, fun p => p.2.1,
    sieve_ofArrows_arrows_mem J _ (J.pullback_stable (hT.from U) hf), fun p => ?_⟩
  have h1 : (Sieve.ofArrows X f).arrows (p.2.1 ≫ hT.from U) := p.2.2
  rw [hT.hom_ext (p.2.1 ≫ hT.from U) (hT.from p.1)] at h1
  obtain ⟨i, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp h1
  obtain ⟨E, hE, ⟨e⟩⟩ := hc i
  exact ⟨E, hE, ⟨overPullbackIsoOfMap J A h G E e⟩⟩

/-- **A single covering of the final object suffices for local constancy**, for an arbitrary
coefficient category. -/
public lemma isLocallyConstant_of_isConstant_cover {T : C} (hT : IsTerminal T) (G : Sheaf J A)
    {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T} (hf : Sieve.ofArrows X f ∈ J T)
    (hc : ∀ i, Sheaf.IsConstant (J.over (X i)) ((J.overPullback A (X i)).obj G)) :
    IsLocallyConstant J G where
  exists_cover U := by
    have hc' : ∀ i, ∃ E : A, True ∧ Nonempty
        ((constantSheaf (J.over (X i)) A).obj E ≅ (J.overPullback A (X i)).obj G) := by
      intro i
      obtain ⟨E, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant (J.over (X i))
        ((J.overPullback A (X i)).obj G)
      exact ⟨E, trivial, ⟨e⟩⟩
    obtain ⟨I', X', f', hf', h'⟩ := exists_trivializing_cover J A hT G _ hf hc' U
    refine ⟨I', X', f', hf', fun i => ?_⟩
    obtain ⟨E, -, ⟨e⟩⟩ := h' i
    exact Sheaf.isConstant_of_iso (J.over (X' i)) e.symm

/-- **Local constancy is equivalent to trivializability on one covering of the final object**,
for an arbitrary coefficient category. -/
public lemma isLocallyConstant_iff_isConstant_cover {T : C} (hT : IsTerminal T) (G : Sheaf J A) :
    IsLocallyConstant J G ↔
      ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ T), Sieve.ofArrows X f ∈ J T ∧
        ∀ i, Sheaf.IsConstant (J.over (X i)) ((J.overPullback A (X i)).obj G) :=
  ⟨fun h => h.exists_cover T, fun ⟨_, _, _, hf, hc⟩ =>
    isLocallyConstant_of_isConstant_cover J A hT G hf hc⟩

section Concrete

variable {FA : A → A → Type*} {CA : A → Type*}
  [∀ E E', FunLike (FA E E') (CA E) (CA E')] [ConcreteCategory A FA]

/-- **A single covering of the final object suffices for finite local constancy**, for an
arbitrary concrete coefficient category. -/
public lemma isFiniteLocallyConstant_of_finite_cover {T : C} (hT : IsTerminal T) (G : Sheaf J A)
    {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T} (hf : Sieve.ofArrows X f ∈ J T)
    (hc : ∀ i, ∃ E : A, Finite (CA E) ∧ Nonempty
      ((constantSheaf (J.over (X i)) A).obj E ≅ (J.overPullback A (X i)).obj G)) :
    IsFiniteLocallyConstant (FD := FA) (CD := CA) J G where
  exists_finite_cover U := exists_trivializing_cover J A hT G _ hf hc U

/-- **Finite local constancy is equivalent to finite trivializability on one covering of the
final object**, for an arbitrary concrete coefficient category. -/
public lemma isFiniteLocallyConstant_iff_finite_cover {T : C} (hT : IsTerminal T)
    (G : Sheaf J A) :
    IsFiniteLocallyConstant (FD := FA) (CD := CA) J G ↔
      ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ T), Sieve.ofArrows X f ∈ J T ∧
        ∀ i, ∃ E : A, Finite (CA E) ∧ Nonempty
          ((constantSheaf (J.over (X i)) A).obj E ≅ (J.overPullback A (X i)).obj G) :=
  ⟨fun h => h.exists_finite_cover T, fun ⟨_, _, _, hf, hc⟩ =>
    isFiniteLocallyConstant_of_finite_cover J A hT G hf hc⟩

end Concrete

end Stacks.ConstantSheaf.Localization

end
