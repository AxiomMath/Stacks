module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Defs
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.LocalUnitConditions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedRingedToposLocallyRinged
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# One is never zero: the sheaf-level form of the first locally ringed condition

Let `(C, J)` be a site and `O` a sheaf of commutative rings on it. Stacks Tag 05D7 is the
displayed morphism of sheaves of sets

  `∅^# ⟶ Equalizer(0, 1 : * ⟶ O)`

from the initial sheaf to the equalizer of the zero and one sections of the structure
sheaf, and the first condition in the definition of a locally ringed site (Stacks
Definition 18.40.4, Tag 04EU) is that this morphism be an isomorphism. In other words, whenever
`U` is not sheaf-theoretically empty, `0 ≠ 1` in `O(U)`; this file proves that equivalence.

## Main definitions

* `Stacks.Sheaves.LocallyRingedSite.singletonSheaf`,
  `Stacks.Sheaves.LocallyRingedSite.zeroSection`,
  `Stacks.Sheaves.LocallyRingedSite.oneSection`: the singleton sheaf `*` and the two
  global sections `0, 1 : * ⟶ O` of the underlying sheaf of sets of `O`.
* `Stacks.Sheaves.LocallyRingedSite.oneIsNeverZero`: the canonical morphism
  `∅^# ⟶ Equalizer(0, 1)`.

## Main results

* `Stacks.Sheaves.LocallyRingedSite.isIso_oneIsNeverZero_iff`: the canonical morphism is an
  isomorphism exactly when `0 ≠ 1` in `O(U)` for every object `U` that the empty sieve does not
  cover.
* `Stacks.Sheaves.LocallyRingedSite.isInitialOfSections` and
  `Stacks.Sheaves.LocallyRingedSite.bot_mem_of_isInitial`: a sheaf of sets is initial
  exactly when it has sections only over objects covered by the empty sieve.
* `Stacks.Sheaves.LocallyRingedSite.isLocallyRingedSite_iff`: Definition 18.40.4 in the
  source's own spelling (the morphism of Tag 05D7 is an isomorphism, together with the
  equivalent conditions of Tag 04ES) holds exactly when the sections-level predicate
  `IsLocallyRingedSite` does.
* `Stacks.Sheaves.LocallyRingedSite.localizedRingedTopos_isLocallyRinged`: in that spelling,
  the localization of a locally ringed topos at a sheaf is locally ringed.
* `Stacks.Sheaves.LocallyRingedSite.nontrivial_stalkRingObj`: if the morphism of Tag 05D7 is an
  isomorphism then the stalk of the structure sheaf at every point is not the zero ring.

## Implementation notes

The initial sheaf `∅^#` is `CategoryTheory.emptySheaf`, whose sections over `U` are the proofs
that the empty sieve covers `U`; it needs no sheafification, so the universes of the site and
of the section rings stay independent. The resulting `HasInitial (Sheaf J (Type w))` is a
local instance only, since a second initial object in scope would make `⊥_ _` ambiguous.

## References

* [Stacks Project, Tag 05D7](https://stacks.math.columbia.edu/tag/05D7)
* [Stacks Project, Tag 05D8](https://stacks.math.columbia.edu/tag/05D8)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 04ES](https://stacks.math.columbia.edu/tag/04ES)
* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sheaves.LocallyRingedSite

universe u v w

section InitialSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The canonical initial sheaf of sets has at most one section over every object: its
sections are the proofs that the empty sieve covers that object. -/
instance subsingleton_emptySheaf_obj (U : Cᵒᵖ) :
    Subsingleton ((CategoryTheory.emptySheaf.{u, v, w} J).obj.obj U) :=
  inferInstanceAs (Subsingleton (ULift.{w} (PLift _)))

variable {J}

/-- An initial sheaf of sets has sections only over sheaf-theoretically empty objects. -/
theorem bot_mem_of_isInitial {F : Sheaf J (Type w)} (hF : IsInitial F) {U : C}
    (x : F.obj.obj (op U)) : (⊥ : Sieve U) ∈ J U :=
  (((hF.uniqueUpToIso (CategoryTheory.emptySheafIsInitial J)).hom.hom.app (op U)) x).down.down

/-- Over a sheaf-theoretically empty object every sheaf of sets has at most one section. -/
theorem subsingleton_sections_of_bot_mem (F : Sheaf J (Type w)) {U : C}
    (hU : (⊥ : Sieve U) ∈ J U) : Subsingleton (F.obj.obj (op U)) :=
  (Types.isTerminalEquivUnique _ (F.isTerminalOfBotCover U hU)).instSubsingleton

/-- A sheaf of sets with sections only over sheaf-theoretically empty objects is initial. -/
noncomputable def isInitialOfSections {F : Sheaf J (Type w)}
    (h : ∀ U : C, F.obj.obj (op U) → (⊥ : Sieve U) ∈ J U) : IsInitial F := by
  classical
  refine IsInitial.ofIso (CategoryTheory.emptySheafIsInitial.{u, v, w} J)
    ⟨(CategoryTheory.emptySheafIsInitial J).to F, ⟨{
      app := fun U => ↾fun x => ⟨⟨h U.unop x⟩⟩
      naturality := by intro U V f; ext x; exact Subsingleton.elim _ _ }⟩, ?_, ?_⟩
  · ext U x
    exact Subsingleton.elim _ _
  · ext U x
    have := subsingleton_sections_of_bot_mem F (h U.unop x)
    exact Subsingleton.elim _ _

end InitialSheaf

section ZeroAndOne

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

attribute [local instance] CategoryTheory.hasInitialSheafOfTypes

/-- The singleton sheaf `*` of Stacks Tag 00W3: a single section over every object. -/
abbrev singletonSheaf : Sheaf J (Type w) :=
  ⟨(Functor.const Cᵒᵖ).obj PUnit.{w + 1},
    Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit⟩

/-- The singleton sheaf is a terminal object of the category of sheaves of sets. -/
noncomputable def isTerminalSingletonSheaf : IsTerminal (singletonSheaf.{u, v, w} J) :=
  Sheaf.isTerminalTerminal J Types.isTerminalPUnit

/-- The global section `0 : * ⟶ O` of the underlying sheaf of sets of `O`. -/
def zeroSection (O : Sheaf J CommRingCat.{w}) :
    singletonSheaf J ⟶ underlyingRingSheaf J O :=
  ⟨{ app := fun U ↦ ↾fun _ : PUnit.{w + 1} ↦ (0 : O.obj.obj U)
     naturality := by
       intro U V f
       ext x
       change 0 = (O.obj.map f).hom 0
       exact (map_zero (O.obj.map f).hom).symm }⟩

/-- The global section `1 : * ⟶ O` of the underlying sheaf of sets of `O`. -/
def oneSection (O : Sheaf J CommRingCat.{w}) :
    singletonSheaf J ⟶ underlyingRingSheaf J O :=
  ⟨{ app := fun U ↦ ↾fun _ : PUnit.{w + 1} ↦ (1 : O.obj.obj U)
     naturality := by
       intro U V f
       ext x
       change 1 = (O.obj.map f).hom 1
       exact (map_one (O.obj.map f).hom).symm }⟩

/-- The canonical morphism of sheaves of sets

  `∅^# ⟶ Equalizer(0, 1 : * ⟶ O)`

from the initial sheaf to the equalizer of the zero and one sections of the structure sheaf.
The first condition in the definition of a locally ringed site (Tag 04EU) is that it be an
isomorphism. -/
@[stacks 05D7 "the displayed morphism from the empty sheaf to the equalizer of 0 and 1"]
noncomputable def oneIsNeverZero (O : Sheaf J CommRingCat.{w}) :
    ⊥_ (Sheaf J (Type w)) ⟶ equalizer (zeroSection J O) (oneSection J O) :=
  initial.to _

variable {J}

/-- A section of `Equalizer(0, 1)` over `U` forces `0 = 1` in `O(U)`. -/
theorem zero_eq_one_of_equalizer_section (O : Sheaf J CommRingCat.{w}) {U : C}
    (x : (equalizer (zeroSection J O) (oneSection J O)).obj.obj (op U)) :
    (0 : O.obj.obj (op U)) = 1 :=
  congrArg
    (fun φ : equalizer (zeroSection J O) (oneSection J O) ⟶ underlyingRingSheaf J O =>
      φ.hom.app (op U) x)
    (equalizer.condition (zeroSection J O) (oneSection J O))

/-- A section of `Equalizer(0, 1)` over `U` obtained from `0 = 1` in `O(U)`. -/
noncomputable def equalizerSectionOfEq (O : Sheaf J CommRingCat.{w}) {U : C}
    (h : (0 : O.obj.obj (op U)) = 1) :
    (equalizer (zeroSection J O) (oneSection J O)).obj.obj (op U) := by
  have l₁ := isLimitOfHasEqualizerOfPreservesLimit (sheafToPresheaf J (Type w))
    (zeroSection J O) (oneSection J O)
  have l₂ := isLimitForkMapOfIsLimit ((evaluation Cᵒᵖ (Type w)).obj (op U)) _ l₁
  refine l₂.lift (Fork.ofι (↾fun _ : PUnit.{w + 1} => PUnit.unit) ?_) PUnit.unit
  ext y
  exact h

/-- The canonical morphism `∅^# ⟶ Equalizer(0, 1)` is an isomorphism exactly when, for every
object `U` that is not sheaf-theoretically empty, the sections `0` and `1` of `O(U)` are
distinct. -/
@[stacks 05D7 "the equivalent sections-level form: 0 ≠ 1 over every object the empty sieve
  does not cover"]
theorem isIso_oneIsNeverZero_iff (O : Sheaf J CommRingCat.{w}) :
    IsIso (oneIsNeverZero J O) ↔
      ∀ U : C, (⊥ : Sieve U) ∉ J U → (0 : O.obj.obj (op U)) ≠ 1 := by
  constructor
  · intro hiso U hU h01
    have hE : IsInitial (equalizer (zeroSection J O) (oneSection J O)) :=
      initialIsInitial.ofIso (asIso (oneIsNeverZero J O))
    exact hU (bot_mem_of_isInitial hE (equalizerSectionOfEq O h01))
  · intro hsec
    have hE : IsInitial (equalizer (zeroSection J O) (oneSection J O)) :=
      isInitialOfSections fun U x =>
        Classical.byContradiction fun hU => hsec U hU (zero_eq_one_of_equalizer_section O x)
    exact ⟨hE.to _, initialIsInitial.hom_ext _ _, hE.hom_ext _ _⟩

end ZeroAndOne

section RingedTopos

attribute [local instance] CategoryTheory.hasInitialSheafOfTypes

variable (X : Stacks.Sheaves.LocallyRingedTopos.RingedTopos.{u})

/-- Condition (2) of Stacks Definition 18.40.4, `Stacks.Sheaves.LocallyRingedSite.Condition1`,
holds exactly when every section is `Stacks.Sheaves.LocallyRingedTopos.LocallyUnitOrCounit`. -/
theorem condition1_iff_locallyUnitOrCounit :
    Stacks.Sheaves.LocallyRingedSite.Condition1 X.O ↔
      ∀ (U : X.C)
        (a : (((sheafToPresheaf X.J CommRingCat.{u}).obj X.O).obj (op U) : CommRingCat.{u})),
        Stacks.Sheaves.LocallyRingedTopos.LocallyUnitOrCounit X U a := by
  constructor
  · intro h U a
    obtain ⟨S, hS, hP⟩ := h U a
    refine ⟨⟨S, hS⟩, fun V g hg => ?_⟩
    have key : IsUnit (Stacks.Sheaves.LocallyRingedSite.restrict X.O g a) ∨
        IsUnit (1 - Stacks.Sheaves.LocallyRingedSite.restrict X.O g a) := by
      refine (hP g hg).imp id fun hu => ?_
      simpa only [Stacks.Sheaves.LocallyRingedSite.Invertible,
        Stacks.Sheaves.LocallyRingedSite.restrict, map_sub, map_one] using hu
    exact key
  · intro h U a
    obtain ⟨S, hP⟩ := h U a
    refine ⟨S.1, S.2, fun V g hg => ?_⟩
    have key : IsUnit (Stacks.Sheaves.LocallyRingedSite.restrict X.O g a) ∨
        IsUnit (1 - Stacks.Sheaves.LocallyRingedSite.restrict X.O g a) := hP g hg
    refine key.imp id fun hu => ?_
    simpa only [Stacks.Sheaves.LocallyRingedSite.Invertible,
      Stacks.Sheaves.LocallyRingedSite.restrict, map_sub, map_one] using hu

/-- Definition 18.40.4 in the source's own spelling (the morphism of Tag 05D7 is an isomorphism,
and the equivalent conditions of Tag 04ES hold) is equivalent to the sections-level predicate
`IsLocallyRingedSite`. -/
@[stacks 04EU "Definition 18.40.4 in the source's spelling (05D7 an isomorphism, plus 04ES)
", stacks 04H8 "a ringed topos is locally ringed exactly when its underlying ringed site is"]
theorem isLocallyRingedSite_iff :
    IsIso (oneIsNeverZero X.J X.O) ∧ Stacks.Sheaves.LocallyRingedSite.Condition1 X.O ↔
      LocalizedRingedTopos.IsLocallyRingedSite X :=
  and_congr (isIso_oneIsNeverZero_iff X.O) (condition1_iff_locallyUnitOrCounit X)

/-- If the morphism of Tag 05D7 is an isomorphism for `X` and the conditions of Tag 04ES hold, then
both hold for the localization of `X` at a sheaf `F`. -/
@[stacks 04IH "(5), first assertion, with condition (1) in the source's sheaf-level spelling of
05D7"]
theorem localizedRingedTopos_isLocallyRinged (F : X.Topos)
    (hX : IsIso (oneIsNeverZero X.J X.O) ∧ Stacks.Sheaves.LocallyRingedSite.Condition1 X.O) :
    IsIso (oneIsNeverZero (LocalizedRingedTopos.localizedRingedTopos X F).J
        (LocalizedRingedTopos.localizedRingedTopos X F).O) ∧
      Stacks.Sheaves.LocallyRingedSite.Condition1 (LocalizedRingedTopos.localizedRingedTopos X F).O
        :=
  (isLocallyRingedSite_iff _).2
    (LocalizedRingedTopos.isLocallyRingedSite_localizedRingedTopos X F
      ((isLocallyRingedSite_iff X).1 hX))

/-- If the morphism of Tag 05D7 is an isomorphism then for every point `p` of the site the stalk
`O_p` is not the zero ring. -/
@[stacks 05D8 "(1) implies (2): if the morphism of 05D7 is an isomorphism then no stalk of
  the structure sheaf is the zero ring"]
theorem nontrivial_stalkRingObj (h : IsIso (oneIsNeverZero X.J X.O))
    (p : Stacks.Sheaves.LocallyRingedTopos.Point X) : Nontrivial p.stalkRingObj := by
  have hE : IsInitial (equalizer (zeroSection X.J X.O) (oneSection X.J X.O)) :=
    initialIsInitial.ofIso (@asIso _ _ _ _ (oneIsNeverZero X.J X.O) h)
  have hSE := hE.isInitialObj p.stalk _
  have hempty : IsEmpty (p.stalk.obj (equalizer (zeroSection X.J X.O) (oneSection X.J X.O))) :=
    ⟨fun x => PEmpty.elim (hSE.to (PEmpty.{u + 1} : Type u) x)⟩
  have hT := (isTerminalSingletonSheaf X.J).isTerminalObj p.stalk _
  by_contra hns
  rw [not_nontrivial_iff_subsingleton] at hns
  have hsub : Subsingleton (p.stalk.obj (underlyingRingSheaf X.J X.O)) :=
    @Equiv.subsingleton _ _ (p.stalkRing_compat.app X.O).toEquiv.symm hns
  have heq : p.stalk.map (zeroSection X.J X.O) = p.stalk.map (oneSection X.J X.O) := by
    ext y
    exact Subsingleton.elim _ _
  have l := isLimitForkMapOfIsLimit p.stalk _
    (equalizerIsEqualizer (zeroSection X.J X.O) (oneSection X.J X.O))
  have pt := l.lift (Fork.ofι (𝟙 (p.stalk.obj (singletonSheaf X.J))) (by rw [heq]))
  exact hempty.elim (pt (hT.from (PUnit.{u + 1} : Type u) PUnit.unit))

end RingedTopos

end Stacks.Sheaves.LocallyRingedSite

end
