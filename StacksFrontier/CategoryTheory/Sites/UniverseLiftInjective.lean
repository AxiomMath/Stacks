module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The universe lift of an injective abelian sheaf is injective

Raising the universe of all groups of sections of a sheaf of abelian groups is the functor
`CategoryTheory.sheafCompose J AddCommGrpCat.uliftFunctor`. This file shows that it carries
injective objects to injective objects.

## Main results

* `Stacks.Sheaves.UniverseLift.exists_uliftDescent`: **a monomorphism into the universe lift of
  an abelian sheaf is the universe lift of a monomorphism of abelian sheaves in the smaller
  universe**, canonically so.
* `Stacks.Sheaves.UniverseLift.injective_uliftSheafFunctor_obj` and
  `Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor`: **the universe lift
  of an injective abelian sheaf is injective**, given a separator of the larger sheaf category
  which is itself a universe lift.

## Main definitions

* `Stacks.Sheaves.UniverseLift.uliftSheafFunctor`: the universe lift on abelian sheaves.
* `Stacks.Sheaves.UniverseLift.uliftDescent`: for a map `α : S ⟶ Y ⋙ uliftFunctor` of presheaves
  of abelian groups which is injective on sections, the presheaf in the smaller universe formed
  by the images of the sections of `S` inside the sections of `Y`.

## Implementation notes

The usual way to see that a functor preserves injectives is to exhibit it as the right adjoint of
an exact functor, and that is unavailable here: the universe lift has no left adjoint, since the
dual of a group in the larger universe need not be small. What replaces it is Baer's criterion in
the form `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms_rlp`: in a Grothendieck
abelian category it is enough to solve the extension problem along the inclusions of the
subobjects of a single separator.

That reduction is what makes the lift accessible, because of `exists_uliftDescent`: a subsheaf of
a universe lift is again a universe lift. A monomorphism of sheaves is injective on sections, so
the sections of a subobject of `(Y ⋙ uliftFunctor)` are in bijection with a subgroup of the
sections of `Y`, which lives in the smaller universe on the nose -- no shrinking is needed, the
subgroup `uliftDescentSubgroup` is the image of the map on sections. The sheaf condition descends
because the universe lift is fully faithful, hence reflects limits.

So an extension problem along the inclusion of a subobject of a lifted separator is the universe
lift of an extension problem in the smaller universe, where injectivity of the coefficient sheaf
solves it; full faithfulness of the lift carries the solution back.

**Why the separator is a hypothesis.** The transport above is available only for a monomorphism
whose target is itself a universe lift, so Baer's criterion has to be applied at a separator which
is one, and nothing here produces such a separator: the separator that
`CategoryTheory.Sheaf.hasSeparator` supplies is a coproduct over the objects of the site of
sheafified free presheaves, and exhibiting it as a universe lift needs the lift to commute with
sheafification and with that coproduct, hence needs the site to be small relative to the smaller
coefficient universe. That is not a defect of the route: the regime where the hypothesis fails is
the regime where `Sheaf J AddCommGrpCat.{t}` is not a Grothendieck abelian category, so it has no
known injective objects to lift in the first place.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open ZeroObject

universe z s t v u

namespace Stacks.Sheaves.UniverseLift

variable {C : Type u} [Category.{v} C]

section Presheaves

variable {Y : Cᵒᵖ ⥤ AddCommGrpCat.{t}} {S : Cᵒᵖ ⥤ AddCommGrpCat.{max t s}}
  (α : S ⟶ Y ⋙ AddCommGrpCat.uliftFunctor.{s, t})

/-- The map on sections of `α : S ⟶ Y ⋙ uliftFunctor` with the universe lift of its target
removed. -/
def uliftDescentHom (U : Cᵒᵖ) : S.obj U →+ Y.obj U :=
  (AddEquiv.ulift (α := (Y.obj U : Type t))).toAddMonoidHom.comp (α.app U).hom

/-- `uliftDescentHom α U x` is the element of `Y.obj U` underlying `α.app U x`. -/
@[simp]
lemma uliftDescentHom_apply (U : Cᵒᵖ) (x : S.obj U) :
    uliftDescentHom α U x = (α.app U x).down := rfl

/-- The maps `uliftDescentHom α` commute with the restriction maps of `S` and `Y`. -/
lemma uliftDescentHom_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (x : S.obj U) :
    uliftDescentHom α V (S.map f x) = Y.map f (uliftDescentHom α U x) :=
  congrArg ULift.down (ConcreteCategory.congr_hom (α.naturality f) x)

/-- The sections of `S` realised as a subgroup of the sections of `Y`. -/
def uliftDescentSubgroup (U : Cᵒᵖ) : AddSubgroup (Y.obj U) := (uliftDescentHom α U).range

/-- The restriction maps of `Y` carry the subgroups `uliftDescentSubgroup α` into each other. -/
lemma uliftDescentSubgroup_mem {U V : Cᵒᵖ} (f : U ⟶ V) {y : Y.obj U}
    (hy : y ∈ uliftDescentSubgroup α U) : Y.map f y ∈ uliftDescentSubgroup α V := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨S.map f x, uliftDescentHom_naturality α f x⟩

/-- The presheaf of abelian groups in the smaller universe whose universe lift is `S`, when `α`
is injective on sections: the subgroups of sections of `Y` cut out by `α`. -/
def uliftDescent : Cᵒᵖ ⥤ AddCommGrpCat.{t} where
  obj U := AddCommGrpCat.of (uliftDescentSubgroup α U)
  map {U _} f := AddCommGrpCat.ofHom
    { toFun := fun x ↦ ⟨Y.map f (x : Y.obj U), uliftDescentSubgroup_mem α f x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b ↦ Subtype.ext (by simp) }
  map_id U := by
    ext x
    exact congrArg (fun g : Y.obj U ⟶ Y.obj U ↦ (ConcreteCategory.hom g) (x : Y.obj U))
      (Y.map_id U)
  map_comp {U _ W} f g := by
    ext x
    exact congrArg (fun h : Y.obj U ⟶ Y.obj W ↦ (ConcreteCategory.hom h) (x : Y.obj U))
      (Y.map_comp f g)

/-- The inclusion of `uliftDescent α` into `Y`. -/
def uliftDescentInclusion : uliftDescent α ⟶ Y where
  app U := AddCommGrpCat.ofHom (uliftDescentSubgroup α U).subtype
  naturality _ _ _ := by
    ext x
    rfl

/-- The inclusion of `uliftDescent α` into `Y` is injective on sections. -/
lemma uliftDescentInclusion_injective (U : Cᵒᵖ) :
    Function.Injective ((uliftDescentInclusion α).app U) := fun _ _ h ↦ Subtype.ext h

variable (hα : ∀ U, Function.Injective (α.app U))

include hα

/-- If `α` is injective on sections, then so is `uliftDescentHom α`. -/
lemma uliftDescentHom_injective (U : Cᵒᵖ) : Function.Injective (uliftDescentHom α U) :=
  fun _ _ h ↦ hα U (ULift.down_injective h)

/-- The sections of `S` are the universe lift of the subgroup `uliftDescentSubgroup α`. -/
def uliftDescentEquiv (U : Cᵒᵖ) :
    (S.obj U : Type (max t s)) ≃+
      ((uliftDescent α ⋙ AddCommGrpCat.uliftFunctor.{s, t}).obj U) :=
  (AddMonoidHom.ofInjective (uliftDescentHom_injective α hα U)).trans
    (AddEquiv.ulift (α := (uliftDescentSubgroup α U : Type t))).symm

/-- `S` is the universe lift of `uliftDescent α`. -/
def uliftDescentIso : S ≅ uliftDescent α ⋙ AddCommGrpCat.uliftFunctor.{s, t} :=
  NatIso.ofComponents (fun U ↦ (uliftDescentEquiv α hα U).toAddCommGrpIso) fun f ↦ by
    ext x
    exact ULift.down_injective (Subtype.ext (uliftDescentHom_naturality α f x))

/-- The isomorphism `uliftDescentIso α hα` followed by the universe lift of
`uliftDescentInclusion α` is `α`. -/
lemma uliftDescentIso_hom_comp :
    (uliftDescentIso α hα).hom ≫
        Functor.whiskerRight (uliftDescentInclusion α)
          AddCommGrpCat.uliftFunctor.{s, t} = α := by
  ext U x
  exact ULift.down_injective rfl

/-- If `S` is a sheaf and `α` is injective on sections, then `uliftDescent α` is a sheaf. -/
lemma isSheaf_uliftDescent (J : GrothendieckTopology C) (hS : Presheaf.IsSheaf J S) :
    Presheaf.IsSheaf J (uliftDescent α) :=
  Presheaf.isSheaf_of_isSheaf_comp J _ AddCommGrpCat.uliftFunctor.{s, t}
    ((Presheaf.isSheaf_of_iso_iff (uliftDescentIso α hα)).1 hS)

end Presheaves

section Sheaves

variable (J : GrothendieckTopology C)

/-- The universe lift of abelian sheaves: raising the universe of all groups of sections. -/
abbrev uliftSheafFunctor :
    Sheaf J AddCommGrpCat.{t} ⥤ Sheaf J AddCommGrpCat.{max t s} :=
  sheafCompose J AddCommGrpCat.uliftFunctor.{s, t}

/-- The universe lift of abelian sheaves is fully faithful. -/
def fullyFaithfulUliftSheafFunctor : (uliftSheafFunctor.{s, t} J).FullyFaithful :=
  fullyFaithfulSheafCompose J AddCommGrpCat.uliftFunctorFullyFaithful

/-- **A monomorphism into the universe lift of an abelian sheaf is the universe lift of a
monomorphism of abelian sheaves in the smaller universe.** -/
theorem exists_uliftDescent {Y : Sheaf J AddCommGrpCat.{t}}
    {S : Sheaf J AddCommGrpCat.{max t s}} (i : S ⟶ (uliftSheafFunctor.{s} J).obj Y) [Mono i] :
    ∃ (S' : Sheaf J AddCommGrpCat.{t}) (i' : S' ⟶ Y) (_ : Mono i')
      (e : (uliftSheafFunctor.{s} J).obj S' ≅ S),
      e.hom ≫ i = (uliftSheafFunctor.{s} J).map i' := by
  have : Mono i.hom :=
    inferInstanceAs (Mono ((sheafToPresheaf J AddCommGrpCat.{max t s}).map i))
  have hα : ∀ U, Function.Injective (i.hom.app U) := fun U ↦
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  refine ⟨⟨uliftDescent i.hom, isSheaf_uliftDescent i.hom hα J S.property⟩,
    ObjectProperty.homMk (uliftDescentInclusion i.hom), ?_,
    ((fullyFaithfulSheafToPresheaf J AddCommGrpCat.{max t s}).preimageIso
      (uliftDescentIso i.hom hα).symm), ?_⟩
  · have hmono : Mono (uliftDescentInclusion i.hom) := by
      rw [NatTrans.mono_iff_mono_app]
      exact fun U ↦ (AddCommGrpCat.mono_iff_injective _).2
        (uliftDescentInclusion_injective i.hom U)
    exact (sheafToPresheaf J AddCommGrpCat.{t}).mono_of_mono_map hmono
  · exact Sheaf.hom_ext ((Iso.inv_comp_eq _).mpr (uliftDescentIso_hom_comp i.hom hα).symm)

variable [HasSheafify J AddCommGrpCat.{max t s}]
  [IsGrothendieckAbelian.{z} (Sheaf J AddCommGrpCat.{max t s})]
  {G : Sheaf J AddCommGrpCat.{t}}

/-- **The universe lift of an injective abelian sheaf is injective**, provided the larger sheaf
category has a separator which is itself a universe lift. -/
theorem injective_uliftSheafFunctor_obj
    (hG : IsSeparator ((uliftSheafFunctor.{s} J).obj G))
    (I : Sheaf J AddCommGrpCat.{t}) [Injective I] :
    Injective ((uliftSheafFunctor.{s} J).obj I) := by
  rw [injective_iff_rlp_monomorphisms_zero,
    ← IsGrothendieckAbelian.generatingMonomorphisms_rlp hG]
  rintro A B i ⟨T⟩
  obtain ⟨T', i', _, e, he⟩ := exists_uliftDescent J T.arrow
  have key : HasLiftingProperty ((uliftSheafFunctor.{s} J).map i')
      (0 : (uliftSheafFunctor.{s} J).obj I ⟶ 0) := by
    refine ⟨fun {f _} _ ↦ ⟨⟨{
      l := (uliftSheafFunctor.{s} J).map (Injective.factorThru
        ((fullyFaithfulUliftSheafFunctor.{s, t} J).preimage f) i')
      fac_left := ?_
      fac_right := (isZero_zero _).eq_of_tgt _ _ }⟩⟩⟩
    rw [← Functor.map_comp, Injective.comp_factorThru]
    exact (fullyFaithfulUliftSheafFunctor.{s, t} J).map_preimage f
  have e' : Arrow.mk ((uliftSheafFunctor.{s} J).map i') ≅ Arrow.mk (Subobject.arrow T) :=
    Arrow.isoMk e (Iso.refl _) (he.trans (Category.comp_id _).symm)
  exact (HasLiftingProperty.iff_of_arrow_iso_left e' _).1 key

/-- **The universe lift of abelian sheaves preserves injective objects**, provided the larger
sheaf category has a separator which is itself a universe lift. -/
theorem preservesInjectiveObjects_uliftSheafFunctor
    (hG : IsSeparator ((uliftSheafFunctor.{s} J).obj G)) :
    (uliftSheafFunctor.{s, t} J).PreservesInjectiveObjects where
  injective_obj {X} _ := injective_uliftSheafFunctor_obj J hG X

end Sheaves

end Stacks.Sheaves.UniverseLift

end
