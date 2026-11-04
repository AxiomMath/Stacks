module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.BaseChangeTransition

/-!
# Base change of a homomorphism of quasi-coherent modules, as a functor on the base

Let `f : X ⟶ S` be a morphism of schemes and let `u : F ⟶ G` be a homomorphism of
quasi-coherent modules on `X`.  For a scheme `T` over `S` write `X_T = X ×_S T` and let `u_T` be
the pullback of `u` along the projection `X_T ⟶ X`.  The Stacks Project
([Stacks, Tag 05MH](https://stacks.math.columbia.edu/tag/05MH)) attaches to this data the
subfunctors of the final functor on `(Over S)ᵒᵖ` recording, for each `T`, whether `u_T` is an
isomorphism, an epimorphism, or zero.

These three assignments are functors: each of the three conditions is stable under a further
base change `T' ⟶ T`. A morphism `g : T' ⟶ T` over `S` induces `X_{T'} ⟶ X_T`, and the pullback
of `u` to `X_{T'}` is identified, naturally in the module, with the pullback along
`X_{T'} ⟶ X_T` of `u_T`. Pulling back carries isomorphisms to isomorphisms; being a left adjoint
it carries epimorphisms to epimorphisms; and being additive it carries the zero map to the zero
map.

Injectivity is not treated here: it is stable only under flat further base change (see the
implementation notes).

## Main definitions

* `Stacks.Flatness.ModuleMapBaseChangeSituation` is the standing data: a morphism of schemes and
  a homomorphism of quasi-coherent modules on its source.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.baseChangeMap` is the pullback of the
  homomorphism to `X ×_S T`.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.IsIsomorphismAfterBaseChange`,
  `IsSurjectiveAfterBaseChange` and `IsZeroAfterBaseChange` are the three conditions.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.baseChangeTransition` is the morphism
  `X ×_S T' ⟶ X ×_S T` induced by a morphism `T' ⟶ T` over `S`.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.isomorphismFunctor`, `surjectivityFunctor` and
  `zeroFunctor` are the resulting subterminal functors on `(Over S)ᵒᵖ`.

## Main results

* `Stacks.Flatness.ModuleMapBaseChangeSituation.baseChangeMap_transition_naturality`: up to the
  comparison isomorphism, the pullback of `u_T` along `X_{T'} ⟶ X_T` is `u_{T'}`.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.isIsomorphismAfterBaseChange_of_hom`,
  `isSurjectiveAfterBaseChange_of_hom` and `isZeroAfterBaseChange_of_hom` are the three
  stability statements.

## Implementation notes

The values of the three functors are `PLift` of a proposition, so they land in `Type 0` while
the morphisms of `Over S` live in `Type u`, as `Stacks.Flatness.representableByIso` allows.

`baseChangeTransition` is `Stacks.BaseChange.transition` of the structure morphism; only the
fact that its composite with the first projection is the first projection of the other base
change is used here.

`AlgebraicGeometry.baseChangeTransition` is the same construction for the *opposite* order of
the two factors: it goes `pullback g' X.hom ⟶ pullback g X.hom` with the base in the first
slot, while the situation here fixes `pullback f T.hom` with the base in the second, so that
the first projection is the one along which the module is pulled back. Rewriting this file in
that vocabulary would put a `CategoryTheory.Limits.pullbackSymmetry` under every module
pullback; the two conventions are not interchangeable.

The missing fourth condition is injectivity.  Stability of `Mono (u_T)` under a further base
change `g` needs `PreservesFiniteLimits (Scheme.Modules.pullback q)` for the induced
`q : X_{T'} ⟶ X_T`, which holds when `g` is flat because `q` is then flat as a base change of
`g`. That flatness of a morphism of schemes makes the module pullback functor exact is not yet
available.

## References

* [Stacks Project, Tag 05MH](https://stacks.math.columbia.edu/tag/05MH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Flatness

/-- The standing data for testing a homomorphism of quasi-coherent modules after an arbitrary
base change: a morphism of schemes `f : X ⟶ S`, two quasi-coherent modules on `X`, and a
homomorphism between them. -/
@[stacks 05MH "the situation"]
structure ModuleMapBaseChangeSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The structure morphism. -/
  f : X ⟶ S
  /-- The source module. -/
  F : X.Modules
  /-- The target module. -/
  G : X.Modules
  /-- The homomorphism whose base changes are tested. -/
  hom : F ⟶ G
  [isQuasicoherentF : F.IsQuasicoherent]
  [isQuasicoherentG : G.IsQuasicoherent]

namespace ModuleMapBaseChangeSituation

attribute [instance] isQuasicoherentF isQuasicoherentG

/-- The base change `X ×_S T` of the source along a scheme `T` over the base. -/
@[stacks 05MH "the base-changed scheme"]
noncomputable abbrev baseChange (D : ModuleMapBaseChangeSituation.{u}) (T : Over D.S) :
    Scheme.{u} :=
  pullback D.f T.hom

/-- The pullback of the module homomorphism to `X ×_S T`. -/
@[stacks 05MH "the base-changed homomorphism"]
noncomputable def baseChangeMap (D : ModuleMapBaseChangeSituation.{u}) (T : Over D.S) :
    (Scheme.Modules.pullback (pullback.fst D.f T.hom)).obj D.F ⟶
      (Scheme.Modules.pullback (pullback.fst D.f T.hom)).obj D.G :=
  (Scheme.Modules.pullback (pullback.fst D.f T.hom)).map D.hom

/-- The condition that the base-changed homomorphism is an isomorphism. -/
@[stacks 05MH "the isomorphism condition"]
abbrev IsIsomorphismAfterBaseChange (D : ModuleMapBaseChangeSituation.{u}) (T : Over D.S) :
    Prop :=
  IsIso (D.baseChangeMap T)

/-- The condition that the base-changed homomorphism is surjective. -/
@[stacks 05MH "the surjectivity condition"]
abbrev IsSurjectiveAfterBaseChange (D : ModuleMapBaseChangeSituation.{u}) (T : Over D.S) :
    Prop :=
  Epi (D.baseChangeMap T)

/-- The condition that the base-changed homomorphism is zero. -/
@[stacks 05MH "the zero condition"]
abbrev IsZeroAfterBaseChange (D : ModuleMapBaseChangeSituation.{u}) (T : Over D.S) : Prop :=
  D.baseChangeMap T = 0

/-- The morphism `X ×_S T' ⟶ X ×_S T` of base changes induced by a morphism `T' ⟶ T` over the
base. -/
noncomputable abbrev baseChangeTransition (D : ModuleMapBaseChangeSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T) : D.baseChange T' ⟶ D.baseChange T :=
  Stacks.BaseChange.transition D.f g

/-- The transition morphism of base changes is compatible with the projections to `X`. -/
@[simp]
theorem baseChangeTransition_comp_fst (D : ModuleMapBaseChangeSituation.{u}) {T T' : Over D.S}
    (g : T' ⟶ T) :
    D.baseChangeTransition g ≫ pullback.fst D.f T.hom = pullback.fst D.f T'.hom :=
  Stacks.BaseChange.transition_comp_fst D.f g

/-- The square formed by the transition morphism of base changes, the two projections to the
schemes over the base, and the given morphism over the base is cartesian: `X ×_S T'` is
`(X ×_S T) ×_T T'`. -/
theorem baseChangeTransition_isPullback (D : ModuleMapBaseChangeSituation.{u}) {T T' : Over D.S}
    (g : T' ⟶ T) :
    IsPullback (D.baseChangeTransition g) (pullback.snd D.f T'.hom)
      (pullback.snd D.f T.hom) g.left :=
  Stacks.BaseChange.transition_isPullback D.f g

/-- The transition morphism of base changes induced by a *flat* morphism over the base is flat,
being a base change of it. -/
theorem baseChangeTransition_flat (D : ModuleMapBaseChangeSituation.{u}) {T T' : Over D.S}
    (g : T' ⟶ T) (hg : Flat g.left) : Flat (D.baseChangeTransition g) :=
  Stacks.BaseChange.transition_flat D.f g hg

/-- The comparison isomorphism between pulling the module back to `X ×_S T'` in one step and
pulling it back to `X ×_S T` and then along the transition morphism. -/
noncomputable def baseChangeTransitionIso (D : ModuleMapBaseChangeSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T) :
    Scheme.Modules.pullback (pullback.fst D.f T.hom) ⋙
        Scheme.Modules.pullback (D.baseChangeTransition g) ≅
      Scheme.Modules.pullback (pullback.fst D.f T'.hom) :=
  Scheme.Modules.pullbackComp (D.baseChangeTransition g) (pullback.fst D.f T.hom) ≪≫
    Scheme.Modules.pullbackCongr (D.baseChangeTransition_comp_fst g)

/-- The comparison isomorphism carries the base change of the homomorphism to `X ×_S T` along
the transition morphism to its base change to `X ×_S T'`. -/
theorem baseChangeMap_transition_naturality (D : ModuleMapBaseChangeSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T) :
    (D.baseChangeTransitionIso g).hom.app D.F ≫ D.baseChangeMap T' =
      (Scheme.Modules.pullback (D.baseChangeTransition g)).map (D.baseChangeMap T) ≫
        (D.baseChangeTransitionIso g).hom.app D.G :=
  ((D.baseChangeTransitionIso g).hom.naturality D.hom).symm

/-- Being an isomorphism after base change is preserved by every further base change. -/
@[stacks 05MH "functoriality of the isomorphism condition"]
theorem isIsomorphismAfterBaseChange_of_hom (D : ModuleMapBaseChangeSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T) (h : D.IsIsomorphismAfterBaseChange T) :
    D.IsIsomorphismAfterBaseChange T' := by
  have : IsIso (D.baseChangeMap T) := h
  refine (isIso_comp_left_iff ((D.baseChangeTransitionIso g).hom.app D.F) _).1 ?_
  rw [D.baseChangeMap_transition_naturality g]
  infer_instance

/-- Being surjective after base change is preserved by every further base change. -/
@[stacks 05MH "functoriality of the surjectivity condition"]
theorem isSurjectiveAfterBaseChange_of_hom (D : ModuleMapBaseChangeSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T) (h : D.IsSurjectiveAfterBaseChange T) :
    D.IsSurjectiveAfterBaseChange T' := by
  have : Epi (D.baseChangeMap T) := h
  refine (epi_comp_iff_of_epi ((D.baseChangeTransitionIso g).hom.app D.F) _).1 ?_
  rw [D.baseChangeMap_transition_naturality g]
  infer_instance

/-- Being zero after base change is preserved by every further base change. -/
@[stacks 05MH "functoriality of the zero condition"]
theorem isZeroAfterBaseChange_of_hom (D : ModuleMapBaseChangeSituation.{u}) {T T' : Over D.S}
    (g : T' ⟶ T) (h : D.IsZeroAfterBaseChange T) : D.IsZeroAfterBaseChange T' := by
  refine (cancel_epi ((D.baseChangeTransitionIso g).hom.app D.F)).1 ?_
  rw [D.baseChangeMap_transition_naturality g, h]
  simp

/-- The subterminal functor on schemes over the base recording where the base-changed
homomorphism is an isomorphism. -/
@[stacks 05MH "the isomorphism functor"]
noncomputable def isomorphismFunctor (D : ModuleMapBaseChangeSituation.{u}) :
    (Over D.S)ᵒᵖ ⥤ Type where
  obj T := PLift (D.IsIsomorphismAfterBaseChange T.unop)
  map g := ↾fun h ↦ ⟨D.isIsomorphismAfterBaseChange_of_hom g.unop h.down⟩
  map_id T := by ext h; exact Subsingleton.elim _ _
  map_comp g h := by ext x; exact Subsingleton.elim _ _

/-- The subterminal functor on schemes over the base recording where the base-changed
homomorphism is surjective. -/
@[stacks 05MH "the surjectivity functor"]
noncomputable def surjectivityFunctor (D : ModuleMapBaseChangeSituation.{u}) :
    (Over D.S)ᵒᵖ ⥤ Type where
  obj T := PLift (D.IsSurjectiveAfterBaseChange T.unop)
  map g := ↾fun h ↦ ⟨D.isSurjectiveAfterBaseChange_of_hom g.unop h.down⟩
  map_id T := by ext h; exact Subsingleton.elim _ _
  map_comp g h := by ext x; exact Subsingleton.elim _ _

/-- The subterminal functor on schemes over the base recording where the base-changed
homomorphism is zero. -/
@[stacks 05MH "the zero functor"]
noncomputable def zeroFunctor (D : ModuleMapBaseChangeSituation.{u}) :
    (Over D.S)ᵒᵖ ⥤ Type where
  obj T := PLift (D.IsZeroAfterBaseChange T.unop)
  map g := ↾fun h ↦ ⟨D.isZeroAfterBaseChange_of_hom g.unop h.down⟩
  map_id T := by ext h; exact Subsingleton.elim _ _
  map_comp g h := by ext x; exact Subsingleton.elim _ _

/-- Every value of the isomorphism functor has at most one element. -/
instance isomorphismFunctor_obj_subsingleton (D : ModuleMapBaseChangeSituation.{u})
    (T : (Over D.S)ᵒᵖ) : Subsingleton (D.isomorphismFunctor.obj T) :=
  inferInstanceAs (Subsingleton (PLift (D.IsIsomorphismAfterBaseChange T.unop)))

/-- The isomorphism functor has a section over `T` exactly when the base-changed homomorphism is
an isomorphism. -/
@[simp]
theorem isomorphismFunctor_obj_nonempty_iff (D : ModuleMapBaseChangeSituation.{u})
    (T : Over D.S) :
    Nonempty (D.isomorphismFunctor.obj (op T)) ↔ D.IsIsomorphismAfterBaseChange T :=
  ⟨fun ⟨⟨h⟩⟩ ↦ h, fun h ↦ ⟨⟨h⟩⟩⟩

end ModuleMapBaseChangeSituation

end Stacks.Flatness

end
