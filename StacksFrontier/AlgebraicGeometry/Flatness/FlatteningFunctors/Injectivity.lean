module

public import Mathlib.CategoryTheory.Widesubcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FlatPullbackStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.ModuleMapBaseChange

/-!
# The injectivity functor of a base-changed homomorphism of quasi-coherent modules

Let `f : X ⟶ S` be a morphism of schemes and let `u : F ⟶ G` be a homomorphism of
quasi-coherent modules on `X`.  Besides the three conditions on the base change `u_T` treated
in `StacksFrontier.AlgebraicGeometry.Flatness.ModuleMapBaseChange` — being an isomorphism, an
epimorphism, or zero — there is a fourth: being a monomorphism.  It differs from the others in
that it is stable only under a *flat* further base change, because the pullback functor on
modules is right exact for every morphism but left exact only for a flat one.

Accordingly the injectivity condition defines a subterminal functor on the category of schemes
over `S` whose morphisms are the *flat* morphisms over `S`, which is Mathlib's
`CategoryTheory.WideSubcategory` for the morphism property "flat after forgetting the
structure morphism".

If `u` is an epimorphism then its base change is too, so for a surjective `u` injectivity after
base change coincides with being an isomorphism after base change; in that case the injectivity
functor extends to all of `Over S` and is isomorphic to the isomorphism functor.

## Main definitions

* `Stacks.Flatness.ModuleMapBaseChangeSituation.IsInjectiveAfterBaseChange` is the fourth
  condition.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.FlatMorphismOver` and
  `Stacks.Flatness.ModuleMapBaseChangeSituation.FlatOver` are the morphism property of being
  flat over the base and the resulting category.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.injectivityFunctor` is the injectivity functor
  on that category, and
  `Stacks.Flatness.ModuleMapBaseChangeSituation.injectivityFunctorOfEpi` is its extension to
  all schemes over the base when the homomorphism is surjective.

## Main results

* `Stacks.Flatness.ModuleMapBaseChangeSituation.isInjectiveAfterBaseChange_of_flat_hom`:
  injectivity after base change is stable under a flat further base change.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.injectivityFunctorOfEpiRestrictionIso` and
  `Stacks.Flatness.ModuleMapBaseChangeSituation.injectivityFunctorOfEpiIsoIsomorphismFunctor`
  identify the extended functor with the original one and with the isomorphism functor.

## Implementation notes

Left exactness of the pullback functor along a flat morphism is not used in the form
`CategoryTheory.Limits.PreservesFiniteLimits`; what is needed is only that it preserves
monomorphisms, and that is
`AlgebraicGeometry.Scheme.Modules.mono_pullback_map_of_flat`, proved stalkwise.

## References

* [Stacks Project, Tag 05MH](https://stacks.math.columbia.edu/tag/05MH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

/-- The condition that the base-changed homomorphism is injective. -/
@[stacks 05MH "the injectivity condition"]
abbrev IsInjectiveAfterBaseChange (D : ModuleMapBaseChangeSituation.{u}) (T : Over D.S) : Prop :=
  Mono (D.baseChangeMap T)

/-- The morphism property on `Over S` consisting of the morphisms whose underlying morphism of
schemes is flat. -/
abbrev FlatMorphismOver (S : Scheme.{u}) : MorphismProperty (Over S) :=
  MorphismProperty.inverseImage (@AlgebraicGeometry.Flat : MorphismProperty Scheme.{u})
    (Over.forget S)

/-- Flatness over the base contains the identities and is stable under composition. -/
@[ega "0 6.7.5" "Schemes over a base S", ega "IV 2.1.6" "more general"]
instance flatMorphismOver_isMultiplicative (S : Scheme.{u}) :
    (FlatMorphismOver S).IsMultiplicative :=
  MorphismProperty.IsMultiplicative.instInverseImage
    (P := (@AlgebraicGeometry.Flat : MorphismProperty Scheme.{u})) (Over.forget S)

/-- The category of schemes over `S` whose morphisms are only the flat ones. -/
@[stacks 05MH "the category with flat morphisms"]
abbrev FlatOver (S : Scheme.{u}) := WideSubcategory (FlatMorphismOver S)

/-- Being injective after base change is preserved by every *flat* further base change: the
transition morphism of base changes is then flat, so pulling back along it preserves
monomorphisms, and the comparison isomorphism carries the base-changed homomorphism over `T`
to the one over `T'`. -/
@[stacks 05MH "functoriality of the injectivity condition"]
theorem isInjectiveAfterBaseChange_of_flat_hom (D : ModuleMapBaseChangeSituation.{u})
    {T T' : Over D.S} (g : T' ⟶ T) (hg : Flat g.left)
    (h : D.IsInjectiveAfterBaseChange T) : D.IsInjectiveAfterBaseChange T' := by
  have hq : Flat (D.baseChangeTransition g) := D.baseChangeTransition_flat g hg
  have hmap : Mono
      ((Scheme.Modules.pullback (D.baseChangeTransition g)).map (D.baseChangeMap T)) :=
    Scheme.Modules.mono_pullback_map_of_flat (D.baseChangeTransition g) (D.baseChangeMap T) h
  have hiso : IsIso ((D.baseChangeTransitionIso g).hom.app D.G) := inferInstance
  have hcomp : Mono ((D.baseChangeTransitionIso g).hom.app D.F ≫ D.baseChangeMap T') := by
    rw [D.baseChangeMap_transition_naturality g]
    exact mono_comp _ _
  exact (MorphismProperty.cancel_left_of_respectsIso
    (MorphismProperty.monomorphisms _) _ _).mp hcomp

/-- The subterminal functor on schemes over the base with flat transition morphisms recording
where the base-changed homomorphism is injective. -/
@[stacks 05MH "the injectivity functor"]
noncomputable def injectivityFunctor (D : ModuleMapBaseChangeSituation.{u}) :
    (FlatOver D.S)ᵒᵖ ⥤ Type where
  obj T := PLift (D.IsInjectiveAfterBaseChange T.unop.obj)
  map g := ↾fun h ↦
    ⟨D.isInjectiveAfterBaseChange_of_flat_hom g.unop.hom g.unop.property h.down⟩
  map_id T := by ext h; exact Subsingleton.elim _ _
  map_comp g h := by ext x; exact Subsingleton.elim _ _

/-- If the homomorphism is surjective then its base change is both injective and surjective
whenever it is injective, hence an isomorphism, and being an isomorphism after base change is
stable under an arbitrary further base change. -/
@[stacks 05MH "unrestricted functoriality of injectivity for a surjection"]
theorem isInjectiveAfterBaseChange_of_hom_of_epi (D : ModuleMapBaseChangeSituation.{u})
    [Epi D.hom] {T T' : Over D.S} (g : T' ⟶ T) (h : D.IsInjectiveAfterBaseChange T) :
    D.IsInjectiveAfterBaseChange T' := by
  have hepi : Epi (D.baseChangeMap T) := by
    have : PreservesColimitsOfSize.{0, 0}
        (Scheme.Modules.pullback (pullback.fst D.f T.hom)) :=
      (Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.fst D.f T.hom)).leftAdjoint_preservesColimits
    exact preserves_epi_of_preservesColimit _ _
  have hmono : Mono (D.baseChangeMap T) := h
  have : IsIso (D.baseChangeMap T') :=
    D.isIsomorphismAfterBaseChange_of_hom g (isIso_of_mono_of_epi _)
  infer_instance

/-- For a surjective homomorphism, injectivity after base change defines a subterminal functor
on all schemes over the base. -/
@[stacks 05MH "the unrestricted injectivity functor for a surjection"]
noncomputable def injectivityFunctorOfEpi (D : ModuleMapBaseChangeSituation.{u}) [Epi D.hom] :
    (Over D.S)ᵒᵖ ⥤ Type where
  obj T := PLift (D.IsInjectiveAfterBaseChange T.unop)
  map g := ↾fun h ↦ ⟨D.isInjectiveAfterBaseChange_of_hom_of_epi g.unop h.down⟩
  map_id T := by ext h; exact Subsingleton.elim _ _
  map_comp g h := by ext x; exact Subsingleton.elim _ _

/-- The unrestricted injectivity functor of a surjection restricts along the inclusion of the
category with flat morphisms to the injectivity functor. -/
@[stacks 05MH "restriction of the unrestricted injectivity functor"]
noncomputable def injectivityFunctorOfEpiRestrictionIso (D : ModuleMapBaseChangeSituation.{u})
    [Epi D.hom] :
    (wideSubcategoryInclusion (FlatMorphismOver D.S)).op ⋙ D.injectivityFunctorOfEpi ≅
      D.injectivityFunctor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro T T' g; ext x; cases x; rfl)

/-- For a surjective homomorphism the unrestricted injectivity functor is the isomorphism
functor: a surjection that is injective after base change is an isomorphism after base change,
and conversely. -/
@[stacks 05MH "injectivity equals isomorphism for a surjection"]
noncomputable def injectivityFunctorOfEpiIsoIsomorphismFunctor
    (D : ModuleMapBaseChangeSituation.{u}) [Epi D.hom] :
    D.injectivityFunctorOfEpi ≅ D.isomorphismFunctor := by
  have hiff : ∀ T : Over D.S,
      D.IsInjectiveAfterBaseChange T ↔ D.IsIsomorphismAfterBaseChange T := by
    intro T
    have hepi : Epi (D.baseChangeMap T) := by
      have : PreservesColimitsOfSize.{0, 0}
          (Scheme.Modules.pullback (pullback.fst D.f T.hom)) :=
        (Scheme.Modules.pullbackPushforwardAdjunction
          (pullback.fst D.f T.hom)).leftAdjoint_preservesColimits
      exact preserves_epi_of_preservesColimit _ _
    refine ⟨fun hm ↦ ?_, fun hi ↦ ?_⟩
    · have : Mono (D.baseChangeMap T) := hm
      exact isIso_of_mono_of_epi _
    · have : IsIso (D.baseChangeMap T) := hi
      infer_instance
  exact NatIso.ofComponents
    (fun T ↦ ({ toFun := fun x ↦ ⟨(hiff T.unop).mp x.down⟩
                invFun := fun x ↦ ⟨(hiff T.unop).mpr x.down⟩
                left_inv := fun _ ↦ Subsingleton.elim _ _
                right_inv := fun _ ↦ Subsingleton.elim _ _ } :
        PLift (D.IsInjectiveAfterBaseChange T.unop) ≃
          PLift (D.IsIsomorphismAfterBaseChange T.unop)).toIso)
    (by intro T T' g; ext x; cases x; rfl)

end Stacks.Flatness.ModuleMapBaseChangeSituation

end
