module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# The two composition comparisons of Stacks 03LU are the same comparison

Stacks 03LU attaches to a morphism `f : X ⟶ Y` of algebraic spaces the adjoint pair `(f^*, f_*)`
on `𝒪`-modules together with the comparisons `f_* ∘ g_* ≅ (f ≫ g)_*` and `g^* ∘ f^* ≅ (f ≫ g)^*`
for a composable pair.  This development builds those comparisons twice, by two routes through
the same two ingredients — the composition law for the direct image of modules along a composite
*morphism of ringed topoi* and the transport of the direct image along Stacks 03G8's cartesian
comparison of the direct images of sheaves of sets.  The routes differ only in which of the two
constructors of the transport they use:
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso`, which takes a 2-isomorphism of
morphisms of ringed topoi, or
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfPushforwardIso`, which takes the
comparison of the direct images of sheaves of sets together with the induced comparison of the
direct images of the structure sheaf of rings.

This file identifies the two, so that the coherences proved for one are available for the other.
In particular the associativity coherence of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompIsoAssoc.lean`, proved there
for `AlgebraicGeometry.Space.modulePullbackCompIso`, holds verbatim for
`AlgebraicGeometry.Space.modulePullbackCompIso`, which is the comparison the conormal
constructions are built on.

## Main results

* In the namespace `AlgebraicGeometry.RingedToposHom`,
  `pushforwardModulesIsoOfNatIso_eq_pushforwardModulesIsoOfPushforwardIso`: the two constructors
  of the transport agree whenever they are fed the same geometric comparison, the comparison of
  the structure sheaves of rings being the one the geometric comparison induces.
* `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_modulePushforwardCompIso'`: the two
  comparisons of direct images agree, after the identification of the direct image of modules of
  the morphism of ringed topoi with the direct image of modules along the morphism itself.

## Implementation notes

Both identifications are proved on underlying sheaves of sets, where
`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor` makes the two sides equal as soon
as their underlying morphisms of sheaves of sets agree.  For the transport read through the
2-isomorphism of morphisms of ringed topoi that underlying morphism is the geometric comparison
by a definitional identity.  For the transport read through the comparison of the direct images
of sheaves of sets it is not: that transport is a whiskered comparison of inverse images followed
by a transport along an equality of functors, and
`moduleSheafFunctor_map_pushforwardModulesIsoOfPushforwardIso_hom_app` evaluates it by splitting
the two factors, the first being the geometric comparison definitionally and the second becoming
an identity because restriction of scalars does not change the underlying sheaf of sets.  The
ring sheaf is named
`AlgebraicGeometry.Space.structureRingSheaf` in that step: the two spellings of it are reconciled
only by unfolding semireducible definitions, so the one the ambient lemmas use must be supplied
rather than inferred.

The identification of the two comparisons of direct images is stated with the two `eqToIso`
factors of `AlgebraicGeometry.Space.modulePushforwardCompIso` on the right-hand side rather than
collapsed.  Collapsing them is a separate matter — it is a property of `eqToHom` at these types,
recorded at the end of the equations section of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` — and nothing here needs
it, since both comparisons carry the same two factors and only the middle factor differs.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (hom_ext_moduleSheafFunctor)

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  (F H : RingedToposHom X Y)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})] in
/-- Restricting scalars along the structure map of one morphism of ringed topoi after the
comparison of the direct images of the structure sheaf of rings is the direct image of modules
of the other morphism. -/
private theorem restrictScalars_comp_eq_pushforwardModules
    (β : pullbackRingSheaf Y.J F.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⟶
      pullbackRingSheaf Y.J H.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    (hstruct : F.structureRingMap ≫ β = H.structureRingMap) :
    (pullbackModuleFunctor Y.J H.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
          SheafOfModules.restrictScalars β) ⋙
        SheafOfModules.restrictScalars F.structureRingMap = H.pushforwardModules := by
  have h1 : (pullbackModuleFunctor Y.J H.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
          SheafOfModules.restrictScalars β) ⋙
        SheafOfModules.restrictScalars F.structureRingMap =
      pullbackModuleFunctor Y.J H.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        SheafOfModules.restrictScalars (F.structureRingMap ≫ β) := rfl
  have h3 : pullbackModuleFunctor Y.J H.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        SheafOfModules.restrictScalars H.structureRingMap = H.pushforwardModules := rfl
  exact h1.trans ((congrArg (fun α ↦ pullbackModuleFunctor Y.J H.toToposHom.pushforward
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
      SheafOfModules.restrictScalars α) hstruct).trans h3)

/-- The transport of the direct image of sheaves of modules built from a comparison of the
direct images of sheaves of sets is that comparison on underlying sheaves of sets.  Neither the
whiskered comparison of inverse images nor the transport along the equality of the two direct
images changes the underlying sheaf of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesIsoOfPushforwardIso_hom_app
    (θ : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (β : pullbackRingSheaf Y.J F.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⟶
      pullbackRingSheaf Y.J H.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    (hβ : (sheafCompose Y.J (forget RingCat.{w₂})).map β =
      θ.hom.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
    (hstruct : F.structureRingMap ≫ β = H.structureRingMap)
    (M : SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
        ((pushforwardModulesIsoOfPushforwardIso F H θ β hβ hstruct).hom.app M) =
      θ.hom.app
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M) := by
  have h := restrictScalars_comp_eq_pushforwardModules F H β hstruct
  have hsplit : (pushforwardModulesIsoOfPushforwardIso F H θ β hβ hstruct).hom.app M =
      (Functor.isoWhiskerRight
          (pullbackModuleFunctorIsoOfNatIso Y.J
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) θ β hβ)
          (SheafOfModules.restrictScalars F.structureRingMap)).hom.app M ≫
        (eqToIso h).hom.app M := NatTrans.comp_app _ _ M
  have hwhisker :
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
      ((Functor.isoWhiskerRight
          (pullbackModuleFunctorIsoOfNatIso Y.J
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) θ β hβ)
          (SheafOfModules.restrictScalars F.structureRingMap)).hom.app M) =
      θ.hom.app
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M) := rfl
  have heq :
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
      ((eqToIso h).hom.app M) =
      CategoryStruct.id
        ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).obj
        (((pullbackModuleFunctor Y.J H.toToposHom.pushforward
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
          SheafOfModules.restrictScalars β) ⋙
          SheafOfModules.restrictScalars F.structureRingMap).obj M)) := by
    rw [eqToIso.hom, CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map]
    exact eqToHom_refl _ _
  refine Eq.trans (congrArg
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
    hsplit) ?_
  refine Eq.trans
    ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map_comp
      _ _) ?_
  exact (congrArg₂ (fun p q ↦ p ≫ q) hwhisker heq).trans (Category.comp_id _)

/-- **The two transports of the direct image of sheaves of modules along a comparison of the
direct images of sheaves of sets agree.**  Given an isomorphism `e` of the direct images of
sheaves of sets of two morphisms of ringed topoi carrying the structure map of the one to the
structure map of the other, the transport built from `e` as a 2-isomorphism of morphisms of
ringed topoi is the transport built from `e` together with the comparison of the direct images
of the structure sheaf of rings that `e` induces.

Both are the isomorphism whose underlying morphism of sheaves of sets is `e`. -/
theorem pushforwardModulesIsoOfNatIso_eq_pushforwardModulesIsoOfPushforwardIso
    (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (he : F.fSharpRing ≫
      pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom = H.fSharpRing) :
    pushforwardModulesIsoOfNatIso F H e he =
      pushforwardModulesIsoOfPushforwardIso F H e
        (pullbackRingSheafMapOfNatTrans Y.J
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom)
        (ringSheafMap_pullbackRingSheafMapOfNatTrans Y.J
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom)
        he := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ hom_ext_moduleSheafFunctor ?_))
  rw [moduleSheafFunctor_map_pushforwardModulesIsoOfPushforwardIso_hom_app]
  rfl

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W X Y Z : AlgebraicSpaces B S hS}

/-- The transport of the direct image of modules along Stacks 03G8's comparison, read through the
2-isomorphism of morphisms of ringed topoi, is the transport read through the comparison of the
direct images of sheaves of sets and the induced comparison of the structure sheaves of rings. -/
theorem pushforwardModulesCompTransport_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardModulesCompTransport B S hS f g =
      @RingedToposHom.pushforwardModulesIsoOfPushforwardIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Z)
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        (compRingedToposHom B S hS f g)
        (smallEtaleRingedToposHom B S hS (f ≫ g))
        (compToposPushforwardIso B S hS f g) (compStructureRingMap B S hS f g)
        (ringSheafMap_compStructureRingMap B S hS f g) (structureRingMap_comp B S hS f g) := by
  exact RingedToposHom.pushforwardModulesIsoOfNatIso_eq_pushforwardModulesIsoOfPushforwardIso
    _ _ (compToposPushforwardIso B S hS f g) _

/-- **The two comparisons of direct images of `𝒪`-modules along a composite agree.**  The
comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of Stacks 03LU built on the direct images of modules of the
morphisms of small étale ringed topoi is the comparison built on the direct images of modules
along the morphisms of algebraic spaces, read across the identification of the two direct
images. -/
theorem modulePushforwardCompIso_eq_modulePushforwardCompIso' (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforwardCompIso B S hS f g =
      eqToIso (modulePushforward_comp_eq B S hS f g) ≪≫
        modulePushforwardCompIso' B S hS f g ≪≫
        eqToIso (pushforwardModules_eq_modulePushforward B S hS (f ≫ g)) := by
  simp only [modulePushforwardCompIso, modulePushforwardCompIso',
    pushforwardModulesCompTransport_eq B S hS f g]
  refine congrArg (fun t ↦ eqToIso (modulePushforward_comp_eq B S hS f g) ≪≫ t) ?_
  exact (Iso.trans_assoc _ _ _).symm

end AlgebraicGeometry.Space

end
