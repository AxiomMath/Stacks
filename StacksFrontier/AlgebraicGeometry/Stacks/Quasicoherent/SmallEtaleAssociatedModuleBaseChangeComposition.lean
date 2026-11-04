module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleBaseChangeConjugate
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkInverseImage

/-!
# The base change of the associated module is compatible with composition

`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` is the identification
`(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` of **Stacks 03LC (1)**, read for the small étale sites of two schemes of
a big étale site and a morphism `a : X ⟶ Y` between them.  This file proves that those
identifications compose: for `a : X ⟶ Y` and `b : Y ⟶ Z`, the identification below `b` followed
by the identification below `a` is the identification below `a ∘ b`, read through the
composition law for the pullbacks of the morphisms of ringed sites of **Stacks 070R (2)** and the
composition law for the pullbacks of modules on the schemes.

The two sides are comparisons of composites of *left* adjoints, so neither has a formula; the
proof transposes the whole pentagon to the right adjoints with `CategoryTheory.conjugateEquiv`,
which is a bijection compatible with composition, whiskering and the associator.  There every
comparison in sight is restriction of sections — `SheafOfModules.pushforwardComp` is the identity
and `SheafOfModules.pushforwardCongr₂` is restriction along a component of the comparison of the
two index functors — so the pentagon becomes a diagram of restriction maps of `𝓕^a` between
objects of the small étale site of `X`.  Its target is the image of an open of `X`, whose open
immersion is a monomorphism, so the diagram commutes because its two sides are restriction along
morphisms that are equal for the only available reason: there is at most one of them
(`AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale`).

This is the composition law for factor 4 of the identification of the sections of
`AlgebraicGeometry.Stack.liftedSectionsIso`, which
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedFppfFamilySheafCondition.lean` carries
as the hypothesis `AlgebraicGeometry.Stack.LiftedSectionsCocycle` — at the inner,
morphism-of-ringed-sites layer `ε_a` of that factor.

## Main definitions

* `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso`: the comparison of the two
  composite *right* adjoints round the square of ringed sites, that is restriction of sections
  along the base change of an open.

## Main results

* `AlgebraicGeometry.SmallEtale.conjugateEquiv_associatedModuleBaseChangeIso_inv`: **the unit
  characterisation of `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`** — its
  conjugate is the comparison of the two composite pushforwards.
* `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp`: **the identifications
  `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` compose**, as an equality of isomorphisms of functors.
* `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp`: the same at one module,
  as an equality of two composites of morphisms of sheaves of modules.

## Implementation notes

The composition law is stated and proved for the inverse isomorphisms, because
`SheafOfModules.conjugateEquiv_pullbackSquareIso_inv` and
`AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv` characterise the
inverses: an isomorphism of left adjoints produced by uniqueness is `leftAdjointUniq` with the
transported adjunction second, and the conjugate of such a comparison comes out without a
transport only in that direction.  `CategoryTheory.Iso.inv_eq_inv` turns the statement about the
isomorphisms into one about the inverses.

`CategoryTheory.Adjunction.comp_assoc` is needed twice: whiskering on the left produces the
adjunction `adj.comp adj₁` and whiskering on the right produces `adj₁.comp adj`, so a composite of
three functors whiskered on both sides arrives with both bracketings of the composite adjunction,
and the two conjugates cannot be composed until they are the same term.

No new Stacks tag is registered.  Stacks 03LC (1) is tagged where it is proved, and what is
added here is that the identifications it provides are functorial in the morphism, between
constructions this library carries.

## References

* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Functor

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **The comparison of the two composite right adjoints round the square of ringed sites of
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`.**  Restricting a sheaf of modules
on the small étale site of `X` along `ε_a` and then to the small Zariski site of `Y` is
restricting it to the small Zariski site of `X` and then pushing forward along `r`: over an open
`V` of `Y` both are the sections over the base change of `V`, read as the preimage open by
`AlgebraicGeometry.SmallEtale.baseChangeOpensIso`.

This is the isomorphism of right adjoints which
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` is conjugate to. -/
public noncomputable abbrev restrictModuleBaseChangeIso :
    SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        restrictModule B Y.obj Y.property ≅
      restrictModule B X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom B a) :=
  SheafOfModules.pushforwardComp.{u} (structureMap B Y.obj Y.property)
      (smallEtaleStructureMapRing B a) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _ (baseChangeOpensIso B a)
      (structureMap_comp_baseChangeOpensIso B a) ≪≫
    (SheafOfModules.pushforwardComp.{u} (schemeHom B a).toRingCatSheafHom
      (structureMap B X.obj X.property)).symm

/-- **The comparison of the two composite restrictions is restriction along the base change of
an open.**  Over an open `V` of `Y` it is the restriction map of `𝓕^a` along the identification
of the base change of `V` with the preimage open.  The two spellings of its source and target
agree by unfolding, which is why the statement holds by `rfl`. -/
public theorem restrictModuleBaseChangeIso_inv_app_app
    (M : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (V : Y.obj.Opens) :
    Scheme.Modules.Hom.app ((restrictModuleBaseChangeIso B a).inv.app M) V =
      M.val.presheaf.map ((baseChangeOpensIso B a).inv.app V).op :=
  rfl

/-- **The unit characterisation of `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`.**
The identification `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` is conjugate, with respect to the two composite
pullback-pushforward adjunctions round the square of ringed sites, to the comparison
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso` of the two composite restrictions.

This pins the identification: `CategoryTheory.conjugateEquiv` is a bijection, so no other
morphism of the two composite pullbacks has that conjugate. -/
public theorem conjugateEquiv_associatedModuleBaseChangeIso_inv :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).comp
          (associatedModuleAdjunction B X.obj X.property))
        ((associatedModuleAdjunction B Y.obj Y.property).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B a)))
        (associatedModuleBaseChangeIso B a).inv =
      (restrictModuleBaseChangeIso B a).inv :=
  SheafOfModules.conjugateEquiv_pullbackSquareIso_inv.{u} _ _ _ _ _ _

/-- The conjugate of the identification below `a`, whiskered by the pullback of modules along
`b`: it is the comparison of the restrictions below `a`, whiskered by the pushforward along
`b`. -/
private theorem conj_whiskerLeft_square :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B b)).comp
          ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).comp
            (associatedModuleAdjunction B X.obj X.property)))
        ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B b)).comp
          ((associatedModuleAdjunction B Y.obj Y.property).comp
            (SheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureMapRing B a))))
        (Functor.whiskerLeft (Scheme.Modules.pullback (schemeHom B b))
          (associatedModuleBaseChangeIso B a).inv) =
      Functor.whiskerRight (restrictModuleBaseChangeIso B a).inv
        (Scheme.Modules.pushforward (schemeHom B b)) := by
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_associatedModuleBaseChangeIso_inv]

/-- The conjugate of the identification below `b`, whiskered by the pullback of sheaves of
modules along `ε_a`: it is the comparison of the restrictions below `b`, whiskered by the
pushforward along `ε_a`. -/
private theorem conj_whiskerRight_square :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B b)).comp
          ((associatedModuleAdjunction B Y.obj Y.property).comp
            (SheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureMapRing B a))))
        ((associatedModuleAdjunction B Z.obj Z.property).comp
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureMapRing B b)).comp
            (SheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureMapRing B a))))
        (Functor.whiskerRight (associatedModuleBaseChangeIso B b).inv
          (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a))) =
      Functor.whiskerLeft (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
        (restrictModuleBaseChangeIso B b).inv := by
  rw [CategoryTheory.Adjunction.comp_assoc, CategoryTheory.Adjunction.comp_assoc,
    conjugateEquiv_whiskerRight, conjugateEquiv_associatedModuleBaseChangeIso_inv]

/-- The conjugate of the composition law for the pullbacks along the morphisms of ringed sites
of Stacks 070R (2), whiskered by the associated-module functor of `Z`. -/
private theorem conj_whiskerLeft_compIso :
    conjugateEquiv
        ((associatedModuleAdjunction B Z.obj Z.property).comp
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureMapRing B b)).comp
            (SheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureMapRing B a))))
        ((associatedModuleAdjunction B Z.obj Z.property).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B (a ≫ b))))
        (Functor.whiskerLeft (associatedModule B Z.obj Z.property)
          (smallEtalePullbackCompIso B a b).inv) =
      Functor.whiskerRight
        ((SheafOfModules.pushforwardComp.{u} (smallEtaleStructureMapRing B b)
            (smallEtaleStructureMapRing B a)).hom ≫
          (smallEtalePushforwardCompIso B a b).inv)
        (restrictModule B Z.obj Z.property) := by
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_smallEtalePullbackCompIso_inv]

/-- The conjugate of the composition law for the pullbacks of modules on the schemes, whiskered
by the associated-module functor of `X`. -/
private theorem conj_whiskerRight_pullbackComp :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B b)).comp
          ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).comp
            (associatedModuleAdjunction B X.obj X.property)))
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (schemeHom B a ≫ schemeHom B b)).comp
          (associatedModuleAdjunction B X.obj X.property))
        (Functor.whiskerRight (Scheme.Modules.pullbackComp (schemeHom B a) (schemeHom B b)).inv
          (associatedModule B X.obj X.property)) =
      Functor.whiskerLeft (restrictModule B X.obj X.property)
        (Scheme.Modules.pushforwardComp (schemeHom B a) (schemeHom B b)).hom := by
  rw [CategoryTheory.Adjunction.comp_assoc, conjugateEquiv_whiskerRight,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv]

/-- The conjugate of the identification below the composite `a ∘ b`, at the spelling of the
composite that the composition law for the pullbacks of modules on the schemes produces. -/
private theorem conj_square_comp :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (schemeHom B a ≫ schemeHom B b)).comp
          (associatedModuleAdjunction B X.obj X.property))
        ((associatedModuleAdjunction B Z.obj Z.property).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B (a ≫ b))))
        (associatedModuleBaseChangeIso B (a ≫ b)).inv =
      (restrictModuleBaseChangeIso B (a ≫ b)).inv :=
  conjugateEquiv_associatedModuleBaseChangeIso_inv B (a ≫ b)

/-- **The comparisons of the composite restrictions compose.**  This is the pentagon of the
composition law, transposed to the right adjoints.  Every comparison appearing in it is
restriction of sections of `𝓕^a` between objects of the small étale site of `X`, and the common
target is the image of the open `(r_b ∘ r_a)⁻¹(V)` of `X`; its open immersion being a
monomorphism, there is at most one morphism into that object, so the two restriction maps agree
with no further argument. -/
private theorem restrictModuleBaseChangeIso_inv_comp :
    (Functor.whiskerRight (restrictModuleBaseChangeIso B a).inv
          (Scheme.Modules.pushforward (schemeHom B b)) ≫
        Functor.whiskerLeft (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
          (restrictModuleBaseChangeIso B b).inv) ≫
      Functor.whiskerRight
        ((SheafOfModules.pushforwardComp.{u} (smallEtaleStructureMapRing B b)
            (smallEtaleStructureMapRing B a)).hom ≫
          (smallEtalePushforwardCompIso B a b).inv)
        (restrictModule B Z.obj Z.property) =
      Functor.whiskerLeft (restrictModule B X.obj X.property)
          (Scheme.Modules.pushforwardComp (schemeHom B a) (schemeHom B b)).hom ≫
        (restrictModuleBaseChangeIso B (a ≫ b)).inv := by
  ext M V x
  have key :
      M.val.presheaf.map ((baseChangeOpensIso B a).inv.app (schemeHom B b ⁻¹ᵁ V)).op ≫
          M.val.presheaf.map
            ((smallEtaleBaseChange B a).map ((baseChangeOpensIso B b).inv.app V)).op ≫
          M.val.presheaf.map
            ((smallEtaleBaseChange_factoredCompIso B X Y Z a b (a ≫ b) rfl).inv.app
              ((opensToSmallEtale B Z.obj Z.property).obj V)).op =
        M.val.presheaf.map ((baseChangeOpensIso B (a ≫ b)).inv.app V).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun f => M.val.presheaf.map (Quiver.Hom.op f))
      (Subsingleton.elim (h := subsingleton_hom_opensToSmallEtale B X.obj X.property _
        (schemeHom B (a ≫ b) ⁻¹ᵁ V)) _ _)
  exact congrArg (fun (h : _ ⟶ _) => (ConcreteCategory.hom h) x) key

/-- **The identifications `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` of Stacks 03LC (1) compose.**  For morphisms
`a : X ⟶ Y` and `b : Y ⟶ Z` of a big étale site, the identification below `b` followed by the
identification below `a` is the identification below `a ∘ b`: on the pullback side of the small
étale sites the two successive pullbacks are composed by
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso`, and on the side of the modules on the
schemes by `AlgebraicGeometry.Scheme.Modules.pullbackComp`.

Neither side has a formula, both being comparisons of composites of left adjoints; the equality
is checked by transposing to the right adjoints, where
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_comp` is a diagram of restriction
maps into the image of an open. -/
public theorem associatedModuleBaseChangeIso_comp :
    isoWhiskerLeft (Scheme.Modules.pullback (schemeHom B b))
          (associatedModuleBaseChangeIso B a) ≪≫
        isoWhiskerRight (associatedModuleBaseChangeIso B b)
          (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)) ≪≫
        isoWhiskerLeft (associatedModule B Z.obj Z.property)
          (smallEtalePullbackCompIso B a b) =
      isoWhiskerRight (Scheme.Modules.pullbackComp (schemeHom B a) (schemeHom B b))
          (associatedModule B X.obj X.property) ≪≫
        associatedModuleBaseChangeIso B (a ≫ b) := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).mp ?_)
  simp only [Iso.trans_inv, isoWhiskerLeft_inv, isoWhiskerRight_inv, Category.assoc]
  refine (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B b)).comp
      ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).comp
        (associatedModuleAdjunction B X.obj X.property)))
    ((associatedModuleAdjunction B Z.obj Z.property).comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureMapRing B (a ≫ b))))).injective ?_
  rw [← conjugateEquiv_comp _
      ((associatedModuleAdjunction B Z.obj Z.property).comp
        ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B b)).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B a)))) _,
    ← conjugateEquiv_comp _
      ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B b)).comp
        ((associatedModuleAdjunction B Y.obj Y.property).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B a)))) _,
    ← conjugateEquiv_comp _
      ((Scheme.Modules.pullbackPushforwardAdjunction
          (schemeHom B a ≫ schemeHom B b)).comp
        (associatedModuleAdjunction B X.obj X.property)) _,
    conj_whiskerLeft_square, conj_whiskerRight_square, conj_whiskerLeft_compIso,
    conj_whiskerRight_pullbackComp, conj_square_comp]
  exact restrictModuleBaseChangeIso_inv_comp B a b

/-- **The identifications `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` compose, at one module.**  Read off from
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp`, this is the form a
componentwise consumer uses: an equality of two composites of morphisms of sheaves of modules on
the small étale site of `X`. -/
public theorem associatedModuleObjBaseChangeIso_comp (𝓖 : Z.obj.Modules) :
    (associatedModuleObjBaseChangeIso B a
            ((Scheme.Modules.pullback (schemeHom B b)).obj 𝓖)).hom ≫
        (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
          (associatedModuleObjBaseChangeIso B b 𝓖).hom ≫
        (smallEtalePullbackCompIso B a b).hom.app
          ((associatedModule B Z.obj Z.property).obj 𝓖) =
      (associatedModule B X.obj X.property).map
          ((Scheme.Modules.pullbackComp (schemeHom B a) (schemeHom B b)).hom.app 𝓖) ≫
        (associatedModuleObjBaseChangeIso B (a ≫ b) 𝓖).hom := by
  have h := NatTrans.congr_app
    (congrArg Iso.hom (associatedModuleBaseChangeIso_comp B a b)) 𝓖
  simpa only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, associatedModuleObjBaseChangeIso,
    Iso.app_hom, Functor.comp_obj, Category.assoc] using h

end AlgebraicGeometry.SmallEtale

end
