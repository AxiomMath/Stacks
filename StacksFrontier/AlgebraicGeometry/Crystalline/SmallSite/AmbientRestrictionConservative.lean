module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionConservative
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictionCalculus

/-!
# The ambient restrictions on a localised small crystalline site are jointly conservative

Let `(U', T', δ')` be an object of the small crystalline site `Cris(X/S)` of a global crystalline
situation and let `Cris(X/S)/(U', T', δ')` be the localisation of that site at it.  Every object
`(U, T, δ)` of the localised site carries its own family of restrictions to the opens of its
ambient scheme `T`, and those restrictions are again objects of the localised site: the
restriction of `(U, T, δ)` to an open `W` of `T` maps to `(U, T, δ)` and hence to `(U', T', δ')`.

This file turns that observation into a family of functors of sites indexed by the objects of the
*fixed* localised site, and proves that restriction of sheaves of modules along that family is
jointly conservative.  It is the small-site counterpart of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionConservative`, whose
site-generic components — invertibility of a component of a morphism of sheaves of modules
depending only on the isomorphism class of the object — are imported and reused verbatim.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.ambientOverFunctor` —
  for an object `X` of the localised site `Cris(X/S)/B`, the functor from the Zariski site of the
  ambient scheme of `X` localised at its greatest open to `Cris(X/S)/B`, sending an open to the
  restriction of `X` to it.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.ambientOverStructureHom` — the comparison of structure sheaves along that functor, which is
  the identity.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.isIso_of_forall_isIso_pushforward_ambientOver` — **the ambient restrictions on a fixed
  localised small crystalline site are jointly conservative**: a morphism of sheaves of modules on
  `Cris(X/S)/B` all of whose restrictions along the functors above are invertible is itself
  invertible.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.isColimitCokernelCoforkOfForallAmbientOver` — consequently **a cokernel of sheaves of modules
  on a localised small crystalline site is detected by the ambient restrictions**: a cofork is a
  cokernel as soon as each of those restrictions carries it to one.

## Implementation notes

The functor is built as `CategoryTheory.Over.post` of
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.restrictOpenFunctor`
followed by `CategoryTheory.Over.map`, so that both halves of continuity and both halves of
cocontinuity are already available: `Over.post` of the restriction functor is
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.restrictOpenPostFunctor`,
which is continuous and cocontinuous because the opens of a scheme have pullbacks and the
restriction functor preserves them, and `Over.map` along any arrow is continuous and cocontinuous
for the localised topologies.  That is why the source of the functor is the slice `Over ⊤` of the
opens of the ambient scheme at its greatest element rather than the opens themselves: the opens
are not of the form `Over V` and the composite would have to have its continuity proved from
scratch.

The sheaf of rings the restrictions are stated over is the big site's
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` at the underlying object,
as for `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
`.restrictOpenPostStructureHom`: the structure sheaf of `Cris(X/S)` is the restriction along the
inclusion of that of `CRIS(X/S)`, and the restrictions of an object of `Cris(X/S)` to the opens of
its ambient scheme are those of the underlying object.

Joint conservativity is `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app`
together with `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward`: the
latter gives invertibility of the component of the morphism at every object in the image of one of
the functors, and for the functor attached to `X` itself the image of the identity arrow of the
greatest open is the restriction of `X` to the whole of its ambient scheme, which is isomorphic to
`X`.  Isomorphic objects have the same components up to conjugation by the transition maps, which
is `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Crystalline.GlobalCrystallineSituation.SmallSite

universe v u

variable {S : GlobalCrystallineSituation.{u}}

namespace CrystallineThickening

variable (B : CrystallineThickening S)

/-- **The restrictions of an object of a localised small crystalline site to the opens of its
ambient scheme, as a functor of sites into that localised site.**  For `X` an object of
`Cris(X/S)/B` — that is, an object `A` of `Cris(X/S)` with a morphism `A ⟶ B` — this sends an open
`W` of the ambient scheme of `A`, presented as an object of the slice of the opens at the greatest
open, to the restriction of `A` to `W`, equipped with its composite morphism to `B`. -/
noncomputable def ambientOverFunctor (X : Over B) :
    Over (⊤ : X.left.obj.thickening.target.scheme.Opens) ⥤ Over B :=
  Over.post (X := (⊤ : X.left.obj.thickening.target.scheme.Opens))
      (restrictOpenFunctor X.left) ⋙
    Over.map (X.left.restrictOpenHom ⊤ ≫ X.hom)

/-- The ambient restrictions of an object of a localised small crystalline site are continuous,
being the localisation of the restriction functor followed by `CategoryTheory.Over.map`. -/
instance isContinuous_ambientOverFunctor (X : Over B) :
    (ambientOverFunctor B X).IsContinuous
      ((Opens.grothendieckTopology X.left.obj.thickening.target.scheme).over ⊤)
      ((smallTopology S).over B) :=
  Functor.isContinuous_comp (restrictOpenPostFunctor X.left ⊤)
    (Over.map (X.left.restrictOpenHom ⊤ ≫ X.hom))
    ((Opens.grothendieckTopology X.left.obj.thickening.target.scheme).over ⊤)
    ((smallTopology S).over (X.left.restrictOpen ⊤)) ((smallTopology S).over B)

/-- The ambient restrictions of an object of a localised small crystalline site are cocontinuous,
being the localisation of the restriction functor followed by `CategoryTheory.Over.map`. -/
instance isCocontinuous_ambientOverFunctor (X : Over B) :
    (ambientOverFunctor B X).IsCocontinuous
      ((Opens.grothendieckTopology X.left.obj.thickening.target.scheme).over ⊤)
      ((smallTopology S).over B) :=
  CategoryTheory.isCocontinuous_comp (restrictOpenPostFunctor X.left ⊤)
    (Over.map (X.left.restrictOpenHom ⊤ ≫ X.hom))
    ((Opens.grothendieckTopology X.left.obj.thickening.target.scheme).over ⊤)
    ((smallTopology S).over (X.left.restrictOpen ⊤))

/-- **The comparison of structure sheaves along the ambient restrictions is the identity.**  The
restriction of `𝒪_{X/S}` to the opens of the ambient scheme of an object of `Cris(X/S)` is the big
site's `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` at the underlying
object, and the composite of `CategoryTheory.Over.post` of the restriction functor with
`CategoryTheory.Over.map` has the same composite with the forgetful functor of the slice, so the
two restrictions of `𝒪_{X/S}` agree. -/
noncomputable def ambientOverStructureHom (X : Over B) :
    (Thickening.ringRestrictionSheaf X.left.obj).over ⊤ ⟶
      ((ambientOverFunctor B X).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology X.left.obj.thickening.target.scheme).over ⊤)
        ((smallTopology S).over B)).obj ((structureSheaf S).over B) :=
  𝟙 _

/-- The comparison of structure sheaves along the ambient restrictions is invertible, being the
identity. -/
instance isIso_ambientOverStructureHom (B : CrystallineThickening S) (X : Over B) :
    IsIso (ambientOverStructureHom B X) :=
  inferInstanceAs (IsIso (𝟙 ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤)))

/-- **The restriction of an object of a localised small crystalline site to the whole of its
ambient scheme is that object.**  The identity arrow of the greatest open of the ambient scheme of
`X` is carried by
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.ambientOverFunctor` to an
object isomorphic to `X`, the structure morphism of the restriction to the greatest open being an
isomorphism. -/
theorem ambientOverFunctor_obj_mk_id_hom (X : Over B) :
    ((ambientOverFunctor B X).obj
        (Over.mk (𝟙 (⊤ : X.left.obj.thickening.target.scheme.Opens)))).hom =
      (restrictOpenFunctor X.left).map
          (𝟙 (⊤ : X.left.obj.thickening.target.scheme.Opens)) ≫
        X.left.restrictOpenHom (⊤ : X.left.obj.thickening.target.scheme.Opens) ≫ X.hom :=
  rfl

/-- **The identification of an object of a localised small crystalline site with its restriction
to the whole of its ambient scheme**, as an isomorphism in the localised site. -/
noncomputable def ambientOverFunctorObjTopIso (X : Over B) :
    (ambientOverFunctor B X).obj
      (Over.mk (𝟙 (⊤ : X.left.obj.thickening.target.scheme.Opens))) ≅ X :=
  Over.isoMk
    (@asIso _ _ _ _ (X.left.restrictOpenHom (⊤ : X.left.obj.thickening.target.scheme.Opens))
      (isIso_restrictOpenHom_top X.left))
    (by
      rw [ambientOverFunctor_obj_mk_id_hom, CategoryTheory.Functor.map_id, Category.id_comp]
      rfl)

/-- **The ambient restrictions on a fixed localised small crystalline site are jointly
conservative.**  A morphism of sheaves of `𝒪_{X/S}`-modules on `Cris(X/S)/B` whose restriction
along the ambient restrictions of *every* object of that site is invertible is itself invertible.

This is the statement the direction (2) ⇒ (1) of [Stacks, Tag 07IT] needs in order to recognise a
cokernel on the localised small crystalline site from its restrictions to the Zariski sites of the
ambient schemes: no single one of those restrictions reflects anything, but between them they see
every object, since the restriction of an object to the whole of its ambient scheme is that
object. -/
theorem isIso_of_forall_isIso_pushforward_ambientOver
    {M N : SheafOfModules.{v} ((structureSheaf S).over B)} (φ : M ⟶ N)
    (h : ∀ X : Over B,
      IsIso ((SheafOfModules.pushforward.{v} (ambientOverStructureHom B X)).map φ)) :
    IsIso φ := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app φ fun W ↦ ?_
  obtain ⟨Y⟩ := W
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso φ
    (ambientOverFunctorObjTopIso B Y)
    (Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward
      (ambientOverStructureHom B Y) φ (h Y)
      (op (Over.mk (𝟙 (⊤ : Y.left.obj.thickening.target.scheme.Opens)))))

/-- Restriction of sheaves of modules along the ambient restrictions preserves colimits of size
`u + 1`, the universe in which a global presentation on a localised small crystalline site is
indexed.  The four sheafification hypotheses are discharged inside a statement that mentions only
the universe `u + 1`, as in `preservesColimitsOfSize_pushforward_restrictOpenPostStructureHom`:
in the consumers instances of the same two classes at the module universe `u` are also in play,
and two candidate instances at an unresolved value universe make the universe constraints
unsolvable. -/
theorem preservesColimitsOfSize_pushforward_ambientOverStructureHom (X : Over B) :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤) from
        SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)) := by
  have _ : HasSheafify ((smallTopology S).over B) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have _ : ((smallTopology S).over B).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have _ : HasSheafify
      ((Opens.grothendieckTopology X.left.obj.thickening.target.scheme).over ⊤)
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      ((Opens.grothendieckTopology X.left.obj.thickening.target.scheme).over ⊤)
      AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _
  exact Stacks.SheafOfModules.pushforward_preservesColimits.{u, u, u + 1, u + 1, u, u}
    (ambientOverFunctor B X) (ambientOverStructureHom B X)

/-- Restriction of sheaves of modules along the ambient restrictions preserves zero morphisms, the
zero morphism of a sheaf of modules being the zero morphism of its underlying presheaf. -/
instance preservesZeroMorphisms_pushforward_ambientOverStructureHom (X : Over B) :
    (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
        SheafOfModules.{u + 1} ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤) from
      SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B X)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- **A cokernel of sheaves of `𝒪_{X/S}`-modules on a localised small crystalline site is detected
by the ambient restrictions.**  A cofork is a cokernel as soon as its restriction along the ambient
restrictions of every object of the localised site is one.

Each of those restrictions preserves the cokernel it has to preserve, being continuous and
cocontinuous, and the family is jointly conservative by
`isIso_of_forall_isIso_pushforward_ambientOver`;
`CategoryTheory.Limits.isColimitCokernelCoforkOfConservativeFamily` assembles the two. -/
noncomputable def isColimitCokernelCoforkOfForallAmbientOver
    {Q P N : SheafOfModules.{u + 1} ((structureSheaf S).over B)}
    {a : Q ⟶ P} {b : P ⟶ N} (hab : a ≫ b = 0) [HasCokernel a]
    (hb : ∀ X : Over B, IsColimit (CokernelCofork.ofπ
      ((SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map b)
      (show (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map a ≫
            (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map b = 0 by
        rw [← Functor.map_comp, hab]
        exact (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map_zero _ _))) :
    IsColimit (CokernelCofork.ofπ b hab) :=
  haveI : ∀ X : Over B, PreservesColimit (parallelPair a 0)
      (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤) from
        SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)) := fun X ↦ by
    have := preservesColimitsOfSize_pushforward_ambientOverStructureHom B X
    have : PreservesColimitsOfSize.{0, 0}
        (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
            SheafOfModules.{u + 1} ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤) from
          SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)) :=
      preservesColimitsOfSize_shrink _
    infer_instance
  isColimitCokernelCoforkOfConservativeFamily hab
    (fun X : Over B ↦
      show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤) from
        SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X))
    (fun _ _ f hf ↦ isIso_of_forall_isIso_pushforward_ambientOver B f hf) hb

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation.SmallSite

end
