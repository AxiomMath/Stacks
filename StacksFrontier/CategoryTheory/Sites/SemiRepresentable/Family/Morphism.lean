module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Ringed

/-!
# Morphisms between ringed semi-representable localizations

Let `X` be a ringed site. A morphism `f : K ⟶ L` of semi-representable objects of its
underlying site induces a morphism between the ringed topoi of sheaves on their componentwise
localization sites. The underlying geometric morphism is the one induced by componentwise
relocalization, and the map on structure sheaves is the canonical identity comparison: both
structure sheaves are restrictions of `O_X` along functors that compose to the same functor,
so there is nothing to compare.

## Main definitions

* `AlgebraicGeometry.RingedSite.localizationRingedTopos`: the ringed topos of a componentwise
  localization.
* `AlgebraicGeometry.RingedSite.familyMorphism`: the morphism of ringed topoi induced by a
  morphism of semi-representable objects, together with the specification of its inverse image
  and of its structure map.

## Implementation notes

`localizationRingedTopos` is the ringed site `AlgebraicGeometry.RingedSite.localization` read
as a ringed topos, in the same way that `AlgebraicGeometry.RingedSite.ringedTopos` reads a
ringed site as a ringed topos; it is stated here at the generality of
`AlgebraicGeometry.RingedSite.localizationStructureSheaf`, whose site and section universes are
independent, where `localization` fixes them equal.

The specification identifies inverse image on sheaves of sets with restriction along the
componentwise relocalization functor, and pins the structure map to the identity comparison
between the two restrictions rather than to an arbitrary isomorphism. The section universe
contains the site and family-index universes so that the right adjoint to restriction can form
products over the fibres of the family map.

The inverse image of sheaves of commutative rings is
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor` and the comparison of that
inverse image with restriction is `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`; the
structure map in inverse-image form is derived from `fSharp` through
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, which is what
`AlgebraicGeometry.RingedToposHom` takes as its data.

`componentwiseTopology_hasSheafCompose_forget₂` is stated as a theorem rather than an instance
and applied with `attribute [local instance]`, so that a consumer can make the very same
instance term available by name instead of coining a second one.

## References

* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w v u r

namespace CategoryTheory.SemiRepresentable

/-- On a componentwise localization site, composition with `forget₂ CommRingCat RingCat`
preserves the sheaf condition, because that functor creates limits and the limits in question
are computed on underlying types. -/
theorem componentwiseTopology_hasSheafCompose_forget₂ {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) :
    (componentwiseTopology J K).HasSheafCompose
      (forget₂ CommRingCat.{r} RingCat.{r}) := by
  let : PreservesLimitsOfSize.{max u v w, max u v w}
      (forget₂ CommRingCat.{r} RingCat.{r}) :=
    AlgebraicGeometry.preservesLimitsOfSize_forget₂_commRingCat_ringCat
  exact hasSheafCompose_of_preservesLimitsOfSize _

end CategoryTheory.SemiRepresentable

open CategoryTheory.SemiRepresentable

attribute [local instance] componentwiseTopology_hasSheafCompose_forget₂

attribute [local implicit_reducible] LocalizationSites.sourceTopology
  LocalizationSites.targetTopology

namespace AlgebraicGeometry.RingedSite

/-- The ringed topos of sheaves on the componentwise localization at a semi-representable
object `K`: the site is the disjoint union of the slice sites of the components of `K` with the
componentwise topology, and the structure sheaf is `O_K`. -/
noncomputable abbrev localizationRingedTopos (X : RingedSite.{u, v, r})
    (K : FormalCoproduct.{w} X.C) : RingedTopos where
  C := ComponentOver K
  J := componentwiseTopology X.J K
  O := localizationStructureSheaf X K

/-- **Stacks 0D9U.** A morphism of semi-representable objects induces a morphism of the ringed
topoi of their componentwise localizations: its inverse image on sheaves of sets is restriction
along the componentwise relocalization functor, and its structure map is the canonical identity
comparison, which is an isomorphism. -/
@[stacks 0D9U "family_morphism"]
noncomputable def familyMorphism (X : RingedSite.{u, v, max u v w r})
    {K L : FormalCoproduct.{w} X.C} (f : K ⟶ L) :
    let S : LocalizationSites.{w} X.C X.J := ⟨K, L, f⟩
    { g : RingedToposHom (localizationRingedTopos X K) (localizationRingedTopos X L) //
      (g.toToposHom.inverseImage ⋙
          sheafToPresheaf S.sourceTopology (Type (max u v w r)) =
        sheafToPresheaf S.targetTopology (Type (max u v w r)) ⋙
          (CategoryTheory.Functor.whiskeringLeft _ _ _).obj S.relocalizationFunctor.op) ∧
      (∃ h : (localizationRingedTopos X K).forgetRing.obj
          ((inverseImageCommRingFunctor g.toToposHom).obj
            (localizationRingedTopos X L).O) =
          (localizationRingedTopos X K).forgetRing.obj (localizationRingedTopos X K).O,
        (localizationRingedTopos X K).forgetRing.map g.fSharpInverseImage =
          eqToHom h) ∧
      IsIso g.fSharpInverseImage } := by
  let S : LocalizationSites.{w} X.C X.J := ⟨K, L, f⟩
  let T : LocalizationSites.{w} X.C X.J := ⟨L, L, 𝟙 L⟩
  let U : LocalizationSites.{w} X.C X.J := ⟨K, K, 𝟙 K⟩
  letI := LocalizationSites.relocalizationFunctor_isContinuous S
  letI := LocalizationSites.relocalizationFunctor_isCocontinuous S
  letI := LocalizationSites.localizationFunctor_isContinuous T
  letI := LocalizationSites.localizationFunctor_isContinuous U
  haveI : U.localizationFunctor.IsContinuous S.sourceTopology X.J := by
    simpa [LocalizationSites.sourceTopology] using
      (LocalizationSites.localizationFunctor_isContinuous U)
  let G : MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max u v w r)))
      (Sheaf S.targetTopology (Type (max u v w r))) :=
    { inverseImage := S.relocalizationFunctor.sheafPushforwardContinuous
        (Type (max u v w r)) S.sourceTopology S.targetTopology
      pushforward := S.relocalizationFunctor.sheafPushforwardCocontinuous
        (Type (max u v w r)) S.sourceTopology S.targetTopology
      adj := S.relocalizationFunctor.sheafAdjunctionCocontinuous
        (Type (max u v w r)) S.sourceTopology S.targetTopology
      preservesFiniteLimits := inferInstance }
  have hcompObj : ∀ Y, (S.relocalizationFunctor ⋙ T.localizationFunctor).obj Y =
        U.localizationFunctor.obj Y := by
    intro Y
    cases Y with
    | mk i V => rfl
  have hcompMap : ∀ Y Z (a : Y ⟶ Z),
      (S.relocalizationFunctor ⋙ T.localizationFunctor).map a ≍
        U.localizationFunctor.map a := by
    intro Y Z a
    cases Y with
    | mk i V =>
      cases Z with
      | mk j W =>
        cases a
        change (Over.forget (L.obj (S.f.f i))).map
            ((Over.map (S.f.φ i)).map _) ≍
          (Over.forget (K.obj i)).map _
        simp [Over.map_map_left]
  have hcomp : S.relocalizationFunctor ⋙ T.localizationFunctor = U.localizationFunctor :=
    CategoryTheory.Functor.hext hcompObj hcompMap
  haveI : S.relocalizationFunctor.IsContinuous S.sourceTopology T.sourceTopology := by
    simpa [LocalizationSites.sourceTopology, LocalizationSites.targetTopology] using
      (LocalizationSites.relocalizationFunctor_isContinuous S)
  let ecomp := Functor.sheafPushforwardContinuousComp'
    (F := S.relocalizationFunctor) (G := T.localizationFunctor)
    (FG := U.localizationFunctor) (eqToIso hcomp)
    CommRingCat.{max u v w r} S.sourceTopology T.sourceTopology X.J
  let eRestr := restrictionCommRingIso S.sourceTopology S.targetTopology
    S.relocalizationFunctor
    ((T.localizationFunctor.sheafPushforwardContinuous CommRingCat.{max u v w r}
      T.sourceTopology X.J).obj X.O)
  let e : (inverseImageCommRingFunctor G).obj (localizationRingedTopos X L).O ≅
      (localizationRingedTopos X K).O := by
    dsimp [localizationRingedTopos, localizationStructureSheaf]
    exact eRestr ≪≫ ecomp.app X.O
  let g : RingedToposHom (localizationRingedTopos X K) (localizationRingedTopos X L) :=
    { toToposHom := G
      fSharp := ((commRingImageAdjunction G).homEquiv _ _) e.hom }
  let h : (localizationRingedTopos X K).forgetRing.obj
        ((inverseImageCommRingFunctor g.toToposHom).obj
          (localizationRingedTopos X L).O) =
      (localizationRingedTopos X K).forgetRing.obj (localizationRingedTopos X K).O := by
    apply CategoryTheory.ObjectProperty.FullSubcategory.ext
    have hobj : ∀ Y,
        ((localizationRingedTopos X K).forgetRing.obj
          ((inverseImageCommRingFunctor g.toToposHom).obj
            (localizationRingedTopos X L).O)).obj.obj Y =
        ((localizationRingedTopos X K).forgetRing.obj
          (localizationRingedTopos X K).O).obj.obj Y := by
      intro Y
      cases Y with
      | op Y =>
        cases Y with
        | mk i V => rfl
    refine CategoryTheory.Functor.hext hobj ?_
    intro Y Z a
    have hm := eq_of_heq
      (hcompMap (Opposite.unop Z) (Opposite.unop Y) (Opposite.unop a))
    have hY := hobj Y
    have hZ := hobj Z
    cases Y with
    | op Y =>
      cases Z with
      | op Z =>
        cases Y
        cases Z
        cases hY
        cases hZ
        dsimp [localizationRingedTopos, RingedTopos.forgetRing, localizationStructureSheaf,
          inverseImageCommRingFunctor, pullbackCommRingSheafFunctor, pullbackCommRingSheaf]
        change (forget CommRingCat.{max u v w r}).map
            (X.O.obj.map ((S.relocalizationFunctor ⋙ T.localizationFunctor).op.map a)) ≍
          (forget CommRingCat.{max u v w r}).map
            (X.O.obj.map (U.localizationFunctor.op.map a))
        exact heq_of_eq (congrArg
          (fun b => (forget CommRingCat.{max u v w r}).map (X.O.obj.map (Opposite.op b))) hm)
  refine ⟨g, ?_, ⟨h, ?_⟩, ?_⟩
  · rfl
  · change (localizationRingedTopos X K).forgetRing.map
        (((commRingImageAdjunction G).homEquiv _ _).symm
          (((commRingImageAdjunction G).homEquiv _ _) e.hom)) = eqToHom h
    rw [Equiv.symm_apply_apply]
    apply Sheaf.hom_ext
    rw [ObjectProperty.eqToHom_hom]
    ext Y x
    cases Y with
    | op Y =>
      cases Y with
      | mk i V =>
        change ((forget CommRingCat.{max u v w r}).map
            (X.O.obj.map ((eqToHom hcomp.symm).app ⟨i, V⟩).op)) x = _
        rw [eqToHom_app, eqToHom_app]
        change ((forget CommRingCat.{max u v w r}).map (X.O.obj.map (𝟙 _))) x = _
        exact congrArg (fun b : X.O.obj.obj (Opposite.op V.left) ⟶
            X.O.obj.obj (Opposite.op V.left) => ((forget CommRingCat.{max u v w r}).map b) x)
          (X.O.obj.map_id (Opposite.op V.left))
  · change IsIso (((commRingImageAdjunction G).homEquiv _ _).symm
      (((commRingImageAdjunction G).homEquiv _ _) e.hom))
    simpa only [Equiv.symm_apply_apply] using e.isIso_hom

end AlgebraicGeometry.RingedSite

end
