module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCechCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.TwoFibreProductHomPresheaf
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteGlobalCohomologyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteRestrictedInjectiveAcyclic
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatRepresentedPresheafCohomology

/-! # Presheaves represented by algebraic stacks smooth over a given one

Let `𝒳` be an algebraic stack and `𝒳' ⊆ 𝒳` its lisse-étale site. The presheaves of sets on `𝒳`
represented by algebraic stacks `𝒯` with a smooth 1-morphism `z : 𝒯 ⟶ 𝒳` (faithful on total
categories) form a class closed under representable covers by objects of `𝒳'` in the sense of
`Stacks.Sites.CoverDescent.IsClosedUnderRepresentableCovers`: the image of the distinguished
object of a smooth surjective atlas `e : (Sch/D) ⟶ 𝒯` is a smooth object of `𝒳`, it covers the
presheaf represented by `z` by **Stacks 06XH**, and the fibre powers of that cover are represented
by the iterated 2-fibre products `D ×_𝒯 ⋯ ×_𝒯 D`, again smooth over `𝒳`.

The point of the class is one member: for a 1-morphism `f : 𝒳 ⟶ 𝒴` and a smooth object `y` of
`𝒴` over a scheme `V`, the presheaf `x ↦ Hom_𝒴(f(x), y)` on `𝒳` is represented by the 2-fibre
product `𝒳 ×_𝒴 (Sch/V)`, whose projection to `𝒳` is a base change of the smooth 1-morphism
`y : (Sch/V) ⟶ 𝒴`. That presheaf, restricted to `𝒳'`, is the one whose free abelian sheaf
corepresents the sections over `y` of the direct image along the restriction `f'` of `f` to the
lisse-étale sites. The dévissage of
`StacksFrontier/CategoryTheory/Sites/Cohomology/CoverDescent/Cohomology.lean` then gives, with no
hypothesis,

* `g_!(ℤ[(g')⁻¹ h]) ≅ ℤ[h]` for `h` that presheaf, and
* `Ext^q(ℤ[(g')⁻¹ h], (g')⁻¹ I) = 0` for `q ≥ 1` and every injective abelian sheaf `I` on the
  étale site of `𝒳`.

This is the input of Stacks 07AK at the 2-fibre product `V ×_{y, 𝒴} 𝒳` which the proof of
Stacks 0GR3 (and therefore of Stacks 07AV) needs.

## Main definitions

* `AlgebraicGeometry.Stack.SmoothRepresented`: the class of presheaves above.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isClosedUnderRepresentableCovers_smoothRepresented`: the
  class is closed under representable covers by smooth objects.
* `AlgebraicGeometry.Stack.LisseEtale.smoothRepresented_homPresheaf`: the presheaf
  `x ↦ Hom_𝒴(f(x), y)` is a member, for `y` a smooth object of `𝒴`.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 0GR3](https://stacks.math.columbia.edu/tag/0GR3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites.CoverDescent

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Closure under representable covers, abstractly.** If `Pz` is a property of 1-morphisms of
algebraic stacks which is stable under precomposition with smooth ones, and images of the
distinguished object of `(Sch/D)` under `Pz` 1-morphisms to `𝒳` lie in `P`, then the presheaves
represented by `Pz` 1-morphisms to `𝒳` are closed under representable covers by objects of `P`. -/
private theorem isClosedUnderRepresentableCovers_of_comp
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (τ : SiteKind) (P : ObjectProperty 𝒳.val.val.obj)
    (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ)
    (Pz : ∀ {𝒜 𝒵 : AlgebraicStacks.{u, w} B S hS}, (𝒜 ⟶ 𝒵) → Prop)
    (hcomp : ∀ {𝒜 𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS} (e : 𝒜 ⟶ 𝒵) (z : 𝒵 ⟶ 𝒲),
      AlgebraicStacks.IsSmooth B S hS e → Pz z → Pz (e ≫ z))
    (hobj : ∀ {D : BigFppfOver B S hS} (g : schemeStack.{u, w} B S hS D ⟶ 𝒳), Pz g →
      P ((CatFiberedInGroupoids.homFunctor g.hom).obj (Over.mk (𝟙 D)))) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
    IsClosedUnderRepresentableCovers.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
      (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)) P.ι
      (fun F => ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (z : 𝒯 ⟶ 𝒳),
        (CatFiberedInGroupoids.homFunctor z.hom).Faithful ∧ Pz z ∧
          Nonempty (F ≅ componentPresheaf (CatFiberedInGroupoids.homFunctor z.hom))) := by
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  have := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  have hgen := @generatesCovering_of_isClosedUnderSitePullback B S hS 𝒳 τ P hcl
  intro F hF
  obtain ⟨𝒯, z, hfaith, hzsm, ⟨eF⟩⟩ := hF
  set zf := CatFiberedInGroupoids.homFunctor z.hom with hzf
  have hz : zf ⋙ 𝒳.val.val.p = 𝒯.val.val.p := z.hom.hom.w
  obtain ⟨D, e, hesm, hesurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒯
  have : (schemeStack.{u, w} B S hS D).val.val.p.Faithful :=
    inferInstanceAs (Over.forget D).Faithful
  have hy := hobj (e ≫ z) (hcomp e z hesm hzsm)
  let E₀ := componentPresheafIsoOfIsTerminal (CatFiberedInGroupoids.homFunctor e.hom ⋙ zf)
    (Over.mkIdTerminal (X := D))
  have := isLocallySurjective_componentPresheafMap_atlas τ hgen zf hz e hesm hesurj
  let t := E₀.inv ≫ componentPresheafMap zf (CatFiberedInGroupoids.homFunctor e.hom) ≫ eF.inv
  have ht : Presheaf.IsLocallySurjective
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) t := inferInstance
  refine ⟨⟨_, hy⟩, t, ht, Presheaf.isLocallySurjective_whisker
    (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) P.ι t, fun r => ?_⟩
  obtain ⟨E, -⟩ := exists_tuplePresheaf_iso_cechTower zf hz e (r + 1)
  have hfaithT : (CatFiberedInGroupoids.homFunctor (cechTower B S hS e (r + 1)).2.hom).Faithful :=
    have := faithful_cechTower e (r + 1)
    Functor.Faithful.of_comp_eq (cechTower B S hS e (r + 1)).2.hom.hom.w
  exact ⟨_, ⟨(cechTower B S hS e (r + 1)).1, (cechTower B S hS e (r + 1)).2 ≫ z,
    Functor.Faithful.comp _ zf,
    hcomp _ z (isSmooth_cechTower e hesm (r + 1)) hzsm, ⟨Iso.refl _⟩⟩,
    ⟨tuplePresheafCompIso E₀.symm _ eF.symm (r + 1) ≪≫ E⟩⟩

/-- **The presheaves on `𝒳` represented by algebraic stacks smooth over `𝒳`.** A presheaf of sets
on the site of `𝒳` belongs to the class when it is isomorphic to the presheaf of components
`Ψ(z)` of a smooth 1-morphism `z : 𝒯 ⟶ 𝒳` of algebraic stacks which is faithful on total
categories. -/
def SmoothRepresented (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (F : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (z : 𝒯 ⟶ 𝒳),
    (CatFiberedInGroupoids.homFunctor z.hom).Faithful ∧ AlgebraicStacks.IsSmooth B S hS z ∧
      Nonempty (F ≅ componentPresheaf (CatFiberedInGroupoids.homFunctor z.hom))

namespace LisseEtale

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The image of the distinguished object of `(Sch/D)` under a smooth 1-morphism to `𝒳` is a
smooth object of `𝒳`. -/
theorem smoothObject_obj_of_isSmooth {D : BigFppfOver B S hS}
    (g : schemeStack.{u, w} B S hS D ⟶ 𝒳) (hg : AlgebraicStacks.IsSmooth B S hS g) :
    smoothObject.{u, w} B S hS 𝒳
      ((CatFiberedInGroupoids.homFunctor g.hom).obj (Over.mk (𝟙 D))) :=
  smoothObject_map.{u, w} B S hS g hg
    ⟨Over.mk (𝟙 D), smoothObject_schemeStack_id.{u, w} B S hS D⟩

/-- **The presheaves represented by algebraic stacks smooth over `𝒳` are closed under
representable covers by smooth objects.** For a member `F ≅ Ψ(z)`, `z : 𝒯 ⟶ 𝒳` smooth, choose a
smooth surjective atlas `e : (Sch/D) ⟶ 𝒯`
(`AlgebraicGeometry.Stack.exists_smooth_surjective_schemeStack`).
The image of the distinguished object of `(Sch/D)` under `e ≫ z` is a smooth object of `𝒳`; its
representable presheaf covers `Ψ(z)` locally surjectively by **Stacks 06XH**
(`AlgebraicGeometry.Stack.isLocallySurjective_componentPresheafMap_atlas`), also after restriction
to the lisse-étale site by cocontinuity of the inclusion; and the fibre powers of the cover are
the presheaves represented by the iterated 2-fibre products of `e`
(`AlgebraicGeometry.Stack.exists_tuplePresheaf_iso_cechTower`), whose projections to `𝒯` are
smooth, so that their composites with `z` are smooth. -/
theorem isClosedUnderRepresentableCovers_smoothRepresented :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p (smoothObject.{u, w} B S hS 𝒳) .etale 𝒳.val.isFiberedInGroupoids
      (isClosedUnderSitePullback_smoothObject 𝒳)
    IsClosedUnderRepresentableCovers.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
      ((smoothObject.{u, w} B S hS 𝒳).ι.inheritedTopology
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale))
      (smoothObject.{u, w} B S hS 𝒳).ι (SmoothRepresented 𝒳) := by
  exact isClosedUnderRepresentableCovers_of_comp 𝒳 .etale (smoothObject.{u, w} B S hS 𝒳)
    (isClosedUnderSitePullback_smoothObject 𝒳) (fun z => AlgebraicStacks.IsSmooth B S hS z)
    (fun e z he hz => AlgebraicStacks.isSmooth_comp B S hS e z he hz)
    (smoothObject_obj_of_isSmooth 𝒳)

end LisseEtale

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The cartesian slice datum of an object of an algebraic stack**, carried by the 1-morphism
`y : (Sch/V) ⟶ 𝒴` of the 2-Yoneda lemma: its functor is assembled from the chosen strongly
cartesian lifts of `y`, which form its cone to `y`. -/
noncomputable def objectMorphismSliceDatum (𝒴 : AlgebraicStacks.{u, w} B S hS)
    (y : 𝒴.val.val.obj) : 𝒴.val.val.p.CartesianSliceDatum y where
  sliceMor := Functor.TwoYoneda.liftFunctor 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
    (𝒴.val.val.p.obj y) (Functor.Fiber.mk (a := y) rfl)
  cone W := (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
    (𝒴.val.val.p.obj y) (Functor.Fiber.mk (a := y) rfl) W).φ
  cone_naturality {W W'} h := Functor.IsStronglyCartesian.fac 𝒴.val.val.p W'.hom
    (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (𝒴.val.val.p.obj y) (Functor.Fiber.mk (a := y) rfl) W').φ (Over.w h).symm
    (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (𝒴.val.val.p.obj y) (Functor.Fiber.mk (a := y) rfl) W).φ
  cone_isStronglyCartesian W := (Functor.TwoYoneda.chosenLift 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids (𝒴.val.val.p.obj y) (Functor.Fiber.mk (a := y) rfl)
      W).isStronglyCartesian
  sliceMor_map_isHomLift {W W'} h := Functor.IsStronglyCartesian.map_isHomLift 𝒴.val.val.p W'.hom
    (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (𝒴.val.val.p.obj y) (Functor.Fiber.mk (a := y) rfl) W').φ (Over.w h).symm
    (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (𝒴.val.val.p.obj y) (Functor.Fiber.mk (a := y) rfl) W).φ

/-- The presheaf `x ↦ Hom_𝒴(f(x), y)` is represented by the projection to `𝒳` of the 2-fibre
product of `f` with the 1-morphism `y : (Sch/V) ⟶ 𝒴`: it is faithful, and `Pz` holds for it
whenever `Pz` holds for all base changes of `y`. -/
private theorem exists_homPresheaf_twoFibreProduct_fst {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (y : 𝒴.val.val.obj)
    (Pz : ∀ {𝒜 𝒵 : AlgebraicStacks.{u, w} B S hS}, (𝒜 ⟶ 𝒵) → Prop)
    (hbc : ∀ Q : Bicategory.TwoCommSq f (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒴.val (Functor.Fiber.mk (a := y) rfl)) :
          schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y) ⟶ 𝒴),
      Bicategory.IsTwoFibreProduct Q → Pz Q.fst) :
    ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (z : 𝒯 ⟶ 𝒳),
      (CatFiberedInGroupoids.homFunctor z.hom).Faithful ∧ Pz z ∧
        Nonempty (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y ≅
          componentPresheaf (CatFiberedInGroupoids.homFunctor z.hom)) := by
  have : (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y)).val.val.p.Faithful :=
    inferInstanceAs (Over.forget _).Faithful
  let yMor : schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y) ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom
    (objectMorphism B S hS 𝒴.val (Functor.Fiber.mk (a := y) rfl))
  let Q := twoFibreProductSquareAlgebraicStacks B S hS f yMor
  exact ⟨Q.pt, Q.fst, faithful_twoFibreProductOver_fst 𝒳.val.val.p _ 𝒴.val.val.p
      f.hom.hom.toFunctor yMor.hom.hom.toFunctor,
    hbc Q (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f yMor),
    ⟨(Stacks.Sites.CoverDescent.twoFibreProductFstHomPresheafIso 𝒳.val.val.p
      𝒴.val.val.p f.hom.hom.toFunctor (objectMorphismSliceDatum 𝒴 y) 𝒴.val.isFiberedInGroupoids
      f.hom.hom.w).symm⟩⟩

namespace LisseEtale

/-- **The presheaf `x ↦ Hom_𝒴(f(x), y)` on `𝒳`, for a smooth object `y` of `𝒴`, is represented by
an algebraic stack smooth over `𝒳`**: the 2-fibre product `𝒳 ×_𝒴 (Sch/V)` of `f` with the
1-morphism `y : (Sch/V) ⟶ 𝒴` of the 2-Yoneda lemma, which is smooth because `y` is a smooth
object, so that its base change, the projection to `𝒳`, is smooth. The identification of the
presheaf it represents with the Hom presheaf is
`Stacks.Sites.CoverDescent.twoFibreProductFstHomPresheafIso`. -/
theorem smoothRepresented_homPresheaf {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (y : LisseEtale.{u, w} B S hS 𝒴) :
    SmoothRepresented 𝒳 (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y.obj) := by
  exact exists_homPresheaf_twoFibreProduct_fst f y.obj
    (fun z => AlgebraicStacks.IsSmooth B S hS z)
    fun Q hQ => AlgebraicStacks.isSmooth_baseChange B S hS _ f Q hQ y.property

end LisseEtale

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The presheaves on `𝒳` represented by algebraic stacks flat over `𝒳`.** A presheaf of sets
on the site of `𝒳` belongs to the class when it is isomorphic to the presheaf of components
`Ψ(z)` of a flat 1-morphism `z : 𝒯 ⟶ 𝒳` of algebraic stacks which is faithful on total
categories. -/
def FlatRepresentedUpToIso (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (F : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (z : 𝒯 ⟶ 𝒳),
    (CatFiberedInGroupoids.homFunctor z.hom).Faithful ∧ AlgebraicStacks.IsFlat B S hS z ∧
      Nonempty (F ≅ componentPresheaf (CatFiberedInGroupoids.homFunctor z.hom))

/-- A presheaf equal to the presheaf of components of a faithful flat 1-morphism
(`AlgebraicGeometry.Stack.FlatRepresented`) is in particular isomorphic to one. -/
theorem flatRepresentedUpToIso_of_flatRepresented {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {F : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1)} (hF : FlatRepresented 𝒳 F) :
    FlatRepresentedUpToIso 𝒳 F :=
  let ⟨𝒯, z, hz, hflat, he⟩ := hF
  ⟨𝒯, z, hz, hflat, ⟨eqToIso he⟩⟩

namespace FlatFppf

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The image of the distinguished object of `(Sch/D)` under a flat 1-morphism to `𝒳` is a flat
object of `𝒳`. -/
theorem flatObject_obj_of_isFlat {D : BigFppfOver B S hS}
    (g : schemeStack.{u, w} B S hS D ⟶ 𝒳) (hg : AlgebraicStacks.IsFlat B S hS g) :
    flatObject B S hS 𝒳.val ((CatFiberedInGroupoids.homFunctor g.hom).obj (Over.mk (𝟙 D))) :=
  flatObject_map B S hS g hg ⟨Over.mk (𝟙 D), flatObject_schemeStack_id.{u, w} B S hS D⟩

/-- **The presheaves represented by algebraic stacks flat over `𝒳` are closed under
representable covers by flat objects.** As in the lisse-étale case
(`AlgebraicGeometry.Stack.LisseEtale.isClosedUnderRepresentableCovers_smoothRepresented`): a
smooth surjective atlas `e : (Sch/D) ⟶ 𝒯` of the source of a flat `z : 𝒯 ⟶ 𝒳` gives a flat
object of `𝒳` covering `Ψ(z)` by **Stacks 06XH**, whose fibre powers are represented by the
iterated 2-fibre products of `e`, flat over `𝒳` through their smooth projections to `𝒯`. -/
theorem isClosedUnderRepresentableCovers_flatRepresented :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p (objectProperty B S hS 𝒳) .fppf 𝒳.val.isFiberedInGroupoids
      (FlatFppf.isClosedUnderSitePullback B S hS 𝒳)
    IsClosedUnderRepresentableCovers.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      ((objectProperty B S hS 𝒳).ι.inheritedTopology
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf))
      (objectProperty B S hS 𝒳).ι (FlatRepresentedUpToIso 𝒳) := by
  exact isClosedUnderRepresentableCovers_of_comp 𝒳 .fppf (objectProperty B S hS 𝒳)
    (FlatFppf.isClosedUnderSitePullback B S hS 𝒳) (fun z => AlgebraicStacks.IsFlat B S hS z)
    (fun e z he hz => AlgebraicStacks.isFlat_comp B S hS e z
      (AlgebraicStacks.isFlat_of_isSmooth B S hS e he) hz)
    (flatObject_obj_of_isFlat 𝒳)

/-- **The presheaf `x ↦ Hom_𝒴(f(x), y)` on `𝒳`, for a flat object `y` of `𝒴`, is represented by an
algebraic stack flat over `𝒳`**: the 2-fibre product `𝒳 ×_𝒴 (Sch/V)`, whose projection to `𝒳`
is a base change of the flat 1-morphism `y : (Sch/V) ⟶ 𝒴` (**Stacks 06PY**). -/
theorem flatRepresented_homPresheaf {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (y : FlatFppf B S hS 𝒴) :
    FlatRepresentedUpToIso 𝒳 (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y.obj) := by
  exact exists_homPresheaf_twoFibreProduct_fst f y.obj
    (fun z => AlgebraicStacks.IsFlat B S hS z)
    fun Q hQ => AlgebraicStacks.isFlat_baseChange B S hS _ f Q hQ y.property

end FlatFppf

end AlgebraicGeometry.Stack
