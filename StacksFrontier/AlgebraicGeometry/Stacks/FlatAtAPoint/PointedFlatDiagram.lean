module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
import all StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation

/-!
# Pointed flat diagrams and flatness at a point (Stacks 0CID)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `x` be a point of `|𝒳|`.
**Stacks 0CIC** considers 2-commutative squares

```
U ---h---> V
|          |
a          b
v          v
𝒳 ---f---> 𝒴
```

in which `U` and `V` are algebraic spaces over `S` — read as categories fibred in groupoids
through `AlgebraicGeometry.Stack.fibredCategory` — the right vertical 1-morphism `b` is flat, the
comparison 1-morphism `(a, h) : U ⟶ 𝒳 ×_𝒴 V` is flat, and a point `u` of `|U|` maps to `x`.
**Stacks 0CID** calls `f` *flat at* `x` when flatness of `h` at `u` holds for one such square.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram`: such a square, bundled with its
  hypotheses and with the point of `|U|` above `x`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsFlatAt`: **Stacks 0CID**, flatness of a 1-morphism
  of algebraic stacks at a point of the source.

## Implementation notes

Flatness of the right vertical 1-morphism and of the comparison is the existential
smooth-diagram criterion of **Stacks 06FM** at flatness of morphisms of algebraic spaces,
`AlgebraicGeometry.Stack.HasPropertyOnSomeSmoothDiagram`, rather than
`AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat`: the comparison 1-morphism `k.hom` of a square
has a 2-fibre product as its target, which is an algebraic stack but is not presented as an
object of `AlgebraicGeometry.Stack.AlgebraicStacks`. On objects of that 2-category the two
notions agree on the nose, by
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram`.

The comparison is tested against every morphism of 2-commutative squares into every 2-fibre
product of the cospan `(b, f)`, which makes the condition independent of the chosen model of
`𝒳 ×_𝒴 V`; this is the device **Stacks 06FM** already uses for the smooth comparison in
`AlgebraicGeometry.Stack.HasPropertyOnEverySmoothDiagram`.

Stacks 0CID is taken at the existential condition, which is the one a square witnesses directly;
Stacks 0CIC, in `StacksFrontier.AlgebraicGeometry.Stacks.FlatAtAPoint.IndependenceOfDiagram`, is
what makes the choice immaterial.

The ingredients of that proof are proved in this module as private declarations:

* `isFlatAt_comp` and `isFlatAt_of_comp`, composition and descent of flatness of a morphism of
  algebraic spaces at a point, read through the étale local rings of **Stacks 04NG**;
* `isFlatAt_of_isPullback` and `isFlatAt_of_isPullback_presheaf`, base change of flatness of a
  morphism of algebraic spaces at a point — the structure sheaf case of **Stacks 05VW** — on top
  of `schemeIsFlatAt_of_isPullback` for schemes;
* `hasPropertyOnSomeSmoothDiagram_preHom_of_preHom`, the flat analogue of
  `AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_one`: the flatness required of the
  comparison 1-morphisms of a diagram needs checking at a single 2-fibre product;
* `PointedFlatDiagram.source_flat`, flatness of the left vertical 1-morphism of a diagram;
* `exists_flat_space_common_refinement_of_square`, two flat charts of an algebraic stack through
  one point are refined by a common flat one;
* `exists_flat_surjective_space_chart`, a flat chart of an algebraic stack by an algebraic space
  surjective on points;
* `nonempty_pointedFlatDiagram`, the existence of a diagram through any point.

None of these carries a `@[stacks]` attribute. In particular the base-change statement is
unexported substrate: Stacks 05VW is a statement about modules, of which only the structure
sheaf case appears here.

## References

* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 0CIC](https://stacks.math.columbia.edu/tag/0CIC)
* [Stacks Project, Tag 0CID](https://stacks.math.columbia.edu/tag/0CID)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site exceeds the default budget
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_PointedFlatDiagram :
    Limits.HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_PointedFlatDiagram
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Limits.HasLimit (Limits.cospan f g) :=
  Limits.HasLimitsOfShape.has_limit _

/-- Cancelling the inverse of an isomorphism at the end of a threefold composite. This is a
general fact about categories, recorded because the hom-categories of the 2-category of
categories fibred in groupoids over the big fppf site of `S` are reached through an induced
bicategory, where `simp` does not see the associativity of 2-morphism composition. -/
private theorem comp_assoc_inv_hom {C : Type*} [Category C] {V W X P Q : C}
    (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Q) (e : P ≅ Q) :
    (a ≫ b ≫ c ≫ e.inv) ≫ e.hom = a ≫ b ≫ c := by
  simp

/-! ### Flatness of morphisms of algebraic spaces at a point: composition and descent -/

/-- **Stacks 05VX, part (1), at the structure sheaf.** If `f : X ⟶ Y` is flat at a point `x` of
`X` and `g : Y ⟶ Z` is flat at the image of `x`, then `f ≫ g` is flat at `x`.

Over the étale local rings this is transitivity of flatness, read at a geometric point above
`x` through the flatness criterion of **Stacks 04NG**. -/
private theorem isFlatAt_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Space.points B S hS X)
    (hf : Space.IsFlatAt B S hS f x)
    (hg : Space.IsFlatAt B S hS g (Space.pointsMap B S hS X f x)) :
    Space.IsFlatAt B S hS (f ≫ g) x := by
  obtain ⟨xbar, rfl⟩ := Space.exists_geometricRepresentative B S hS X x
  rw [Space.isFlatAt_iff_etaleLocalRingMap_flat hX hZ (f ≫ g) xbar]
  rw [Space.isFlatAt_iff_etaleLocalRingMap_flat hX hY f xbar] at hf
  rw [← Space.geometricPointMap_image f xbar,
    Space.isFlatAt_iff_etaleLocalRingMap_flat hY hZ g (Space.geometricPointMap f xbar)] at hg
  rw [← Space.etaleLocalRingMap_comp hX hY f g xbar]
  exact RingHom.Flat.comp hg hf

/-- **Stacks 05VY at a point, at the structure sheaf.** If `f : X ⟶ Y` is flat at a point `x` of
`X` and `f ≫ g` is flat at `x`, then `g : Y ⟶ Z` is flat at the image of `x`.

Over the étale local rings this is flat permanence (**Stacks 039V**): the étale local ring of `X`
at a geometric point above `x` is flat over that of `Z`, and faithfully flat over that of `Y`
because a flat local homomorphism of local rings is faithfully flat. No surjectivity hypothesis
is needed, in contrast with the global statement
`AlgebraicGeometry.Space.isFlat_of_comp_of_isSurjective_of_isFlat`. -/
private theorem isFlatAt_of_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Space.points B S hS X)
    (hf : Space.IsFlatAt B S hS f x)
    (hfg : Space.IsFlatAt B S hS (f ≫ g) x) :
    Space.IsFlatAt B S hS g (Space.pointsMap B S hS X f x) := by
  obtain ⟨xbar, rfl⟩ := Space.exists_geometricRepresentative B S hS X x
  rw [Space.isFlatAt_iff_etaleLocalRingMap_flat hX hY f xbar] at hf
  rw [Space.isFlatAt_iff_etaleLocalRingMap_flat hX hZ (f ≫ g) xbar] at hfg
  rw [← Space.geometricPointMap_image f xbar,
    Space.isFlatAt_iff_etaleLocalRingMap_flat hY hZ g (Space.geometricPointMap f xbar)]
  let ybar := Space.geometricPointMap f xbar
  let A := Space.etaleLocalRing B S hS Y ybar
  let C := Space.etaleLocalRing B S hS Z (Space.geometricPointMap g ybar)
  let M := Space.etaleLocalRing B S hS X xbar
  let α := Space.etaleLocalRingMap hX f xbar
  let β := Space.etaleLocalRingMap hY g ybar
  let γ := Space.etaleLocalRingMap hX (f ≫ g) xbar
  have hαγ : γ = α.comp β := (Space.etaleLocalRingMap_comp hX hY f g xbar).symm
  let _ : Algebra C A := β.toAlgebra
  let _ : Algebra A M := α.toAlgebra
  let _ : Algebra C M := γ.toAlgebra
  let _ : IsScalarTower C A M := IsScalarTower.of_algebraMap_smul fun c n => by
    change α (β c) • n = γ c • n
    rw [RingHom.congr_fun hαγ c]
    rfl
  have : IsLocalRing A := Space.isLocalRing_etaleLocalRing B S hS Y hY ybar
  have : IsLocalRing M := Space.isLocalRing_etaleLocalRing B S hS X hX xbar
  have : IsLocalHom (algebraMap A M) := Space.isLocalHom_etaleLocalRingMap B S hS hX hY f xbar
  have : Module.Flat A M := hf
  have : Module.Flat C M := hfg
  have : Module.FaithfullyFlat A M := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat M

/-- **Precomposing with an isomorphism of schemes does not affect flatness at a point.** This
is a re-derivation of a `private` lemma of
`StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite`, repeated here rather than
reached by `import all` so that this module does not acquire that file's import cone. -/
private theorem schemeIsFlatAt_comp_of_isIso {P Q A : Scheme.{u}} (e : P ⟶ Q) [IsIso e]
    (q : Q ⟶ A) (t : P) (hflat : AlgebraicGeometry.IsFlatAt q.toLRSHom.toShHom (e t)) :
    AlgebraicGeometry.IsFlatAt (e ≫ q).toLRSHom.toShHom t := by
  have hbij : Function.Bijective (e.stalkMap t).hom := ConcreteCategory.bijective_of_isIso _
  have hcomp : ((q.stalkMap (e t) ≫ e.stalkMap t).hom).Flat := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.Flat.comp_iff_of_bijective_left hbij).mpr hflat
  have heq := congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp e q t)
  change ((e ≫ q).stalkMap t).hom.Flat
  exact heq ▸ hcomp

/-- **Base change of flatness at a point, for morphisms of schemes.** In a cartesian square the
projection to the new base is flat at a point as soon as the morphism it is a base change of is
flat at the image point. This is
`AlgebraicGeometry.isFlatAt_pullback_fst_of_isFlatAt` transported along the comparison with the
canonical fibre product, and it is a re-derivation of a `private` lemma of
`StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite`. -/
private theorem schemeIsFlatAt_of_isPullback {P A X' Y' : Scheme.{u}} {p : P ⟶ A} {q : P ⟶ X'}
    {w : A ⟶ Y'} {f : X' ⟶ Y'} (hsq : IsPullback p q w f) (t : P)
    (hflat : AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom (q t)) :
    AlgebraicGeometry.IsFlatAt p.toLRSHom.toShHom t := by
  have hsnd : (Limits.pullback.snd w f) (hsq.isoPullback.hom t) = q t := by
    rw [← Scheme.Hom.comp_apply, hsq.isoPullback_hom_snd]
  have hbase : AlgebraicGeometry.IsFlatAt (Limits.pullback.fst w f).toLRSHom.toShHom
      (hsq.isoPullback.hom t) :=
    AlgebraicGeometry.isFlatAt_pullback_fst_of_isFlatAt w f _ (by rw [hsnd]; exact hflat)
  exact hsq.isoPullback_hom_fst ▸
    schemeIsFlatAt_comp_of_isIso hsq.isoPullback.hom (Limits.pullback.fst w f) t hbase

/-- **Base change of flatness at a point, for morphisms of algebraic spaces** — the structure
sheaf case of **Stacks 05VW**. In a cartesian square of algebraic spaces over `S`, the
projection to the new base is flat at a point of the apex as soon as the morphism it is a base
change of is flat at the image of that point.

Compatible surjective étale charts of the cartesian square
(`AlgebraicGeometry.Space.exists_compatible_etale_charts`) give a chart `V` of the target, a
chart `U ⟶ V` of `f`, a chart `V' ⟶ V` of `g` and the induced chart `U' = U ×_V V' ⟶ V'` of the
base change, with `U'` an atlas of the fibre product. A field-valued point of `U'` lying over
the given point turns the two squares into pointed étale charts, whose selected scheme points
correspond under `U' ⟶ U`. Flatness of a morphism of germs being étale local on source and
target (**Stacks 04ND**), flatness at a point is the induced germ condition read in any one
pointed chart (**Stacks 04NC**), so the statement becomes the one for schemes.

This declaration carries no `@[stacks]` attribute: Stacks 05VW is a statement about modules and
is not formalized in this development, and this is only the unexported ingredient that the
equivalence of **Stacks 0CIC** needs. -/
private theorem isFlatAt_of_isPullback
    {X₁ X₀ Y₁ Y₀ : AlgebraicSpaces B S hS} {g' : X₁ ⟶ X₀} {f' : X₁ ⟶ Y₁} {f : X₀ ⟶ Y₀}
    {g : Y₁ ⟶ Y₀} (sq : IsPullback g' f' f g) (x' : Space.points B S hS X₁.1)
    (hf : Space.IsFlatAt B S hS f.hom (Space.pointsMap B S hS X₁.1 g'.hom x')) :
    Space.IsFlatAt B S hS f'.hom x' := by
  classical
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    Space.inverseImage_isStableUnderComposition B S hS Space.etale_isStableUnderComposition
  have hQbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  obtain ⟨U, V, U', V', p, q, pU, pV', v, a, b, c, hcharts, hap, hbq, hcX, hcY,
      hvSurj, hvEtale, haSurj, haEtale, hbSurj, hbEtale, hcSurj, hcEtale⟩ :=
    Space.exists_compatible_etale_charts B S hS f g
  let eAs : X₁ ≅ AlgebraicSpaces.fiberProduct B S hS f g :=
    sq.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f g)
  let e : X₁.1 ≅ Limits.pullback f.hom g.hom :=
    { hom := eAs.hom.hom
      inv := eAs.inv.hom
      hom_inv_id := congrArg (fun k => k.hom) eAs.hom_inv_id
      inv_hom_id := congrArg (fun k => k.hom) eAs.inv_hom_id }
  have heFst : e.hom ≫ Limits.pullback.fst f.hom g.hom = g'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_fst _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heSnd : e.hom ≫ Limits.pullback.snd f.hom g.hom = f'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_snd _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heInvSnd : e.inv ≫ f'.hom = Limits.pullback.snd f.hom g.hom := by
    rw [← heSnd, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hcXEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ e.inv) :=
    have _ : IsIso e.inv := ⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩
    MorphismProperty.RespectsIso.postcomp _ e.inv c hcEtale
  have hcommF : yoneda.map p ≫ v = (a ≫ Limits.pullback.snd v f.hom) ≫ f.hom := by
    calc yoneda.map p ≫ v = (a ≫ Limits.pullback.fst v f.hom) ≫ v := by rw [← hap]
      _ = (a ≫ Limits.pullback.snd v f.hom) ≫ f.hom := by
          simp only [Category.assoc, Limits.pullback.condition]
  have hcommF' : yoneda.map pV' ≫ (b ≫ Limits.pullback.snd v g.hom) = (c ≫ e.inv) ≫ f'.hom := by
    calc yoneda.map pV' ≫ (b ≫ Limits.pullback.snd v g.hom)
        = c ≫ Limits.pullback.snd f.hom g.hom := by
          simpa only [Category.assoc] using hcY.symm
      _ = (c ≫ e.inv) ≫ f'.hom := by rw [Category.assoc, heInvSnd]
  obtain ⟨z, hz⟩ :=
    (Space.surjective_iff_surjective_pointsMap B S hS (Limits.pullback f.hom g.hom)
      (isAlgebraicSpace_pullback B S hS f.hom g.hom X₀.property Y₁.property Y₀.property)
      U' c).mp hcSurj (Space.pointsMap B S hS X₁.1 e.hom x')
  obtain ⟨r, rfl⟩ := Quot.exists_rep z
  have hz' : Space.pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U')) =
      Space.pointsMap B S hS X₁.1 e.hom x' := hz
  let chartF : Space.EtaleChartAtPoint B S hS f.hom
      (Space.pointsMap B S hS X₁.1 g'.hom x') :=
    { U := U
      V := V
      a := a ≫ Limits.pullback.snd v f.hom
      b := v
      h := p
      a_etale := MorphismProperty.comp_mem _ a (Limits.pullback.snd v f.hom) haEtale
        (hQbc.of_isPullback (IsPullback.of_hasPullback v f.hom) hvEtale)
      b_etale := hvEtale
      comm := hcommF
      representative := Space.FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : Space.pointsMap B S hS (yoneda.obj U) (a ≫ Limits.pullback.snd v f.hom)
            ((Space.FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r).class B S hS
              (yoneda.obj U)) =
            Space.pointsMap B S hS (yoneda.obj U')
              (yoneda.map pU ≫ a ≫ Limits.pullback.snd v f.hom)
              (r.class B S hS (yoneda.obj U')) := rfl
        have h₂ : Space.pointsMap B S hS (yoneda.obj U')
            (c ≫ Limits.pullback.fst f.hom g.hom) (r.class B S hS (yoneda.obj U')) =
            Space.pointsMap B S hS (Limits.pullback f.hom g.hom)
              (Limits.pullback.fst f.hom g.hom)
              (Space.pointsMap B S hS (yoneda.obj U') c
                (r.class B S hS (yoneda.obj U'))) := rfl
        have h₃ : Space.pointsMap B S hS (Limits.pullback f.hom g.hom)
            (Limits.pullback.fst f.hom g.hom) (Space.pointsMap B S hS X₁.1 e.hom x') =
            Space.pointsMap B S hS X₁.1 (e.hom ≫ Limits.pullback.fst f.hom g.hom) x' :=
          (congrFun (Space.pointsMap_comp B S hS X₁.1 e.hom
            (Limits.pullback.fst f.hom g.hom)) x').symm
        rw [h₁, ← hcX, h₂, hz', h₃, heFst] }
  let chartF' : Space.EtaleChartAtPoint B S hS f'.hom x' :=
    { U := U'
      V := V'
      a := c ≫ e.inv
      b := b ≫ Limits.pullback.snd v g.hom
      h := pV'
      a_etale := hcXEtale
      b_etale := MorphismProperty.comp_mem _ b (Limits.pullback.snd v g.hom) hbEtale
        (hQbc.of_isPullback (IsPullback.of_hasPullback v g.hom) hvEtale)
      comm := hcommF'
      representative := r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : Space.pointsMap B S hS (yoneda.obj U') (c ≫ e.inv)
            (r.class B S hS (yoneda.obj U')) =
            Space.pointsMap B S hS (Limits.pullback f.hom g.hom) e.inv
              (Space.pointsMap B S hS (yoneda.obj U') c
                (r.class B S hS (yoneda.obj U'))) := rfl
        have h₂ : Space.pointsMap B S hS (Limits.pullback f.hom g.hom) e.inv
            (Space.pointsMap B S hS X₁.1 e.hom x') =
            Space.pointsMap B S hS X₁.1 (e.hom ≫ e.inv) x' :=
          (congrFun (Space.pointsMap_comp B S hS X₁.1 e.hom e.inv) x').symm
        rw [h₁, hz', h₂, e.hom_inv_id, Space.pointsMap_id, id_eq] }
  have hsource : chartF.sourcePoint B S hS =
      (BigFppfOver.toScheme B S hS).map pU (chartF'.sourcePoint B S hS) := by
    change ((BigFppfOver.toScheme B S hS).map (r.value ≫ pU))
        (IsLocalRing.closedPoint r.carrier) =
      (BigFppfOver.toScheme B S hS).map pU
        (((BigFppfOver.toScheme B S hS).map r.value) (IsLocalRing.closedPoint r.carrier))
    rw [Functor.map_comp]
    exact Scheme.Hom.comp_apply _ _ _
  refine (Space.holdsOnEveryEtaleChartAtPoint_iff_some B S hS _
    MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat X₁.property Y₁.property
    f'.hom x').mpr ⟨chartF', ?_⟩
  refine (MorphismOfGerms.isFlat_ofSchemeHom_iff _ _).mpr ?_
  refine schemeIsFlatAt_of_isPullback hcharts.flip (chartF'.sourcePoint B S hS) ?_
  rw [← hsource]
  exact (MorphismOfGerms.isFlat_ofSchemeHom_iff _ _).mp (hf chartF)

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_of_isPullback` read on presheaves: the
category of algebraic spaces over `S` is a full subcategory of presheaves, so a cartesian square
of presheaves with algebraic corners is cartesian there. -/
private theorem isFlatAt_of_isPullback_presheaf
    {X₁ X₀ Y₁ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX₀ : IsAlgebraicSpace B S hS X₀)
    (hY₁ : IsAlgebraicSpace B S hS Y₁) (hY₀ : IsAlgebraicSpace B S hS Y₀)
    {g' : X₁ ⟶ X₀} {f' : X₁ ⟶ Y₁} {f : X₀ ⟶ Y₀} {g : Y₁ ⟶ Y₀}
    (sq : IsPullback g' f' f g) (x' : Space.points B S hS X₁)
    (hf : Space.IsFlatAt B S hS f (Space.pointsMap B S hS X₁ g' x')) :
    Space.IsFlatAt B S hS f' x' :=
  isFlatAt_of_isPullback B S hS
    (X₁ := ⟨X₁, hX₁⟩) (X₀ := ⟨X₀, hX₀⟩) (Y₁ := ⟨Y₁, hY₁⟩) (Y₀ := ⟨Y₀, hY₀⟩)
    (g' := ObjectProperty.homMk g') (f' := ObjectProperty.homMk f')
    (f := ObjectProperty.homMk f) (g := ObjectProperty.homMk g)
    (IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) sq) x' hf

/-- A flat morphism of algebraic spaces over `S` is flat at every point of its source; this is
one direction of **Stacks 03MM**. -/
private theorem isFlatAt_of_isFlat {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G)
    (x : Space.points B S hS F) (hg : Space.IsFlat B S hS g) :
    Space.IsFlatAt B S hS g x :=
  (Space.isFlat_iff_forall_isFlatAt B S hS g).1 hg x

/-! ### Flatness of 1-morphisms between the stacks of algebraic spaces -/

/-- **Flatness of the 1-morphism attached to a morphism of algebraic spaces.** The 1-morphism of
**Stacks 0458** induced by a morphism `f` of algebraic spaces over `S` is flat — in the sense of
the existential smooth-diagram criterion of **Stacks 06FM** — exactly when `f` is flat.

Source and target are representable by the algebraic spaces themselves, so the third assertion
of Stacks 06FM reads the criterion on the induced morphism of representing presheaves, which is
`f` itself by `AlgebraicGeometry.Stack.representingMap_associatedMap`. -/
private theorem hasPropertyOnSomeSmoothDiagram_associatedMap_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    Stack.HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ g => Space.IsFlat B S hS g)
        (Stack.associatedMap B S hS f).1 ↔
      Space.IsFlat B S hS f := by
  refine Iff.trans (Stack.hasPropertyOnSomeSmoothDiagram_iff_represented.{u, u} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
    (Stack.isAlgebraicStack_fibredCategory.{u, u} B S hS F hF)
    (Stack.isAlgebraicStack_fibredCategory.{u, u} B S hS G hG) F G hF hG
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) _) ?_
  rw [Stack.representingMap_associatedMap]

/-- A diagram of algebraic spaces over a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`,
marked at a point of its top left corner above a point `x` of `|𝒳|`, whose right vertical
1-morphism and whose comparison 1-morphisms to the 2-fibre products of the cospan `(b, f)` are
flat. These are the diagrams **Stacks 0CIC** tests flatness of `f` at `x` on. -/
structure PointedFlatDiagram {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (x : points B S hS 𝒳) where
  /-- the algebraic space in the top left corner -/
  U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- the algebraic space in the top right corner -/
  V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `U` is an algebraic space over `S` -/
  algebraicU : IsAlgebraicSpace B S hS U
  /-- `V` is an algebraic space over `S` -/
  algebraicV : IsAlgebraicSpace B S hS V
  /-- the left vertical 1-morphism -/
  a : Stack.fibredCategory B S hS U ⟶ 𝒳.val
  /-- the right vertical 1-morphism -/
  b : Stack.fibredCategory B S hS V ⟶ 𝒴.val
  /-- the top horizontal morphism of algebraic spaces -/
  h : U ⟶ V
  /-- the invertible 2-cell filling the square -/
  iso : (Stack.associatedMap B S hS h).1 ≫ b ≅ a ≫ f.hom
  /-- the marked point of `|U|` -/
  u : Space.points B S hS U
  /-- the marked point lies over `x` -/
  liesOver : Stack.spacePointMap B S hS U 𝒳.val a.hom u = x
  /-- the right vertical 1-morphism is flat -/
  flatB : Stack.HasPropertyOnSomeSmoothDiagram B S hS
    (fun _ _ g => Space.IsFlat B S hS g) b
  /-- every comparison 1-morphism to a 2-fibre product of the cospan `(b, f)` is flat -/
  flatComparison : ∀ (Q : Bicategory.TwoCommSq b f.hom)
    (_hQ : Bicategory.IsTwoFibreProduct Q)
    (k : Bicategory.TwoCommSq.PreHom
      (Stack.diagramCone B S hS f.hom a b h iso) Q),
    Stack.HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ g => Space.IsFlat B S hS g) k.hom

/-- **Stacks 0CID.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is *flat at* a point
`x` of `|𝒳|` when the top horizontal morphism of some diagram of
`AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram` is flat at its marked point.

**Stacks 0CIC** identifies this with the corresponding condition on every such diagram, so the
choice of the existential formulation is immaterial. -/
@[stacks 0CID]
abbrev IsFlatAt {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (x : points B S hS 𝒳) : Prop :=
  ∃ d : PointedFlatDiagram B S hS f x, Space.IsFlatAt B S hS d.h d.u

variable {B S hS}

/-- **The left vertical 1-morphism of a diagram of Stacks 0CIC is flat.** It is 2-isomorphic to
the comparison `(a, h) : U ⟶ 𝒳 ×_𝒴 V` followed by the projection `𝒳 ×_𝒴 V ⟶ 𝒳`, which is flat
as a base change of `b` (**Stacks 06PY**), and the comparison is flat by hypothesis.

The 2-fibre product is taken at the canonical square of **Stacks 04T2**; its universal property
is needed in the ambient 2-category of categories fibred in groupoids, where the comparison
1-morphisms of the diagram live, and that is
`AlgebraicGeometry.Stack.isTwoFibreProduct_underlying_algebraicStacks`. -/
private theorem PointedFlatDiagram.source_flat
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    {x : points B S hS 𝒳} (d : PointedFlatDiagram B S hS f x) :
    Stack.HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ g => Space.IsFlat B S hS g) d.a := by
  classical
  let bst : Stack.algebraicSpaceStack.{u, w} B S hS d.V d.algebraicV ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom d.b
  let Qs := Stack.twoFibreProductSquareAlgebraicStacks B S hS bst f
  have hQs := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS bst f
  have hQ : Bicategory.IsTwoFibreProduct Qs.underlying :=
    Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS Qs hQs
  let k : Bicategory.TwoCommSq.PreHom (Stack.diagramCone B S hS f.hom d.a d.b d.h d.iso)
    Qs.underlying := Quotient.out (hQ.from _)
  have hk : IsFlat B S hS
      (Bicategory.InducedBicategory.mkHom k.hom :
        Stack.algebraicSpaceStack.{u, w} B S hS d.U d.algebraicU ⟶ Qs.pt) :=
    d.flatComparison Qs.underlying hQ k
  exact Stack.hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS _ k.isoSnd.symm
    (isFlat_comp B S hS _ Qs.snd hk
      (isFlat_baseChange B S hS bst f Qs.swap (Bicategory.isTwoFibreProduct_swap hQs) d.flatB))

/-- **A morphism of representing presheaves recovers its 1-morphism up to a 2-isomorphism.**
Let `g : 𝒳 ⟶ W'` be a 1-morphism from a category fibred in groupoids represented by an algebraic
space `W` to the category of elements of an algebraic space `U`. The 1-morphism of
**Stacks 0458** attached to the morphism `W ⟶ U` that `g` induces is 2-isomorphic to the backward
1-morphism of the representing equivalence followed by `g`.

Both induce the same morphism of representing presheaves — the left by
`AlgebraicGeometry.Stack.representingMap_associatedMap`, the right by functoriality together with
`AlgebraicGeometry.Stack.representingMap_equivalenceOverInvMap` — so the uniqueness clause of
**Stacks 04SW** supplies the 2-isomorphism. -/
private theorem nonempty_twoIso_associatedMap_representingMap
    {𝒬 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {W U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : StacksRepresentableCFG.EquivalenceOver 𝒬.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (g : 𝒬 ⟶ Stack.fibredCategory B S hS U) :
    Nonempty ((Stack.associatedMap B S hS (Stack.representingMap B S hS 𝒬
          (Stack.fibredCategory B S hS U) W U e
          (StacksRepresentableCFG.EquivalenceOver.refl _) g)).1 ≅
      Stack.equivalenceOverInvMap B S hS W e ≫ g) := by
  refine (Stack.nonempty_unique_twoIso_of_representingMap_eq B S hS
    (Stack.fibredCategory B S hS W) (Stack.fibredCategory B S hS U) W U
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) ?_).map (fun h => h.default)
  rw [Stack.representingMap_associatedMap, Stack.representingMap_comp B S hS W W U
    (StacksRepresentableCFG.EquivalenceOver.refl _) e
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (Stack.equivalenceOverInvMap B S hS W e) g,
    Stack.representingMap_equivalenceOverInvMap, Category.id_comp]

/-- The morphism of representing presheaves of a flat 1-morphism is flat, respects points and
recovers the 1-morphism up to 2-isomorphism. -/
private theorem flat_representingMap_pointsMap_eq
    {𝒬 : Stack.AlgebraicStacks.{u, w} B S hS} {W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hY : IsAlgebraicSpace B S hS Y)
    (e : StacksRepresentableCFG.EquivalenceOver 𝒬.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (c : 𝒬 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Y hY) (zW : Space.points B S hS W)
    {pbar : Stack.points B S hS 𝒬.val.val 𝒬.val.property}
    (hzW : Stack.spacePointMap B S hS W 𝒬.val
      (Stack.representingEquivalence B S hS W 𝒬.val e).functor zW = pbar)
    (hc : IsFlat B S hS c) {y : Space.points B S hS Y}
    (hy : Stack.pointsMap B S hS 𝒬.val.val 𝒬.val.property
        (Stack.algebraicSpaceStack.{u, w} B S hS Y hY).val.property c.hom.hom pbar =
      Stack.spacePointMap B S hS Y (Stack.fibredCategory B S hS Y)
        (BasedFunctor.id (Stack.fibredCategory B S hS Y).val) y) :
    Space.IsFlat B S hS (Stack.representingMap B S hS 𝒬.val
        (Stack.algebraicSpaceStack.{u, w} B S hS Y hY).val W Y e
        (StacksRepresentableCFG.EquivalenceOver.refl _) c.hom) ∧
      Space.pointsMap B S hS W (Stack.representingMap B S hS 𝒬.val
        (Stack.algebraicSpaceStack.{u, w} B S hS Y hY).val W Y e
        (StacksRepresentableCFG.EquivalenceOver.refl _) c.hom) zW = y ∧
      Nonempty ((Stack.associatedMap B S hS (Stack.representingMap B S hS 𝒬.val
        (Stack.fibredCategory B S hS Y) W Y e (StacksRepresentableCFG.EquivalenceOver.refl _)
        c.hom)).1 ≅ Stack.equivalenceOverInvMap B S hS W e ≫ c.hom) := by
  have nat := Stack.spacePointMap_representing_naturality B S hS W Y 𝒬.val
    (Stack.algebraicSpaceStack.{u, w} B S hS Y hY).val e
    (StacksRepresentableCFG.EquivalenceOver.refl _) c.hom zW
  have hflat := Stack.isFlat_representingMap_of_isFlat.{u, w} B S hS W Y hW hY e
    (StacksRepresentableCFG.EquivalenceOver.refl _) c hc
  exact ⟨hflat,
    (Stack.spacePointMap_id_bijective B S hS Y).injective
      (nat.trans ((congrArg (Stack.pointsMap B S hS 𝒬.val.val 𝒬.val.property
        (Stack.algebraicSpaceStack.{u, w} B S hS Y hY).val.property c.hom.hom) hzW).trans hy)),
    nonempty_twoIso_associatedMap_representingMap e c.hom⟩

/-- **Two flat charts of an algebraic stack through one point are refined by a common flat one**,
with the 2-fibre product square of the two charts and its representability taken as data.

The two projections of the square are flat as base changes of the two charts (**Stacks 06PY**),
the point of the apex over the two given points exists by **Stacks 04XH**, and the morphisms of
algebraic spaces are the ones the projections induce on representing presheaves
(**Stacks 04SW**). The 2-isomorphism is the filler of the square, conjugated by the comparisons
of `AlgebraicGeometry.Stack.AlgebraicStacks.nonempty_twoIso_associatedMap_representingMap`.

The square is a parameter rather than the canonical one so that the proof term stays small. -/
private theorem exists_flat_space_common_refinement_of_square
    {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (ast : Stack.algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (bst : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳)
    (ha : IsFlat B S hS ast) (hb : IsFlat B S hS bst)
    (P : Bicategory.TwoCommSq ast bst) (hP : Bicategory.IsTwoFibreProduct P)
    (hrep : Stack.IsRepresentableByAlgebraicSpace B S hS P.pt.val)
    (u : Space.points B S hS U) (v : Space.points B S hS V)
    (huv : Stack.spacePointMap B S hS U 𝒳.val ast.hom.hom u =
      Stack.spacePointMap B S hS V 𝒳.val bst.hom.hom v) :
    ∃ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS W)
      (p : W ⟶ U) (q : W ⟶ V) (w : Space.points B S hS W),
      Space.IsFlat B S hS p ∧ Space.IsFlat B S hS q ∧
      Space.pointsMap B S hS W p w = u ∧ Space.pointsMap B S hS W q w = v ∧
      Nonempty ((Stack.associatedMap B S hS p).1 ≫ ast.hom ≅
        (Stack.associatedMap B S hS q).1 ≫ bst.hom) := by
  classical
  have hPfst := isFlat_baseChange B S hS bst ast P hP hb
  have hPsnd := isFlat_baseChange B S hS ast bst P.swap (Bicategory.isTwoFibreProduct_swap hP) ha
  obtain ⟨W, hW, ⟨e⟩⟩ := hrep
  have e1 := congrFun (Stack.spacePointMap_eq_pointsMap_comp B S hS U 𝒳.val ast.hom.hom) u
  have e2 := congrFun (Stack.spacePointMap_eq_pointsMap_comp B S hS V 𝒳.val bst.hom.hom) v
  simp only [Function.comp_apply] at e1 e2
  obtain ⟨pbar, hbar₁, hbar₂⟩ :=
    Stack.exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP _ _
      (e1.symm.trans (huv.trans e2))
  obtain ⟨zW, hzW⟩ :=
    (Stack.bijective_spacePointMap_representing B S hS W P.pt.val e).surjective pbar
  obtain ⟨hp, hzp, ⟨ep⟩⟩ := flat_representingMap_pointsMap_eq hW hU e P.fst zW hzW hPfst hbar₁
  obtain ⟨hq, hzq, ⟨eq'⟩⟩ := flat_representingMap_pointsMap_eq hW hV e P.snd zW hzW hPsnd hbar₂
  exact ⟨W, hW, _, _, zW, hp, hq, hzp, hzq,
    ⟨Bicategory.whiskerRightIso ep ast.hom ≪≫
      Bicategory.associator (Stack.equivalenceOverInvMap B S hS W e) P.fst.hom ast.hom ≪≫
      Bicategory.whiskerLeftIso (Stack.equivalenceOverInvMap B S hS W e)
        (Bicategory.InducedBicategory.isoHom P.iso) ≪≫
      (Bicategory.associator (Stack.equivalenceOverInvMap B S hS W e) P.snd.hom bst.hom).symm ≪≫
      Bicategory.whiskerRightIso eq'.symm bst.hom⟩⟩

/-- **The flat condition on comparisons needs checking at a single 2-fibre product.** If one
comparison 1-morphism from a 2-commutative square `T` to one 2-fibre product of a cospan passes
the existential smooth-diagram criterion of **Stacks 06FM**, then so does every comparison
1-morphism from `T` to every 2-fibre product of that cospan.

The comparison of the two 2-fibre products is an equivalence, and terminality identifies the
composite with the given comparison; the diagram witnessing the criterion is carried across by
postcomposing its right vertical 1-morphism with that equivalence, which keeps it smooth by
`AlgebraicGeometry.Stack.isRelativelySmooth_comp_of_isEquivalence` and leaves its top horizontal
morphism of algebraic spaces untouched. -/
private theorem hasPropertyOnSomeSmoothDiagram_preHom_of_preHom
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {T Q₁ Q₂ : Bicategory.TwoCommSq g f}
    (hQ₁ : Bicategory.IsTwoFibreProduct Q₁) (hQ₂ : Bicategory.IsTwoFibreProduct Q₂)
    (k₁ : Bicategory.TwoCommSq.PreHom T Q₁) (k₂ : Bicategory.TwoCommSq.PreHom T Q₂)
    (hk : Stack.HasPropertyOnSomeSmoothDiagram B S hS P k₁.hom) :
    Stack.HasPropertyOnSomeSmoothDiagram B S hS P k₂.hom := by
  classical
  obtain ⟨U, V, hU, hV, a, b, h₀, ⟨η⟩, ha, hasurj, hb, hPh⟩ := hk
  let d : Bicategory.TwoCommSq.PreHom Q₁ Q₂ := Quotient.out (hQ₂.from Q₁)
  obtain ⟨θ, -, -⟩ : Bicategory.TwoCommSq.PreHom.Rel (k₁.comp d) k₂ :=
    Quotient.exact (hQ₂.hom_ext (Quotient.mk _ (k₁.comp d)) (Quotient.mk _ k₂))
  refine ⟨U, V, hU, hV, a, b ≫ d.hom, h₀, ⟨?_⟩, ha, hasurj,
    Stack.isRelativelySmooth_comp_of_isEquivalence B S hS b d.hom
      (Bicategory.isEquivalence_of_isTwoFibreProduct hQ₁ hQ₂ d) hb, hPh⟩
  exact (Bicategory.associator (Stack.associatedMap B S hS h₀).1 b d.hom).symm ≪≫
    Bicategory.whiskerRightIso η d.hom ≪≫ Bicategory.associator a k₁.hom d.hom ≪≫
    Bicategory.whiskerLeftIso a θ

/-- **The 1-morphism attached to the morphism of representing presheaves induced by a
1-morphism of categories of elements is 2-isomorphic to it.** Both induce the same morphism of
representing presheaves, by `AlgebraicGeometry.Stack.representingMap_associatedMap`, so the
uniqueness clause of **Stacks 04SW** supplies the 2-isomorphism. -/
private theorem nonempty_twoIso_associatedMap_representingMap_self
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Stack.fibredCategory B S hS U ⟶ Stack.fibredCategory B S hS V) :
    Nonempty ((Stack.associatedMap B S hS (Stack.representingMap B S hS
          (Stack.fibredCategory B S hS U) (Stack.fibredCategory B S hS V) U V
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) g)).1 ≅ g) :=
  (Stack.nonempty_unique_twoIso_of_representingMap_eq B S hS
    (Stack.fibredCategory B S hS U) (Stack.fibredCategory B S hS V) U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (by rw [Stack.representingMap_associatedMap])).map (fun h => h.default)

/-- **An algebraic stack over `S` has a flat chart by an algebraic space surjective on points.**
A smooth presentation by an algebraic space, surjective on objects, is flat by the
identity-diagram criterion of **Stacks 06FM** together with
`AlgebraicGeometry.Space.isFlat_id`, and surjective on objects implies surjective on points by
**Stacks 04XI**. -/
private theorem exists_flat_surjective_space_chart (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hV : IsAlgebraicSpace B S hS V)
      (b : Stack.fibredCategory B S hS V ⟶ 𝒵.val),
      Stack.HasPropertyOnSomeSmoothDiagram B S hS
        (fun _ _ k => Space.IsFlat B S hS k) b ∧
      Function.Surjective (Stack.spacePointMap B S hS V 𝒵.val b.hom) := by
  obtain ⟨V, hV, b, hbsm, hbsu⟩ :=
    Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      𝒵.property
  refine ⟨V, hV, b, Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ b V hV
    (StacksRepresentableCFG.EquivalenceOver.refl _) hbsm (Space.isFlat_id B S hS hV), ?_⟩
  have hcomp := Stack.spacePointMap_comp B S hS V (Stack.fibredCategory B S hS V) 𝒵.val
    (BasedFunctor.id (Stack.fibredCategory B S hS V).val) b.hom
  rw [BasedFunctor.id_comp] at hcomp
  rw [hcomp]
  exact (Stack.pointsMap_surjective_of_isSurjectiveOnObjects B S hS
    (𝒳 := Stack.algebraicSpaceStack.{u, w} B S hS V hV) (𝒴 := 𝒵)
    (Bicategory.InducedBicategory.mkHom b) hbsu).comp
    (Stack.spacePointMap_id_bijective B S hS V).surjective

/-- **Every point of a 1-morphism's source lies on a diagram of Stacks 0CIC.** The diagram is
built from a flat chart `b` of the target by an algebraic space surjective on points and a flat
chart `i` of the 2-fibre product `𝒳 ×_𝒴 V` by an algebraic space surjective on points: the left
vertical 1-morphism is `i` followed by the projection to `𝒳`, the top horizontal morphism of
algebraic spaces is the one `i` followed by the projection to `V` induces on representing
presheaves (**Stacks 04SW**), and the marked point is a point of the chart above a point of the
2-fibre product over the given point and a point of `V` over its image (**Stacks 04XH**).

The comparison with the canonical 2-fibre product is `i` itself, which is flat, and
`AlgebraicGeometry.Stack.AlgebraicStacks.hasPropertyOnSomeSmoothDiagram_preHom_of_preHom`
carries that to every 2-fibre product and every comparison. -/
private theorem nonempty_pointedFlatDiagram
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (x : points B S hS 𝒳) :
    Nonempty (PointedFlatDiagram B S hS f x) := by
  classical
  obtain ⟨V, hV, b, hb, hbsurj⟩ := exists_flat_surjective_space_chart 𝒴
  let bst : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom b
  let Ps := Stack.twoFibreProductSquareAlgebraicStacks B S hS bst f
  have hPs := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS bst f
  let R : Bicategory.TwoCommSq b f.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f.hom
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b f.hom
  obtain ⟨v, hv⟩ := hbsurj (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property
    𝒴.val.property f.hom.hom x)
  have hvcomp := congrFun (Stack.spacePointMap_eq_pointsMap_comp B S hS V 𝒴.val b.hom) v
  simp only [Function.comp_apply] at hvcomp
  obtain ⟨z, -, hzx⟩ := Stack.exists_point_of_isTwoFibreProduct_algebraicStacks B S hS Ps hPs
    _ x (hvcomp.symm.trans hv)
  obtain ⟨U, hU, i, hi, hisurj⟩ := exists_flat_surjective_space_chart Ps.pt
  obtain ⟨u, hu⟩ := hisurj z
  obtain ⟨eh⟩ := nonempty_twoIso_associatedMap_representingMap_self (i ≫ R.fst)
  let h₀ := Stack.representingMap B S hS (Stack.fibredCategory B S hS U)
    (Stack.fibredCategory B S hS V) U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (i ≫ R.fst)
  let a₀ : Stack.fibredCategory B S hS U ⟶ 𝒳.val := i ≫ R.snd
  let η : (Stack.associatedMap B S hS h₀).1 ≫ b ≅ a₀ ≫ f.hom :=
    Bicategory.whiskerRightIso eh b ≪≫ Bicategory.associator i R.fst b ≪≫
      Bicategory.whiskerLeftIso i R.iso ≪≫
      (Bicategory.associator i R.snd f.hom).symm
  let j : Bicategory.TwoCommSq.PreHom
      (Stack.diagramCone B S hS f.hom a₀ b h₀ η) R :=
    { hom := i
      isoFst := eh
      isoSnd := Iso.refl a₀
      compat := by
        change η.hom ≫ Bicategory.whiskerRight (𝟙 a₀) f.hom ≫
            (Bicategory.associator i R.snd f.hom).hom =
          Bicategory.whiskerRight eh.hom b ≫ (Bicategory.associator i R.fst b).hom ≫
            Bicategory.whiskerLeft i R.iso.hom
        rw [Bicategory.id_whiskerRight, Category.id_comp]
        exact comp_assoc_inv_hom _ _ _ (Bicategory.associator i R.snd f.hom) }
  have hcomp :=
    congrFun (Stack.spacePointMap_comp B S hS U Ps.pt.val 𝒳.val i.hom
      R.snd.hom) u
  simp only [Function.comp_apply] at hcomp
  refine ⟨⟨U, V, hU, hV, a₀, b, h₀, η, u, ?_, hb, fun Q hQ k =>
    hasPropertyOnSomeSmoothDiagram_preHom_of_preHom _ hR hQ j k hi⟩⟩
  exact hcomp.trans ((congrArg (Stack.pointsMap B S hS Ps.pt.val.val
    Ps.pt.val.property 𝒳.val.property R.snd.hom) hu).trans hzx)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
