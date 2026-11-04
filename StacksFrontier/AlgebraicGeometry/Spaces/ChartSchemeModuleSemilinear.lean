module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction

/-!
# The scalars on the sections of the chart restriction of a module on an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `M` be a
quasi-coherent `𝒪_X`-module and let `A` be an étale scheme chart of `X`. The sections of the chart
restriction of `M` over a Zariski open `W` of the chart's scheme are, as a module over the
functions on `W`, the sections of `M` over the étale chart which `W` cuts out, with scalars
restricted along a ring map `chartSectionsRingHom` from the functions on `W` to the sections of
`𝒪_X` over that étale chart.

## Main definitions

* `AlgebraicGeometry.Space.chartSectionsRingHom`: the ring map along which the sections of the
  chart restriction are semilinear, the comparison of structure sheaves of the small étale site of
  the chart's scheme followed by the structure map of the inverse of the comparison of the two
  small étale sites.
* `AlgebraicGeometry.Space.chartSectionsLinearEquiv`: the chart sections identification, as a
  linear equivalence over the functions on the Zariski open.

## Main results

* `Stacks.SheafOfModules.pushforward_obj_val_obj` and
  `Stacks.SheafOfModules.smul_pushforward_obj_val_obj`: the sections of a pushforward of sheaves
  of modules are, as a module, the sections of the target with scalars restricted along the
  structure map; equivalently, the identification of the underlying types is semilinear along
  that map.
* `Stacks.SheafOfModules.pushforward_pushforward_obj_val_obj` and
  `Stacks.SheafOfModules.smul_pushforward_pushforward_obj_val_obj`: the same for two pushforwards
  at once, with the two structure maps composed.
* `Stacks.SheafOfModules.pushforward_pushforward_obj`: two pushforwards are the pushforward along
  the composite functor, with the two structure maps composed.
* `AlgebraicGeometry.SmallEtale.restrictModule_obj_val_obj_moduleCat` and
  `AlgebraicGeometry.SmallEtale.smul_restrictModule_obj_val_obj`: the sections of a restriction
  along the inclusion of the small Zariski site are semilinear over the comparison of structure
  sheaves.
* `AlgebraicGeometry.Space.surjective_chartSectionsRingHom`: the composite scalar map is
  surjective.
* `AlgebraicGeometry.Space.chartSchemeEtaleModule_eq_pushforward` and
  `AlgebraicGeometry.Space.chartSmallEtaleRestriction_obj_moduleCat`: the two steps of the chain
  which carry the identity as their structure map, read off at an object.
* `AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_obj_moduleCat` and
  `AlgebraicGeometry.Space.chartSectionsLinearEquiv_smul`: the sections of the chart restriction
  over a Zariski open `W` are the sections of `M` over the étale chart which `W` cuts out, with
  scalars restricted along `AlgebraicGeometry.Space.chartSectionsRingHom`.

## Implementation notes

Writing a semilinearity statement as

```
(r • x : Γ((restrictModule B T hT).obj N, V)) = ((structureMap B T hT).hom.app (op V)).hom r • x
```

fails with `failed to synthesize HSMul …`, since a type ascription on a term is ignored by
instance search. The statements below instead ascribe the operand, with `show … from`, as in
`CategoryTheory.ModuleCat.restrictScalars.smul_def'`.

At the chart, collapsing the four restrictions of scalars in one `rfl` exhausts the heartbeat
budget inside `whnf`, and so does stating the chart-level semilinearity with a `show … from` across
the whole chain. The collapse is done in two steps, by
`Stacks.SheafOfModules.pushforward_pushforward_obj_val_obj` and
`AlgebraicGeometry.Space.chartSmallEtaleRestriction_obj_moduleCat`, and the semilinearity is
stated through `AlgebraicGeometry.Space.chartSectionsLinearEquiv`.

The chart is spelled `AlgebraicGeometry.Space.openChartOfComparison`, not
`AlgebraicGeometry.Space.openChart`: the two are equal, by
`AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj`, but not by `rfl`, and at the
module level rewriting along that equality would also move the codomain of the scalar map.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.SheafOfModules

universe w m v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : CategoryTheory.Sheaf J RingCat.{w}} {R : CategoryTheory.Sheaf K RingCat.{w}}
  [F.IsContinuous J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
  (N : _root_.SheafOfModules.{m} R) (A : C)

/-- The sections over `A` of the direct image of `N` along a continuous functor `F` and a
morphism of sheaves of rings `φ` are, as a module, the sections of `N` over `F.obj A` with scalars
restricted along the component of `φ` at `A`. -/
theorem pushforward_obj_val_obj :
    ((_root_.SheafOfModules.pushforward.{m} φ).obj N).val.obj (op A) =
      (ModuleCat.restrictScalars (φ.hom.app (op A)).hom).obj (N.val.obj (op (F.obj A))) := rfl

/-- A scalar of the sections of `S` over `A` acts on a section of `N` over `F.obj A`, read as a
section of the direct image over `A`, through the component of `φ` at `A`. -/
theorem smul_pushforward_obj_val_obj (r : S.obj.obj (op A)) (x : N.val.obj (op (F.obj A))) :
    r • (show ((_root_.SheafOfModules.pushforward.{m} φ).obj N).val.obj (op A) from x) =
      (show R.obj.obj (op (F.obj A)) from (φ.hom.app (op A)).hom r) • x := rfl

section TwoLayers

universe v₃ u₃

variable {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E} {G : D ⥤ E}
  [G.IsContinuous K L] {Q : CategoryTheory.Sheaf L RingCat.{w}}
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{w} K L).obj Q)

/-- The sections over `A` of the direct image along `F` of the direct image along `G` of `N` are
the sections of `N` over `G.obj (F.obj A)` with scalars restricted along the composite of the two
structure maps. -/
theorem pushforward_pushforward_obj_val_obj (N : _root_.SheafOfModules.{m} Q) (A : C) :
    ((_root_.SheafOfModules.pushforward.{m} φ).obj
        ((_root_.SheafOfModules.pushforward.{m} ψ).obj N)).val.obj (op A) =
      (ModuleCat.restrictScalars
          ((ψ.hom.app (op (F.obj A))).hom.comp (φ.hom.app (op A)).hom)).obj
        (N.val.obj (op (G.obj (F.obj A)))) := rfl

-- Implementation note: stated for a bare pair of morphisms of sheaves of rings, since checking
-- the same equality after the functors are spelled out exhausts the heartbeat budget in `whnf`.
/-- Two pushforwards of sheaves of modules are the pushforward along the composite functor, with
the composite of the two structure maps. -/
theorem pushforward_pushforward_obj (N : _root_.SheafOfModules.{m} Q) :
    haveI : (F ⋙ G).IsContinuous J L := Functor.isContinuous_comp _ _ _ K _
    (_root_.SheafOfModules.pushforward.{m} φ).obj
        ((_root_.SheafOfModules.pushforward.{m} ψ).obj N) =
      (_root_.SheafOfModules.pushforward.{m} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map ψ)).obj N := rfl

/-- A scalar of the sections of `S` over `A` acts on a section of `N` over `G.obj (F.obj A)`,
read as a section of the two-fold direct image over `A`, through the composite of the components
of `φ` and `ψ`. -/
theorem smul_pushforward_pushforward_obj_val_obj (N : _root_.SheafOfModules.{m} Q) (A : C)
    (r : S.obj.obj (op A)) (x : N.val.obj (op (G.obj (F.obj A)))) :
    r • (show ((_root_.SheafOfModules.pushforward.{m} φ).obj
        ((_root_.SheafOfModules.pushforward.{m} ψ).obj N)).val.obj (op A) from x) =
      (show Q.obj.obj (op (G.obj (F.obj A))) from
        (ψ.hom.app (op (F.obj A))).hom ((φ.hom.app (op A)).hom r)) • x := rfl

end TwoLayers

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)
    (N : SheafOfModules.{u} (structureSheaf B T hT)) (V : T.Opens)

/-- The sections over an open `V` of `T` of the restriction of `N` along the inclusion of the
small Zariski site are, as a module, the sections of `N` over `V` read as an object of the small
étale site, with scalars restricted along the comparison of structure sheaves. -/
theorem restrictModule_obj_val_obj_moduleCat :
    ((restrictModule B T hT).obj N).val.obj (op V) =
      (ModuleCat.restrictScalars ((structureMap B T hT).hom.app (op V)).hom).obj
        (N.val.obj (op (opensObj B T hT V))) := rfl

/-- A function on the open `V` acts on a section of `N` over `V`, read as an object of the small
étale site, through the component at `V` of `AlgebraicGeometry.SmallEtale.structureMap`, which is
the inverse of `AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem smul_restrictModule_obj_val_obj (r : T.ringCatSheaf.obj.obj (op V))
    (x : N.val.obj (op (opensObj B T hT V))) :
    r • (show ((restrictModule B T hT).obj N).val.obj (op V) from x) =
      (show (structureSheaf B T hT).obj.obj (op (opensObj B T hT V)) from
        ((structureMap B T hT).hom.app (op V)).hom r) • x := rfl

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))

/-! ### The composite scalar map of the chart -/

/-- The ring map along which the sections of the chart restriction are semilinear: over a
Zariski open `W` of the chart's scheme, the comparison of structure sheaves of the small étale
site of that scheme, `AlgebraicGeometry.SmallEtale.structureMap`, followed by the structure map of
the inverse of the comparison of the two small étale sites,
`Stacks.SheafOfModules.reindexBackSharp`. -/
noncomputable def chartSectionsRingHom (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens) :
    (chartScheme A).ringCatSheaf.obj.obj (op W) →+*
      (structureRingSheaf B S hS X).obj.obj (op (openChartOfComparison B S hS X A W)) :=
  RingHom.comp
    ((Stacks.SheafOfModules.reindexBackSharp
        (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
        (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
        (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).hom.app
      (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property W))).hom
    ((_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS X A).left.property).hom.app (op W)).hom

/-- The composite scalar map `chartSectionsRingHom` of the chart is surjective. -/
theorem surjective_chartSectionsRingHom (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens) :
    Function.Surjective (chartSectionsRingHom B S hS X A W) := by
  have h := Function.Surjective.comp
    (Stacks.SheafOfModules.surjective_reindexBackSharp_app
      (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
      (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property W))
    (_root_.AlgebraicGeometry.SmallEtale.surjective_structureMap_hom_app
      (associatedBigEtaleSite B) (chartScheme A)
      (chartFppfObject B S hS X A).left.property W)
  exact h

/-! ### The module-level chart sections identification -/

/-- The restriction of `M` to the small étale site of the chart's scheme is the direct image,
along the inverse of the comparison of the two small étale sites, of the restriction of `M` to
the small étale site of the chart. -/
theorem chartSchemeEtaleModule_eq_pushforward (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    chartSchemeEtaleModule B S hS X M hM A =
      (SheafOfModules.pushforward.{u} (Stacks.SheafOfModules.reindexBackSharp
          (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
          (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
          (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))).obj
        (chartSmallEtaleRestriction B S hS X M A) := rfl

/-- The sections of the restriction of `M` to the small étale site of a chart, over an object of
that site, are, as a module, the sections of `M` over the étale chart of `X` it becomes. -/
theorem chartSmallEtaleRestriction_obj_moduleCat (A : SmallEtale B S hS X.1)
    (P : SmallEtale B S hS (chartSpace B S hS X A).1) :
    (chartSmallEtaleRestriction B S hS X M A).val.obj (op P) =
      M.val.obj (op ((SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor.obj P).left) :=
  rfl

/-- The sections of the chart restriction of `M` over a Zariski open `W` of the chart's scheme
are, as a module, the sections of `M` over the étale chart which `W` cuts out, with scalars
restricted along `AlgebraicGeometry.Space.chartSectionsRingHom`. -/
theorem restrictModule_chartSchemeEtaleModule_obj_moduleCat
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op W) =
      (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A W)).obj
        (M.val.obj (op (openChartOfComparison B S hS X A W))) :=
  ((congrArg (fun Z => ((_root_.AlgebraicGeometry.SmallEtale.restrictModule
            (associatedBigEtaleSite B) (chartScheme A)
            (chartFppfObject B S hS X A).left.property).obj Z).val.obj (op W))
        (chartSchemeEtaleModule_eq_pushforward B S hS X M hM A)).trans
      (Stacks.SheafOfModules.pushforward_pushforward_obj_val_obj
        (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property)
        (Stacks.SheafOfModules.reindexBackSharp
          (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
          (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
          (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))
        (chartSmallEtaleRestriction B S hS X M A) W)).trans
    (congrArg (fun Z => (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A W)).obj Z)
      (chartSmallEtaleRestriction_obj_moduleCat B S hS X M A _))

/-- Over a Zariski open `W` of the chart's scheme, the sections of the chart restriction of `M`
are linearly isomorphic, over the functions on `W`, to the sections of `M` over the étale chart
which `W` cuts out with scalars restricted along `AlgebraicGeometry.Space.chartSectionsRingHom`. -/
noncomputable def chartSectionsLinearEquiv (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op W)
      ≃ₗ[(chartScheme A).ringCatSheaf.obj.obj (op W)]
        (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A W)).obj
          (M.val.obj (op (openChartOfComparison B S hS X A W))) :=
  (eqToIso (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A W)).toLinearEquiv

/-- A function on a Zariski open `W` of the chart's scheme acts on a section of the chart
restriction over `W` as `AlgebraicGeometry.Space.chartSectionsRingHom` of it acts on the
corresponding section of `M` over the étale chart which `W` cuts out. -/
theorem chartSectionsLinearEquiv_smul (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens)
    (r : (chartScheme A).ringCatSheaf.obj.obj (op W))
    (x : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op W)) :
    chartSectionsLinearEquiv B S hS X M hM A W (r • x) =
      chartSectionsRingHom B S hS X A W r •
        (show M.val.obj (op (openChartOfComparison B S hS X A W)) from
          chartSectionsLinearEquiv B S hS X M hM A W x) :=
  (map_smul (chartSectionsLinearEquiv B S hS X M hM A W) r x).trans
    (ModuleCat.restrictScalars.smul_def' (chartSectionsRingHom B S hS X A W) r _)

end AlgebraicGeometry.Space

end
