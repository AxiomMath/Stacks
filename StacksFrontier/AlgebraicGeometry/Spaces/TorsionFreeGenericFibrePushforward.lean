module

public import StacksFrontier.AlgebraicGeometry.Spaces.TorsionFreeOverSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondence

/-!
# The direct image along the generic fibre is torsion free

Let `R` be a valuation ring with fraction field `K`, `T = Spec R`, and `j : X_K ⟶ X` the inclusion
of the generic fibre of an algebraic space `X` over `T`.  The proof of Stacks 0DM0 takes finite
type quasi-coherent submodules `G ⊂ j_*F_K` of the direct image of a quasi-coherent
`𝒪_{X_K}`-module and uses that they are torsion free over `R`, hence flat (Stacks 0539).  This
file proves that.

The point is that the nonzero elements of `R` act invertibly on `j_*F_K`.  The sections of
`j_*F_K` over an étale scheme chart `V` of `X` are the compatible families of sections of `F_K`
over the étale scheme charts `U'` of `X_K` lying over `X_K ×_X V`, and a function `t` on `T` acts
on such a family through its pullbacks to the `U'`, which are units as soon as `t ≠ 0`: the
morphism `U' ⟶ T` factors through `Spec K`.  So a nonzero `t` acts injectively on the sections
of `j_*F_K`, and by `AlgebraicGeometry.Space.isTorsionFreeOver_of_injective_smul_of_valuationRing`
the quasi-coherent module `j_*F_K` is torsion free over `T`.  Torsion freeness passes to
submodules (`AlgebraicGeometry.Space.IsTorsionFreeOver.of_mono`).

The statements are made for an arbitrary morphism `j : X' ⟶ X` of algebraic spaces over
`X ⟶ h_W` such that the nonzero global functions on `W` pull back to units on every étale
scheme chart of `X'`; the generic fibre is the case of interest.

## Main results

* `AlgebraicGeometry.Space.moduleChartProjection_app_smul`: a chart projection of a direct image
  is semilinear over the pullback of functions.
* `AlgebraicGeometry.Space.injective_smul_modulePushforward`: a function acting injectively on
  the sections of `F'` over every chart above `X' ×_X V`, through its pullbacks, acts injectively
  on the sections of `j_*F'` over `V`.
* `AlgebraicGeometry.Space.isTorsionFreeOver_modulePushforward_of_valuationRing`: over the
  spectrum of a valuation ring, a quasi-coherent direct image `j_*F'` along a morphism on whose
  charts the nonzero functions of the base become units is torsion free over the base.
* `AlgebraicGeometry.Space.isTorsionFreeOver_subobject_modulePushforward_of_valuationRing`:
  so is every subobject of it.

## References

* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A chart projection of the direct image is semilinear over the pullback of functions.**
For an étale scheme chart `V` of `Y` and an étale scheme chart of `X` above `X ×_Y V`, the
projection of the sections of `f_*F` over `V` to the sections of `F` over that chart carries the
action of a function `r` on `V` to the action of its pullback. -/
theorem moduleChartProjection_app_smul {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1)
    (idx : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op V))
    (x : ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    (show F.val.obj idx.right from
        (moduleChartProjection B S hS f V idx).app (moduleSetSheaf B S hS X F) (r • x)) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj idx.right from
        chartPullback B S hS f V idx r) •
        (show F.val.obj idx.right from
          (moduleChartProjection B S hS f V idx).app (moduleSetSheaf B S hS X F) x) := by
  have hP : PreservesFiniteProducts (smallEtaleDirectImage B S hS f ⋙
      sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)) := inferInstance
  have hQ : PreservesFiniteProducts (sectionsFunctor.{u} (SmallEtale.topology B S hS X.1)
      idx.right) := inferInstance
  have hR : (SmallEtale.topology B S hS X.1).HasSheafCompose
      (forget RingCat.{u}) := inferInstance
  have hA : (SmallEtale.topology B S hS X.1).HasSheafCompose
      (forget AddCommGrpCat.{u}) := inferInstance
  refine Eq.trans (@moduleSMulObj_naturality _ _ _ hR hA
    (structureRingSheaf B S hS X) F _ hP _ hQ
    (moduleChartProjection B S hS f V idx)
    (show ((smallEtaleDirectImage B S hS f ⋙
        sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)).obj
      (structureSetSheaf B S hS X)) from
      ((structureSharp B S hS f).hom.app (op V)).hom r) x) ?_
  rw [moduleChartProjection_app_structureSharp]
  exact sectionsFunctor_map_moduleSMulHom
    (structureRingSheaf B S hS X) F idx.right
    (chartPullback B S hS f V idx r)
    ((moduleChartProjection B S hS f V idx).app (moduleSetSheaf B S hS X F) x)

/-- **Injectivity of the action on a direct image, chart by chart.**  A function `r` on an
étale scheme chart `V` of `Y` acts injectively on the sections of `f_*F` over `V` as soon as its
pullback to every étale scheme chart of `X` above `X ×_Y V` acts injectively on the sections of
`F` over that chart: the sections of `f_*F` over `V` are determined by their chart projections,
which are semilinear. -/
theorem injective_smul_modulePushforward {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op V))
    (h : ∀ idx : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op,
      Function.Injective fun m : F.val.obj idx.right =>
        (show (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj idx.right from
          chartPullback B S hS f V idx r) • m) :
    Function.Injective fun x : ((modulePushforward B S hS f).obj F).val.obj (op V) => r • x := by
  intro x y hxy
  refine moduleChartProjection_ext B S hS f V (moduleSetSheaf B S hS X F) (fun idx => h idx ?_)
  have hx := moduleChartProjection_app_smul f F V idx r x
  have hy := moduleChartProjection_app_smul f F V idx r y
  refine hx.symm.trans (Eq.trans ?_ hy)
  exact congrArg (fun z => (show F.val.obj idx.right from
    (moduleChartProjection B S hS f V idx).app (moduleSetSheaf B S hS X F) z)) hxy

/-- The pullback of a function on `W` along `β : V ⟶ W` to an étale scheme chart of `X'` above
`X' ×_X V` is the pullback along the composite with the chart morphism. -/
theorem chartPullback_appTop {X' X : AlgebraicSpaces B S hS} (j : X' ⟶ X)
    (V : SmallEtale B S hS X.1) {W : BigFppfOver B S hS}
    (β : (SmallEtale.toOver B S hS X.1).obj V ⟶ W)
    (idx : StructuredArrow (op (chartBaseChange B S hS j V)) (comparisonFunctor B S hS X').op)
    (t : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    chartPullback B S hS j V idx (((BigFppfOver.toScheme B S hS).map β).appTop t) =
      ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS j V idx ≫ β)).appTop t := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rfl

/-- The composite of the structure morphism of an étale scheme chart of `X'` above `X' ×_X V`
with `X' ⟶ X ⟶ h_W` is induced by the chart morphism followed by `β : V ⟶ W`. -/
theorem chartBaseChangeMap_comp_comm {X' X : AlgebraicSpaces B S hS} (j : X' ⟶ X)
    {W : BigFppfOver B S hS} (g : X ⟶ schemeSpace W) (V : SmallEtale B S hS X.1)
    (β : (SmallEtale.toOver B S hS X.1).obj V ⟶ W) (hβ : V.1.hom ≫ g.hom = yoneda.map β)
    (idx : StructuredArrow (op (chartBaseChange B S hS j V)) (comparisonFunctor B S hS X').op) :
    idx.right.unop.1.hom ≫ (j ≫ g).hom =
      yoneda.map (chartBaseChangeMap B S hS j V idx ≫ β) := by
  have hc := chartBaseChangeMap_comm B S hS j idx.right.unop V idx.hom.unop
  change idx.right.unop.1.hom ≫ j.hom ≫ g.hom = _
  rw [← Category.assoc, hc, Category.assoc, hβ, Functor.map_comp]
  rfl

/-- **The nonzero functions of the base act injectively on a direct image.**  Let
`g : X ⟶ h_W` and `j : X' ⟶ X` be morphisms of algebraic spaces such that the pullback of every
nonzero global function on `W` to every étale scheme chart of `X'` is a unit.  Then for every
`𝒪_{X'}`-module `F'`, every étale scheme chart `V` of `X` with induced morphism `β : V ⟶ W`, and
every nonzero global function `t` on `W`, the pullback `β^*t` acts injectively on the sections
of `j_*F'` over `V`. -/
theorem injective_appTop_smul_modulePushforward_of_isUnit {X' X : AlgebraicSpaces B S hS}
    (j : X' ⟶ X)
    {W : BigFppfOver B S hS} (g : X ⟶ schemeSpace W) (F' : Modules.{u, u} B S hS X'.1 X'.2)
    (hunit : ∀ (U' : SmallEtale B S hS X'.1) (γ : (SmallEtale.toOver B S hS X'.1).obj U' ⟶ W),
      U'.1.hom ≫ (j ≫ g).hom = yoneda.map γ → ∀ t : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤),
        t ≠ 0 → IsUnit (((BigFppfOver.toScheme B S hS).map γ).appTop t))
    (V : SmallEtale B S hS X.1) (β : (SmallEtale.toOver B S hS X.1).obj V ⟶ W)
    (hβ : V.1.hom ≫ g.hom = yoneda.map β) (t : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (ht : t ≠ 0) :
    Function.Injective fun m : ((modulePushforward B S hS j).obj F').val.obj (op V) =>
      (show (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op V) from
        ((BigFppfOver.toScheme B S hS).map β).appTop t) • m := by
  refine injective_smul_modulePushforward j F' V _ (fun idx => ?_)
  have hu := hunit idx.right.unop _ (chartBaseChangeMap_comp_comm j g V β hβ idx) t ht
  rw [← chartPullback_appTop] at hu
  have hu' : IsUnit (show (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj idx.right from
        chartPullback B S hS j V idx (((BigFppfOver.toScheme B S hS).map β).appTop t)) := hu
  exact hu'.isSMulRegular (F'.val.obj idx.right)

/-- **A direct image on whose charts the nonzero functions of a valuation ring become units is
torsion free.**  Let `R` be a valuation ring, `W` an object of the big fppf site whose scheme is
`Spec R`, `g : X ⟶ h_W` and `j : X' ⟶ X` morphisms of algebraic spaces such that the pullback of
every nonzero global function on `W` to every étale scheme chart of `X'` is a unit, and `F'` an
`𝒪_{X'}`-module whose direct image `j_*F'` is quasi-coherent.  Then `j_*F'` is torsion free over
`h_W`.

For the inclusion `j : X_K ⟶ X` of the generic fibre over `Spec R`, `K` the fraction field, the
hypothesis on `j` holds because every chart of `X_K` maps to `Spec K`; this is the torsion
freeness of `j_*F_K` used in the proof of Stacks 0DM0. -/
theorem isTorsionFreeOver_modulePushforward_of_valuationRing {R : Type u} [CommRing R]
    [IsDomain R] [ValuationRing R] {W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (CommRingCat.of R))
    {X' X : AlgebraicSpaces B S hS} (j : X' ⟶ X) (g : X ⟶ schemeSpace W)
    (F' : Modules.{u, u} B S hS X'.1 X'.2)
    (hqc : ((modulePushforward B S hS j).obj F').IsQuasicoherentOnSite)
    (hunit : ∀ (U' : SmallEtale B S hS X'.1) (γ : (SmallEtale.toOver B S hS X'.1).obj U' ⟶ W),
      U'.1.hom ≫ (j ≫ g).hom = yoneda.map γ → ∀ t : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤),
        t ≠ 0 → IsUnit (((BigFppfOver.toScheme B S hS).map γ).appTop t)) :
    IsTorsionFreeOver B S hS X.2 g.hom ((modulePushforward B S hS j).obj F') :=
  isTorsionFreeOver_of_injective_smul_of_valuationRing e g _ hqc
    (fun V β hβ t ht =>
      injective_appTop_smul_modulePushforward_of_isUnit j g F' hunit V β hβ t ht)

/-- **Every submodule of such a direct image is torsion free.**  Under the hypotheses of
`AlgebraicGeometry.Space.isTorsionFreeOver_modulePushforward_of_valuationRing`, every subobject
of `j_*F'` is torsion free over `h_W`. -/
theorem isTorsionFreeOver_subobject_modulePushforward_of_valuationRing {R : Type u}
    [CommRing R] [IsDomain R] [ValuationRing R] {W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (CommRingCat.of R))
    {X' X : AlgebraicSpaces B S hS} (j : X' ⟶ X) (g : X ⟶ schemeSpace W)
    (F' : Modules.{u, u} B S hS X'.1 X'.2)
    (hqc : ((modulePushforward B S hS j).obj F').IsQuasicoherentOnSite)
    (hunit : ∀ (U' : SmallEtale B S hS X'.1) (γ : (SmallEtale.toOver B S hS X'.1).obj U' ⟶ W),
      U'.1.hom ≫ (j ≫ g).hom = yoneda.map γ → ∀ t : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤),
        t ≠ 0 → IsUnit (((BigFppfOver.toScheme B S hS).map γ).appTop t))
    (G : Subobject ((modulePushforward B S hS j).obj F')) :
    IsTorsionFreeOver B S hS X.2 g.hom (G : Modules.{u, u} B S hS X.1 X.2) :=
  (isTorsionFreeOver_modulePushforward_of_valuationRing e j g F' hqc hunit).subobject G

end AlgebraicGeometry.Space

end
