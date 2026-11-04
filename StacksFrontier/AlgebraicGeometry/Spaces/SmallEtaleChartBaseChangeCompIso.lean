module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartProjectionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartProjection

/-!
# Base change of étale scheme charts along a composite

Let `h : D ⟶ A` and `g : A ⟶ C` be representable morphisms of algebraic spaces over a scheme `S`
contained in a big fppf site `B`.  Base change of étale scheme charts of Stacks 03G2, part (4),
is the functor `AlgebraicGeometry.Space.smallBaseChange`; this file proves that it respects
composition, as a natural isomorphism
`(- ×_C D) ≅ (- ×_C A) ×_A D` of functors `SmallEtale C ⥤ SmallEtale D`.

The comparison at a single chart is already available:
`AlgebraicGeometry.Space.chartBaseChangeCompComparison`, the unique morphism of indices out of
the iterated base-changed chart, read on underlying charts.  What is added here is that it is an
isomorphism — both indices are initial — and that it is natural in the chart.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeMiddle` is the middle projection
  `V ×_C D ⟶ V ×_C A` of the two base changes, as a morphism of the big fppf category.
* `AlgebraicGeometry.Space.smallBaseChangeChartCompIso` is **the composition comparison of base
  change of étale scheme charts**.

## Main results

* `AlgebraicGeometry.Space.chartBaseChangeCompComparison_comp_snd`: the comparison of charts
  followed by the cartesian projection of `h` is the middle projection.  This is what pins the
  comparison down: a morphism into `(V ×_C A) ×_A D` is determined by its two projections, and
  the one to `D` is forced by its being a morphism of charts of `D`.
* `AlgebraicGeometry.Space.chartBaseChangeCompComparison_naturality`: the comparison of charts
  is natural in the chart.
* `AlgebraicGeometry.Space.smallBaseChangeChartCompIso_hom_app`: the components of the
  composition comparison are the comparisons of charts.

## Implementation notes

Nothing here invokes a universal property of a fibre product to *construct* a morphism of
charts; the comparison is the one initiality already supplies, and the two lemmas
`AlgebraicGeometry.Space.toOver_map_chartBaseChangeCompComparison_comp_snd` and
`CategoryTheory.CostructuredArrow.w` are its two projections.  The middle projection, by
contrast, is constructed, by `CategoryTheory.Functor.relativelyRepresentable.lift`: it is the
only morphism in sight that is not already named.

Every equality of morphisms of charts below is reduced to an equality of morphisms of the big
fppf category by `CategoryTheory.CostructuredArrow.hom_ext`, and then to the two projections by
`CategoryTheory.Functor.relativelyRepresentable.hom_ext`.  The projection to `D` is in both
cases the commuting triangle of the charts, so only the projection to the chart of `C` carries
content.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comp

variable {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom)

/-- The compatibility making the middle projection well defined: the cartesian projection of
`V ×_C D` to `D`, followed by `h`, lies over the cartesian projection to `V`. -/
theorem chartBaseChangeMiddle_cond (V : SmallEtale B S hS C.1) :
    (hrephg.fst V.1.hom ≫ h.hom) ≫ g.hom =
      yoneda.map (hrephg.snd V.1.hom) ≫ V.1.hom := by
  rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom]
  exact hrephg.w V.1.hom

/-- **The middle projection** `V ×_C D ⟶ V ×_C A`: the morphism of the big fppf category over
the chart `V` whose composite with the cartesian projection of `V ×_C A` to `A` is the cartesian
projection of `V ×_C D` to `D` followed by `h`. -/
def chartBaseChangeMiddle (V : SmallEtale B S hS C.1) :
    (SmallEtale.toOver B S hS D.1).obj ((smallBaseChange B S hS (h ≫ g) hrephg).obj V) ⟶
      (SmallEtale.toOver B S hS A.1).obj ((smallBaseChange B S hS g hrepg).obj V) :=
  hrepg.lift (hrephg.fst V.1.hom ≫ h.hom) (hrephg.snd V.1.hom)
    (chartBaseChangeMiddle_cond B S hS h g hrephg V)

/-- The middle projection followed by the cartesian projection of `V ×_C A` to `A` is the
cartesian projection of `V ×_C D` to `D` followed by `h`. -/
@[reassoc (attr := simp)]
theorem chartBaseChangeMiddle_fst (V : SmallEtale B S hS C.1) :
    yoneda.map (chartBaseChangeMiddle B S hS h g hrepg hrephg V) ≫ hrepg.fst V.1.hom =
      hrephg.fst V.1.hom ≫ h.hom :=
  hrepg.lift_fst _ _ _

/-- The middle projection followed by the cartesian projection of `V ×_C A` to `V` is the
cartesian projection of `V ×_C D` to `V`. -/
@[reassoc (attr := simp)]
theorem chartBaseChangeMiddle_snd (V : SmallEtale B S hS C.1) :
    chartBaseChangeMiddle B S hS h g hrepg hrephg V ≫ hrepg.snd V.1.hom =
      hrephg.snd V.1.hom :=
  hrepg.lift_snd _ _ _

/-- **The comparison of charts followed by the cartesian projection of `h` is the middle
projection.**  Both are morphisms into the base-changed chart `V ×_C A` of `A`, so they agree as
soon as their two projections do: the one to `V` is
`AlgebraicGeometry.Space.toOver_map_chartBaseChangeCompComparison_comp_snd`, and the one to `A`
is the commuting triangle of the charts of `D` followed by the cartesian square of `h`. -/
theorem chartBaseChangeCompComparison_comp_snd (V : SmallEtale B S hS C.1) :
    (SmallEtale.toOver B S hS D.1).map
          (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫
        hreph.snd ((smallBaseChange B S hS g hrepg).obj V).1.hom =
      chartBaseChangeMiddle B S hS h g hrepg hrephg V := by
  have hw : yoneda.map ((SmallEtale.toOver B S hS D.1).map
          (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V)) ≫
        hreph.fst ((smallBaseChange B S hS g hrepg).obj V).1.hom =
      hrephg.fst V.1.hom :=
    CostructuredArrow.w
      (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).hom
  have hcart : yoneda.map (hreph.snd ((smallBaseChange B S hS g hrepg).obj V).1.hom) ≫
        hrepg.fst V.1.hom =
      hreph.fst ((smallBaseChange B S hS g hrepg).obj V).1.hom ≫ h.hom :=
    (hreph.w ((smallBaseChange B S hS g hrepg).obj V).1.hom).symm
  refine hrepg.hom_ext ?_ ?_
  · erw [yoneda.map_comp_assoc, hcart, ← Category.assoc, hw, chartBaseChangeMiddle_fst]
    rfl
  · erw [Category.assoc, toOver_map_chartBaseChangeCompComparison_comp_snd,
      chartBaseChangeMiddle_snd]

/-- The middle projection is natural in the chart: both sides are morphisms into the
base-changed chart of `A` with the same two projections. -/
theorem chartBaseChangeMiddle_naturality {V₁ V₂ : SmallEtale B S hS C.1} (k : V₁ ⟶ V₂) :
    (SmallEtale.toOver B S hS D.1).map ((smallBaseChange B S hS (h ≫ g) hrephg).map k) ≫
        chartBaseChangeMiddle B S hS h g hrepg hrephg V₂ =
      chartBaseChangeMiddle B S hS h g hrepg hrephg V₁ ≫
        (SmallEtale.toOver B S hS A.1).map ((smallBaseChange B S hS g hrepg).map k) := by
  have hwhg : yoneda.map ((SmallEtale.toOver B S hS D.1).map
          ((smallBaseChange B S hS (h ≫ g) hrephg).map k)) ≫ hrephg.fst V₂.1.hom =
      hrephg.fst V₁.1.hom :=
    CostructuredArrow.w ((smallBaseChange B S hS (h ≫ g) hrephg).map k).hom
  have hwg : yoneda.map ((SmallEtale.toOver B S hS A.1).map
          ((smallBaseChange B S hS g hrepg).map k)) ≫ hrepg.fst V₂.1.hom =
      hrepg.fst V₁.1.hom :=
    CostructuredArrow.w ((smallBaseChange B S hS g hrepg).map k).hom
  refine hrepg.hom_ext ?_ ?_
  · erw [yoneda.map_comp_assoc, chartBaseChangeMiddle_fst B S hS h g hrepg hrephg V₂,
      ← Category.assoc, hwhg, yoneda.map_comp_assoc, hwg,
      chartBaseChangeMiddle_fst B S hS h g hrepg hrephg V₁]
    rfl
  · erw [Category.assoc, chartBaseChangeMiddle_snd B S hS h g hrepg hrephg V₂,
      smallBaseChange_map_snd B S hS (h ≫ g) hrephg k, Category.assoc,
      smallBaseChange_map_snd B S hS g hrepg k, ← Category.assoc,
      chartBaseChangeMiddle_snd B S hS h g hrepg hrephg V₁]
    rfl

/-- **The comparison of charts is natural in the chart.**  Both sides are morphisms of charts of
`D` into the iterated base-changed chart, so they agree as soon as their projections to the
chart of `A` do, and those are the two sides of
`AlgebraicGeometry.Space.chartBaseChangeMiddle_naturality`. -/
theorem chartBaseChangeCompComparison_naturality {V₁ V₂ : SmallEtale B S hS C.1} (k : V₁ ⟶ V₂) :
    (smallBaseChange B S hS (h ≫ g) hrephg).map k ≫
        chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V₂ =
      chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V₁ ≫
        (smallBaseChange B S hS g hrepg ⋙ smallBaseChange B S hS h hreph).map k := by
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hreph.hom_ext ?_ ?_))
  · exact (CostructuredArrow.w
      ((smallBaseChange B S hS (h ≫ g) hrephg).map k ≫
        chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V₂).hom).trans
      (CostructuredArrow.w
        (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V₁ ≫
          (smallBaseChange B S hS g hrepg ⋙
            smallBaseChange B S hS h hreph).map k).hom).symm
  · erw [Category.assoc, chartBaseChangeCompComparison_comp_snd B S hS h g hreph hrepg hrephg V₂,
      chartBaseChangeMiddle_naturality B S hS h g hrepg hrephg k,
      ← chartBaseChangeCompComparison_comp_snd B S hS h g hreph hrepg hrephg V₁,
      Category.assoc, ← smallBaseChange_map_snd B S hS h hreph
        ((smallBaseChange B S hS g hrepg).map k), Category.assoc]
    rfl

/-- **The comparison of charts is an isomorphism.**  It is the unique morphism of indices
between two initial indices of the same Kan-extension limit, so the unique morphism back is a
two-sided inverse. -/
instance isIso_chartBaseChangeCompComparison (V : SmallEtale B S hS C.1) :
    IsIso (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) := by
  refine ⟨((smallBaseChangeIndex_isInitial B S hS (h ≫ g) hrephg V).to
    (compChartIndex B S hS h g hreph hrepg V)).right.unop, ?_, ?_⟩
  · exact congrArg (fun m => (StructuredArrow.Hom.right m).unop)
      ((smallBaseChangeIndex_isInitial B S hS (h ≫ g) hrephg V).hom_ext
        ((smallBaseChangeIndex_isInitial B S hS (h ≫ g) hrephg V).to
            (compChartIndex B S hS h g hreph hrepg V) ≫
          (isInitial_compChartIndex B S hS h g hreph hrepg V).to
            (smallBaseChangeIndex B S hS (h ≫ g) hrephg V))
        (𝟙 _))
  · exact congrArg (fun m => (StructuredArrow.Hom.right m).unop)
      ((isInitial_compChartIndex B S hS h g hreph hrepg V).hom_ext
        ((isInitial_compChartIndex B S hS h g hreph hrepg V).to
            (smallBaseChangeIndex B S hS (h ≫ g) hrephg V) ≫
          (smallBaseChangeIndex_isInitial B S hS (h ≫ g) hrephg V).to
            (compChartIndex B S hS h g hreph hrepg V))
        (𝟙 _))

/-- **Base change of étale scheme charts respects composition.**  For representable `h : D ⟶ A`
and `g : A ⟶ C`, base change of charts along `h ≫ g` is base change along `g` followed by base
change along `h`: at a chart `V` of `C` the comparison is the canonical isomorphism of
`V ×_C D` with `(V ×_C A) ×_A D`. -/
def smallBaseChangeChartCompIso :
    smallBaseChange B S hS (h ≫ g) hrephg ≅
      smallBaseChange B S hS g hrepg ⋙ smallBaseChange B S hS h hreph :=
  NatIso.ofComponents
    (fun V => asIso (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V))
    (fun k => chartBaseChangeCompComparison_naturality B S hS h g hreph hrepg hrephg k)

/-- The composition comparison at a chart `V` is the comparison of charts at `V`. -/
@[simp]
theorem smallBaseChangeChartCompIso_hom_app (V : SmallEtale B S hS C.1) :
    (smallBaseChangeChartCompIso B S hS h g hreph hrepg hrephg).hom.app V =
      chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V :=
  rfl

/-- Base change of charts along `g` followed by base change along `h` is a continuous functor of
small étale sites. -/
instance isContinuous_smallBaseChange_comp :
    (smallBaseChange B S hS g hrepg ⋙ smallBaseChange B S hS h hreph).IsContinuous
      (SmallEtale.topology B S hS C.1) (SmallEtale.topology B S hS D.1) :=
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS A.1) _

/-- Pulling a regular function back along two morphisms of schemes in turn is pulling it back
along the composite, read at the sheaf of not necessarily commutative rings. -/
theorem forget_two_gamma_map_comp_apply {P Q R : Scheme.{u}} (f₁ : P ⟶ Q) (f₂ : Q ⟶ R)
    (t : (forget₂ CommRingCat.{u} RingCat.{u}).obj (Scheme.Γ.obj (op R))) :
    (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map f₁.op)
        ((forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map f₂.op) t) =
      (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map (f₁ ≫ f₂).op) t := by
  rw [op_comp, Scheme.Γ.map_comp, Functor.map_comp]
  rfl

/-- **The triangle of cartesian projections, on underlying schemes.**  The comparison of the
base-changed chart of the composite with the iterated base-changed chart, followed by the two
cartesian projections, is the cartesian projection of the composite. -/
theorem toScheme_map_chartBaseChangeCompComparison_comp_snd (V : SmallEtale B S hS C.1) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS D.1).map
          (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V)) ≫
        (BigFppfOver.toScheme B S hS).map
          (hreph.snd ((smallBaseChange B S hS g hrepg).obj V).1.hom) ≫
        (BigFppfOver.toScheme B S hS).map (hrepg.snd V.1.hom) =
      (BigFppfOver.toScheme B S hS).map (hrephg.snd V.1.hom) := by
  refine Eq.trans (congrArg (fun q => (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS D.1).map
        (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V)) ≫ q)
    ((BigFppfOver.toScheme B S hS).map_comp _ _).symm) ?_
  refine Eq.trans ((BigFppfOver.toScheme B S hS).map_comp _ _).symm ?_
  exact congrArg (BigFppfOver.toScheme B S hS).map
    (toOver_map_chartBaseChangeCompComparison_comp_snd B S hS h g hreph hrepg hrephg V)

/-- **The structure maps of base change of étale scheme charts compose.**  Pulling a regular
function on an étale chart `V` of `C` back along the cartesian projection `V ×_C A ⟶ V` and then
along `(V ×_C A) ×_A D ⟶ V ×_C A` is pulling it back along `V ×_C D ⟶ V`, read through the
comparison `AlgebraicGeometry.Space.smallBaseChangeChartCompIso` of the two base changes.

This is the analogue, for the chart base change of a representable morphism of algebraic spaces,
of `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_comparisonComp`. -/
theorem smallBaseChangeSharp_comparisonComp :
    SheafOfModules.comparisonComp (smallBaseChangeSharp B S hS g hrepg)
          (smallBaseChangeSharp B S hS h hreph) ≫
        (Functor.sheafPushforwardContinuousNatTrans
            (smallBaseChangeChartCompIso B S hS h g hreph hrepg hrephg).hom RingCat.{u}
            (SmallEtale.topology B S hS C.1) (SmallEtale.topology B S hS D.1)).app
          (smallEtaleRingSheaf B S hS D.1 D.2) =
      smallBaseChangeSharp B S hS (h ≫ g) hrephg := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  refine ConcreteCategory.hom_ext _ _ fun r => ?_
  refine Eq.trans (forget_two_gamma_map_comp_apply
    ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS D.1).map
      (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V.unop)))
    ((BigFppfOver.toScheme B S hS).map
      (hreph.snd ((smallBaseChange B S hS g hrepg).obj V.unop).1.hom)) _) ?_
  refine Eq.trans (forget_two_gamma_map_comp_apply _
    ((BigFppfOver.toScheme B S hS).map (hrepg.snd V.unop.1.hom)) r) ?_
  refine congrArg (fun q => (forget₂ CommRingCat.{u} RingCat.{u}).map
    (Scheme.Γ.map (Quiver.Hom.op q)) r) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact toScheme_map_chartBaseChangeCompComparison_comp_snd B S hS h g hreph hrepg hrephg V.unop

end Comp

end AlgebraicGeometry.Space

end
