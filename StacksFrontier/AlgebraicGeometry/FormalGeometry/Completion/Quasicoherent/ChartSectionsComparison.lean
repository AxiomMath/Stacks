module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ChartActionSquare
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.PushforwardAffineSectionsComparison

/-!
# The cohomology of a chart as sections of the higher direct image, semilinearly

Let `f : X ⟶ Y` be a proper morphism, `ℐ ⊆ 𝒪_Y` a quasi-coherent sheaf of ideals, `ℱ` a
quasi-coherent `𝒪_X`-module and `V` an affine open of `Y`. [Stacks, Tag 02O8] on the chart
`f⁻¹(V) ⟶ Spec Γ(Y, V)` is a statement about `⨁ₙ Hᵖ(f⁻¹(V), ℐⁿℱ)` as a module over the *ring*
Rees algebra `⨁ₙ ℐ(V)ⁿ`, while [Stacks, Tag 02O9] needs a statement about `Γ(V, 𝓜ₙ)` for
`𝓜 = Stacks.Blowup.pushforwardReesGradedModulePlus` as a module over the *sheaf* Rees algebra.
This file produces the comparison between the two and proves that it is semilinear for the two
actions.

## Main definitions

* `Stacks.Algebraization.chartRees`: the restriction of `ℐⁿℱ` to `f⁻¹(V)`, the module both the
  chart's graded module and the comparison below are read at.
* `Stacks.Algebraization.chartSections`: the comparison
  `Hᵖ(f⁻¹(V), (ℐⁿℱ)|_{f⁻¹V}) → Γ(V, R ᵖ f_*(ℐⁿℱ))`.

## Main results

* `Stacks.Algebraization.chartSections_surjective` and
  `Stacks.Algebraization.chartSections_add`: the comparison is onto and additive.
* `Stacks.Algebraization.chartSections_actHom`: **the semilinearity.** The comparison carries the
  action of a homogeneous element `b` of degree `k` of the ring Rees algebra to the action of the
  section of `ℐᵏ` over `V` attached to `b`.
* `Stacks.Algebraization.isIso_chartPieceRestrict`: the comparison of the pieces is an
  isomorphism, which is what makes the first factor of the composite invertible.

## Implementation notes

The comparison is three isomorphisms:

* `Hᵖ(−)` of `Stacks.Algebraization.chartPieceRestrict`, which identifies the degree-`n` piece of
  the chart's graded module with the restriction of `ℐⁿℱ` to `f⁻¹(V)`;
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.cohomologyExtendSectionsEquiv`, which
  identifies the cohomology of a quasi-coherent module on `f⁻¹(V)` with the sections over `V` of
  the higher direct image of its extension to `X`;
* the inverse of `Stacks.Blowup.unitDerived` over `V`, which removes the extension; it is
  invertible by `Stacks.Blowup.isIso_unitDerived_app`.

**Only additivity and semilinearity are proved**, not `Γ(Y, V)`-linearity, because that is all
the affine criterion `SheafOfModules.GradedModule.isFiniteType_of_affine_span` consumes: it asks
for a *spanning* family of products, and the scalars of a span are absorbed by
`SheafOfModules.GradedModule.smulSection_smul_right`. Proving linearity would require comparing
the `Γ(Y, V)`-action on the cohomology of the chart — which is the `Γ(f⁻¹V, ⊤)`-action restricted
along the chart's structure morphism — with the one on `Γ(V, 𝓜ₙ)`, at an argument built from
`CategoryTheory.Functor.rightDerived`; that is the comparison the implementation notes of the
sibling file `PushforwardAffineSectionsComparison` record as a kernel timeout.

The semilinearity is `cohomologyExtendSectionsEquiv_naturality` at
`ψ = Stacks.Blowup.mulRestrict`, together with the factored action square
`Stacks.Algebraization.actHom_comp_chartPieceRestrict` and the splitting of
`R ᵖ f_*(Stacks.Blowup.mulHom)` as the higher direct image of the unit followed by
`R ᵖ f_*` of the pushforward of `mulRestrict`, which is the same splitting
`Stacks.Blowup.smulSectionHom_comp` uses.

## References

* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02O9](https://stacks.math.columbia.edu/tag/02O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.FormalFunctions
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage
open Stacks.AlgebraicGeometry.SubmoduleRestrict
open SheafOfModules.GradedModule

universe u

namespace Stacks.Algebraization

/-- The factored comparison is an isomorphism: both of its factors are transports along
equalities of objects. Stated of variable submodules, for the reason recorded in the
implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ChartActionSquare`. -/
public theorem isIso_restrictToCompare {A : Type u} [CommRing A] (Z : Over (Spec (.of A)))
    {Zt : Scheme.{u}} (g : Z.left ⟶ Zt) [hg : IsOpenImmersion g]
    {G : Zt.Modules} (N : G.Submodule) {P : (Scheme.Modules.restrict G g).Submodule}
    (e : P = restrictTo g N) : IsIso (restrictToCompare Z g N e) := by
  subst e
  have hall : restrictToCompare Z g N (rfl : restrictTo g N = restrictTo g N) = 𝟙 _ := rfl
  rw [hall]
  exact IsIso.id _

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules)

/-- The comparison `Stacks.Algebraization.chartPieceRestrict` of the degree-`d` piece of the
chart's graded module with the restriction of `ℐᵈℱ` to `f⁻¹(V)` is an isomorphism: it is
`Stacks.Algebraization.restrictToCompare`, which `isIso_restrictToCompare` inverts. -/
public theorem isIso_chartPieceRestrict [F.IsQuasicoherent] (V : Y.affineOpens) (d : ℤ) :
    IsIso (chartPieceRestrict f I F V d) := by
  have : IsOpenImmersion (show (affineBaseChart f V).left ⟶ X from (f ⁻¹ᵁ V.1).ι) :=
    inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ V.1).ι)
  simp only [chartPieceRestrict]
  apply isIso_restrictToCompare

variable (p : ℕ)

/-- The restriction to `f⁻¹(V)` of `ℐⁿℱ`, which is both the target of
`Stacks.Algebraization.chartPieceRestrict` and the module the comparison of the sibling file
`PushforwardAffineSectionsComparison` is applied to. -/
public abbrev chartRees (V : Y.affineOpens) (n : ℤ) : (f ⁻¹ᵁ V.1).toScheme.Modules :=
  (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V.1).ι).obj (Stacks.Blowup.reesComapMod f I F n)

/-- The restriction of `ℐⁿℱ` to `f⁻¹(V)` is quasi-coherent when `ℱ` is. -/
public instance isQuasicoherent_chartRees [F.IsQuasicoherent] (V : Y.affineOpens) (n : ℤ) :
    (chartRees f I F V n).IsQuasicoherent :=
  haveI := Stacks.Blowup.reesComapMod_isQuasicoherent f I F n
  inferInstance

variable [QuasiCompact f] [QuasiSeparated f]

/-- **The comparison.** The degree-`n` cohomology of the chart's graded module in degree `p` is
the module of sections over `V` of the degree-`n` piece of
`Stacks.Blowup.pushforwardReesGradedModulePlus`. -/
public def chartSections [F.IsQuasicoherent] (V : Y.affineOpens) (n : ℤ)
    (z : (cohomologyFunctor (affineBaseChart f V) p).obj
      ((reesFiltrationModule (I.ideal V) (affineBaseChart f V)
        (affineBaseChartModule f F V)).piece n)) :
    Γ(((Scheme.Modules.pushforward f).rightDerived p).obj
      (Stacks.Blowup.reesComapMod f I F n), V.1) :=
  haveI : IsAffine V.1.toScheme := V.2
  inv ((Stacks.Blowup.unitDerived f I F p n V.1).app V.1)
    (cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n)
      (((cohomologyFunctor (affineBaseChart f V) p).map
        (chartPieceRestrict f I F V n)).hom z))

/-- The comparison is additive: each of its three factors is. -/
public theorem chartSections_add [F.IsQuasicoherent] (V : Y.affineOpens) (n : ℤ)
    (z z' : (cohomologyFunctor (affineBaseChart f V) p).obj
      ((reesFiltrationModule (I.ideal V) (affineBaseChart f V)
        (affineBaseChartModule f F V)).piece n)) :
    chartSections f I F p V n (z + z') =
      chartSections f I F p V n z + chartSections f I F p V n z' := by
  have : IsAffine V.1.toScheme := V.2
  simp only [chartSections]
  refine Eq.trans (congrArg
    (fun y : Γ(extendDerived f V.1 p (chartRees f I F V n), V.1) =>
      inv ((Stacks.Blowup.unitDerived f I F p n V.1).app V.1) y)
    (Eq.trans (congrArg (cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n))
        (map_add ((cohomologyFunctor (affineBaseChart f V) p).map
          (chartPieceRestrict f I F V n)).hom z z'))
      (map_add (cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n)) _ _))) ?_
  exact map_add _ _ _

/-- The comparison is onto: each of its three factors is invertible. -/
public theorem chartSections_surjective [F.IsQuasicoherent] (V : Y.affineOpens) (n : ℤ) :
    Function.Surjective (chartSections f I F p V n) := by
  have : IsAffine V.1.toScheme := V.2
  intro w
  refine ⟨((cohomologyFunctor (affineBaseChart f V) p).map
      (@inv _ _ _ _ (chartPieceRestrict f I F V n)
        (isIso_chartPieceRestrict f I F V n))).hom
    ((cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n)).symm
      ((Stacks.Blowup.unitDerived f I F p n V.1).app V.1 w)), ?_⟩
  have hiso : ((cohomologyFunctor (affineBaseChart f V) p).map
        (chartPieceRestrict f I F V n)).hom
      (((cohomologyFunctor (affineBaseChart f V) p).map
        (@inv _ _ _ _ (chartPieceRestrict f I F V n)
          (isIso_chartPieceRestrict f I F V n))).hom
        ((cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n)).symm
          ((Stacks.Blowup.unitDerived f I F p n V.1).app V.1 w))) =
      (cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n)).symm
        ((Stacks.Blowup.unitDerived f I F p n V.1).app V.1 w) := by
    refine Eq.trans (cohomologyFunctor_map_comp_apply (affineBaseChart f V) p _ _ _) ?_
    refine Eq.trans (congrArg
      (fun φ : chartRees f I F V n ⟶ chartRees f I F V n =>
        ((cohomologyFunctor (affineBaseChart f V) p).map φ).hom
          ((cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n)).symm
            ((Stacks.Blowup.unitDerived f I F p n V.1).app V.1 w)))
      (@IsIso.inv_hom_id _ _ _ _ (chartPieceRestrict f I F V n)
        (isIso_chartPieceRestrict f I F V n))) ?_
    exact cohomologyFunctor_map_id_apply (affineBaseChart f V) p _
  simp only [chartSections]
  refine Eq.trans (congrArg
    (fun y : Γ(extendDerived f V.1 p (chartRees f I F V n), V.1) =>
      inv ((Stacks.Blowup.unitDerived f I F p n V.1).app V.1) y)
    (Eq.trans (congrArg (cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n)) hiso)
      ((cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n)).apply_symm_apply _))) ?_
  exact Stacks.Blowup.unitDerived_inv_hom_app f I F p n V.1 w

/-- **The semilinearity of the comparison.** Acting on the cohomology of the chart by a
homogeneous element `b` of degree `k` of the ring Rees algebra `⨁ₙ ℐ(V)ⁿ` and then comparing is
comparing and then acting by the section of `ℐᵏ` over `V` attached to `b`.

The left-hand action is `Stacks.Cohomology.FormalFunctions.actHom`, which is the action
[Stacks, Tag 02O8] is about on the chart; the right-hand one is
`Stacks.Blowup.pushforwardReesGradedModulePlus`'s, presented as `Stacks.Blowup.smulPlus`. -/
public theorem chartSections_actHom [F.IsQuasicoherent] (V : Y.affineOpens) {k : ℕ}
    (b : ↥(Stacks.Blowup.reesGrading (I.ideal V) k)) (n : ℤ)
    (z : (cohomologyFunctor (affineBaseChart f V) p).obj
      ((reesFiltrationModule (I.ideal V) (affineBaseChart f V)
        (affineBaseChartModule f F V)).piece n)) :
    chartSections f I F p V (n + (k : ℤ))
        (((cohomologyFunctor (affineBaseChart f V) p).map
          (actHom (I.ideal V) (affineBaseChart f V)
            (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
              (affineBaseChartModule f F V)) b n rfl)).hom z) =
      Stacks.Blowup.smulPlus f I F p n (k : ℤ) (op V.1)
        (chartSections f I F p V n z) (chartReesSection I V b rfl) := by
  have : IsAffine V.1.toScheme := V.2
  -- the left-hand side, through the factored action square
  have hleft : ((cohomologyFunctor (affineBaseChart f V) p).map
        (chartPieceRestrict f I F V (n + (k : ℤ)))).hom
      (((cohomologyFunctor (affineBaseChart f V) p).map
        (actHom (I.ideal V) (affineBaseChart f V)
          (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
            (affineBaseChartModule f F V)) b n rfl)).hom z) =
      ((cohomologyFunctor (affineBaseChart f V) p).map
        (Stacks.Blowup.mulRestrict f I F n (k : ℤ) V.1
          (Stacks.Blowup.reesPieceComapSection f I (k : ℤ) (op V.1)
            (chartReesSection I V b rfl)))).hom
        (((cohomologyFunctor (affineBaseChart f V) p).map
          (chartPieceRestrict f I F V n)).hom z) := by
    refine Eq.trans (cohomologyFunctor_map_comp_apply (affineBaseChart f V) p _ _ z) ?_
    refine Eq.trans ?_ (cohomologyFunctor_map_comp_apply (affineBaseChart f V) p _ _ z).symm
    exact congrArg (fun φ : (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
          (affineBaseChartModule f F V)).piece n ⟶ chartRees f I F V (n + (k : ℤ)) =>
        ((cohomologyFunctor (affineBaseChart f V) p).map φ).hom z)
      (actHom_comp_chartPieceRestrict f I F V b n)
  -- the splitting of `R ᵖ f_*(mulHom)` used by `Stacks.Blowup.smulSectionHom_comp`
  have hsplit : ((Scheme.Modules.pushforward f).rightDerived p).map
        (Stacks.Blowup.mulHom f I F n (k : ℤ) V.1
          (Stacks.Blowup.reesPieceComapSection f I (k : ℤ) (op V.1)
            (chartReesSection I V b rfl))) =
      Stacks.Blowup.unitDerived f I F p n V.1 ≫
        ((Scheme.Modules.pushforward f).rightDerived p).map
          ((Scheme.Modules.pushforward (f ⁻¹ᵁ V.1).ι).map
            (Stacks.Blowup.mulRestrict f I F n (k : ℤ) V.1
              (Stacks.Blowup.reesPieceComapSection f I (k : ℤ) (op V.1)
                (chartReesSection I V b rfl)))) :=
    Functor.map_comp _ _ _
  have hunit : (Stacks.Blowup.unitDerived f I F p n V.1).app V.1
        (chartSections f I F p V n z) =
      cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n)
        (((cohomologyFunctor (affineBaseChart f V) p).map
          (chartPieceRestrict f I F V n)).hom z) := by
    simp only [chartSections]
    exact Stacks.Blowup.unitDerived_hom_inv_app f I F p n V.1 _
  have hrhs : Stacks.Blowup.smulPlus f I F p n (k : ℤ) (op V.1)
        (chartSections f I F p V n z) (chartReesSection I V b rfl) =
      inv ((Stacks.Blowup.unitDerived f I F p (n + (k : ℤ)) V.1).app V.1)
        ((((Scheme.Modules.pushforward f).rightDerived p).map
          ((Scheme.Modules.pushforward (f ⁻¹ᵁ V.1).ι).map
            (Stacks.Blowup.mulRestrict f I F n (k : ℤ) V.1
              (Stacks.Blowup.reesPieceComapSection f I (k : ℤ) (op V.1)
                (chartReesSection I V b rfl))))).app V.1
          (cohomologyExtendSectionsEquiv f V.1 p (chartRees f I F V n)
            (((cohomologyFunctor (affineBaseChart f V) p).map
              (chartPieceRestrict f I F V n)).hom z))) := by
    refine Eq.trans (Stacks.Blowup.smulSectionHom_apply f I F p n (k : ℤ) V.1 _
      (chartSections f I F p V n z)) ?_
    refine congrArg (fun y => inv
      ((Stacks.Blowup.unitDerived f I F p (n + (k : ℤ)) V.1).app V.1) y) ?_
    refine Eq.trans (congrArg (fun ψ : ((Scheme.Modules.pushforward f).rightDerived p).obj
        (Stacks.Blowup.reesComapMod f I F n) ⟶
        ((Scheme.Modules.pushforward f).rightDerived p).obj
          ((Scheme.Modules.pushforward (f ⁻¹ᵁ V.1).ι).obj
            (chartRees f I F V (n + (k : ℤ)))) =>
      ψ.app V.1 (chartSections f I F p V n z)) hsplit) ?_
    exact congrArg (fun y => (((Scheme.Modules.pushforward f).rightDerived p).map
      ((Scheme.Modules.pushforward (f ⁻¹ᵁ V.1).ι).map
        (Stacks.Blowup.mulRestrict f I F n (k : ℤ) V.1
          (Stacks.Blowup.reesPieceComapSection f I (k : ℤ) (op V.1)
            (chartReesSection I V b rfl))))).app V.1 y) hunit
  rw [hrhs]
  simp only [chartSections, hleft]
  exact congrArg (fun y => inv
      ((Stacks.Blowup.unitDerived f I F p (n + (k : ℤ)) V.1).app V.1) y)
    (cohomologyExtendSectionsEquiv_naturality f V.1 p (chartRees f I F V n)
      (chartRees f I F V (n + (k : ℤ)))
      (Stacks.Blowup.mulRestrict f I F n (k : ℤ) V.1
        (Stacks.Blowup.reesPieceComapSection f I (k : ℤ) (op V.1)
          (chartReesSection I V b rfl)))
      (((cohomologyFunctor (affineBaseChart f V) p).map
        (chartPieceRestrict f I F V n)).hom z))

end Stacks.Algebraization

end
