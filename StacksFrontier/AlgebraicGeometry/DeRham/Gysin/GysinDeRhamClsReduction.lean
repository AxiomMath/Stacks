module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartForms
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDeRhamTarget
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcisionAbelian

/-!
# Splitting the one hypothesis of Stacks 0G87 into an excision half and a class-map half

`Stacks.Gysin.ClsCommutesWithDeRham` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamTarget.lean` is the **one** remaining
hypothesis of the square of [Stacks, Tag 0G87] at the chart data of [Stacks, Tag 0G86]: the class
map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] of an equation chart is natural along the relative
de Rham differential of `X/S` on the equation wedges `ω ∧ d f₁ ∧ ⋯ ∧ d f_c`.

`Stacks.Gysin.chartClsHom`, the class map of a chart, is **two** factors: the class map of
[Stacks, Tag 0G7Q] for the chart's own *global* equations on `W.toScheme`, which is
`Stacks.Perfect.SupportedFraction.supportedFractionSource`, followed by the derived excision of
[Stacks, Tag 0G78] on degree-`c` cohomology sheaves, `Stacks.Gysin.supportCohomologyRestrictIso`,
which carries the result back to the restriction to `W` of the global target
`Stacks.Gysin.gysinTarget`.  Accordingly the naturality splits in two, and **this file proves that
the split is valid**: the two halves together give `ClsCommutesWithDeRham`, and nothing else is
needed.

* the **excision half** is `Stacks.Gysin.SupportCohomologyRestrictAbNatural` of
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcisionAbelian.lean`, at the de Rham
  differential read as a morphism of the underlying abelian sheaves — that the abelian reading of
  the excision commutes with the action of [Stacks, Tag 0G74] part (2);
* the **class-map half** is `Stacks.Gysin.ChartFractionCommutesWithDeRham` below — the same
  naturality for `supportedFractionSource` alone, on the chart, with no excision in it.

Before this file nothing joined the two: `GysinDeRhamTarget.lean` did not even import
`GysinTargetExcisionAbelian.lean`, and `SupportCohomologyRestrictAbNatural` had no consumer
anywhere, so granting it left `ClsCommutesWithDeRham` no closer.

## Main definitions

* `Stacks.Gysin.abRestrictSections`: **the action on the sections over an open `V ≤ W` of the
  ambient scheme of a morphism of the underlying abelian sheaves of two restrictions to the chart
  `W`.**  This is `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections` for a morphism that is
  only additive — the de Rham differential is `𝒪_X`-linear for no `X`, so the module-level notion
  does not apply to it — and it is the bridge between a square proved on the chart and the square
  of [Stacks, Tag 0G87], whose vertical arrows are morphisms of abelian sheaves on `X`.
* `Stacks.Gysin.ChartFractionCommutesWithDeRham`: **the class-map half**, as a proposition: on the
  chart, where the equations are global sections and [Stacks, Tag 0G7Q] applies verbatim, the
  class map `Stacks.Perfect.SupportedFraction.supportedFractionSource` is natural along the
  relative de Rham differential of `X/S` restricted to the chart, **on the equation wedges**, the
  local cohomology sheaf of the chart acting on the differential through [Stacks, Tag 0G74]
  part (2).

## Main results

* `Stacks.Gysin.abRestrictSections_restrictAbHom`: reading the restriction to a chart of a
  morphism of abelian sheaves on `X` over an open of the chart recovers the morphism itself, and
  `Stacks.Gysin.abRestrictSections_abelianSheaf_map`: for a morphism of modules the reading is
  `restrictSections`.  Together with `Stacks.Gysin.abRestrictSections_comp` these are what carry a
  morphism equation on the chart to the section-level statement
  `Stacks.Gysin.ClsCommutesWithDeRham` is.
* `Stacks.Gysin.chartClsSquare_of_excision_of_chartFraction`: **the square on a chart from the two
  halves** — the class-map half is the square for `supportedFractionSource`, and the excision
  half, conjugated into the inverse direction, carries it across the excision.
* `Stacks.Gysin.abSectionsHom_gysinTargetDeRhamHom_chartCls` and
  `Stacks.Gysin.abSectionsHom_gysinTargetDeRhamHom_chartClsOfGen`: that square read on the
  sections over an open of the chart.
* `Stacks.Gysin.clsCommutesWithDeRham_of_excision_of_chartFraction`: **the one hypothesis of
  [Stacks, Tag 0G87] at the chart data of [Stacks, Tag 0G86], from the two halves and nothing
  else**, and `Stacks.Gysin.gysinHom_comm_deRham_of_excision_of_chartFraction`: the square of
  [Stacks, Tag 0G87] itself under those two hypotheses.

## Implementation notes

**No `@[stacks 0G87]` attribute is attached here, and none should be.**  Everything below is an
implication with two explicit hypotheses; a tag counts only on a declaration proved under the
source's own hypotheses, and a suffix names a partial object and can never license an assumed
input.  Both hypotheses are theorems elsewhere — the class-map half is
`Stacks.Gysin.chartFractionCommutesWithDeRham` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinChartFractionDeRham.lean`, the excision half is
`Stacks.Gysin.supportCohomologyRestrictAbNatural` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean` — and the tag is
registered where both are supplied rather than assumed:
`Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRank.lean`.

**Why the class-map half carries the wedge.**  At an arbitrary section the class map does *not*
commute with `d`: the predecessor of `ClsCommutesWithDeRham` asserted `d(y/∏f) = (dy)/∏f` and was
refuted with `S = Spec k`, `X = Spec k[t, s]`, `Z = {t = 0}`, `f₁ = t`, `c = 1`, `p = 0`,
`y = t·ds` — the Leibniz term was dropped.  So `ChartFractionCommutesWithDeRham` is stated with
`Stacks.Gysin.gysinWedgeOnHom` precomposed on both sides, exactly as `ClsCommutesWithDeRham` is
quantified only over equation wedges, and exactly as the *global* square
`AlgebraicGeometry.Scheme.Hom.GysinFormulaCommutesWithDeRham` is stated.  The reduction below
would be *false* without it.

**What discharges each half.**  The excision half holds for an arbitrary morphism of the
underlying abelian sheaves as soon as
`Stacks.Gysin.ExcisionAbComparisonEqAbelianExcision` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinAbelianExcisionBridge.lean` does, by
`Stacks.Gysin.supportCohomologyRestrictAbNatural_of_excisionAbComparison_eq` there; that equation
is the derived-versus-classical comparison of the two excisions and is open.  For the class-map
half the corresponding *global* statement is proved unconditionally —
`Stacks.Perfect.SupportedEndoForgetDegreewise.gysinFormulaCommutesWithDeRham`, which carries no
quasi-coherence hypothesis, the differential forms being quasi-coherent by
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms_natCast_add` — but in the
`AlgebraicGeometry.Scheme.Hom.formFractionClass` spelling of the class map and the
`AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap` spelling of [Stacks, Tag 0G74] part (2),
whereas the chart transport is built on `supportedFractionSource` and
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap`.  Turning the one into the
other needs the comparison of the two spellings of the class map
(`Stacks.Perfect.supportedFractionSource_comp_supportCohomologyToPushforward` of
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/FractionClassSpellings.lean`), the
comparison of the two spellings of [Stacks, Tag 0G74] part (2), and the identification of
`Ω^•_{X/S}|_W` with `Ω^•_{W/S}` carrying the differentials to each other.  The class-map half is
therefore not closed here; it is a statement about `W.toScheme` alone, with no excision and no
derived-versus-classical comparison in it, which is strictly less than what the whole hypothesis
used to need.

**Quasi-coherence is supplied in this setting.**  `supportedFractionSource` asks for
`[F.IsQuasicoherent]` of the coefficient module, and the coefficient module here is
`(Ω^{p+c}_{X/S})|_W`; the instance is derived from
`isQuasicoherent_relativeDifferentialForms_natCast_add`, exactly as it is inside
`Stacks.Gysin.chartClsHom`, so no quasi-coherence hypothesis appears anywhere below.

**Every chase is a helper at a variable category, applied with `exact`, with the objects implicit
and the morphisms explicit.**  `conj_inv_square` and `chart_square_formal` are the whole content
of the chart square as formal identities.  Two further costs are specific to this file.  The
arrow of the excision must be written as `(abelianSheaf W.toScheme).map` of the isomorphism and
*not* as `Stacks.Gysin.supportCohomologyRestrictAbHom`, even though the two are definitionally
equal: the latter spells its source through `Stacks.Gysin.abelianRestrict` and the former through
`Scheme.Modules.restrict`, and asking the elaborator to cross those two spellings four times in
one application exhausts the heartbeat budget, whereas crossing it once, inside the hypothesis
`hexc`, costs nothing.  And `Stacks.Gysin.chartGysinChartData` is a structure literal with a dozen
fields, so a single definitional unification that has to unfold several of its projections at once
exceeds the recursion depth; `clsCommutesWithDeRham_of_excision_of_chartFraction` therefore
rewrites each projection separately, with every rewrite rule instantiated in advance, and finishes
with `convert … using 2`, which splits the one deep unification into shallow ones.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RingedSpace
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Perfect.GysinAbelianSquare (supportCohomologySheafAbelianMap)
open Stacks.Perfect.LocalCohomologyExcision (chartOpen ι_image_chartOpen)
open Stacks.Perfect.SupportedFraction (supportedFractionSource)

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

variable {Z X S : Scheme.{u}}

/-! ### Formal chases -/

/-- Conjugating a commutative square by two inverse pairs.  Stated at a variable category with
every morphism explicit. -/
theorem conj_inv_square {C₀ : Type*} [Category* C₀] {a b a' b' : C₀}
    (eh : a ⟶ b) (ei : b ⟶ a) (eh' : a' ⟶ b') (ei' : b' ⟶ a')
    (hb : ei ≫ eh = 𝟙 b) (ha' : eh' ≫ ei' = 𝟙 a')
    (u : b ⟶ b') (v : a ⟶ a') (h : v ≫ eh' = eh ≫ u) :
    ei ≫ v = u ≫ ei' := by
  calc ei ≫ v = ei ≫ v ≫ eh' ≫ ei' := by rw [ha', Category.comp_id]
    _ = ei ≫ eh ≫ u ≫ ei' := by rw [reassoc_of% h]
    _ = u ≫ ei' := by simp [reassoc_of% hb]

/-- The whole chase of the chart square, at a variable category: a square `hexc` conjugated into
the inverse direction and pasted onto a square `hcls` which holds only after precomposition with
`w`. -/
theorem chart_square_formal {C₀ : Type*} [Category* C₀]
    {A B B' Tp Tp' Sp Sp' : C₀} (w : A ⟶ B) (sp : B ⟶ Sp) (sp' : B' ⟶ Sp')
    (eh : Tp ⟶ Sp) (ei : Sp ⟶ Tp) (eh' : Tp' ⟶ Sp') (ei' : Sp' ⟶ Tp')
    (dW : B ⟶ B') (u : Sp ⟶ Sp') (v : Tp ⟶ Tp')
    (hb : ei ≫ eh = 𝟙 Sp) (ha' : eh' ≫ ei' = 𝟙 Tp')
    (hexc : v ≫ eh' = eh ≫ u) (hcls : w ≫ sp ≫ u = w ≫ dW ≫ sp') :
    w ≫ (sp ≫ ei) ≫ v = w ≫ dW ≫ sp' ≫ ei' := by
  simp only [Category.assoc, conj_inv_square eh ei eh' ei' hb ha' u v hexc]
  rw [reassoc_of% hcls]

/-! ### The action on sections over an open of a chart -/

/-- The action on sections of a composite of morphisms of the underlying abelian sheaves. -/
theorem abSectionsHom_comp {Y : Scheme.{u}} {F G H : Y.Modules}
    (α : (abelianSheaf Y).obj F ⟶ (abelianSheaf Y).obj G)
    (β : (abelianSheaf Y).obj G ⟶ (abelianSheaf Y).obj H) (V : Y.Opens) (x : Γ(F, V)) :
    abSectionsHom (α ≫ β) V x = abSectionsHom β V (abSectionsHom α V x) := rfl

/-- The action on sections of the underlying morphism of a morphism of modules. -/
theorem abSectionsHom_abelianSheaf_map {Y : Scheme.{u}} {F G : Y.Modules} (φ : F ⟶ G)
    (V : Y.Opens) (x : Γ(F, V)) :
    abSectionsHom ((abelianSheaf Y).map φ) V x = φ.app V x := rfl

/-- **The action on the sections over an open of a chart of a morphism of the underlying abelian
sheaves of two restrictions to the chart.**  The sections of `ℱ|_W` over `chartOpen W hV` are the
sections of `ℱ` over `W.ι ''ᵁ chartOpen W hV`, which is `V` again; the identification is applied
as the pair of mutually inverse restriction maps along it, exactly as `Stacks.Gysin.chartCls` does
for the class map and `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections` for a morphism of
modules. -/
def abRestrictSections {M N : X.Modules} (W : X.Opens)
    (θ : (abelianSheaf W.toScheme).obj (Scheme.Modules.restrict M W.ι) ⟶
      (abelianSheaf W.toScheme).obj (Scheme.Modules.restrict N W.ι))
    (V : X.Opens) (hV : V ≤ W) (m : Γ(M, V)) : Γ(N, V) :=
  N.presheaf.map (homOfLE (ι_image_chartOpen W hV).ge).op
    (abSectionsHom θ (chartOpen W hV)
      (M.presheaf.map (homOfLE (ι_image_chartOpen W hV).le).op m))

/-- Reading a composite over an open of the chart composes the two readings: the two restriction
maps along the equal opens that meet in the middle cancel. -/
theorem abRestrictSections_comp {M N P : X.Modules} (W : X.Opens)
    (α : (abelianSheaf W.toScheme).obj (Scheme.Modules.restrict M W.ι) ⟶
      (abelianSheaf W.toScheme).obj (Scheme.Modules.restrict N W.ι))
    (β : (abelianSheaf W.toScheme).obj (Scheme.Modules.restrict N W.ι) ⟶
      (abelianSheaf W.toScheme).obj (Scheme.Modules.restrict P W.ι))
    (V : X.Opens) (hV : V ≤ W) (m : Γ(M, V)) :
    abRestrictSections W (α ≫ β) V hV m
      = abRestrictSections W β V hV (abRestrictSections W α V hV m) :=
  congrArg (fun z => P.presheaf.map (homOfLE (ι_image_chartOpen W hV).ge).op z)
    (congrArg (abSectionsHom β (chartOpen W hV))
      (modules_presheaf_map_homOfLE_self (ι_image_chartOpen W hV).ge
        (ι_image_chartOpen W hV).le
        (abSectionsHom α (chartOpen W hV)
          (M.presheaf.map (homOfLE (ι_image_chartOpen W hV).le).op m))).symm)

/-- Reading the underlying morphism of a morphism of modules over an open of the chart is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictSections`. -/
theorem abRestrictSections_abelianSheaf_map {M N : X.Modules} (W : X.Opens)
    (φ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (V : X.Opens) (hV : V ≤ W) (m : Γ(M, V)) :
    abRestrictSections W ((abelianSheaf W.toScheme).map φ) V hV m
      = restrictSections φ V hV m :=
  (restrictSections_apply φ V hV m).symm

/-- **Reading the restriction to a chart of a morphism of the underlying abelian sheaves over an
open of the chart recovers the morphism itself.**  This is what lets the square of
[Stacks, Tag 0G87], whose vertical arrows live on `X`, be settled by a square on the chart. -/
theorem abRestrictSections_restrictAbHom {M N : X.Modules} (W : X.Opens)
    (ψ : (abelianSheaf X).obj M ⟶ (abelianSheaf X).obj N)
    (V : X.Opens) (hV : V ≤ W) (m : Γ(M, V)) :
    abRestrictSections W (restrictAbHom W ψ) V hV m = abSectionsHom ψ V m :=
  Eq.trans
    (congrArg (fun z => N.presheaf.map (homOfLE (ι_image_chartOpen W hV).ge).op z)
      (abSectionsHom_res ψ (ι_image_chartOpen W hV).le m))
    (modules_presheaf_map_homOfLE_self (ι_image_chartOpen W hV).le
      (ι_image_chartOpen W hV).ge (abSectionsHom ψ V m))

/-- Reading a three-factor composite whose last factor is the restriction of a morphism on the
ambient scheme. -/
theorem abRestrictSections_comp3_right {M N P Q : X.Modules} (W : X.Opens)
    (φ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (φ' : Scheme.Modules.restrict N W.ι ⟶ Scheme.Modules.restrict P W.ι)
    (ψ : (abelianSheaf X).obj P ⟶ (abelianSheaf X).obj Q)
    (V : X.Opens) (hV : V ≤ W) (m : Γ(M, V)) :
    abRestrictSections W
        ((abelianSheaf W.toScheme).map φ ≫ (abelianSheaf W.toScheme).map φ' ≫
          restrictAbHom W ψ) V hV m
      = abSectionsHom ψ V (restrictSections φ' V hV (restrictSections φ V hV m)) := by
  rw [abRestrictSections_comp, abRestrictSections_comp, abRestrictSections_restrictAbHom,
    abRestrictSections_abelianSheaf_map, abRestrictSections_abelianSheaf_map]

/-- Reading a three-factor composite whose middle factor is the restriction of a morphism on the
ambient scheme. -/
theorem abRestrictSections_comp3_middle {M N P Q : X.Modules} (W : X.Opens)
    (φ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (ψ : (abelianSheaf X).obj N ⟶ (abelianSheaf X).obj P)
    (φ' : Scheme.Modules.restrict P W.ι ⟶ Scheme.Modules.restrict Q W.ι)
    (V : X.Opens) (hV : V ≤ W) (m : Γ(M, V)) :
    abRestrictSections W
        ((abelianSheaf W.toScheme).map φ ≫ restrictAbHom W ψ ≫
          (abelianSheaf W.toScheme).map φ') V hV m
      = restrictSections φ' V hV (abSectionsHom ψ V (restrictSections φ V hV m)) := by
  rw [abRestrictSections_comp, abRestrictSections_comp, abRestrictSections_abelianSheaf_map,
    abRestrictSections_restrictAbHom, abRestrictSections_abelianSheaf_map]

/-! ### The class-map half -/

/-- **The class-map half of the one hypothesis of [Stacks, Tag 0G87]**: on the chart `W`, where
the equations are global sections and [Stacks, Tag 0G7Q] applies verbatim, the class map
`Stacks.Perfect.SupportedFraction.supportedFractionSource` is natural along the relative de Rham
differential of `X/S` restricted to the chart, **on the equation wedges**, the local cohomology
sheaf of the chart acting on the differential through [Stacks, Tag 0G74] part (2).

No excision occurs in it: both sides are morphisms of abelian sheaves on `W.toScheme` between the
restrictions to `W` of the forms of `X/S` and the local cohomology sheaves taken *on the chart*.
That is the whole point of the splitting — the passage from the chart to `X` is the other half,
`Stacks.Gysin.SupportCohomologyRestrictAbNatural`.

The wedge `Stacks.Gysin.gysinWedgeOnHom` on the left of both composites is not a convenience: at
an arbitrary section the equation is *false*, see the counterexample in the implementation notes
of `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamCompat.lean`.

**This is the shape of the proved global square, not a weakening of it.**  The right-hand
composite here is "wedge, then the differential in degree `p + c`, then the class map", whereas
`AlgebraicGeometry.Scheme.Hom.GysinFormulaCommutesWithDeRham` — proved unconditionally by
`Stacks.Perfect.SupportedEndoForgetDegreewise.gysinFormulaCommutesWithDeRham` — has
"the differential in degree `p`, then the wedge in degree `p + 1`, then the class map".  The two
agree because the wedge factor commutes with `d`, which is step (iii) of the source's proof and is
`AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_comm_deRhamDifferentialPresheafHom`; the shape chosen
here is the one `Stacks.Gysin.ClsCommutesWithDeRham` asks for, which applies
`Stacks.Gysin.ambientDeRhamShift` to the wedge. -/
def ChartFractionCommutesWithDeRham (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ}
    (p : ℕ) (W : X.Opens) (g : Fin (d + 1) → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet (restrictEquations W g) ⊆ W.ι ⁻¹' Set.range i.base) : Prop :=
  haveI : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  haveI : (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π (p + 1) (d + 1)
  (abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)) ≫
      (abelianSheaf W.toScheme).map
          (supportedFractionSource (restrictEquations W g)
            (Scheme.Modules.restrict
              (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) W.ι) hTW hTf) ≫
        supportCohomologySheafAbelianMap hTW (d + 1)
          (restrictAbHom W (ambientDeRhamShiftAbHom π (d + 1) p)) =
    (abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)) ≫
      restrictAbHom W (ambientDeRhamShiftAbHom π (d + 1) p) ≫
        (abelianSheaf W.toScheme).map
          (supportedFractionSource (restrictEquations W g)
            (Scheme.Modules.restrict
              (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ))) W.ι)
            hTW hTf)

/-! ### The square on a chart, from the two halves -/

/-- **The square of [Stacks, Tag 0G87] on a chart, from the excision half and the class-map
half.**  The chart class map `Stacks.Gysin.chartClsHom` is the class map of [Stacks, Tag 0G7Q] of
the chart's own global equations followed by the derived excision of [Stacks, Tag 0G78]; the
class-map half is the square for the first factor and the excision half, conjugated into the
inverse direction, carries it across the second. -/
theorem chartClsSquare_of_excision_of_chartFraction (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {d : ℕ} (p : ℕ) (W : X.Opens) (g : Fin (d + 1) → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet (restrictEquations W g) ⊆ W.ι ⁻¹' Set.range i.base)
    (hexc : SupportCohomologyRestrictAbNatural W (isClosed_range_base i) hTW (d + 1)
      (ambientDeRhamShiftAbHom π (d + 1) p))
    (hcls : ChartFractionCommutesWithDeRham i π p W g hTW hTf) :
    (abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)) ≫
        (abelianSheaf W.toScheme).map
            (chartClsHom i π p W (restrictEquations W g) hTW hTf) ≫
          restrictAbHom W (gysinTargetDeRhamHom i π (d + 1) p) =
      (abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)) ≫
        restrictAbHom W (ambientDeRhamShiftAbHom π (d + 1) p) ≫
          (abelianSheaf W.toScheme).map
            (chartClsHom i π (p + 1) W (restrictEquations W g) hTW hTf) := by
  have : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  have : (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π (p + 1) (d + 1)
  exact chart_square_formal
    ((abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)))
    ((abelianSheaf W.toScheme).map
      (supportedFractionSource (restrictEquations W g)
        (Scheme.Modules.restrict
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) W.ι) hTW hTf))
    ((abelianSheaf W.toScheme).map
      (supportedFractionSource (restrictEquations W g)
        (Scheme.Modules.restrict
          (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ))) W.ι) hTW hTf))
    ((abelianSheaf W.toScheme).map
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW ((d + 1 : ℕ) : ℤ)
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).hom)
    ((abelianSheaf W.toScheme).map
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW ((d + 1 : ℕ) : ℤ)
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv)
    ((abelianSheaf W.toScheme).map
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW ((d + 1 : ℕ) : ℤ)
        (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ)))).hom)
    ((abelianSheaf W.toScheme).map
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW ((d + 1 : ℕ) : ℤ)
        (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv)
    (restrictAbHom W (ambientDeRhamShiftAbHom π (d + 1) p))
    (supportCohomologySheafAbelianMap hTW (d + 1)
      (restrictAbHom W (ambientDeRhamShiftAbHom π (d + 1) p)))
    (restrictAbHom W (gysinTargetDeRhamHom i π (d + 1) p))
    (((abelianSheaf W.toScheme).mapIso
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW ((d + 1 : ℕ) : ℤ)
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))))).inv_hom_id)
    (((abelianSheaf W.toScheme).mapIso
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW ((d + 1 : ℕ) : ℤ)
        (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ))))).hom_inv_id)
    hexc hcls

/-! ### The chart-local naturality of the class map, from the two halves -/

/-- **The class map of a chart commutes with the de Rham differential on the equation wedges, on
sections over an open of the chart, given the two halves.**  This is
`chartClsSquare_of_excision_of_chartFraction` read over an open `V ≤ W` of the ambient scheme
through `Stacks.Gysin.abRestrictSections`, which is where the vertical arrows of the square of
[Stacks, Tag 0G87] — morphisms of abelian sheaves on `X` — meet a square proved on the chart. -/
theorem abSectionsHom_gysinTargetDeRhamHom_chartCls (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {d : ℕ} (p : ℕ) (W : X.Opens) (g : Fin (d + 1) → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet (restrictEquations W g) ⊆ W.ι ⁻¹' Set.range i.base)
    (hexc : SupportCohomologyRestrictAbNatural W (isClosed_range_base i) hTW (d + 1)
      (ambientDeRhamShiftAbHom π (d + 1) p))
    (hcls : ChartFractionCommutesWithDeRham i π p W g hTW hTf)
    (V : X.Opens) (hV : V ≤ W) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    abSectionsHom (gysinTargetDeRhamHom i π (d + 1) p) V
        (chartCls i π p W (restrictEquations W g) hTW hTf V hV
          (gysinWedgeOn π g (p : ℤ) hV ω))
      = chartCls i π (p + 1) W (restrictEquations W g) hTW hTf V hV
          (ambientDeRhamShift π (d + 1) p V (gysinWedgeOn π g (p : ℤ) hV ω)) := by
  have h := congrArg (fun θ => abRestrictSections W θ V hV ω)
    (chartClsSquare_of_excision_of_chartFraction i π p W g hTW hTf hexc hcls)
  rw [abRestrictSections_comp3_right, abRestrictSections_comp3_middle,
    restrictSections_gysinWedgeOnHom] at h
  rw [chartCls_eq_restrictSections, chartCls_eq_restrictSections,
    ← abSectionsHom_ambientDeRhamShiftAbHom]
  exact h

/-- `Stacks.Gysin.chartClsOfGen` is `Stacks.Gysin.chartCls` of the chart's own global equations,
on a section.  True by definition, and recorded so that the two spellings can be exchanged without
a definitional unfolding inside a larger statement. -/
theorem chartClsOfGen_apply (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens) (g : Fin (d + 1) → Γ(X, W))
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W g)
    (hvanish : ∀ (V : X.Opens) (hV : V ≤ W) (j : Fin (d + 1)),
      (i.app V).hom (X.presheaf.map (homOfLE hV).op (g j)) = 0)
    (V : X.Opens) (hV : V ≤ W)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V)) :
    chartClsOfGen i π p W g hgen hvanish V hV y
      = chartCls i π p W (restrictEquations W g) (isClosed_preimage_range_base i W)
          (equationsClosedSet_restrictEquations i W
            (isCutOutByEquationsOn_of_isGeneratedByOn i hgen hvanish)).le V hV y := rfl

/-- `abSectionsHom_gysinTargetDeRhamHom_chartCls` for the class map
`Stacks.Gysin.chartClsOfGen` of a chart whose equations generate the ideal, which is the shape the
`cls` field of `Stacks.Gysin.chartGysinChartData` takes. -/
theorem abSectionsHom_gysinTargetDeRhamHom_chartClsOfGen (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {d : ℕ} (p : ℕ) (W : X.Opens) (g : Fin (d + 1) → Γ(X, W))
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W g)
    (hvanish : ∀ (V : X.Opens) (hV : V ≤ W) (j : Fin (d + 1)),
      (i.app V).hom (X.presheaf.map (homOfLE hV).op (g j)) = 0)
    (hexc : SupportCohomologyRestrictAbNatural W (isClosed_range_base i)
      (isClosed_preimage_range_base i W) (d + 1) (ambientDeRhamShiftAbHom π (d + 1) p))
    (hcls : ChartFractionCommutesWithDeRham i π p W g
      (isClosed_preimage_range_base i W)
      (equationsClosedSet_restrictEquations i W
        (isCutOutByEquationsOn_of_isGeneratedByOn i hgen hvanish)).le)
    (V : X.Opens) (hV : V ≤ W) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    abSectionsHom (gysinTargetDeRhamHom i π (d + 1) p) V
        (chartClsOfGen i π p W g hgen hvanish V hV (gysinWedgeOn π g (p : ℤ) hV ω))
      = chartClsOfGen i π (p + 1) W g hgen hvanish V hV
          (ambientDeRhamShift π (d + 1) p V (gysinWedgeOn π g (p : ℤ) hV ω)) := by
  rw [chartClsOfGen_apply, chartClsOfGen_apply]
  exact abSectionsHom_gysinTargetDeRhamHom_chartCls i π p W g _ _ hexc hcls V hV ω

/-! ### The one hypothesis of Stacks 0G87, from the two halves -/

section Assemble

variable (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ) (Chart : Type u)
  (ambient : Chart → X.Opens) (equations : (a : Chart) → Fin (d + 1) → Γ(X, ambient a))
  (hvanish : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a) (j : Fin (d + 1)),
    (i.app V).hom (X.presheaf.map (homOfLE hV).op (equations a j)) = 0)
  (hcover : ∀ x : X, ∃ a, x ∈ ambient a)
  (hgen : ∀ a, IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) (ambient a) (equations a))

/-- `Stacks.Gysin.chartGysinChartData_cls` with the containment stated through the chart data, so
that it applies to the proof term the field `chart_ambient` of
`Stacks.Gysin.GysinDeRhamData` supplies. -/
private theorem chartGysinChartData_cls' (a : Chart) (V : X.Opens)
    (hV : V ≤ (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).ambient a) :
    (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).cls a V hV
      = chartClsOfGen i π p (ambient a) (equations a) (hgen a) (hvanish a) V hV := rfl

/-- The equation wedge of a chart of the chart data is the equation wedge of the given
equations. -/
private theorem gysinWedgeOn_chartGysinChartData_equations (a : Chart) (V : X.Opens)
    (hV : V ≤ (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).ambient a)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    gysinWedgeOn π
        ((chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).equations a)
        (p : ℤ) hV ω = gysinWedgeOn π (equations a) (p : ℤ) hV ω := rfl

/-- The arrow on the two targets of the chart data is the arrow of [Stacks, Tag 0G74] part (2) at
the Gysin target: the two unfoldings it is carried along are reflexivity. -/
private theorem chartGysinTargetDeRhamHom_eq :
    chartGysinTargetDeRhamHom i π p Chart ambient equations hvanish hcover hgen
      = gysinTargetDeRhamHom i π (d + 1) p :=
  gysinTargetDeRhamHomOfEq_rfl i π (d + 1) p

/-- **The one hypothesis of [Stacks, Tag 0G87] follows from the excision half and the class-map
half.**  `Stacks.Gysin.ClsCommutesWithDeRham` at the chart data of [Stacks, Tag 0G86] is the
conjunction of
`Stacks.Gysin.SupportCohomologyRestrictAbNatural` of each chart, at the relative de Rham
differential of `X/S`, and `Stacks.Gysin.ChartFractionCommutesWithDeRham` of each chart — and
nothing else.

Neither half is registered as anything: this is an implication with two explicit hypotheses, and
no `@[stacks 0G87]` attribute is attached here or anywhere.  Its point is that the excision half
is the statement the comparison
`Stacks.Gysin.ExcisionAbComparisonEqAbelianExcision` of `GysinAbelianExcisionBridge.lean`
discharges, by
`Stacks.Gysin.supportCohomologyRestrictAbNatural_of_excisionAbComparison_eq`, so that the two are
joined. -/
theorem clsCommutesWithDeRham_of_excision_of_chartFraction
    (hexc : ∀ a, SupportCohomologyRestrictAbNatural (ambient a) (isClosed_range_base i)
      (isClosed_preimage_range_base i (ambient a)) (d + 1)
      (ambientDeRhamShiftAbHom π (d + 1) p))
    (hcls : ∀ a, ChartFractionCommutesWithDeRham i π p (ambient a) (equations a)
      (isClosed_preimage_range_base i (ambient a))
      (equationsClosedSet_restrictEquations i (ambient a)
        (isCutOutByEquationsOn_of_isGeneratedByOn i (hgen a) (hvanish a))).le) :
    ClsCommutesWithDeRham
      (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover hgen)
      (chartGysinTargetDeRhamHom i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinMatch i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinMatch_ambient i π p Chart ambient equations hvanish hcover hgen) := by
  refine fun (a : Chart) (V : X.Opens) (hV : V ≤ ambient a)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) => ?_
  have ew := gysinWedgeOn_chartGysinChartData_equations i π p Chart ambient equations hvanish
    hcover hgen a V hV ω
  have ec1 := chartGysinChartData_cls' i π p Chart ambient equations hvanish hcover hgen a V hV
  have ec2 := chartGysinChartData_cls' i π (p + 1) Chart ambient equations hvanish hcover hgen a V
    (hV.trans (chartGysinMatch_ambient i π p Chart ambient equations hvanish hcover hgen a))
  have eψ := chartGysinTargetDeRhamHom_eq i π p Chart ambient equations hvanish hcover hgen
  simp only [chartGysinMatch, ew, ec1, ec2, eψ]
  convert abSectionsHom_gysinTargetDeRhamHom_chartClsOfGen i π p (ambient a)
    (equations a) (hgen a) (hvanish a) (hexc a) (hcls a) V hV ω using 2 <;> rfl

/-- **The square of [Stacks, Tag 0G87] for the glued Gysin map of [Stacks, Tag 0G86], under the
two halves.**  This is `Stacks.Gysin.gysinHom_comm_deRham_chartGysinChartData` with its one
hypothesis replaced by the two it splits into. -/
theorem gysinHom_comm_deRham_of_excision_of_chartFraction
    (hexc : ∀ a, SupportCohomologyRestrictAbNatural (ambient a) (isClosed_range_base i)
      (isClosed_preimage_range_base i (ambient a)) (d + 1)
      (ambientDeRhamShiftAbHom π (d + 1) p))
    (hcls : ∀ a, ChartFractionCommutesWithDeRham i π p (ambient a) (equations a)
      (isClosed_preimage_range_base i (ambient a))
      (equationsClosedSet_restrictEquations i (ambient a)
        (isCutOutByEquationsOn_of_isGeneratedByOn i (hgen a) (hvanish a))).le)
    (V : X.Opens) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    abSectionsHom
        (chartGysinTargetDeRhamHom i π p Chart ambient equations hvanish hcover hgen)
        V ((chartGysinChartData i π p Chart ambient equations hvanish hcover
          hgen).gysinHom.app V x)
      = (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover
          hgen).gysinHom.app V (pushforwardDeRham i π p V x) :=
  gysinHom_comm_deRham_chartGysinChartData i π p Chart ambient equations hvanish hcover hgen
    (clsCommutesWithDeRham_of_excision_of_chartFraction i π p Chart ambient equations hvanish
      hcover hgen hexc hcls) V x

end Assemble

end Stacks.Gysin

end
