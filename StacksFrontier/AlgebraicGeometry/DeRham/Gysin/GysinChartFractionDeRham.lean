module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDeRhamClsReduction
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechCokernelPassage
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetDegreewise

/-!
# The class-map half of the one hypothesis of Stacks 0G87

`Stacks.Gysin.ClsCommutesWithDeRham` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamTarget.lean` is the one remaining
hypothesis of the square of [Stacks, Tag 0G87] at the chart data of [Stacks, Tag 0G86], and
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamClsReduction.lean` splits it into two: the
**excision half**, `Stacks.Gysin.SupportCohomologyRestrictAbNatural`, and the **class-map half**,
`Stacks.Gysin.ChartFractionCommutesWithDeRham`.  **This file discharges the class-map half**, for
every closed immersion, every chart and every degree, with no hypothesis beyond the data the
chart carries.

The class-map half says that on a chart `W`, where the equations are global sections and
[Stacks, Tag 0G7Q] applies verbatim, the class map
`Stacks.Perfect.SupportedFraction.supportedFractionSource` of the chart's own equations is natural
along the restriction to `W` of the relative de Rham differential of `X/S`, **on the equation
wedges** — the local cohomology sheaf acting on the differential through [Stacks, Tag 0G74]
part (2) in the shape
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap`.  The wedge on the left of
both composites is not a convenience: at an arbitrary section the statement is false, the
counterexample being recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamCompat.lean`.

Nothing here repeats the derived-category work of [Stacks, Tag 0G85].  The two inputs it rests on
were already in the library and are unconditional: the square of step (ii) between the Čech
cokernel and `i_*ℋ ᶜ_T`,
`Stacks.Perfect.AbelianCechCokernelPassage.map_cokernelLastDifToSupport_abelian_square`, which
holds for an arbitrary morphism of the underlying abelian sheaves and for every closed subset
containing the zero locus of the equations; and the identification of the two constructions of
the action of `i_*ℋ ᶜ_T` on such a morphism, which is
`supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap` of
`Stacks.Perfect.SupportedEndoForgetDegreewise`.
What is new is the passage from the morphism level to the class map
`supportedFractionSource` — which needs the localized Leibniz rule, and nothing else.

## Main definitions

* `Stacks.Gysin.chartDeRhamShiftPresheafHom`: **the relative de Rham differential of `X/S`
  restricted to a chart, as a morphism of the underlying abelian presheaves of the restrictions
  of the forms.**  It is `Stacks.Gysin.restrictAbHom` of
  `Stacks.Gysin.ambientDeRhamShiftAbHom`, written in the
  `AlgebraicGeometry.Scheme.Modules.presheaf` spelling so that the crossing with the
  `Stacks.Gysin.abelianRestrict` spelling happens once.

## Main results

* `Stacks.Gysin.supportedFractionSource_comm_of_smul`: **the class map of [Stacks, Tag 0G7Q], read
  on the coefficient module and in `i_*ℋ ᶜ_T(ℱ)`, is natural along a morphism `ψ` of the
  underlying abelian sheaves that commutes with dividing by the product of the equations after
  precomposition with a factor `u`.**  This is the general statement the chart needs: the fraction
  is not natural in an arbitrary additive morphism, and the localized identity is exactly what
  repairs it.  `Stacks.Gysin.map_comp_supportedFractionSource_comm_of_smul` is the same with the
  factor `u` an `𝒪_Y`-linear morphism, which is the shape of
  `Stacks.Gysin.ChartFractionCommutesWithDeRham`.
* `Stacks.Gysin.ambientDeRhamShift_smul_gysinWedgeOn` and
  `ambientDeRhamShift_smul_gysinWedgeOn_comm`: **the localized Leibniz rule for the equations of a
  chart** — over an open on which the product of the equations is invertible, dividing by that
  product commutes with the de Rham differential on the image of the equation wedge.  This is
  `AlgebraicGeometry.SheafOfModules.d_smul_formProduct_prodDegOne_of_mul_eq_one`, which already
  takes the equations over the open in question rather than globally, restated in the chart's
  vocabulary.
* `Stacks.Gysin.chartFractionCommutesWithDeRham`: **the class-map half of the one hypothesis of
  [Stacks, Tag 0G87] holds**, unconditionally.
* `Stacks.Gysin.clsCommutesWithDeRham_of_excision` and
  `Stacks.Gysin.gysinHom_comm_deRham_of_excision`: **`Stacks.Gysin.ClsCommutesWithDeRham` at the
  chart data of [Stacks, Tag 0G86], and the square of [Stacks, Tag 0G87] itself, from the excision
  half alone.**  The two-hypothesis implications of `GysinDeRhamClsReduction.lean` lose their
  second hypothesis.

## Implementation notes

**No `@[stacks 0G87]` attribute is attached here, and none should be.**  Everything below is
still an implication: its remaining hypothesis is the abelian reading of the derived excision of
[Stacks, Tag 0G78], `Stacks.Gysin.SupportCohomologyRestrictAbNatural`, and a tag counts only on a
declaration proved under the source's own hypotheses.  That hypothesis is now a theorem —
`Stacks.Gysin.supportCohomologyRestrictAbNatural` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean`, which discharges
it for an arbitrary morphism of the underlying abelian sheaves through
`Stacks.Gysin.supportCohomologyRestrictAbNatural_of_excisionAbComparison_eq` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinAbelianExcisionBridge.lean` — and the tag is
registered where that hypothesis is supplied rather than assumed:
`Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRank.lean`.

**Quasi-coherence is not a hypothesis anywhere below.**  `supportedFractionSource` and the square
of step (ii) ask for it of the coefficient modules, which here are the restrictions to the chart
of `Ω^{p+c}_{X/S}`; the instance comes from
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms_natCast_add` together with
the quasi-coherence of a restriction, exactly as inside `Stacks.Gysin.chartClsHom`.

**The scalar action of a chart on the sections of a restriction is not definitionally the ambient
one.**  `Γ(ℱ|_W, V)` and `Γ(ℱ, W.ι ''ᵁ V)` are the same type, and `Γ(𝒪_W, V)` and
`Γ(𝒪_X, W.ι ''ᵁ V)` are the same ring, but the module structure of the restriction is restriction
of scalars along `AlgebraicGeometry.Scheme.Hom.appIso` of the inclusion, which is the inverse of
an isomorphism and therefore opaque to the elaborator: unification reports
`inv` as a definition it may not unfold.  Mathlib provides
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply` for this, and `smul_restrict_eq`
is that lemma in the form the computation below rewrites with.  The same crossing appears for the
wedge factor, where the morphism level is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomApp` and the bridge is
`restrictSections_image`.

**Where the two expensive unifications were moved to.**  A statement that mentions both
`Γ(ℱ|_W, V)` and `Γ(ℱ, W.ι ''ᵁ V)` is not type-correct at reducible transparency, so a `rw`
performed after such a term appears in the goal fails; every rewrite below is therefore
instantiated in advance and applied in a single `simp only` traversal.  And the hypothesis of
`map_comp_supportedFractionSource_comm_of_smul` is stated with the two factors applied in
succession rather than as a composite, because converting between the two — a `rfl` — costs the
kernel its whole budget at the chart's concrete types and nothing at the abstract ones.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom sectionsHom)
open Stacks.Perfect.AbelianCechCokernelPassage (supportCohomologyForgetAbMap
  map_cokernelLastDifToSupport_abelian_square)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Perfect.SupportedEndoForgetDegreewise
open Stacks.Perfect.GysinAbelianSquare (supportCohomologySheafAbelianMap)
open Stacks.Perfect.ExtendedAlternatingCech (prodTerm)
open Stacks.Perfect.SupportedFraction (supportedFractionSource fractionHom lastDif
  cokernelLastDifToSupport supportedFractionClass cokernelπ_comp_supportedFractionClass)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The class map of Stacks 0G7Q through the top Čech term -/

/-- The class map of [Stacks, Tag 0G7Q] read on the coefficient module factors through the top
term of the extended alternating Čech complex: it is the fraction, the canonical epimorphism onto
the cokernel of the last Čech differential, and the comparison of [Stacks, Tag 0G7L]. -/
theorem supportedFractionSource_eq_fractionHom_comp {Y : Scheme.{u}} {d : ℕ}
    (e : Fin (d + 1) → Γ(Y, ⊤)) (F : Y.Modules) [F.IsQuasicoherent] {T : Set Y}
    (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T) :
    supportedFractionSource e F hT hTe =
      fractionHom e F d ≫ cokernel.π (lastDif e F) ≫ cokernelLastDifToSupport e F hT hTe := by
  rw [supportedFractionSource, ← Category.assoc, cokernelπ_comp_supportedFractionClass,
    Category.assoc]

/-! ### The class map of Stacks 0G7Q is natural in a localized-Leibniz morphism -/

/-- **The class map of [Stacks, Tag 0G7Q], read on the coefficient module and in `i_*ℋ ᶜ_T(ℱ)`,
is natural along a morphism of the underlying abelian sheaves that commutes with dividing by the
product of the equations after precomposition with `u`.** -/
theorem supportedFractionSource_comm_of_smul {Y : Scheme.{u}} {d : ℕ}
    (e : Fin (d + 1) → Γ(Y, ⊤)) {E F G : Y.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (u : Scheme.Modules.presheaf E ⟶ Scheme.Modules.presheaf F)
    (w : Scheme.Modules.presheaf E ⟶ Scheme.Modules.presheaf G)
    (h : ∀ (V : Y.Opens) (v : Γ(Y, V)) (y : Γ(E, V)),
      Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (∏ j, e j) * v = 1 →
      sectionsHom ψ V (v • sectionsHom u V y) = v • sectionsHom w V y)
    {T : Set Y} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T) :
    abHom u ≫ (abelianSheaf Y).map (supportedFractionSource e F hT hTe) ≫
        supportCohomologySheafAbelianMap hT (d + 1) (abHom ψ) =
      abHom w ≫ (abelianSheaf Y).map (supportedFractionSource e G hT hTe) := by
  have hfrac : abHom u ≫ (abelianSheaf Y).map (fractionHom e F d) ≫
        Stacks.Perfect.AbelianFraction.prodTermAb e ψ d =
      abHom w ≫ (abelianSheaf Y).map (fractionHom e G d) := by
    have hpre := Stacks.Perfect.GysinFractionDeRham.fracTerm_comm_prodTermPre_of_smul e ψ u w h
    rw [Stacks.Perfect.GysinFractionDeRham.fracTerm_eq_fractionHom,
      Stacks.Perfect.GysinFractionDeRham.fracTerm_eq_fractionHom] at hpre
    exact congrArg (abHom (F := E) (G := prodTerm e G d)) hpre
  have hact : supportCohomologySheafAbelianMap hT (d + 1) (abHom ψ) =
      supportCohomologyForgetAbMap hT ((d + 1 : ℕ) : ℤ) ψ :=
    supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap hT (d + 1) ψ
  rw [supportedFractionSource_eq_fractionHom_comp, supportedFractionSource_eq_fractionHom_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [hact, map_cokernelLastDifToSupport_abelian_square e hT hTe ψ,
    reassoc_of% (Stacks.Perfect.AbelianFraction.map_cokernelπ_comp_cokernelLastDifAb e ψ),
    reassoc_of% hfrac]

/-- Reading a composite of morphisms of abelian presheaves as a morphism of abelian sheaves
composes the two readings. -/
private theorem abHom_comp {Y : Scheme.{u}} {M N P : Y.Modules}
    (α : Scheme.Modules.presheaf M ⟶ Scheme.Modules.presheaf N)
    (β : Scheme.Modules.presheaf N ⟶ Scheme.Modules.presheaf P) :
    abHom (α ≫ β) = abHom α ≫ abHom β := rfl

/-- **`supportedFractionSource_comm_of_smul` with the first factor an `𝒪_Y`-linear morphism**, in
which shape the two composites are the two sides of
`Stacks.Gysin.ChartFractionCommutesWithDeRham`: the wedge factor of the Gysin formula is
`𝒪_X`-linear, and only the differential is not. -/
theorem map_comp_supportedFractionSource_comm_of_smul {Y : Scheme.{u}} {d : ℕ}
    (e : Fin (d + 1) → Γ(Y, ⊤)) {E F G : Y.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (uu : E ⟶ F)
    (h : ∀ (V : Y.Opens) (v : Γ(Y, V)) (y : Γ(E, V)),
      Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (∏ j, e j) * v = 1 →
      sectionsHom ψ V (v • sectionsHom (Scheme.Modules.Hom.mapPresheaf uu) V y) =
        v • sectionsHom ψ V (sectionsHom (Scheme.Modules.Hom.mapPresheaf uu) V y))
    {T : Set Y} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T) :
    (abelianSheaf Y).map uu ≫ (abelianSheaf Y).map (supportedFractionSource e F hT hTe) ≫
        supportCohomologySheafAbelianMap hT (d + 1) (abHom ψ) =
      (abelianSheaf Y).map uu ≫ abHom ψ ≫
        (abelianSheaf Y).map (supportedFractionSource e G hT hTe) := by
  have hgen := supportedFractionSource_comm_of_smul e ψ (Scheme.Modules.Hom.mapPresheaf uu)
    (Scheme.Modules.Hom.mapPresheaf uu ≫ ψ) (fun V v y hv => h V v y hv) hT hTe
  rw [abHom_comp, ← Stacks.Perfect.AbelianFraction.abelianSheaf_map uu, Category.assoc] at hgen
  exact hgen

/-! ### The localized Leibniz rule on a chart -/

variable {X S : Scheme.{u}}

/-- The canonical identification of two terms of the de Rham complex of equal degree undoes the
reindexing of a multiple of a form. -/
private theorem xIsoOfEq_smul_reindexForm (π : X ⟶ S) {m n : ℕ} (h : m = n) (U : X.Opensᵒᵖ)
    (r : X.toRingedSpace.sheaf.obj.obj U)
    (z : ((deRhamAlgebras π).exteriorPower m).val.obj U) :
    ((deRhamComplex π).XIsoOfEq h.symm).hom.val.app U
        (r • AlgebraicGeometry.SheafOfModules.reindexForm (deRhamAlgebras π) h U z)
      = r • z := by
  subst h
  rw [HomologicalComplex.XIsoOfEq_rfl]
  rfl

/-- **The localized Leibniz rule on a chart**: over an open `V ≤ W` on which the product of the
chart's equations is invertible, dividing by that product commutes with the de Rham differential
on the image of the equation wedge. -/
theorem ambientDeRhamShift_smul_gysinWedgeOn (π : X ⟶ S) {W : X.Opens} {c : ℕ}
    (g : Fin c → Γ(X, W)) (p : ℕ) {V : X.Opens} (hV : V ≤ W) (v : Γ(X, V))
    (hv : (∏ j, X.presheaf.map (homOfLE hV).op (g j)) * v = 1)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    ambientDeRhamShift π c p V (v • gysinWedgeOn π g (p : ℤ) hV ω) =
      v • gysinWedgeOn π g ((p + 1 : ℕ) : ℤ) hV
        (((deRhamComplex π).d p (p + 1)).val.app (op V) ω) := by
  refine Eq.trans (congrArg
    (((deRhamComplex π).XIsoOfEq (show p + c + 1 = p + 1 + c by omega)).hom.val.app (op V))
    (AlgebraicGeometry.SheafOfModules.d_smul_formProduct_prodDegOne_of_mul_eq_one
      (deRhamAlgebras π)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras π)) p c (op V)
      (fun j => X.presheaf.map (homOfLE hV).op (g j)) v hv ω)) ?_
  exact xIsoOfEq_smul_reindexForm π (show p + 1 + c = p + c + 1 by omega) (op V) v _

/-- **The localized Leibniz rule on a chart, in the shape the class-map half consumes**: dividing
by an invertible restriction of the product of the chart's equations commutes with the de Rham
differential of `X/S` on the image of the equation wedge. -/
theorem ambientDeRhamShift_smul_gysinWedgeOn_comm (π : X ⟶ S) {W : X.Opens} {c : ℕ}
    (g : Fin c → Γ(X, W)) (p : ℕ) {V : X.Opens} (hV : V ≤ W) (v : Γ(X, V))
    (hv : (∏ j, X.presheaf.map (homOfLE hV).op (g j)) * v = 1)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    ambientDeRhamShift π c p V (v • gysinWedgeOn π g (p : ℤ) hV ω) =
      v • ambientDeRhamShift π c p V (gysinWedgeOn π g (p : ℤ) hV ω) := by
  rw [ambientDeRhamShift_smul_gysinWedgeOn π g p hV v hv ω, ambientDeRhamShift_gysinWedgeOn]

/-! ### Reading the two factors on the sections over an open of the chart -/

/-- The action on sections of a composite of morphisms of abelian presheaves. -/
private theorem sectionsHom_comp {Y : Scheme.{u}} {M N P : Y.Modules}
    (α : Scheme.Modules.presheaf M ⟶ Scheme.Modules.presheaf N)
    (β : Scheme.Modules.presheaf N ⟶ Scheme.Modules.presheaf P) (V : Y.Opens) (x : Γ(M, V)) :
    sectionsHom (α ≫ β) V x = sectionsHom β V (sectionsHom α V x) := rfl

/-- The action on the sections over an open `V` of the chart of the underlying abelian-presheaf
morphism of a morphism of restrictions is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomApp`, which is written on the sections over
`W.ι ''ᵁ V` in the ambient scheme's spelling. -/
private theorem sectionsHom_mapPresheaf_restrict {M N : X.Modules} (W : X.Opens)
    (φ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (V : W.toScheme.Opens) (m : Γ(M, W.ι ''ᵁ V)) :
    sectionsHom (Scheme.Modules.Hom.mapPresheaf φ) V m = restrictHomApp φ V m :=
  (restrictHomApp_apply φ V m).symm

/-- **The equation wedge of a chart, read on the sections over an open of the chart.** -/
theorem sectionsHom_mapPresheaf_gysinWedgeOnHom (π : X ⟶ S) {W : X.Opens} {c : ℕ}
    (g : Fin c → Γ(X, W)) (q : ℤ) (V : W.toScheme.Opens)
    (y : Γ(Scheme.Modules.restrict (relativeDifferentialForms π q) W.ι, V)) :
    sectionsHom (Scheme.Modules.Hom.mapPresheaf (gysinWedgeOnHom π g q)) V y =
      gysinWedgeOn π g q (Scheme.Opens.ι_image_le W V) y :=
  (sectionsHom_mapPresheaf_restrict W (gysinWedgeOnHom π g q) V y).trans
    ((restrictSections_image (gysinWedgeOnHom π g q) V
          (Scheme.Opens.ι_image_le W V) y).symm.trans
      (restrictSections_gysinWedgeOnHom π g q (W.ι ''ᵁ V) (Scheme.Opens.ι_image_le W V) y))

/-- Mathlib's comparison of the sections of a restriction with the sections over the image open
is the identity, so it acts trivially on a section. -/
private theorem restrictAppIso_hom_apply (W : X.Opens) (M : X.Modules) (V : W.toScheme.Opens)
    (z : Γ(Scheme.Modules.restrict M W.ι, V)) :
    (Scheme.Modules.restrictAppIso W.ι M V).hom z = z := rfl

/-- The comparison of the structure sheaves along an open immersion of an open subscheme acts
trivially on a function, `AlgebraicGeometry.Scheme.Opens.ι_appIso` saying that it is the
identity. -/
private theorem ι_appIso_inv_apply (W : X.Opens) (V : W.toScheme.Opens) (v : Γ(W.toScheme, V)) :
    (W.ι.appIso V).inv v = v := by
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- **The scalar action of a chart on the sections of a restriction is the ambient one.**  The
two module structures are *not* definitionally equal — the chart's goes through
`AlgebraicGeometry.Scheme.Hom.appIso` of the inclusion, which is an inverse of an isomorphism and
so opaque — and this is
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply`, which relates them. -/
private theorem smul_restrict_eq (W : X.Opens) (M : X.Modules) (V : W.toScheme.Opens)
    (v : Γ(W.toScheme, V)) (z : Γ(Scheme.Modules.restrict M W.ι, V)) :
    (v • z : Γ(Scheme.Modules.restrict M W.ι, V)) =
      (W.ι.appIso V).inv v • (Scheme.Modules.restrictAppIso W.ι M V).hom z :=
  Scheme.Modules.smul_restrictAppIso_hom_apply W.ι M V v z

/-- **The relative de Rham differential of `X/S` restricted to a chart, as a morphism of the
underlying abelian presheaves of the restrictions.**  It is
`Stacks.Gysin.restrictAbHom` of `Stacks.Gysin.ambientDeRhamShiftAbHom`, named so that the one
crossing between the `Stacks.Gysin.abelianRestrict` spelling of the source and the
`AlgebraicGeometry.Scheme.Modules.restrict` spelling happens once, here. -/
def chartDeRhamShiftPresheafHom (π : X ⟶ S) (W : X.Opens) (c p : ℕ) :
    Scheme.Modules.presheaf
        (Scheme.Modules.restrict (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) W.ι) ⟶
      Scheme.Modules.presheaf
        (Scheme.Modules.restrict
          (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ))) W.ι) :=
  (restrictAbHom W (ambientDeRhamShiftAbHom π c p)).hom

/-- The restricted differential, as a morphism of abelian sheaves on the chart, is the restriction
of the differential. -/
theorem abHom_chartDeRhamShiftPresheafHom (π : X ⟶ S) (W : X.Opens) (c p : ℕ) :
    abHom (chartDeRhamShiftPresheafHom π W c p) =
      restrictAbHom W (ambientDeRhamShiftAbHom π c p) := rfl

/-- **The restricted differential, read on the sections over an open of the chart**: it is the
ambient differential over the image of that open. -/
theorem sectionsHom_chartDeRhamShiftPresheafHom (π : X ⟶ S) (W : X.Opens) (c p : ℕ)
    (V : W.toScheme.Opens)
    (z : Γ(Scheme.Modules.restrict
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) W.ι, V)) :
    sectionsHom (chartDeRhamShiftPresheafHom π W c p) V z =
      ambientDeRhamShift π c p (W.ι ''ᵁ V) z := rfl

/-- **The product of a chart's equations, read on the chart and restricted to an open of it, is
the product of the restrictions of the equations.** -/
theorem map_prod_restrictEquations (W : X.Opens) {c : ℕ} (g : Fin c → Γ(X, W))
    (V : W.toScheme.Opens) :
    W.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (∏ j, restrictEquations W g j) =
      ∏ j, X.presheaf.map (homOfLE (Scheme.Opens.ι_image_le W V)).op (g j) := by
  rw [map_prod (W.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom
    (restrictEquations W g) Finset.univ]
  exact Finset.prod_congr rfl fun j _ =>
    (presheaf_map_comp_apply _ _ (g j)).trans (presheaf_map_congr _ _ (g j))

/-- **The localized Leibniz rule of a chart, entirely in the chart's spelling.**  This is the
hypothesis `Stacks.Gysin.supportedFractionSource_comm_of_smul` asks for, at the equation wedge of
the chart and the restriction to the chart of the relative de Rham differential of `X/S`. -/
theorem sectionsHom_chartDeRhamShift_smul_gysinWedge (π : X ⟶ S) {W : X.Opens} {c : ℕ}
    (g : Fin c → Γ(X, W)) (p : ℕ) (V : W.toScheme.Opens) (v : Γ(W.toScheme, V))
    (y : Γ(Scheme.Modules.restrict (relativeDifferentialForms π (p : ℤ)) W.ι, V))
    (hv : W.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (∏ j, restrictEquations W g j) * v = 1) :
    sectionsHom (chartDeRhamShiftPresheafHom π W c p) V
        (v • sectionsHom (Scheme.Modules.Hom.mapPresheaf (gysinWedgeOnHom π g (p : ℤ))) V y) =
      v • sectionsHom (chartDeRhamShiftPresheafHom π W c p) V
        (sectionsHom (Scheme.Modules.Hom.mapPresheaf (gysinWedgeOnHom π g (p : ℤ))) V y) := by
  rw [map_prod_restrictEquations] at hv
  have hv' : (∏ j, X.presheaf.map (homOfLE (Scheme.Opens.ι_image_le W V)).op (g j)) *
      (W.ι.appIso V).inv v = 1 := by
    rw [ι_appIso_inv_apply]
    exact hv
  have hkey := ambientDeRhamShift_smul_gysinWedgeOn_comm π g p
    (Scheme.Opens.ι_image_le W V) ((W.ι.appIso V).inv v) hv' y
  rw [← sectionsHom_mapPresheaf_gysinWedgeOnHom π g (p : ℤ) V y] at hkey
  simp only [smul_restrict_eq, restrictAppIso_hom_apply,
    sectionsHom_chartDeRhamShiftPresheafHom]
  exact hkey

/-! ### The class-map half of Stacks 0G87 -/

/-- **The class-map half of the one hypothesis of [Stacks, Tag 0G87] holds.** -/
theorem chartFractionCommutesWithDeRham {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {d : ℕ} (p : ℕ) (W : X.Opens) (g : Fin (d + 1) → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet (restrictEquations W g) ⊆ W.ι ⁻¹' Set.range i.base) :
    ChartFractionCommutesWithDeRham i π p W g hTW hTf := by
  have : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  have : (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π (p + 1) (d + 1)
  exact map_comp_supportedFractionSource_comm_of_smul (restrictEquations W g)
    (chartDeRhamShiftPresheafHom π W (d + 1) p) (gysinWedgeOnHom π g (p : ℤ))
    (fun V v y hv => sectionsHom_chartDeRhamShift_smul_gysinWedge π g p V v y hv) hTW hTf

/-! ### The one hypothesis of Stacks 0G87 that remains -/

section Assemble

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
  (Chart : Type u) (ambient : Chart → X.Opens)
  (equations : (a : Chart) → Fin (d + 1) → Γ(X, ambient a))
  (hvanish : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a) (j : Fin (d + 1)),
    (i.app V).hom (X.presheaf.map (homOfLE hV).op (equations a j)) = 0)
  (hcover : ∀ x : X, ∃ a, x ∈ ambient a)
  (hgen : ∀ a, IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) (ambient a) (equations a))

/-- **The class-map half of every chart of the chart data of [Stacks, Tag 0G86].** -/
theorem chartFractionCommutesWithDeRham_charts (a : Chart) :
    ChartFractionCommutesWithDeRham i π p (ambient a) (equations a)
      (isClosed_preimage_range_base i (ambient a))
      (equationsClosedSet_restrictEquations i (ambient a)
        (isCutOutByEquationsOn_of_isGeneratedByOn i (hgen a) (hvanish a))).le :=
  chartFractionCommutesWithDeRham i π p (ambient a) (equations a) _ _

/-- **`Stacks.Gysin.ClsCommutesWithDeRham` at the chart data of [Stacks, Tag 0G86] follows from
the excision half alone.**  The class-map half is discharged by
`Stacks.Gysin.chartFractionCommutesWithDeRham`, so
`Stacks.Gysin.clsCommutesWithDeRham_of_excision_of_chartFraction` loses its second
hypothesis. -/
theorem clsCommutesWithDeRham_of_excision
    (hexc : ∀ a, SupportCohomologyRestrictAbNatural (ambient a) (isClosed_range_base i)
      (isClosed_preimage_range_base i (ambient a)) (d + 1)
      (ambientDeRhamShiftAbHom π (d + 1) p)) :
    ClsCommutesWithDeRham
      (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover hgen)
      (chartGysinTargetDeRhamHom i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinMatch i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinMatch_ambient i π p Chart ambient equations hvanish hcover hgen) :=
  clsCommutesWithDeRham_of_excision_of_chartFraction i π p Chart ambient equations hvanish
    hcover hgen hexc
    (chartFractionCommutesWithDeRham_charts i π p Chart ambient equations hvanish hgen)

/-- **The square of [Stacks, Tag 0G87] for the glued Gysin map of [Stacks, Tag 0G86], under the
excision half alone.**  This is
`Stacks.Gysin.gysinHom_comm_deRham_of_excision_of_chartFraction` with its class-map hypothesis
discharged; the abelian reading of the derived excision of [Stacks, Tag 0G78] is the one
hypothesis that remains here, and no `@[stacks 0G87]` attribute is attached, this being an
implication.  That hypothesis is supplied, and the tag registered, in
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRank.lean`. -/
theorem gysinHom_comm_deRham_of_excision
    (hexc : ∀ a, SupportCohomologyRestrictAbNatural (ambient a) (isClosed_range_base i)
      (isClosed_preimage_range_base i (ambient a)) (d + 1)
      (ambientDeRhamShiftAbHom π (d + 1) p))
    (V : X.Opens) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    abSectionsHom
        (chartGysinTargetDeRhamHom i π p Chart ambient equations hvanish hcover hgen)
        V ((chartGysinChartData i π p Chart ambient equations hvanish hcover
          hgen).gysinHom.app V x)
      = (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover
          hgen).gysinHom.app V (pushforwardDeRham i π p V x) :=
  gysinHom_comm_deRham_of_excision_of_chartFraction i π p Chart ambient equations hvanish
    hcover hgen hexc
    (chartFractionCommutesWithDeRham_charts i π p Chart ambient equations hvanish hgen) V x

end Assemble

end Stacks.Gysin

end
