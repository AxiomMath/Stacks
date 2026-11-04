module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDifferentialSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.LocalizedLeibniz
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechDerivedSquare

/-!
# The relative de Rham differential as a morphism of abelian sheaves, and the squares of 0G85

Let `π : X ⟶ S` be a morphism of schemes.  The relative de Rham differential
`d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}` is only `π⁻¹𝒪_S`-linear, so in this library it is a morphism in
`SheafOfModules (underlyingRingSheaf (π⁻¹𝒪_S))` and **not** a morphism of `X.Modules`.  Every
construction that [Stacks, Tag 0G85] needs to apply to it — the abelian extended alternating Čech
complex of `Stacks.Perfect.AbelianFraction.cplxAb`, the abelian Čech cokernel
`Stacks.Perfect.AbelianFraction.cokernelLastDifAb`, the abelian derived square
`Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare`, and the abelian action
`Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap` of `i_*ℋ ᶜ_Z` on the target of the Gysin
map — takes as input a morphism of the **underlying abelian (pre)sheaves** of two objects of
`X.Modules`.  No declaration in the library produced such a morphism out of a de Rham differential,
so none of those constructions could be applied to `d` at all.

This file supplies that passage and uses it.  Restriction of scalars along `π⁻¹𝒪_S ⟶ 𝒪_X` does not
change the underlying presheaf of abelian groups —
`PresheafOfModules.restrictScalarsCompToPresheaf` is `Iso.refl` — so the de Rham differential,
which is a morphism between two sheaves of `π⁻¹𝒪_S`-modules whose underlying abelian presheaves
are those of `Ω^p_{X/S}` and `Ω^{p+1}_{X/S}`, *is* a morphism of the underlying abelian presheaves
of those two `𝒪_X`-modules.  Nothing is forgotten and no comparison map is involved: the two
presheaves are equal by `rfl`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamDifferentialPresheafHom`: **the relative de Rham differential
  as a morphism `Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}` of the underlying abelian presheaves on `X`.**
* `AlgebraicGeometry.Scheme.Hom.deRhamDifferentialAbHom`: the same in the abelian-sheaf spelling of
  `Stacks.Perfect.AbelianFraction.abelianSheaf`.
* `AlgebraicGeometry.Scheme.Hom.deRhamReindexPresheafHom`: the canonical identification of two
  terms of the de Rham complex of equal degree, in the same spelling; it carries the degree
  bookkeeping of the graded Leibniz rule.
* `AlgebraicGeometry.Scheme.Hom.cechCokernelDeRhamMap`: the action of the Čech cokernel of
  [Stacks, Tag 0G7Q] on the de Rham differential.
* `AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap`: **the action of `i_*ℋ ᶜ_Z` on the de Rham
  differential, at the target of the Gysin map of [Stacks, Tag 0G83]** — the right-hand vertical
  arrow of the comparison square of [Stacks, Tag 0G85].
* `AlgebraicGeometry.Scheme.Hom.GysinFormulaCommutesWithDeRham`: **the comparison square of
  [Stacks, Tag 0G85] for the Gysin formula**, as a proposition.  Nothing here proves it; it is
  proved by `Stacks.Perfect.SupportedEndoForgetDegreewise.gysinFormulaCommutesWithDeRham`, by a
  different route from the one the implementation notes below describe.
* `AlgebraicGeometry.Scheme.Hom.FormFractionClassCommutesWithDeRham`: **the same square for the
  fraction class alone**, which is steps (i) and (ii) of the source's proof in the spelling the
  Gysin map uses.  Also a statement and not a theorem.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamDifferentialPresheafHom_app`: on local sections the morphism
  of abelian presheaves is the de Rham differential, by `rfl`.
* `AlgebraicGeometry.Scheme.Hom.deRhamDifferentialPresheafHom_app_gysinWedgeHom` and
  `AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_comm_deRhamDifferentialPresheafHom`: **the wedge
  factor of the Gysin formula commutes with the de Rham differential, in the abelian vocabulary** —
  on local sections and as a square of morphisms of abelian presheaves on `X`.  This is
  `AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_comm_d`, which is step (iii) of the proof of
  [Stacks, Tag 0G85], with `d` read as the morphism of abelian presheaves built here.
* `AlgebraicGeometry.Scheme.Hom.gysinFormulaCommutesWithDeRham_of_formFractionClass`: **the square
  of [Stacks, Tag 0G85] for the Gysin formula follows from the square for the fraction class** —
  step (iii) is discharged, so what remains of [Stacks, Tag 0G85] on the Gysin formula is exactly
  `FormFractionClassCommutesWithDeRham`.  This is a reduction, not a proof: the hypothesis is the
  missing content.
* `AlgebraicGeometry.Scheme.Hom.map_cokernelπ_comp_cechCokernelDeRhamMap`: the defining property of
  the action on the Čech cokernel.
* `AlgebraicGeometry.Scheme.Hom.abelianCechDerivedSquare_deRhamDifferential`: **step (ii) of the
  proof of [Stacks, Tag 0G85] at the de Rham differential** — the comparison of [Stacks, Tag 0G7L],
  after forgetting the module structure and composed with the comparison of [Stacks, Tag 0G74]
  part (2), is natural along `d`.  This is
  `Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare` instantiated at the de Rham
  differential, which the library could not do before.

## Implementation notes

**Carried hypotheses.**  Nothing in the first section carries any hypothesis beyond the standing
size conditions: the de Rham differential exists for every morphism of schemes and every degree,
and the identification of the underlying abelian presheaves is by `rfl`.
`abelianCechDerivedSquare_deRhamDifferential` carries exactly the hypotheses of
`Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare`, namely `hT : IsClosed T` and
`hTe : equationsClosedSet e ⊆ T`, together with quasi-coherence of the two coefficient modules —
which is *not* a hypothesis here but a theorem,
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms`, declared as a local
instance for the purpose.  `cechCokernelDeRhamMap` and `gysinTargetDeRhamMap` carry a nonempty
family of equations, written `Fin (c + 1)`, as everywhere in this development; the latter also
specialises the closed subset to the common zero locus of the equations, which is a specialisation
and not a hypothesis.

**Why `Fin (c+1)` and the degree `p + (c + 1)`.**  The Gysin map of [Stacks, Tag 0G83] raises the
exterior degree by the number `c + 1` of equations, so the right-hand vertical arrow of the square
is the de Rham differential in degree `p + (c + 1)`; the integer degree
`((p + (c + 1) : ℕ) : ℤ)` of this file and the degree `(p : ℤ) + ((c + 1 : ℕ) : ℤ)` in which
`AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology` reads the target of the Gysin map are the
same term up to unfolding `Int.add`, so no transport appears.

**What is NOT proved here, and what [Stacks, Tag 0G85] still needs.**  The three steps of the
source's proof are present in the library — step (i) is [Stacks, Tag 0G74] part (2), available as
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexForgetIso` and, at the Gysin
map's target, as `Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso`; step (ii)
is `Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare`, instantiated at `d` below;
step (iii) is `AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_comm_d`, restated below — and the
localized Leibniz rule
`AlgebraicGeometry.Scheme.Hom.d_smul_equationsWedge_basicOpen` supplies the fraction-level identity
`d(α/g) = d(α)/g`.  Step (iii) is discharged below and the whole square for the Gysin formula is
reduced to `FormFractionClassCommutesWithDeRham` by
`gysinFormulaCommutesWithDeRham_of_formFractionClass`; steps (i) and (ii) are nevertheless **not
composable as they stand**, so `FormFractionClassCommutesWithDeRham` is left unproved here.
`GysinFormulaCommutesWithDeRham` is *not* left unproved: it is proved by
`Stacks.Perfect.SupportedEndoForgetDegreewise.gysinFormulaCommutesWithDeRham`, which goes through
`Stacks.Perfect.GysinFractionDeRham.gysinFormulaCommutesWithDeRham_of_topCechClassNatural` and so
avoids `FormFractionClassCommutesWithDeRham` altogether.  Four distinct declarations are missing
for the route through the fraction class, each of them a comparison between two spellings that the
project has never related; the first three are what the proof of
`FormFractionClassCommutesWithDeRham` needs, and the fourth is what passing from the Gysin formula
to the Gysin map needs:

1. **The derived square of step (ii) read on the degree-`c` cohomology sheaves.**
   `abelianCechDerivedSquare` is an identity in the derived category of abelian sheaves on `X`.
   What the square of [Stacks, Tag 0G85] needs is its image under the degree-`c` cohomology sheaf
   functor, identified with `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap` on
   the right and with `Stacks.Perfect.AbelianFraction.cokernelLastDifAb` on the left.  No
   declaration applies any cohomology functor of the derived category of abelian sheaves to
   `cechToDerivedSupport` or to `Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison`;
   `Stacks.Perfect.SupportedFraction.cechHomologyToSupport` is the module-level analogue and has no
   abelian counterpart.  Equivalently: the abelian case of
   `Stacks.Perfect.GysinAbelianSquare.cokernelLastDifToSupport_abelian_square_mapPresheaf`, which
   is proved there only for a morphism of `X.Modules`.
2. **The identification of the two constructions of the class map of [Stacks, Tag 0G7Q]** — this
   one is available.  The Gysin map is built from
   `Stacks.Perfect.FractionClass.pushforwardFractionClass`, which factors through
   `Stacks.Perfect.CechLocalCohomology.pushforwardLocalCohomologyIso` and the complex
   `AlgebraicGeometry.ExtendedAlternatingCech.data`; the abelian derived square speaks about
   `Stacks.Perfect.SupportedFraction.cechToDerivedSupport` and the complex
   `Stacks.Perfect.ExtendedAlternatingCech.cplx`.  The two comparisons *are* related, by
   `Stacks.Perfect.CechSupportTransport.cokernelLastDifToPushforward_eq`, and the two
   multiplication-by-a-global-function morphisms
   (`Stacks.Perfect.FractionClass.globalSmul` and `Stacks.Perfect.SupportedFraction.globalSmul`)
   are the same morphism, by `Stacks.Perfect.smulHom_eq_globalSmul`.  Assembled, these give
   `Stacks.Perfect.supportedFractionSource_comp_supportCohomologyToPushforward`, which identifies
   the two class maps.
3. **The compatibility of the fraction `s/(f₁ ⋯ f_c)` with `d`.**
   `Stacks.Perfect.FractionClass.fracTerm` is *not* natural in a merely additive morphism, which is
   why the localized Leibniz rule is needed; but that rule is an identity between local sections of
   `Ω^•_{X/S}`, and carrying it to `fracTerm` needs the sectionwise description of
   `Stacks.Perfect.FractionClass.divFactor`, i.e. that on an open where the product of the
   equations is invertible the inverse of `Stacks.Perfect.FractionClass.smulHom (∏ f)` acts on
   sections as multiplication by the inverse section.  That description is not in the library.
4. **Restriction of `p`-forms to `Z` as a morphism of abelian sheaves, and its commutation with the
   de Rham differentials.**  This is the left-hand vertical arrow of the square for the Gysin *map*
   rather than for the Gysin *formula*, which is why only the latter is stated here.  The
   sectionwise input is
   `AlgebraicGeometry.Scheme.Hom.deRhamComplex_d_relativeDifferentialFormsMap` of
   `StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapCommutesWithDifferential`, and
   `StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapDeRham` packages it into the composite
   `AlgebraicGeometry.Scheme.Hom.formRestriction`, supplies the direct image along `i` of the de
   Rham differential of `Z` as a morphism of abelian sheaves on `X`, and so states **and proves**
   the square for `AlgebraicGeometry.Scheme.Hom.gysinMap` itself, which is where the
   `@[stacks 0G85]` attribute lives.  Only the square for
   `AlgebraicGeometry.Scheme.Hom.gysinFormulaHom`, which is what `GysinFormulaCommutesWithDeRham`
   states, is stated here.

**No declaration here carries a `@[stacks ...]` attribute.**  Nothing here proves
[Stacks, Tag 0G85] or any part of it that is not already recorded elsewhere: the passage from `d`
to a morphism of abelian presheaves is library bookkeeping with no counterpart in the source, the
instantiations are instances of statements whose tags are recorded on them, and
`GysinFormulaCommutesWithDeRham` is a proposition that nothing here proves.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G84](https://stacks.math.columbia.edu/tag/0G84)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G74](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] isQuasicoherent_relativeDifferentialForms

variable {X S : Scheme.{u}}

/-! ### The de Rham differential as a morphism of the underlying abelian sheaves -/

/-- **The relative de Rham differential `d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}` as a morphism of the
underlying presheaves of abelian groups on `X`.**

The differential obeys `d(g ω) = d g ∧ ω + g · d ω`, so it is only `π⁻¹𝒪_S`-linear and is a
morphism of `X.Modules` for no scheme `X`; it is a morphism of sheaves of `π⁻¹𝒪_S`-modules, which
is the category the terms of `AlgebraicGeometry.Scheme.Hom.deRhamComplex` live in.  Restriction of
scalars leaves the underlying presheaf of abelian groups unchanged — on the nose, by
`PresheafOfModules.restrictScalarsCompToPresheaf`, which is `Iso.refl` — so forgetting the
`π⁻¹𝒪_S`-module structure of the differential gives a morphism of the underlying abelian presheaves
of the `𝒪_X`-modules `Ω^p_{X/S}` and `Ω^{p+1}_{X/S}`.

This is the input every abelian construction of the proof of [Stacks, Tag 0G85] asks for, and the
reason the library could not previously apply any of them to a de Rham differential. -/
public def deRhamDifferentialPresheafHom (π : X ⟶ S) (p : ℕ) :
    Scheme.Modules.presheaf (relativeDifferentialForms π (p : ℤ)) ⟶
      Scheme.Modules.presheaf (relativeDifferentialForms π ((p + 1 : ℕ) : ℤ)) :=
  (PresheafOfModules.toPresheaf _).map
    (X := ((deRhamComplex π).X p).val) (Y := ((deRhamComplex π).X (p + 1)).val)
    ((deRhamComplex π).d p (p + 1)).val

/-- On a local `p`-form, the morphism of abelian presheaves of
`AlgebraicGeometry.Scheme.Hom.deRhamDifferentialPresheafHom` is the de Rham differential. -/
public theorem deRhamDifferentialPresheafHom_app (π : X ⟶ S) (p : ℕ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), U)) :
    (deRhamDifferentialPresheafHom π p).app (op U) ω =
      ((deRhamComplex π).d p (p + 1)).val.app (op U) ω := rfl

/-- **The relative de Rham differential as a morphism of the underlying abelian sheaves on `X`**,
in the spelling `Stacks.Perfect.AbelianFraction.abelianSheaf` of the forgetful functor that
`Stacks.Perfect.GysinAbelianSquare` and `Stacks.Perfect.AbelianFraction` are stated in. -/
public def deRhamDifferentialAbHom (π : X ⟶ S) (p : ℕ) :
    (abelianSheaf X).obj (relativeDifferentialForms π (p : ℤ)) ⟶
      (abelianSheaf X).obj (relativeDifferentialForms π ((p + 1 : ℕ) : ℤ)) :=
  abHom (deRhamDifferentialPresheafHom π p)

/-- The underlying morphism of abelian presheaves of
`AlgebraicGeometry.Scheme.Hom.deRhamDifferentialAbHom` is
`AlgebraicGeometry.Scheme.Hom.deRhamDifferentialPresheafHom`. -/
public theorem deRhamDifferentialAbHom_hom (π : X ⟶ S) (p : ℕ) :
    (deRhamDifferentialAbHom π p).hom = deRhamDifferentialPresheafHom π p := rfl

/-! ### Step (iii) of Stacks 0G85 in the abelian vocabulary -/

/-- **The wedge factor of the Gysin formula commutes with the de Rham differential, with `d` read
as a morphism of abelian presheaves.**  On a local `p`-form `ω` on `X`,

`d(ω ∧ d f₁ ∧ ⋯ ∧ d f_c) = d(ω) ∧ d f₁ ∧ ⋯ ∧ d f_c`,

the two sides compared in degree `p + c + 1` through the identification of that degree with
`p + 1 + c`.  This is `AlgebraicGeometry.Scheme.Hom.d_gysinWedgeHom_app`, which is step (iii) of
the proof of [Stacks, Tag 0G85], restated with the differential in the vocabulary in which the
abelian constructions of that proof act on it. -/
public theorem deRhamDifferentialPresheafHom_app_gysinWedgeHom (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (p : ℕ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), U)) :
    (deRhamDifferentialPresheafHom π (p + c)).app (op U)
          ((gysinWedgeHom π f (p : ℤ)).val.app (op U) ω) =
      ((deRhamComplex π).XIsoOfEq (show p + 1 + c = p + c + 1 by omega)).hom.val.app (op U)
        ((gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)).val.app (op U)
          ((deRhamDifferentialPresheafHom π p).app (op U) ω)) :=
  d_gysinWedgeHom_app π f p (op U) ω

/-- The canonical identification of two terms of the de Rham complex of equal degree, read as an
isomorphism of the underlying abelian presheaves on `X`.  It is `HomologicalComplex.XIsoOfEq`
forgotten exactly as `AlgebraicGeometry.Scheme.Hom.deRhamDifferentialPresheafHom` forgets the
differential, and it carries the degree bookkeeping of the graded Leibniz rule — the wedge factor
raises the degree of `Ω^{p+1}` to `p + 1 + c` while the differential lands in degree
`p + c + 1`. -/
public def deRhamReindexPresheafHom (π : X ⟶ S) {m n : ℕ} (h : m = n) :
    Scheme.Modules.presheaf (relativeDifferentialForms π (m : ℤ)) ⟶
      Scheme.Modules.presheaf (relativeDifferentialForms π (n : ℤ)) :=
  (PresheafOfModules.toPresheaf _).map
    (X := ((deRhamComplex π).X m).val) (Y := ((deRhamComplex π).X n).val)
    ((deRhamComplex π).XIsoOfEq h).hom.val

/-- On local sections the reindexing of
`AlgebraicGeometry.Scheme.Hom.deRhamReindexPresheafHom` is the canonical identification of the two
terms of the de Rham complex. -/
public theorem deRhamReindexPresheafHom_app (π : X ⟶ S) {m n : ℕ} (h : m = n) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms π (m : ℤ), U)) :
    (deRhamReindexPresheafHom π h).app (op U) ω =
      ((deRhamComplex π).XIsoOfEq h).hom.val.app (op U) ω := rfl

/-- **The wedge factor of the Gysin formula commutes with the de Rham differential, as a square of
morphisms of abelian presheaves on `X`.**  This is step (iii) of the proof of
[Stacks, Tag 0G85] in the category the abelian constructions of steps (i) and (ii) live in:

`Ω^p ⟶ Ω^{p+c}`, `Ω^{p+1} ⟶ Ω^{p+1+c}`

with the de Rham differentials as vertical arrows and the wedge with `d f₁ ∧ ⋯ ∧ d f_c` as
horizontal arrows, the right-hand degree read in the spelling `p + c + 1` of the complex through
`AlgebraicGeometry.Scheme.Hom.deRhamReindexPresheafHom`.  It is
`AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_comm_d`, whose two sides are morphisms of sheaves of
`π⁻¹𝒪_S`-modules, with both sides forgotten to the underlying abelian presheaves — where the wedge
factor becomes the underlying morphism of a morphism of `X.Modules` and the differential becomes
`deRhamDifferentialPresheafHom`. -/
public theorem gysinWedgeHom_comm_deRhamDifferentialPresheafHom (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (p : ℕ) :
    Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f (p : ℤ)) ≫
        deRhamDifferentialPresheafHom π (p + c) =
      deRhamDifferentialPresheafHom π p ≫
        Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)) ≫
          deRhamReindexPresheafHom π (show p + 1 + c = p + c + 1 by omega) := by
  refine NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun ω => ?_))
  exact d_gysinWedgeHom_app π f p U ω

/-! ### The Čech cokernel of Stacks 0G7Q acting on the de Rham differential -/

/-- **The action of the Čech cokernel of [Stacks, Tag 0G7Q] on the de Rham differential**: the
morphism `Coker(lastDif f Ω^p_{X/S}) ⟶ Coker(lastDif f Ω^{p+1}_{X/S})` of abelian sheaves on `X`
induced by `d`.  This is the left-hand vertical arrow of the comparison square of step (ii) of the
proof of [Stacks, Tag 0G85], at the de Rham differential;
`Stacks.Perfect.AbelianFraction.cokernelLastDifAb` is the construction, and what is new is that it
can be applied to `d` at all. -/
public def cechCokernelDeRhamMap (π : X ⟶ S) {c : ℕ} (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) :
    (abelianSheaf X).obj (cokernel (Stacks.Perfect.SupportedFraction.lastDif f
        (relativeDifferentialForms π (p : ℤ)))) ⟶
      (abelianSheaf X).obj (cokernel (Stacks.Perfect.SupportedFraction.lastDif f
        (relativeDifferentialForms π ((p + 1 : ℕ) : ℤ)))) :=
  Stacks.Perfect.AbelianFraction.cokernelLastDifAb f (deRhamDifferentialPresheafHom π p)

/-- The defining property of `AlgebraicGeometry.Scheme.Hom.cechCokernelDeRhamMap`: it is compatible
with the canonical epimorphisms onto the two Čech cokernels, the map on the top Čech terms being
the one `d` induces there. -/
public theorem map_cokernelπ_comp_cechCokernelDeRhamMap (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) :
    (abelianSheaf X).map (cokernel.π (Stacks.Perfect.SupportedFraction.lastDif f
          (relativeDifferentialForms π (p : ℤ)))) ≫ cechCokernelDeRhamMap π f p =
      Stacks.Perfect.AbelianFraction.prodTermAb f (deRhamDifferentialPresheafHom π p) c ≫
        (abelianSheaf X).map (cokernel.π (Stacks.Perfect.SupportedFraction.lastDif f
          (relativeDifferentialForms π ((p + 1 : ℕ) : ℤ)))) :=
  Stacks.Perfect.AbelianFraction.map_cokernelπ_comp_cokernelLastDifAb f
    (deRhamDifferentialPresheafHom π p)

/-! ### Step (ii) of Stacks 0G85 at the de Rham differential -/

/-- **Step (ii) of the proof of [Stacks, Tag 0G85], at the de Rham differential.**  The comparison

`𝓕^• ⟶ i_* R𝓗_T(ℱ)`

of [Stacks, Tag 0G7L], after forgetting the module structure and followed by the comparison of
[Stacks, Tag 0G74] part (2) with the direct image folded in, carries the abelian Čech derived map
induced by `d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}` to `i_* R𝓗_T^{ab}` applied to `d` placed in degree `0`.

This is `Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare` instantiated at the de
Rham differential, which was impossible before
`AlgebraicGeometry.Scheme.Hom.deRhamDifferentialPresheafHom`: that square is natural in an
arbitrary morphism of the underlying abelian sheaves of two quasi-coherent coefficient modules, and
`Ω^p_{X/S}` is quasi-coherent in every degree by
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms`.  It carries exactly
`hT : IsClosed T` and `hTe : equationsClosedSet e ⊆ T`. -/
public theorem abelianCechDerivedSquare_deRhamDifferential (π : X ⟶ S) {m : ℕ}
    (e : Fin m → Γ(X, ⊤)) {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T)
    (p : ℕ) :
    (Stacks.Cohomology.UnderlyingAbelianSheaf.underlyingDerivedSheaf
            (structureSheafRing X.toRingedSpace)).map
          (Stacks.Perfect.SupportedFraction.cechToDerivedSupport e
            (relativeDifferentialForms π (p : ℤ)) hT hTe) ≫
        (Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison hT).app
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (relativeDifferentialForms π (p : ℤ))) ≫
        (Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedPushforward
            X.toRingedSpace T hT).map
          (Stacks.Perfect.AbelianCechDerivedSquare.derivedSingleAb
            (deRhamDifferentialPresheafHom π p)) =
      Stacks.Perfect.AbelianCechDerivedSquare.derivedCechAb e
          (deRhamDifferentialPresheafHom π p) ≫
        (Stacks.Cohomology.UnderlyingAbelianSheaf.underlyingDerivedSheaf
            (structureSheafRing X.toRingedSpace)).map
          (Stacks.Perfect.SupportedFraction.cechToDerivedSupport e
            (relativeDifferentialForms π ((p + 1 : ℕ) : ℤ)) hT hTe) ≫
        (Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison hT).app
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (relativeDifferentialForms π ((p + 1 : ℕ) : ℤ))) :=
  Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare e hT hTe
    (deRhamDifferentialPresheafHom π p)

/-! ### The right-hand vertical arrow of the square of Stacks 0G85 -/

/-- **The action of `i_*ℋ ᶜ_Z` on the de Rham differential, at the target of the Gysin map.**  For
a nonempty family `f₁, …, f_c` of global equations with common zero locus `Z` and `c = c' + 1`,
this is the morphism

`i_*ℋ ᶜ_Z(Ω^q_{X/S}) ⟶ i_*ℋ ᶜ_Z(Ω^{q+1}_{X/S})`

of abelian sheaves on `X` induced by `d : Ω^q_{X/S} ⟶ Ω^{q+1}_{X/S}`.  It is
`Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap`, which is [Stacks, Tag 0G74] part (2) at
the Gysin map's target conjugating the abelian local cohomology functor, applied to the de Rham
differential.

**This is the arrow whose absence made the statement of [Stacks, Tag 0G85] fail to typecheck**: the
target of `AlgebraicGeometry.Scheme.Hom.gysinMap` is an `𝒪_X`-module and `ℋ ᶜ_Z` is a functor on
`𝒪_X`-modules, so before this the local cohomology sheaf did not act on `d` at all. -/
public def gysinTargetDeRhamMap (π : X ⟶ S) {c : ℕ} (f : Fin (c + 1) → Γ(X, ⊤)) (q : ℕ) :
    (abelianSheaf X).obj (pushforwardLocalCohomology f
        (relativeDifferentialForms π (q : ℤ))) ⟶
      (abelianSheaf X).obj (pushforwardLocalCohomology f
        (relativeDifferentialForms π ((q + 1 : ℕ) : ℤ))) :=
  Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap f (deRhamDifferentialAbHom π q)

/-- The action of `i_*ℋ ᶜ_Z` on the de Rham differential extends the `𝒪_X`-linear action: on the
underlying abelian-sheaf morphism of a morphism `φ` of `X.Modules` the same construction is the
underlying morphism of the functorial action on `φ`.  This is
`Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap_map`; it says nothing about `d`, and is
recorded to pin down that `gysinTargetDeRhamMap` is the right notion rather than merely a map of
the right type. -/
public theorem gysinTargetAbelianMap_map_of_modules {c : ℕ} (f : Fin (c + 1) → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) :
    Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap f ((abelianSheaf X).map φ) =
      (abelianSheaf X).map
        ((Stacks.Perfect.GysinLocalCohomology.localCohomologyPushforwardFunctor
          (isClosed_equationsClosedSet f) (((c + 1 : ℕ)) : ℤ)).map φ) :=
  Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap_map f φ

/-! ### The comparison square of Stacks 0G85 for the Gysin formula -/

/-- **The comparison square of [Stacks, Tag 0G85] for the Gysin formula**, as a proposition: the
square

`Ω^p_{X/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c}_{X/S})`,  `Ω^{p+1}_{X/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c+1}_{X/S})`

whose horizontal arrows are the underlying abelian-sheaf morphisms of
`AlgebraicGeometry.Scheme.Hom.gysinFormulaHom`, that is of
`ω̃ ↦ c_{f₁,…,f_c}(ω̃) ∧ d f₁ ∧ ⋯ ∧ d f_c`, whose left vertical arrow is the de Rham differential
read as a morphism of abelian sheaves and whose right vertical arrow is
`AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap`, commutes.

By `AlgebraicGeometry.Scheme.Hom.formRestriction_comp_gysinMap` and the surjectivity of restriction
of `p`-forms to `Z` this is the content of [Stacks, Tag 0G85] on the Gysin formula; passing from it
to the corresponding square for `AlgebraicGeometry.Scheme.Hom.gysinMap` needs in addition the
commutation of restriction to `Z` with the de Rham differentials, which the library does not have
as a morphism of abelian sheaves — see item 4 of the implementation notes.

**This proposition is not proved anywhere, and nothing in this file or elsewhere in the library
assumes it.**  It is recorded because it is the first spelling of the square of
[Stacks, Tag 0G85] that typechecks at all; the implementation notes of this file list the four
declarations still missing for its proof.

The right-hand composite is the Gysin formula in degree `p + 1`, written out as the wedge with
`d f₁ ∧ ⋯ ∧ d f_c` followed by the fraction class, with the degree bookkeeping explicit between
them: the wedge raises the degree `p + 1` to `p + 1 + c`, whereas the differential of the
left-hand composite lands in degree `p + c + 1`, and
`AlgebraicGeometry.Scheme.Hom.deRhamReindexPresheafHom` is the canonical identification of those
two terms of the de Rham complex. -/
public def GysinFormulaCommutesWithDeRham (π : X ⟶ S) {c : ℕ} (f : Fin (c + 1) → Γ(X, ⊤))
    (p : ℕ) : Prop :=
  (abelianSheaf X).map (gysinFormulaHom π f (p : ℤ)) ≫
      gysinTargetDeRhamMap π f (p + (c + 1)) =
    deRhamDifferentialAbHom π p ≫
      abHom (Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)) ≫
          deRhamReindexPresheafHom π (show p + 1 + (c + 1) = p + (c + 1) + 1 by omega)) ≫
        (abelianSheaf X).map (formFractionClass π f ((p + (c + 1) + 1 : ℕ) : ℤ))

/-- **The comparison square of [Stacks, Tag 0G85] for the fraction class alone**, as a proposition:
the class map `c_{f₁,…,f_c}` of [Stacks, Tag 0G7Q] in the form
`AlgebraicGeometry.Scheme.Hom.formFractionClass` that the Gysin map is built from commutes with the
de Rham differential, the local cohomology sheaf acting on the differential through
`AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap`.

**This is exactly the content of steps (i) and (ii) of the proof of [Stacks, Tag 0G85] in the
spelling the Gysin map uses, and it is the only thing still missing**: by
`AlgebraicGeometry.Scheme.Hom.gysinFormulaCommutesWithDeRham_of_formFractionClass` it implies the
square for the Gysin formula, step (iii) being
`AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_comm_deRhamDifferentialPresheafHom`.  It is not proved
here and it is not assumed anywhere except as an explicit hypothesis of that reduction; the
implementation notes of this file list the four declarations its proof needs. -/
public def FormFractionClassCommutesWithDeRham (π : X ⟶ S) {c : ℕ} (f : Fin (c + 1) → Γ(X, ⊤))
    (q : ℕ) : Prop :=
  (abelianSheaf X).map (formFractionClass π f (q : ℤ)) ≫ gysinTargetDeRhamMap π f q =
    deRhamDifferentialAbHom π q ≫
      (abelianSheaf X).map (formFractionClass π f ((q + 1 : ℕ) : ℤ))

/-- Forgetting the module structure turns a composite of morphisms of abelian presheaves into the
composite of the corresponding morphisms of abelian sheaves. -/
theorem abHom_comp {F G H : X.Modules}
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (χ : Scheme.Modules.presheaf G ⟶ Scheme.Modules.presheaf H) :
    abHom (ψ ≫ χ) = abHom ψ ≫ abHom χ := rfl

/-- **The square of [Stacks, Tag 0G85] for the Gysin formula follows from the square for the
fraction class.**  Step (iii) of the source's proof — that the wedge factor
`ω̃ ↦ ω̃ ∧ d f₁ ∧ ⋯ ∧ d f_c` commutes with the de Rham differential, which is
`AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_comm_d` — is discharged here, so the whole of
[Stacks, Tag 0G85] on the Gysin formula is reduced to the single hypothesis
`AlgebraicGeometry.Scheme.Hom.FormFractionClassCommutesWithDeRham`, which is steps (i) and (ii) in
the spelling the Gysin map uses.

This is a reduction and **not** a proof of [Stacks, Tag 0G85]: nothing in the library discharges
its hypothesis.  The conclusion is nevertheless available unconditionally, by the other route —
see `Stacks.Perfect.SupportedEndoForgetDegreewise.gysinFormulaCommutesWithDeRham`. -/
public theorem gysinFormulaCommutesWithDeRham_of_formFractionClass (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ)
    (hfrac : FormFractionClassCommutesWithDeRham π f (p + (c + 1))) :
    GysinFormulaCommutesWithDeRham π f p := by
  have hwedge := gysinWedgeHom_comm_deRhamDifferentialPresheafHom π f p (c := c + 1)
  simp only [FormFractionClassCommutesWithDeRham, deRhamDifferentialAbHom] at hfrac
  simp only [GysinFormulaCommutesWithDeRham, deRhamDifferentialAbHom]
  rw [show gysinFormulaHom π f (p : ℤ) = gysinWedgeHom π f (p : ℤ) ≫
        formFractionClass π f ((p + (c + 1) : ℕ) : ℤ) from rfl,
    CategoryTheory.Functor.map_comp, Category.assoc, hfrac,
    Stacks.Perfect.AbelianFraction.abelianSheaf_map (gysinWedgeHom π f (p : ℤ)),
    ← Category.assoc, ← abHom_comp, hwedge, abHom_comp, Category.assoc]

end AlgebraicGeometry.Scheme.Hom

end
