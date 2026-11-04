module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalkPerfect
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaGoodBaseChange.GeneralComparison
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeTorDimension
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartDerivedStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartStalkGenerator
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 0F9X: derived pullback commutes with derived décalage at a good triple

Let `(X, D, M)` be a triple as in Situation 0F8S — a scheme, an effective Cartier divisor on it
with ideal sheaf `ℐ = ℐ_D`, and a perfect object `M` of `D(𝒪_X)` — and let `h : Y ⟶ X` be a
morphism of schemes for which the inverse image `E = h^{-1}D` is defined, with ideal sheaf
`𝒥 = ℐ_E`.  [Stacks, Tag 0F9X] asserts that for a **good** triple

`Lh^*(Lη_ℐ M) = Lη_𝒥(Lh^* M)`

in `D(𝒪_Y)`.  This file proves it, for an arbitrary `h`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_affineOpen_stalk_goodModel`: goodness of
  the triple, read at a point: an affine open on which `D` is principal, together with a bounded
  complex of finite free `𝒪_{X,x}`-modules representing the derived stalk whose determinantal
  ideals at the germ of the equation are all principal.
* `AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullback_derivedEta_iso`:
  **[Stacks, Tag 0F9X]**.

## How goodness becomes the stalkwise hypothesis

`Stacks.Divisors.Eta.nonempty_derivedPullback_derivedEta_iso_of_forall_stalk_good` proves the
tag from a stalkwise hypothesis: at every point `z` of `Y` a generator `a` of the stalk ideal
`ℐ_{h(z)}` whose germ generates the stalk ideal of `h^*ℐ`, and a bounded complex `C` of finite
free `𝒪_{X,h(z)}`-modules representing the stalk complex with all `I_i(C, a)` principal.  The
three inputs are supplied here:

* the complex and the principality come from an affine chart through `h(z)`, whose complex base
  changed to the stalk represents the derived stalk by
  `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.nonempty_q_baseChange_iso_derivedStalk`
  and whose determinantal ideals base change by Tag 0GSU;
* away from `D` no chart is needed: the stalk ideal is the unit ideal, so the germ of the
  equation is a unit and every determinantal ideal is the unit ideal, while the complex comes
  from perfectness of the derived stalk (Tag 0657);
* the two generator statements are `Stacks.Divisors.Eta.generatesStalkIdeal_germ` on `X` and
  `Stacks.Divisors.Eta.generatesStalkIdeal_pullbackIdealIncl` on `Y`.

## Implementation notes

The presentation of the object by a K-flat complex of flat modules that the comparison is
written at is produced by `Stacks.Divisors.Eta.exists_kFlat_isFlat_rep'`, so nothing is carried.
The chart's `represents` field speaks of the situation's own model of the derived category of
`𝒪_X`-modules, whereas the comparison is written at
`CategoryTheory.HasDerivedCategory.standard`; `CategoryTheory.Localization.compUniqFunctor` moves
a representative across, which is the same transport
`AlgebraicGeometry.ComplexAndDivisorSituation.standardObject` performs on the object.

## References

* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
* [Stacks Project, Tag 0GSU](https://stacks.math.columbia.edu/tag/0GSU)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Divisors.Eta (idealSheaf idealSheafι derivedEtaData)
open Stacks.IdealTorsion (GeneratesStalkIdeal)
open Stacks.IdealTorsion.Eta (stalkComplex pullbackIdealIncl)
open Stacks.RingedSpace (commStalkGermMap)
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.ComplexAndDivisorSituation.isEffectiveCartierDivisor

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable (S : ComplexAndDivisorSituation.{u, d})

/-- A complex of `𝒪_X`-modules representing the object of the triple in the situation's own
model of the derived category. -/
private noncomputable def situationRep : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ :=
  (@DerivedCategory.Q _ _ _ S.hasDerivedCategory).objPreimage S.M

/-- `AlgebraicGeometry.ComplexAndDivisorSituation.situationRep` represents the object of the
triple in the situation's own model. -/
private theorem nonempty_q_situationRep_iso :
    Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj S.situationRep ≅ S.M) :=
  ⟨(@DerivedCategory.Q _ _ _ S.hasDerivedCategory).objObjPreimageIso S.M⟩

/-- `AlgebraicGeometry.ComplexAndDivisorSituation.situationRep` represents
`AlgebraicGeometry.ComplexAndDivisorSituation.standardObject` in the standard model: the
canonical equivalence of the two localizations is compatible with the two localization functors,
by `CategoryTheory.Localization.compUniqFunctor`. -/
private noncomputable def qSituationRepIsoStandardObject :
    DerivedCategory.Q.obj S.situationRep ≅ S.standardObject :=
  ((Localization.compUniqFunctor (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
        (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
          (OXMod.{u, u} S.X.toRingedSpace)))
        (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
          (ComplexShape.up ℤ))).app S.situationRep).symm ≪≫
    (Localization.uniq (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
        (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
          (OXMod.{u, u} S.X.toRingedSpace)))
        (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
          (ComplexShape.up ℤ))).functor.mapIso S.nonempty_q_situationRep_iso.some

/-- **The degreewise stalk of two complexes representing the same object of `D(𝒪_X)` represent
the same object of `D(𝒪_{X,x})`.**  The stalk functor is exact, so its descent to the derived
categories is computed degreewise. -/
private theorem nonempty_q_stalkComplex_iso_of_q_iso {X : Scheme.{u}} (x : X)
    (K L : CochainComplex X.Modules ℤ) (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    Nonempty (DerivedCategory.Q.obj (stalkComplex X.toRingedSpace x K) ≅
      DerivedCategory.Q.obj (stalkComplex X.toRingedSpace x L)) :=
  ⟨((Stacks.Duality.modulesStalkFunctor x).mapDerivedCategoryFactors.app K).symm ≪≫
    (Stacks.Duality.modulesStalkFunctor x).mapDerivedCategory.mapIso e ≪≫
    (Stacks.Duality.modulesStalkFunctor x).mapDerivedCategoryFactors.app L⟩

/-- **Goodness of the triple read at a point.**  At every point `x` of a good triple there are an
affine open `U ∋ x` on which `D` is cut out by a nonzerodivisor `f` and a bounded complex `C` of
finite free `𝒪_{X,x}`-modules such that every determinantal ideal `I_i(C, germ f)` is principal
and `C` represents the degreewise stalk at `x` of a complex presenting the object of the triple.

On `D` the chart supplied by goodness is base changed to the stalk: its determinantal ideals stay
principal by Tag 0GSU, and the base-changed complex represents the derived stalk by
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.nonempty_q_baseChange_iso_derivedStalk`.
Away from `D` the germ of the equation is a unit, so every determinantal ideal is the unit ideal,
and the complex comes from perfectness of the derived stalk. -/
theorem exists_affineOpen_stalk_goodModel (hgood : S.IsGoodTriple)
    (𝒦 : CochainComplex S.X.Modules ℤ) (e : DerivedCategory.Q.obj 𝒦 ≅ S.standardObject)
    (x : S.X) :
    ∃ (U : S.X.affineOpens) (hx : x ∈ (U : S.X.Opens)) (f : Γ(S.X, (U : S.X.Opens))),
      S.D.ideal U = Ideal.span {f} ∧
        ∃ C : BoundedComplex (ringStalk S.X.toRingedSpace x),
          (∀ i : ℤ,
            (idealI C ((S.X.presheaf.germ (U : S.X.Opens) x hx).hom f) i).IsPrincipal) ∧
            Nonempty (DerivedCategory.Q.obj C.toCochainComplex ≅
              DerivedCategory.Q.obj (stalkComplex S.X.toRingedSpace x 𝒦)) := by
  obtain ⟨eK⟩ := nonempty_q_stalkComplex_iso_of_q_iso x S.situationRep 𝒦
    (S.qSituationRepIsoStandardObject ≪≫ e.symm)
  by_cases hxD : x ∈ S.D.supportSet
  · obtain ⟨C₀, hxC₀, hprin⟩ := hgood x hxD
    refine ⟨C₀.U, hxC₀, C₀.f, C₀.divisor_ideal,
      C₀.complex.baseChange (S.X.presheaf.germ (C₀.U : S.X.Opens) x hxC₀).hom,
      fun i => C₀.isPrincipal_determinantalIdeal_baseChange _ i (hprin i), ?_⟩
    obtain ⟨eC⟩ := C₀.nonempty_q_baseChange_iso_derivedStalk x hxC₀ S.situationRep
      S.nonempty_q_situationRep_iso
    refine ⟨?_ ≪≫ eK⟩
    rw [← Stacks.Duality.affineGermRingHom_eq_germ C₀.U.2 x hxC₀]
    exact eC
  · obtain ⟨U, hU, hxU, f, hfreg, hfideal⟩ :=
      Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
        S.D S.isEffectiveCartierDivisor x
    have hunit : IsUnit ((S.X.presheaf.germ U x hxU).hom f) := by
      refine Ideal.span_singleton_eq_top.1 ?_
      rw [← AlgebraicGeometry.IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span
        (U := ⟨U, hU⟩) hxU hfideal]
      exact (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support S.D x).2
        fun hc => hxD (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 hc)
    have hperf : StacksDraft.Perfect.IsPerfect
        (DerivedCategory.Q.obj (stalkComplex S.X.toRingedSpace x 𝒦)) := by
      have hA : (show OXMod.{u, u} S.X.toRingedSpace ⥤
          ModuleCat.{u} (ToType (S.X.presheaf.stalk x)) from
          Stacks.Duality.modulesStalkFunctor x).Additive :=
        Stacks.Duality.modulesStalkFunctor_additive x
      have hL : PreservesFiniteLimits (show OXMod.{u, u} S.X.toRingedSpace ⥤
          ModuleCat.{u} (ToType (S.X.presheaf.stalk x)) from
          Stacks.Duality.modulesStalkFunctor x) :=
        Stacks.Duality.modulesStalkFunctor_preservesFiniteLimits x
      have hC : PreservesFiniteColimits (show OXMod.{u, u} S.X.toRingedSpace ⥤
          ModuleCat.{u} (ToType (S.X.presheaf.stalk x)) from
          Stacks.Duality.modulesStalkFunctor x) :=
        Stacks.Duality.modulesStalkFunctor_preservesFiniteColimits x
      have h0 := RingedSpace.isPerfect_moduleStalkOver_of_isPerfect
        (X := S.X.toRingedSpace) x (RingedSpace.ringCatStalkEquiv S.X.toRingedSpace x).symm
        (Stacks.Duality.modulesStalkFunctor x) (Iso.refl _) (DerivedCategory.Q.obj 𝒦)
        (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso e.symm
          (RingedSpace.KFlatDerivedPullback.isPerfect_uniqFunctor_obj S.hasDerivedCategory
            (HasDerivedCategory.standard (OXMod.{u, u} S.X.toRingedSpace)) S.M S.isPerfect))
      obtain ⟨P, a, b, h1, h2, h3, h4, ⟨i⟩⟩ := h0
      exact ⟨P, a, b, h1, h2, h3, h4,
        ⟨((Stacks.Duality.modulesStalkFunctor x).mapDerivedCategoryFactors.app 𝒦).symm ≪≫ i⟩⟩
    obtain ⟨C, hC⟩ := StacksDraft.Perfect.exists_boundedComplex_iso_of_isPerfect _ hperf
    refine ⟨⟨U, hU⟩, hxU, f, hfideal, C, fun i => ?_, hC⟩
    have htop : idealI C ((S.X.presheaf.germ U x hxU).hom f) i = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (pow_rank_mem_idealI C _ i) (hunit.pow (C.rank i))
    exact ⟨1, htop.trans Ideal.span_singleton_one.symm⟩

/-- **[Stacks, Tag 0F9X].**  Let `(X, D, M)` be a triple as in Situation 0F8S, with `ℐ` the ideal
sheaf of `D`, and let `h : Y ⟶ X` be a morphism of schemes such that the inverse image
`E = h^{-1}D` is defined, with ideal sheaf `𝒥`.  If `(X, D, M)` is a good triple then

`Lh^*(Lη_ℐ M) ≅ Lη_𝒥(Lh^* M)`

in `D(𝒪_Y)`, the right-hand side being the décalage by the ideal sheaf of `E` of the object of
the pulled-back triple, i.e.
`AlgebraicGeometry.ComplexAndDivisorSituation.etaDerivedPullbackObject`.

No flatness of `h` is assumed.  The object is presented by a K-flat complex of flat modules —
which every object admits — and goodness is read at the stalks by
`AlgebraicGeometry.ComplexAndDivisorSituation.exists_affineOpen_stalk_goodModel`, which also
supplies the generator of the stalk ideal whose germ generates the stalk ideal of `h^*ℐ`. -/
@[stacks 0F9X "the whole statement: for a good triple and an arbitrary morphism `h` along which \
the inverse image of the divisor is defined, `Lh^*(Lη_I M) ≅ Lη_J(Lh^* M)`. Goodness enters \
through its reading at the stalks, \
AlgebraicGeometry.ComplexAndDivisorSituation.exists_affineOpen_stalk_goodModel, and the \
ring-level input is Stacks 0F7X in the form \
Stacks.Eta.GoodBaseChange.quasiIso_baseChangeMap_comp_etaBaseChangeMap_of_kFlat. The case of a \
flat h without goodness is Stacks.Divisors.Eta.isIso_derivedEtaPullbackComparison"]
theorem nonempty_derivedPullback_derivedEta_iso (hgood : S.IsGoodTriple) {Y : Scheme.{u}}
    (h : Y ⟶ S.X) (hD : Stacks.Divisors.IsPullbackDefined h S.D) :
    Nonempty ((derivedPullback h.toLRSHom.toShHom).obj
        ((derivedEtaData S.D).functor.obj S.standardObject) ≅
      (derivedEtaData (S.D.comap h)).functor.obj (S.derivedPullbackObject h)) := by
  obtain ⟨𝒦, h𝒦, hflat, ⟨e⟩⟩ :=
    Stacks.Divisors.Eta.exists_kFlat_isFlat_rep' S.D S.standardObject
  refine Stacks.Divisors.Eta.nonempty_derivedPullback_derivedEta_iso_of_forall_stalk_good
    h S.D hD 𝒦 hflat h𝒦 (fun z => ?_) S.standardObject e
  obtain ⟨U, hx, f, hfideal, C, hprin, hCiso⟩ :=
    S.exists_affineOpen_stalk_goodModel hgood 𝒦 e (h.base z)
  exact ⟨(S.X.presheaf.germ (U : S.X.Opens) (h.base z) hx).hom f,
    Stacks.Divisors.Eta.generatesStalkIdeal_germ S.D U hx hfideal
      (AlgebraicGeometry.isRegular_of_isEffectiveCartierDivisor_of_ideal_eq_span
        S.isEffectiveCartierDivisor U hfideal).mem_nonZeroDivisors,
    Stacks.Divisors.Eta.generatesStalkIdeal_pullbackIdealIncl h S.D hD U hfideal z hx,
    C, hprin, hCiso⟩

end AlgebraicGeometry.ComplexAndDivisorSituation

end
