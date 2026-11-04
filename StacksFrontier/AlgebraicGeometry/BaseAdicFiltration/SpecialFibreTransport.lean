module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.FunctorialGraded
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionRelativeLeray.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections

/-!
# The hypotheses of the filtration argument, read on the special fibre

The filtration argument of [Stacks, Tag 0E3X] for a morphism `g : U ⟶ V` of flat families over
an Artinian local base `A` asks for two things *about the families*: that the comparison of
special fibres `c_1` be invertible, and that `R¹g_*` kill `𝒪_U/𝔪𝒪_U`.  The tag's own hypotheses
are instead about the morphism `f : X ⟶ Y` of special fibres: `f_*𝒪_X = 𝒪_Y` and `R¹f_*𝒪_X = 0`.
Bridging the two needs no more of the deformation data than the cartesian square

```
X --- f ---> Y
|            |
i_X         i_Y
v            v
U --- g ---> V
```

together with the statement that `i_X` and `i_Y` cut out the special fibres, i.e. that their
ideal sheaves are `𝔪 𝒪_U` and `𝔪 𝒪_V` (`Stacks.BaseAdicFiltration.baseIdeal`).

`Stacks.BaseAdicFiltration.specialFibreIsoPushforwardUnit` identifies `𝒪_U/𝔪𝒪_U`, which the
filtration argument carries on `U`, with `(i_X)_* 𝒪_X`, which lives on the special fibre.  It is
[Stacks, Tag 0EL1] at exponent `1` — `Stacks.Algebraization.idealQuotientPushforwardIso`, whose
hypothesis `i_X.ker = (𝔪 𝒪_U) ^ 1` is the displayed one after `pow_one` — followed by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` to turn `i_X^* 𝒪_U` into `𝒪_X`.  What makes
it usable is that it is *normalized*: composed with the quotient projection it is the
structure-sheaf comparison of `i_X`
(`Stacks.BaseAdicFiltration.adicProj_comp_specialFibreIsoPushforwardUnit`), because
`pullbackUnitIso` transposes to that comparison under the pullback--pushforward adjunction
(`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_homEquiv`).

**The vanishing** travels through the two degenerate Leray collapses, in opposite directions.
`Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.isZero_rightDerived_pushforward_iff`
turns `R¹g_*((i_X)_*𝒪_X)` into `R¹(i_X ≫ g)_*𝒪_X` — this is the collapse for a closed immersion
in the *first* position, and it is what replaces the spectral sequence.  The square rewrites
`i_X ≫ g` as `f ≫ i_Y`, and `Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology`
then splits `R¹(f ≫ i_Y)_*` as `(i_Y)_* ∘ R¹f_*`, which needs only that `(i_Y)_*` preserve
homology — that is exactness of direct image along a closed immersion,
`Stacks.ClosedImmersion.preservesFiniteColimits_pushforward`.

**The comparison** is a square of structure-sheaf maps.  `c_1` is characterized by
`Stacks.BaseAdicFiltration.adicProj_comp_adicQuotientComparison`, so after cancelling the
projection — an epimorphism, `Stacks.Algebraization.epi_cokernel_π_idealPowerMultiple` — the
identity to prove is exactly the cocycle condition
`Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom_comp_pushforwardSquareIso` for the
square, with the two normalizations above supplying the two edges.  Nothing has to be said about
`c_1` itself beyond that characterization.

## Main definitions

* `Stacks.BaseAdicFiltration.specialFibreIsoPushforwardUnit` — `𝒪_U/𝔪𝒪_U ≅ (i_X)_* 𝒪_X`.

## Main results

* `Stacks.BaseAdicFiltration.adicProj_comp_specialFibreIsoPushforwardUnit` — the identification
  is normalized by the structure-sheaf comparison of `i_X`.
* `Stacks.BaseAdicFiltration.isZero_rightDerived_one_specialFibre_of_isZero` — **the tag's
  `R¹f_*𝒪_X = 0` gives `R¹g_*(𝒪_U/𝔪𝒪_U) = 0`.**
* `Stacks.BaseAdicFiltration.isIso_adicQuotientComparison_one_of_isIso` — **the tag's
  `f_*𝒪_X = 𝒪_Y` gives invertibility of `c_1`.**
* `Stacks.BaseAdicFiltration.isIso_unitToPushforwardUnit_of_specialFibre` — the two together,
  fed to the filtration argument: `𝒪_V ⟶ g_*𝒪_U` is invertible.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray
open Stacks.AlgebraicGeometry.AffineBaseChange
open Stacks.AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.BaseAdicFiltration

variable {A : Type u} [CommRing A] {U X : Scheme.{u}}
  (p : U ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (iX : X ⟶ U) [IsClosedImmersion iX]

/-- **The special fibre, as the direct image of the structure sheaf of the closed subscheme.**
For `i_X : X ⟶ U` a closed immersion whose ideal sheaf is `I 𝒪_U`, the quotient `𝒪_U/I𝒪_U` that
the filtration argument carries on `U` is `(i_X)_* 𝒪_X`.

This is [Stacks, Tag 0EL1] at exponent `1`, whose conclusion is `(i_X)_* i_X^* 𝒪_U`, followed by
the identification of `i_X^* 𝒪_U` with `𝒪_X`. -/
def specialFibreIsoPushforwardUnit (hk : iX.ker = baseIdeal p I) :
    specialFibre p I (SheafOfModules.unit U.ringCatSheaf) ≅
      (Scheme.Modules.pushforward iX).obj (SheafOfModules.unit X.ringCatSheaf) :=
  idealQuotientPushforwardIso (baseIdeal p I) 1 (SheafOfModules.unit U.ringCatSheaf) iX
      (by rw [hk, pow_one]) ≪≫
    (Scheme.Modules.pushforward iX).mapIso (Scheme.Modules.pullbackUnitIso iX)

/-- **The identification is normalized by the structure-sheaf comparison of `i_X`.** Composing
the projection `𝒪_U ⟶ 𝒪_U/I𝒪_U` with it gives `𝒪_U ⟶ (i_X)_* 𝒪_X`.

Tag 0EL1's comparison is the adjunction unit descended through the projection, so the composite
is the unit followed by `i_X^* 𝒪_U ≅ 𝒪_X`; that is the transpose of the latter, which is the
structure-sheaf comparison by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_homEquiv`. -/
theorem adicProj_comp_specialFibreIsoPushforwardUnit (hk : iX.ker = baseIdeal p I) :
    adicProj p I 1 (SheafOfModules.unit U.ringCatSheaf) ≫
        (specialFibreIsoPushforwardUnit p I iX hk).hom =
      Scheme.Modules.unitToPushforwardUnit iX := by
  have h1 := idealQuotientPushforwardMap_π (baseIdeal p I) 1
    (SheafOfModules.unit U.ringCatSheaf) iX (by rw [hk, pow_one])
  have h2 := Scheme.Modules.pullbackUnitIso_homEquiv iX
  rw [Adjunction.homEquiv_unit] at h2
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ (Scheme.Modules.pushforward iX).map
      (Scheme.Modules.pullbackUnitIso iX).hom) h1)).trans h2

section Vanishing

variable {V Y : Scheme.{u}}

/-- A higher direct image vanishes along one morphism exactly when it vanishes along an equal
one.  This is where the commutativity of the special-fibre square is spent: it rewrites the
composite `i_X ≫ g` as `f ≫ i_Y`. -/
theorem isZero_rightDerived_pushforward_congr {a b : X ⟶ V} (h : a = b) (M : X.Modules)
    (n : ℕ) :
    IsZero (((Scheme.Modules.pushforward a).rightDerived n).obj M) ↔
      IsZero (((Scheme.Modules.pushforward b).rightDerived n).obj M) := by
  subst h
  exact Iff.rfl

/-- **`R¹(f ≫ i)_* = 0` when `R¹f_* = 0` and `i` is a closed immersion.** Direct image along a
closed immersion is exact, hence preserves homology, so it commutes with passing to the first
right derived functor of the inner direct image
(`Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology`); an additive functor carries a
zero object to a zero object, and `Scheme.Modules.pushforwardComp` identifies the composite of
the two direct images with the direct image of the composite. -/
theorem isZero_rightDerived_one_comp_of_isZero (fXY : X ⟶ Y) (iY : Y ⟶ V)
    [IsClosedImmersion iY] (M : X.Modules)
    (hR : IsZero (((Scheme.Modules.pushforward fXY).rightDerived 1).obj M)) :
    IsZero (((Scheme.Modules.pushforward (fXY ≫ iY)).rightDerived 1).obj M) := by
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (Scheme.Modules.pushforward fXY) (Scheme.Modules.pushforward iY) 1 M
  have hzero : IsZero ((Scheme.Modules.pushforward iY).obj
      (((Scheme.Modules.pushforward fXY).rightDerived 1).obj M)) :=
    IsZero.of_iso (isZero_zero _)
      ((Scheme.Modules.pushforward iY).mapIso hR.isoZero ≪≫
        (Scheme.Modules.pushforward iY).mapZeroObject)
  exact (hzero.of_iso e.symm).of_iso
    ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (Scheme.Modules.pushforwardComp fXY iY) 1).app M).symm

/-- **The tag's `R¹f_*𝒪_X = 0` gives `R¹g_*(𝒪_U/I𝒪_U) = 0`.** The quotient is `(i_X)_* 𝒪_X`,
so the degenerate Leray collapse for the closed immersion `i_X` turns `R¹g_*` of it into
`R¹(i_X ≫ g)_* 𝒪_X`; the square rewrites that as `R¹(f ≫ i_Y)_* 𝒪_X`, which vanishes with
`R¹f_*𝒪_X`. -/
theorem isZero_rightDerived_one_specialFibre_of_isZero (g : U ⟶ V) (iY : Y ⟶ V)
    [IsClosedImmersion iY] (fXY : X ⟶ Y)
    (hk : iX.ker = baseIdeal p I) (hsq : fXY ≫ iY = iX ≫ g)
    (hR : IsZero (((Scheme.Modules.pushforward fXY).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (specialFibre p I (SheafOfModules.unit U.ringCatSheaf))) := by
  have h1 : IsZero (((Scheme.Modules.pushforward (iX ≫ g)).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)) :=
    (isZero_rightDerived_pushforward_congr hsq (SheafOfModules.unit X.ringCatSheaf) 1).1
      (isZero_rightDerived_one_comp_of_isZero fXY iY
        (SheafOfModules.unit X.ringCatSheaf) hR)
  have h2 := (isZero_rightDerived_pushforward_iff iX g
    (SheafOfModules.unit X.ringCatSheaf) 1).2 h1
  exact h2.of_iso
    (((Scheme.Modules.pushforward g).rightDerived 1).mapIso
      (specialFibreIsoPushforwardUnit p I iX hk))

end Vanishing

section Comparison

variable {V Y : Scheme.{u}} (pV : V ⟶ Spec (CommRingCat.of A)) {g : U ⟶ V}
  (hg : g ≫ pV = p) (iY : Y ⟶ V) [IsClosedImmersion iY] (fXY : X ⟶ Y)

include hg in
/-- **The square of structure-sheaf comparisons commutes.**  Read through the identifications of
the two special fibres with the direct images of the structure sheaves of the closed subschemes,
the comparison `c_1 : 𝒪_V/I𝒪_V ⟶ g_*(𝒪_U/I𝒪_U)` becomes `(i_Y)_*` of `𝒪_Y ⟶ f_*𝒪_X`, up to the
identification of the two composite direct images around the square.  Both sides are tested
against the projection out of `𝒪_V`, an epimorphism, where the identity is the cocycle condition
`Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom_comp_pushforwardSquareIso`. -/
private theorem adicQuotientComparison_one_comp_pushforwardSquareIso
    (hkX : iX.ker = baseIdeal p I) (hkY : iY.ker = baseIdeal pV I)
    (hsq : iX ≫ g = fXY ≫ iY) :
    adicQuotientComparison pV hg I 1
        (Scheme.Modules.unitToPushforwardUnit g) ≫
      ((Scheme.Modules.pushforward g).map
          (specialFibreIsoPushforwardUnit p I iX hkX).hom ≫
        (AffinePushforward.pushforwardSquareIso hsq).hom.app
          (SheafOfModules.unit X.ringCatSheaf)) =
      (specialFibreIsoPushforwardUnit pV I iY hkY).hom ≫
        (Scheme.Modules.pushforward iY).map
          (Scheme.Modules.unitToPushforwardUnit fXY) := by
  have : Epi (adicProj pV I 1 (SheafOfModules.unit V.ringCatSheaf)) :=
    epi_cokernel_π_idealPowerMultiple _ _ _
  have hcmp := adicProj_comp_adicQuotientComparison pV hg I 1
    (Scheme.Modules.unitToPushforwardUnit g)
  have hnX := adicProj_comp_specialFibreIsoPushforwardUnit p I iX hkX
  have hnY := adicProj_comp_specialFibreIsoPushforwardUnit pV I iY hkY
  -- the inner contraction `g_*(π) ≫ g_*(e) ≫ T = g_*(u) ≫ T`
  have hinner : (Scheme.Modules.pushforward g).map
        (adicProj p I 1 (SheafOfModules.unit U.ringCatSheaf)) ≫
      ((Scheme.Modules.pushforward g).map
          (specialFibreIsoPushforwardUnit p I iX hkX).hom ≫
        (AffinePushforward.pushforwardSquareIso hsq).hom.app
          (SheafOfModules.unit X.ringCatSheaf)) =
      (Scheme.Modules.pushforward g).map (Scheme.Modules.unitToPushforwardUnit iX) ≫
        (AffinePushforward.pushforwardSquareIso hsq).hom.app
          (SheafOfModules.unit X.ringCatSheaf) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ (AffinePushforward.pushforwardSquareIso hsq).hom.app
          (SheafOfModules.unit X.ringCatSheaf))
        ((Functor.map_comp _ _ _).symm.trans
          (congrArg (Scheme.Modules.pushforward g).map hnX)))
  have hL : adicProj pV I 1 (SheafOfModules.unit V.ringCatSheaf) ≫
      (adicQuotientComparison pV hg I 1 (Scheme.Modules.unitToPushforwardUnit g) ≫
        ((Scheme.Modules.pushforward g).map
            (specialFibreIsoPushforwardUnit p I iX hkX).hom ≫
          (AffinePushforward.pushforwardSquareIso hsq).hom.app
            (SheafOfModules.unit X.ringCatSheaf))) =
      Scheme.Modules.unitToPushforwardUnit g ≫
        ((Scheme.Modules.pushforward g).map
            (Scheme.Modules.unitToPushforwardUnit iX) ≫
          (AffinePushforward.pushforwardSquareIso hsq).hom.app
            (SheafOfModules.unit X.ringCatSheaf)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ ((Scheme.Modules.pushforward g).map
            (specialFibreIsoPushforwardUnit p I iX hkX).hom ≫
          (AffinePushforward.pushforwardSquareIso hsq).hom.app
            (SheafOfModules.unit X.ringCatSheaf))) hcmp).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun q => Scheme.Modules.unitToPushforwardUnit g ≫ q) hinner)))
  have hR : adicProj pV I 1 (SheafOfModules.unit V.ringCatSheaf) ≫
      ((specialFibreIsoPushforwardUnit pV I iY hkY).hom ≫
        (Scheme.Modules.pushforward iY).map
          (Scheme.Modules.unitToPushforwardUnit fXY)) =
      Scheme.Modules.unitToPushforwardUnit iY ≫
        (Scheme.Modules.pushforward iY).map
          (Scheme.Modules.unitToPushforwardUnit fXY) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ (Scheme.Modules.pushforward iY).map
        (Scheme.Modules.unitToPushforwardUnit fXY)) hnY)
  exact (cancel_epi (adicProj pV I 1 (SheafOfModules.unit V.ringCatSheaf))).1
    (hL.trans ((structureUnitHom_comp_pushforwardSquareIso hsq).trans hR.symm))

include hg in
/-- **The tag's `f_*𝒪_X = 𝒪_Y` gives invertibility of the comparison of special fibres.** For
`g : U ⟶ V` over the base and `i_X`, `i_Y` cutting out the special fibres in a commutative
square over `f`, the comparison `c_1 : 𝒪_V/I𝒪_V ⟶ g_*(𝒪_U/I𝒪_U)` induced by `𝒪_V ⟶ g_*𝒪_U` is
invertible as soon as `𝒪_Y ⟶ f_*𝒪_X` is.

Both quotients are direct images of structure sheaves of the special fibres, and under those
identifications `c_1` becomes `(i_Y)_*` of `𝒪_Y ⟶ f_*𝒪_X`, up to the identification of the two
composite direct images around the square.  That this square of structure-sheaf maps commutes is
`Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom_comp_pushforwardSquareIso`; the
projection out of `𝒪_V` is an epimorphism, so checking `c_1` against it loses nothing. -/
theorem isIso_adicQuotientComparison_one_of_isIso
    (hkX : iX.ker = baseIdeal p I) (hkY : iY.ker = baseIdeal pV I)
    (hsq : iX ≫ g = fXY ≫ iY)
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit fXY)) :
    IsIso (C := V.Modules) (adicQuotientComparison pV hg I 1
      (Scheme.Modules.unitToPushforwardUnit g)) := by
  have hu : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit fXY) := h0
  have key := adicQuotientComparison_one_comp_pushforwardSquareIso p I iX pV hg iY fXY hkX hkY hsq
  have hRiso : IsIso (C := V.Modules)
      ((specialFibreIsoPushforwardUnit pV I iY hkY).hom ≫
        (Scheme.Modules.pushforward iY).map
          (Scheme.Modules.unitToPushforwardUnit fXY)) :=
    (specialFibreIsoPushforwardUnit pV I iY hkY ≪≫
      (Scheme.Modules.pushforward iY).mapIso
        (@asIso _ _ _ _ (Scheme.Modules.unitToPushforwardUnit fXY) h0)).isIso_hom
  have hBiso : IsIso (C := V.Modules)
      ((Scheme.Modules.pushforward g).map
          (specialFibreIsoPushforwardUnit p I iX hkX).hom ≫
        (AffinePushforward.pushforwardSquareIso hsq).hom.app
          (SheafOfModules.unit X.ringCatSheaf)) :=
    ((Scheme.Modules.pushforward g).mapIso
      (specialFibreIsoPushforwardUnit p I iX hkX) ≪≫
      (AffinePushforward.pushforwardSquareIso hsq).app
        (SheafOfModules.unit X.ringCatSheaf)).isIso_hom
  have hcomp : IsIso (C := V.Modules)
      (adicQuotientComparison pV hg I 1 (Scheme.Modules.unitToPushforwardUnit g) ≫
        ((Scheme.Modules.pushforward g).map
            (specialFibreIsoPushforwardUnit p I iX hkX).hom ≫
          (AffinePushforward.pushforwardSquareIso hsq).hom.app
            (SheafOfModules.unit X.ringCatSheaf))) := by
    rw [key]; exact hRiso
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hBiso hcomp

include hg in
/-- **[Stacks, Tag 0E3X], the faithfulness half: `g_*𝒪_U = 𝒪_V` follows from `f_*𝒪_X = 𝒪_Y`
and `R¹f_*𝒪_X = 0`.** For flat families over an Artinian local base and a commutative square
cutting out the special fibres, the comparison `𝒪_V ⟶ g_*𝒪_U` of the families is invertible as
soon as the tag's two hypotheses hold for the morphism `f` of special fibres.

This is the filtration argument of
`Stacks.BaseAdicFiltration.isIso_structureSheafComparison_of_isIso_specialFibre` with both of
its hypotheses supplied by the two transports above. -/
theorem isIso_unitToPushforwardUnit_of_specialFibre [IsArtinianRing A] [IsLocalRing A]
    [AlgebraicGeometry.Flat pV] [AlgebraicGeometry.Flat p]
    (hkX : iX.ker = baseIdeal p (IsLocalRing.maximalIdeal A))
    (hkY : iY.ker = baseIdeal pV (IsLocalRing.maximalIdeal A))
    (hsq : iX ≫ g = fXY ≫ iY)
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit fXY))
    (hR : IsZero (((Scheme.Modules.pushforward fXY).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    IsIso (C := V.Modules) (Scheme.Modules.unitToPushforwardUnit g) :=
  isIso_structureSheafComparison_of_isIso_specialFibre pV hg
    (Scheme.Modules.unitToPushforwardUnit g)
    (isIso_adicQuotientComparison_one_of_isIso p (IsLocalRing.maximalIdeal A) iX pV hg iY fXY
      hkX hkY hsq h0)
    (isZero_rightDerived_one_specialFibre_of_isZero p (IsLocalRing.maximalIdeal A) iX g iY fXY
      hkX hsq.symm hR)

end Comparison

end Stacks.BaseAdicFiltration

end
