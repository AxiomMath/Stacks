module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.AlgebraicGeometry.RingedSpace.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAllPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleEtaleChartTransport
public import StacksFrontier.RingTheory.Valuation.Localization

/-!
# Torsion free modules over a valuation ring are flat, on algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be an `𝒪_X`-module.  Flatness of `F` over `Y` (Stacks 05VV) is read on the commuting squares
of étale scheme charts of `f`: on such a square `U ⟶ V`, the restriction `F|_U` is flat over `V`
at every point of `U`.  The same reading of torsion freeness defines what it means for `F` to be
*torsion free over `Y`*: on every square, every stalk of `F|_U` is a torsion free module over the
corresponding local ring of `V`.

The proof of Stacks 0DM0 uses that over a valuation ring `R` the two notions agree: a
quasi-coherent module on an algebraic space `X` over `Spec R` whose sections have no `R`-torsion
is flat over `R`, flatness over a valuation ring being the same as torsion freeness
(Stacks 0539).  This file proves that statement.  The target is the algebraic space represented
by an object `W` of the big fppf site whose local rings are Bézout domains, for instance
`W = Spec R` for a valuation ring `R`; the test of torsion freeness is needed only on the squares
whose target chart is `W` itself, where the local rings of the target are those of `W`.

## Main definitions

* `AlgebraicGeometry.Space.IsTorsionFreeOverOnChartDiagram`: torsion freeness of the restriction
  of `F` to the source chart of one commuting square of étale scheme charts, over the target
  chart.
* `AlgebraicGeometry.Space.IsTorsionFreeOver`: torsion freeness of `F` over `Y`, on every such
  square.

## Main results

* `AlgebraicGeometry.Space.IsFlatOver.isTorsionFreeOver`: a module flat over `Y` is torsion free
  over `Y`.
* `AlgebraicGeometry.Space.isFlatOver_of_isTorsionFreeOver_restrictToChart`: for a target
  represented by `W` with Bézout domains as local rings, a quasi-coherent module which is
  torsion free over `W` on every étale scheme chart of `X` is flat over `W`.
* `AlgebraicGeometry.Space.isFlatOver_iff_isTorsionFreeOver`: for such a target, flatness and
  torsion freeness over it agree for a quasi-coherent module.
* `AlgebraicGeometry.Space.isFlatOver_iff_isTorsionFreeOver_of_valuationRing`: the case
  `W = Spec R` for a valuation ring `R`, the step of the proof of Stacks 0DM0 citing
  Stacks 0539.

## Implementation notes

Flatness over `Y` is read on *every* commuting square of charts, and torsion freeness over `Y`
is defined in the same way, so that a flat module is visibly torsion free.  For the converse only
the squares whose target chart is the identity chart of `W` are used: by the chart independence
of Stacks 05VU, `AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram`, it is
enough to test flatness at each point of `|X|` on one square through it, and every étale scheme
chart `U` of `X` sits in such a square, the composite `U ⟶ X ⟶ h_W` being the image of a unique
morphism `U ⟶ W` by the Yoneda lemma.  On that square the local rings of the target are those of
`W`, and Stacks 0539 applies stalk by stalk.  This is why the theorem is stated for a
represented target: the local rings of an arbitrary étale chart of `Spec R` need not be
valuation rings in any way visible from `R`, but those of `Spec R` are its localizations at
primes.

Quasi-coherence of `F` enters only through Stacks 05VU.

## References

* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Torsion freeness over the target -/

/-- Torsion freeness of a module on an algebraic space over the target, on one commuting square
of étale scheme charts: every stalk of the restriction of `F` to the source chart is a torsion
free module over the corresponding local ring of the target chart, through the vertical
morphism of schemes of the square. -/
noncomputable abbrev IsTorsionFreeOverOnChartDiagram {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX) (d : ChartDiagram B S hS X Y f) : Prop :=
  AlgebraicGeometry.IsTorsionFreeOver
    (LocallyRingedSpace.forgetToSheafedSpace.map
      ((BigFppfOver.toScheme B S hS).map d.g).toLRSHom)
    (restrictToChart B S hS hX F d.U)

/-- An `𝒪_X`-module is *torsion free over* `Y` along `f : X ⟶ Y` when, on every commuting square
of étale scheme charts of `f`, its restriction to the chart of `X` is torsion free over the
chart of `Y`.  This is the reading of `AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV with
flatness of the stalks replaced by torsion freeness. -/
noncomputable abbrev IsTorsionFreeOver {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) (F : Modules.{u, u} B S hS X hX) : Prop :=
  ∀ d : ChartDiagram B S hS X Y f, IsTorsionFreeOverOnChartDiagram B S hS hX F d

variable {B S hS}

/-- A module flat over the target is torsion free over the target: on every square of charts,
every stalk of the restriction is flat, hence torsion free, over the local ring of the target
chart. -/
theorem IsFlatOver.isTorsionFreeOver {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {f : X ⟶ Y} {F : Modules.{u, u} B S hS X hX}
    (h : IsFlatOver B S hS hX f F) : IsTorsionFreeOver B S hS hX f F :=
  fun d u => (h d u).isTorsionFreeOverAt

/-! ### Torsion free modules over a target with Bézout local rings -/

/-- An étale scheme chart `U` of `X`, together with the morphism `α : U ⟶ W` through which the
composite `U ⟶ X ⟶ h_W` factors, read as a commuting square of étale scheme charts of
`f : X ⟶ h_W` whose target chart is the identity chart of `W`. -/
def chartDiagramSelfChart {W : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace W) (U : SmallEtale B S hS X.1)
    (α : (SmallEtale.toOver B S hS X.1).obj U ⟶ W) (hα : U.1.hom ≫ f.hom = yoneda.map α) :
    ChartDiagram B S hS X.1 (schemeSpace W).1 f.hom where
  U := U
  V := selfChart B S hS W
  g := α
  comm := hα.trans (Category.comp_id (yoneda.map α)).symm

/-- **A torsion free module over a target with Bézout local rings is flat.**  Let `W` be an
object of the big fppf site all of whose local rings are Bézout domains — for instance the
spectrum of a valuation ring — and let `f : X ⟶ h_W` be a morphism from an algebraic space.  A
quasi-coherent `𝒪_X`-module `F` whose restriction to every étale scheme chart `U` of `X` is
torsion free over `W`, through the morphism `α : U ⟶ W` induced by `f`, is flat over `h_W` in
the sense of Stacks 05VV.

Stalk by stalk this is Stacks 0539; the passage from the squares with target chart `W` to all
squares is the chart independence of Stacks 05VU. -/
theorem isFlatOver_of_isTorsionFreeOver_restrictToChart {W : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace W)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hdom : ∀ w, IsDomain (((BigFppfOver.toScheme B S hS).obj W).presheaf.stalk w))
    (hbez : ∀ w, IsBezout (((BigFppfOver.toScheme B S hS).obj W).presheaf.stalk w))
    (htf : ∀ (U : SmallEtale B S hS X.1) (α : (SmallEtale.toOver B S hS X.1).obj U ⟶ W),
      U.1.hom ≫ f.hom = yoneda.map α →
        AlgebraicGeometry.IsTorsionFreeOver
          (LocallyRingedSpace.forgetToSheafedSpace.map
            ((BigFppfOver.toScheme B S hS).map α).toLRSHom)
          (restrictToChart B S hS X.2 F U)) :
    IsFlatOver B S hS X.2 f.hom F := by
  refine isFlatOver_of_forall_isFlatOverAtPoint B S hS f F hF fun x => ?_
  obtain ⟨d, u, rfl⟩ := exists_chartDiagram_pointOfEtaleChart B S hS X.2 (schemeSpace W).2 f.hom x
  let α : (SmallEtale.toOver B S hS X.1).obj d.U ⟶ W :=
    Yoneda.fullyFaithful.preimage (d.U.1.hom ≫ f.hom)
  have hα : d.U.1.hom ≫ f.hom = yoneda.map α := (Yoneda.fullyFaithful.map_preimage _).symm
  exact (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f F hF
    (chartDiagramSelfChart f d.U α hα) u).2
    ((@isFlatOverAt_iff_isTorsionFreeOverAt _ _ _ _ u (hdom _) (hbez _)).2 (htf d.U α hα u))

/-- **Flatness and torsion freeness over a target with Bézout local rings agree.**  For an
object `W` of the big fppf site all of whose local rings are Bézout domains, a quasi-coherent
module on an algebraic space over `h_W` is flat over `h_W` (Stacks 05VV) exactly when it is
torsion free over `h_W`.  This is Stacks 0539 read on the étale scheme charts. -/
theorem isFlatOver_iff_isTorsionFreeOver {W : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace W)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hdom : ∀ w, IsDomain (((BigFppfOver.toScheme B S hS).obj W).presheaf.stalk w))
    (hbez : ∀ w, IsBezout (((BigFppfOver.toScheme B S hS).obj W).presheaf.stalk w)) :
    IsFlatOver B S hS X.2 f.hom F ↔ IsTorsionFreeOver B S hS X.2 f.hom F :=
  ⟨IsFlatOver.isTorsionFreeOver, fun h => isFlatOver_of_isTorsionFreeOver_restrictToChart f F hF
    hdom hbez fun U α hα => h (chartDiagramSelfChart f U α hα)⟩

/-! ### Over a valuation ring -/

/-- The local ring at a point `t` of a scheme isomorphic to `Spec R` is isomorphic to the
localization of `R` at the prime `p` corresponding to `t`. -/
noncomputable def stalkRingEquivOfIsoSpec {T : Scheme.{u}} {R : Type u} [CommRing R]
    (e : T ≅ Spec (CommRingCat.of R)) (t : T) (p : PrimeSpectrum R) (hp : e.hom.base t = p) :
    T.presheaf.stalk t ≃+* Localization.AtPrime p.asIdeal := by
  subst hp
  exact ((asIso (e.hom.stalkMap t)).symm ≪≫
    Spec.stalkIso (CommRingCat.of R) (e.hom.base t)).commRingCatIsoToRingEquiv

/-- Every local ring of a scheme isomorphic to the spectrum of a domain is a domain. -/
theorem isDomain_stalk_of_iso_spec {T : Scheme.{u}} {R : Type u} [CommRing R] [IsDomain R]
    (e : T ≅ Spec (CommRingCat.of R)) (t : T) : IsDomain (T.presheaf.stalk t) :=
  MulEquiv.isDomain _ (stalkRingEquivOfIsoSpec e t _ rfl).toMulEquiv

/-- Every local ring of a scheme isomorphic to the spectrum of a valuation ring is a valuation
ring: it is a localization of `R` at a prime. -/
theorem valuationRing_stalk_of_iso_spec {T : Scheme.{u}} {R : Type u} [CommRing R] [IsDomain R]
    [ValuationRing R] (e : T ≅ Spec (CommRingCat.of R)) (t : T) :
    haveI := isDomain_stalk_of_iso_spec e t
    ValuationRing (T.presheaf.stalk t) := by
  have := isDomain_stalk_of_iso_spec e t
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum R, e.hom.base t = p := ⟨_, rfl⟩
  have : ValuationRing (Localization.AtPrime p.asIdeal) :=
    ValuationRing.of_isLocalization p.asIdeal.primeCompl
  exact ValuationRing.of_ringEquiv (stalkRingEquivOfIsoSpec e t p hp)

/-- Every local ring of a scheme isomorphic to the spectrum of a valuation ring is Bézout. -/
private theorem isBezout_stalk_of_iso_spec {T : Scheme.{u}} {R : Type u} [CommRing R] [IsDomain R]
    [ValuationRing R] (e : T ≅ Spec (CommRingCat.of R)) (t : T) : IsBezout (T.presheaf.stalk t) :=
  have := isDomain_stalk_of_iso_spec e t
  have := valuationRing_stalk_of_iso_spec e t
  inferInstance

/-- **The flatness step of Stacks 0DM0, which is Stacks 0539 on an algebraic space.**  Let `R`
be a valuation ring and let `W` be an object of the big fppf site whose scheme is `Spec R`.  A
quasi-coherent module on an algebraic space over `h_W` is flat over `h_W` (Stacks 05VV) exactly
when it is torsion free over `h_W`: on every commuting square of étale scheme charts, the
stalks of its restriction to the source chart have no torsion over the local rings of the
target chart. -/
theorem isFlatOver_iff_isTorsionFreeOver_of_valuationRing {R : Type u} [CommRing R] [IsDomain R]
    [ValuationRing R] {W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (CommRingCat.of R))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace W)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    IsFlatOver B S hS X.2 f.hom F ↔ IsTorsionFreeOver B S hS X.2 f.hom F :=
  isFlatOver_iff_isTorsionFreeOver f F hF (isDomain_stalk_of_iso_spec e)
    (isBezout_stalk_of_iso_spec e)

/-- **A torsion free module over a valuation ring is flat, on an algebraic space.**  Let `R` be a
valuation ring and let `W` be an object of the big fppf site whose scheme is `Spec R`.  A
quasi-coherent module on an algebraic space `X` over `h_W` whose restriction to every étale
scheme chart `U` of `X` has stalks without torsion over the local rings of `Spec R`, through the
morphism `U ⟶ W` induced by `X ⟶ h_W`, is flat over `h_W` in the sense of Stacks 05VV.

This is the step of the proof of Stacks 0DM0 in which the finite type submodules of `j_*F_K` are
seen to be flat over `R` because they are torsion free, by Stacks 0539. -/
theorem isFlatOver_of_isTorsionFreeOver_restrictToChart_of_valuationRing {R : Type u}
    [CommRing R] [IsDomain R] [ValuationRing R] {W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ Spec (CommRingCat.of R))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace W)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (htf : ∀ (U : SmallEtale B S hS X.1) (α : (SmallEtale.toOver B S hS X.1).obj U ⟶ W),
      U.1.hom ≫ f.hom = yoneda.map α →
        AlgebraicGeometry.IsTorsionFreeOver
          (LocallyRingedSpace.forgetToSheafedSpace.map
            ((BigFppfOver.toScheme B S hS).map α).toLRSHom)
          (restrictToChart B S hS X.2 F U)) :
    IsFlatOver B S hS X.2 f.hom F :=
  isFlatOver_of_isTorsionFreeOver_restrictToChart f F hF (isDomain_stalk_of_iso_spec e)
    (isBezout_stalk_of_iso_spec e) htf

end AlgebraicGeometry.Space

end
