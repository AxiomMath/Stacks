module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeAffineOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.AffineFiniteProjective
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOnRingedSpaces
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tag 0F8T: an affine chart pulled back along a morphism of schemes

This file gives the route to part (1) of Stacks tag 0F8T that avoids the derived affine
comparison square of Stacks 08DW.  Part (1) itself, and parts (2) and (3), are
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullback`,
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullback_determinantalIdeal` and
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodTriple_pullback` of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback`.

Let `(U, A, f, M^•)` be an affine chart, `h : Y ⟶ X` a morphism of schemes, and
`V = Spec B ⊆ Y` an affine open with `h(V) ⊆ U`; write `φ : A ⟶ B` for the induced map on
sections and `d : V ⟶ U` for `AlgebraicGeometry.Scheme.Hom.resLE`.  The square

  `V ⟶ U`,  `V ≅ Spec B ⟶ Spec A ≅ U`

commutes by `AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE`, so pulling a sheaf of
`𝒪_U`-modules of the form `M^~` back along `d` is the sheaf of `B ⊗_A M`-modules on `V`.  This
is Stacks tag 01I9 (`AlgebraicGeometry.pullbackTildeIso`) transported to the two affine opens.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullbackRepresentsIsoOfKFlat`: the
  isomorphism in `D(𝒪_V)` that is the content of part (1) of the tag on this route — the
  restriction to `V` of the degreewise pullback of a K-flat complex representing `M` is the
  complex of sheaves of `M^• ⊗_A B`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.resLE_isoSpec`: the commuting square
  of the two affine opens.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.restrictPullbackTildeIso` and
  `.chartTildePullbackIso`: the affine dictionary conjugated by `U ≅ Spec A` and `V ≅ Spec B`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.isStrictlyPerfect_chartComplex`: the
  complex of `𝒪_U`-modules which a chart's bounded complex gives rise to is strictly perfect,
  hence K-flat.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullbackRestrictChartComplexIso` and
  `.pullbackChartComplexIso`: the two degreewise identifications the representation needs.

## Why Stacks 08DW is not needed

`M^•` is a bounded complex of finite *free* modules, so the complex of `𝒪_U`-modules it gives
rise to is strictly perfect, hence K-flat, and a K-flat complex computes the derived pullback
degreewise.  The derived affine comparison square of Stacks 08DW part (2)
(`AlgebraicGeometry.affinePullbackComparison`) therefore never appears: it collapses to the
degreewise Stacks 01I9.  Exactly one derived step survives, namely that degreewise pullback along
`d` computes `Ld^*` on the two K-flat complexes `P|_U` and the chart's complex of sheaves; that is
`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`, whose two model binders are free, so it is
available at `CategoryTheory.HasDerivedCategory.standard`, which is the model the affine chart's
`represents` field is stated at.

## References

* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- **The commuting square of the two affine opens of a pulled-back chart.**  The restriction
`d : V ⟶ U` of `h` to the two affine opens, followed by `U ≅ Spec Γ(X, U)`, is `V ≅ Spec Γ(Y, V)`
followed by the spectrum of the map `Γ(X, U) ⟶ Γ(Y, V)` induced by `h`. -/
theorem resLE_isoSpec (C : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X) (V : Y.affineOpens)
    (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens)) :
    h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV ≫ C.U.2.isoSpec.hom =
      V.2.isoSpec.hom ≫ Spec.map (h.appLE (C.U : S.X.Opens) (V : Y.Opens) hV) :=
  (Scheme.Opens.toSpecΓ_SpecMap_appLE h (C.U : S.X.Opens) (V : Y.Opens) hV).symm

/-- **Transport across the square of the two affine opens.**  Restricting along `U ≅ Spec A` and
then pulling back along `d : V ⟶ U` is pulling back along `Spec φ` and then restricting along
`V ≅ Spec B`.  Both restrictions are along isomorphisms, hence open immersions, so each is the
pullback along the same morphism by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and the two composites agree by
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.resLE_isoSpec`. -/
def restrictPullbackTildeIso (C : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens)) :
    Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom ⋙
        Scheme.Modules.pullback (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV) ≅
      Scheme.Modules.pullback (Spec.map (h.appLE (C.U : S.X.Opens) (V : Y.Opens) hV)) ⋙
        Scheme.Modules.restrictFunctor V.2.isoSpec.hom :=
  restrictIsoSpecPullbackIsoOfLE h C.U.2 V.2 hV

/-- **The affine dictionary on the two affine opens of a pulled-back chart.**  The functor
carrying an `A`-module to the sheaf of `𝒪_U`-modules it gives rise to and then pulling back along
`d : V ⟶ U` is extension of scalars to `B` followed by the sheaf of `𝒪_V`-modules it gives rise
to.  This is Stacks tag 01I9 (`AlgebraicGeometry.pullbackTildeIso`) conjugated by the two
isomorphisms `U ≅ Spec A` and `V ≅ Spec B`. -/
def chartTildePullbackIso (C : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens)) :
    (tilde.functor Γ(S.X, C.U) ⋙ Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom) ⋙
        Scheme.Modules.pullback (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV) ≅
      ModuleCat.extendScalars (h.appLE (C.U : S.X.Opens) (V : Y.Opens) hV).hom ⋙
        (tilde.functor Γ(Y, (V : Y.Opens)) ⋙
          Scheme.Modules.restrictFunctor V.2.isoSpec.hom) :=
  restrictPullbackTildeIsoOfLE h C.U.2 V.2 hV

/-! ### Strict perfection of the complex of sheaves of a chart -/

/-- Strict perfection transported backwards along an isomorphism of complexes. -/
theorem isStrictlyPerfect_of_iso {X : RingedSpace.{u, u}}
    {K L : CochainComplex (OXMod.{u, u} X) ℤ} (e : K ≅ L) (h : IsStrictlyPerfect L) :
    IsStrictlyPerfect K where
  bounded := h.bounded.subset fun i hi hz =>
    hi (((HomologicalComplex.eval _ _ i).mapIso e).isZero_iff.2 hz)
  directSummand i :=
    isDirectSummandOfFiniteFree_of_iso ((HomologicalComplex.eval _ _ i).mapIso e)
      (h.directSummand i)

/-- Only finitely many terms of the cochain complex of a bounded complex of finite free modules
are nonzero: a term of rank zero is the zero module. -/
theorem finite_nonzero_toCochainComplex {A : Type u} [CommRing A] (M : BoundedComplex A) :
    {i : ℤ | ¬ IsZero (M.toCochainComplex.X i)}.Finite :=
  M.bounded.subset fun i hi hr => hi (by
    rw [BoundedComplex.toCochainComplex_X, hr]
    exact ModuleCat.isZero_of_subsingleton _)

/-- **The complex of `𝒪_{Spec A}`-modules of a bounded complex of finite free `A`-modules is
strictly perfect.**  Each term is `A^{r_i}`, which is finite free, and only finitely many terms
are nonzero. -/
theorem isStrictlyPerfect_tilde_toCochainComplex (A : CommRingCat.{u})
    (M : BoundedComplex A) :
    IsStrictlyPerfect (X := (Spec A).toRingedSpace)
      (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        M.toCochainComplex) :=
  Stacks.AffineTilde.isStrictlyPerfect_tildeComplex_of_projective M.toCochainComplex
    (finite_nonzero_toCochainComplex M) fun i => by
      rw [BoundedComplex.toCochainComplex_X]
      exact ⟨inferInstance, inferInstance⟩

/-- **The complex of `𝒪_U`-modules a chart's bounded complex gives rise to is strictly
perfect**, hence K-flat.  It is the pullback along `U ≅ Spec Γ(X, U)` of the strictly perfect
complex `\widetilde{M^•}` on `Spec Γ(X, U)`, and termwise pullback preserves strict perfection by
`Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback`. -/
theorem isStrictlyPerfect_chartComplex (C : AffineChart S) :
    IsStrictlyPerfect (X := (C.U : S.X.Opens).toScheme.toRingedSpace)
      (((tilde.functor Γ(S.X, C.U) ⋙
        Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C.complex.toCochainComplex) := by
  refine isStrictlyPerfect_of_iso
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor Γ(S.X, C.U) ⋙
        Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom))
      (ComplexShape.up ℤ)).app C.complex.toCochainComplex).symm ?_
  refine isStrictlyPerfect_of_iso
    ((NatIso.mapHomologicalComplex
      (Scheme.Modules.restrictFunctorIsoPullback C.U.2.isoSpec.hom)
      (ComplexShape.up ℤ)).app _) ?_
  exact Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback
    C.U.2.isoSpec.hom.toLRSHom.toShHom _
    (isStrictlyPerfect_tilde_toCochainComplex Γ(S.X, C.U) C.complex)

/-! ### The square of degreewise pullbacks -/

/-- **Pulling a complex of `𝒪_X`-modules back along `h` and restricting it to `V` is restricting
it to `U` and pulling it back along `d : V ⟶ U`.**  Both restrictions are pullbacks along the
inclusions of the open subschemes, and `V ⟶ Y ⟶ X` equals `V ⟶ U ⟶ X` by
`AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`. -/
def pullbackRestrictChartIso (C : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens)) :
    Scheme.Modules.pullback h ⋙ Scheme.Modules.restrictFunctor (V : Y.Opens).ι ≅
      Scheme.Modules.restrictFunctor (C.U : S.X.Opens).ι ⋙
        Scheme.Modules.pullback (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback h)
      (Scheme.Modules.restrictFunctorIsoPullback (V : Y.Opens).ι) ≪≫
    Scheme.Modules.pullbackComp (V : Y.Opens).ι h ≪≫
    Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι h hV).symm ≪≫
    (Scheme.Modules.pullbackComp (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV)
      (C.U : S.X.Opens).ι).symm ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.restrictFunctorIsoPullback (C.U : S.X.Opens).ι).symm
      (Scheme.Modules.pullback (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV))

/-- The same at a fixed complex. -/
def pullbackRestrictChartComplexIso (C : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens))
    (P : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ) :
    ((Scheme.Modules.restrictFunctor (V : Y.Opens).ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.pullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      ((Scheme.Modules.pullback
            (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.restrictFunctor (C.U : S.X.Opens).ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (Scheme.Modules.pullback h ⋙
        Scheme.Modules.restrictFunctor (V : Y.Opens).ι)) (ComplexShape.up ℤ)).app P ≪≫
    (NatIso.mapHomologicalComplex (C.pullbackRestrictChartIso h V hV)
      (ComplexShape.up ℤ)).app P ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (Scheme.Modules.restrictFunctor (C.U : S.X.Opens).ι ⋙
        Scheme.Modules.pullback (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV)))
      (ComplexShape.up ℤ)).app P).symm

/-- **The chart's complex of sheaves, pulled back to `V`, is the complex of sheaves of the base
change `M^• ⊗_A B`.**  This is
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.chartTildePullbackIso` at the chart's
bounded complex, followed by
`Stacks.Eta.DeterminantalIdeal.baseChangeCochainIso` identifying the extension of scalars of the
cochain complex of `M^•` with the cochain complex of `M^• ⊗_A B`. -/
def pullbackChartComplexIso (C : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens)) :
    ((Scheme.Modules.pullback
          (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((tilde.functor Γ(S.X, C.U) ⋙
        Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C.complex.toCochainComplex) ≅
      ((tilde.functor Γ(Y, (V : Y.Opens)) ⋙
        Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (C.complex.baseChange
          (h.appLE (C.U : S.X.Opens) (V : Y.Opens) hV).hom).toCochainComplex :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl ((tilde.functor Γ(S.X, C.U) ⋙
        Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom) ⋙
        Scheme.Modules.pullback (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV)))
      (ComplexShape.up ℤ)).app C.complex.toCochainComplex ≪≫
    (NatIso.mapHomologicalComplex (C.chartTildePullbackIso h V hV)
      (ComplexShape.up ℤ)).app C.complex.toCochainComplex ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars
          (h.appLE (C.U : S.X.Opens) (V : Y.Opens) hV).hom ⋙
        (tilde.functor Γ(Y, (V : Y.Opens)) ⋙
          Scheme.Modules.restrictFunctor V.2.isoSpec.hom)))
      (ComplexShape.up ℤ)).app C.complex.toCochainComplex).symm ≪≫
    ((tilde.functor Γ(Y, (V : Y.Opens)) ⋙
      Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso
      (Stacks.Eta.DeterminantalIdeal.baseChangeCochainIso
        (h.appLE (C.U : S.X.Opens) (V : Y.Opens) hV).hom C.complex)

/-! ### The chart pulled back along a general morphism -/

section Represents

attribute [local instance 10000] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

/-- **The restriction of a K-flat complex to an open subscheme is K-flat.**  Restriction along
an open immersion is pullback along it, and pullback preserves K-flatness by Stacks 06YC. -/
theorem kFlat_restrictFunctor {X : Scheme.{u}} (U : X.Opens)
    (P : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ) (hP : KFlat X.toRingedSpace P) :
    KFlat U.toScheme.toRingedSpace
      (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  kFlat_of_iso
    (Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional
      U.ι.toLRSHom.toShHom P hP)
    ((NatIso.mapHomologicalComplex (Scheme.Modules.restrictFunctorIsoPullback U.ι)
      (ComplexShape.up ℤ)).app P).symm

/-- **The representation of the pulled-back chart, without Stacks 08DW.**  Let `(U, A, f, M^•)`
be an affine chart for `(X, D, M)`, let `h : Y ⟶ X` be a morphism of schemes, let `V = Spec B`
be an affine open of `Y` with `h(V) ⊆ U`, and let `P` be a K-flat complex of `𝒪_X`-modules whose
restriction to `U` is identified in `D(𝒪_U)` with the complex of sheaves of `M^•`.  Then the
restriction to `V` of the degreewise pullback `h^*P` is isomorphic, in `D(𝒪_V)`, to the complex
of sheaves of the base change `M^• ⊗_A B`.

This is the content of part (1) of Stacks tag 0F8T on this file's route, and the counterpart of
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullbackRepresentsIso`, which gets the
same conclusion for an arbitrary complex representing `Lh^*M` out of the derived affine
comparison square of Stacks 08DW.  Here 08DW never appears: the restriction of `h^*P` to `V` is
the degreewise pullback along `d : V ⟶ U` of `P|_U`
(`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullbackRestrictChartComplexIso`);
both `P|_U` and the chart's complex of sheaves are K-flat — the first because pullback preserves
K-flatness, the second because it is strictly perfect, `M^•` being a bounded complex of finite
free modules — so degreewise pullback along `d` computes `Ld^*` on each and the given
identification transports; and the result is the complex of sheaves of `M^• ⊗_A B` by
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullbackChartComplexIso`, which is the
degreewise Stacks 01I9. -/
def pullbackRepresentsIsoOfKFlat (C : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens))
    (P : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ)
    (hP : KFlat S.X.toRingedSpace P)
    (e : DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor (C.U : S.X.Opens).ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj
        (((tilde.functor Γ(S.X, C.U) ⋙
          Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C.complex.toCochainComplex)) :
    DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor (V : Y.Opens).ι).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((Scheme.Modules.pullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≅
      DerivedCategory.Q.obj
        (((tilde.functor Γ(Y, (V : Y.Opens)) ⋙
          Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (C.complex.baseChange
            (h.appLE (C.U : S.X.Opens) (V : Y.Opens) hV).hom).toCochainComplex) :=
  DerivedCategory.Q.mapIso (C.pullbackRestrictChartComplexIso h V hV P) ≪≫
    (Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat
      (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV).toLRSHom.toShHom _
      (kFlat_restrictFunctor (C.U : S.X.Opens) P hP)).symm ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV).toLRSHom.toShHom).mapIso e ≪≫
    Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat
      (h.resLE (C.U : S.X.Opens) (V : Y.Opens) hV).toLRSHom.toShHom _
      (kFlat_of_isStrictlyPerfect _ C.isStrictlyPerfect_chartComplex) ≪≫
    DerivedCategory.Q.mapIso (C.pullbackChartComplexIso h V hV)

end Represents

end AffineChart

end AlgebraicGeometry.ComplexAndDivisorSituation

-- Part (2) of Stacks tag 0F8T, read on the pulled-back chart, is
-- `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullback_determinantalIdeal` of
-- `StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback`; this records the tag on
-- it there.
add_to_stacks 0F8T "part (2) for a general `h`: the determinantal ideals of the chart base-changed \
along the ring map induced by `h` on the two affine opens"
  AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullback_determinantalIdeal

end
