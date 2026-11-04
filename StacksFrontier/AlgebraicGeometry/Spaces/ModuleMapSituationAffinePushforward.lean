module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationAffineAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksCore.Tactic.StacksAttribute

/-!
# The base-change loci of a map of modules under an affine direct image

In Situation Stacks 083F — a morphism `f : X ⟶ Y` of algebraic spaces and a map `u : F ⟶ G`
of quasi-coherent `𝒪_X`-modules — let `g : X ⟶ X'` be an affine morphism over `Y`, and let
`u' = g_*u : g_*F ⟶ g_*G` be the direct image, a map of quasi-coherent `𝒪_{X'}`-modules.
**Stacks 0CW8** says that the four loci of `u` and of `u'` agree:
`F_{u,iso} = F_{u',iso}`, `F_{u,inj} = F_{u',inj}`, `F_{u,surj} = F_{u',surj}` and
`F_{u,zero} = F_{u',zero}`.

`StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationAffine` proves the four equalities from
an input `AlgebraicGeometry.Space.ModuleMapSituation.PushforwardIdentifiesBaseChange` at every
test scheme, and builds the situation of `u'` from the scheme-target case of the
quasi-coherence clause of Stacks 07U8.  This file discharges both, so the four equalities below
take exactly the hypotheses of the source.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.pushforwardIdentifiesBaseChange`: the input holds
  at every test scheme `T`.  The direct image along `g_T` carries `u_T` to `u'_T`, up to the base
  change isomorphisms of Stacks 07U8 for the cartesian square
  `AlgebraicGeometry.Space.ModuleMapSituation.isPullback_affinePushforwardBaseChange`
  (`AlgebraicGeometry.Space.nonempty_arrowIso_modulePullback_map_modulePushforward_map`); and
  `g_T` is affine (Stacks 03WI), so its direct image detects isomorphisms, monomorphisms,
  epimorphisms and vanishing of maps of quasi-coherent modules
  (`StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness`).
* `AlgebraicGeometry.Space.ModuleMapSituation.isoFunctor_affinePushforward_eq_unconditional`,
  `.injFunctor_affinePushforward_eq_unconditional`,
  `.surjFunctor_affinePushforward_eq_unconditional` and
  `.zeroFunctor_affinePushforward_eq_unconditional`: **Stacks 0CW8**, with no hypothesis beyond
  the source's: `g` affine and over `Y`.

## Implementation notes

The situation of `u'` is `AlgebraicGeometry.Space.ModuleMapSituation.affinePushforward`, whose
quasi-coherence argument is supplied by the theorem
`AlgebraicGeometry.Space.schemeTargetAffinePushforwardQuasicoherent`, so no hypothesis remains.

The base change `u'_T` is compared with the inverse image of `g_*u` through
`AlgebraicGeometry.Space.ModuleMapSituation.arrow_mk_affinePushforward_baseChangeHom`, and the
cartesian square is restated with the projection of the situation of `u'`
(`isPullback_affinePushforwardBaseChange'`): elaborating the comparison against the
`ObjectProperty.homMk` spelling of the same projection times out, although the two are
definitionally equal.

## References

* [Stacks Project, Tag 0CW8](https://stacks.math.columbia.edu/tag/0CW8)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : ModuleMapSituation.{u, u} B S hS) {X' : AlgebraicSpaces B S hS} (g : D.X ⟶ X')
  (f' : X' ⟶ D.Y)

/-- The base change `u'_T` of `u' = g_*u` is the inverse image of `g_*u` along the projection
`X' ×_Y T ⟶ X'`. -/
theorem arrow_mk_affinePushforward_baseChangeHom
    (h07U8 : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (hg : IsAffineHom B S hS g.hom) (T : D.SchemesOver) :
    Arrow.mk ((D.affinePushforward g f' h07U8 hg).baseChangeHom (modulePullbackSystem B S hS) T) =
      Arrow.mk ((modulePullback B S hS ((D.affinePushforward g f' h07U8 hg).baseChangeProjection
        T)).map ((modulePushforward B S hS g).map D.u)) := rfl

/-- The cartesian square of
`AlgebraicGeometry.Space.ModuleMapSituation.isPullback_affinePushforwardBaseChange`, with the
projection `X' ×_Y T ⟶ X'` spelled as the projection of the situation of `u' = g_*u`. -/
theorem isPullback_affinePushforwardBaseChange'
    (h07U8 : SchemeTargetAffinePushforwardQuasicoherent B S hS) (hg : IsAffineHom B S hS g.hom)
    (comm : g ≫ f' = D.f) (T : D.SchemesOver) :
    IsPullback (Y := (D.affinePushforward g f' h07U8 hg).baseChangeSpace T)
      (D.baseChangeProjection T) (D.affinePushforwardBaseChange g f' comm T) g
      ((D.affinePushforward g f' h07U8 hg).baseChangeProjection T) :=
  D.isPullback_affinePushforwardBaseChange g f' comm T

variable (hg : IsAffineHom B S hS g.hom) (comm : g ≫ f' = D.f)

include comm in
/-- **The input `PushforwardIdentifiesBaseChange` of the conditional form of Stacks 0CW8 holds at
every test scheme**: the base change maps of Stacks 07U8 identify `u'_T` with `g_{T,*}u_T`, and
the direct image along the affine `g_T` detects the four conditions on maps of quasi-coherent
modules. -/
theorem pushforwardIdentifiesBaseChange (T : D.SchemesOver) :
    D.PushforwardIdentifiesBaseChange g f' (schemeTargetAffinePushforwardQuasicoherent B S hS) hg
      comm T := by
  have sq := D.isPullback_affinePushforwardBaseChange' g f'
    (schemeTargetAffinePushforwardQuasicoherent B S hS) hg comm T
  have hA := D.arrow_mk_affinePushforward_baseChangeHom g f'
    (schemeTargetAffinePushforwardQuasicoherent B S hS) hg T
  have hgT : IsAffineHom B S hS (D.affinePushforwardBaseChange g f' comm T).hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq) hg
  have hFT := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.baseChangeProjection T) D.F D.quasicoherent_F
  have hGT := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.baseChangeProjection T) D.G D.quasicoherent_G
  exact ⟨⟨eqToIso hA ≪≫ (nonempty_arrowIso_modulePullback_map_modulePushforward_map sq hg D.u
      D.quasicoherent_F D.quasicoherent_G).some⟩,
    isIso_modulePushforward_map_iff_of_isAffineHom _ hgT hFT hGT _,
    mono_modulePushforward_map_iff_of_isAffineHom _ hgT hFT hGT _,
    epi_modulePushforward_map_iff_of_isAffineHom _ hgT hFT hGT _,
    modulePushforward_map_eq_zero_iff_of_isAffineHom _ hgT hFT _⟩

include comm

/-- **Stacks 0CW8**, `F_{u,iso} = F_{u',iso}`: for an affine morphism `g : X ⟶ X'` over `Y`,
the isomorphism locus of `u` is that of its direct image `u' = g_*u`. -/
@[stacks 0CW8 "F_iso"]
theorem isoFunctor_affinePushforward_eq_unconditional :
    (D.affinePushforward g f' (schemeTargetAffinePushforwardQuasicoherent B S hS) hg).isoFunctor
        (modulePullbackSystem B S hS) =
      D.isoFunctor (modulePullbackSystem B S hS) :=
  D.isoFunctor_affinePushforward_eq g f' _ hg comm
    (D.pushforwardIdentifiesBaseChange g f' hg comm)

/-- **Stacks 0CW8**, `F_{u,inj} = F_{u',inj}`: for an affine morphism `g : X ⟶ X'` over `Y`,
the universal-injectivity locus of `u` is that of its direct image `u' = g_*u`. -/
@[stacks 0CW8 "F_inj"]
theorem injFunctor_affinePushforward_eq_unconditional :
    (D.affinePushforward g f' (schemeTargetAffinePushforwardQuasicoherent B S hS) hg).injFunctor
        (modulePullbackSystem B S hS) =
      D.injFunctor (modulePullbackSystem B S hS) :=
  D.injFunctor_affinePushforward_eq g f' _ hg comm
    (D.pushforwardIdentifiesBaseChange g f' hg comm)

/-- **Stacks 0CW8**, `F_{u,surj} = F_{u',surj}`: for an affine morphism `g : X ⟶ X'` over `Y`,
the surjectivity locus of `u` is that of its direct image `u' = g_*u`. -/
@[stacks 0CW8 "F_surj"]
theorem surjFunctor_affinePushforward_eq_unconditional :
    (D.affinePushforward g f' (schemeTargetAffinePushforwardQuasicoherent B S hS) hg).surjFunctor
        (modulePullbackSystem B S hS) =
      D.surjFunctor (modulePullbackSystem B S hS) :=
  D.surjFunctor_affinePushforward_eq g f' _ hg comm
    (D.pushforwardIdentifiesBaseChange g f' hg comm)

/-- **Stacks 0CW8**, `F_{u,zero} = F_{u',zero}`: for an affine morphism `g : X ⟶ X'` over `Y`,
the vanishing locus of `u` is that of its direct image `u' = g_*u`. -/
@[stacks 0CW8 "F_zero"]
theorem zeroFunctor_affinePushforward_eq_unconditional :
    (D.affinePushforward g f' (schemeTargetAffinePushforwardQuasicoherent B S hS) hg).zeroFunctor
        (modulePullbackSystem B S hS) =
      D.zeroFunctor (modulePullbackSystem B S hS) :=
  D.zeroFunctor_affinePushforward_eq g f' _ hg comm
    (D.pushforwardIdentifiesBaseChange g f' hg comm)

end ModuleMapSituation

end AlgebraicGeometry.Space

end
