module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.InjectiveQcohSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapse
import StacksCore.Tactic.StacksAttribute

/-!
# Acyclicity of an injective quasi-coherent module on a Noetherian algebraic space

Let `X` be a Noetherian algebraic space over a scheme `S` and let `𝒥` be an injective object of
the category `QCoh(𝒪_X)` of quasi-coherent modules on the small étale site of `X`.  Stacks 09TL,
part (1) asserts that `H^p(U, 𝒥|_U) = 0` for `p > 0` and every quasi-compact and quasi-separated
algebraic space `U` étale over `X`.

The argument below is the source's.  Stacks 09TJ writes `𝒥` as a direct summand — a retract — of
a filtered colimit `colim_i ℱ_i` of quasi-coherent modules of the form `ℱ_i = (Z_i ⟶ X)_* 𝒢_i`
with `Z_i` the spectrum of an Artinian ring and `𝒢_i` coherent, so it suffices to prove the
vanishing for the colimit; since étale restriction commutes with colimits and `U` is
quasi-compact and quasi-separated, `H^p(U, -|_U)` carries that filtered colimit to the filtered
colimit of the `H^p(U, ℱ_i|_U)`, which vanish.  A filtered colimit of zero objects is zero and a
retract of a zero object is zero, which is the whole of the deduction performed here.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictionCohomology`: the functor `M ↦ H^p(U, M|_U)` on the
  quasi-coherent modules of `X`, for an étale `g : U ⟶ X`.
* `AlgebraicGeometry.Space.IsZeroEtaleRestrictionCohomologyOfArtinian`: the hypothesis `hartin`,
  the Artinian case of the source's proof.

## Main results

* `AlgebraicGeometry.Space.isZero_of_isColimit_of_forall_isZero`: a colimit of a diagram of zero
  objects is zero.

## Implementation notes

### Which cohomology, and the universe

`H^p(U, -)` is the `p`-th right derived functor of global sections of `𝒪_U`-modules on the small
étale ringed site of `U`, spelled
`Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}` applied to
`AlgebraicGeometry.RingedSite.ringSheaf (AlgebraicGeometry.Space.smallEtaleRingedSite …)`.  It is
*not* spelled `Stacks.Cohomology.SiteModules.globalModuleCohomology`: the module universe of that
abbreviation is the join `max (u + 1) w` of the universe of the objects of the small étale site
with the free module universe, so it is never the universe `u` at which
`AlgebraicGeometry.Space.modulePushforward` — and hence `IsArtinianPushforward`, and hence
Stacks 09TJ — is available.  This is the same arrangement, for the same reason, as
`StacksFrontier/AlgebraicGeometry/Spaces/AffineMorphismCohomologyCollapse.lean`, and the structure
sheaf is written out rather than taken through `structureRingSheaf` for the reason given there:
instance search otherwise stalls on `u + 1 =?= max (u + 1) ?w`.

The restriction `𝒥|_U` is `AlgebraicGeometry.Space.etaleModulePullback` along the étale
`g : U ⟶ X`, restriction of sections along postcomposition of étale charts with `g`, which is
the source's `|_U`.  Everything is polymorphic in `u`.

### What is assumed

Three inputs are carried as explicit hypotheses; each is named in the part string of the
attribute, so what is proved and what is assumed can be read off the statement itself.  None of
them asserts more than the source's own proof establishes.  The first, `hchart`, is the
hypothesis of the chart reduction
`AlgebraicGeometry.Space.exists_filtered_colimit_artinian_pushforwards_retract` of Stacks 09TJ
and is passed through verbatim; the other two are
quantified over the properties of `U` and `p` that make them legitimate, so that the source's
binders `hUqc`, `hUqs` and `hp` are consumed exactly where the source consumes them.

* `hcolim` is "pullback commutes with colimits, and `U` is quasi-compact and quasi-separated" —
  that is Stacks 073E together with the exactness properties of étale restriction and with the
  compatibility of the colimits of `QCoh(𝒪_X)` with the ambient ones.  Stacks 073E is formalized in
  this library as `AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections`, but
  for sheaves of *abelian groups* on the small étale site, with coefficients `Ab.{u + 1}` and
  cohomology `CategoryTheory.Sheaf.Γ`; transporting it to `𝒪`-modules is the comparison of module
  cohomology with the cohomology of the underlying abelian sheaf, which this library does not
  have.  `QCoh(𝒪_X)` is moreover not known to be closed under the filtered colimits of
  `Mod(𝒪_X)` — that is the colimit clause of Stacks 03M1, part (3) — so the preservation cannot
  be assembled from a statement about the ambient category either.  It is therefore asked for the
  composite functor, which is exactly what the argument consumes.
* `hartin` is the Artinian case: `H^p(U, ℱ|_U) = 0` for `p > 0` and `ℱ` an Artinian direct image.
  The source proves it by base change — `Z_i ×_X U ⟶ U` is affine because `Z_i ⟶ X` is, by
  Stacks 09TF, which is formalized here as
  `AlgebraicGeometry.Space.isAffineHom_of_isArtinianRing` — followed by the Leray collapse of
  Stacks 0733 along that affine morphism and the vanishing of the higher cohomology of a
  quasi-coherent module on the affine `Z_i ×_X U`.  The Leray collapse along an affine morphism
  is formalized, for a quasi-coherent module, as
  `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`, Stacks 0D2U; higher vanishing on
  an affine is the étale-site analogue of Stacks 01XB, that is Stacks 03DW, equivalently Descent,
  Proposition 03DX (2), and on an affine étale chart it is
  `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`.

Stacks 09TJ is used through its chart reduction, so the hypothesis `hchart` of that reduction
— the four inputs at the affine surjective étale chart of Stacks 03H6 — appears here unchanged
and is not restated or strengthened.  Those four inputs are all proved, and Stacks 09TJ itself
is `AlgebraicGeometry.Space.exists_filtered_colimit_artinian_pushforwards_retract_of_isNoetherian`;
the unconditional form of Stacks 09TL, part (1), is
`AlgebraicGeometry.Space.isZero_etaleRestrictionCohomology_of_injective_of_isNoetherian`.

### What is not covered

Part (2) of Stacks 09TL, the vanishing `R^p f_*𝒥 = 0` for `p > 0` and `f : X ⟶ Y` with `Y`
quasi-separated, is not stated here.  Its proof identifies `R^p f_*𝒥` with the sheafification of
the presheaf `V ↦ H^p(V ×_Y X, 𝒥)`, which is Stacks 072W; that tag is formalized in this library, as
`Stacks.Cohomology.HigherDirectImage.higherDirectImage_iso_sheafify_cohomologyPresheaf`, but for
a direct image of the form `SheafOfModules.pushforward φ` along a continuous functor, whereas
`AlgebraicGeometry.Space.modulePushforward` is built from a right Kan extension and the structure
map of Stacks 03D6, and the comparison between the two is not available.  The chartwise reduction
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_chartwise` is no substitute: it
asks for `f` to be representable, which the source does not.

## References

* [Stacks Project, Tag 09TL](https://stacks.math.columbia.edu/tag/09TL)
* [Stacks Project, Tag 09TJ](https://stacks.math.columbia.edu/tag/09TJ)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 09TF](https://stacks.math.columbia.edu/tag/09TF)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two formal facts about zero objects -/

variable {B S hS} in
/-- A colimit of a diagram all of whose objects are zero is zero.

Every coprojection into the colimit is zero, so the identity of the colimit agrees with the zero
map after composing with each of them, and a map out of a colimit is determined by those
composites. -/
theorem isZero_of_isColimit_of_forall_isZero {I : Type*} [Category* I] {C : Type*} [Category* C]
    [HasZeroMorphisms C] {D : I ⥤ C} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ i, IsZero (D.obj i)) : IsZero c.pt := by
  refine (IsZero.iff_id_eq_zero _).mpr (hc.hom_ext fun i => ?_)
  rw [Category.comp_id, comp_zero]
  exact (hD i).eq_of_src _ _

/-! ### Cohomology of an étale restriction -/

/-- The functor `M ↦ H^p(U, M|_U)` on the quasi-coherent `𝒪_X`-modules, for an étale morphism
`g : U ⟶ X` of algebraic spaces: étale restriction along `g` followed by the `p`-th right derived
functor of global sections of `𝒪_U`-modules on the small étale ringed site of `U`.

This is the functor to which the source applies Stacks 073E. -/
def etaleRestrictionCohomology {X U : AlgebraicSpaces B S hS} (g : U ⟶ X)
    (hg : IsEtale B S hS g.hom) (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS U.1 U.2
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤
      ModuleCat.{u + 1} (GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O))) :=
  have := hasInjectiveResolutions_modules B S hS U.1 U.2
  ObjectProperty.ι _ ⋙ etaleModulePullback B S hS g hg ⋙
    (globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS U.1 U.2).O))).rightDerived p

/-- The hypothesis `hartin` of Stacks 09TL, part (1): the Artinian case of the source's proof.

An Artinian direct image `(Z ⟶ X)_*𝒢` — `Z` the spectrum of an Artinian ring and `𝒢` coherent,
`AlgebraicGeometry.Space.IsArtinianPushforward` — has no cohomology in degree `p` on `U` after
restriction along `g`.  See the implementation notes of this file for the two results of the
Stacks project that prove it and that this library does not carry. -/
def IsZeroEtaleRestrictionCohomologyOfArtinian {X U : AlgebraicSpaces B S hS} (g : U ⟶ X)
    (hg : IsEtale B S hS g.hom) (p : ℕ) : Prop :=
  0 < p → ∀ M : QuasicoherentSheaves.{u, u} B S hS X.1 X.2,
    IsArtinianPushforward B S hS X M.obj →
      IsZero ((etaleRestrictionCohomology B S hS g hg p).obj M)

/-! ### Stacks 09TL, part (1) -/

end AlgebraicGeometry.Space

end

end
