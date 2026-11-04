module

public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction

/-!
# Higher direct images of quasi-coherent modules are quasi-coherent

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  If `f` is quasi-compact and quasi-separated then every higher direct image `R^i f_*`
carries a quasi-coherent `𝒪_X`-module to a quasi-coherent `𝒪_Y`-module, for every `i`.  This is
Stacks 0720, and it is the statement below.

The source's proof has two steps.  The first is the reduction to the case of an affine base:
quasi-coherence of an `𝒪_Y`-module is tested on the affine étale scheme charts `V` of `Y`, and
over such a chart `R^i f_*F` restricts to `R^i f'_*(F|_U)` for `U = V ×_Y X` and `f' : U ⟶ V`
the base change of `f`.  That step is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart`.  The second
step is the affine-base case itself, proved in the source by induction on `i` from the relative
Leray spectral sequence of an affine étale cover of `X`; it is carried here as the hypothesis
`haffine`, in the shape `AlgebraicGeometry.Space.AffineTargetHigherPushforwardQuasicoherent`.

## Main definitions

* `AlgebraicGeometry.Space.AffineTargetHigherPushforwardQuasicoherent` is the affine-base case of
  Stacks 0720 in degree `i`: the same conclusion for every quasi-compact and quasi-separated
  morphism of algebraic spaces whose target is an affine algebraic space.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward`: **Stacks 0720**
  in the binders of its source statement, granted the affine-base case and the
  injective-preservation half of Stacks 03F3 for the chart base changes of `f`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_representable`:
  the same conclusion for a *representable* `f`, granted the affine-base case alone.
* `AlgebraicGeometry.Space.affineTargetHigherPushforwardQuasicoherent_of_forall`: the affine-base
  case follows from the general statement, so the hypothesis `haffine` is no stronger than the
  conclusion it is used to reach.

## Implementation notes

The `@[stacks 0720]` attribute is **qualified**: it claims the reduction of the source's
statement to an affine base, not the affine case, which is the hypothesis `haffine`; Stacks 0720
without any qualifier is the conclusion below with `haffine` and `h03F3` discharged.  The
arrangement follows `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom`
for Stacks 073H and `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom`
for Stacks 07U8, which withhold their affine cases in the same way.

*Why `haffine` cannot be discharged here.*  The source's induction consumes three results that
this development does not have in a form that applies to modules on the small étale site of an
algebraic space: the comparison of étale with Zariski higher direct images for quasi-coherent
modules (Stacks 03DW, equivalently Stacks 03DX, part (2)), of which only the Zariski half is
present; the relative Leray spectral sequence of Stacks 0734, which is proved for a ringed topos
whose three universes agree, whereas the small étale site of an algebraic space over a
`Scheme.{u}` has its objects in `Type (u + 1)` and its modules at `u`; and the extension clause of
the weak Serre subcategory of quasi-coherent modules, Stacks 03M1, part (4), of which the kernel
and cokernel clauses are unconditional but the extension clause is proved nowhere.

*Why `haffine` is the smallest hypothesis of its shape.*  It restricts the conclusion to an
affine target and keeps both of the source's hypotheses on the morphism, and
`AlgebraicGeometry.Space.affineTargetHigherPushforwardQuasicoherent_of_forall` shows it to be a
consequence of the tag's own statement.  Quasi-compactness of the source, which the source's
second step also uses, is not assumed: for an affine target it follows from quasi-compactness of
the morphism, by `AlgebraicGeometry.Space.isQuasiCompactSpace_chartBaseChange`.

*What `h03F3` is.*  The first step identifies `(R^i f_*F)|_V` with `R^i f'_*(F|_U)` by base change
for right derived functors, which needs étale restriction along the structure morphism
`U ⟶ X` to carry injective `𝒪_X`-modules to injective `𝒪_U`-modules — Stacks 03F3, part (1), at
the small étale site.  That is proved for the structure morphism of an étale scheme *chart*, and
`U = V ×_Y X` is a scheme chart of `X` exactly when `f` is representable, which is why the
representable form below carries nothing beyond `haffine`.

*The degree* runs over all of `ℕ` in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`, the convention the source's proof is written in.  *The
module universe* is the universe `u` of the schemes, because
`AlgebraicGeometry.Space.modulePushforward` exists only there.  *The two local priority raises*
are those of `StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardEtaleBaseChange.lean`:
instance search for `Abelian` and for `EnoughInjectives` on the modules at module universe `u`
otherwise commits to the module-universe-`max u v r w` instances in the import closure and then
fails on the universe constraint.  Both attributes are `local`.

## References

* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The affine-base case of Stacks 0720 -/

/-- The affine-base case of Stacks 0720 in degree `i`: for every quasi-compact and
quasi-separated morphism `g : U ⟶ Y` of algebraic spaces over `S` whose target is an affine
algebraic space, and every quasi-coherent `𝒪_U`-module `G`, the higher direct image
`R^i g_*G` is quasi-coherent.

This is the second step of the source's proof of Stacks 0720, the step carried out there by
induction on `i` from the relative Leray spectral sequence of an affine étale cover of `U`. -/
def AffineTargetHigherPushforwardQuasicoherent (i : ℕ) : Prop :=
  ∀ (U Y : AlgebraicSpaces B S hS) (g : U ⟶ Y), IsAffineSpace B S hS Y.1 →
    IsQuasiCompact B S hS g.hom → IsQuasiSeparated B S hS g.hom →
    ∀ G : Modules.{u, u} B S hS U.1 U.2, G.IsQuasicoherentOnSite →
      have := hasInjectiveResolutions_modules B S hS U.1 U.2
      (((modulePushforward B S hS g).rightDerived i).obj G).IsQuasicoherentOnSite

/-- The affine-base case of Stacks 0720 is a consequence of the statement of Stacks 0720, an
affine algebraic space being in particular an algebraic space.  So the hypothesis `haffine`
below is no stronger than the conclusion it is used to reach. -/
theorem affineTargetHigherPushforwardQuasicoherent_of_forall (i : ℕ)
    (h : ∀ (U Y : AlgebraicSpaces B S hS) (g : U ⟶ Y), IsQuasiCompact B S hS g.hom →
      IsQuasiSeparated B S hS g.hom →
      ∀ G : Modules.{u, u} B S hS U.1 U.2, G.IsQuasicoherentOnSite →
        have := hasInjectiveResolutions_modules B S hS U.1 U.2
        (((modulePushforward B S hS g).rightDerived i).obj G).IsQuasicoherentOnSite) :
    AffineTargetHigherPushforwardQuasicoherent B S hS i :=
  fun U Y g _ hgqc hgqs G hG ↦ h U Y g hgqc hgqs G hG

/-! ### Stacks 0720 -/

/-- **Stacks 0720.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
algebraic spaces over a scheme `S`, and let `F` be a quasi-coherent `𝒪_X`-module on the small
étale site of `X`.  Then the higher direct image `R^i f_*F` is quasi-coherent for every `i`.

The affine-base case of the source's proof is the hypothesis `haffine`, and the
injective-preservation half of Stacks 03F3 for the chart base changes of `f` is the hypothesis
`h03F3`; everything else is the source's reduction to an affine base, by Stacks 03M0,
condition (4), and the higher-direct-image clause of Stacks 03LX, with the hypotheses of the
affine case supplied from those of `f` by Stacks 03HF and Stacks 03KL, part (3). -/
@[stacks 0720 "the reduction to an affine base; the affine case is the hypothesis haffine"]
theorem isQuasicoherentOnSite_rightDerived_modulePushforward {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (i : ℕ)
    (h03F3 : ∀ V : SmallEtale B S hS Y.1,
      (chartBaseChangeModulePullback B S hS f V).PreservesInjectiveObjects)
    (haffine : AffineTargetHigherPushforwardQuasicoherent B S hS i) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived i).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_of_forall_affine_chart B S hS f hfqc hfqs F i h03F3
    fun V hV hqc hqs _ ↦
      haffine _ _ (chartBaseChangeProjection B S hS f V)
        (isAffineSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V) hV) hqc hqs _
        (isQuasicoherentOnSite_etaleModulePullback B S hS
          (chartBaseChangeInclusion B S hS f V)
          (isEtale_chartBaseChangeInclusion B S hS f V) F inferInstance)

/-- **Stacks 0720 for a representable morphism, granted only the affine-base case.** For a
representable, quasi-compact and quasi-separated morphism `f : X ⟶ Y` of algebraic spaces over
`S` and a quasi-coherent `𝒪_X`-module `F`, the higher direct image `R^i f_*F` is quasi-coherent
for every `i`.

Representability makes the base change `V ×_Y X` of `f` at an étale scheme chart `V` of `Y` an
étale scheme chart of `X`, so the chartwise identification is Equation 69.3.0.1 of the source,
Stacks 071Z, in which the injective-preservation half of Stacks 03F3 is discharged; the
hypothesis `h03F3` is therefore not needed.  The quasi-compactness and quasi-separatedness of the
base-changed morphism, which the affine case takes, come from those of `f` by Stacks 03HF and
Stacks 03KL, part (3). -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_of_representable
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (i : ℕ)
    (haffine : AffineTargetHigherPushforwardQuasicoherent B S hS i) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived i).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_of_chartwise_of_representable B S hS f hf F i
    fun V hV ↦
      have hpb := AlgebraicSpaces.isPullback_hom _ _ _
        (isPullback_smallBaseChangeChart B S hS f hf V)
      haffine _ _ (smallBaseChangeChartMap B S hS f hf V)
        (isAffineSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V) hV)
        (isQuasiCompact_of_isPullback B S hS hpb hfqc)
        (isQuasiSeparated_of_isPullback B S hS hpb hfqs)
        _ (isQuasicoherentOnSite_etaleModulePullback B S hS
          (chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V))
          (isEtale_chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V)) F inferInstance)

end AlgebraicGeometry.Space

end
