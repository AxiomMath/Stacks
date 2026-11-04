module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinFractionDeRham
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechFractionBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionNaturality

/-!
# Base change of the class map of Stacks 0G7Q in degree `c`

Let `g : X' ⟶ X` be a morphism of schemes, let `f : Fin c → Γ(X, 𝒪_X)` with `c = d + 1` be a
finite family of global functions, write `f'ⱼ = g^♯(fⱼ)` for the pulled-back equations, let `ℱ`
be a **quasi-coherent** `𝒪_X`-module and put `ℱ' = g^*ℱ`.  Let `Z ⊆ X` be the common zero locus
of the `fⱼ` and `Z' ⊆ X'` that of the `f'ⱼ`.

This file proves the **first diagram of [Stacks, Tag 0G7U]**: the class maps `c_{f₁,…,f_c}` of
[Stacks, Tag 0G7Q], read on `X` resp. `X'` as maps `ℱ ⟶ i_*ℋ^c_Z(ℱ)` resp.
`ℱ' ⟶ i'_*ℋ^c_{Z'}(ℱ')` (which is how the library states them,
`Stacks.Perfect.SupportedFraction.supportedFractionSource`), commute with base change:

`g^*(c_{f₁,…,f_c})` followed by the degree-`c` comparison `= c_{f'₁,…,f'_c}`

as maps `g^*ℱ ⟶ i'_*ℋ^c_{Z'}(ℱ')`.

The degree-`c` comparison that the diagram needs is built here too.  It exists because `c` is
the *top* degree of the extended alternating Čech complex of [Stacks, Tag 0G7I]: there the
complex has nothing above degree `c`, so its degree-`c` cohomology is the cokernel of the last
differential `lastDif`, and `g^*` is a left adjoint, hence preserves that cokernel.  Transporting
along the comparison `g^*(ℱ^•) ⟶ (ℱ')^•` of the two Čech complexes carries it to the cokernel of
the last differential for `f'` and `ℱ'`.  For quasi-coherent `ℱ` the identification of the
cokernel with `i_*ℋ^c_Z(ℱ)` is invertible — that is [Stacks, Tag 0G7M] — and this is the only
place quasi-coherence is used.

The remark says of the top horizontal arrow of that diagram that it "is the map of Cohomology,
Remark 0G78 on cohomology sheaves in degree `c`".  The last section identifies the two: the
degree-`c` cohomology of the arrow of [Stacks, Tag 0G78] — the upper route of the remark's
derived diagram, `Stacks.Perfect.SupportedDerivedBaseChange.supportedPullbackRoute` followed by
`i'_* R𝓗_{Z'}` of `Lg^*ℱ ⟶ ℱ'` — is `degreeCBaseChange`, once the canonical comparison
`ℋ^c(Lg^*(-)) ⟶ g^*ℋ^c(-)` that the remark suppresses is prefixed.  This is read off the derived
diagram `Stacks.Perfect.CechDerivedBaseChange.derivedBaseChangeSquare_cech` by cancelling
`ℋ^c(Lg^*(ℱ^• ⟶ i_* R𝓗_Z(ℱ)))`, invertible by [Stacks, Tag 0G7M] again.

## Main definitions

* `Stacks.Perfect.CechDegreeCBaseChange.cokernelLastDifBaseChange`: the comparison of the
  cokernel of `g^*(lastDif)` with the cokernel of the last differential of the Čech complex of
  the pulled-back equations, induced by the degreewise Čech comparison.
* `Stacks.Perfect.CechDegreeCBaseChange.degreeCBaseChange`: **the degree-`c` comparison**
  `g^*(i_*ℋ^c_Z(ℱ)) ⟶ i'_*ℋ^c_{Z'}(ℱ')`.
* `Stacks.Perfect.CechDegreeCBaseChange.cokernelIsoHomologySucc`: for a cochain complex over `ℕ`
  with nothing above degree `p + 1`, the identification of the cokernel of the differential into
  degree `p + 1` with the degree-`(p + 1)` homology.
* `Stacks.Perfect.CechDegreeCBaseChange.pullbackExtendHomologyToCokernel`: the degree-`c`
  cohomology of `g^*(ℱ^•)`, read as the cokernel of `g^*(lastDif)`.
* `Stacks.Perfect.CechDegreeCBaseChange.derivedPullbackDegreeCComparison`: **the canonical
  comparison `ℋ^c(Lg^* i_* R𝓗_Z(ℱ)) ⟶ g^*ℋ^c_Z(ℱ)`** that [Stacks, Tag 0G7U] suppresses when it
  reads its derived diagram on cohomology sheaves.
* `Stacks.Perfect.CechDegreeCBaseChange.supportCohomologySheafPullbackIso`: `i'_*ℋ^c_{Z'}(ℱ')`
  read at the two spellings of `Z'`, the common zero locus of the `f'ⱼ` and the preimage
  `g^{-1}(Z)`.

## Main results

* `Stacks.Perfect.CechDegreeCBaseChange.pullback_lastDif_comp_cplxBaseChange`: the square of the
  comparison of complexes `Stacks.Perfect.CechBaseChange.cplxBaseChange` at the last
  differential, which is what makes `cokernelLastDifBaseChange` well defined.
* `Stacks.Perfect.CechDegreeCBaseChange.supportedFractionSource_baseChange`: **the first diagram
  of [Stacks, Tag 0G7U]** — the class map of [Stacks, Tag 0G7Q] commutes with base change, as
  maps out of `g^*ℱ`.
* `Stacks.Perfect.CechDegreeCBaseChange.comp_homologyMap_eq_of_cokernelπ`: a map of cochain
  complexes over `ℕ`, read in top cohomology, is the map it induces on the cokernels of the last
  differentials.
* `Stacks.Perfect.CechDegreeCBaseChange.homologyMap_extendBaseChange`: **in degree `c` the
  base-change comparison of the extended alternating Čech complexes is
  `cokernelLastDifBaseChange`.**
* `Stacks.Perfect.CechDegreeCBaseChange.degreeCBaseChange_eq_homology_zeroG78`: **the top arrow
  of the first diagram of [Stacks, Tag 0G7U] is the map of [Stacks, Tag 0G78] read on cohomology
  sheaves in degree `c`.**

## Implementation notes

The square of the comparison of complexes at the last differential is the `comm` field of
`Stacks.Perfect.CechBaseChange.cplxBaseChange` at `(d, d + 1)`, with both differentials rewritten
by `Stacks.Perfect.SupportedFraction.cplx_d_lastDif`; on the source the differential of
`((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cplx f ℱ)` is the
inverse image of the differential of `cplx f ℱ`, so the rewrite there is a `congrArg`.

That `Scheme.Modules.pullback g` preserves the cokernel is
`CategoryTheory.Adjunction.leftAdjoint_preservesColimits` applied to
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, and the comparison it produces
is `CategoryTheory.Limits.PreservesCokernel.iso`, characterized by
`CategoryTheory.Limits.PreservesCokernel.π_iso_hom`.  That characterization is the only property
of it the diagram uses.

The identity the diagram reduces to is the compatibility of the fraction `s / (f₁ ⋯ f_c)` with
base change, which the library has as
`Stacks.Perfect.CechFractionBaseChange.cplxBaseChange_comp_fracTermTop` — stated for
`Stacks.Perfect.FractionClass.fracTermTop`, the presentation of the fraction by its components.
The class map is built from `Stacks.Perfect.SupportedFraction.fractionHom`, the presentation by
sections, and the two are identified by
`Stacks.Perfect.GysinFractionDeRham.fracTerm_eq_fractionHom` after
`Stacks.Perfect.FractionClass.fracTermTop_succ` has specialized the top degree to a positive one.

[Stacks, Tag 0G7U] has two diagrams; the derived one is
`Stacks.Perfect.CechDerivedBaseChange.derivedBaseChangeSquare_cech`, so the tag's registration
for the first diagram sits on `supportedFractionSource_baseChange` below.

**The two invertibility statements of [Stacks, Tag 0G7M] need the closed set bounded BOTH ways.**
`Stacks.Perfect.SupportedFraction.isIso_cokernelLastDifToSupport` and
`Stacks.Perfect.SupportedFraction.isIso_cechToSupport` each take `equationsClosedSet e ⊆ T` *and*
`T ⊆ equationsClosedSet e`, while the maps they are about take only the first.  At
`T = equationsClosedSet e` that means passing `le_rfl` twice, and the second `le_rfl` reads as a
broken goal if one is not expecting it.  At `T = g^{-1}(Z)` the two bounds are
`Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback_subset` and the reverse
inclusion of the same equality.

**`lastDif` crosses a `def`/`abbrev` boundary.**
`Stacks.Perfect.SupportedFraction.lastDif f ℱ : term f ℱ d ⟶ prodTerm f ℱ d` has `prodTerm` a
reducible `abbrev` but `term` and `cplx` plain `def`s, so `term f ℱ d` and `(cplx f ℱ).X d` are
definitionally but not reducibly equal.  Statements about `cokernel (lastDif f ℱ)` therefore meet
`cokernel ((cplx f ℱ).d d (d + 1))` only up to `Stacks.Perfect.SupportedFraction.cplx_d_lastDif`,
which is why `cokernelIsoHomologySucc` takes the differential as a separate argument `φ` together
with a proof that it is the differential, rather than being stated at `K.d p (p + 1)` and
transported afterwards.

**Two spellings of `Z'`.**  `degreeCBaseChange` lands in `i'_*ℋ^c_{Z'}(ℱ')` with `Z'` the common
zero locus of the `f'ⱼ`, because that is where the class map of [Stacks, Tag 0G7Q] for `f'`
lives; the arrow of [Stacks, Tag 0G78] lands in the same sheaf with `Z'` the preimage
`g^{-1}(Z)`, because that is the shape the remark is stated at.  The two closed subsets are equal
but not definitionally so, so `supportPushSingle_congr` — a `subst` on the equality of sets, the
proofs of closedness being irrelevant — and `cechToDerivedSupport_comp_eqToHom` move between
them, and `supportCohomologySheafPullbackIso` appears in
`degreeCBaseChange_eq_homology_zeroG78`.

**`Category.assoc` is not always available to `rw`.**  `rw` and `simp only` check their results
at `implicit` transparency, and the objects of the last section are spelled through
`DerivedCategory.homologyFunctor`, `HomologicalComplex.homology` and `cokernel` over `X'.Modules`,
which carries two instance paths (`X'.Modules` and
`SheafOfModules (structureSheafRing X'.toRingedSpace)`); reassociating such a composite is
rejected with "did not find an occurrence of the pattern" even for `Category.assoc` itself.  Every
such step is therefore taken in term mode against a `have` universally quantified over one
ambient category — `close`, `glueA`, `glueB` in `homologyMap_extendBaseChange` and `mapc`,
`mapd`, `assoc3`, `glueC`, `glue` in `degreeCBaseChange_eq_homology_zeroG78` — which is the
recipe
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/SupportedDerivedBaseChange.lean`
already uses.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.CechBaseChange (cplxBaseChange)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.CechFractionBaseChange (cplxBaseChange_comp_fracTermTop
  pullback_map_globalSmul)
open Stacks.Perfect.ExtendedAlternatingCech (cplx prodTerm)
open Stacks.Perfect.FractionClass (fracTermTop fracTermTop_succ)
open Stacks.Perfect.GysinFractionDeRham (fracTerm_eq_fractionHom)
open Stacks.Perfect.SupportedFraction (globalSmul fractionClassTrans)
open Stacks.Perfect.SupportedFraction (lastDif cplx_d_lastDif fractionHom
  equationsMultiplication supportedFractionClass cokernelπ_comp_supportedFractionClass
  supportCohomologySheaf cokernelLastDifToSupport isIso_cokernelLastDifToSupport
  supportedFractionSource cplx_d_top_eq_zero derivedQHomologyIso embeddingUpNat_f
  derivedQHomologyIso_hom_naturality cokernelLastDifIsoHomology
  cokernelπ_comp_cokernelLastDifIsoHomology cechHomologyToSupport extendHomologyToSupport
  supportPush supportPushSingle cechToSupport cechToDerivedSupport isIso_cechToSupport)
open Stacks.Perfect.CechBaseChange (extendBaseChange)
open Stacks.Perfect.CechDerivedBaseChange (cechDerivedBaseChange derivedBaseChangeSquare_cech)
open Stacks.Perfect.SupportedDerivedBaseChange (supportedPullbackRoute
  isClosed_equationsClosedSet_pullback equationsClosedSet_pullback
  equationsClosedSet_pullback_subset)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback.Composition (derivedPullbackComparisonOnComplex)
open AlgebraicGeometry.RingedSpaceThickening (derivedPullbackSingleObj)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechDegreeCBaseChange

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules)

/-! ### The last differential and the Čech comparison -/

/-- **The square of the base-change comparison of the extended alternating Čech complexes at the
last differential.**  This is the `comm` field of
`Stacks.Perfect.CechBaseChange.cplxBaseChange` at the pair `(d, d + 1)`, with the two
differentials rewritten by `Stacks.Perfect.SupportedFraction.cplx_d_lastDif`; the differential of
the inverse image of a complex is the inverse image of its differential. -/
public theorem pullback_lastDif_comp_cplxBaseChange :
    (Scheme.Modules.pullback g).map (lastDif f F) ≫ (cplxBaseChange g f F).f (d + 1) =
      (cplxBaseChange g f F).f d ≫ lastDif (fun j => g.appTop (f j))
        ((Scheme.Modules.pullback g).obj F) := by
  have hL : (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cplx f F)).d d (d + 1) = (Scheme.Modules.pullback g).map (lastDif f F) :=
    congrArg (Scheme.Modules.pullback g).map (cplx_d_lastDif f F)
  have hR : (cplx (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)).d d (d + 1) =
      lastDif (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) :=
    cplx_d_lastDif _ _
  rw [← hL, ← hR]
  exact ((cplxBaseChange g f F).comm d (d + 1)).symm

/-- **The comparison of the cokernels of the last differentials.**  The inverse image of the last
differential of the Čech complex of `f` and `ℱ` and the last differential of the Čech complex of
`f'` and `ℱ'` are compared by the degreewise Čech comparison, so the class of a top-degree
cochain may be carried across; `pullback_lastDif_comp_cplxBaseChange` is what makes this well
defined. -/
public def cokernelLastDifBaseChange :
    cokernel ((Scheme.Modules.pullback g).map (lastDif f F)) ⟶
      cokernel (lastDif (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)) :=
  cokernel.desc _
    ((cplxBaseChange g f F).f (d + 1) ≫
      cokernel.π (lastDif (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)))
    ((Category.assoc ((Scheme.Modules.pullback g).map (lastDif f F))
          ((cplxBaseChange g f F).f (d + 1))
          (cokernel.π (lastDif (fun j => g.appTop (f j))
            ((Scheme.Modules.pullback g).obj F)))).symm.trans
      ((congrArg (fun ψ => ψ ≫ cokernel.π (lastDif (fun j => g.appTop (f j))
              ((Scheme.Modules.pullback g).obj F)))
            (pullback_lastDif_comp_cplxBaseChange g f F)).trans
        ((Category.assoc ((cplxBaseChange g f F).f d)
              (lastDif (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F))
              (cokernel.π (lastDif (fun j => g.appTop (f j))
                ((Scheme.Modules.pullback g).obj F)))).trans
          ((congrArg (fun ψ => (cplxBaseChange g f F).f d ≫ ψ)
              (cokernel.condition (lastDif (fun j => g.appTop (f j))
                ((Scheme.Modules.pullback g).obj F)))).trans comp_zero))))

/-! ### The degree-`c` comparison -/

/-- **The degree-`c` comparison `g^*(i_*ℋ^c_Z(ℱ)) ⟶ i'_*ℋ^c_{Z'}(ℱ')`** of
[Stacks, Tag 0G7U].  In the top degree `c = d + 1` the cohomology sheaf `i_*ℋ^c_Z(ℱ)` is the
cokernel of the last Čech differential, by the invertible identification
`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport` of [Stacks, Tag 0G7M]; the inverse
image preserves that cokernel, being a left adjoint; and `cokernelLastDifBaseChange` carries it
to the cokernel of the last Čech differential of the pulled-back data, which is
`i'_*ℋ^c_{Z'}(ℱ')` by the same identification on `X'`. -/
public def degreeCBaseChange [F.IsQuasicoherent] :
    (Scheme.Modules.pullback g).obj
        (supportCohomologySheaf (isClosed_equationsClosedSet f) F ((d + 1 : ℕ) : ℤ)) ⟶
      supportCohomologySheaf (isClosed_equationsClosedSet (fun j => g.appTop (f j)))
        ((Scheme.Modules.pullback g).obj F) ((d + 1 : ℕ) : ℤ) :=
  letI : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
  haveI : IsIso (cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) le_rfl) :=
    isIso_cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl
  (Scheme.Modules.pullback g).map
      (inv (cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) le_rfl)) ≫
    (PreservesCokernel.iso (Scheme.Modules.pullback g) (lastDif f F)).hom ≫
      cokernelLastDifBaseChange g f F ≫
        cokernelLastDifToSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
          (isClosed_equationsClosedSet (fun j => g.appTop (f j))) le_rfl

/-! ### The first diagram of Stacks 0G7U -/

/-- The inverse image of the identification of [Stacks, Tag 0G7M] of the last-differential cokernel
with the support cohomology, followed by `degreeCBaseChange`, is the preserved-cokernel comparison
followed by `cokernelLastDifBaseChange` and the same identification on `X'`. -/
private theorem pullback_map_cokernelLastDifToSupport_comp_degreeCBaseChange [F.IsQuasicoherent] :
    (Scheme.Modules.pullback g).map
          (cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) le_rfl) ≫
        degreeCBaseChange g f F =
      (PreservesCokernel.iso (Scheme.Modules.pullback g) (lastDif f F)).hom ≫
        cokernelLastDifBaseChange g f F ≫ cokernelLastDifToSupport _ _ _ le_rfl := by
  let : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
  have : IsIso (cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) le_rfl) :=
    isIso_cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl
  change _ ≫ (Scheme.Modules.pullback g).map (inv _) ≫ _ = _
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The first diagram of [Stacks, Tag 0G7U]**: the class map `c_{f₁,…,f_c}` of
[Stacks, Tag 0G7Q], read on the coefficient module and in `i_*ℋ^c_Z(ℱ)`, commutes with base
change.  The inverse image of the class map for `f` and `ℱ`, followed by the degree-`c`
comparison `degreeCBaseChange`, is the class map for the pulled-back equations `f'` and the
inverse-image module `ℱ'`.

Unfolding both class maps, the inverse of the identification of [Stacks, Tag 0G7M] sitting in
`degreeCBaseChange` cancels against its occurrence in the class map, and what is left is the
class of the fraction `s / (f₁ ⋯ f_c)`: the characterizing property of the preserved-cokernel
comparison turns the inverse image of the class of a top-degree cochain into the class of its
inverse image, and the remaining identity is the compatibility of the fraction with base change,
`Stacks.Perfect.CechFractionBaseChange.cplxBaseChange_comp_fracTermTop`. -/
@[stacks 0G7U "the first diagram of the remark: the class map c_{f_1,...,f_c} of Tag 0G7Q commutes \
  with base change, for quasi-coherent F, read on X in i_*H^c_Z(F) -- the spelling \
  supportedFractionSource, which is the one Tag 0G7Q is itself registered at in \
  SupportedFractionMap.  Its top horizontal arrow IS the map of Cohomology Remark 0G78 on \
  cohomology sheaves in degree c, which the remark's own sentence asserts: that identification is \
  degreeCBaseChange_eq_homology_zeroG78 below, prefixed by the comparison the remark suppresses"]
public theorem supportedFractionSource_baseChange [F.IsQuasicoherent] :
    (Scheme.Modules.pullback g).map
          (supportedFractionSource f F (isClosed_equationsClosedSet f) le_rfl) ≫
        degreeCBaseChange g f F =
      supportedFractionSource (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
        (isClosed_equationsClosedSet (fun j => g.appTop (f j))) le_rfl := by
  have hD : cokernel.π ((Scheme.Modules.pullback g).map (lastDif f F)) ≫
        cokernelLastDifBaseChange g f F =
      (cplxBaseChange g f F).f (d + 1) ≫
        cokernel.π (lastDif (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)) :=
    cokernel.π_desc _ _ _
  have hfrac : (Scheme.Modules.pullback g).map (fractionHom f F d) ≫
        (cplxBaseChange g f F).f (d + 1) =
      fractionHom (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) d := by
    have h := cplxBaseChange_comp_fracTermTop g f F
    have h1 : fracTermTop f F = fractionHom f F d := fracTerm_eq_fractionHom f F
    have h2 : fracTermTop (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) =
        fractionHom (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) d :=
      fracTerm_eq_fractionHom _ _
    rw [h1, h2] at h
    exact h
  have hVD : (Scheme.Modules.pullback g).map (fractionHom f F d) ≫
        cokernel.π ((Scheme.Modules.pullback g).map (lastDif f F)) ≫
          cokernelLastDifBaseChange g f F =
      fractionHom (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) d ≫
        cokernel.π (lastDif (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)) :=
    (congrArg (fun ψ => (Scheme.Modules.pullback g).map (fractionHom f F d) ≫ ψ) hD).trans
      ((Category.assoc ((Scheme.Modules.pullback g).map (fractionHom f F d))
            ((cplxBaseChange g f F).f (d + 1))
            (cokernel.π (lastDif (fun j => g.appTop (f j))
              ((Scheme.Modules.pullback g).obj F)))).symm.trans
        (congrArg (fun ψ => ψ ≫ cokernel.π (lastDif (fun j => g.appTop (f j))
          ((Scheme.Modules.pullback g).obj F))) hfrac))
  let : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
  rw [show supportedFractionSource f F (isClosed_equationsClosedSet f) le_rfl = _ from
      Stacks.Perfect.SupportedFraction.cokernelπ_comp_supportedFractionClass_comp f F _ le_rfl,
    show supportedFractionSource (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
        (isClosed_equationsClosedSet _) le_rfl = _ from
      Stacks.Perfect.SupportedFraction.cokernelπ_comp_supportedFractionClass_comp _ _ _ le_rfl]
  simp only [Functor.map_comp, Category.assoc]
  rw [pullback_map_cokernelLastDifToSupport_comp_degreeCBaseChange,
    PreservesCokernel.π_iso_hom_assoc, reassoc_of% hVD]

/-! ### The top cohomology of a complex over `ℕ` is the cokernel of the last differential -/

section TopCokernel

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℕ) (p : ℕ)
  (h : K.d (p + 1) (p + 1 + 1) = 0) (φ : K.X p ⟶ K.X (p + 1)) (hφ : φ = K.d p (p + 1))

/-- **In a cochain complex over `ℕ` with nothing above degree `p + 1` the map to the cycles
induced by the last differential is that differential**, read through the identification of the
degree-`(p + 1)` cycles with the degree-`(p + 1)` term.  Both sides become the differential after
composing with the inclusion of the cycles, which is a monomorphism. -/
public theorem toCycles_eq_comp_iCyclesIso_inv :
    K.toCycles p (p + 1) =
      K.d p (p + 1) ≫
        (K.iCyclesIso (p + 1) (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) h).inv := by
  rw [← cancel_mono (K.iCycles (p + 1)), K.toCycles_i p (p + 1), Category.assoc,
    HomologicalComplex.iCyclesIso_inv_hom_id, Category.comp_id]

/-- **The cokernel of the last differential of a cochain complex over `ℕ` is its top
cohomology.**  If the complex has nothing above degree `p + 1` then its degree-`(p + 1)` term is
its own cycles, so the degree-`(p + 1)` homology is the cokernel of the differential into degree
`p + 1`; both presentations are cokernels of that differential, so the identification is
canonical.  The differential is taken as a separate argument `φ` together with the proof `hφ`
that it *is* the differential, because the differentials of the complexes met in practice have
names of their own — `Stacks.Perfect.SupportedFraction.lastDif` and its inverse image — and the
cokernel one wants is the cokernel of those. -/
public def cokernelIsoHomologySucc : cokernel φ ≅ K.homology (p + 1) :=
  CokernelCofork.mapIsoOfIsColimit (cokernelIsCokernel φ)
    (K.homologyIsCokernel p (p + 1) (CochainComplex.prev_nat_succ p))
    (Arrow.isoMk (Iso.refl _)
      (K.iCyclesIso (p + 1) (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) h).symm
      (by rw [Iso.refl_hom, Category.id_comp, hφ]
          exact toCycles_eq_comp_iCyclesIso_inv K p h))

/-- The identification of the cokernel of the last differential with the top cohomology carries
the class of a top-degree cochain to its cohomology class. -/
public theorem cokernelπ_comp_cokernelIsoHomologySucc :
    cokernel.π φ ≫ (cokernelIsoHomologySucc K p h φ hφ).hom =
      (K.iCyclesIso (p + 1) (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) h).inv ≫
        K.homologyπ (p + 1) :=
  CokernelCofork.π_mapOfIsColimit (cokernelIsCokernel φ) _ _

/-- **A map of cochain complexes over `ℕ`, read in top cohomology, is the map it induces on the
cokernels of the last differentials.**  The two cokernels are identified with the two top
cohomologies by maps `αK`, `αL` characterized — as `cokernelπ_comp_cokernelIsoHomologySucc`
characterizes the identification of `cokernelIsoHomologySucc` — by what they do to the class of
a top-degree cochain, and `u` is any map of the cokernels induced by `ψ` in degree `p + 1`.

Both sides are maps out of `cokernel φK`, so it is enough to compose with `cokernel.π φK`; after
that the two characterizations and naturality of `HomologicalComplex.homologyπ` reduce the
identity to the naturality of the identification of the top-degree cycles with the top-degree
term, which holds because the inclusion of the cycles is a monomorphism. -/
public theorem comp_homologyMap_eq_of_cokernelπ {K L : CochainComplex C ℕ} (ψ : K ⟶ L) (p : ℕ)
    (hK : K.d (p + 1) (p + 1 + 1) = 0) (hL : L.d (p + 1) (p + 1 + 1) = 0)
    {AK AL : C} (φK : AK ⟶ K.X (p + 1)) (φL : AL ⟶ L.X (p + 1))
    (αK : cokernel φK ⟶ K.homology (p + 1)) (αL : cokernel φL ⟶ L.homology (p + 1))
    (u : cokernel φK ⟶ cokernel φL)
    (hαK : cokernel.π φK ≫ αK =
      (K.iCyclesIso (p + 1) (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hK).inv ≫
        K.homologyπ (p + 1))
    (hαL : cokernel.π φL ≫ αL =
      (L.iCyclesIso (p + 1) (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hL).inv ≫
        L.homologyπ (p + 1))
    (hu : cokernel.π φK ≫ u = ψ.f (p + 1) ≫ cokernel.π φL) :
    αK ≫ HomologicalComplex.homologyMap ψ (p + 1) = u ≫ αL := by
  have hcyc : (K.iCyclesIso (p + 1) (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hK).inv ≫
        HomologicalComplex.cyclesMap ψ (p + 1) =
      ψ.f (p + 1) ≫
        (L.iCyclesIso (p + 1) (p + 1 + 1) (CochainComplex.next ℕ (p + 1)) hL).inv := by
    rw [← cancel_mono (L.iCycles (p + 1)), Category.assoc,
      HomologicalComplex.cyclesMap_i, ← Category.assoc,
      HomologicalComplex.iCyclesIso_inv_hom_id, Category.id_comp, Category.assoc,
      HomologicalComplex.iCyclesIso_inv_hom_id, Category.comp_id]
  refine (cancel_epi (cokernel.π φK)).mp ?_
  rw [reassoc_of% hαK, HomologicalComplex.homologyπ_naturality, reassoc_of% hu, hαL,
    reassoc_of% hcyc]

end TopCokernel

/-! ### The top arrow as the map of Stacks 0G78 in degree `c` -/

section ZeroG78

attribute [local instance 10000] HasDerivedCategory.standard

/-- The differential out of the top degree of the degreewise inverse image of the extended
alternating Čech complex vanishes: it is the inverse image of the differential out of the top
degree, which vanishes by
`Stacks.Perfect.SupportedFraction.cplx_d_top_eq_zero`. -/
public theorem pullbackCplx_d_top_eq_zero :
    (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cplx f F)).d (d + 1) (d + 1 + 1) = 0 :=
  (congrArg (Scheme.Modules.pullback g).map (cplx_d_top_eq_zero f F)).trans
    (CategoryTheory.Functor.map_zero (Scheme.Modules.pullback g) _ _)

/-- The differential into the top degree of the degreewise inverse image of the extended
alternating Čech complex is the inverse image of the last differential. -/
public theorem pullback_lastDif_eq_d :
    (Scheme.Modules.pullback g).map (lastDif f F) =
      (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cplx f F)).d d (d + 1) :=
  (congrArg (Scheme.Modules.pullback g).map (cplx_d_lastDif f F)).symm

/-- **The degree-`c` cohomology of `g^*(ℱ^•)`, read as the cokernel of `g^*(lastDif)`.**

Three identifications in a row: the cohomology of a complex read in the derived category is its
cohomology (`Stacks.Perfect.SupportedFraction.derivedQHomologyIso`); applying `g^*` degreewise
commutes with extending by zero
(`HomologicalComplex.mapHomologicalComplexExtendIso`), so the complex is the extension by zero
of the `ℕ`-graded `g^*(ℱ^•)`, whose degree-`c` cohomology is its cohomology before extending
(`HomologicalComplex.extendHomologyIso`); and in the top degree that cohomology is the cokernel
of the differential into it (`cokernelIsoHomologySucc`), which is `g^*(lastDif)`. -/
public def pullbackExtendHomologyToCokernel :
    (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).obj
        (DerivedCategory.Q.obj
          (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((cplx f F).extend ComplexShape.embeddingUpNat))) ⟶
      cokernel ((Scheme.Modules.pullback g).map (lastDif f F)) :=
  (derivedQHomologyIso _ ((d + 1 : ℕ) : ℤ)).hom ≫
    HomologicalComplex.homologyMap
        (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.pullback g)
          (cplx f F) ComplexShape.embeddingUpNat).inv ((d + 1 : ℕ) : ℤ) ≫
      (HomologicalComplex.extendHomologyIso
            (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (cplx f F))
            ComplexShape.embeddingUpNat (embeddingUpNat_f (d + 1))).hom ≫
        (cokernelIsoHomologySucc
          (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (cplx f F)) d (pullbackCplx_d_top_eq_zero g f F)
          ((Scheme.Modules.pullback g).map (lastDif f F))
          (pullback_lastDif_eq_d g f F)).inv

/-- **In degree `c` the base-change comparison of the extended alternating Čech complexes is
`cokernelLastDifBaseChange`.**  Read through `pullbackExtendHomologyToCokernel` on the source and
through the identification of the cokernel of the last differential with the degree-`c`
cohomology sheaf on the target, the degree-`c` cohomology of
`Stacks.Perfect.CechBaseChange.extendBaseChange` is the comparison of the cokernels of the last
differentials.

Both are induced by the degree-`c` component `(cplxBaseChange g f ℱ).f c` on the top cokernel:
that is `cokernel.π_desc` for `cokernelLastDifBaseChange`, and for the cohomology it is
`comp_homologyMap_eq_of_cokernelπ`.  The two remaining factors of
`pullbackExtendHomologyToCokernel` are moved across by the naturality of the two bridges between
cohomology in the derived category and `HomologicalComplex.homology`, namely
`Stacks.Perfect.SupportedFraction.derivedQHomologyIso_hom_naturality` and
`HomologicalComplex.extendHomologyIso_hom_naturality`, after
`HomologicalComplex.mapHomologicalComplexExtendIso` has been split off `extendBaseChange`. -/
public theorem homologyMap_extendBaseChange :
    (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
          (DerivedCategory.Q.map (extendBaseChange g f F)) =
      pullbackExtendHomologyToCokernel g f F ≫
        cokernelLastDifBaseChange g f F ≫
          (cokernelLastDifIsoHomology (fun j => g.appTop (f j))
              ((Scheme.Modules.pullback g).obj F)).hom ≫
            (HomologicalComplex.extendHomologyIso
                (cplx (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F))
                ComplexShape.embeddingUpNat (embeddingUpNat_f (d + 1))).inv ≫
              (derivedQHomologyIso
                ((cplx (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)).extend
                  ComplexShape.embeddingUpNat) ((d + 1 : ℕ) : ℤ)).inv := by
  have key : (cokernelIsoHomologySucc
          (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (cplx f F)) d (pullbackCplx_d_top_eq_zero g f F)
          ((Scheme.Modules.pullback g).map (lastDif f F))
          (pullback_lastDif_eq_d g f F)).hom ≫
        HomologicalComplex.homologyMap (cplxBaseChange g f F) (d + 1) =
      cokernelLastDifBaseChange g f F ≫
        (cokernelLastDifIsoHomology (fun j => g.appTop (f j))
          ((Scheme.Modules.pullback g).obj F)).hom :=
    comp_homologyMap_eq_of_cokernelπ (cplxBaseChange g f F) d
      (pullbackCplx_d_top_eq_zero g f F)
      (cplx_d_top_eq_zero (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F))
      ((Scheme.Modules.pullback g).map (lastDif f F))
      (lastDif (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)) _ _ _
      (cokernelπ_comp_cokernelIsoHomologySucc _ d (pullbackCplx_d_top_eq_zero g f F) _
        (pullback_lastDif_eq_d g f F))
      (cokernelπ_comp_cokernelLastDifIsoHomology (fun j => g.appTop (f j))
        ((Scheme.Modules.pullback g).obj F))
      (cokernel.π_desc _ _ _)
  have hEB : extendBaseChange g f F =
      (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.pullback g) (cplx f F)
          ComplexShape.embeddingUpNat).inv ≫
        HomologicalComplex.extendMap (cplxBaseChange g f F) ComplexShape.embeddingUpNat := rfl
  have hsplit : HomologicalComplex.homologyMap (extendBaseChange g f F) ((d + 1 : ℕ) : ℤ) =
      HomologicalComplex.homologyMap
          (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.pullback g)
            (cplx f F) ComplexShape.embeddingUpNat).inv ((d + 1 : ℕ) : ℤ) ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap (cplxBaseChange g f F) ComplexShape.embeddingUpNat)
          ((d + 1 : ℕ) : ℤ) :=
    (congrArg (fun α => HomologicalComplex.homologyMap α ((d + 1 : ℕ) : ℤ)) hEB).trans
      (HomologicalComplex.homologyMap_comp _ _ _)
  have hdefΨ : pullbackExtendHomologyToCokernel g f F =
      (derivedQHomologyIso
            (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((cplx f F).extend ComplexShape.embeddingUpNat)) ((d + 1 : ℕ) : ℤ)).hom ≫
        HomologicalComplex.homologyMap
            (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.pullback g)
              (cplx f F) ComplexShape.embeddingUpNat).inv ((d + 1 : ℕ) : ℤ) ≫
          (HomologicalComplex.extendHomologyIso
                (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
                  (cplx f F)) ComplexShape.embeddingUpNat (embeddingUpNat_f (d + 1))).hom ≫
            (cokernelIsoHomologySucc
              (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
                (cplx f F)) d (pullbackCplx_d_top_eq_zero g f F)
              ((Scheme.Modules.pullback g).map (lastDif f F))
              (pullback_lastDif_eq_d g f F)).inv := rfl
  have close : ∀ {V₀ V₁ V₂ V₃ V₄ V₅ : X'.Modules} (a : V₀ ⟶ V₁) (i : V₁ ≅ V₂) (j : V₂ ≅ V₃)
      (x : V₀ ⟶ V₄) (y : V₄ ⟶ V₅) (z : V₅ ⟶ V₃),
      a ≫ i.hom ≫ j.hom = x ≫ y ≫ z → a = x ≫ y ≫ z ≫ j.inv ≫ i.inv := by
    intro V₀ V₁ V₂ V₃ V₄ V₅ a i j x y z hc
    rw [show x ≫ y ≫ z ≫ j.inv ≫ i.inv = (x ≫ y ≫ z) ≫ j.inv ≫ i.inv by
      simp only [Category.assoc], ← hc]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have glueA : ∀ {W₀ W₁ W₂ W₃ W₄ W₅ : X'.Modules} (a : W₀ ⟶ W₁) (b : W₁ ⟶ W₂) (t : W₂ ⟶ W₃)
      (e : W₃ ⟶ W₄) (w : W₄ ⟶ W₅) (m : W₃ ⟶ W₅),
      e ≫ w = m → (a ≫ b ≫ t ≫ e) ≫ w = a ≫ b ≫ t ≫ m := by
    intro W₀ W₁ W₂ W₃ W₄ W₅ a b t e w m hw
    rw [← hw]
    simp only [Category.assoc]
  have glueB : ∀ {W₀ W₁ W₂ : X'.Modules} (e : W₀ ≅ W₁) (w : W₀ ⟶ W₂) (m : W₁ ⟶ W₂),
      e.hom ≫ m = w → e.inv ≫ w = m := by
    intro W₀ W₁ W₂ e w m hw
    rw [← hw, Iso.inv_hom_id_assoc]
  refine close _ _ _ _ _ _ ?_
  rw [hdefΨ, reassoc_of% (derivedQHomologyIso_hom_naturality (extendBaseChange g f F)
    ((d + 1 : ℕ) : ℤ)), hsplit, Category.assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality]
  exact (glueA _ _ _ _ _ _ (glueB _ _ _ key)).symm

/-! #### The two spellings of the closed subset `Z'` -/

section ClosedSetTransport

variable {Y : Scheme.{u}}

/-- **`i_* R𝓗_T(ℱ)` depends only on the closed subset `T`.**  Two equal closed subsets give the
same object of `D(𝒪_X)`; the proofs that they are closed are proofs of a proposition, so they do
not enter. -/
public theorem supportPushSingle_congr {T T' : Set Y} (hTT' : T = T') (hT : IsClosed T)
    (hT' : IsClosed T') (G : Y.Modules) :
    supportPushSingle hT G = supportPushSingle hT' G := by
  subst hTT'
  rfl

/-- **The comparison of [Stacks, Tag 0G7L] depends only on the closed subset it is read at.**
At two equal closed subsets it is the same map, under the identification
`supportPushSingle_congr` of the two targets. -/
public theorem cechToDerivedSupport_comp_eqToHom {m : ℕ} (e : Fin m → Γ(Y, ⊤)) (G : Y.Modules)
    {T T' : Set Y} (hT : IsClosed T) (hT' : IsClosed T')
    (hTe : equationsClosedSet e ⊆ T) (hT'e : equationsClosedSet e ⊆ T') (hTT' : T = T')
    (hobj : supportPushSingle hT G = supportPushSingle hT' G) :
    cechToDerivedSupport e G hT hTe ≫ eqToHom hobj = cechToDerivedSupport e G hT' hT'e := by
  subst hTT'
  exact Category.comp_id _

end ClosedSetTransport

/-- **`i'_*ℋ^c_{Z'}(ℱ')` read at the two spellings of `Z'`.**  [Stacks, Tag 0G7U] writes `Z'`
both as the common zero locus of the pulled-back equations — which is where the class map of
[Stacks, Tag 0G7Q] for `f'` and `ℱ'` lives, hence where `degreeCBaseChange` lands — and as the
preimage `g^{-1}(Z)`, which is the shape [Stacks, Tag 0G78] is stated at, hence where the
remark's top arrow lands.  The two are the same closed subset of `X'` by
`Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback`, so this is one object
written two ways. -/
public def supportCohomologySheafPullbackIso :
    (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).obj
        ((supportPush (isClosed_equationsClosedSet_pullback g f)).obj
          ((DerivedCategory.singleFunctor X'.Modules 0).obj
            ((Scheme.Modules.pullback g).obj F))) ≅
      supportCohomologySheaf (isClosed_equationsClosedSet (fun j => g.appTop (f j)))
        ((Scheme.Modules.pullback g).obj F) ((d + 1 : ℕ) : ℤ) :=
  eqToIso (congrArg (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).obj
    (supportPushSingle_congr (equationsClosedSet_pullback g f).symm
      (isClosed_equationsClosedSet_pullback g f)
      (isClosed_equationsClosedSet (fun j => g.appTop (f j)))
      ((Scheme.Modules.pullback g).obj F)))

/-- **The canonical comparison `ℋ^c(Lg^* i_* R𝓗_Z(ℱ)) ⟶ g^*ℋ^c_Z(ℱ)` that
[Stacks, Tag 0G7U] suppresses.**  The remark reads its derived diagram "on cohomology sheaves in
degree `c`", and for its first diagram it then silently replaces `ℋ^c(Lg^*(-))` by `g^*ℋ^c(-)`;
this is that replacement, for the object the remark's top arrow starts at.

It exists because `ℱ^• ⟶ i_* R𝓗_Z(ℱ)` is invertible for quasi-coherent `ℱ`
(`Stacks.Perfect.SupportedFraction.isIso_cechToSupport`, which is [Stacks, Tag 0G7M]), so the
source may be computed on the Čech complex: pull `Lg^*` of that comparison back, pass from the
derived to the degreewise inverse image by the comparison of [Stacks, Tag 06YJ], read the result
as the cokernel of `g^*(lastDif)` by `pullbackExtendHomologyToCokernel`, and undo the two
identifications `degreeCBaseChange` itself is built from — that `g^*` preserves the cokernel,
and [Stacks, Tag 0G7M] again. -/
public def derivedPullbackDegreeCComparison [F.IsQuasicoherent] :
    (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).obj
        ((derivedPullback g.toLRSHom.toShHom).obj
          ((supportPush (isClosed_equationsClosedSet f)).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F))) ⟶
      (Scheme.Modules.pullback g).obj
        (supportCohomologySheaf (isClosed_equationsClosedSet f) F ((d + 1 : ℕ) : ℤ)) :=
  letI : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
  (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
      ((derivedPullback g.toLRSHom.toShHom).map
        (@asIso _ _ _ _ _
          (isIso_cechToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl)).inv) ≫
    (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
        (derivedPullbackComparisonOnComplex g.toLRSHom.toShHom
          ((cplx f F).extend ComplexShape.embeddingUpNat)) ≫
      pullbackExtendHomologyToCokernel g f F ≫
        (PreservesCokernel.iso (Scheme.Modules.pullback g) (lastDif f F)).inv ≫
          (Scheme.Modules.pullback g).map
            (cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) le_rfl)

/-- **The top arrow of the first diagram of [Stacks, Tag 0G7U] is the map of [Stacks, Tag 0G78]
read on cohomology sheaves in degree `c`.**  This is what the remark asserts verbatim: the top
horizontal arrow of its first diagram "is the map of Cohomology, Remark 0G78 on cohomology
sheaves in degree `c`".

The arrow of [Stacks, Tag 0G78] is the upper route
`Stacks.Perfect.SupportedDerivedBaseChange.supportedPullbackRoute` of the remark's derived
diagram — its left-hand equal sign followed by its top horizontal arrow — followed by
`i'_* R𝓗_{Z'}` of the down arrow `Lg^*ℱ ⟶ ℱ'`; it is the whole left-to-right passage of the
derived diagram above the Čech complexes, and it is the composite that stands to the left of
`Lg^*` of the comparison of [Stacks, Tag 0G7L] in
`Stacks.Perfect.CechDerivedBaseChange.derivedBaseChangeSquare_cech`.  Its degree-`c` cohomology
starts at `ℋ^c(Lg^* i_* R𝓗_Z(ℱ))`, not at `g^*ℋ^c_Z(ℱ)` where `degreeCBaseChange` starts, so the
canonical comparison `derivedPullbackDegreeCComparison` of the two is prefixed; and it ends at
`i'_*ℋ^c_{Z'}(ℱ')` spelled at the preimage `g^{-1}(Z)`, so the identification
`supportCohomologySheafPullbackIso` of the two spellings of `Z'` is appended.

The proof is the source's own: take the degree-`c` cohomology of the derived diagram
`derivedBaseChangeSquare_cech`, and cancel `ℋ^c(Lg^*(ℱ^• ⟶ i_* R𝓗_Z(ℱ)))`, which is invertible
because the comparison of [Stacks, Tag 0G7L] is ([Stacks, Tag 0G7M], as
`Stacks.Perfect.SupportedFraction.isIso_cechToSupport`).  What is left on the other side is
`ℋ^c` of the lower horizontal arrow `Lg^*(ℱ^•) ⟶ (ℱ')^•` followed by `ℋ^c` of the comparison of
[Stacks, Tag 0G7L] for `f'` and `ℱ'`, and that is `cokernelLastDifBaseChange` followed by the
identification of [Stacks, Tag 0G7M] — which is `degreeCBaseChange` — by
`homologyMap_extendBaseChange`. -/
@[stacks 0G7U "the top horizontal arrow of the first diagram is the map of Cohomology Remark 0G78 \
  on cohomology sheaves in degree c: the degree-c cohomology of the upper route of the derived \
  diagram, preceded by the canonical comparison of H^c(Lg^*(-)) with g^*H^c(-) that the remark \
  leaves implicit"]
public theorem degreeCBaseChange_eq_homology_zeroG78 [F.IsQuasicoherent] :
    derivedPullbackDegreeCComparison g f F ≫ degreeCBaseChange g f F =
      (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
          (supportedPullbackRoute g.toLRSHom.toShHom (equationsClosedSet f)
              (isClosed_equationsClosedSet f)
              ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
            (supportPush (isClosed_equationsClosedSet_pullback g f)).map
              (derivedPullbackSingleObj g.toLRSHom.toShHom F)) ≫
        (supportCohomologySheafPullbackIso g f F).hom := by
  let : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
  have mapc : ∀ {W₀ W₁ W₂ : DerivedCategory X'.Modules} (x : W₀ ⟶ W₁) (y : W₁ ⟶ W₂),
      (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map (x ≫ y) =
        (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map x ≫
          (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map y :=
    fun x y => (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map_comp x y
  have mapd : ∀ {W₀ W₁ W₂ : DerivedCategory X.Modules} (x : W₀ ⟶ W₁) (y : W₁ ⟶ W₂),
      (derivedPullback g.toLRSHom.toShHom).map x ≫
          (derivedPullback g.toLRSHom.toShHom).map y =
        (derivedPullback g.toLRSHom.toShHom).map (x ≫ y) :=
    fun x y => ((derivedPullback g.toLRSHom.toShHom).map_comp x y).symm
  have assoc3 : ∀ {W₀ W₁ W₂ W₃ : DerivedCategory X'.Modules} (x : W₀ ⟶ W₁) (y : W₁ ⟶ W₂)
      (z : W₂ ⟶ W₃), (x ≫ y) ≫ z = x ≫ y ≫ z := fun x y z => Category.assoc x y z
  have glueC : ∀ {V₀ V₁ V₂ V₃ V₄ V₅ V₆ : X'.Modules} (a : V₀ ⟶ V₁) (b : V₁ ⟶ V₂)
      (t₁ : V₂ ⟶ V₃) (t₂ : V₃ ⟶ V₄) (t₃ : V₄ ⟶ V₅) (w : V₅ ⟶ V₆),
      (a ≫ b ≫ t₁ ≫ t₂ ≫ t₃) ≫ w = a ≫ b ≫ t₁ ≫ t₂ ≫ t₃ ≫ w := by
    intro V₀ V₁ V₂ V₃ V₄ V₅ V₆ a b t₁ t₂ t₃ w
    simp only [Category.assoc]
  have glue : ∀ {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ Ck : X'.Modules}
      (invA : O₀ ⟶ O₁) (A : O₁ ⟶ O₀) (Cm : O₁ ⟶ O₂) (Ps : O₂ ⟶ O₃) (PCi : O₃ ⟶ O₄)
      (PCh : O₄ ⟶ O₃) (Pm : O₄ ⟶ O₅) (D : O₅ ⟶ O₆) (u : O₃ ⟶ Ck) (q : Ck ⟶ O₆)
      (R : O₀ ⟶ O₇) (τ : O₇ ⟶ O₆) (E : O₂ ⟶ O₈) (Cp : O₈ ⟶ O₇) (Cf : O₈ ⟶ O₆),
      Pm ≫ D = PCh ≫ u ≫ q → PCi ≫ PCh = 𝟙 O₃ → E ≫ Cf = Ps ≫ u ≫ q →
      Cp ≫ τ = Cf → A ≫ R = Cm ≫ E ≫ Cp → invA ≫ A = 𝟙 O₀ →
      (invA ≫ Cm ≫ Ps ≫ PCi ≫ Pm) ≫ D = R ≫ τ := by
    intro O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ Ck invA A Cm Ps PCi PCh Pm D u q R τ E Cp Cf
      h₁ h₂ h₃ h₄ h₅ h₆
    have h₅' : A ≫ R ≫ τ = Cm ≫ E ≫ Cp ≫ τ := by
      rw [← Category.assoc, h₅]
      simp only [Category.assoc]
    simp only [Category.assoc]
    rw [h₁, reassoc_of% h₂, ← h₃, ← h₄, ← h₅', reassoc_of% h₆]
  have hcanc : (@asIso _ _ _ _ _
        (isIso_cechToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl)).inv ≫
      cechToDerivedSupport f F (isClosed_equationsClosedSet f) le_rfl = 𝟙 _ :=
    Iso.inv_hom_id _
  have h₆ := ((mapc _ _).symm.trans
      (congrArg (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
        (((mapd _ _).trans
          (congrArg (derivedPullback g.toLRSHom.toShHom).map hcanc)).trans
            ((derivedPullback g.toLRSHom.toShHom).map_id _)))).trans
    ((DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map_id _)
  have h₅ := (((mapc _ _).symm.trans
      (congrArg (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
        ((derivedBaseChangeSquare_cech g f F).trans (assoc3 _ _ _)))).trans
    (mapc _ _)).trans (whisker_eq _ (mapc _ _))
  have hdefQ : cokernelLastDifToSupport (fun j => g.appTop (f j))
        ((Scheme.Modules.pullback g).obj F)
        (isClosed_equationsClosedSet (fun j => g.appTop (f j))) le_rfl =
      (cokernelLastDifIsoHomology (fun j => g.appTop (f j))
          ((Scheme.Modules.pullback g).obj F)).hom ≫
        (HomologicalComplex.extendHomologyIso
            (cplx (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F))
            ComplexShape.embeddingUpNat (embeddingUpNat_f (d + 1))).inv ≫
          (derivedQHomologyIso
              ((cplx (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)).extend
                ComplexShape.embeddingUpNat) ((d + 1 : ℕ) : ℤ)).inv ≫
            (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
              (cechToDerivedSupport (fun j => g.appTop (f j))
                ((Scheme.Modules.pullback g).obj F)
                (isClosed_equationsClosedSet (fun j => g.appTop (f j))) le_rfl) := rfl
  have h₃ : (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
          (DerivedCategory.Q.map (extendBaseChange g f F)) ≫
        (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
          (cechToDerivedSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
            (isClosed_equationsClosedSet (fun j => g.appTop (f j))) le_rfl) =
      pullbackExtendHomologyToCokernel g f F ≫
        cokernelLastDifBaseChange g f F ≫
          cokernelLastDifToSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
            (isClosed_equationsClosedSet (fun j => g.appTop (f j))) le_rfl := by
    rw [hdefQ, homologyMap_extendBaseChange g f F]
    exact glueC _ _ _ _ _ _
  have hdefτ : (supportCohomologySheafPullbackIso g f F).hom =
      (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
        (eqToHom (supportPushSingle_congr (equationsClosedSet_pullback g f).symm
          (isClosed_equationsClosedSet_pullback g f)
          (isClosed_equationsClosedSet (fun j => g.appTop (f j)))
          ((Scheme.Modules.pullback g).obj F))) :=
    (eqToHom_map (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)) _).symm
  have h₄ : (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
          (cechToDerivedSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
            (isClosed_equationsClosedSet_pullback g f)
            (equationsClosedSet_pullback_subset g f)) ≫
        (supportCohomologySheafPullbackIso g f F).hom =
      (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
        (cechToDerivedSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
          (isClosed_equationsClosedSet (fun j => g.appTop (f j))) le_rfl) :=
    (congrArg (fun t => (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
            (cechToDerivedSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
              (isClosed_equationsClosedSet_pullback g f)
              (equationsClosedSet_pullback_subset g f)) ≫ t) hdefτ).trans
      ((mapc _ _).symm.trans
        (congrArg (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
          (cechToDerivedSupport_comp_eqToHom (fun j => g.appTop (f j))
            ((Scheme.Modules.pullback g).obj F) (isClosed_equationsClosedSet_pullback g f)
            (isClosed_equationsClosedSet (fun j => g.appTop (f j)))
            (equationsClosedSet_pullback_subset g f) le_rfl
            (equationsClosedSet_pullback g f).symm _)))
  have hdefC : derivedPullbackDegreeCComparison g f F =
      (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
          ((derivedPullback g.toLRSHom.toShHom).map
            (@asIso _ _ _ _ _
              (isIso_cechToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl)).inv) ≫
        (DerivedCategory.homologyFunctor X'.Modules ((d + 1 : ℕ) : ℤ)).map
            (derivedPullbackComparisonOnComplex g.toLRSHom.toShHom
              ((cplx f F).extend ComplexShape.embeddingUpNat)) ≫
          pullbackExtendHomologyToCokernel g f F ≫
            (PreservesCokernel.iso (Scheme.Modules.pullback g) (lastDif f F)).inv ≫
              (Scheme.Modules.pullback g).map
                (cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) le_rfl) := rfl
  refine Eq.trans (congrArg (fun t => t ≫ degreeCBaseChange g f F) hdefC) ?_
  exact glue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullback_map_cokernelLastDifToSupport_comp_degreeCBaseChange g f F)
    (Iso.inv_hom_id _) h₃ h₄ h₅ h₆

end ZeroG78

/-! ### The first diagram of Stacks 0G7U with all four arrows -/

/-- `ℱ' = g^*ℱ` is killed by `(f'₁, …, f'_c)` after its cokernel projection: multiplication by
each pulled-back equation followed by the projection onto the cokernel of
`(f'₁, …, f'_c) : ℱ'^{⊕c} ⟶ ℱ'` is zero. -/
public theorem globalSmul_comp_cokernelπ_pullback (i : Fin (d + 1)) :
    globalSmul (g.appTop (f i)) ((Scheme.Modules.pullback g).obj F) ≫
        cokernel.π (equationsMultiplication (fun j => g.appTop (f j))
          ((Scheme.Modules.pullback g).obj F)) = 0 := by
  have h : Sigma.ι (fun _ : Fin (d + 1) => (Scheme.Modules.pullback g).obj F) i ≫
      equationsMultiplication (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) =
      globalSmul (g.appTop (f i)) ((Scheme.Modules.pullback g).obj F) :=
    Sigma.ι_desc _ _
  rw [← h, Category.assoc, cokernel.condition, comp_zero]

/-- The transpose along `g^* ⊣ g_*` of the bottom arrow `equationsQuotientBaseChange` is well
defined: the unit of the adjunction followed by `g_*` of the cokernel projection for `f'` kills
`(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`, because `g^*` carries multiplication by `fᵢ` to multiplication by
`f'ᵢ` (`Stacks.Perfect.CechFractionBaseChange.pullback_map_globalSmul`). -/
public theorem equationsMultiplication_comp_unit_comp_pushforward :
    equationsMultiplication f F ≫
        (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F ≫
          (Scheme.Modules.pushforward g).map (cokernel.π (equationsMultiplication
            (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F))) = 0 := by
  refine Stacks.Perfect.SupportedFraction.equationsMultiplication_comp f F _ fun i => ?_
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality
    (globalSmul (f i) F)
  have hsmul : (Scheme.Modules.pullback g).map (globalSmul (f i) F) =
      globalSmul (g.appTop (f i)) ((Scheme.Modules.pullback g).obj F) :=
    pullback_map_globalSmul g (f i) F
  rw [← Category.assoc]
  refine Eq.trans (congrArg (fun ψ => ψ ≫ (Scheme.Modules.pushforward g).map (cokernel.π
    (equationsMultiplication (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F))))
    hnat) ?_
  rw [Functor.comp_map, Category.assoc, ← Functor.map_comp, hsmul,
    globalSmul_comp_cokernelπ_pullback, Functor.map_zero, comp_zero]

/-- **The bottom arrow of the first diagram of [Stacks, Tag 0G7U]**, read on `X'` along the fully
faithful `i'_*`: the comparison `g^*(i_*i^*ℱ) ⟶ i'_*(i')^*ℱ'` of the two quotients
`ℱ/(f₁, …, f_c)ℱ` and `ℱ'/(f'₁, …, f'_c)ℱ'`, presented as cokernels of
`(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ` and `(f'₁, …, f'_c) : ℱ'^{⊕c} ⟶ ℱ'` as in [Stacks, Tag 0G7Q].  It is
the transpose along `g^* ⊣ g_*` of the map induced by the unit `ℱ ⟶ g_*g^*ℱ = g_*ℱ'`; on the
class of a local section `s` of `ℱ` it is the class of `g^*s`
(`pullback_map_cokernelπ_comp_equationsQuotientBaseChange`). -/
public def equationsQuotientBaseChange :
    (Scheme.Modules.pullback g).obj (cokernel (equationsMultiplication f F)) ⟶
      cokernel (equationsMultiplication (fun j => g.appTop (f j))
        ((Scheme.Modules.pullback g).obj F)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (cokernel.desc _ ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F ≫
        (Scheme.Modules.pushforward g).map (cokernel.π (equationsMultiplication
          (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F))))
      (equationsMultiplication_comp_unit_comp_pushforward g f F))

/-- The bottom arrow sends the class of `g^*s` to the class of `g^*s`: precomposed with the inverse
image of the projection onto `ℱ/(f₁, …, f_c)ℱ` it is the projection onto
`ℱ'/(f'₁, …, f'_c)ℱ'`. -/
public theorem pullback_map_cokernelπ_comp_equationsQuotientBaseChange :
    (Scheme.Modules.pullback g).map (cokernel.π (equationsMultiplication f F)) ≫
        equationsQuotientBaseChange g f F =
      cokernel.π (equationsMultiplication (fun j => g.appTop (f j))
        ((Scheme.Modules.pullback g).obj F)) := by
  rw [equationsQuotientBaseChange, ← Adjunction.homEquiv_naturality_left_symm, cokernel.π_desc,
    ← Adjunction.homEquiv_unit, Equiv.symm_apply_apply]

/-- The component of the transformation `Stacks.Perfect.SupportedFraction.fractionClassTrans` of
[Stacks, Tag 0G7Q] at a quasi-coherent module, preceded by the projection onto the quotient, is
the class map read on the coefficient module. -/
public theorem cokernelπ_comp_fractionClassTrans_app [F.IsQuasicoherent] :
    cokernel.π (equationsMultiplication f F) ≫
        (fractionClassTrans f).app F =
      supportedFractionSource f F (isClosed_equationsClosedSet f) le_rfl :=
  rfl

/-- **The first diagram of [Stacks, Tag 0G7U], with all four of its arrows**, read on `X'` along
the fully faithful direct image `i'_*` along the inclusion of `Z'`: for a quasi-coherent
`𝒪_X`-module `ℱ` the square

```
g^*(i_*ℋ^c_Z(ℱ))  --degreeCBaseChange-->  i'_*ℋ^c_{Z'}(ℱ')
      ^                                          ^
 g^*(c_{f₁,…,f_c})                         c_{f'₁,…,f'_c}
      |                                          |
g^*(i_*i^*ℱ)  --equationsQuotientBaseChange-->  i'_*(i')^*ℱ'
```

commutes, where the vertical arrows are the components at `ℱ` and at `ℱ' = g^*ℱ` of the natural
transformation `Stacks.Perfect.SupportedFraction.fractionClassTrans` that [Stacks, Tag 0G7Q] is
registered at — `c_{f₁,…,f_c}` read on `X` along the fully faithful `i_*`, with source the
quotient `ℱ/(f₁, …, f_c)ℱ = i_*i^*ℱ` that the remark presents it on — the bottom arrow is the
comparison of the two quotients, and the top arrow is the degree-`c` comparison, which is the map
of Cohomology, Remark 0G78 on cohomology sheaves in degree `c` by
`degreeCBaseChange_eq_homology_zeroG78`.

**Why this is the remark's diagram.**  The remark's diagram lives on `Z'`, with corners
`h^*i^*ℱ`, `(i')^*ℱ'`, `(i')^{-1}𝒪_{X'} ⊗_{h^{-1}i^{-1}𝒪_X} h^{-1}ℋ^c_Z(ℱ) = h^*ℋ^c_Z(ℱ)` and
`ℋ^c_{Z'}(ℱ')`.  Applying the fully faithful `i'_*` does not change whether it commutes, and
`i'_*h^* = g^*i_*` for the cartesian square `Z' = Z ×_X X'` of the setting
(`AlgebraicGeometry.ExtendedAlternatingCech.isPullback_equationsClosedSubscheme`) carries its
left-hand corners to `g^*(i_*i^*ℱ)` and `g^*(i_*ℋ^c_Z(ℱ))`; this is the form in which the library
states the class map of [Stacks, Tag 0G7Q] itself.

The proof cancels the epimorphism `g^*` of the projection `ℱ ⟶ i_*i^*ℱ` and is then
`supportedFractionSource_baseChange`. -/
@[stacks 0G7U "the first diagram of the remark with all four arrows, for quasi-coherent F: the \
  components of the Tag 0G7Q transformation c_{f_1,...,f_c} at F and at F' = g^*F on the \
  quotients i_*i^*F = F/(f_1,...,f_c)F, the comparison of the two quotients as bottom arrow, and \
  the degree-c comparison (the Tag 0G78 map in degree c) as top arrow; read on X' along the fully \
  faithful i'_*"]
public theorem fractionClassTrans_baseChange [F.IsQuasicoherent] :
    (Scheme.Modules.pullback g).map ((fractionClassTrans f).app F) ≫
        degreeCBaseChange g f F =
      equationsQuotientBaseChange g f F ≫
        (fractionClassTrans (fun j => g.appTop (f j))).app
          ((Scheme.Modules.pullback g).obj F) := by
  have : (Scheme.Modules.pullback g).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isLeftAdjoint
  refine (cancel_epi ((Scheme.Modules.pullback g).map
    (cokernel.π (equationsMultiplication f F)))).mp ?_
  -- `rw` checks its motive at `implicit` transparency, where the objects here do not typecheck
  -- (see the implementation notes), so the steps are glued in a generic category.
  have glue : ∀ {W₀ W₁ W₂ W₃ W₄ : X'.Modules} (a : W₀ ⟶ W₁) (b : W₁ ⟶ W₂) (c : W₂ ⟶ W₃)
      (x : W₀ ⟶ W₂) (e₁ : W₁ ⟶ W₄) (e₂ : W₄ ⟶ W₃) (z : W₀ ⟶ W₄) (y : W₀ ⟶ W₃),
      a ≫ b = x → x ≫ c = y → a ≫ e₁ = z → z ≫ e₂ = y → a ≫ b ≫ c = a ≫ e₁ ≫ e₂ := by
    intro W₀ W₁ W₂ W₃ W₄ a b c x e₁ e₂ z y h₁ h₂ h₃ h₄
    rw [← Category.assoc, h₁, h₂, ← h₄, ← h₃, Category.assoc]
  exact glue _ _ _ _ _ _ _ _
    (((Scheme.Modules.pullback g).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.pullback g).map (cokernelπ_comp_fractionClassTrans_app f F)))
    (supportedFractionSource_baseChange g f F)
    (pullback_map_cokernelπ_comp_equationsQuotientBaseChange g f F)
    (cokernelπ_comp_fractionClassTrans_app _ _)

end Stacks.Perfect.CechDegreeCBaseChange

end
