module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeAffineBaseCoherence
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeLocalization
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedPullbackSingleTor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PushforwardStalkTorVanishing
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PushforwardUnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SingleBaseChangeStep
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 08IB]

Let

```
      g'
  X' ---→ X
  |       |
f'|       |f
  v   g   v
  S' ---→ S
```

be a Cartesian square of schemes with `f` quasi-compact and quasi-separated and with `X` and
`S'` Tor independent over `S`.  [Stacks, Tag 08IB] says that the derived base-change map

`Lg^*(Rf_*K) ⟶ Rf'_*(L(g')^*K)`

of [Stacks, Tag 08HY] is then an isomorphism for every `K` in `D(𝒪_X)` with quasi-coherent
cohomology sheaves.  This module proves it.

`AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_transposedUnitBaseChange` had reduced the
tag over an affine base to one input: the invertibility of the derived base-change map of the
**transposed** square at the single complex `𝒪_{S'}[0]`, and
`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent_of_overAffineBase` had reduced the tag
to that affine case.  The input is supplied here from
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_derivedBaseChangeMap_singleUnit_of`, the
compatibility of the derived and the ordinary base-change mates, at its five invertibility
inputs.

## Main results

* `AlgebraicGeometry.homEquiv_symm_pullbackPushforwardUnitHom` — the transpose, under
  `g'^* ⊣ g'_*`, of the ordinary comparison `f^*(g_*𝒪_{S'}) ⟶ g'_*𝒪_{X'}` of
  `AlgebraicGeometry.pullbackPushforwardUnitHom`: the identification of the two composite inverse
  images, the ordinary counit of `g^* ⊣ g_*` and `f'^*𝒪_{S'} ≅ 𝒪_{X'}`.  This is the ordinary
  mate written in the form the compatibility of the two mates consumes.
* `AlgebraicGeometry.pullbackSquareIso_counit_eq` — the same at the
  `RingedSpaceModuleAdjunction` spelling, which is the hypothesis `h5` of the compatibility.
* `AlgebraicGeometry.isIso_singlePushforwardComparisonScheme` — `(h_*M)[0] ≅ Rh_*(M[0])` for an
  affine `h` and a quasi-coherent `M`, which is [Stacks, Tag 0G9N].
* `AlgebraicGeometry.isIso_derivedToOrdinaryPullbackSingleUnit` —
  `Lh^*(𝒪_Z[0]) ≅ (h^*𝒪_Z)[0]`, from the K-flatness of the structure sheaf.
* `AlgebraicGeometry.isIso_derivedBaseChangeMap_singleUnit` — **the input that was missing**:
  `Lf^*(Rg_*𝒪_{S'}[0]) ⟶ Rg'_*(Lf'^*𝒪_{S'}[0])` is invertible for a Cartesian square with `g`
  affine and `X`, `S'` Tor independent over `S`.
* `AlgebraicGeometry.derivedBaseChangeIsIsoOverAffineBase` — [Stacks, Tag 08IB] over an affine
  base.
* `AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent` — **[Stacks, Tag 08IB]**.

## Implementation notes

*Where the five invertibility inputs come from.*  `Rg_*(𝒪_{S'}[0]) ≅ (g_*𝒪_{S'})[0]` and
`Rg'_*(𝒪_{X'}[0]) ≅ (g'_*𝒪_{X'})[0]` are [Stacks, Tag 0G9N] for an affine morphism, through
`AlgebraicGeometry.isIso_derivedPushforwardUnit_app_of_isAffineHom`; `g'` is affine because
affineness is stable under base change.  `Lf^*((g_*𝒪_{S'})[0]) ≅ (f^*(g_*𝒪_{S'}))[0]` is where
Tor independence enters: `AlgebraicGeometry.stalkTorVanishing_pushforwardStructureSheaf` turns it
into the stalkwise vanishing that
`Stacks.Cohomology.PullbackSingleTor.isIso_derivedToOrdinaryPullbackSingle_pushforward_unit`
consumes.  `Lf'^*(𝒪_{S'}[0]) ≅ (f'^*𝒪_{S'})[0]` holds for every morphism, the structure sheaf
being flat.  And `f^*(g_*𝒪_{S'}) ≅ g'_*𝒪_{X'}` is the ordinary affine base change
`AlgebraicGeometry.isIso_pullbackPushforwardUnitHom`.

*One spelling per object.*  `AlgebraicGeometry.pullbackPushforwardUnitHomRS` is a type
ascription of the ordinary base-change comparison at the `RingedSpaceModuleAdjunction` spelling
of the inverse and direct images.  It is needed, not cosmetic: a kernel defeq between two
spellings of an object of
`DerivedCategory (SheafOfModules (structureSheafRing _))` does not terminate inside the kernel's
deterministic limit, so every object occurring in the statements below is spelled one way.  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/SingleBaseChangeStep.lean` record the same
constraint and the two rules it imposes.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.AlgebraicGeometry.AffineBaseChange
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap derivedBaseChangeMap_adjoint
  derivedPullbackCompIsoLeft)

universe u

namespace AlgebraicGeometry

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-! ### The ordinary comparison, transposed -/

/-- **The transpose of the ordinary comparison `f^*(g_*𝒪_{S'}) ⟶ g'_*𝒪_{X'}`.**  Under
`g'^* ⊣ g'_*` the comparison `AlgebraicGeometry.pullbackPushforwardUnitHom` is the
identification of the two composite inverse images, followed by `f'^*` of the ordinary counit of
`g^* ⊣ g_*` at `𝒪_{S'}` and by `f'^*𝒪_{S'} ≅ 𝒪_{X'}`.

`Stacks.Modules.homEquiv_pullbackSquareIso_comp` identifies the transpose of the base-change
morphism of [Stacks, Tag 02KG], and
`AlgebraicGeometry.pullbackPushforwardUnitHom_eq_baseChangeNatTrans` identifies the comparison
with that morphism followed by `g'_*(f'^*𝒪_{S'} ≅ 𝒪_{X'})`. -/
theorem homEquiv_symm_pullbackPushforwardUnitHom (w : g' ≫ f = f' ≫ g) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g').homEquiv _ _).symm
        (pullbackPushforwardUnitHom w) =
      (Stacks.Modules.pullbackSquareIso g g' f f' w.symm).hom.app
          ((Scheme.Modules.pushforward g).obj (unitObj S')) ≫
        (Scheme.Modules.pullback f').map
          ((Scheme.Modules.pullbackPushforwardAdjunction g).counit.app (unitObj S')) ≫
        (pullbackUnitIso f').hom := by
  rw [pullbackPushforwardUnitHom_eq_baseChangeNatTrans w,
    Adjunction.homEquiv_naturality_right_symm, ← Stacks.Modules.homEquiv_pullbackSquareIso_comp,
    Equiv.symm_apply_apply, Category.assoc]


/-! ### The identification of the two mates -/

section Identification

attribute [local instance 100000] HasDerivedCategory.standard

/-- `AlgebraicGeometry.pullbackPushforwardUnitHom`, ascribed at the
`RingedSpaceModuleAdjunction` spelling of the inverse and direct images.  The two spellings are
the same functor by `rfl`; the ascription is made so that all the statements below use one
spelling.  A kernel defeq between two spellings of an object of
`DerivedCategory (SheafOfModules (structureSheafRing _))` does not terminate within the kernel's
deterministic limit. -/
def pullbackPushforwardUnitHomRS (w : g' ≫ f = f' ≫ g) :
    (modulePullback f.toLRSHom.toShHom).obj
        ((modulePushforward g.toLRSHom.toShHom).obj (unitObj S')) ⟶
      (modulePushforward g'.toLRSHom.toShHom).obj (unitObj X') :=
  pullbackPushforwardUnitHom w

/-- `pullbackPushforwardUnitHomRS` is invertible for a Cartesian square with `g` affine: it is
`AlgebraicGeometry.pullbackPushforwardUnitHom`. -/
theorem isIso_pullbackPushforwardUnitHomRS (hsq : IsPullback g' f' f g) [IsAffineHom g] :
    IsIso (pullbackPushforwardUnitHomRS hsq.w) :=
  isIso_pullbackPushforwardUnitHom hsq

/-- The ordinary identity that
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedBaseChangeMap_singleUnit_eq_of` asks for, at
the ringed-space spelling: `AlgebraicGeometry.homEquiv_symm_pullbackPushforwardUnitHom` with the
transpose written out through the counit. -/
theorem pullbackSquareIso_counit_eq (w : g' ≫ f = f' ≫ g) :
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.modulePullbackSquareIso
            g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
            (Stacks.Modules.toShHom_comm w)).hom.app
          ((modulePushforward g.toLRSHom.toShHom).obj (unitObj S')) ≫
        (modulePullback f'.toLRSHom.toShHom).map
            ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).counit.app
              (unitObj S')) ≫
          (pullbackUnitIso f').hom =
      (modulePullback g'.toLRSHom.toShHom).map (pullbackPushforwardUnitHomRS w) ≫
        (modulePullbackPushforwardAdjunction g'.toLRSHom.toShHom).counit.app (unitObj X') :=
  (homEquiv_symm_pullbackPushforwardUnitHom w).symm.trans
    (Adjunction.homEquiv_counit
      (modulePullbackPushforwardAdjunction g'.toLRSHom.toShHom) _ _
      (pullbackPushforwardUnitHomRS w))

/-! ### The invertibility inputs -/

/-- **The comparison `(h_*M)[0] ⟶ Rh_*(M[0])` is invertible for an affine morphism and a
quasi-coherent sheaf.**  Three of its four factors are components of natural isomorphisms; the
fourth is the comparison `h_* ⟶ Rh_*`, which [Stacks, Tag 0G9N] inverts on a complex of
quasi-coherent modules, here the single complex on `M`. -/
theorem isIso_singlePushforwardComparisonScheme {Y Z : Scheme.{u}} (h : Y ⟶ Z) [IsAffineHom h]
    (M : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (hM : M.IsQuasicoherent)
    (d : ℤ) : IsIso (singlePushforwardComparison h.toLRSHom.toShHom M d) :=
  Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_singlePushforwardComparison
    h.toLRSHom.toShHom M d
    (AlgebraicGeometry.isIso_derivedPushforwardUnit_app_of_isAffineHom h
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) d).obj M)
      (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_singleFunctor_obj_X
        d M hM))

/-- **`Lh^*(𝒪_Z[0]) ⟶ (h^*𝒪_Z)[0]` is invertible**: the structure sheaf is flat, so the single
complex on it is K-flat and the derived-pullback comparison of [Stacks, Tag 06YJ] is invertible
there. -/
theorem isIso_derivedToOrdinaryPullbackSingleUnit {Y Z : Scheme.{u}} (h : Y ⟶ Z) :
    IsIso (derivedToOrdinaryPullbackSingle h.toLRSHom.toShHom (unitObj Z) 0) := by
  refine AlgebraicGeometry.isIso_derivedToOrdinaryPullbackSingle h.toLRSHom.toShHom
    (unitObj Z) 0 ?_
  exact Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    h.toLRSHom.toShHom _
    (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Z.toRingedSpace.sheaf _
      (Stacks.RingedSpace.isFlat_unit_of_ringedSpace Z.toRingedSpace) 0)

/-! ### The one remaining input of [Stacks, Tag 08IB] -/

/-- **The derived base-change map of the transposed square is invertible at `𝒪_{S'}[0]`.**  For a
Cartesian square of schemes with `g` affine and `X`, `S'` Tor independent over `S`,

`Lf^*(Rg_*𝒪_{S'}[0]) ⟶ Rg'_*(Lf'^*𝒪_{S'}[0])`

is an isomorphism.  This is the input
`AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_transposedUnitBaseChange` was waiting for;
it is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_derivedBaseChangeMap_singleUnit_of` at its
five invertibility inputs: [Stacks, Tag 0G9N] at `g` and at `g'`, the stalkwise Tor vanishing of
`AlgebraicGeometry.stalkTorVanishing_pushforwardStructureSheaf`, the K-flatness of the structure
sheaf, and the ordinary affine base change
`AlgebraicGeometry.isIso_pullbackPushforwardUnitHom`. -/
theorem isIso_derivedBaseChangeMap_singleUnit (hsq : IsPullback g' f' f g) [IsAffineHom g]
    (htor : TorIndependent f g) :
    IsIso (derivedBaseChangeMap f'.toLRSHom.toShHom g'.toLRSHom.toShHom g.toLRSHom.toShHom
      f.toLRSHom.toShHom (Stacks.Modules.toShHom_comm hsq.w).symm
      (Stacks.Cohomology.DerivedProjectionFormula.singleUnit S'.toRingedSpace)) := by
  have : IsAffineHom g' := isAffineHom_of_isPullback_right hsq
  exact Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_derivedBaseChangeMap_singleUnit_of
    g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
    (Stacks.Modules.toShHom_comm hsq.w) (pullbackPushforwardUnitHomRS hsq.w)
    (pullbackUnitIso f').hom
    (pullbackSquareIso_counit_eq hsq.w)
    (isIso_singlePushforwardComparisonScheme g (unitObj S')
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S') 0)
    (isIso_singlePushforwardComparisonScheme g' (unitObj X')
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X') 0)
    (Stacks.Cohomology.PullbackSingleTor.isIso_derivedToOrdinaryPullbackSingle_pushforward_unit
      f g (AlgebraicGeometry.stalkTorVanishing_pushforwardStructureSheaf f g htor))
    (isIso_derivedToOrdinaryPullbackSingleUnit f')
    ((pullbackUnitIso f').isIso_hom) (isIso_pullbackPushforwardUnitHomRS hsq)

/-! ### [Stacks, Tag 08IB] -/

/-- **[Stacks, Tag 08IB] over an affine base.**  For a Cartesian square of schemes with `f`
quasi-compact and quasi-separated, both bases affine and `X`, `S'` Tor independent over `S`, the
derived base-change map of [Stacks, Tag 08HY] is invertible on complexes with quasi-coherent
cohomology.

`AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_transposedUnitBaseChange` at
`isIso_derivedBaseChangeMap_singleUnit`. -/
theorem derivedBaseChangeIsIsoOverAffineBase : DerivedBaseChangeIsIsoOverAffineBase.{u} := by
  intro X' X S' S g' f' f g _ _ hsq hqc hqs htor sq K hK
  have : IsAffineHom g := isAffineHom_of_isAffine g
  exact isIso_derivedBaseChangeMap_of_isIso_transposedUnitBaseChange hsq hqc hqs sq K hK
    (isIso_derivedBaseChangeMap_singleUnit hsq htor)

/-- **[Stacks, Tag 08IB].**  Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a Cartesian square of schemes with `f` quasi-compact and quasi-separated and `X` and `S'` Tor
independent over `S`, and let `K` be an object of `D(𝒪_X)` with quasi-coherent cohomology
sheaves.  Then the derived base-change map

`Lg^*(Rf_*K) ⟶ Rf'_*(L(g')^*K)`

of [Stacks, Tag 08HY] is an isomorphism.

`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent_of_overAffineBase` — the source's
reduction to an affine base — at `derivedBaseChangeIsIsoOverAffineBase`. -/
@[stacks 08IB, sga "6 IV 3.1.0" "more general"]
theorem derivedBaseChangeIsIsoOnQuasicoherent : DerivedBaseChangeIsIsoOnQuasicoherent.{u} :=
  derivedBaseChangeIsIsoOnQuasicoherent_of_overAffineBase derivedBaseChangeIsIsoOverAffineBase

end Identification

end AlgebraicGeometry

end
