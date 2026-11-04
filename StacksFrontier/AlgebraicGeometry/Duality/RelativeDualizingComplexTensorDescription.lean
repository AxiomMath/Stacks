module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonFlatTensor
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.RelativeDualizingComplexStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StructureSheafCompactObject
import StacksCore.Tactic.StacksAttribute

/-!
# The relative dualizing complex of a proper flat morphism of finite presentation

Let `Y` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ Y` be proper, flat and of
finite presentation, and let `a = f^×` be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
of [Stacks, Tag 0A9E]. [Stacks, Tag 0B6S] calls `ω^•_{X/Y} = a(𝒪_Y)` the relative dualizing
complex and asserts:

* there is a functorial isomorphism `a(K) = Lf^*K ⊗ᴸ_{𝒪_X} ω^•_{X/Y}` for `K ∈ D_QCoh(𝒪_Y)`, by
  [Stacks, Tag 0E4K];
* the trace map `Tr_{f, 𝒪_Y} : Rf_* ω^•_{X/Y} ⟶ 𝒪_Y` induces the trace map `Tr_{f, K}` for every
  `K`: the square
  ```
  Rf_* a(K)                ──Tr_{f,K}──→  K
     ‖                                    ‖
  Rf_*(Lf^*K ⊗ᴸ ω^•) = K ⊗ᴸ Rf_* ω^• ──id_K ⊗ Tr_{f,𝒪_Y}──→ K
  ```
  commutes, the equality on the lower left being the projection formula of [Stacks, Tag 08EU].

* for `g : Y' ⟶ Y` a morphism of quasi-compact quasi-separated schemes and `X' = Y' ×_Y X`,
  `ω^•_{X'/Y'} = L(g')^* ω^•_{X/Y}` by [Stacks, Tag 0AAB], and the trace map of `f' : X' ⟶ Y'`
  is the base change of `Tr_{f, 𝒪_Y}` via the base change isomorphism, by [Stacks, Tag 0B6J].

This file proves all of them. The functorial isomorphism is the map of Equation 48.8.0.1
([Stacks, Tag 0A9S]), invertible by [Stacks, Tag 0E4K]
(`Stacks.Duality.isIso_twistedInverseImageCompareWithPullback_pullbackCotensorator_of_flat`); the
square is the adjunction characterization of that map.

## Main definitions

* `Stacks.Duality.relativeDualizingTensorIso` — the functorial isomorphism
  `Lf^*K ⊗ᴸ ω^•_{X/Y} ≅ a(K)`, natural in `K`.
* `Stacks.Duality.relativeDualizingProjectionFormulaIso` — the projection formula
  `K ⊗ᴸ Rf_* ω^•_{X/Y} ≅ Rf_*(Lf^*K ⊗ᴸ ω^•_{X/Y})` of [Stacks, Tag 08EU] at `ω^•_{X/Y}`.

## Main results

* `Stacks.Duality.relativeDualizingTensorIso_hom_app` — its components are the map of
  Equation 48.8.0.1.
* `Stacks.Duality.relativeDualizingBaseChangeIso`,
  `Stacks.Duality.relativeDualizingBaseChangeIso_hom` — the base change isomorphism
  `L(g')^* ω^•_{X/Y} ≅ ω^•_{X'/Y'}`, built from the invertible base change map of [Stacks,
  Tag 0AA6].
* `Stacks.Duality.map_trace_comp_eq_baseChange_comp_trace` — the trace of `f'` is the base change
  of the trace of `f`.
* `Stacks.Duality.map_relativeDualizingTensorIso_hom_app_comp_trace` — the commuting square of
  the Remark.

## Implementation notes

The tensor product `⊗ᴸ` is `Stacks.Duality.quasiCoherentDerivedTensor`, the derived tensor product
of [Stacks, Tag 06YU] on `D_QCoh`; `Lf^*` is `Stacks.Duality.quasiCoherentDerivedPullback'`; the
identification `K ⊗ᴸ 𝒪_Y = K` on the lower right is the right unitor
`Stacks.Duality.quasiCoherentRightUnitor`. The comparison map of Equation 48.8.0.1 is built from
the cotensorator `Stacks.Duality.pullbackCotensorator` of the monoidal structure of `Lf^*` on
`D_QCoh`, for which the projection formula holds by
`Stacks.Duality.isIso_projectionFormulaMap_pullbackCotensorator`.

Finite presentation is stated as `LocallyOfFinitePresentation`: a proper morphism is quasi-compact
and quasi-separated, so together with properness this is finite presentation.

## References

* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 0E4K](https://stacks.math.columbia.edu/tag/0E4K)
* [Stacks Project, Tag 0AWG](https://stacks.math.columbia.edu/tag/0AWG)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0AAB](https://stacks.math.columbia.edu/tag/0AAB)
* [Stacks Project, Tag 0B6J](https://stacks.math.columbia.edu/tag/0B6J)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

/-- The relative dualizing complex `ω^•_{X/Y}` of [Stacks, Tag 0B6S],
`Stacks.Duality.relativeDualizingComplexStructureSheaf`, is `a(𝒪_Y)` for the right adjoint `a`
of [Stacks, Tag 0A9E]. -/
theorem relativeDualizingComplexStructureSheaf_eq :
    relativeDualizingComplexStructureSheaf f =
      (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (derivedStructureSheaf Y) :=
  rfl

/-- The trace map `Tr_{f, 𝒪_Y}` of [Stacks, Tag 0B6S],
`Stacks.Duality.relativeDualizingTraceStructureSheaf`, is the counit of `Rf_* ⊣ a` at `𝒪_Y`. -/
theorem relativeDualizingTraceStructureSheaf_eq :
    relativeDualizingTraceStructureSheaf f =
      (twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app
        (derivedStructureSheaf Y) :=
  rfl

/-- **The projection formula at the relative dualizing complex**, [Stacks, Tag 08EU]: the
isomorphism `K ⊗ᴸ Rf_* ω^•_{X/Y} ≅ Rf_*(Lf^*K ⊗ᴸ ω^•_{X/Y})` which is the equality on the lower
left of the square of [Stacks, Tag 0B6S]. -/
def relativeDualizingProjectionFormulaIso (K : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedTensor Y).obj K).obj
        ((quasiCoherentDerivedPushforward f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (derivedStructureSheaf Y))) ≅
      (quasiCoherentDerivedPushforward f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj K)).obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (derivedStructureSheaf Y))) :=
  asIso (projectionFormulaMap f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (pullbackCotensorator f) _ K)

/-- **The functorial isomorphism `a(K) = Lf^*K ⊗ᴸ ω^•_{X/Y}` of [Stacks, Tag 0B6S]**, for
`Y` quasi-compact and quasi-separated and `f : X ⟶ Y` proper, flat and of finite presentation:
an isomorphism of functors `D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` from `K ↦ Lf^*K ⊗ᴸ_{𝒪_X} ω^•_{X/Y}`, where
`ω^•_{X/Y} = a(𝒪_Y)` is the relative dualizing complex, to the right adjoint `a` of
[Stacks, Tag 0A9E]. Its components are the map of Equation 48.8.0.1 ([Stacks, Tag 0A9S]), which
is invertible by [Stacks, Tag 0E4K]. -/
@[stacks 0B6S "the functorial isomorphism a(K) = Lf^*K ⊗^L omega^bullet_{X/Y} for K in \
D_QCoh(O_Y), omega^bullet_{X/Y} = a(O_Y), for Y quasi-compact quasi-separated and f proper flat \
of finite presentation: an isomorphism of functors whose components are the map of Equation \
48.8.0.1, invertible by Tag 0E4K"]
def relativeDualizingTensorIso :
    quasiCoherentDerivedPullback' f ⋙ (quasiCoherentDerivedTensor X).flip.obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (derivedStructureSheaf Y)) ≅
      twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) :=
  NatIso.ofComponents
    (fun K =>
      haveI := isIso_twistedInverseImageCompareWithPullback_pullbackCotensorator_of_flat f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) K
      asIso (twistedInverseImageCompareWithPullback f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (pullbackCotensorator f) quasiCoherentRightUnitor K))
    (fun h => compareWithPullback_naturality f _ _ _ _ h)

/-- The components of the functorial isomorphism of [Stacks, Tag 0B6S] are the map of
Equation 48.8.0.1. -/
theorem relativeDualizingTensorIso_hom_app (K : quasiCoherentDerivedCategory Y) :
    (relativeDualizingTensorIso f).hom.app K =
      twistedInverseImageCompareWithPullback f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (pullbackCotensorator f) quasiCoherentRightUnitor K :=
  rfl

/-- **The trace map `Tr_{f, 𝒪_Y}` induces the trace map `Tr_{f, K}` for every `K`**, the
commuting square of [Stacks, Tag 0B6S]: `Rf_*` of the isomorphism
`Lf^*K ⊗ᴸ ω^•_{X/Y} ≅ a(K)` followed by the trace `Tr_{f, K} : Rf_* a(K) ⟶ K` of
[Stacks, Tag 0AWG] is the projection formula `Rf_*(Lf^*K ⊗ᴸ ω^•_{X/Y}) ≅ K ⊗ᴸ Rf_* ω^•_{X/Y}` of
[Stacks, Tag 08EU], followed by `id_K ⊗ Tr_{f, 𝒪_Y} : K ⊗ᴸ Rf_* ω^•_{X/Y} ⟶ K ⊗ᴸ 𝒪_Y` and the
identification `K ⊗ᴸ 𝒪_Y = K`. -/
@[stacks 0B6S "the trace compatibility: Tr_{f,K} composed with Rf_* of the isomorphism a(K) = \
Lf^*K ⊗^L omega^bullet_{X/Y} is the projection formula of Tag 08EU followed by id_K ⊗ Tr_{f,O_Y} \
and K ⊗^L O_Y = K, the Remark's commuting square, for Y quasi-compact quasi-separated and f \
proper flat of finite presentation"]
theorem map_relativeDualizingTensorIso_hom_app_comp_trace (K : quasiCoherentDerivedCategory Y) :
    (quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
        ((relativeDualizingTensorIso f).hom.app K) ≫
      (twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app K =
    (relativeDualizingProjectionFormulaIso f K).inv ≫
      ((quasiCoherentDerivedTensor Y).obj K).map (relativeDualizingTraceStructureSheaf f) ≫
      quasiCoherentRightUnitor.hom.app K := by
  let hpush := isQuasicoherent_homology_derivedPushforward_of_qcqs f
  let adj := twistedInverseImageAdjunction f hpush
  let ρ := quasiCoherentRightUnitor (Y := Y)
  let α := (pullbackCotensorator f)
  rw [relativeDualizingTraceStructureSheaf_eq]
  show (quasiCoherentDerivedPushforward f hpush).map
      (compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
        (twistedInverseImage f hpush).map (ρ.hom.app K)) ≫ adj.counit.app K =
    inv (projectionFormulaMap f hpush α _ K) ≫
      ((quasiCoherentDerivedTensor Y).obj K).map (adj.counit.app (derivedStructureSheaf Y)) ≫
        ρ.hom.app K
  have e : (quasiCoherentDerivedPushforward f hpush).map
      ((twistedInverseImage f hpush).map (ρ.hom.app K)) ≫ adj.counit.app K =
        adj.counit.app _ ≫ ρ.hom.app K := adj.counit_naturality (ρ.hom.app K)
  rw [Functor.map_comp, Category.assoc, e, ← Category.assoc,
    map_compareWithPullbackTensor_comp_counit, Category.assoc]

section BaseChange

variable {X' Y' : Scheme.{u}} [CompactSpace Y'] [QuasiSeparatedSpace Y'] {g' : X' ⟶ X}
  {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)

include sq in
/-- The base change `f'` of `f` is quasi-compact. -/
theorem quasiCompact_of_isPullback_relativeDualizing : QuasiCompact f' :=
  MorphismProperty.of_isPullback sq inferInstance

include sq in
/-- The base change `f'` of `f` is quasi-separated. -/
theorem quasiSeparated_of_isPullback_relativeDualizing : QuasiSeparated f' :=
  MorphismProperty.of_isPullback sq inferInstance

/-- **The base change isomorphism of the relative dualizing complex**, the first assertion of the
last sentence of [Stacks, Tag 0B6S]: for a morphism `g : Y' ⟶ Y` of quasi-compact quasi-separated
schemes and the cartesian square with `g' : X' = Y' ×_Y X ⟶ X`, `f' : X' ⟶ Y'`, the base change map
`L(g')^* a(𝒪_Y) ⟶ a'(Lg^*𝒪_Y)` of [Stacks, Tag 0AA6], invertible by [Stacks, Tag 0AAB], followed
by `a'` of `Lg^*𝒪_Y ≅ 𝒪_{Y'}`: `L(g')^* ω^•_{X/Y} ≅ ω^•_{X'/Y'}`. -/
def relativeDualizingBaseChangeIso :
    haveI := quasiCompact_of_isPullback_relativeDualizing f sq
    haveI := quasiSeparated_of_isPullback_relativeDualizing f sq
    (quasiCoherentDerivedPullback' g').obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (derivedStructureSheaf Y)) ≅
      (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).obj
        (derivedStructureSheaf Y') :=
  haveI := quasiCompact_of_isPullback_relativeDualizing f sq
  haveI := quasiSeparated_of_isPullback_relativeDualizing f sq
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
  haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
    (torIndependent_of_flat_left f g)
  haveI := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat sq
    (derivedStructureSheaf Y)
  asIso ((twistedInverseImageBaseChangeMap g' f' f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq).app
        (derivedStructureSheaf Y)) ≪≫
    (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).mapIso
      (quasiCoherentDerivedPullbackDerivedStructureSheafIsoOfIsQuasicoherent g
        (isQuasicoherent_homology_derivedPullback' g))

/-- **`ω^•_{X'/Y'} = L(g')^* ω^•_{X/Y}`**, the first assertion of the last sentence of
[Stacks, Tag 0B6S]: the base change map of [Stacks, Tag 0AA6] at `𝒪_Y` is an isomorphism
([Stacks, Tag 0AAB]), and composed with `a'(Lg^*𝒪_Y ≅ 𝒪_{Y'})` it is the isomorphism
`relativeDualizingBaseChangeIso`. -/
@[stacks 0B6S "the base change of the relative dualizing complex in the Remark's last sentence: \
for g : Y' to Y a morphism of quasi-compact quasi-separated schemes and X' = Y' x_Y X, the base \
change map L(g')^* a(O_Y) to a'(Lg^* O_Y) of Tag 0AA6 is an isomorphism (Tag 0AAB), so \
omega^bullet_{X'/Y'} = L(g')^* omega^bullet_{X/Y} through it and a'(Lg^* O_Y = O_{Y'})"]
theorem relativeDualizingBaseChangeIso_hom :
    haveI := quasiCompact_of_isPullback_relativeDualizing f sq
    haveI := quasiSeparated_of_isPullback_relativeDualizing f sq
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq
      (torIndependent_of_flat_left f g)
    IsIso ((twistedInverseImageBaseChangeMap g' f' f g
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq).app
          (derivedStructureSheaf Y)) ∧
      (relativeDualizingBaseChangeIso f sq).hom =
        (twistedInverseImageBaseChangeMap g' f' f g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq).app
            (derivedStructureSheaf Y) ≫
          (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).map
            (quasiCoherentDerivedPullbackDerivedStructureSheafIsoOfIsQuasicoherent g
        (isQuasicoherent_homology_derivedPullback' g)).hom :=
  ⟨isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat sq _, rfl⟩

/-- **The trace map of `f'` is the base change of the trace map of `f`**, the second assertion of
the last sentence of [Stacks, Tag 0B6S], by [Stacks, Tag 0B6J]: `Lg^*` of
`Tr_{f, 𝒪_Y} : Rf_* ω^•_{X/Y} ⟶ 𝒪_Y`, followed by `Lg^*𝒪_Y ≅ 𝒪_{Y'}`, is the base change map
`β : Lg^* Rf_* ⟶ Rf'_* L(g')^*` at `ω^•_{X/Y}` (invertible, [Stacks, Tag 08IB]), followed by
`Rf'_*` of the base change isomorphism `L(g')^* ω^•_{X/Y} ≅ ω^•_{X'/Y'}` and
`Tr_{f', 𝒪_{Y'}} : Rf'_* ω^•_{X'/Y'} ⟶ 𝒪_{Y'}`. -/
@[stacks 0B6S "the base change of the trace in the Remark's last sentence: Tr_{f',O_{Y'}} is the \
base change of Tr_{f,O_Y} via the base change isomorphism, i.e. Lg^* Tr_{f,O_Y} followed by Lg^* \
O_Y = O_{Y'} equals the base change map of Rf_* at omega^bullet_{X/Y} followed by Rf'_* of \
L(g')^* omega^bullet_{X/Y} = omega^bullet_{X'/Y'} and Tr_{f',O_{Y'}} (Tag 0B6J)"]
theorem map_trace_comp_eq_baseChange_comp_trace :
    haveI := quasiCompact_of_isPullback_relativeDualizing f sq
    haveI := quasiSeparated_of_isPullback_relativeDualizing f sq
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
    IsIso (quasiCoherentDerivedBaseChange g' f' f g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPullback' g') sq.w).natTrans ∧
    (quasiCoherentDerivedPullback' g).map
        ((twistedInverseImageAdjunction f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app
          (derivedStructureSheaf Y)) ≫
      (quasiCoherentDerivedPullbackDerivedStructureSheafIsoOfIsQuasicoherent g
        (isQuasicoherent_homology_derivedPullback' g)).hom =
    (quasiCoherentDerivedBaseChange g' f' f g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPullback' g') sq.w).natTrans.app
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (derivedStructureSheaf Y)) ≫
      (quasiCoherentDerivedPushforward f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).map
        (relativeDualizingBaseChangeIso f sq).hom ≫
      (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).counit.app
        (derivedStructureSheaf Y') := by
  have := quasiCompact_of_isPullback_relativeDualizing f sq
  have := quasiSeparated_of_isPullback_relativeDualizing f sq
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
  refine ⟨isIso_quasiCoherentDerivedBaseChange_natTrans _ _ _ _ sq
    (torIndependent_of_flat_left f g), ?_⟩
  have h := map_trace_eq_baseChange_comp_trace_of_torIndependent sq
    (torIndependent_of_flat_left f g) (derivedStructureSheaf Y)
  have e := (twistedInverseImageAdjunction f'
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).counit_naturality
      (quasiCoherentDerivedPullbackDerivedStructureSheafIsoOfIsQuasicoherent g
        (isQuasicoherent_homology_derivedPullback' g)).hom
  rw [h]
  simp only [relativeDualizingBaseChangeIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← e]

end BaseChange

end Stacks.Duality

end
