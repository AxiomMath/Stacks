module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePreimageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image along an affine morphism is cartesian on affine charts

Let `f : X ⟶ Y` be a representable *affine* morphism of algebraic spaces over a scheme `S`
contained in a big fppf site `B`. This file proves that `f_*` preserves the base change property
of the sections over the affine étale charts, and draws the consequences on the small étale site:
quasi-coherence of the direct image, which is the quasi-coherence assertion of Stacks 07U8 and
Stacks 03M9 for an affine morphism, and coherence of the localized direct images along a finite
morphism onto a locally Noetherian algebraic space.

For an affine chart `W` of `Y` and a smaller affine chart `V`, the base-changed charts `W ×_Y X`
and `V ×_Y X` are again affine étale charts of `X`, and `V ×_Y X` is the fibre product
`V ×_W (W ×_Y X)`; all four schemes being affine, `Γ` turns that fibre product into a tensor
product of rings,

`𝒪_X(V ×_Y X) = 𝒪_Y(V) ⊗_{𝒪_Y(W)} 𝒪_X(W ×_Y X)`.

The sections of `f_*𝓕` over a chart are those of `𝓕` over the base-changed chart, so cancelling
this base change turns the comparison for `f_*𝓕` between `V` and `W` into the comparison for `𝓕`
between `V ×_Y X` and `W ×_Y X`.

## Main results

* `isPushout_smallBaseChangeChartRingHom`: the four rings of functions of the two charts and
  their base changes form a pushout square.
* `isCartesianOnAffineCharts_modulePushforward_of_isAffineHom`: the direct image along a
  representable affine morphism of a module cartesian on affine charts is cartesian on affine
  charts.
* `isQuasicoherentOnSite_modulePushforward_of_isAffineHom_of_relativelyRepresentable`: **the
  quasi-coherence assertion of Stacks 07U8**, equivalently Stacks 03M9 for an affine morphism —
  the direct image of a quasi-coherent module along a representable affine morphism is
  quasi-coherent.
* `isCoherentOnSite_chartLocalizedModulePushforward_of_isFinite`: for a finite morphism onto a
  locally Noetherian algebraic space, the localized direct image of a coherent module at any
  étale chart is coherent on the slice.
* `isCoherent_modulePushforward_structureSheaf_preimage'`: **the coherence assertion of
  Stacks 0GF7** — the structure sheaf of the inverse image of a closed subspace under a finite
  morphism pushes forward to a coherent module.
* `isCoherent_and_supportOfSheaf_eq_univ_modulePushforward_structureSheaf_preimage`: **the
  whole of Stacks 0GF7**, registered under that tag with exactly its hypotheses — for `f`
  moreover surjective, that direct image is coherent and its support is all of `Z`.

## References

* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The chart-level structure map of small-chart base change commutes with restriction between
charts: it is a morphism of sheaves of rings. -/
theorem smallBaseChangeChartRingHom_comp (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    (chartRestrict (hF := X.2) ((smallBaseChange B S hS f hrep).map k)).comp
        (smallBaseChangeChartRingHom B S hS f hrep W) =
      (smallBaseChangeChartRingHom B S hS f hrep V).comp (chartRestrict (hF := Y.2) k) :=
  congrArg RingCat.Hom.hom ((smallBaseChangeSharp B S hS f hrep).hom.naturality k.op).symm

/-- **Global functions on the base change of an affine chart are the tensor product**, in the
spelling of small-chart base change: for a representable `f : X ⟶ Y` and a morphism `k : V ⟶ W`
of étale charts of `Y` with `V`, `W` and `W ×_Y X` affine, the two chart-level structure maps
and the two chart restrictions form a pushout square of rings. -/
theorem isPushout_smallBaseChangeChartRingHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) {V W : SmallEtale B S hS Y.1} (k : V ⟶ W)
    (hXW : IsAffine (chartScheme ((smallBaseChange B S hS f hrep).obj W)))
    (hV : IsAffine (chartScheme V)) (hW : IsAffine (chartScheme W)) :
    IsPushout (CommRingCat.ofHom (smallBaseChangeChartRingHom B S hS f hrep W))
      (CommRingCat.ofHom (chartRestrict (hF := Y.2) k))
      (CommRingCat.ofHom (chartRestrict (hF := X.2) ((smallBaseChange B S hS f hrep).map k)))
      (CommRingCat.ofHom (smallBaseChangeChartRingHom B S hS f hrep V)) :=
  isPushout_appTop_representablePullback B S hS f hrep k hXW hV hW

/-- The sections of the base-change direct image over an étale chart `W` of `Y` are the sections
of the module over the base-changed chart, so they carry the module structure of the latter over
the functions on that chart — before the restriction of scalars along the structure map. -/
@[instance_reducible]
noncomputable def smallBaseChangeChartSectionsModule (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS Y.1) :
    Module (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj W))
      (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj G).val.obj (op W)) :=
  (G.val.obj (op ((smallBaseChange B S hS f hrep).obj W))).isModule

section

attribute [local irreducible] AlgebraicGeometry.Space.smallBaseChange

/-- **The direct image of a module cartesian on affine charts along an affine representable
morphism is cartesian on affine charts.**

Let `f : X ⟶ Y` be a representable affine morphism of algebraic spaces and let `𝓕` be an
`𝒪_X`-module whose sections over an affine étale chart of `X` base change to the sections over
a smaller affine chart.  Then `f_*𝓕` has the same property on `Y`. -/
theorem isCartesianOnAffineCharts_modulePushforward_of_isAffineHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCartesianOnAffineCharts G) :
    IsCartesianOnAffineCharts ((modulePushforward B S hS f).obj G) := by
  refine IsCartesianOnAffineCharts.of_iso
    ((modulePushforwardChartIso B S hS f hrep).app G).symm ?_
  intro W V hW hV k
  have hXW : IsAffine (chartScheme ((smallBaseChange B S hS f hrep).obj W)) :=
    isAffine_smallBaseChange_obj B S hS f hrep haff W hW
  have hXV : IsAffine (chartScheme ((smallBaseChange B S hS f hrep).obj V)) :=
    isAffine_smallBaseChange_obj B S hS f hrep haff V hV
  obtain ⟨hinj, hsurj⟩ := hG _ _ hXW hXV ((smallBaseChange B S hS f hrep).map k)
  let := chartAlgebra (hF := Y.2) k
  let := (smallBaseChangeChartRingHom B S hS f hrep W).toAlgebra
  let := (smallBaseChangeChartRingHom B S hS f hrep V).toAlgebra
  let := chartAlgebra (hF := X.2) ((smallBaseChange B S hS f hrep).map k)
  let := ((smallBaseChangeChartRingHom B S hS f hrep V).comp
    (chartRestrict (hF := Y.2) k)).toAlgebra
  have htow₁ : IsScalarTower (chartRing B S hS Y.1 Y.2 W) (chartRing B S hS Y.1 Y.2 V)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj V)) :=
    .of_algebraMap_eq' rfl
  have htow₂ : IsScalarTower (chartRing B S hS Y.1 Y.2 W)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj W))
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj V)) :=
    .of_algebraMap_eq' (smallBaseChangeChartRingHom_comp B S hS f hrep k).symm
  have hpush : Algebra.IsPushout (chartRing B S hS Y.1 Y.2 W) (chartRing B S hS Y.1 Y.2 V)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj W))
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj V)) :=
    Algebra.IsPushout.symm (CommRingCat.isPushout_iff_isPushout.1
      (isPushout_smallBaseChangeChartRingHom B S hS f hrep k hXW hV hW))
  let : Module (chartRing B S hS Y.1 Y.2 W)
      (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj G).val.obj (op W)) :=
    (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj G).val.obj (op W)).isModule
  let : Module (chartRing B S hS Y.1 Y.2 V)
      (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj G).val.obj (op V)) :=
    (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj G).val.obj (op V)).isModule
  let := smallBaseChangeChartSectionsModule B S hS f hrep G W
  have htow₃ : IsScalarTower (chartRing B S hS Y.1 Y.2 W)
      (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj W))
      (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj G).val.obj (op W)) :=
    ⟨fun _ _ _ => mul_smul _ _ _⟩
  set e := Algebra.IsPushout.cancelBaseChange (chartRing B S hS Y.1 Y.2 W)
    (chartRing B S hS Y.1 Y.2 V)
    (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj W))
    (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj V))
    (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj G).val.obj (op W)) with he
  have key : ∀ z, sectionsBaseChange
      ((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj G) k z =
      sectionsBaseChange G ((smallBaseChange B S hS f hrep).map k) (e.symm z) := by
    intro z
    set g := sectionsBaseChange G ((smallBaseChange B S hS f hrep).map k) with hg
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
        refine ((map_add _ x y).trans (congrArg₂ (· + ·) hx hy)).trans ?_
        exact ((congrArg (fun z => g z) (map_add e.symm x y)).trans (map_add g _ _)).symm
    | tmul b x =>
        exact (congrArg (fun z => g z)
          (Algebra.IsPushout.cancelBaseChange_symm_tmul (chartRing B S hS Y.1 Y.2 W)
            (chartRing B S hS Y.1 Y.2 V)
            (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj W))
            (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hrep).obj V))
            (((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj G).val.obj (op W))
            b x)).symm
  refine ⟨fun a b hab => e.symm.injective (hinj ?_), fun c => ?_⟩
  · exact (key a).symm.trans (hab.trans (key b))
  · obtain ⟨w, hw⟩ := hsurj c
    exact ⟨e w, (key (e w)).trans
      ((congrArg (fun z => sectionsBaseChange G ((smallBaseChange B S hS f hrep).map k) z)
        (e.symm_apply_apply w)).trans hw)⟩

end

/-! ### Quasi-coherence of the direct image along an affine morphism -/

/-- **The quasi-coherence assertion of Stacks 07U8, and Stacks 03M9 for an affine morphism.**
The direct image of a quasi-coherent module along a representable affine morphism of algebraic
spaces is quasi-coherent. -/
theorem isQuasicoherentOnSite_modulePushforward_of_isAffineHom_of_relativelyRepresentable
    (f : X ⟶ Y) (hrep : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS f).obj G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_modulePushforward_of_isAffineHom B S hS f hrep haff G
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G hG))

/-! ### Coherence of the direct image along a finite morphism -/

/-- **The chart case of the coherence assertion of Stacks 07UH.**  For a finite morphism
`f : X ⟶ Y` of algebraic spaces with `Y` locally Noetherian, a coherent `𝒪_X`-module `𝓕` and
*any* étale chart `V` of `Y`, the localized direct image `f'_*(𝓕|_U)` of Stacks 04CF is coherent
on the slice at `V`. -/
theorem isCoherentOnSite_chartLocalizedModulePushforward_of_isFinite (f : X ⟶ Y)
    (hf : IsFinite B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCoherent B S hS X.1 X.2 G)
    (V : SmallEtale B S hS Y.1) :
    ((chartLocalizedModulePushforward B S hS f V).obj
      ((moduleChartBaseChangeRestriction B S hS f V).obj G)).IsCoherentOnSite :=
  isCoherentOnSite_chartLocalizedModulePushforward_of_isCoherentOnSite B S hS f G
    (isCoherent_modulePushforward_of_isFinite' B S hS f hf hY G hG).toIsCoherentOnSite V

/-! ### Stacks 0GF7 -/

/-- **The coherence assertion of Stacks 0GF7.**  Let `f : Y ⟶ X` be a finite morphism of
algebraic spaces over `S` with `X` locally Noetherian, let `i : Z ⟶ X` be a closed immersion,
and let `f' : Z' ⟶ Z` be the base change of `f` along `i`.  Then `𝒢 = f'_*𝒪_{Z'}` is a coherent
`𝒪_Z`-module. -/
theorem isCoherent_modulePushforward_structureSheaf_preimage' {Z Z' : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (i : Z ⟶ X) {i' : Z' ⟶ Y} {f' : Z' ⟶ Z} (sq : IsPullback i' f' f i)
    (hf : IsFinite B S hS f.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hi : IsClosedImmersion B S hS i.hom) :
    IsCoherent B S hS Z.1 Z.2 ((modulePushforward B S hS f').obj
      (SheafOfModules.unit (structureRingSheaf B S hS Z'))) := by
  have hZ : HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z.2 X.2 i.hom
      (isLocallyOfFiniteType_of_isImmersion B S hS i.hom
        (isImmersion_of_isClosedImmersion B S hS hi)) hX
  have hf' : IsFinite B S hS f'.hom :=
    isFinite_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hf
  have hZ' : HasEtaleLocalProperty B S hS Z'.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z'.2 Z.2 f'.hom
      (isLocallyOfFiniteType_of_isFinite B S hS Z'.2 Z.2 hf') hZ
  have : Fact (HasEtaleLocalProperty B S hS Z'.1
    (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) := ⟨hZ'⟩
  exact isCoherent_modulePushforward_of_isFinite' B S hS f' hf' hZ _
    (isCoherent_structureSheaf B S hS Z'.1 Z'.2)

/-- **Stacks 0GF7.**  Let `S` be a scheme and let `f : Y ⟶ X` be a morphism of algebraic spaces
over `S` which is finite and surjective, with `X` locally Noetherian.  Let `i : Z ⟶ X` be a
closed immersion, let `i' : Z' ⟶ Y` be the inverse image of `Z`, and let `f' : Z' ⟶ Z` be the
induced morphism.  Then `𝒢 = f'_*𝒪_{Z'}` is a coherent `𝒪_Z`-module whose support is all of `Z`.

Coherence is `isCoherent_modulePushforward_structureSheaf_preimage'`, which needs neither the
surjectivity of `f` nor a chart of `Z`; the support is
`supportOfSheaf_modulePushforward_structureSheaf_preimage_eq_univ`. -/
@[stacks 0GF7 "the whole statement: for f finite and surjective with X locally Noetherian and \
i : Z -> X a closed immersion, the direct image f'_* O_{Z'} along the induced morphism of the \
inverse image is a coherent O_Z-module, and its support is all of Z"]
theorem isCoherent_and_supportOfSheaf_eq_univ_modulePushforward_structureSheaf_preimage
    {Z Z' : AlgebraicSpaces B S hS} (f : Y ⟶ X) (i : Z ⟶ X) {i' : Z' ⟶ Y} {f' : Z' ⟶ Z}
    (sq : IsPullback i' f' f i) (hf : IsFinite B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hi : IsClosedImmersion B S hS i.hom) :
    IsCoherent B S hS Z.1 Z.2 ((modulePushforward B S hS f').obj
        (SheafOfModules.unit (structureRingSheaf B S hS Z'))) ∧
      supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj
        ((modulePushforward B S hS f').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Z')))) = Set.univ :=
  ⟨isCoherent_modulePushforward_structureSheaf_preimage' B S hS f i sq hf hX hi,
    supportOfSheaf_modulePushforward_structureSheaf_preimage_eq_univ B S hS f i sq hsurj⟩

end AlgebraicGeometry.Space

end
