module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleRelationChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardPresentationExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAffineGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The direct image along a quasi-compact quasi-separated morphism of algebraic spaces

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a
scheme `S` contained in a big fppf site `B`.  **Stacks 03M9** asserts that `f_*` carries
quasi-coherent `𝒪_X`-modules to quasi-coherent `𝒪_Y`-modules.

The source reduces to an affine base and there exhibits `f_*F` as the kernel of a morphism
`a_*(F|_U) ⟶ b_*(F|_R)` attached to an affine étale chart `U` of `X` and its relation
`R = U ×_X U`, by the exact sequence of Stacks 03M8.  Over an affine base `V` the first term is
the direct image along a morphism of affine schemes, hence quasi-coherent.  The relation `R` is a
quasi-compact scheme but need not be affine; instead of computing `b_*(F|_R)` we embed it, by the
same exact sequence applied to `b` and an affine étale chart of `R`, into the direct image along a
morphism of affine schemes.  A kernel is unchanged by composing with a monomorphism, so `f_*F` is
the kernel of a morphism of quasi-coherent modules, and therefore quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.exists_chart_relation_of_isQuasiCompactSpace`: a quasi-compact
  algebraic space has a surjective étale chart with affine underlying scheme, together with the
  relation chart `R = U ×_X U` in the shape Stacks 03M8 consumes.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_chartToSpace_comp`: the direct
  image along a morphism from an affine étale chart to an affine represented algebraic space
  preserves quasi-coherence.
* `AlgebraicGeometry.Space.exists_mono_isQuasicoherentOnSite_of_isQuasiCompactSpace`: over an
  affine base, the direct image of a quasi-coherent module from a quasi-compact algebraic space
  embeds into a quasi-coherent module.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_affine_target`: Stacks 03M9
  over an affine base.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`: **Stacks 03M9**.

## References

* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine étale chart of a quasi-compact algebraic space, with its relation.**  A
quasi-compact algebraic space `X` has an étale scheme chart `U` with affine underlying scheme
which is surjective on points (Stacks 03H6), and an étale scheme chart `R` with two morphisms
`t, s : R ⟶ U` exhibiting `R` as `U ×_X U`, both as presheaves and in the spaces-étale site of
`X`, which is the form in which Stacks 03M8 takes it. -/
theorem exists_chart_relation_of_isQuasiCompactSpace {X : AlgebraicSpaces B S hS}
    (hX : IsQuasiCompactSpace B S hS X.1) :
    ∃ (U R : SmallEtale B S hS X.1) (t s : R ⟶ U),
      IsAffine (chartScheme U) ∧ IsSurjective B S hS U.1.hom ∧
      IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map t))
        (yoneda.map ((SmallEtale.toOver B S hS X.1).map s)) U.1.hom U.1.hom ∧
      IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
        ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
        ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)) := by
  obtain ⟨W, p, hW, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  have hp := (isEtale_iff_presheaf_of_yoneda B S hS p).1 het
  obtain ⟨T, t, s, hpb, ht, -⟩ := exists_etale_kernelPair B S hS p hp
  let U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk p, hp⟩
  let R : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map t ≫ p), etale_comp_of_scheme B S hS t p ht hp⟩
  let tR : R ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk t rfl)
  let sR : R ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk s hpb.w.symm)
  have hpb' : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map tR))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map sR)) U.1.hom U.1.hom := hpb
  refine ⟨U, R, tR, sR, hW, isSurjective_of_presheafSurjective B S hS p hsurj, hpb', ?_⟩
  refine IsPullback.of_map_of_faithful (SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _) ?_
  have hfrom : (SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _).map
        ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)) =
      U.1.hom :=
    congrArg (fun k => k.hom)
      (SpacesEtale.toSpaces_map_from_idObj B S hS ((comparisonFunctor B S hS X).obj U))
  rwa [hfrom]

/-- **The direct image along a morphism from an affine étale chart to an affine represented
algebraic space preserves quasi-coherence.**  The composite of the structure morphism of the
chart with `g` is a morphism of represented algebraic spaces whose underlying morphism of
schemes goes between affine schemes, hence is affine, and the direct image along such a morphism
preserves quasi-coherence by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_representedSpaceMap`. -/
theorem isQuasicoherentOnSite_modulePushforward_chartToSpace_comp {X : AlgebraicSpaces B S hS}
    (U : SmallEtale B S hS X.1) (hU : IsAffine (chartScheme U)) {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (g : X ⟶ ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (M : Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2)
    (hM : M.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS (chartToSpace B S hS X U ≫ g)).obj M).IsQuasicoherentOnSite := by
  let g' : (SmallEtale.toOver B S hS X.1).obj U ⟶ V :=
    yoneda.preimage (chartToSpace B S hS X U ≫ g).hom
  have key : chartToSpace B S hS X U ≫ g = representedSpaceMap B S hS g' :=
    ObjectProperty.hom_ext _ (yoneda.map_preimage _).symm
  rw [key]
  have := hU
  have := hV
  exact @isQuasicoherentOnSite_modulePushforward_representedSpaceMap B S hS _ _ g'
    (inferInstance : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g'))
    M hM

/-- The restriction of a quasi-coherent module to an étale chart is quasi-coherent. -/
private theorem isQuasicoherentOnSite_chart_pullback {X : AlgebraicSpaces B S hS}
    (U : SmallEtale B S hS X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    ((etaleModulePullback.{u, u} B S hS _ ((comparisonFunctor B S hS X).obj U).2).obj
      F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_etaleModulePullback B S hS _ ((comparisonFunctor B S hS X).obj U).2 F hF

/-- **The direct image of a quasi-coherent module from a quasi-compact algebraic space to an
affine base embeds into a quasi-coherent module.**  With `U` an affine surjective étale chart of
`X` and `R = U ×_X U`, the first arrow `g_*F ⟶ a_*(F|_U)` of the exact sequence of Stacks 03M8
is a monomorphism, and `a_*(F|_U)` is the direct image along a morphism of affine schemes. -/
theorem exists_mono_isQuasicoherentOnSite_of_isQuasiCompactSpace {X : AlgebraicSpaces B S hS}
    (hX : IsQuasiCompactSpace B S hS X.1) {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (g : X ⟶ ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    ∃ (N : Modules.{u, u} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V))
      (_ : N.IsQuasicoherentOnSite) (m : (modulePushforward B S hS g).obj F ⟶ N), Mono m := by
  obtain ⟨U, R, t, s, hU, hsurj, -, hR⟩ :=
    exists_chart_relation_of_isQuasiCompactSpace B S hS hX
  refine ⟨_, isQuasicoherentOnSite_modulePushforward_chartToSpace_comp B S hS U hU hV g _
    (isQuasicoherentOnSite_chart_pullback B S hS U F hF), _,
    (exact_moduleChartDirectImage B S hS g hsurj hR F).2⟩

/-- **Stacks 03M9 over an affine base.**  Let `g : X ⟶ V` be a quasi-separated morphism from a
quasi-compact algebraic space to an algebraic space represented by an affine object of the site.
Then `g_*F` is quasi-coherent for every quasi-coherent `𝒪_X`-module `F`.

Choose an affine surjective étale chart `U` of `X` and its relation `R = U ×_X U`.  By the exact
sequence of Stacks 03M8, `g_*F` is the kernel of `t^* - s^* : a_*(F|_U) ⟶ b_*(F|_R)`.  The first
term is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_chartToSpace_comp`.  Since `g`
is quasi-separated, `R` is quasi-compact, so `b_*(F|_R)` embeds into a quasi-coherent module `N`
by `AlgebraicGeometry.Space.exists_mono_isQuasicoherentOnSite_of_isQuasiCompactSpace`; composing
with the embedding does not change the kernel, which is therefore a kernel of a morphism of
quasi-coherent modules. -/
theorem isQuasicoherentOnSite_modulePushforward_of_affine_target {X : AlgebraicSpaces B S hS}
    (hX : IsQuasiCompactSpace B S hS X.1) {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (g : X ⟶ ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (hg : IsQuasiSeparated B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS g).obj F).IsQuasicoherentOnSite := by
  obtain ⟨U, R, t, s, hU, hsurj, hpb, hR⟩ :=
    exists_chart_relation_of_isQuasiCompactSpace B S hS hX
  have hRqc : IsQuasiCompactSpace B S hS (chartSpace B S hS X R).1 := by
    have := hU
    have := hV
    exact (isQuasiCompactSpace_selfPullback B S hS U.1.hom g.hom
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS V)
      (isQuasiCompactSpace_yoneda B S hS _
        (by
          have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.obj.left) := hU
          infer_instance))
      hg (isQuasiCompact_yoneda_of_isAffine B S hS _ hU hV)).of_iso B S hS hpb.isoPullback.symm
  have hex := exact_moduleChartDirectImage B S hS g hsurj hR F
  have := hex.2
  obtain ⟨N, hN, m, hm⟩ := exists_mono_isQuasicoherentOnSite_of_isQuasiCompactSpace B S hS
    hRqc hV (chartToSpace B S hS X R ≫ g)
    _ (isQuasicoherentOnSite_chart_pullback B S hS R F hF)
  have hA := isQuasicoherentOnSite_modulePushforward_chartToSpace_comp B S hS U hU hV g _
    (isQuasicoherentOnSite_chart_pullback B S hS U F hF)
  have e := (hex.1.fIsKernel.conePointUniqueUpToIso (kernelIsKernel _)).trans
    (kernelCompMono _ m).symm
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm
    (@isQuasicoherentOnSite_kernel_of_quasicoherent B S hS _ _ _ _ _ hA hN)

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03M9.**  Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
algebraic spaces over `S`.  Then the direct image `f_*F` of a quasi-coherent `𝒪_X`-module `F` is
quasi-coherent.

Quasi-coherence of `f_*F` is tested on the affine étale charts `V` of `Y`, over which `f_*F`
restricts to the direct image along the base change `V ×_Y X ⟶ V` of the restriction of `F`
(`AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_forall_affine_chart`); that base
change is quasi-separated with quasi-compact source, and the affine-base case is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_affine_target`. -/
@[stacks 03M9]
theorem isQuasicoherentOnSite_modulePushforward_of_qcqs (f : X ⟶ Y)
    (quasiCompact : IsQuasiCompact B S hS f.hom)
    (quasiSeparated : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (F_qcoh : F.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite := by
  have := F_qcoh
  exact pushforward_isQuasicoherentOnSite_of_forall_affine_chart B S hS f quasiCompact
    quasiSeparated F
    fun V hV _ hqs hqcs ↦
      isQuasicoherentOnSite_modulePushforward_of_affine_target B S hS hqcs hV
        (chartBaseChangeProjection B S hS f V) hqs _
        (isQuasicoherentOnSite_etaleModulePullback B S hS _
          (isEtale_chartBaseChangeInclusion B S hS f V) F F_qcoh)

end AlgebraicGeometry.Space

end
