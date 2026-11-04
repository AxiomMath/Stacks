module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierSupportedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFittingRank
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSheafBlowupComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedQuotientNoSupportedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsUnion

/-!
# Blowing up a Fitting ideal makes the strict transform of an affine morphism finite locally free

Let `f : U ⟶ B'` be an affine morphism of algebraic spaces over `S`, let `F = f_*𝒪_U` and let
`C ⊆ B'` be the closed subspace cut out by the `k`-th Fitting ideal sheaf of `F`.  Suppose `F` is
finite locally free of rank `k` on the open complement of `C`, and let `b : B'' ⟶ B'` be the
blowup of `B'` in `C`.  Then the strict transform `U'` of `U` is finite locally free of rank `k`
over `B'' = B' ×_{B'} B''`.

This is the flattening which Step 2 of the proof of Stacks 0ADD sketched in Stacks 0ADE asks for,
in the case of a single Fitting stratum: "we can choose a `U`-admissible blowup `b : X̃ ⟶ X` such
that the strict transform `Ỹ` of `Y` is flat over `X̃`".  The blowup in the Fitting ideal is such a
blowup, by Stacks 0D0Q, which makes the strict transform `F'` of `F` finite locally free of rank
`k`; Stacks 0866 identifies `F'` with the direct image of the strict transform of `𝒪_U`, and
Stacks 0864 together with the absence of sections of `𝒪_{U'}` supported on the exceptional
divisor identifies the latter with the direct image of `𝒪_{U'}`.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_strictTransform_of_fittingIdeal`: the
  statement above.

## References

* [Stacks Project, Tag 0ADE](https://stacks.math.columbia.edu/tag/0ADE)
* [Stacks Project, Tag 0D0Q](https://stacks.math.columbia.edu/tag/0D0Q)
* [Stacks Project, Tag 0866](https://stacks.math.columbia.edu/tag/0866)
* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Blowing up the `k`-th Fitting ideal of `f_*𝒪_U` makes the strict transform of `U` finite
locally free of rank `k`.**  Let `f : U ⟶ B'` be affine, `F = f_*𝒪_U` quasi-coherent with finite
sections over affine charts, `C ⊆ B'` the closed subspace with defining ideal `Fit_k(F)`, and
suppose `F` is finite locally free of rank `k` on `B' ∖ C`.  For the blowup `b : B'' ⟶ B'` of `B'`
in `C`, the composite `U' ⟶ U ×_{B'} B'' ⟶ B' ×_{B'} B''` of the inclusion of the strict
transform of `U` with the base change of `f` is finite locally free of rank `k`. -/
theorem isFiniteLocallyFreeOfRank_strictTransform_of_fittingIdeal
    {Bsp U Bsp' : AlgebraicSpaces B S hS} (f : U ⟶ Bsp) (hf : IsAffineHom B S hS f.hom) (k : ℕ)
    (Z : ClosedSubspaces B S hS Bsp.1)
    (hZ : definingIdealSheaf B S hS Bsp Z =
      fittingIdeal B S hS Bsp.1 Bsp.2 (pushforwardStructureModule B S hS f) k)
    {b : Bsp' ⟶ Bsp} (hb : IsBlowupAlong B S hS Z b)
    (hFqc : (pushforwardStructureModule B S hS f).IsQuasicoherentOnSite)
    (hFfin : ∀ W : SmallEtale B S hS Bsp.1,
      IsAffine ((SmallEtale.toOver B S hS Bsp.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS Bsp.1 Bsp.2 W)
          ((pushforwardStructureModule B S hS f).val.obj (Opposite.op W)))
    (h : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite B S hS (openComplementSpace B S hS Bsp Z).1
        (openComplementSpace B S hS Bsp Z).2)
      ((modulePullback B S hS (openComplementHom B S hS Bsp Z)).obj
        (pushforwardStructureModule B S hS f)) k) :
    IsFiniteLocallyFreeOfRank B S hS
      (strictTransformSpaceι B S hS (f ≫ 𝟙 Bsp) b (preimageClosedSubspace b Z).1 ≫
        strictTransformPullbackMap B S hS f (𝟙 Bsp) b) k := by
  set F := pushforwardStructureModule B S hS f with hFdef
  -- Stacks 0D0Q: the strict transform of `F` has rank `k`
  have hST := isFiniteLocallyFreeOfRank_strictTransformSheaf B S hS F k Z hZ hb hFqc hFfin h
  -- Stacks 0866: it is the direct image of the strict transform of `𝒪_U`
  obtain ⟨-, e₁, -⟩ := exists_modulePushforward_strictTransformSheaf_iso_unconditional B S hS f
    (𝟙 Bsp) b Z (SheafOfModules.unit (structureRingSheaf B S hS U))
    (SheafOfModules.isQuasicoherentOnSite_unit _) hb hf
  -- Stacks 0864: the strict transform of `𝒪_U` is the direct image of the strict transform of
  -- `𝒪_U` relative to the blowup `U' ⟶ U`
  obtain ⟨e₂, -⟩ := exists_strictTransformSheafIso_modulePushforward_strictTransformSpace B S hS
    (f ≫ 𝟙 Bsp) b Z hb (SheafOfModules.unit (structureRingSheaf B S hS U))
  -- that relative strict transform is `𝒪_{U'}`: the exceptional divisor of `U' ⟶ U` is Cartier
  set ι := strictTransformSpaceι B S hS (f ≫ 𝟙 Bsp) b (preimageClosedSubspace b Z).1 with hι
  set b'' := ι ≫ strictTransformPullbackToSource B S hS (f ≫ 𝟙 Bsp) b with hb''
  have hbl := isBlowupAlong_strictTransform B S hS (f ≫ 𝟙 Bsp) b Z hb
  have hD := isEffectiveCartierDivisor_exceptionalDivisor hbl
  have hno := hasNoSectionsSupportedIn_of_iso B S hS _
    (modulePullbackUnitIso B S hS b'')
    (hasNoSectionsSupportedIn_structureSheaf_of_isEffectiveCartierDivisor B S hS _ _ hD)
  have hzero := supportedSectionsSubmodule_ι_eq_zero_of_hasNoSectionsSupportedIn B S hS _ _ _ hno
  have : IsIso (cokernel.π (supportedSectionsSubmodule B S hS _ _
      (subspacePointSet B S hS _
        (preimageClosedSubspace b'' (preimageClosedSubspace (f ≫ 𝟙 Bsp) Z)).1)
      ((modulePullback B S hS b'').obj
        (SheafOfModules.unit (structureRingSheaf B S hS U)))).ι) :=
    cokernel.π_of_zero hzero
  let e₃ : strictTransformSheafOver B S hS b''
      (preimageClosedSubspace b'' (preimageClosedSubspace (f ≫ 𝟙 Bsp) Z))
      (SheafOfModules.unit (structureRingSheaf B S hS U)) ≅
      SheafOfModules.unit (structureRingSheaf B S hS (strictTransformSpace B S hS (f ≫ 𝟙 Bsp) b
        (preimageClosedSubspace b Z).1)) :=
    (asIso (cokernel.π _)).symm ≪≫ modulePullbackUnitIso B S hS b''
  -- the direct image of `𝒪_{U'}` to `B' ×_{B'} B''`
  set g' := strictTransformPullbackMap B S hS f (𝟙 Bsp) b with hg'
  let e : pushforwardStructureModule B S hS (ι ≫ g') ≅
      strictTransformSheaf B S hS (𝟙 Bsp) b (preimageClosedSubspace b Z).1 F :=
    ((modulePushforwardCompIso B S hS ι g').app _).symm ≪≫
      (modulePushforward B S hS g').mapIso
        (((modulePushforward B S hS ι).mapIso e₃.symm) ≪≫ e₂.symm) ≪≫ e₁
  -- affineness of `U' ⟶ B' ×_{B'} B''`
  have hιaff : IsAffineHom B S hS ι.hom :=
    isAffineHom_of_isClosedImmersion B S hS _
      (strictTransformSubfunctor_isClosedSubspace B S hS (f ≫ 𝟙 Bsp) b _).2
  have hg'aff : IsAffineHom B S hS g'.hom :=
    isAffineHom_of_isPullback' B S hS (AlgebraicSpaces.isPullback_hom B S hS
      (isPullback_strictTransformPullbackMap B S hS f (𝟙 Bsp) b)) hf
  exact (isFiniteLocallyFreeOfRank_iff B S hS _ k).2 ⟨isAffineHom_comp B S hS _ _ hιaff hg'aff,
    RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e.symm hST⟩

end AlgebraicGeometry.Space

end
