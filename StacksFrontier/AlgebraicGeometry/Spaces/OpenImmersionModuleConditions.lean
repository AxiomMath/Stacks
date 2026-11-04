module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace

/-!
# Flatness and proper support along an open immersion

Let `j : X ⟶ Y` be an open immersion of algebraic spaces over a base `T`, with structure
morphisms `p : Y ⟶ T` and `j ≫ p : X ⟶ T`.  This file records how the conditions on a quotient
in the Quot functor of Stacks 09TR — flatness over the base and support proper over the base —
pass between `𝒪_Y`-modules and `𝒪_X`-modules along `j`.

* Restriction to `X` preserves flatness over the base, `j` being flat (Stacks 05VY).
* If the support of an `𝒪_Y`-module `Q` is proper over the base and contained in `|X|`, then
  the support of `j^*Q` is proper over the base: it is the inverse image of `Supp(Q)`, and the
  reduced induced subspace on `Supp(Q)`, which lies in the open subspace `X`, is its own inverse
  image in `X`.
* If the support of an `𝒪_X`-module `Q'` is proper over the base and `Y` is separated over the
  base, then the support of `j_*Q'` lies in `|X|`: the image of `Supp(Q')` in `|Y|` is closed by
  Stacks 0CZG, so `j_*Q'` is supported in it.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_comp_modulePullback_of_isFlat`: the pullback along a flat
  morphism of a quasi-coherent module flat over the base is flat over the base.
* `AlgebraicGeometry.Space.hasProperSupport_modulePullback_of_isOpenImmersion`: restriction to
  an open subspace containing the support preserves proper support.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_subset_range_of_hasProperSupport`:
  the direct image along an open immersion of a module with proper support is supported in the
  open subspace, when the ambient space is separated over the base.

## References

* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : AlgebraicSpaces B S hS}

/-- **Pullback along a flat morphism preserves flatness over the base** (Stacks 05VY): if `G`
is a quasi-coherent `𝒪_Y`-module flat over `T` along `g : Y ⟶ T` and `f : X ⟶ Y` is flat, then
`f^*G` is flat over `T` along `f ≫ g`.  The statement is pointwise on geometric points. -/
theorem isFlatOver_comp_modulePullback_of_isFlat (f : X ⟶ Y) (g : Y ⟶ T)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hqc : G.IsQuasicoherentOnSite)
    (hf : IsFlat B S hS f.hom) (hG : IsFlatOver B S hS Y.2 g.hom G) :
    IsFlatOver B S hS X.2 (f ≫ g).hom ((modulePullback B S hS f).obj G) := by
  have := hqc
  have : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hqc
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS g G] at hG
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS (f ≫ g)]
  intro xbar
  exact (isFlatOverAtGeometricPoint_modulePullback_iff_of_isFlatAt B S hS f g G xbar
    (isFlatAt_of_isFlat B S hS f.hom hf xbar.image)).mp (hG _)

/-- **Restriction to an open subspace containing the support preserves proper support.**  Let
`j : X ⟶ Y` be an open immersion and `q = j ≫ p` for `p : Y ⟶ T` locally of finite type.  If an
`𝒪_Y`-module `Q` has support proper over `T` and contained in `|X|`, then `j^*Q` has support
proper over `T`.

The support of `j^*Q` is the inverse image `Z'` of `Z = Supp(Q)`.  The inverse image `W` in `X` of
the reduced induced subspace on `Z` maps isomorphically to it, because that subspace factors
through the open immersion `j`; so `W` is proper over `T`, and the reduced induced subspace on
`Z'` factors through `W`. -/
theorem hasProperSupport_modulePullback_of_isOpenImmersion (j : X ⟶ Y)
    (hj : IsOpenImmersion B S hS j.hom) (p : Y ⟶ T) (q : X ⟶ T) (hq : j ≫ p = q)
    (hp : IsLocallyOfFiniteType B S hS p.hom) (hq' : IsLocallyOfFiniteType B S hS q.hom)
    (Q : Modules.{u, u} B S hS Y.1 Y.2)
    (hQ : HasProperSupport B S hS Y.2 T.2 p.hom hp ((SheafOfModules.toSheaf _).obj Q))
    (hsub : supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj Q) ⊆
      Set.range (pointsMap B S hS X.1 j.hom)) :
    HasProperSupport B S hS X.2 T.2 q.hom hq'
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS j).obj Q)) := by
  have hcomm : j.hom ≫ p.hom = q.hom := by rw [← hq]; rfl
  obtain ⟨hZ, hproper⟩ := hQ
  set Z := supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj Q) with hZdef
  have hje : IsEtale B S hS j.hom := isEtale_of_isOpenImmersion B S hS hj
  have hsupp : supportOfSheaf B S hS X.1
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS j).obj Q)) =
        pointsMap B S hS X.1 j.hom ⁻¹' Z :=
    supportOfSheaf_modulePullback_of_isEtale B S hS j hje Q
  have hZ' : IsClosed (pointsMap B S hS X.1 j.hom ⁻¹' Z) :=
    isClosed_preimage_pointsMap B S hS X.2 Y.2 j.hom hZ
  unfold HasProperSupport
  rw [hsupp]
  refine ⟨hZ', ?_⟩
  set R := reducedClosedSubspace B S hS Y.1 Y.2 Z hZ with hRdef
  have hRalg : IsAlgebraicSpace B S hS R.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS Y.1 Y.2 Z hZ
  -- the reduced induced subspace on `Z` factors through the open immersion
  obtain ⟨l, hl⟩ := (factorsThrough_isOpenImmersion_iff_points B S hS X.2 Y.2 hRalg j.hom hj
    R.ι).2 (by rw [hRdef, range_pointsMap_ι_reducedClosedSubspace]; exact hsub)
  set W := R.preimage j.hom with hWdef
  have hsq : IsPullback (R.fromPreimage j.hom) W.ι R.ι j.hom := Subfunctor.isPullback_preimage _ R
  have hWalg : IsAlgebraicSpace B S hS W.toFunctor :=
    isAlgebraicSpace_of_isPullback hRalg X.2 Y.2.isSheaf Y.2.diagonal_representable hsq
  have _ : Mono j.hom := mono_of_presheaf_isOpenImmersion hj
  -- the inverse image maps isomorphically onto the reduced induced subspace
  have hiso : IsIso (R.fromPreimage j.hom) := by
    refine ⟨⟨hsq.lift (𝟙 _) l (by rw [Category.id_comp, hl]), ?_, hsq.lift_fst _ _ _⟩⟩
    apply hsq.hom_ext
    · rw [Category.assoc, hsq.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hsq.lift_snd, Category.id_comp, ← cancel_mono j.hom, Category.assoc,
        hl, hsq.w]
  have hWproper : IsProper B S hS (W.ι ≫ q.hom) := by
    have h := isProper_comp B S hS hWalg hRalg T.2 (R.fromPreimage j.hom) (R.ι ≫ p.hom)
      (isProper_of_isIso B S hS _) hproper
    rwa [← Category.assoc, hsq.w, Category.assoc, hcomm] at h
  -- the reduced induced subspace on `Z'` factors through the inverse image
  set R' := reducedClosedSubspace B S hS X.1 X.2 (pointsMap B S hS X.1 j.hom ⁻¹' Z) hZ'
  have hR'alg : IsAlgebraicSpace B S hS R'.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS X.1 X.2 _ hZ'
  obtain ⟨m, hm⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS Y.2 hR'alg R
    (isClosedSubspace_reducedClosedSubspace B S hS Y.1 Y.2 Z hZ)
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X.1 X.2 _ hZ')
    (R'.ι ≫ j.hom)).2 (by
      rintro _ ⟨x, rfl⟩
      rw [hRdef, range_pointsMap_ι_reducedClosedSubspace, pointsMap_comp_apply]
      have hx : pointsMap B S hS R'.toFunctor R'.ι x ∈ pointsMap B S hS X.1 j.hom ⁻¹' Z := by
        rw [← range_pointsMap_ι_reducedClosedSubspace B S hS X.1 X.2 _ hZ']
        exact ⟨x, rfl⟩
      exact hx)
  exact isProperOver_of_isProper_ι_comp B S hS X.2 T.2 q.hom hq' _ hZ' W hWalg hWproper
    (hsq.lift m R'.ι hm) (hsq.lift_snd _ _ _)

/-- **The direct image along an open immersion of a module with proper support is supported in
the open subspace**, when the ambient space is separated over the base.  Let `j : X ⟶ Y` be an
open immersion over `T`, with `Y ⟶ T` separated and locally of finite type.  If `Q'` is an
`𝒪_X`-module whose support is proper over `T`, then the image of its support in `|Y|` is closed
by Stacks 0CZG, and the support of `j_*Q'` lies in that image, by
`AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_subset_range_of_isClosed_image`. -/
theorem supportOfSheaf_modulePushforward_subset_range_of_hasProperSupport (j : X ⟶ Y)
    (p : Y ⟶ T) (q : X ⟶ T) (hq : j ≫ p = q)
    (hp : IsLocallyOfFiniteType B S hS p.hom) (hq' : IsLocallyOfFiniteType B S hS q.hom)
    (hsep : IsSeparated B S hS p.hom) (Q' : Modules.{u, u} B S hS X.1 X.2)
    (hQ' : HasProperSupport B S hS X.2 T.2 q.hom hq' ((SheafOfModules.toSheaf _).obj Q')) :
    supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS j).obj Q')) ⊆
      Set.range (pointsMap B S hS X.1 j.hom) := by
  have hcomm : j.hom ≫ p.hom = q.hom := by rw [← hq]; rfl
  obtain ⟨hcl, hproper⟩ := hQ'
  exact supportOfSheaf_modulePushforward_subset_range_of_isClosed_image B S hS j Q'
    (isClosed_image_of_isProperOver B S hS X.2 Y.2 T.2 j.hom q.hom p.hom hcomm hq' hp hsep _ hcl
      hproper)

end AlgebraicGeometry.Space

end
