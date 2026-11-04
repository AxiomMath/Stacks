module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeBaseChangeLocalPasting
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapDegenerate
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapLocalOnSource
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineOpenSquare
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Conclusion (c) of [Stacks, Tag 0EX3] reduces to affine bases

The source proves conclusion (c) of [Stacks, Tag 0EX3] after saying *"we can check (a), (b), and
(c) locally on `Y'` and `Y''`"*, and then works with `Y''` and `Y'` affine. This file carries out
that reduction for (c): the canonical map

> `γ : h^* R^d f'_* F' ⟶ R^d f''_* (h')^* F'`

(`…TopDegreeBaseChange.topDirectImageBaseChangeMap`) is compatible with restricting both bases to
a compatible pair of opens, and so it is invertible as soon as it is invertible whenever both
bases are affine.

## Main results

* `…TopDegreeBaseChange.isIso_homologyFunctor_map_derivedPullback_map_iff`: for an open
  immersion `j`, `Hᵈ(Lj^* φ)` is invertible exactly when `j^* Hᵈ(φ)` is.
* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_restrictBase_iff`: **`γ` is compatible
  with restriction to an open `V ⊆ Y'` and an open `W ⊆ Y''` with `W ≤ h⁻¹(V)`.** The `γ` of the
  restricted situation (`TopDegreeBaseChangeSituation.restrictBase`) and restricted square
  (`isPullback_resLE_of_isPullback`) is invertible exactly when the restriction of `γ` to `W` is.
* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_affine`: **the reduction lemma.**
  If `γ` is invertible for every situation with affine `Y'` and every cartesian square with
  affine `Y''`, it is invertible for every situation and every cartesian square.

## Implementation notes

The compatibility is the pasting law of `TopDegreeBaseChangeLocalPasting.lean` applied twice to
one rectangle, `f''⁻¹(W) ⟶ X'` over `W ⟶ Y'`: once as the restricted square followed by the
open-immersion square of `V ⊆ Y'`, once as the open-immersion square of `W ⊆ Y''` followed by the
given square. The two horizontal composites agree only propositionally (`Scheme.Hom.resLE_comp_ι`),
so the passage between them is
`…TopDegreeBaseChange.isIso_homologyFunctor_map_derivedBaseChangeMap_comp_congr`, proved by
substitution.

The affine case enters the reduction lemma as an explicit hypothesis. No `@[stacks 0EX3]`
attribute is placed: what is proved is a reduction step of (c), not (c).

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open DerivedCategory

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance high] CategoryTheory.instHasWeakSheafifyOfHasSheafify

section Schemes

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange

/-- **`Hᵈ` commutes with restriction to an open subscheme, as far as invertibility goes.** For an
open immersion `j`, `Hᵈ(Lj^* φ)` is invertible exactly when `j^* Hᵈ(φ)` is: the derived pullback
along `j` is the exact functor `j^*` applied degreewise
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`), and an exact functor
commutes with `Hᵈ`
(`CategoryTheory.Functor.isIso_homologyFunctor_map_mapDerivedCategory_map_iff`). -/
theorem isIso_homologyFunctor_map_derivedPullback_map_iff {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] {K L : DerivedCategory Z.Modules} (φ : K ⟶ L) (d : ℤ) :
    IsIso ((homologyFunctor U.Modules d).map ((derivedPullback j.toLRSHom.toShHom).map φ)) ↔
      IsIso ((Scheme.Modules.pullback j).map ((homologyFunctor Z.Modules d).map φ)) := by
  have hadd : (modulePullback j.toLRSHom.toShHom).Additive := modulePullback_additive _
  have hlim : PreservesFiniteLimits (modulePullback j.toLRSHom.toShHom) :=
    (modulePullback j.toLRSHom.toShHom).preservesFiniteLimits_of_preservesHomology
  refine (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso j.toLRSHom.toShHom)
    (homologyFunctor U.Modules d)) φ).trans ?_
  exact @Functor.isIso_homologyFunctor_map_mapDerivedCategory_map_iff _ _ _ _ _ _
    (modulePullback j.toLRSHom.toShHom) hadd hlim inferInstance _ _ _ _ φ d

variable {X'' Y'' : Scheme.{u}}

/-- **The canonical map of [Stacks, Tag 0EX3] (c) is compatible with restriction to a compatible
pair of opens of the two bases.** Let `V` be an open of `Y'` and `W` an open of `Y''` with
`W ≤ h⁻¹(V)`. The situation restricts to `V` (`TopDegreeBaseChangeSituation.restrictBase`), the
cartesian square restricts to the square over `W ⟶ V`
(`isPullback_resLE_of_isPullback`), and `F'` restricts to `f'⁻¹(V)`. Then the canonical map `γ`
of the restricted data is invertible exactly when the restriction to `W` of `γ` is.

The proof pastes the restricted square with the open-immersion square of `V ⊆ Y'` on its right
and, separately, the square of `W ⊆ Y''` with the given square on its left. The two rectangles
coincide, so their two-step composites agree; the open-immersion squares contribute isomorphisms
(their base change maps are invertible, [Stacks, Tag 08HY] along an open immersion, and their
derived pullbacks are underived), and `Hᵈ` commutes with restriction to `W`. -/
theorem isIso_topDirectImageBaseChangeMap_restrictBase_iff
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (sq : IsPullback h' f'' S.f' h)
    (V : S.Y'.Opens) (W : Y''.Opens) (hWV : W ≤ h ⁻¹ᵁ V) :
    IsIso (@topDirectImageBaseChangeMap _ _ (S.restrictBase V)
        ((Scheme.Modules.pullback (S.f' ⁻¹ᵁ V).ι).obj F')
        (AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion (S.f' ⁻¹ᵁ V).ι F')
        (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) (preimage_le_preimage_of_isPullback sq hWV))
        (f'' ∣_ W) (h.resLE V W hWV)
        (toShHom_comm_of_isPullback _ _ _ (isPullback_resLE_of_isPullback sq hWV))) ↔
      IsIso ((Scheme.Modules.restrictFunctor W.ι).map
        (topDirectImageBaseChangeMap S F' h' f'' h (toShHom_comm_of_isPullback h' f'' h sq))) := by
  have hsqV := isPullback_toShHom_of_isOpenImmersion _ _ _ _
    (isPullback_morphismRestrict S.f' V).flip
  have hsqW := isPullback_toShHom_of_isOpenImmersion _ _ _ _
    (isPullback_morphismRestrict f'' W).flip
  have eg := congrArg (fun k => Scheme.Hom.toLRSHom k |>.toShHom)
    (Scheme.Hom.resLE_comp_ι h' (preimage_le_preimage_of_isPullback sq hWV))
  have eh := congrArg (fun k => Scheme.Hom.toLRSHom k |>.toShHom) (Scheme.Hom.resLE_comp_ι h hWV)
  simp only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] at eg eh
  refine (@isIso_topDirectImageBaseChangeMap_iff _ _ (S.restrictBase V) _
    (AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion (S.f' ⁻¹ᵁ V).ι F')
    _ _ _ _).trans ?_
  refine (isIso_homologyFunctor_map_iff_of_isOpenImmersions_right _ _ _ _ _ _ _ hsqV
    (toShHom_comm_of_isPullback _ _ _ (isPullback_resLE_of_isPullback sq hWV)) F' _).trans ?_
  refine (isIso_homologyFunctor_map_derivedBaseChangeMap_comp_congr _ _ eg eh _
    (hcomp_square _ _ _ _ _ _ _ (toShHom_comm_of_isPullback h' f'' h sq) hsqW.w) F' _).trans ?_
  refine (isIso_homologyFunctor_map_derivedPullback_map_iff_of_isOpenImmersions_left _ _ _ _ _ _
    _ (toShHom_comm_of_isPullback h' f'' h sq) hsqW F' _).symm.trans ?_
  refine (isIso_homologyFunctor_map_derivedPullback_map_iff W.ι _ _).trans ?_
  refine (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback W.ι) _).symm.trans ?_
  refine (isIso_comp_left_iff
    ((Scheme.Modules.restrictFunctor W.ι).map (topDirectImagePullbackIso S F' h).hom)
    _).symm.trans ?_
  exact Iff.of_eq (congrArg IsIso
    ((Scheme.Modules.restrictFunctor W.ι).map_comp (topDirectImagePullbackIso S F' h).hom _).symm)

/-- **Conclusion (c) of [Stacks, Tag 0EX3] reduces to affine bases.** If the canonical map `γ` is
an isomorphism for every top-degree base-change situation whose base `Y'` is affine and every
cartesian second square whose base `Y''` is affine, then it is an isomorphism for every situation
and every cartesian second square.

This is the source's *"we can check (a), (b), and (c) locally on `Y'` and `Y''`"* for (c). The
affine opens `W` of `Y''` lying over an affine open `V` of `Y'` cover `Y''`
(`exists_isAffineOpen_cover_over`), invertibility of a morphism of sheaves of modules is local
(`isIso_topDirectImageBaseChangeMap_of_isIso_restrict`), and over each such pair the restriction
of `γ` is the `γ` of the restricted situation and square
(`isIso_topDirectImageBaseChangeMap_restrictBase_iff`), whose two bases `V` and `W` are affine.

The affine case is an explicit hypothesis here; this is an intermediate step, not conclusion (c),
and carries no `@[stacks 0EX3]` attribute. -/
theorem isIso_topDirectImageBaseChangeMap_of_affine
    (hA : ∀ (T : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u}) [IsAffine T.Y']
      {X₂ Y₂ : Scheme.{u}} [IsAffine Y₂] (a' : X₂ ⟶ T.X') (b : X₂ ⟶ Y₂) (a : Y₂ ⟶ T.Y')
      (sq : IsPullback a' b T.f' a) (G : T.X'.Modules) [G.IsQuasicoherent],
      IsIso (topDirectImageBaseChangeMap T G a' b a (toShHom_comm_of_isPullback a' b a sq)))
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (sq : IsPullback h' f'' S.f' h) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h (toShHom_comm_of_isPullback h' f'' h sq)) := by
  obtain ⟨W, hW, hWV⟩ := exists_isAffineOpen_cover_over h
  refine isIso_topDirectImageBaseChangeMap_of_isIso_restrict S F' h' f'' h _ W hW fun z => ?_
  obtain ⟨hWz, V, hV, hsub⟩ := hWV z
  have : IsAffine (V : Scheme) := hV
  have : IsAffine (W z : Scheme) := hWz
  exact (isIso_topDirectImageBaseChangeMap_restrictBase_iff S F' h' f'' h sq V (W z) hsub).1
    (@hA (S.restrictBase V) inferInstance _ _ inferInstance _ _ _
      (isPullback_resLE_of_isPullback sq hsub) _
      (AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion (S.f' ⁻¹ᵁ V).ι F'))

end Schemes

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
