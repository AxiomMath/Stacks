module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.ConstantFamilyDescent
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.FibreIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniSmooth
import StacksCore.Tactic.StacksAttribute

/-!
# No deformations of a smooth proper family with a trivialized relative equivalence

Let `k` be a field, let `S` be of finite type over `k` with a `k`-rational point `s`, and let
`g : Y ⟶ S` be smooth and proper. Write `Y_s = Y ×_S Spec k` for the fibre and
`X = Y_s ×_k S ⟶ S` for the constant family with that fibre. If `K` is the Fourier-Mukai kernel of
a relative equivalence from `X` to `Y` over `S` whose derived restriction along the comparison
morphism `i : Y_s ×_k Y_s ⟶ X ×_S Y` is the diagonal kernel `Δ_{Y_s/k,*}𝒪_{Y_s}`, then `Y` is
constant near `s`: there is an open `U ⊆ S` containing the point `s` picks out with
`Y|_U ≅ Y_s ×_k U` over `U`.

That is [Stacks, Tag 0G0R].

## Main results

* `AlgebraicGeometry.exists_opens_nonempty_iso_constantFamily_of_isRelativeEquivalenceKernel`:
  **[Stacks, Tag 0G0R].**
* `AlgebraicGeometry.exists_opens_nonempty_iso_constantFamily_of_isPerfect`: the same for any
  perfect kernel with the given restriction, the form [Stacks, Tag 0G0S] applies.

## Implementation notes

The subscheme the source builds by gluing is the scheme-theoretic support `Z` of `H^0(K)`
(`AlgebraicGeometry.cohomologySupportIdeal`), global from the start. What the source's local
analysis gives is then recovered pointwise:

* `AlgebraicGeometry.comap_cohomologySupportIdeal_eq_ker_diagonal` says the fibre of `Z` over `s`
  is the diagonal of `Y_s`, as closed subschemes of `Y_s ×_k Y_s`;
* `AlgebraicGeometry.exists_ideal_derivedStalk_iso_single_diagonal` gives, at a point of the
  diagonal, the flatness of `Z` over `S` there.

The fibre of `Z` over `s` is identified with `Y_s` by pasting two cartesian squares — the
inverse-image square of an ideal sheaf (`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_comap`)
over the fibre square of `i` (`AlgebraicGeometry.isPullback_fibreSquareToProductComparison`) —
and then by the identification of a closed immersion with the subscheme its kernel cuts out, which
is the universal property `AlgebraicGeometry.IsClosedImmersion.lift` applied in both directions.

With that identification the two projections `Z_s ⟶ X_s` and `Z_s ⟶ Y_s` become the two
projections of the diagonal, hence isomorphisms, and
`AlgebraicGeometry.exists_opens_nonempty_iso_constantFamily_of_isIso_fibre_of_isSection` — which
is [Stacks, Tag 0G0Q] with the properness shrink — finishes.

Only the first clause of `AlgebraicGeometry.IsRelativeEquivalenceKernel`, perfectness of `K`, is
used; the registered statement nevertheless takes the source's hypothesis in full, as the source
states it, and is the instance of the perfect-kernel generalization.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G0Q](https://stacks.math.columbia.edu/tag/0G0Q)
* [Stacks Project, Tag 0G0I](https://stacks.math.columbia.edu/tag/0G0I)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {S Y : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (s : Spec (.of k) ⟶ S)
  [LocallyOfFiniteType q] [QuasiCompact q] [Smooth g] [IsProper g]

/-- **A closed immersion is the subscheme its kernel cuts out.** -/
theorem exists_iso_subscheme_ker {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (I : X.IdealSheafData) (hI : I = f.ker) :
    ∃ e : Z ≅ I.subscheme, e.hom ≫ I.subschemeι = f := by
  have h : I.subschemeι.ker = f.ker := by rw [Scheme.IdealSheafData.ker_subschemeι, hI]
  refine ⟨⟨IsClosedImmersion.lift I.subschemeι f h.le, IsClosedImmersion.lift f I.subschemeι h.ge,
    ?_, ?_⟩, IsClosedImmersion.lift_fac _ _ h.le⟩
  · simp [← cancel_mono f]
  · simp [← cancel_mono I.subschemeι]

/-- **Flatness at a point of the subscheme, read at a point of the ambient scheme named
separately.** `AlgebraicGeometry.isFlatAt_subschemeι_comp_of_derivedStalk_iso_single` with the
point of `W` given as an equality, so that a caller who produces the derived-stalk description at
a point it knows under another name needs no transport. -/
theorem isFlatAt_subschemeι_comp_of_derivedStalk_iso_single_of_eq {W S' : Scheme.{u}}
    [IsLocallyNoetherian W] (p : W ⟶ S') (K : DerivedCategory W.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) K)
    (ζ : (cohomologySupportIdeal K hK).subscheme) (z : W)
    (hz : z = (cohomologySupportIdeal K hK).subschemeι ζ) (I : Ideal (W.presheaf.stalk z))
    (e : (derivedStalkFunctor z).obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (W.presheaf.stalk z)) 0).obj
        (ModuleCat.of (W.presheaf.stalk z) (W.presheaf.stalk z ⧸ I)))
    (hflat : RingHom.Flat ((Ideal.Quotient.mk I).comp (p.stalkMap z).hom)) :
    AlgebraicGeometry.IsFlatAt
      ((cohomologySupportIdeal K hK).subschemeι ≫ p).toLRSHom.toShHom ζ := by
  subst hz
  exact isFlatAt_subschemeι_comp_of_derivedStalk_iso_single p K hK ζ I e hflat

/-- **The fibre of `Z` over `s` is `Y_s`, through the diagonal.** The fibre over the `k`-rational
point `s` of the scheme-theoretic support of `H^0(K)` is `Y_s`, by an isomorphism whose composite
into `X ×_S Y` is the diagonal of `Y_s` followed by the comparison morphism. -/
theorem exists_iso_fibre_cohomologySupportSubscheme (hs : s ≫ q = 𝟙 _)
    (K : DerivedCategory (Limits.pullback (constantFamilyπ q g s) g).Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Limits.pullback (constantFamilyπ q g s) g).toRingedSpace) K)
    (hdiag : Nonempty ((derivedPullback
        (fibreSquareToProductComparison q g s hs).toLRSHom.toShHom).obj K ≅
      diagonalKernel (fibreAtRationalPointπ g s))) :
    ∃ e : fibreAtRationalPoint g s ≅ Limits.pullback
        ((cohomologySupportIdeal K hK).subschemeι ≫ constantFamilyProductToBase q g s) s,
      e.hom ≫ Limits.pullback.fst _ s ≫ (cohomologySupportIdeal K hK).subschemeι =
          Limits.pullback.diagonal (fibreAtRationalPointπ g s) ≫
            fibreSquareToProductComparison q g s hs ∧
        e.hom ≫ Limits.pullback.snd _ s = fibreAtRationalPointπ g s := by
  have hci : IsClosedImmersion (fibreSquareToProductComparison q g s hs) :=
    isClosedImmersion_fibreSquareToProductComparison q g s hs
  obtain ⟨u, hu⟩ := exists_iso_subscheme_ker
    (Limits.pullback.diagonal (fibreAtRationalPointπ g s))
    ((cohomologySupportIdeal K hK).comap (fibreSquareToProductComparison q g s hs))
    (comap_cohomologySupportIdeal_eq_ker_diagonal q g s hs K hK hdiag)
  have hpaste :
      IsPullback ((cohomologySupportIdeal K hK).comap
            (fibreSquareToProductComparison q g s hs) |>.subschemeMap
          (cohomologySupportIdeal K hK) (fibreSquareToProductComparison q g s hs)
          ((cohomologySupportIdeal K hK).le_map_comap
            (fibreSquareToProductComparison q g s hs)))
        (((cohomologySupportIdeal K hK).comap
            (fibreSquareToProductComparison q g s hs)).subschemeι ≫
          (Limits.pullback.snd (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s) ≫
            fibreAtRationalPointπ g s))
        ((cohomologySupportIdeal K hK).subschemeι ≫ constantFamilyProductToBase q g s) s :=
    ((Scheme.IdealSheafData.isPullback_comap (cohomologySupportIdeal K hK)
      (fibreSquareToProductComparison q g s hs)).flip).paste_vert
      (isPullback_fibreSquareToProductComparison q g s hs)
  refine ⟨u ≪≫ hpaste.isoPullback, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc]
    rw [← Category.assoc (hpaste.isoPullback.hom), hpaste.isoPullback_hom_fst,
      Scheme.IdealSheafData.subschemeMap_subschemeι, ← Category.assoc, hu]
  · simp only [Iso.trans_hom, Category.assoc]
    rw [hpaste.isoPullback_hom_snd, ← Category.assoc, hu, ← Category.assoc,
      Limits.pullback.diagonal_snd, Category.id_comp]

/-- The first component of the base change of a morphism over `S` along `s`. -/
theorem overPullback_map_left_comp_fst {S' A B T : Scheme.{u}} (h₁ : A ⟶ S') (h₂ : B ⟶ S')
    (t : T ⟶ S') (φ : Over.mk h₁ ⟶ Over.mk h₂) :
    ((Over.pullback t).map φ).left ≫ Limits.pullback.fst h₂ t =
      Limits.pullback.fst h₁ t ≫ φ.left :=
  Limits.pullback.lift_fst _ _ _

/-- The second component of the base change of a morphism over `S` along `s`. -/
theorem overPullback_map_left_comp_snd {S' A B T : Scheme.{u}} (h₁ : A ⟶ S') (h₂ : B ⟶ S')
    (t : T ⟶ S') (φ : Over.mk h₁ ⟶ Over.mk h₂) :
    ((Over.pullback t).map φ).left ≫ Limits.pullback.snd h₂ t =
      Limits.pullback.snd h₁ t :=
  Limits.pullback.lift_snd _ _ _

/-- Let `K ∈ D(𝒪_{X ×_S Y})` be perfect, with derived restriction along the comparison morphism
`i : Y_s ×_k Y_s ⟶ X ×_S Y` isomorphic to the diagonal kernel `Δ_{Y_s/k,*}𝒪_{Y_s}`. Then there
is an open `U ⊆ S` containing the image of `s` over which `X` is isomorphic to the constant
family `Y_s × U`.

This is [Stacks, Tag 0G0R] with the kernel only assumed perfect, which is the form
[Stacks, Tag 0G0S] applies. -/
theorem exists_opens_nonempty_iso_constantFamily_of_isPerfect
    (rational : s ≫ q = 𝟙 _)
    (K : DerivedCategory (Limits.pullback (constantFamilyπ q g s) g).Modules)
    (hpperf : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Limits.pullback (constantFamilyπ q g s) g).toRingedSpace) K)
    (restrict : Nonempty ((derivedPullback
        (fibreSquareToProductComparison q g s rational).toLRSHom.toShHom).obj K ≅
      diagonalKernel (fibreAtRationalPointπ g s))) :
    ∃ U : S.Opens, Set.range s.base ⊆ (U : Set S) ∧
      Nonempty ((Over.pullback U.ι).obj (Over.mk g) ≅
        Over.mk (Limits.pullback.snd (fibreAtRationalPointπ g s) (U.ι ≫ q))) := by
  have hNW : IsLocallyNoetherian (Limits.pullback (constantFamilyπ q g s) g) :=
    isLocallyNoetherian_fibreProduct q g s
  have hproper : IsProper (constantFamilyProductToBase q g s) :=
    isProper_constantFamilyProductToBase q g s
  have hci : IsClosedImmersion (fibreSquareToProductComparison q g s rational) :=
    isClosedImmersion_fibreSquareToProductComparison q g s rational
  obtain ⟨eZ, heZfst, heZsnd⟩ :=
    exists_iso_fibre_cohomologySupportSubscheme q g s rational K hpperf restrict
  have heZfst' : ∀ {T : Scheme.{u}}
      (m : Limits.pullback (constantFamilyπ q g s) g ⟶ T),
      eZ.hom ≫ Limits.pullback.fst ((cohomologySupportIdeal K hpperf).subschemeι ≫
            constantFamilyProductToBase q g s) s ≫
          (cohomologySupportIdeal K hpperf).subschemeι ≫ m =
        Limits.pullback.diagonal (fibreAtRationalPointπ g s) ≫
          fibreSquareToProductComparison q g s rational ≫ m := fun m => by
    simpa only [Category.assoc] using heZfst =≫ m
  have hZproper : IsProper (Over.mk ((cohomologySupportIdeal K hpperf).subschemeι ≫
      constantFamilyProductToBase q g s)).hom :=
    inferInstanceAs (IsProper ((cohomologySupportIdeal K hpperf).subschemeι ≫
      constantFamilyProductToBase q g s))
  -- the two projections out of `Z`
  let a : Over.mk ((cohomologySupportIdeal K hpperf).subschemeι ≫
      constantFamilyProductToBase q g s) ⟶ Over.mk (constantFamilyπ q g s) :=
    Over.homMk ((cohomologySupportIdeal K hpperf).subschemeι ≫
      Limits.pullback.fst (constantFamilyπ q g s) g)
      (by simp [Limits.pullback.condition])
  let b : Over.mk ((cohomologySupportIdeal K hpperf).subschemeι ≫
      constantFamilyProductToBase q g s) ⟶ Over.mk g :=
    Over.homMk ((cohomologySupportIdeal K hpperf).subschemeι ≫
      Limits.pullback.snd (constantFamilyπ q g s) g) (by simp)
  -- flatness of `Z` over `S` above `s`
  have hZflat : ∀ ζ : (Over.mk ((cohomologySupportIdeal K hpperf).subschemeι ≫
        constantFamilyProductToBase q g s)).left,
      (Over.mk ((cohomologySupportIdeal K hpperf).subschemeι ≫
          constantFamilyProductToBase q g s)).hom ζ =
        s.base (IsLocalRing.closedPoint k) →
      AlgebraicGeometry.IsFlatAt (Over.mk ((cohomologySupportIdeal K hpperf).subschemeι ≫
        constantFamilyProductToBase q g s)).hom.toLRSHom.toShHom ζ := by
    intro ζ hζ
    obtain ⟨w, hw⟩ : (cohomologySupportIdeal K hpperf).subschemeι ζ ∈
        Set.range (fibreSquareToProductComparison q g s rational).base := by
      rw [range_fibreSquareToProductComparison q g s rational]
      exact ⟨IsLocalRing.closedPoint k, hζ.symm⟩
    obtain ⟨y, rfl⟩ :
        w ∈ Set.range (Limits.pullback.diagonal (fibreAtRationalPointπ g s)).base := by
      by_contra hwnot
      exact notMem_support_cohomologySupportIdeal_of_notMem_range_diagonal q g s rational K hpperf
        restrict w hwnot (hw ▸ ζ.2)
    obtain ⟨I, ⟨eI⟩, -, hflatI⟩ :=
      exists_ideal_derivedStalk_iso_single_diagonal q g s rational K hpperf restrict y
    exact isFlatAt_subschemeι_comp_of_derivedStalk_iso_single_of_eq
      (constantFamilyProductToBase q g s) K hpperf ζ _ hw I eI hflatI
  -- the fibre of `Z` maps isomorphically to the fibre of `X`
  have ha : IsIso ((Over.pullback s).map a).left := by
    have hsq : IsPullback (Limits.pullback.snd (constantFamilyπ q g s) s)
        (Limits.pullback.fst (constantFamilyπ q g s) s ≫
          Limits.pullback.fst (fibreAtRationalPointπ g s) q)
        (s ≫ q) (fibreAtRationalPointπ g s) :=
      (IsPullback.of_hasPullback (constantFamilyπ q g s) s).flip.paste_vert
        (IsPullback.of_hasPullback (fibreAtRationalPointπ g s) q).flip
    have hXs : IsIso (Limits.pullback.fst (constantFamilyπ q g s) s ≫
        Limits.pullback.fst (fibreAtRationalPointπ g s) q) :=
      MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u}) hsq
        (rational ▸ (MorphismProperty.isomorphisms Scheme.{u}).id_mem _)
    have h1 : ((Over.pullback s).map a).left ≫
        (Limits.pullback.fst (constantFamilyπ q g s) s ≫
          Limits.pullback.fst (fibreAtRationalPointπ g s) q) =
        Limits.pullback.fst ((cohomologySupportIdeal K hpperf).subschemeι ≫
            constantFamilyProductToBase q g s) s ≫
          (cohomologySupportIdeal K hpperf).subschemeι ≫
            (Limits.pullback.fst (constantFamilyπ q g s) g ≫
              Limits.pullback.fst (fibreAtRationalPointπ g s) q) := by
      rw [← Category.assoc (((Over.pullback s).map a).left),
        overPullback_map_left_comp_fst _ _ s a]
      simp only [a, Over.homMk_left, Category.assoc]
    have hcomp : eZ.hom ≫ (((Over.pullback s).map a).left ≫
        (Limits.pullback.fst (constantFamilyπ q g s) s ≫
          Limits.pullback.fst (fibreAtRationalPointπ g s) q)) = 𝟙 _ := by
      rw [h1, heZfst' _, ← Category.assoc (fibreSquareToProductComparison q g s rational),
        fibreSquareToProductComparison_comp_fst_fst, Limits.pullback.diagonal_fst]
    have := isIso_of_hom_comp_eq_id eZ.hom hcomp
    exact IsIso.of_isIso_comp_right _ (Limits.pullback.fst (constantFamilyπ q g s) s ≫
      Limits.pullback.fst (fibreAtRationalPointπ g s) q)
  -- the fibre of `Z` maps isomorphically to the fibre of `Y`
  have hb : IsIso ((Over.pullback s).map b).left := by
    have hcomp : eZ.hom ≫ ((Over.pullback s).map b).left = 𝟙 _ := by
      refine Limits.pullback.hom_ext ?_ ?_
      · simp only [Over.mk_hom]
        rw [Category.assoc, overPullback_map_left_comp_fst _ _ s b, Category.id_comp]
        simp only [b, Over.homMk_left]
        rw [heZfst' (Limits.pullback.snd (constantFamilyπ q g s) g),
          fibreSquareToProductComparison_comp_snd, ← Category.assoc,
          Limits.pullback.diagonal_snd, Category.id_comp]
      · simp only [Over.mk_hom]
        rw [Category.assoc, overPullback_map_left_comp_snd _ _ s b, heZsnd, Category.id_comp]
    exact isIso_of_hom_comp_eq_id eZ.hom hcomp
  exact exists_opens_nonempty_iso_constantFamily_of_isIso_fibre_of_isSection q g s rational a b
    hZflat ha hb

/-- **[Stacks, Tag 0G0R].** Let `k` be a field, `q : S ⟶ Spec k` of finite type, `s` a
`k`-rational point of `S` (a section of `q`), and `g : Y ⟶ S` smooth and proper. Let
`X = Y_s ×_k S` be the constant family with fibre `Y_s = Y ×_S Spec k`. If `K` is the Fourier-Mukai
kernel of a relative equivalence from `X` to `Y` over `S` whose derived restriction along the
comparison morphism `i : Y_s ×_k Y_s ⟶ X ×_S Y` is the diagonal kernel `Δ_{Y_s/k,*}𝒪_{Y_s}`, then
there is an open `U ⊆ S` containing the point `s` picks out with `Y|_U` isomorphic to `Y_s ×_k U`
over `U`. -/
@[stacks 0G0R]
theorem exists_opens_nonempty_iso_constantFamily_of_isRelativeEquivalenceKernel
    (rational : s ≫ q = 𝟙 _)
    (K : DerivedCategory (Limits.pullback (constantFamilyπ q g s) g).Modules)
    (relEquiv : IsRelativeEquivalenceKernel (constantFamilyπ q g s) g K)
    (restrict : Nonempty ((derivedPullback
        (fibreSquareToProductComparison q g s rational).toLRSHom.toShHom).obj K ≅
      diagonalKernel (fibreAtRationalPointπ g s))) :
    ∃ U : S.Opens, Set.range s.base ⊆ (U : Set S) ∧
      Nonempty ((Over.pullback U.ι).obj (Over.mk g) ≅
        Over.mk (Limits.pullback.snd (fibreAtRationalPointπ g s) (U.ι ≫ q))) :=
  exists_opens_nonempty_iso_constantFamily_of_isPerfect q g s rational K relEquiv.1 restrict

end AlgebraicGeometry

end
