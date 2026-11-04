module

public import StacksFrontier.Deformation.Examples.Geometric.SmoothingProper
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingFormalTower
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingFamilyOperations
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SyntomicFibres

/-!
# Smoothing a proper curve with isolated local complete intersection singularities

This file proves [Stacks, Tag 0E7Y]: a scheme `X` proper over a field `k` which is a local
complete intersection over `k`, of dimension at most one, and smooth over `k` away from finitely
many points, is the special fibre of a flat projective morphism `Y ⟶ Spec k⟦t⟧` whose generic
fibre is smooth.

The proof is the source's.

* `X = X' ⨿ X''` with `X'` of dimension zero and `X''` equidimensional of dimension one
  (`Deformation.Examples.Smoothing.exists_isCompl_zeroDimensional_equidimensional`, from the
  source's appeal to Algebra 00SB and Morphisms 02NM).
* `X'` is smoothed by the finite family of [Stacks, Tag 0E7W]
  (`Smoothing.exists_flat_finite_projective_smoothing_of_topologicalKrullDim_le_zero`).
* For `X''` there is a formal smoothing: a cartesian tower of flat deformations `Xₙ` of `X''` over
  `Spec (k⟦t⟧ ⧸ (t) ^ (n + 1))` whose first Fitting ideal contains `t ^ n` at some level
  (`Deformation.Examples.Smoothing.exists_formalSmoothingTower`: Tags 0E7X, 0DZP and 06HN).
  It algebraizes to a flat projective family with smooth generic fibre
  (`Deformation.Examples.Smoothing.exists_flat_isProjective_smoothing_of_tower`: Tags 0E7R, 0D4G
  and 0E7T).
* The two families are put side by side
  (`Deformation.Examples.Smoothing.exists_smoothing_of_isCompl`); a disjoint union of projective
  morphisms over the affine base `Spec k⟦t⟧` is projective
  (`AlgebraicGeometry.isProjective_coprod_desc_of_isAffine`).

## Main results

* `Deformation.Examples.Smoothing.exists_flat_isProjective_smoothing_of_isProper`: Tag 0E7Y.

## References

* [The Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Deformation.Examples.Smoothing

variable (k : Type u) [Field k]

/-- **The equidimensional one-dimensional piece of [Stacks, Tag 0E7Y].** A scheme proper over `k`,
equidimensional of dimension one, which is a local complete intersection over `k` smooth away
from finitely many points, is the special fibre of a flat projective family over `Spec k⟦t⟧` with
smooth generic fibre: the formal smoothing tower algebraizes. -/
theorem exists_flat_isProjective_smoothing_of_equidimensional {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hf : IsLocalCompleteIntersectionOverField f)
    (hfin : (f.smoothLocus : Set X)ᶜ.Finite) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      Flat g ∧ AlgebraicGeometry.IsProjective g ∧
      Smooth (g.fiberToSpecResidueField
        (⟨⊥, inferInstance⟩ : PrimeSpectrum (PowerSeries k))) ∧
      ∃ e : X ≅ pullback g
          (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
        e.hom ≫ pullback.snd g
            (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = f := by
  obtain ⟨Xn, q, i, hcart, hflat, ⟨e0, he0⟩, hfit⟩ :=
    exists_formalSmoothingTower k f hf hfin hdim.le
  have hq0 : q 0 = (e0.inv ≫ f) ≫ (specBottomIso k).hom := by
    rw [← he0, ← specBottomIso_inv]; simp
  have hprop : IsProper (q 0) := by rw [hq0]; infer_instance
  have hCM0 : IsCohenMacaulay (Xn 0) :=
    (isCohenMacaulay_iff_of_iso e0).mp (isCohenMacaulay_of_syntomic_over_field f hf)
  have hequi0 : TopologicalSpace.Equidimensional (Xn 0) :=
    TopologicalSpace.Equidimensional.of_homeomorph (Scheme.homeoOfIso e0).symm hequi
  have hdim0 : topologicalKrullDim (Xn 0) = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e0).isHomeomorph, hdim]
  obtain ⟨Y, g, hg, hproj, hsm, e, he⟩ := exists_flat_isProjective_smoothing_of_tower k q i hcart
    hflat hprop hCM0 hequi0 hdim0 hfit
  exact ⟨Y, g, hg, hproj, hsm, e0 ≪≫ e, by simp [he, he0]⟩

/-- An open and closed subscheme of a scheme quasi-compact over `Spec k` is quasi-compact over
`Spec k`. -/
theorem quasiCompact_ι_comp_of_isClosed {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [QuasiCompact f] (W : X.Opens) (hW : IsClosed (W : Set X)) : QuasiCompact (W.ι ≫ f) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.isCompact
  infer_instance

/-- **[Stacks, Tag 0E7Y].** Let `X` be a scheme over a field `k`. Assume (1) `X` is proper over
`k`, (2) `X` is a local complete intersection over `k`, (3) `X` has dimension `≤ 1`, and (4)
`X → Spec(k)` is smooth except at finitely many points. Then there exists a flat projective
morphism `Y → Spec(k[[t]])` whose generic fibre is smooth and whose special fibre is isomorphic to
`X`.

The generic fibre is the fibre over the zero ideal of `k⟦t⟧`, smooth over its residue field. The
special fibre is the base change along `Spec k ⟶ Spec k⟦t⟧` given by the constant coefficient,
and the isomorphism with `X` is one of schemes over `Spec k`. Projectivity is
`AlgebraicGeometry.IsProjective`, [Stacks, Tag 01W8]. -/
@[stacks 0E7Y]
theorem exists_flat_isProjective_smoothing_of_isProper {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (hf : IsLocalCompleteIntersectionOverField f) (hdim : topologicalKrullDim X ≤ 1)
    (hfin : (f.smoothLocus : Set X)ᶜ.Finite) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      Flat g ∧ AlgebraicGeometry.IsProjective g ∧
      Smooth (g.fiberToSpecResidueField
        (⟨⊥, inferInstance⟩ : PrimeSpectrum (PowerSeries k))) ∧
      ∃ e : X ≅ pullback g
          (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
        e.hom ≫ pullback.snd g
            (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = f := by
  obtain ⟨U, V, hUV, -, hVci, hU0, hVequi, hVdim⟩ :=
    exists_isCompl_zeroDimensional_equidimensional k f hdim
  have hsyn : ∀ W : X.Opens, IsLocalCompleteIntersectionOverField (W.ι ≫ f) :=
    isLocalCompleteIntersectionOverField_ι_comp k f hf
  have hcl : ∀ {A B : X.Opens}, IsCompl A B → IsClosed (A : Set X) := fun {A B} h => by
    have : IsCompl (A : Set X) B := ⟨Opens.coe_disjoint.mpr h.1,
      codisjoint_iff.mpr (by
        change (A : Set X) ∪ B = Set.univ
        rw [← Opens.coe_sup, h.sup_eq_top, Opens.coe_top])⟩
    rw [this.eq_compl]
    exact B.isOpen.isClosed_compl
  have zero : ∀ W : X.Opens, IsClosed (W : Set X) → topologicalKrullDim W ≤ 0 →
      ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
        AlgebraicGeometry.IsProjective g ∧ Flat g ∧
        Smooth (g.fiberToSpecResidueField
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k))) ∧
        ∃ e : W.toScheme ≅
            pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
          e.hom ≫ pullback.snd g
              (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = W.ι ≫ f := by
    intro W hW hW0
    have := quasiCompact_ι_comp_of_isClosed k f W hW
    obtain ⟨Y, g, hg, -, hproj, hsm, e, he⟩ :=
      exists_flat_finite_projective_smoothing_of_topologicalKrullDim_le_zero k (W.ι ≫ f)
        (hsyn W) hW0
    exact ⟨Y, g, hproj, hg, hsm, e, he⟩
  obtain ⟨Y, g, hproj, hg, hsm, e, he⟩ := exists_smoothing_of_isCompl k f hUV
    (fun _ _ g => AlgebraicGeometry.IsProjective g)
    (fun g₁ g₂ h₁ h₂ => isProjective_coprod_desc_of_isAffine g₁ g₂ h₁ h₂)
    (zero U (hcl hUV) hU0) (by
      by_cases hV : IsEmpty V
      · exact zero V (hcl hUV.symm) ((topologicalKrullDim_eq_bot_iff_isEmpty V).mpr hV ▸ bot_le)
      · have := hVci
        obtain ⟨Y, g, hg, hproj, hsm, e, he⟩ :=
          exists_flat_isProjective_smoothing_of_equidimensional k (V.ι ≫ f) (hsyn V)
            (finite_compl_smoothLocus_ι_comp k f hfin V) hVequi
            (hVdim (not_isEmpty_iff.mp hV))
        exact ⟨Y, g, hproj, hg, hsm, e, he⟩)
  exact ⟨Y, g, hg, hproj, hsm, e, he⟩

end Deformation.Examples.Smoothing
