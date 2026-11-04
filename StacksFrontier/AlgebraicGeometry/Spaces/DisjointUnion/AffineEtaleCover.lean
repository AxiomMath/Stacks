module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValuedRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# A surjective étale map from a disjoint union of affines

Every algebraic space `Y` over `S` receives a surjective étale morphism `V₀ ⟶ Y` from an
algebraic space `V₀ = ⨆ i, Y i` which is a disjoint union, in the sheaves of sets on the big
fppf site, of affine schemes `Y i`: refine an étale atlas `U ⟶ Y` by the disjoint union of all
affine opens of `U` (compare Stacks 03FX).

## Main results

* `AlgebraicGeometry.Space.exists_isColimit_cofan_affine_etale_surjective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A surjective étale map from a disjoint union of affines.** Every algebraic space `Y`
over `S` receives a surjective étale morphism `b₀ : V₀ ⟶ Y` whose source is the disjoint union,
in the sheaves of sets on the big fppf site of `S`, of a family `Y i` of affine schemes, with
injections `j i : Y i ⟶ V₀`; `b₀` is relatively representable, its source being a scheme. -/
theorem exists_isColimit_cofan_affine_etale_surjective (Y : AlgebraicSpaces B S hS) :
    ∃ (ι : Type u) (Yi : ι → AlgebraicSpaces B S hS) (V₀ : AlgebraicSpaces B S hS)
      (j : ∀ i, Yi i ⟶ V₀) (b₀ : V₀ ⟶ Y),
      (∀ i, IsAffineSpace B S hS (Yi i).1) ∧ IsEtale B S hS b₀.hom ∧
        IsSurjective B S hS b₀.hom ∧ yoneda.relativelyRepresentable b₀.hom ∧
        Nonempty (IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj V₀)
          fun i => (algebraicSpacesToSheaf B S hS).map (j i))) := by
  obtain ⟨U, p, hpS, hpE⟩ := Y.2.exists_atlas
  obtain ⟨ι, X, V, j, q, hXaff, -, -, -, hqsurj, hqet, -, ⟨hV⟩⟩ :=
    BigFppfOver.exists_affineOpens_surjective_etale_sigma' B S hS U
  let J := BigFppfOver.topology B S hS
  have hY : IsColimit (Cofan.mk (J.yoneda.obj V) fun i => J.yoneda.map (j i)) :=
    (((fullyFaithful_reflectsColimits.{u, u}
      (sheafCompose J uliftFunctor.{u + 1, u})).reflectsColimitsOfShape
        (J := Discrete ι)).reflectsColimit
          (K := Discrete.functor fun i => J.yoneda.obj (X i))).reflects
      ((Cofan.isColimitMapCoconeEquiv (sheafCompose J uliftFunctor.{u + 1, u}) _
        (Cofan.mk (J.yoneda.obj V) fun i => J.yoneda.map (j i))).symm hV) |>.some
  refine ⟨ι, fun i => schemeSpace (X i), schemeSpace V, fun i => schemeSpaceMap (j i),
    ObjectProperty.homMk (yoneda.map q ≫ p),
    fun i => isAffineSpace_yoneda B S hS (X i) (hXaff i),
    isEtale_comp B S hS (isEtale_schemeSpaceMap B S hS V q hqet)
      (isEtale_of_presheaf_etale B S hS hpE),
    isSurjective_comp B S hS (fun w => mem_range_pointsMap_yoneda_map B S hS q w
      (hqsurj.surj _)) (isSurjective_of_presheafSurjective B S hS p hpS),
    Functor.relativelyRepresentable.of_diag Y.2.diagonal_representable _, ⟨hY⟩⟩

end AlgebraicGeometry.Space

end
