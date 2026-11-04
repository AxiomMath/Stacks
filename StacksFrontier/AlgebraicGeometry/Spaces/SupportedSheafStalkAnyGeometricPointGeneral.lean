module

public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafPushforwardStalkGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafStalkAnyGeometricPoint
import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSmallEtale
import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint

/-!
# The stalk of a direct image of a supported sheaf, at an arbitrary geometric point, along an
arbitrary morphism

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `i : Z ⟶ X` be a
closed immersion and let `i' : W ⟶ Y` be its inverse image, through an integral and universally
injective `f' : W ⟶ Z`.  For an abelian sheaf `K` on the small étale site of `Y` supported on
`|W|` the canonical comparison `(f_*K)_{f(ȳ)} ⟶ K_ȳ` is an isomorphism at *every* geometric
point `ȳ` of `Y`, not only at those lying on `W`.

This is
`AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support_of_isPullback`
— the degree-zero case of Stacks 0AEQ — with the hypothesis that `f` be representable removed.
It is the input Stacks 0AER rests on.

A geometric point lying on `W` is handled by
`AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support` after
replacing it by a geometric point coming from `W` with the same image point: the stalk functors
at two geometric points lying over the same point of the space are isomorphic, Stacks 04K4.  At
a geometric point off `|W|` both sides vanish — the sheaf because it is supported on `|W|`, and
its direct image because `K` is the direct image of a sheaf on `W`, so `f_*K` is the direct
image along the *closed immersion* `i` of a sheaf on `Z`, while the image point misses `|Z|` by
cartesianness.  That last step is why nothing is needed of `f`: the vanishing is read off the
representable `i_*`, and the square isomorphism joining `f_*` to it is the mixed one of
`StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafPushforwardStalkGeneral`.

## Main results

* `smallEtaleAbelianMixedSquareIso`: the square isomorphism `i'_* ⋙ f_* ≅ f'_* ⋙ i_*` with
  the representable direct image on the three representable legs and the general one on `f`.
* `isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support_of_isPullback`: the comparison on
  stalks at an arbitrary geometric point, for an arbitrary `f`.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 0AEQ](https://stacks.math.columbia.edu/tag/0AEQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Z W : AlgebraicSpaces B S hS}

/-- **The direct image across a commutative square, with the representable direct image on the
three representable legs and the general one on `f`.**  For `i' ≫ f = d = f' ≫ i` with `i'`,
`f'` and `i` representable and `f` arbitrary, `i'_* ⋙ f_* ≅ f'_* ⋙ i_*`.

Both sides are identified with the general direct image along the diagonal `d`, by the two
mixed composition isomorphisms of
`StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafPushforwardStalkGeneral`. -/
def smallEtaleAbelianMixedSquareIso (i' : W ⟶ Y) (f' : W ⟶ Z) (f : Y ⟶ X) (i : Z ⟶ X)
    (d : W ⟶ X) (hi' : yoneda.relativelyRepresentable i'.hom)
    (hf' : yoneda.relativelyRepresentable f'.hom)
    (hi : yoneda.relativelyRepresentable i.hom)
    (h₁ : i' ≫ f = d) (h₂ : f' ≫ i = d) :
    smallEtaleAbelianPushforward.{u + 1} B S hS i' hi' ⋙
        smallEtaleAbelianDirectImage B S hS f ≅
      smallEtaleAbelianPushforward.{u + 1} B S hS f' hf' ⋙
        smallEtaleAbelianPushforward.{u + 1} B S hS i hi :=
  smallEtaleAbelianMixedCompIsoRight B S hS i' f d hi' h₁ ≪≫
    (smallEtaleAbelianMixedCompIsoBoth B S hS f' i d hf' hi h₂).symm

/-- **The stalk of a direct image of a sheaf supported on a closed subspace, at an arbitrary
geometric point and along an arbitrary morphism.** For a cartesian square with closed immersions
`i : Z ⟶ X` and `i' : W ⟶ Y` and `f' : W ⟶ Z` integral and universally injective, an abelian
sheaf `K` on `Y_étale` supported on `|W|` and any geometric point `ȳ` of `Y`, the canonical
comparison `(f_*K)_{f(ȳ)} ⟶ K_ȳ` is an isomorphism.

This is the degree-zero case of Stacks 0AEQ for abelian sheaves, with no hypothesis on `f`. -/
theorem isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support_of_isPullback (f : Y ⟶ X)
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) (i' : W ⟶ Y)
    (hi' : IsClosedImmersion B S hS i'.hom) (f' : W ⟶ Z)
    (hf'int : IsIntegralHom B S hS f'.hom) (hf'inj : UniversallyInjective B S hS f'.hom)
    (sq : IsPullback f' i' i f) (y : GeometricPoint B S hS Y.1)
    (K : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
    (hK : supportOfSheaf B S hS Y.1 K ⊆ Set.range (pointsMap B S hS W.1 i'.hom)) :
    IsIso ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app K) := by
  have hf'r := relativelyRepresentable_of_isIntegralHom B S hS f' hf'int
  by_cases hy : y.image ∈ Set.range (pointsMap B S hS W.1 i'.hom)
  · obtain ⟨w₀, hw₀⟩ := hy
    obtain ⟨w, hw⟩ := exists_geometricRepresentative B S hS W.1 w₀
    have hlift : (geometricPointMap i'.hom w).image = y.image := by
      rw [geometricPointMap_image, hw, hw₀]
    have h₀ := isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support B S hS f i hi i'
      hi' f' hf'int hf'inj sq.w.symm w K hK
    rw [isIso_app_smallEtaleAbelianDirectImageStalkMap_iff_counit] at h₀
    obtain ⟨e⟩ := stalkFunctor_iso_of_liesOver (x := y.image) Y.property
      AddCommGrpCat.{u + 1} (geometricPointMap i'.hom w) y hlift rfl
    rw [isIso_app_smallEtaleAbelianDirectImageStalkMap_iff_counit,
      ← NatIso.isIso_map_iff (Functor.isoWhiskerLeft
        (sheafToPresheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}) e) _]
    exact h₀
  · -- Off `|W|` both the stalk of `K` and the stalk of `f_*K` vanish.
    have htgt : IsZero ((smallEtaleAbelianStalk B S hS y).obj K) := by
      rw [show (smallEtaleAbelianStalk B S hS y).obj K =
          (stalkFunctor AddCommGrpCat.{u + 1} y).obj K.obj from rfl,
        isZero_stalkFunctor_iff_subsingleton_stalkSet B S hS Y.property y K.obj]
      by_contra hns
      exact hy (hK ⟨y, rfl, hns⟩)
    have hx : (geometricPointMap f.hom y).image ∉
        Set.range (pointsMap B S hS Z.1 i.hom) := by
      rintro ⟨z, hz⟩
      refine hy ?_
      have heq : pointsMap B S hS Z.1 i.hom z = pointsMap B S hS Y.1 f.hom y.image := hz
      obtain ⟨c, -, hc⟩ := exists_point_of_isPullback B S hS sq z y.image heq
      exact ⟨c, hc⟩
    have hunit : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).unit.app K) :=
      isIso_unit_app_of_supportOfSheaf_subset B S hS i' hi' K hK
    have esq := (smallEtaleAbelianMixedSquareIso B S hS i' f' f i (i' ≫ f)
      hi'.rep hf'r hi.rep rfl sq.w).app
        ((smallEtaleAbelianInverseImage B S hS i' hi'.rep).obj K)
    have etot : (smallEtaleAbelianDirectImage B S hS f).obj K ≅
        (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj
          ((smallEtaleAbelianPushforward.{u + 1} B S hS f' hf'r).obj
            ((smallEtaleAbelianInverseImage B S hS i' hi'.rep).obj K)) :=
      (smallEtaleAbelianDirectImage B S hS f).mapIso (asIso
        ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).unit.app K)) ≪≫ esq
    have hsrc : IsZero ((smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).obj
        ((smallEtaleAbelianDirectImage B S hS f).obj K)) :=
      IsZero.of_iso
        (isZero_stalkFunctor_smallEtaleAbelianPushforward_of_notMem B S hS i hi _ _ hx)
        ((smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).mapIso etot)
    rw [hsrc.eq_of_src ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app K)
      (hsrc.iso htgt).hom]
    infer_instance

end AlgebraicGeometry.Space

end
