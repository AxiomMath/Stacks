module

public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafPushforwardStalk
import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSmallEtale
import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianPushforwardComp
import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint

/-!
# The stalk of a direct image of a supported sheaf, at an arbitrary geometric point

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `i : Z ⟶ X` be a
closed immersion and let `i' : W ⟶ Y` be its inverse image, through an integral and universally
injective `f' : W ⟶ Z`. For an abelian sheaf `K` on the small étale site of `Y` supported on
`|W|` the canonical comparison `(f_*K)_{f(ȳ)} ⟶ K_ȳ` is an isomorphism at *every* geometric
point `ȳ` of `Y`, not only at those lying on `W`.

A geometric point lying on `W` is handled by
`AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support` after
replacing it by a geometric point coming from `W` with the same image point: the stalk functors
at two geometric points lying over the same point of the space are isomorphic, Stacks 04K4. At a
geometric point off `|W|` both sides vanish — the sheaf because it is supported on `|W|`, and
its direct image because `K` is the direct image of a sheaf on `W`, so `f_*K` is the direct
image of a sheaf on `Z`, while the image point misses `|Z|` by cartesianness.

## Main results

* `Space.supportOfSheaf_subset_of_isZero_smallEtaleAbelianInverseImage`: an abelian sheaf whose
  inverse image on an open subspace vanishes is supported on the complement of that subspace.
* `Space.isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support_of_isPullback`: the comparison
  on stalks at an arbitrary geometric point.

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

variable {X Y Z W V : AlgebraicSpaces B S hS}

/-- A point in the image of `|V| ⟶ |Y|` is the image point of a geometric point of the form
`geometricPointMap g v`. -/
private theorem exists_geometricPointMap_image_eq (g : V ⟶ Y) {x : points B S hS Y.1}
    (hx : x ∈ Set.range (pointsMap B S hS V.1 g.hom)) :
    ∃ v : GeometricPoint B S hS V.1, (geometricPointMap g.hom v).image = x := by
  obtain ⟨v₀, hv₀⟩ := hx
  obtain ⟨v, hv⟩ := exists_geometricRepresentative B S hS V.1 v₀
  exact ⟨v, by rw [geometricPointMap_image, hv, hv₀]⟩

/-- **A sheaf with vanishing restriction to an open subspace is supported on the complement.**
If the inverse image of an abelian sheaf `P` on `Y_étale` along `j : V ⟶ Y` is zero and the
complement of a set `T` of points of `Y` is covered by the image of `|V|`, then the support of
`P` is contained in `T`.

A point outside `T` is the image of a point of `V`, which carries a geometric point by
`AlgebraicGeometry.Space.exists_geometricRepresentative`; the stalk of `P` at its image is the
stalk of the inverse image, Stacks 04K2 part (4), hence zero, and the stalk at any other
geometric point over the same point of `Y` is isomorphic to it by Stacks 04K4. -/
theorem supportOfSheaf_subset_of_isZero_smallEtaleAbelianInverseImage (j : V ⟶ Y)
    (hj : yoneda.relativelyRepresentable j.hom) (T : Set (points B S hS Y.1))
    (hT : Tᶜ ⊆ Set.range (pointsMap B S hS V.1 j.hom))
    (P : abelianSheaves.{u + 1} B S hS Y)
    (hP : IsZero ((smallEtaleAbelianInverseImage B S hS j hj).obj P)) :
    supportOfSheaf B S hS Y.1 P ⊆ T := by
  intro x hx
  by_contra hxT
  obtain ⟨v, hy⟩ := exists_geometricPointMap_image_eq B S hS j (hT hxT)
  obtain ⟨p, hp, hns⟩ := hx
  have hzv : IsZero ((smallEtaleAbelianStalk B S hS (geometricPointMap j.hom v)).obj P) :=
    IsZero.of_iso (Functor.map_isZero (smallEtaleAbelianStalk B S hS v) hP)
      ((smallEtaleAbelianInverseImageStalkIso B S hS j hj v).app P).symm
  have hsub : Subsingleton (stalkSet (geometricPointMap j.hom v)
      (P.obj ⋙ forget AddCommGrpCat.{u + 1})) :=
    (isZero_stalkFunctor_iff_subsingleton_stalkSet B S hS Y.property _ P.obj).1 hzv
  obtain ⟨e⟩ := stalkSetFunctor_iso_of_liesOver.{u, u + 1} Y.property p
    (geometricPointMap j.hom v) hp hy
  exact hns ⟨fun a b ↦
    (e.app (P.obj ⋙ forget AddCommGrpCat.{u + 1})).toEquiv.injective (hsub.elim _ _)⟩

/-- The stalk comparison at a sheaf is invertible exactly when the geometric stalk of the
counit at that sheaf is: the comparison is that stalk preceded by the identification of
Stacks 04K2 part (4). -/
theorem isIso_app_smallEtaleAbelianPushforwardStalkMap_iff_counit (f : Y ⟶ X)
    (hfr : yoneda.relativelyRepresentable f.hom) (y : GeometricPoint B S hS Y.1)
    (K : abelianSheaves.{u + 1} B S hS Y) :
    IsIso ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app K) ↔
      IsIso ((smallEtaleAbelianStalk B S hS y).map
        ((smallEtaleAbelianInverseImageAdjunction B S hS f hfr).counit.app K)) := by
  constructor
  · intro h
    rw [smallEtaleAbelianPushforwardStalkMap_app] at h
    exact IsIso.of_isIso_comp_left
      ((smallEtaleAbelianInverseImageStalkIso B S hS f hfr y).inv.app
        ((smallEtaleAbelianPushforward.{u + 1} B S hS f hfr).obj K)) _
  · intro h
    rw [smallEtaleAbelianPushforwardStalkMap_app]
    infer_instance

/-- At a geometric point off `|W|`, the stalk comparison for a sheaf supported on `|W|` is an
isomorphism between two zero objects. -/
theorem isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support_of_notMem (f : Y ⟶ X)
    (hfr : yoneda.relativelyRepresentable f.hom) (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (i' : W ⟶ Y)
    (hi' : IsClosedImmersion B S hS i'.hom) (f' : W ⟶ Z)
    (hf'int : IsIntegralHom B S hS f'.hom)
    (sq : IsPullback f' i' i f) (y : GeometricPoint B S hS Y.1)
    (K : abelianSheaves.{u + 1} B S hS Y)
    (hK : supportOfSheaf B S hS Y.1 K ⊆ Set.range (pointsMap B S hS W.1 i'.hom))
    (hy : y.image ∉ Set.range (pointsMap B S hS W.1 i'.hom)) :
    IsIso ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app K) := by
  have hf'r := relativelyRepresentable_of_isIntegralHom B S hS f' hf'int
  have htgt : IsZero ((smallEtaleAbelianStalk B S hS y).obj K) := by
    rw [show (smallEtaleAbelianStalk B S hS y).obj K =
        (stalkFunctor AddCommGrpCat.{u + 1} y).obj K.obj from rfl,
      isZero_stalkFunctor_iff_subsingleton_stalkSet B S hS Y.property y K.obj]
    by_contra hns
    exact hy (hK ⟨y, rfl, hns⟩)
  have hx : (geometricPointMap f.hom y).image ∉
      Set.range (pointsMap B S hS Z.1 i.hom) := by
    rintro ⟨z, hz⟩
    have heq : pointsMap B S hS Z.1 i.hom z = pointsMap B S hS Y.1 f.hom y.image := hz
    obtain ⟨c, -, hc⟩ := exists_point_of_isPullback B S hS sq z y.image heq
    exact hy ⟨c, hc⟩
  have hunit : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).unit.app K) :=
    isIso_unit_app_of_supportOfSheaf_subset B S hS i' hi' K hK
  have esq := (smallEtaleAbelianPushforwardSiteCommSquareIso B S hS i' f' f i (i' ≫ f)
    hi'.rep hfr hf'r hi.rep (MorphismProperty.comp_mem _ i'.hom f.hom hi'.rep hfr) rfl sq.w).app
      ((smallEtaleAbelianInverseImage B S hS i' hi'.rep).obj K)
  have etot : (smallEtaleAbelianPushforward.{u + 1} B S hS f hfr).obj K ≅
      (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj
        ((smallEtaleAbelianPushforward.{u + 1} B S hS f' hf'r).obj
          ((smallEtaleAbelianInverseImage B S hS i' hi'.rep).obj K)) :=
    (smallEtaleAbelianPushforward.{u + 1} B S hS f hfr).mapIso (asIso
      ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).unit.app K)) ≪≫ esq
  have hsrc : IsZero ((smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).obj
      ((smallEtaleAbelianPushforward.{u + 1} B S hS f hfr).obj K)) :=
    IsZero.of_iso
      (isZero_stalkFunctor_smallEtaleAbelianPushforward_of_notMem B S hS i hi _ _ hx)
      ((smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).mapIso etot)
  rw [hsrc.eq_of_src ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app K)
    (hsrc.iso htgt).hom]
  infer_instance

/-- **The stalk of a direct image of a sheaf supported on a closed subspace, at an arbitrary
geometric point.** For a cartesian square with closed immersions `i : Z ⟶ X` and `i' : W ⟶ Y`
and `f' : W ⟶ Z` integral and universally injective, an abelian sheaf `K` on `Y_étale`
supported on `|W|` and any geometric point `ȳ` of `Y`, the canonical comparison
`(f_*K)_{f(ȳ)} ⟶ K_ȳ` is an isomorphism.

This is `AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support`
with the hypothesis that `ȳ` lie on `W` removed. -/
theorem isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support_of_isPullback (f : Y ⟶ X)
    (hfr : yoneda.relativelyRepresentable f.hom) (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (i' : W ⟶ Y)
    (hi' : IsClosedImmersion B S hS i'.hom) (f' : W ⟶ Z)
    (hf'int : IsIntegralHom B S hS f'.hom) (hf'inj : UniversallyInjective B S hS f'.hom)
    (sq : IsPullback f' i' i f) (y : GeometricPoint B S hS Y.1)
    (K : abelianSheaves.{u + 1} B S hS Y)
    (hK : supportOfSheaf B S hS Y.1 K ⊆ Set.range (pointsMap B S hS W.1 i'.hom)) :
    IsIso ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app K) := by
  by_cases hy : y.image ∈ Set.range (pointsMap B S hS W.1 i'.hom)
  · obtain ⟨w, hlift⟩ := exists_geometricPointMap_image_eq B S hS i' hy
    have h₀ := isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support B S hS f hfr i hi i'
      hi' f' hf'int hf'inj sq.w.symm w K hK
    rw [isIso_app_smallEtaleAbelianPushforwardStalkMap_iff_counit] at h₀
    obtain ⟨e⟩ := stalkFunctor_iso_of_liesOver (x := y.image) Y.property
      AddCommGrpCat.{u + 1} (geometricPointMap i'.hom w) y hlift rfl
    rwa [isIso_app_smallEtaleAbelianPushforwardStalkMap_iff_counit,
      ← NatIso.isIso_map_iff (Functor.isoWhiskerLeft
        (sheafToPresheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}) e) _]
  · exact isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support_of_notMem B S hS f hfr i hi
      i' hi' f' hf'int sq y K hK hy

end AlgebraicGeometry.Space

end
