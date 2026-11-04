module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFppfDescent
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace

/-!
# Properties with an open locus descend along fppf coverings of the base

Let `P` be a property of families of curves satisfying condition (o) of Stacks 0E0E: for every
family `G` there is an open subspace of its base through which the base morphism of a family
mapping to `G` factors exactly when that family has `P`. If a family of curves `G ⟶ S` has `P`
after base change along every member of an fppf covering `{Wᵢ ⟶ S}`, then all the `Wᵢ` map into
the open of `G`, which therefore contains every point of `S`; so the identity of `S` factors
through it and `G` has `P`.

Applied to stability, whose locus is open by Stacks 0E76, this gives the stability of the glued
stabilization in Stacks 0E8A.

## Main results

* `AlgebraicGeometry.IsOpenCurvesLocus.prop_ofIsFppfCovering`: a property with an open locus
  descends along fppf coverings of the base.

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- A cartesian square over a transported base is a cartesian square over the composite base
morphism. -/
theorem isPullback_toBase_of_isPullback_comp_eqToHom (Y : CurveFamily B hZ)
    {W S₀ : BigFppfOver B integerBase hZ} (h : Y.base = W) {Q : AlgebraicSpaces B integerBase hZ}
    {r : Y.total ⟶ Q} {q : Q ⟶ schemeSpace S₀} {φ : W ⟶ S₀}
    (hsq : IsPullback r (Y.toBase ≫ eqToHom (congrArg schemeSpace h)) q (schemeSpaceMap φ)) :
    IsPullback r Y.toBase q (schemeSpaceMap (eqToHom h ≫ φ)) := by
  subst h
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using hsq

/-- The points of a transported base have the same images. -/
theorem exists_pointsMap_eqToHom_comp {A W S₀ : BigFppfOver B integerBase hZ} (h : A = W)
    (φ : W ⟶ S₀) (x : Space.points B integerBase hZ (schemeSpace W).obj) :
    ∃ y : Space.points B integerBase hZ (schemeSpace A).obj,
      Space.pointsMap B integerBase hZ _ (schemeSpaceMap (eqToHom h ≫ φ)).hom y =
        Space.pointsMap B integerBase hZ _ (schemeSpaceMap φ).hom x := by
  subst h
  exact ⟨x, by rw [eqToHom_refl, Category.id_comp]⟩

end CurveFamily

/-- **A property with an open locus descends along fppf coverings of the base.** Let `P` satisfy
condition (o) of Stacks 0E0E, and let `G = Q ⟶ S₀` be the family of curves obtained from
cartesian squares over an fppf covering `{φᵢ : Wᵢ ⟶ S₀}` by families `Yᵢ ⟶ Wᵢ` having `P`. Then
`G` has `P`. -/
theorem IsOpenCurvesLocus.prop_ofIsFppfCovering {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) {S₀ : BigFppfOver B integerBase hZ}
    {Q : AlgebraicSpaces B integerBase hZ} (q : Q ⟶ schemeSpace S₀) {ι : Type v}
    {W : ι → BigFppfOver B integerBase hZ} (φ : ∀ i, W i ⟶ S₀)
    (hcov : Space.IsFppfCovering B integerBase hZ (fun i => (schemeSpace (W i)).obj)
      (fun i => (schemeSpaceMap (φ i)).hom))
    {Y : ι → CurveFamily B hZ} (hY : ∀ i, (Y i).base = W i) (r : ∀ i, (Y i).total ⟶ Q)
    (hsq : ∀ i, IsPullback (r i) ((Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i))) q
      (schemeSpaceMap (φ i)))
    (hYP : ∀ i, P (Y i)) : P (CurveFamily.ofIsFppfCovering q φ hcov hY r hsq) := by
  let G := CurveFamily.ofIsFppfCovering q φ hcov hY r hsq
  obtain ⟨W', hW', hchar⟩ := hP G
  have hfac : ∀ i, Set.range (Space.pointsMap B integerBase hZ (schemeSpace (W i)).obj
      (schemeSpaceMap (φ i)).hom) ⊆ Set.range (Space.pointsMap B integerBase hZ W'.toFunctor
        W'.ι) := by
    intro i
    let a : Y i ⟶ G :=
      { baseMap := eqToHom (hY i) ≫ φ i
        totalMap := r i
        cartesian := CurveFamily.isPullback_toBase_of_isPullback_comp_eqToHom (Y i) (hY i)
          (hsq i) }
    have hfa := (Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace S₀).property (schemeSpace (Y i).base).property W' hW' _).1
      ((hchar (Y i) a).1 (hYP i))
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := CurveFamily.exists_pointsMap_eqToHom_comp (hY i) (φ i) x
    exact hfa ⟨y, hy⟩
  refine (hchar G (𝟙 G)).2 ((Space.factorsThrough_openSubspace_iff_points B integerBase hZ
    (schemeSpace S₀).property (schemeSpace S₀).property W' hW' _).2 ?_)
  have hid : (schemeSpaceMap (CurveFamily.Hom.baseMap (𝟙 G))).hom = 𝟙 (schemeSpace S₀).obj :=
    yoneda.map_id _
  rw [hid, Space.pointsMap_id]
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcov.jointly_surjective x)
  exact hfac i ⟨y, rfl⟩

end AlgebraicGeometry

end
