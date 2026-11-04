module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Quasi-compactness along a finite covering family

Three facts about covering a quasi-compact situation by finitely many affine pieces, over a big
fppf site of a scheme `S`:

* a covering sieve of an *affine* object of the site contains a finite family of arrows with
  affine sources whose images cover the base;
* a quasi-compact algebraic stack receives a surjective 1-morphism from the algebraic stack of a
  single affine object of the site;
* quasi-compactness of a 2-fibre product `𝒵 ×_𝒴 𝒰` follows from that of the 2-fibre products
  `𝒱 i ×_𝒴 𝒰` taken along a finite family `a i : 𝒱 i ⟶ 𝒵` whose maps on points cover `|𝒵|`.

## Main results

* `AlgebraicGeometry.Stack.exists_finite_affine_family_of_mem_topology`: the first.
* `AlgebraicGeometry.Stack.exists_affine_isSurjective_of_isQuasiCompactStack`: the second.
* `AlgebraicGeometry.Stack.isQuasiCompactStack_twoFibreProduct_of_finite_cover`: the third.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 0DQK](https://stacks.math.columbia.edu/tag/0DQK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A covering sieve of an affine object of the big fppf site of `S` contains a finite family of
arrows with affine sources whose images cover the base. -/
theorem exists_finite_affine_family_of_mem_topology {A : BigFppfOver B S hS}
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    {R : Sieve A} (hR : R ∈ BigFppfOver.topology B S hS A) :
    ∃ (I : Type u) (_ : Finite I) (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ A),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧ (∀ i, R.arrows (v i)) ∧
        ∀ x : (BigFppfOver.toScheme B S hS).obj A,
          ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (v i)).base := by
  classical
  choose V v hVaff hVR hVflat hVlfp hVmem using fun x =>
    BigFppfOver.exists_affine_mem_of_mem_topology B S hS hR x
  let _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj A) :=
    @Scheme.compactSpace_of_isAffine ((BigFppfOver.toScheme B S hS).obj A) hA
  have hopen : ∀ x, IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map (v x)).base) := by
    intro x
    have _ := hVflat x
    have _ := hVlfp x
    exact (Scheme.Hom.isOpenMap ((BigFppfOver.toScheme B S hS).map (v x))).isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => Set.range ((BigFppfOver.toScheme B S hS).map (v x)).base) hopen
    (fun x _ => Set.mem_iUnion.2 ⟨x, hVmem x⟩)
  refine ⟨{x // x ∈ s}, inferInstance, fun i => V i.1, fun i => v i.1, fun i => hVaff i.1,
    fun i => hVR i.1, fun x => ?_⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, hx⟩

/-- A quasi-compact algebraic stack over `S` receives a surjective 1-morphism from the algebraic
stack of a single affine object of the big fppf site of `S`. -/
theorem exists_affine_isSurjective_of_isQuasiCompactStack (𝒯 : AlgebraicStacks.{u, w} B S hS)
    (h𝒯 : IsQuasiCompactStack.{u, w} B S hS 𝒯.val 𝒯.property) :
    ∃ (A : BigFppfOver B S hS) (α : schemeStack.{u, w} B S hS A ⟶ 𝒯),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧ IsSurjective B S hS α := by
  classical
  obtain ⟨U, a₁, ha₁sm, ha₁su⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒯
  let _ := pointTopology B S hS (schemeStack.{u, w} B S hS U).val
  let _ := pointTopology B S hS 𝒯.val
  let _ : CompactSpace (AlgebraicStacks.points B S hS 𝒯) := h𝒯
  let φ := pointsHomeomorphScheme B S hS U
  let n : (BigFppfOver.toScheme B S hS).obj U → AlgebraicStacks.points B S hS 𝒯 :=
    AlgebraicStacks.pointsMap B S hS a₁ ∘ φ.symm
  have hnOpen : IsOpenMap n :=
    (AlgebraicStacks.isOpenMap_pointsMap B S hS a₁
      (AlgebraicStacks.isFlat_of_isSmooth B S hS a₁ ha₁sm)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a₁ ha₁sm)).comp
      φ.symm.isOpenMap
  have hnSurj : Function.Surjective n := ha₁su.comp φ.symm.surjective
  obtain ⟨A, k, hAaff, hAsurj⟩ :=
    exists_affine_refinement_of_isOpenMap_surjective B S hS U n hnOpen hnSurj
  let _ := pointTopology B S hS (schemeFibredCategory B S hS A)
  let kk : schemeStack.{u, w} B S hS A ⟶ schemeStack.{u, w} B S hS U :=
    Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS k)
  refine ⟨A, kk ≫ a₁, hAaff, ?_⟩
  have hpt : ∀ y : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS A),
      AlgebraicStacks.pointsMap B S hS (kk ≫ a₁) y =
        n (((BigFppfOver.toScheme B S hS).map k).base
          (pointsHomeomorphScheme B S hS A y)) := by
    intro y
    have hnat := pointsHomeomorphScheme_naturality B S hS k y
    rw [AlgebraicStacks.pointsMap_comp]
    show AlgebraicStacks.pointsMap B S hS a₁ (AlgebraicStacks.pointsMap B S hS kk y) =
      AlgebraicStacks.pointsMap B S hS a₁
        (φ.symm (((BigFppfOver.toScheme B S hS).map k).base
          (pointsHomeomorphScheme B S hS A y)))
    rw [← hnat, Homeomorph.symm_apply_apply]
  intro z
  obtain ⟨x, hx⟩ := hAsurj z
  obtain ⟨y, hy⟩ := (pointsHomeomorphScheme B S hS A).surjective x
  exact ⟨y, by rwa [hpt y, hy]⟩

/-- A family of morphisms of the site whose images cover the base induces a family of 1-morphisms
of algebraic stacks whose maps on points cover. -/
theorem exists_mem_range_pointsMap_schemeStackMap {A : BigFppfOver B S hS} {I : Type v}
    (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ A)
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj A,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (v i)).base)
    (z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS A)) :
    ∃ i, z ∈ Set.range (AlgebraicStacks.pointsMap B S hS
      (schemeStackMap.{u, w} B S hS (v i))) := by
  classical
  let _ := pointTopology B S hS (schemeFibredCategory B S hS A)
  obtain ⟨i, wpt, hwpt⟩ := hcov (pointsHomeomorphScheme B S hS A z)
  let _ := pointTopology B S hS (schemeFibredCategory B S hS (V i))
  refine ⟨i, (pointsHomeomorphScheme B S hS (V i)).symm wpt,
    (pointsHomeomorphScheme B S hS A).injective ?_⟩
  exact (pointsHomeomorphScheme_naturality B S hS (v i) _).trans
    (by rwa [Homeomorph.apply_symm_apply])

/-- Quasi-compactness of a 2-fibre product descends along a finite covering family: let
`g : 𝒵 ⟶ 𝒴` and `f : 𝒰 ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S` and let
`a i : 𝒱 i ⟶ 𝒵` be a finite family of 1-morphisms whose maps on points cover `|𝒵|`. If every
2-fibre product `𝒱 i ×_𝒴 𝒰` taken along `a i ≫ g` is quasi-compact, then `𝒵 ×_𝒴 𝒰` is
quasi-compact. -/
theorem isQuasiCompactStack_twoFibreProduct_of_finite_cover
    {𝒴 𝒵 𝒰 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒴) (f : 𝒰 ⟶ 𝒴)
    {I : Type v} [Finite I] {𝒱 : I → AlgebraicStacks.{u, w} B S hS} (a : ∀ i, 𝒱 i ⟶ 𝒵)
    (hcov : ∀ z : AlgebraicStacks.points B S hS 𝒵,
      ∃ i, z ∈ Set.range (AlgebraicStacks.pointsMap B S hS (a i)))
    (h : ∀ i, IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS (a i ≫ g) f).val
      (twoFibreProductAlgebraicStack B S hS (a i ≫ g) f).property) :
    IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS g f).val
      (twoFibreProductAlgebraicStack B S hS g f).property := by
  classical
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g
  have hK : ∀ i, IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd (a i)).val
      (twoFibreProductAlgebraicStack B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd (a i)).property := by
    intro i
    have h1 := isQuasiCompactStack_of_isTwoFibreProduct B S hS
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (a i ≫ g) f))
      (isTwoFibreProduct_cancelSndSquareAlgebraicStacks B S hS f g (a i) (a i ≫ g)
        (Iso.refl _))
      (h i)
    exact h1
  let _ := pointTopology B S hS (twoFibreProductAlgebraicStack B S hS f g).val
  have hunion : (Set.univ : Set (AlgebraicStacks.points B S hS
      (twoFibreProductAlgebraicStack B S hS f g))) =
      ⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS
          (twoFibreProductSquareAlgebraicStacks B S hS f g).snd (a i)).fst) := by
    refine Set.eq_of_subset_of_subset (fun wpt _ => ?_) (fun _ _ => Set.mem_univ _)
    obtain ⟨i, v, hv⟩ := hcov (AlgebraicStacks.pointsMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd wpt)
    obtain ⟨ppt, hppt, -⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd (a i))
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd (a i))
      wpt v hv.symm
    exact Set.mem_iUnion.2 ⟨i, ppt, hppt⟩
  have hcompact : IsCompact (Set.univ : Set (AlgebraicStacks.points B S hS
      (twoFibreProductAlgebraicStack B S hS f g))) := by
    rw [hunion]
    refine isCompact_iUnion fun i => ?_
    let _ := pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd (a i)).pt.val
    let _ : CompactSpace (AlgebraicStacks.points B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd (a i)).pt) := hK i
    exact isCompact_range (continuous_pointsMap B S hS _
      (twoFibreProductAlgebraicStack B S hS f g).val
      (twoFibreProductSquareAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd (a i)).fst.hom.hom)
  have hmain : IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS f g).val
      (twoFibreProductAlgebraicStack B S hS f g).property := ⟨hcompact⟩
  exact isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap hQ)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f) hmain

end AlgebraicGeometry.Stack

end
