module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.Adjoints
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.PointDetection
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.PointSheaf
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.BoundedCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectNotFibrewise
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.SpanningSet

/-!
# The essential image of a functor agreeing with a fully faithful one on zero-dimensional sheaves

Let `k` be a field, let `X`, `Y` be proper schemes over `k` with `X` regular, and let
`F, G : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` be `k`-linear exact functors such that `F(𝓕) ≅ G(𝓕)` for every
coherent `𝒪_X`-module `𝓕` with `dim Supp(𝓕) = 0`, and such that `F` is fully faithful. Then the
essential image of `G` is contained in the essential image of `F`: this is [Stacks, Tag 0GX0].

## Main definitions

* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.perfectPointSheaf`: the skyscraper `𝒪_x` at a
  closed point of a regular Noetherian scheme, as an object of `D_perf(𝒪_X)`.

## Main results

* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.isPerfect_single_of_isCoherent`: a coherent
  module on a quasi-compact regular scheme, placed in degree zero, is perfect.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.isZero_of_forall_hom_perfectPointSheaf_shift`:
  on a regular Noetherian scheme, an object of `D_perf(𝒪_X)` with no nonzero map to any shift of
  any closed-point skyscraper is zero.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.essImage_of_agree_on_zeroDimensional`: the
  essential image of `G` is contained in the essential image of `F`.

## References

* [Stacks Project, Tag 0GX0](https://stacks.math.columbia.edu/tag/0GX0)
* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite Stacks.Cohomology.PerfectComplexes
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear

/-! ### Perfect point sheaves -/

section PointSheaves

variable (X : Scheme.{u})

/-- A coherent module on a quasi-compact regular scheme, placed in degree zero, is perfect. -/
theorem isPerfect_single_of_isCoherent (hX : IsRegular X) [CompactSpace X] (M : X.Modules)
    (hM : M.IsCoherent) :
    IsPerfect (X := X.toRingedSpace) ((DerivedCategory.singleFunctor X.Modules 0).obj M) := by
  change perfectInModules X _
  rw [perfectInModules_eq_derivedCategoryBBounded X hX]
  exact derivedCategoryBBounded_singleFunctor_obj X M hM

/-- The skyscraper `𝒪_x` at a closed point of a regular Noetherian scheme, as an object of
`D_perf(𝒪_X)`. -/
abbrev perfectPointSheaf (hX : IsRegular X) [IsNoetherian X] (x : X) (hx : IsClosed ({x} : Set X)) :
    PerfectDerivedCategory X :=
  ⟨pointSheaf X x, isPerfect_single_of_isCoherent X hX _
    (isCoherent_residueFieldSkyscraperSheaf X x hx)⟩

/-- Morphisms into a shift in `D_perf(𝒪_X)` are morphisms into the shift in `D(𝒪_X)`. -/
def perfectHomShiftEquiv (A B : PerfectDerivedCategory X) (i : ℤ) :
    (A ⟶ B⟦i⟧) ≃ (A.obj ⟶ B.obj⟦i⟧) :=
  (ObjectProperty.fullyFaithfulι _).homEquiv.trans
    (Iso.homCongr (Iso.refl _) (((ObjectProperty.ι _).commShiftIso i).app B))

/-- On a regular Noetherian scheme, a perfect complex with no nonzero map to any shift of any
closed-point skyscraper is zero ([Stacks, Tag 0G03] part (4)). -/
theorem isZero_of_forall_hom_perfectPointSheaf_shift (hX : IsRegular X) [IsNoetherian X]
    (K : PerfectDerivedCategory X)
    (h : ∀ (x : X) (hx : IsClosed ({x} : Set X)) (i : ℤ),
      Subsingleton (K ⟶ (perfectPointSheaf X hX x hx)⟦i⟧)) :
    IsZero K :=
  IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) K
    (isZero_of_forall_hom_pointSheaf_shift X K.obj K.property fun x hx i ↦
      (perfectHomShiftEquiv X K (perfectPointSheaf X hX x hx) i).symm.injective.subsingleton)

end PointSheaves

/-! ### [Stacks, Tag 0GX0] -/

section EssentialImage

variable {k : Type u} [Field k] (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
  [IsProper Y.hom]

/-- The inclusion of the essential image of a fully faithful functor which is a right adjoint is a
right adjoint. -/
theorem isRightAdjoint_essImage_ι {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [F.Full]
    [F.Faithful] [F.IsRightAdjoint] : F.essImage.ι.IsRightAdjoint := by
  have : F.toEssImage.Full := Functor.Full.of_comp_faithful_iso F.toEssImageCompι
  have : F.toEssImage.Faithful := Functor.Faithful.of_comp_iso F.toEssImageCompι
  have : F.toEssImage.IsEquivalence := { }
  let e := F.toEssImage.asEquivalence
  exact Functor.isRightAdjoint_of_iso
    ((Functor.isoWhiskerLeft e.inverse F.toEssImageCompι).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.counitIso _ ≪≫ Functor.leftUnitor _)

/-- Let `k` be a field and let `X`, `Y` be proper schemes over `k` with
`X` regular. Let `F, G : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` be `k`-linear exact functors such that
(1) `F(𝓕) ≅ G(𝓕)` for every coherent `𝒪_X`-module `𝓕` with `dim Supp(𝓕) = 0`, and (2) `F` is
fully faithful. Then the essential image of `G` is contained in the essential image of `F`.

The coherent module `𝓕` is read in `D_perf(𝒪_X)` placed in degree zero; the hypothesis asks for
the isomorphism for every proof that it is perfect, which is automatic on a regular scheme
(`isPerfect_single_of_isCoherent`). -/
@[stacks 0GX0]
theorem essImage_of_agree_on_zeroDimensional (hX : IsRegular X.left)
    (F G : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear k] [G.CommShift ℤ] [G.IsTriangulated]
    [G.Linear k]
    (hagree : ∀ (M : X.left.Modules), M.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp M) = 0 →
      ∀ (hM : IsPerfect (X := X.left.toRingedSpace)
          ((DerivedCategory.singleFunctor X.left.Modules 0).obj M)),
        Nonempty (F.obj (⟨_, hM⟩ : PerfectDerivedCategory X.left) ≅
          G.obj (⟨_, hM⟩ : PerfectDerivedCategory X.left)))
    (hFF : Nonempty F.FullyFaithful) (E : PerfectDerivedCategory X.left) :
    F.essImage (G.obj E) := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have : F.Full := hFF.some.full
  have : F.Faithful := hFF.some.faithful
  have := (isLeftAdjoint_and_isRightAdjoint X Y hX F).2
  have := (isLeftAdjoint_and_isRightAdjoint X Y hX G).2
  let A : ObjectProperty (PerfectDerivedCategory Y.left) := F.essImage
  have : A.ι.IsRightAdjoint := isRightAdjoint_essImage_ι F
  obtain ⟨h1, h2⟩ :=
    A.isRightAdjoint_ι_iff_extensionProduct_leftOrthogonal_self_eq_top_and_isSaturated
  have hiso := (h2 (h1.1 inferInstance)).2
  rw [ObjectProperty.isoClosure_eq_self] at hiso
  rw [show F.essImage = A from rfl, hiso]
  intro N f hN
  let adj : G.leftAdjoint ⊣ G := Adjunction.ofIsRightAdjoint G
  have hz : IsZero (G.leftAdjoint.obj N) := by
    refine isZero_of_forall_hom_perfectPointSheaf_shift X.left hX _ fun x hx i ↦ ?_
    let P := perfectPointSheaf X.left hX x hx
    obtain ⟨e⟩ := hagree _ (isCoherent_residueFieldSkyscraperSheaf X.left x hx)
      (topologicalKrullDim_supp_residueFieldSkyscraperSheaf X.left x hx) P.property
    have hA : A ((F.obj P)⟦i⟧) := A.le_shift i _ (F.obj_mem_essImage P)
    refine ⟨fun a b ↦ (adj.homEquiv _ _).injective ?_⟩
    have hzero : ∀ c : N ⟶ G.obj (P⟦i⟧), c = 0 := fun c ↦ by
      simpa using hN (c ≫ (G.commShiftIso i).hom.app P ≫ ((shiftFunctor _ i).map e.inv)) hA
    rw [hzero (adj.homEquiv _ _ a), hzero (adj.homEquiv _ _ b)]
  rw [← (adj.homEquiv _ _).apply_symm_apply f, hz.eq_of_src ((adj.homEquiv _ _).symm f) 0,
    Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

end EssentialImage

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
