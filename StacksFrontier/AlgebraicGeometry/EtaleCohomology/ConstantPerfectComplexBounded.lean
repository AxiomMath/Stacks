module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantPerfectComplex
public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.PointFiber
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConnectedConstantModels
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering

/-!
# Vanishing of a locally constant sheaf over a connected base

A locally constant sheaf of modules is determined, over a member of a trivializing covering, by
one module of coefficients. Over a connected base the coefficients of two members whose images
meet are isomorphic, so one vanishing forces all of them: a locally constant sheaf which
vanishes over a single object whose image is nonempty is zero.

The statement is proved for a site carrying a *realization* in a topological space — the
interface of `Stacks.ConstantSheaf.exists_cover_uniform_constantComplex_representation'` — and
then instantiated at the small étale site of a connected scheme, where the realization is the
open image of an object.

## Main results

* `Stacks.ConstantSheaf.exists_iso_of_constantModels_of_point`: constant models of one sheaf
  over two objects carrying lifts of one point of the site have isomorphic coefficients.
* `Stacks.ConstantSheaf.isZero_of_isZero_overPullback_of_coversTop`: a sheaf whose restriction
  to every member of a family of objects covering the final object vanishes is zero.
* `Stacks.ConstantSheaf.isZero_of_isZero_overPullback_of_connected`: a locally constant sheaf of
  modules on a site with a connected realization which vanishes over one object with nonempty
  image is zero.
* `AlgebraicGeometry.isZero_of_isZero_overPullback_of_connectedSpace`: the same on the small
  étale site of a connected scheme.

## Implementation notes

The comparison of two constant models is read off the fibre at a point of the site lifting to
both objects, and *not* off a common refinement of the two objects: by Tag 04H2
(`CategoryTheory.GrothendieckTopology.Point.sheafFiberOverIso`) the fibre at the localized point
`p.over x` of the restriction of a sheaf to the slice over the object carrying `x` is the fibre
at `p` of the sheaf itself, so both coefficient modules are identified with the single module
`F_p`. Routing through a common refinement — which is what the cofiltered structure of the
neighbourhoods of `p` supplies — would additionally need the restriction of a constant sheaf
along an arrow of the base, and so a pullback-stability hypothesis on the site that the fibre
route does not use.

Vanishing descends from a covering family through
`CategoryTheory.Sheaf.isZero_of_isCoveringFamily`, whose hypothesis is the vanishing of the
*sections* over the members: the sections of the restriction of `F` to the slice over `U i` at
an object `f : W ⟶ U i` of that slice are the sections of `F` over `W`, so a vanishing
restriction gives the vanishing sections the covering-family criterion asks for, for every
object admitting an arrow to a member.

## References

* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe m w vA uA r v u

namespace Stacks.ConstantSheaf

/-! ### Constant models at a point of the site -/

/-- **Constant models of one sheaf over two objects carrying lifts of one point of the site have
isomorphic coefficients.** -/
theorem exists_iso_of_constantModels_of_point
    {C : Type u} [Category.{v} C] [LocallySmall.{w} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{vA} A] [∀ U : C, HasWeakSheafify (J.over U) A]
    [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    (F : Sheaf J A) (p : J.Point.{w}) {U V : C}
    (x : p.fiber.obj U) (y : p.fiber.obj V) (M N : A)
    (eU : (constantSheaf (J.over U) A).obj M ≅ (J.overPullback A U).obj F)
    (eV : (constantSheaf (J.over V) A).obj N ≅ (J.overPullback A V).obj F) :
    Nonempty (M ≅ N) :=
  ⟨(GrothendieckTopology.Point.constantFiberIso (J.over U) A (p.over x) M).symm ≪≫
    ((p.over x).sheafFiber (A := A)).mapIso eU ≪≫
      (GrothendieckTopology.Point.sheafFiberOverIso p x A).app F ≪≫
        ((GrothendieckTopology.Point.sheafFiberOverIso p y A).app F).symm ≪≫
          ((p.over y).sheafFiber (A := A)).mapIso eV.symm ≪≫
            GrothendieckTopology.Point.constantFiberIso (J.over V) A (p.over y) N⟩

/-! ### Vanishing over a covering family -/

/-- **A sheaf whose restriction to every member of a family of objects covering the final object
vanishes is zero.** -/
theorem isZero_of_isZero_overPullback_of_coversTop
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{vA} A] [HasZeroMorphisms A] (F : Sheaf J A)
    {I : Type*} (U : I → C) (hU : J.CoversTop U)
    (hF : ∀ i, IsZero ((J.overPullback A (U i)).obj F)) :
    IsZero F := by
  refine F.isZero_of_isCoveringFamily (P := fun W => ∃ i, Nonempty (W ⟶ U i))
    (fun W => ⟨(Sieve.ofObjects U W).arrows, by simpa using hU W, fun _ _ hf => hf⟩) ?_
  rintro W ⟨i, ⟨f⟩⟩
  exact (sheafToPresheaf (J.over (U i)) A ⋙
    (evaluation (Over (U i))ᵒᵖ A).obj (op (Over.mk f))).map_isZero (hF i)

/-! ### Vanishing over a connected realization -/

/-- **A locally constant sheaf of modules on a site with a connected realization which vanishes
over one object whose image is nonempty is zero.**

The realization is carried by `img`, as in
`Stacks.ConstantSheaf.exists_cover_uniform_constantComplex_representation'`: the images are open,
a family of arrows to the final object `X` is covering exactly when its images cover, and two
objects whose images meet carry lifts of one point of the site. -/
theorem isZero_of_isZero_overPullback_of_connected
    {C : Type u} [Category.{v} C] [LocallySmall.{w} C] (J : GrothendieckTopology C)
    (Λ : Type r) [Ring Λ]
    [HasSheafify J (ModuleCat.{m} Λ)] [∀ U : C, HasSheafify (J.over U) (ModuleCat.{m} Λ)]
    [HasProducts.{w} (ModuleCat.{m} Λ)] [HasColimitsOfSize.{w, w} (ModuleCat.{m} Λ)]
    (X : C) (hX : IsTerminal X)
    {Z : Type*} [TopologicalSpace Z] [ConnectedSpace Z] (img : C → Set Z)
    (himgOpen : ∀ U : C, IsOpen (img U))
    (himgCover : ∀ {I : Type (max u v)} (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ↔ (⋃ i, img (U i)) = Set.univ)
    (hpoint : ∀ (U V : C) (z : Z), z ∈ img U → z ∈ img V →
      ∃ p : J.Point.{w}, Nonempty (p.fiber.obj U) ∧ Nonempty (p.fiber.obj V))
    (F : Sheaf J (ModuleCat.{m} Λ)) (hF : IsLocallyConstant J F)
    (V : C) (z₀ : Z) (hz₀ : z₀ ∈ img V)
    (hV : IsZero ((J.overPullback (ModuleCat.{m} Λ) V).obj F)) :
    IsZero F := by
  classical
  have hzero (W : C) {N : ModuleCat.{m} Λ} (hN : IsZero N) :
      IsZero ((constantSheaf (J.over W) (ModuleCat.{m} Λ)).obj N) := by
    unfold constantSheaf
    exact Functor.map_isZero _ hN
  obtain ⟨I, U, f, hcov, hconst⟩ := hF.exists_cover X
  have hconst' (i : I) : ∃ M : ModuleCat.{m} Λ,
      Nonempty ((constantSheaf (J.over (U i)) (ModuleCat.{m} Λ)).obj M ≅
        (J.overPullback (ModuleCat.{m} Λ) (U i)).obj F) := (hconst i).mem_essImage
  choose M e using hconst'
  obtain ⟨i₀, hi₀⟩ := exists_index_iUnion_eq_univ_of_connected (fun i => img (U i)) M
    ((himgCover U f).mp hcov) (fun i => himgOpen (U i))
    (fun i j z hi hj =>
      have ⟨p, ⟨a⟩, ⟨b⟩⟩ := hpoint (U i) (U j) z hi hj
      exists_iso_of_constantModels_of_point J (ModuleCat.{m} Λ) F p a b (M i) (M j)
        (e i).some (e j).some)
  have hM : IsZero (M i₀) := by
    obtain ⟨i, hi⟩ : ∃ i : {i : I // Nonempty (M i ≅ M i₀)}, z₀ ∈ img (U i.1) := by
      simpa only [← hi₀, Set.mem_iUnion] using Set.mem_univ z₀
    obtain ⟨p, ⟨a⟩, ⟨b⟩⟩ := hpoint (U i.1) V z₀ hi hz₀
    obtain ⟨eM⟩ := exists_iso_of_constantModels_of_point J (ModuleCat.{m} Λ) F p a b
      (M i.1) 0 (e i.1).some ((hzero V (isZero_zero _)).iso hV)
    exact ((isZero_zero (ModuleCat.{m} Λ)).of_iso eM).of_iso i.property.some.symm
  refine isZero_of_isZero_overPullback_of_coversTop J (ModuleCat.{m} Λ) F
    (fun i : {i : I // Nonempty (M i ≅ M i₀)} => U i.1) ?_ fun i => ?_
  · rw [J.coversTop_iff_of_isTerminal X hX]
    exact J.superset_covering (Sieve.ofArrows_le_ofObjects _ _)
      ((himgCover (fun i : {i : I // Nonempty (M i ≅ M i₀)} => U i.1) fun i => f i.1).mpr hi₀)
  · exact (hzero (U i.1) (hM.of_iso i.property.some)).of_iso (e i.1).some.symm

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

/-- **A locally constant sheaf of `Λ`-modules on the small étale site of a connected scheme which
vanishes over one object with nonempty source is zero.** -/
theorem isZero_of_isZero_overPullback_of_connectedSpace
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [ConnectedSpace S]
    (Λ : Type r) [Ring Λ]
    [HasSheafify (SmallEtale.topology B S hS) (ModuleCat.{m} Λ)]
    [∀ U : SmallEtale B S hS,
      HasSheafify ((SmallEtale.topology B S hS).over U) (ModuleCat.{m} Λ)]
    [HasProducts.{max u w} (ModuleCat.{m} Λ)]
    [HasColimitsOfSize.{max u w, max u w} (ModuleCat.{m} Λ)]
    (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{m} Λ))
    (hF : Stacks.ConstantSheaf.IsLocallyConstant (SmallEtale.topology B S hS) F)
    (V : SmallEtale B S hS) (z : S) (hz : z ∈ (siteEtaleImageOpen B S hS V : Set S))
    (hV : IsZero (((SmallEtale.topology B S hS).overPullback (ModuleCat.{m} Λ) V).obj F)) :
    IsZero F :=
  have : LocallySmall.{max u w} (SmallEtale B S hS) :=
    CategoryTheory.locallySmall_max.{w, u, u + 1}
  Stacks.ConstantSheaf.isZero_of_isZero_overPullback_of_connected
    (SmallEtale.topology B S hS) Λ (SmallEtale.final B S hS)
    (SmallEtale.finalIsTerminal B S hS)
    (fun U => (siteEtaleImageOpen B S hS U : Set S))
    (fun U => (siteEtaleImageOpen B S hS U).2)
    (fun U g => SmallEtale.ofArrows_mem_topology_final_iff B S hS U g)
    (exists_sitePoint_fiber_nonempty B S hS) F hF V z hz hV

end AlgebraicGeometry

end
