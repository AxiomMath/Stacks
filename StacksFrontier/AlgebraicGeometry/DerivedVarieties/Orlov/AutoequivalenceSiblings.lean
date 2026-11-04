module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.PullbackTensorFunctor
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Criterion
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent

/-!
# An exact autoequivalence of `D_perf` fixing the closed-point skyscrapers is a twisted pullback

Let `k` be a field, `X` a proper regular scheme over `k` and `e : D_perf(𝒪_X) ≌ D_perf(𝒪_X)` a
`k`-linear exact autoequivalence with `e(𝒪_x) ≅ 𝒪_x` for every closed point `x`. Steps four to six
of the proof of [Stacks, Tag 0G27] (`exists_pullbackTensor_of_fixes_perfectPointSheaf`) give an
automorphism `f` of `X` over `k`, the identity on the underlying space, and an invertible module
`ℒ` with `e(𝓕) ≅ f^*𝓕 ⊗ ℒ` naturally in the coherent module `𝓕`. This file carries out the last
step: `e` and `F'(M) = Lf^*M ⊗^𝐋 ℒ` are siblings, by [Stacks, Tag 0FZU], since they agree on
`Coh(𝒪_X)` and there are no negative `Ext`s between coherent modules.

It also records the sibling relation of [Stacks, Tag 0FZZ] for exact functors
`D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` with only `X` regular: `D_perf(𝒪_X) = D^b_Coh(𝒪_X)` by
[Stacks, Tag 0FDC] and `D_perf(𝒪_Y) ⊆ D^b_Coh(𝒪_Y)` by [Stacks, Tag 0FXU].

## Main definitions

* `AlgebraicGeometry.AreSiblingsPerfectRegularSource`: [Stacks, Tag 0FZZ] for a regular source.
* `AlgebraicGeometry.perfectCoherentSingleFunctor`: `Coh(𝒪_X) ⥤ D_perf(𝒪_X)`, `X` regular.

## Main results

* `AlgebraicGeometry.areSiblingsPerfectRegularSource_iff`: siblings on `D_perf` are functors with
  naturally isomorphic restrictions to `Coh(𝒪_X)` and isomorphic values.
* `Orlov.areSiblingsPerfect_perfectPullbackDerivedTensor`: the sibling statement, given the
  agreement on coherent modules.
* `Orlov.exists_areSiblingsPerfect_of_fixes_perfectPointSheaf`: [Stacks, Tag 0G27] for an
  autoequivalence.

## References

* [Stacks Project, Tag 0G27](https://stacks.math.columbia.edu/tag/0G27)
* [Stacks Project, Tag 0FZU](https://stacks.math.columbia.edu/tag/0FZU)
* [Stacks Project, Tag 0FZZ](https://stacks.math.columbia.edu/tag/0FZZ)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)
open AlgebraicGeometry.SheafOfModules (CoherentModules)
open AlgebraicGeometry.CoherentModuleFunctors

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard

-- Two abelian structures on `Coh(𝒪_X)` are in scope; `D^b_Coh` and the sibling relation are
-- stated with the one of `AlgebraicGeometry.CoherentAbelian`, so it is the one selected here.
attribute [local instance 100000] CoherentAbelian.coherentModulesAbelian

/-- **An invertible module on a regular Noetherian scheme, placed in degree zero, is perfect**: it
is coherent ([Stacks, Tag 01XZ]). -/
theorem isPerfect_single_of_isInvertible {X : Scheme.{u}} (hX : IsRegular X) [IsNoetherian X]
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    IsPerfect (X := X.toRingedSpace) ((DerivedCategory.singleFunctor X.Modules 0).obj L) :=
  isPerfect_single_of_isCoherent X hX L
    (@Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X _ L hL)

section PerfectRegularSource

/-- **[Stacks, Tag 0FXU] as an inequality of properties of objects of `D(𝒪_Y)`.** On a Noetherian
scheme every perfect object is bounded with coherent cohomology, so `D_perf(𝒪_Y)` is contained in
`D^b_Coh(𝒪_Y)`. -/
theorem _root_.AlgebraicGeometry.perfectInModules_le_derivedCategoryBBounded (Y : Scheme.{u})
    [IsNoetherian Y] :
    perfectInModules Y ≤ DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y) :=
  fun K hK => Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect Y K hK

/-- The inclusion `Coh(𝒪_X) ⥤ D_perf(𝒪_X)` of the coherent modules placed in degree zero, on a
quasi-compact regular scheme: the inclusion into `D^b_Coh(𝒪_X)` followed by the identification
`D^b_Coh(𝒪_X) = D_perf(𝒪_X)` of [Stacks, Tag 0FDC]. -/
def _root_.AlgebraicGeometry.perfectCoherentSingleFunctor {X : Scheme.{u}} (hX : IsRegular X)
    [CompactSpace X] :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      (perfectInModules X).FullSubcategory :=
  boundedCoherentSingleFunctor X ⋙
    ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge

variable {X Y : Scheme.{u}} (hX : IsRegular X) [CompactSpace X] [IsNoetherian Y]
  (F F' : (perfectInModules X).FullSubcategory ⥤ (perfectInModules Y).FullSubcategory)
  [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]

/-- **Stacks Project, Tag 0FZZ, for a regular source.** If `X` is regular then
`D_perf(𝒪_X) = D^b_Coh(𝒪_X)` by [Stacks, Tag 0FDC], and the source uses the same terminology for
exact functors `D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`, with no hypothesis on `Y` beyond the standing one: two
such functors are **siblings** if they are siblings as exact functors
`D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)`, after precomposition with `D^b_Coh(𝒪_X) = D_perf(𝒪_X)` and
composition with the inclusion `D_perf(𝒪_Y) ⊆ D^b_Coh(𝒪_Y)` of [Stacks, Tag 0FXU] (`Y`
Noetherian, as a scheme of finite type over a field is). For `Y` regular as well this is
`AlgebraicGeometry.AreSiblingsPerfect`
(`AlgebraicGeometry.areSiblingsPerfect_iff_areSiblingsPerfectRegularSource`). -/
@[stacks 0FZZ "the case of a regular source: siblings of exact functors \
`D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` for `X` quasi-compact regular and `Y` Noetherian"]
def _root_.AlgebraicGeometry.AreSiblingsPerfectRegularSource : Prop :=
  AreSiblingsCoherent
    (ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge ⋙ F ⋙
      ObjectProperty.ιOfLE (perfectInModules_le_derivedCategoryBBounded Y))
    (ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge ⋙ F' ⋙
      ObjectProperty.ιOfLE (perfectInModules_le_derivedCategoryBBounded Y))

/-- **For a regular target the two readings of [Stacks, Tag 0FZZ] on `D_perf` agree**: the
inclusion `D_perf(𝒪_Y) ⊆ D^b_Coh(𝒪_Y)` is then half of the identification of the two. -/
theorem _root_.AlgebraicGeometry.areSiblingsPerfect_iff_areSiblingsPerfectRegularSource
    (hY : IsRegular Y) :
    AreSiblingsPerfect hX hY F F' ↔ AreSiblingsPerfectRegularSource hX F F' :=
  Iff.rfl

/-- **Being siblings on `D_perf` of a regular Noetherian scheme, spelled out**: two exact functors
`D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` are siblings exactly when their restrictions to the coherent modules
are naturally isomorphic and their values at every perfect object are isomorphic. -/
theorem _root_.AlgebraicGeometry.areSiblingsPerfectRegularSource_iff [IsNoetherian X] :
    AreSiblingsPerfectRegularSource hX F F' ↔
      Nonempty (perfectCoherentSingleFunctor hX ⋙ F ≅ perfectCoherentSingleFunctor hX ⋙ F') ∧
        ∀ K, Nonempty (F.obj K ≅ F'.obj K) := by
  let ιY := ObjectProperty.ιOfLE (perfectInModules_le_derivedCategoryBBounded Y)
  have hff := ObjectProperty.fullyFaithfulιOfLE (perfectInModules_le_derivedCategoryBBounded Y)
  unfold AreSiblingsPerfectRegularSource
  rw [areSiblingsCoherent_iff]
  constructor
  · rintro ⟨⟨e⟩, h⟩
    refine ⟨⟨(hff.whiskeringRight _).preimageIso
      (e : (perfectCoherentSingleFunctor hX ⋙ F) ⋙ ιY ≅
        (perfectCoherentSingleFunctor hX ⋙ F') ⋙ ιY)⟩, fun K =>
      (h ((ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).le).obj
        K)).map hff.preimageIso⟩
  · rintro ⟨⟨e⟩, h⟩
    exact ⟨⟨(Functor.isoWhiskerRight e ιY :)⟩, fun K =>
      (h ((ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge).obj
        K)).map ιY.mapIso⟩

end PerfectRegularSource

section Siblings

variable {X : Scheme.{u}} {hX : IsRegular X} [IsNoetherian X]
  (e : PerfectDerivedCategory X ≌ PerfectDerivedCategory X) [e.functor.CommShift ℤ]
  [e.inverse.CommShift ℤ] [e.functor.IsTriangulated]
  (hfix : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
    Nonempty (e.functor.obj (perfectPointSheaf X hX x hx) ≅ perfectPointSheaf X hX x hx))
  (hfix' : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
    Nonempty (e.inverse.obj (perfectPointSheaf X hX x hx) ≅ perfectPointSheaf X hX x hx))

/-- **The last step of [Stacks, Tag 0G27]**: if the restriction of `e` to `Coh(𝒪_X)` is
`𝓕 ↦ f^*𝓕 ⊗ ℒ` for an automorphism `f` of `X` and an invertible module `ℒ`, then `e` and
`M ↦ Lf^*M ⊗^𝐋 ℒ` are siblings ([Stacks, Tag 0FZU]): on coherent modules the latter is
`𝓕 ↦ (f^*𝓕 ⊗ ℒ)[0]`, and there are no negative `Ext`s between coherent modules. -/
theorem areSiblingsPerfect_perfectPullbackDerivedTensor (f : X ≅ X) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (α : coherentToModules X ⋙ pullbackTensor f.hom L ≅
      coherentRestrictionOfFixes e hfix hfix' ⋙ coherentToModules X) :
    @AreSiblingsPerfect X X hX hX _ _ e.functor
      (perfectPullbackDerivedTensor f.hom L (isPerfect_single_of_isInvertible hX L hL))
      ‹_› ‹_›
      (show (perfectPullbackDerivedTensor f.hom L
        (isPerfect_single_of_isInvertible hX L hL)).CommShift ℤ from inferInstance)
      (show (perfectPullbackDerivedTensor f.hom L
        (isPerfect_single_of_isInvertible hX L hL)).IsTriangulated from inferInstance) := by
  let F' := perfectPullbackDerivedTensor f.hom L (isPerfect_single_of_isInvertible hX L hL)
  let G := boundedCoherentOfPerfect X hX e.functor
  let G' := boundedCoherentOfPerfect X hX F'
  let H := coherentRestrictionOfFixes e hfix hfix'
  let ιY := (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι
  let iso₁ : boundedCoherentSingleFunctor X ⋙ G ≅ H ⋙ boundedCoherentSingleFunctor X :=
    (coherentRestrictionOfBoundedCoherentIso G
      (essImage_boundedCoherentOfPerfect_obj e hfix hfix')).symm
  let iso₂' : (boundedCoherentSingleFunctor X ⋙ G') ⋙ ιY ≅
      (H ⋙ boundedCoherentSingleFunctor X) ⋙ ιY :=
    (Iso.refl ((boundedCoherentSingleFunctor X ⋙ ιY) ⋙ pullbackDerivedTensor f.hom L) :
        (boundedCoherentSingleFunctor X ⋙ G') ⋙ ιY ≅
          (boundedCoherentSingleFunctor X ⋙ ιY) ⋙ pullbackDerivedTensor f.hom L) ≪≫
      Functor.isoWhiskerRight (boundedCoherentSingleFunctorCompιIso X) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (singlePullbackDerivedTensorIso f.hom L (isFlat_of_isInvertible L hL)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight α _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft H (boundedCoherentSingleFunctorCompιIso X).symm ≪≫
      (Functor.associator _ _ _).symm
  let iso₂ : boundedCoherentSingleFunctor X ⋙ G' ≅ H ⋙ boundedCoherentSingleFunctor X :=
    ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso iso₂'
  delta AreSiblingsPerfect AreSiblingsCoherent
  refine @areSiblings_of_restrictionIso_of_negative_ext _ _ _ _ _ _ _ _ _ _ _ _
    (coherentToModulesDerivedBounded X ⋙ G) (coherentToModulesDerivedBounded X ⋙ G') ?_ ?_ ?_ ?_
    ⟨(iso₁ ≪≫ iso₂.symm : boundedSingleFunctor _ ⋙ (coherentToModulesDerivedBounded X ⋙ G) ≅
      boundedSingleFunctor _ ⋙ (coherentToModulesDerivedBounded X ⋙ G'))⟩ ?_
  exact fun A B q hq => @Equiv.subsingleton _ _
    (Iso.homCongr (iso₁.app A) ((shiftFunctor _ q).mapIso (iso₁.app B)))
    (subsingleton_hom_boundedCoherentSingle_shift X (H.obj A) (H.obj B) q hq)

end Siblings

section Field

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
  {hX : IsRegular X.left} [IsNoetherian X.left]

/-- **[Stacks, Tag 0G27] for an autoequivalence fixing the closed-point skyscrapers.** For `X`
proper and regular over `k` and a `k`-linear exact autoequivalence `e` of `D_perf(𝒪_X)` with
`e(𝒪_x) ≅ 𝒪_x` and `e⁻¹(𝒪_x) ≅ 𝒪_x` for every closed point `x`, there are an automorphism `f` of
`X` over `k` inducing the identity on the underlying topological space and an invertible
`𝒪_X`-module `ℒ` such that `e` and `M ↦ Lf^*M ⊗^𝐋 ℒ` are siblings. -/
theorem exists_areSiblingsPerfect_of_fixes_perfectPointSheaf
    (e : PerfectDerivedCategory X.left ≌ PerfectDerivedCategory X.left) [e.functor.CommShift ℤ]
    [e.inverse.CommShift ℤ] [e.functor.IsTriangulated]
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X; e.functor.Linear k)
    (hfix : ∀ (x : X.left) (hx : IsClosed ({x} : Set X.left)),
      Nonempty (e.functor.obj (perfectPointSheaf X.left hX x hx) ≅
        perfectPointSheaf X.left hX x hx))
    (hfix' : ∀ (x : X.left) (hx : IsClosed ({x} : Set X.left)),
      Nonempty (e.inverse.obj (perfectPointSheaf X.left hX x hx) ≅
        perfectPointSheaf X.left hX x hx)) :
    ∃ (f : X.left ≅ X.left) (L : X.left.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible X.left.presheaf X.left.ringCatSheaf.2 L),
      f.hom ≫ X.hom = X.hom ∧ (∀ x : X.left, f.hom x = x) ∧
      @AreSiblingsPerfect X.left X.left hX hX _ _ e.functor
        (perfectPullbackDerivedTensor f.hom L (isPerfect_single_of_isInvertible hX L hL))
        ‹_› ‹_›
        (show (perfectPullbackDerivedTensor f.hom L
          (isPerfect_single_of_isInvertible hX L hL)).CommShift ℤ from inferInstance)
        (show (perfectPullbackDerivedTensor f.hom L
          (isPerfect_single_of_isInvertible hX L hL)).IsTriangulated from inferInstance) := by
  obtain ⟨f, L, hL, ⟨α⟩, hf, hpts⟩ :=
    exists_pullbackTensor_of_fixes_perfectPointSheaf e hfix hfix' hlin
  exact ⟨f, L, hL, hf, hpts, areSiblingsPerfect_perfectPullbackDerivedTensor e hfix hfix' f L hL α⟩

end Field

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
