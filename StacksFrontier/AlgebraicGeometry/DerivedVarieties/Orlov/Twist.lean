module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.AutoequivalenceSiblings
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.ObjectwiseOrlov
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeFunctionField
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation

/-!
# [Stacks, Tag 0G27] for an exact equivalence, and the twist over an algebraically closed field

Let `k` be a field, `X` a proper regular scheme over `k` and `F` a `k`-linear exact endofunctor of
`D_perf(𝒪_X)` with `F(𝓕) ≅ 𝓕` for every coherent `𝓕` with zero-dimensional support. Once `F` is
known to be fully faithful ([Stacks, Tag 0G26]) and essentially surjective ([Stacks, Tag 0GX0]),
it is an equivalence fixing the closed-point skyscrapers both ways, and
`exists_areSiblingsPerfect_of_fixes_perfectPointSheaf` gives the conclusion of
[Stacks, Tag 0G27]: an automorphism `f` of `X` over `k`, the identity on points, and an invertible
`ℒ` with `F` a sibling of `M ↦ Lf^*M ⊗^𝐋 ℒ`.

Over an algebraically closed field and for `X` smooth (hence reduced) the automorphism is the
identity, two morphisms of reduced schemes locally of finite type over an algebraically closed
field into a separated one being equal as soon as they agree on closed points; so `F` is
object-wise `E ↦ E ⊗^𝐋 ℒ` with `ℒ` invertible, which is the shape
`AlgebraicGeometry.TwistOfFixingZeroDimensional` asks for.

## Main results

* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.exists_areSiblingsPerfect_of_fullyFaithful_of_essSurj`:
  [Stacks, Tag 0G27] for `F` fully faithful and essentially surjective.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.exists_twist_of_fullyFaithful_of_essSurj`: over
  an algebraically closed field, the object-wise twist.

## References

* [Stacks Project, Tag 0G27](https://stacks.math.columbia.edu/tag/0G27)
* [Stacks Project, Tag 0G05](https://stacks.math.columbia.edu/tag/0G05)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard

-- Two abelian structures on `Coh(𝒪_X)` are in scope; `D^b_Coh` and the sibling relation are
-- stated with the one of `AlgebraicGeometry.CoherentAbelian`, so it is the one selected here.
attribute [local instance 100000] CoherentAbelian.coherentModulesAbelian

/-- **Siblings agree object by object**: if `F` and `F'` are siblings as functors on `D_perf`,
then `F(E) ≅ F'(E)` for every perfect `E`. -/
theorem nonempty_iso_obj_of_areSiblingsPerfect {X : Scheme.{u}} {hX : IsRegular X}
    [IsNoetherian X] (F F' : PerfectDerivedCategory X ⥤ PerfectDerivedCategory X)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : @AreSiblingsPerfect X X hX hX _ _ F F' ‹_› ‹_› ‹_› ‹_›) (E : PerfectDerivedCategory X) :
    Nonempty ((F.obj E).obj ≅ (F'.obj E).obj) := by
  let K := (ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).le).obj E
  let ι := (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι
  delta AreSiblingsPerfect AreSiblingsCoherent at h
  let c := coherentToModulesDerivedBounded X
  obtain ⟨-, ho⟩ := h
  obtain ⟨e⟩ := ho (c.objPreimage K)
  let i : c.obj (c.objPreimage K) ≅ K := c.objObjPreimageIso K
  exact ⟨ι.mapIso ((boundedCoherentOfPerfect X hX F).mapIso i.symm) ≪≫ ι.mapIso e ≪≫
    ι.mapIso ((boundedCoherentOfPerfect X hX F').mapIso i)⟩

section Field

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]

/-- **[Stacks, Tag 0G27] for a fully faithful, essentially surjective functor.** For `X` proper and
regular over `k` and a `k`-linear exact endofunctor `F` of `D_perf(𝒪_X)` with `F(𝓕) ≅ 𝓕` for every
coherent `𝓕` with zero-dimensional support, if `F` is fully faithful and essentially surjective,
there are an automorphism `f` of `X` over `k` inducing the identity on the underlying topological
space and an invertible `𝒪_X`-module `ℒ` such that `F` and `M ↦ Lf^*M ⊗^𝐋 ℒ` are siblings. -/
theorem exists_areSiblingsPerfect_of_fullyFaithful_of_essSurj (hX : IsRegular X.left)
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory X.left) [F.CommShift ℤ]
    [F.IsTriangulated]
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X; F.Linear k)
    (hfix : ∀ (𝓕 : X.left.Modules), 𝓕.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp 𝓕) = 0 →
      ∀ h𝓕 : IsPerfect (X := X.left.toRingedSpace)
          ((DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕),
        Nonempty ((F.obj ⟨_, h𝓕⟩).obj ≅ (DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕))
    (hFF : Nonempty F.FullyFaithful) [F.EssSurj] :
    haveI : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
    ∃ (f : X.left ≅ X.left) (L : X.left.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible X.left.presheaf X.left.ringCatSheaf.2 L),
      f.hom ≫ X.hom = X.hom ∧ (∀ x : X.left, f.hom x = x) ∧
      @AreSiblingsPerfect X.left X.left hX hX _ _ F
        (perfectPullbackDerivedTensor f.hom L (isPerfect_single_of_isInvertible hX L hL))
        ‹_› ‹_›
        (show (perfectPullbackDerivedTensor f.hom L
          (isPerfect_single_of_isInvertible hX L hL)).CommShift ℤ from inferInstance)
        (show (perfectPullbackDerivedTensor f.hom L
          (isPerfect_single_of_isInvertible hX L hL)).IsTriangulated from inferInstance) := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have := hFF.some.full
  have := hFF.some.faithful
  have : F.IsEquivalence := { }
  let e := F.asEquivalence
  let : e.functor.CommShift ℤ := ‹F.CommShift ℤ›
  have : e.functor.IsTriangulated := ‹F.IsTriangulated›
  let : e.inverse.CommShift ℤ := e.commShiftInverse ℤ
  have hP : ∀ (x : X.left) (hx : IsClosed ({x} : Set X.left)),
      Nonempty (F.obj (perfectPointSheaf X.left hX x hx) ≅ perfectPointSheaf X.left hX x hx) :=
    fun x hx => by
      obtain ⟨i⟩ := hfix _ (isCoherent_residueFieldSkyscraperSheaf X.left x hx)
        (topologicalKrullDim_supp_residueFieldSkyscraperSheaf X.left x hx)
        (perfectPointSheaf X.left hX x hx).property
      exact ⟨(ObjectProperty.fullyFaithfulι _).preimageIso i⟩
  have hP' : ∀ (x : X.left) (hx : IsClosed ({x} : Set X.left)),
      Nonempty (e.inverse.obj (perfectPointSheaf X.left hX x hx) ≅
        perfectPointSheaf X.left hX x hx) :=
    fun x hx => by
      obtain ⟨i⟩ := hP x hx
      exact ⟨e.inverse.mapIso i.symm ≪≫ e.unitIso.symm.app _⟩
  exact exists_areSiblingsPerfect_of_fixes_perfectPointSheaf e hlin hP hP'

end Field

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Over (Spec (CommRingCat.of k))}
  [IsProper X.hom] [Smooth X.hom]

/-- **Over an algebraically closed field, a functor as in [Stacks, Tag 0G27] is object-wise a
twist.** For `X` smooth and proper over an algebraically closed field `k` and a `k`-linear exact,
fully faithful and essentially surjective endofunctor `H` of `D_perf(𝒪_X)` fixing every coherent
module with zero-dimensional support, there are perfect `L, L'` with `L' ⊗^𝐋 L ≅ 𝒪_X` and
`H(E) ≅ E ⊗^𝐋 L` for every perfect `E`: the automorphism of [Stacks, Tag 0G27] fixes every point
of the reduced scheme `X`, hence is the identity ([Stacks, Tag 0G05]); `L` is the invertible
module and `L'` its dual. -/
theorem exists_twist_of_fullyFaithful_of_essSurj
    (H : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory X.left) [H.CommShift ℤ]
    [H.IsTriangulated]
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X; H.Linear k)
    (hfix : ∀ (𝓕 : X.left.Modules), 𝓕.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp 𝓕) = 0 →
      ∀ h𝓕 : IsPerfect (X := X.left.toRingedSpace)
          ((DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕),
        Nonempty ((H.obj ⟨_, h𝓕⟩).obj ≅ (DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕))
    (hFF : Nonempty H.FullyFaithful) [H.EssSurj] :
    ∃ L L' : DerivedCategory X.left.Modules,
      IsPerfect (X := X.left.toRingedSpace) L ∧ IsPerfect (X := X.left.toRingedSpace) L' ∧
        Nonempty ((dtenR X.left L).obj L' ≅
          (DerivedCategory.singleFunctor X.left.Modules 0).obj
            (SheafOfModules.unit X.left.ringCatSheaf)) ∧
        ∀ E : PerfectDerivedCategory X.left,
          Nonempty ((H.obj E).obj ≅ (dtenR X.left L).obj E.obj) := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have hX : IsRegular X.left := isRegular_of_smooth_over_field X.hom
  obtain ⟨f, L, hL, hf, hpts, hsib⟩ :=
    exists_areSiblingsPerfect_of_fullyFaithful_of_essSurj hX H hlin hfix hFF
  have hf1 : f.hom = 𝟙 X.left := by
    have : IsReduced X.left := isReduced_of_isRegular hX
    have : LocallyOfFiniteType (f.hom ≫ X.hom) := by
      rw [hf]
      infer_instance
    exact AlgebraicGeometry.ext_of_apply_eq X.hom Set.univ isClosed_univ.isLocallyClosed dense_univ
      (fun x _ _ => by rw [hpts x]; rfl) (by rw [hf, Category.id_comp])
  have hLi := hL
  let L' : X.left.Modules := Stacks.SheafOfModules.dualSheaf X.left.presheaf X.left.ringCatSheaf.2 L
  have hL' : Stacks.SheafOfModules.IsInvertible X.left.presheaf X.left.ringCatSheaf.2 L' :=
    Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.left.presheaf X.left.ringCatSheaf.2 L
  have hev :=
    Stacks.SheafOfModules.Invertible.isIso_evaluation X.left.presheaf X.left.ringCatSheaf.2 L
  refine ⟨(DerivedCategory.singleFunctor X.left.Modules 0).obj L,
    (DerivedCategory.singleFunctor X.left.Modules 0).obj L',
    isPerfect_single_of_isInvertible hX L hL, isPerfect_single_of_isInvertible hX L' hL',
    ⟨(singleDerivedTensorIso X.left L (isFlat_of_isInvertible L hL)).app L' ≪≫
      (DerivedCategory.singleFunctor X.left.Modules 0).mapIso
        (@asIso _ _ _ _ (Stacks.SheafOfModules.evaluation X.left.presheaf X.left.ringCatSheaf.2 L)
          hev)⟩,
    fun E => ?_⟩
  obtain ⟨e⟩ := nonempty_iso_obj_of_areSiblingsPerfect H _ hsib E
  exact ⟨e ≪≫ (dtenR X.left _).mapIso (eqToIso (by rw [hf1]; rfl) ≪≫
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso
      X.left.toRingedSpace).app E.obj)⟩

end AlgClosed

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
