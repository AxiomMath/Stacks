module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.Amplitude
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.CoherentRestriction
public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.EquivalenceOverField
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.EquivalenceReconstruction
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentKernels.QuasiFiniteSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Affine
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.StalkOrder
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.TensorPullback
public import Mathlib.Topology.JacobsonSpace

/-!
# An exact autoequivalence of `D_perf` fixing the closed-point skyscrapers, on coherent modules

Let `k` be a field, `X` a proper regular scheme over `k` and `e : D_perf(𝒪_X) ≌ D_perf(𝒪_X)` a
`k`-linear exact autoequivalence with `e(𝒪_x) ≅ 𝒪_x` for every closed point `x`, where `𝒪_x` is the
residue-field skyscraper. This file carries out steps four to six of the proof of
[Stacks, Tag 0G27]:

* `e` carries `Coh(𝒪_X)` into itself (step three,
  `exists_isCoherent_iso_single_of_fixes_perfectPointSheaf`), so it restricts to a `k`-linear
  autoequivalence `H` of `Coh(𝒪_X)`;
* by [Stacks, Tag 0FZR] there are an automorphism `f` of `X` over `k` and an invertible module
  `ℒ` with `H(𝓕) ≅ f^*𝓕 ⊗ ℒ`;
* `f` is the identity on the underlying topological space: `f^*𝒪_x ⊗ ℒ ≅ H(𝒪_x) ≅ 𝒪_x` has support
  `f⁻¹(x)` and `{x}`, so `f` fixes the closed points, and a homeomorphism of a Jacobson space
  fixing the closed points is the identity.

## Main results

* `isEquivalence_coherentRestriction_of_fixes`: the restriction to `Coh(𝒪_X)` is an
  equivalence.
* `eq_of_forall_isClosed_apply_eq`: a homeomorphism of a Jacobson `T₀` space fixing every closed
  point is the identity.
* `exists_pullbackTensor_of_fixes_perfectPointSheaf`: the automorphism and the invertible module.

## References

* [Stacks Project, Tag 0G27](https://stacks.math.columbia.edu/tag/0G27)
* [Stacks Project, Tag 0FZR](https://stacks.math.columbia.edu/tag/0FZR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)
open AlgebraicGeometry.SheafOfModules (CoherentModules)
open AlgebraicGeometry.CoherentModuleFunctors
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Homeomorphisms of a Jacobson space fixing the closed points -/

/-- **A homeomorphism of a Jacobson `T₀` space fixing every closed point is the identity.** The
closure of a point `y` is the closure of the closed points it contains, which the homeomorphism
fixes; so `y` and its image have the same closure. -/
theorem eq_of_forall_isClosed_apply_eq {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    [T0Space T] (f : T ≃ₜ T) (h : ∀ x : T, IsClosed ({x} : Set T) → f x = x) (y : T) :
    f y = y := by
  have hfix : f '' (closure {y} ∩ closedPoints T) = closure {y} ∩ closedPoints T := by
    ext z
    refine ⟨?_, fun hz => ⟨z, hz, h z hz.2⟩⟩
    rintro ⟨w, hw, rfl⟩
    rwa [h w hw.2]
  have hc : closure (closure {y} ∩ closedPoints T) = closure {y} := by
    rw [JacobsonSpace.closure_inter_closedPoints_eq_closure isClosed_closure.isLocallyClosed,
      closure_closure]
  have hcl : closure ({f y} : Set T) = closure {y} := by
    rw [← Set.image_singleton, ← f.image_closure, ← hc, f.image_closure, hfix]
  exact (inseparable_iff_closure_eq.2 hcl).eq

/-! ### Supports of twisted pullbacks -/

section Support

variable {X Y : Scheme.{u}}

/-- An invertible module in the sense of `Stacks.SheafOfModules` is an `IsInvertibleModule`. -/
private theorem isInvertibleModule_of_isInvertible (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    Stacks.Ample.IsInvertibleModule Y L :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible Y.presheaf
    _ L).mp hL

/-- **The stalks of an invertible module are nonzero.** -/
theorem nontrivial_stalk_of_isInvertible (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) (y : Y) :
    Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf y) := by
  have := isInvertibleModule_of_isInvertible L hL
  obtain ⟨g, -, hg⟩ := Stacks.StalkOrder.exists_generator L y
  exact ⟨⟨g, 0, fun h0 => one_ne_zero (hg 1 (by rwa [one_smul]))⟩⟩

/-- **The support of `f^*𝓕 ⊗ ℒ` contains `f⁻¹(Supp 𝓕)`** for `𝓕` of finite type and `ℒ`
invertible: the stalk of the tensor product is the tensor product of the stalks, and over a local
ring the tensor product of two nonzero finite modules is nonzero. -/
theorem preimage_supp_subset_supp_pullbackTensor (f : Y ⟶ X) (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) (M : X.Modules)
    [M.IsFiniteType] :
    f ⁻¹' SheafOfModules.supp M ⊆ SheafOfModules.supp ((pullbackTensor f L).obj M) := by
  intro y hy
  have := isInvertibleModule_of_isInvertible L hL
  have : L.IsFiniteType := Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule L
  have h1 : Nontrivial (((Scheme.Modules.pullback f).obj M).presheaf.stalk y) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).mp (by rwa [Stacks.Modules.supp_pullback])
  have h2 : Nontrivial (L.presheaf.stalk y) := nontrivial_stalk_of_isInvertible L hL y
  have : Module.Finite (Y.presheaf.stalk y)
      (((Scheme.Modules.pullback f).obj M).presheaf.stalk y) :=
    SheafOfModules.finite_stalk Y.sheaf ((Scheme.Modules.pullback f).obj M) y
  have : Module.Finite (Y.presheaf.stalk y) (L.presheaf.stalk y) :=
    SheafOfModules.finite_stalk Y.sheaf L y
  refine (SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).mpr ?_
  have e : ((pullbackTensor f L).obj M).presheaf.stalk y ≃ₗ[Y.presheaf.stalk y]
      ((Scheme.Modules.pullback f).obj M).presheaf.stalk y ⊗[Y.presheaf.stalk y]
        L.presheaf.stalk y := by
    rw [← stalkModule_toRingedSpace_eq ((pullbackTensor f L).obj M) y,
      ← stalkModule_toRingedSpace_eq ((Scheme.Modules.pullback f).obj M) y,
      ← stalkModule_toRingedSpace_eq L y]
    exact Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y.toRingedSpace y
      ((Scheme.Modules.pullback f).obj M) L
  exact e.toEquiv.nontrivial_congr.mpr CoherentKernels.nontrivial_tensorProduct_of_finite

end Support

/-! ### The restriction to coherent modules -/

section Transport

variable (X : Scheme.{u}) (hX : IsRegular X) [IsNoetherian X]

/-- An endofunctor of `D_perf(𝒪_X)` read as an endofunctor of `D^b_Coh(𝒪_X)`, along the equality
`D_perf(𝒪_X) = D^b_Coh(𝒪_X)` of [Stacks, Tag 0FDC]. -/
abbrev boundedCoherentOfPerfect (F : PerfectDerivedCategory X ⥤ PerfectDerivedCategory X) :
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory :=
  ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge ⋙ F ⋙
    ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).le

variable {X hX}
variable (e : PerfectDerivedCategory X ≌ PerfectDerivedCategory X) [e.functor.CommShift ℤ]
  [e.inverse.CommShift ℤ]
  (hfix : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
    Nonempty (e.functor.obj (perfectPointSheaf X hX x hx) ≅ perfectPointSheaf X hX x hx))
  (hfix' : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
    Nonempty (e.inverse.obj (perfectPointSheaf X hX x hx) ≅ perfectPointSheaf X hX x hx))

include hfix hfix' in
/-- **An autoequivalence of `D_perf(𝒪_X)` fixing the closed-point skyscrapers, both ways, carries
`Coh(𝒪_X)` into `Coh(𝒪_X)`**, read in `D^b_Coh(𝒪_X)`. -/
theorem essImage_boundedCoherentOfPerfect_obj (A : CoherentModules X.ringCatSheaf) :
    (boundedCoherentSingleFunctor X).essImage
      ((boundedCoherentOfPerfect X hX e.functor).obj ((boundedCoherentSingleFunctor X).obj A)) := by
  let B := (boundedCoherentSingleFunctor X).obj A
  let eA : B.obj ≅ (DerivedCategory.singleFunctor X.Modules 0).obj A.obj :=
    (boundedCoherentSingleFunctorCompιIso X).app A
  let E : PerfectDerivedCategory X :=
    (ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge).obj B
  have : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor X.Modules 0).obj A.obj)
      0 := inferInstanceAs (((DerivedCategory.singleFunctor X.Modules 0).obj
        (show X.Modules from A.obj)).IsLE 0)
  have : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor X.Modules 0).obj A.obj)
      0 := inferInstanceAs (((DerivedCategory.singleFunctor X.Modules 0).obj
        (show X.Modules from A.obj)).IsGE 0)
  have h0 : E.obj.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso eA.symm 0
  have h0' : E.obj.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso eA.symm 0
  obtain ⟨N, hN, ⟨eN⟩⟩ :=
    exists_isCoherent_iso_single_of_fixes_perfectPointSheaf X hX e hfix hfix' E h0 h0'
  exact ⟨⟨N, hN⟩, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
    ((boundedCoherentSingleFunctorCompιIso X).app ⟨N, hN⟩ ≪≫ eN.symm)⟩⟩

/-- The restriction to `Coh(𝒪_X)` of an autoequivalence of `D_perf(𝒪_X)` fixing the closed-point
skyscrapers both ways. -/
abbrev coherentRestrictionOfFixes :
    CoherentModules X.ringCatSheaf ⥤ CoherentModules X.ringCatSheaf :=
  coherentRestrictionOfBoundedCoherent (boundedCoherentOfPerfect X hX e.functor)
    (essImage_boundedCoherentOfPerfect_obj e hfix hfix')

/-- **The restriction to `Coh(𝒪_X)` is an equivalence**: it is fully faithful because `e` and the
inclusion of `Coh(𝒪_X)` into `D^b_Coh(𝒪_X)` are, and essentially surjective because the inverse of
`e` carries `Coh(𝒪_X)` into itself as well. -/
theorem isEquivalence_coherentRestriction_of_fixes :
    (coherentRestrictionOfFixes e hfix hfix').IsEquivalence := by
  let G := boundedCoherentOfPerfect X hX e.functor
  let hF := essImage_boundedCoherentOfPerfect_obj e hfix hfix'
  let H := coherentRestrictionOfFixes e hfix hfix'
  have hG : G.FullyFaithful :=
    ((ObjectProperty.fullyFaithfulιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge).comp
      e.fullyFaithfulFunctor).comp
      (ObjectProperty.fullyFaithfulιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).le)
  have hH : H.FullyFaithful := Functor.FullyFaithful.ofCompFaithful
    (G := boundedCoherentSingleFunctor X)
    (Functor.FullyFaithful.ofIso ((boundedCoherentSingleFunctorFullyFaithful X).comp hG)
      (coherentRestrictionOfBoundedCoherentIso G hF).symm)
  have := hH.full
  have := hH.faithful
  have : H.EssSurj := ⟨fun N => by
    obtain ⟨M, ⟨eM⟩⟩ := essImage_boundedCoherentOfPerfect_obj e.symm hfix' hfix N
    exact ⟨M, ⟨(boundedCoherentSingleFunctorFullyFaithful X).preimageIso
      ((coherentRestrictionOfBoundedCoherentIso G hF).app M ≪≫ G.mapIso eM ≪≫
        (ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).le).mapIso
          (e.counitIso.app _))⟩⟩⟩
  exact { }

include hfix in
/-- **The restriction fixes the closed-point skyscrapers.** -/
theorem nonempty_coherentRestrictionOfFixes_obj_iso (x : X) (hx : IsClosed ({x} : Set X)) :
    Nonempty ((coherentRestrictionOfFixes e hfix hfix').obj
        ⟨residueFieldSkyscraperSheaf X x, isCoherent_residueFieldSkyscraperSheaf X x hx⟩ ≅
      ⟨residueFieldSkyscraperSheaf X x, isCoherent_residueFieldSkyscraperSheaf X x hx⟩) := by
  let G := boundedCoherentOfPerfect X hX e.functor
  let hF := essImage_boundedCoherentOfPerfect_obj e hfix hfix'
  let Ox : CoherentModules X.ringCatSheaf :=
    ⟨residueFieldSkyscraperSheaf X x, isCoherent_residueFieldSkyscraperSheaf X x hx⟩
  obtain ⟨eP⟩ := hfix x hx
  let c : (ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge).obj
      ((boundedCoherentSingleFunctor X).obj Ox) ≅ perfectPointSheaf X hX x hx :=
    (ObjectProperty.fullyFaithfulι _).preimageIso ((boundedCoherentSingleFunctorCompιIso X).app Ox)
  let ιle := ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).le
  exact ⟨(boundedCoherentSingleFunctorFullyFaithful X).preimageIso
    ((coherentRestrictionOfBoundedCoherentIso G hF).app Ox ≪≫
      ιle.mapIso (e.functor.mapIso c ≪≫ eP ≪≫ c.symm))⟩

end Transport

/-! ### The automorphism and the invertible module -/

/-- The inclusion of a full subcategory into a larger one is linear. -/
instance linear_ιOfLE {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C]
    [Linear R C] {P P' : ObjectProperty C} (h : P ≤ P') : (ObjectProperty.ιOfLE h).Linear R where
  map_smul _ _ := rfl

section Field

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
  {hX : IsRegular X.left} [IsNoetherian X.left]
  (e : PerfectDerivedCategory X.left ≌ PerfectDerivedCategory X.left) [e.functor.CommShift ℤ]
  [e.inverse.CommShift ℤ]
  (hfix : ∀ (x : X.left) (hx : IsClosed ({x} : Set X.left)),
    Nonempty (e.functor.obj (perfectPointSheaf X.left hX x hx) ≅ perfectPointSheaf X.left hX x hx))
  (hfix' : ∀ (x : X.left) (hx : IsClosed ({x} : Set X.left)),
    Nonempty (e.inverse.obj (perfectPointSheaf X.left hX x hx) ≅ perfectPointSheaf X.left hX x hx))

/-- **Steps four to six of [Stacks, Tag 0G27].** A `k`-linear autoequivalence `e` of
`D_perf(𝒪_X)`, for `X` proper and regular over `k`, fixing the closed-point skyscrapers both ways,
restricts on `Coh(𝒪_X)` to `𝓕 ↦ f^*𝓕 ⊗ ℒ` for an automorphism `f` of `X` over `k` which is the
identity on the underlying topological space and an invertible module `ℒ` ([Stacks, Tag 0FZR]). -/
theorem exists_pullbackTensor_of_fixes_perfectPointSheaf
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X; e.functor.Linear k) :
    ∃ (f : X.left ≅ X.left) (L : X.left.Modules),
      Stacks.SheafOfModules.IsInvertible X.left.presheaf X.left.ringCatSheaf.2 L ∧
      Nonempty (coherentToModules X.left ⋙ pullbackTensor f.hom L ≅
        coherentRestrictionOfFixes e hfix hfix' ⋙ coherentToModules X.left) ∧
      f.hom ≫ X.hom = X.hom ∧ ∀ x : X.left, f.hom x = x := by
  let : Linear k X.left.Modules := modulesLinear k X
  let : Linear k (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear k X
  have := isEquivalence_coherentRestriction_of_fixes e hfix hfix'
  have : e.functor.Linear k := hlin
  have : (boundedCoherentOfPerfect X.left hX e.functor).Linear k := ⟨fun {_ _} f r =>
    congrArg (ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X.left hX).le).map
      (Functor.Linear.map_smul (F := e.functor)
        ((ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X.left hX).ge).map f)
        r)⟩
  obtain ⟨f, L, hL, ⟨α⟩, hf⟩ := exists_iso_pullbackTensor_over_field k X X
    (coherentRestrictionOfFixes e hfix hfix')
    (linear_coherentRestrictionOfBoundedCoherent _ _ k)
  refine ⟨f, L, hL, ⟨α⟩, hf, ?_⟩
  have hclosed : ∀ x : X.left, IsClosed ({x} : Set X.left) → f.hom x = x := by
    intro x hx
    obtain ⟨β⟩ := nonempty_coherentRestrictionOfFixes_obj_iso e hfix hfix' x hx
    let γ : (pullbackTensor f.hom L).obj (residueFieldSkyscraperSheaf X.left x) ≅
        residueFieldSkyscraperSheaf X.left x :=
      α.app ⟨residueFieldSkyscraperSheaf X.left x,
          isCoherent_residueFieldSkyscraperSheaf X.left x hx⟩ ≪≫
        (coherentToModules X.left).mapIso β
    have : (residueFieldSkyscraperSheaf X.left x).IsFiniteType :=
      (isCoherent_residueFieldSkyscraperSheaf X.left x hx).isFiniteType
    have h1 := preimage_supp_subset_supp_pullbackTensor f.hom L hL
      (residueFieldSkyscraperSheaf X.left x)
    rw [SheafOfModules.supp_eq_of_iso γ, supp_residueFieldSkyscraperSheaf X.left x hx] at h1
    have hinv : f.hom (f.inv x) = x := by
      rw [← Scheme.Hom.comp_apply, f.inv_hom_id]
      rfl
    have h2 : f.inv x = x := h1 (show f.inv x ∈ f.hom ⁻¹' ({x} : Set X.left) from hinv)
    rwa [h2] at hinv
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  exact eq_of_forall_isClosed_apply_eq f.hom.homeomorph hclosed

end Field

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
