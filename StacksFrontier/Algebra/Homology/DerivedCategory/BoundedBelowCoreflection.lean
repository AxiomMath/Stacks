module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# `D⁺(ℬ) ≌ D⁺_ℬ(𝒜)` for an exact subcategory with a coreflection

Let `𝒜` be an abelian category and let `ℬ ⊆ 𝒜` be the full subcategory cut out by an object
property `P` closed under kernels, cokernels and finite products, so that `ℬ` is abelian and the
inclusion `i = P.ι` is exact. The inclusion induces the comparison functor

`D⁺(ℬ) ⟶ D⁺_ℬ(𝒜) ⊆ D(𝒜)`

onto the strictly full subcategory `DerivedCategoryB.derivedCategoryBPlus P` of bounded below
objects all of whose cohomology objects lie in `ℬ` ([Stacks, Tag 06UP]). This file proves that
the comparison is an equivalence as soon as `i` admits a right adjoint whose total right derived
functor inverts it *on the heart*: that is, given a right adjoint `Ψ` of the derived functor on
bounded below objects whose unit and counit are invertible on single objects, the comparison is
an equivalence.

This is the formal content of the proof of [Stacks, Tag 06ZV], where `𝒜` is the category of
`𝒪`-modules on the big site of an affine scheme, `ℬ = Adeq(𝒪)`, and `Ψ = RA` for the adequator
`A` of [Stacks, Tag 06ZS]: the source passes from the heart to all of `D⁺` by a spectral
sequence argument (Derived Categories, Lemma [Stacks, Tag 015J]), and the dévissage along the
truncation triangles below is the same passage, carried out on the derived category directly.

## Main definitions

* `DerivedCategoryB.boundedBelowComparison`: the comparison functor `D⁺(ℬ) ⥤ D⁺_ℬ(𝒜)`, the lift of
  `DerivedCategory.Plus.ι ⋙ P.ι.mapDerivedCategory` through the full subcategory.
* `DerivedCategoryB.boundedBelowEquivalence`: the equivalence `D⁺(ℬ) ≌ D⁺_ℬ(𝒜)`, whose functor is
  `DerivedCategoryB.boundedBelowComparison` by definition.

## Main results

* `DerivedCategory.Plus.isIso_app_of_isGE_of_isLE_plus` and
  `DerivedCategory.Plus.isIso_app_of_bounded_below`: the dévissage for a shift-compatible natural
  transformation between exact endofunctors of `D⁺(C)` — invertibility on the cohomology objects
  of `K`, placed in degree zero, gives invertibility at `K`.
* `DerivedCategoryB.boundedBelowComparison_ι`: the comparison functor followed by the inclusion of
  `D⁺_ℬ(𝒜)` *is* `DerivedCategory.Plus.ι ⋙ P.ι.mapDerivedCategory`, by `rfl`.
* `DerivedCategoryB.isEquivalence_boundedBelowComparison`: **the theorem**, that the comparison
  functor is an equivalence.
* `DerivedCategoryB.boundedBelowEquivalence_functor` and
  `DerivedCategoryB.boundedBelowEquivalence_inverse`: the functor and the quasi-inverse of the
  equivalence, pinned by `rfl`.

## Implementation notes

The dévissage is the bounded below one: an object of `D⁺(C)` has cohomology in a possibly
infinite range of degrees, so the window induction `DerivedCategory.Plus.prop_of_isGE_of_isLE`
has to be followed by a per-degree argument along the truncation triangle at the degree under
inspection. That second step is where the two functors are required to preserve boundedness
below; for the comparison functor this is proved below, and for `Ψ` it is a hypothesis, there
being no class recording it.

The analogous statement for endofunctors of the *unbounded* derived category is
`CategoryTheory.NatTrans.isIso_app_of_isGE` of
`StacksFrontier/Algebra/Homology/DerivedCategory/BoundedBelowNaturalTransformations.lean`. It does
not apply here: a total right derived functor is defined on `D⁺(𝒜)` only, so the composites
whose unit and counit are at stake are endofunctors of the bounded below derived categories and
of nothing larger.

`CategoryTheory.Functor.mapDerivedCategoryPlus` carries no `Functor.CommShift` or
`Functor.IsTriangulated` instance in the library; both hold because it is a lift of an exact
functor through a triangulated subcategory, and they are recorded here.

The equivalence is produced from the comparison functor by
`CategoryTheory.Functor.asEquivalence`, so that its functor field is the comparison functor
itself rather than something isomorphic to it, and its inverse field is
`CategoryTheory.Functor.inv` of that functor; both are pinned by `rfl`. The quasi-inverse of the
source's proof is `Ψ` restricted to `D⁺_ℬ(𝒜)`, which is isomorphic to
`CategoryTheory.Functor.inv` of the comparison functor because the counit exhibits it as a
right adjoint of an equivalence; that isomorphism is not spelled out, the inverse being
determined up to unique isomorphism by the comparison functor itself.

## References

* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

universe v u v' u'

namespace CategoryTheory.Functor

/-! ### Exact functors and boundedness below -/

section Exact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **An exact functor preserves boundedness below.** Its action on the derived category
commutes with cohomology, so the degrees in which the cohomology vanishes are unchanged. -/
theorem isGE_obj_mapDerivedCategory (X : DerivedCategory C) (n : ℤ) (hX : X.IsGE n) :
    (F.mapDerivedCategory.obj X).IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (F.map_isZero ((DerivedCategory.isGE_iff X n).1 hX i hi)).of_iso
    ((F.mapDerivedCategoryHomologyIso i).app X)

/-- **An exact functor preserves boundedness below on `D⁺`.** -/
theorem isGE_mapDerivedCategoryPlus_obj (X : DerivedCategory.Plus C) (n : ℤ) (hX : X.IsGE n) :
    (F.mapDerivedCategoryPlus.obj X).IsGE n := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
  exact isGE_obj_mapDerivedCategory F _ n ((DerivedCategory.Plus.isGE_ι_obj_iff X n).2 hX)

/-- The action of an exact functor on the bounded below derived category commutes with the
shift, being the lift of a shift-compatible functor through a shift-stable subcategory. -/
noncomputable instance commShift_mapDerivedCategoryPlus :
    (F.mapDerivedCategoryPlus).CommShift ℤ := by
  dsimp only [Functor.mapDerivedCategoryPlus]
  infer_instance

/-- The action of an exact functor on the bounded below derived category is triangulated, being
the lift of a triangulated functor through a triangulated subcategory. -/
instance isTriangulated_mapDerivedCategoryPlus :
    (F.mapDerivedCategoryPlus).IsTriangulated := by
  dsimp only [Functor.mapDerivedCategoryPlus]
  infer_instance

end Exact

end CategoryTheory.Functor

namespace DerivedCategory.Plus

/-! ### Dévissage of a natural transformation on the bounded below derived category -/

section Devissage

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {H₁ H₂ : Plus C ⥤ Plus C} [H₁.CommShift ℤ] [H₂.CommShift ℤ]
  [H₁.IsTriangulated] [H₂.IsTriangulated] (η : H₁ ⟶ H₂) [NatTrans.CommShift η ℤ]

/-- The objects of `D⁺(C)` at which `η` is invertible. -/
private abbrev plusIsoLocus : ObjectProperty (Plus C) := fun K ↦ IsIso (η.app K)

private instance plusIsoLocus_isTriangulated : (plusIsoLocus η).IsTriangulated :=
  Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated H₁ H₂ η

private instance plusIsoLocus_isClosedUnderIsomorphisms :
    (plusIsoLocus η).IsClosedUnderIsomorphisms :=
  Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms η

/-- **Invertibility on an object of `C` placed in degree zero gives invertibility on it placed
in any degree.** -/
theorem isIso_app_singleFunctor_obj_plus (M : C) (q : ℤ)
    (hM : IsIso (η.app ((singleFunctor C 0).obj M))) :
    IsIso (η.app ((singleFunctor C q).obj M)) :=
  prop_singleFunctor_obj (plusIsoLocus η) M q hM

/-- **The bounded case of the dévissage on `D⁺(C)`.** If `K` has no cohomology outside the
window `[a, a + n]` and `η` is invertible on each cohomology object of `K` placed in degree
zero, then `η` is invertible at `K`. -/
theorem isIso_app_of_isGE_of_isLE_plus (a : ℤ) :
    ∀ (n : ℕ) (K : Plus C), K.IsGE a → K.IsLE (a + (n : ℤ)) →
      (∀ q : ℤ, a ≤ q → q ≤ a + (n : ℤ) →
        IsIso (η.app ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)))) →
      IsIso (η.app K) :=
  prop_of_isGE_of_isLE (plusIsoLocus η) a

omit [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated]
  [NatTrans.CommShift η ℤ] in
/-- The naturality square of `η` at a morphism `g`, read on cohomology in a fixed degree. -/
private theorem isIso_homologyMap_app_plus_of_isIso {X Y : Plus C} (g : X ⟶ Y) (q : ℤ)
    (h₁ : IsIso ((homologyFunctor C q).map (H₁.map g)))
    (h₂ : IsIso ((homologyFunctor C q).map (H₂.map g)))
    (hX : IsIso ((homologyFunctor C q).map (η.app X))) :
    IsIso ((homologyFunctor C q).map (η.app Y)) := by
  have hcomm : (homologyFunctor C q).map (H₁.map g) ≫ (homologyFunctor C q).map (η.app Y) =
      (homologyFunctor C q).map (η.app X) ≫ (homologyFunctor C q).map (H₂.map g) := by
    simpa only [Functor.map_comp] using
      congrArg (fun m ↦ (homologyFunctor C q).map m) (η.naturality g)
  exact IsIso.of_isIso_fac_left hcomm

/-- **Invertibility on `D⁺(C)`, from invertibility on the cohomology objects.** Let
`η : H₁ ⟶ H₂` be a shift-compatible natural transformation between exact endofunctors of
`D⁺(C)`, each of which carries `D^{≥m}` into `D^{≥m}`, and let `K` be an object of `D⁺(C)`
bounded below by `a`. If `η` is invertible on every cohomology object of `K` placed in degree
zero, then `η` is invertible at `K`.

A morphism of `D⁺(C)` is invertible exactly when it is so on every cohomology object, so it is
enough to fix a degree `q`. Below `a` both sides vanish there. Otherwise truncate at `q`: the
truncation `τ_{≤q}K` sits in the window `[a, q]`, so `η` is invertible at it by the bounded
case, while `H₁` and `H₂` of the inclusion `τ_{≤q}K ⟶ K` are both invertible on `H^q` because
the third vertex of the truncation triangle lies in `D^{≥q+1}` and both functors keep it there.
The naturality square of `η` then forces the remaining map. -/
theorem isIso_app_of_bounded_below
    (hH₁ : ∀ (L : Plus C) (m : ℤ), L.IsGE m → (H₁.obj L).IsGE m)
    (hH₂ : ∀ (L : Plus C) (m : ℤ), L.IsGE m → (H₂.obj L).IsGE m)
    (K : Plus C) (a : ℤ) (hGE : K.IsGE a)
    (hH : ∀ q : ℤ, IsIso (η.app ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)))) :
    IsIso (η.app K) := by
  rw [isIso_iff]
  intro q
  by_cases haq : a ≤ q
  · have hT := TStructure.t.triangleLEGT_distinguished q K
    have hU : IsIso (η.app ((TStructure.t.truncLE q).obj K)) := by
      refine isIso_app_of_isGE_of_isLE_plus η a (q - a).toNat _ inferInstance ?_
        fun p hp₁ hp₂ ↦ ?_
      · rw [show a + ((q - a).toNat : ℤ) = q by omega]
        infer_instance
      · have hiso : IsIso ((homologyFunctor C p).map ((TStructure.t.truncLEι q).app K)) :=
          isIso_homologyMap_truncLEι_app K p q (by omega)
        exact (plusIsoLocus η).prop_of_iso
          ((singleFunctor C 0).mapIso (asIso ((homologyFunctor C p).map
            ((TStructure.t.truncLEι q).app K)))).symm (hH p)
    have hV : ((TStructure.t.truncGT q).obj K).IsGE (q + 1) := inferInstance
    have key : ∀ (H : Plus C ⥤ Plus C) [H.CommShift ℤ] [H.IsTriangulated],
        (∀ (L : Plus C) (m : ℤ), L.IsGE m → (H.obj L).IsGE m) →
        IsIso ((homologyFunctor C q).map (H.map ((TStructure.t.truncLEι q).app K))) :=
      fun H _ _ hH ↦ isIso_homologyMap_mor₁_of_isGE₃ _ (H.map_distinguished _ hT) q (q + 1)
        (hH _ (q + 1) hV) (by omega)
    have h₁ := key H₁ hH₁
    have h₂ := key H₂ hH₂
    exact isIso_homologyMap_app_plus_of_isIso η ((TStructure.t.truncLEι q).app K) q h₁ h₂
      inferInstance
  · have hz₁ := hH₁ K a hGE
    have hz₂ := hH₂ K a hGE
    exact IsZero.isIso (isZero_homology_of_isGE' (H₁.obj K) a q (by omega))
      (isZero_homology_of_isGE' (H₂.obj K) a q (by omega)) _

end Devissage

end DerivedCategory.Plus

namespace DerivedCategoryB

open DerivedCategory CategoryTheory.ObjectProperty

/-! ### The comparison functor `D⁺(ℬ) ⥤ D⁺_ℬ(𝒜)` -/

section Comparison

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts]
  [PreservesFiniteLimits P.ι] [PreservesFiniteColimits P.ι]
  [HasDerivedCategory P.FullSubcategory]

/-- The image of a bounded below complex of `ℬ` under the inclusion is a bounded below object of
`D(𝒜)` all of whose cohomology objects lie in `ℬ`. -/
theorem derivedCategoryBPlus_obj_mapDerivedCategory (X : Plus P.FullSubcategory) :
    derivedCategoryBPlus P ((Plus.ι ⋙ P.ι.mapDerivedCategory).obj X) := by
  obtain ⟨n, hn⟩ := X.2
  exact ⟨(isBoundedBelow_iff_exists_isGE _).2 ⟨n, P.ι.isGE_obj_mapDerivedCategory _ n hn⟩,
    fun m ↦ P.prop_of_iso ((P.ι.mapDerivedCategoryHomologyIso m).app (Plus.ι.obj X)).symm
      (P.prop_ι_obj _)⟩

/-- **The comparison functor `D⁺(ℬ) ⥤ D⁺_ℬ(𝒜)`** of [Stacks, Tag 06UP]: the inclusion
`ℬ ⥤ 𝒜` applied degreewise to complexes, read as a functor into the strictly full subcategory
of `D(𝒜)` of bounded below objects with cohomology in `ℬ`. -/
noncomputable def boundedBelowComparison :
    Plus P.FullSubcategory ⥤ (derivedCategoryBPlus P).FullSubcategory :=
  (derivedCategoryBPlus P).lift (Plus.ι ⋙ P.ι.mapDerivedCategory)
    (derivedCategoryBPlus_obj_mapDerivedCategory P)

/-- **The comparison functor is the canonical one**: composed with the inclusion of `D⁺_ℬ(𝒜)`
into `D(𝒜)` it *is* the inclusion of `D⁺(ℬ)` into `D(ℬ)` followed by the action of `ℬ ⥤ 𝒜`. -/
theorem boundedBelowComparison_ι :
    boundedBelowComparison P ⋙ (derivedCategoryBPlus P).ι = Plus.ι ⋙ P.ι.mapDerivedCategory :=
  rfl

/-- The comparison functor is the action of the inclusion on bounded below derived categories,
followed by the inclusion of `D⁺(𝒜)` into `D(𝒜)`. -/
theorem boundedBelowComparison_ι' :
    boundedBelowComparison P ⋙ (derivedCategoryBPlus P).ι =
      P.ι.mapDerivedCategoryPlus ⋙ Plus.ι :=
  rfl

end Comparison

/-! ### The equivalence -/

section Equivalence

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts]
  [PreservesFiniteLimits P.ι] [PreservesFiniteColimits P.ι]
  [HasDerivedCategory P.FullSubcategory]
  (Ψ : Plus A ⥤ Plus P.FullSubcategory) [Ψ.CommShift ℤ] [Ψ.IsTriangulated]
  (adj : P.ι.mapDerivedCategoryPlus ⊣ Ψ) [adj.CommShift ℤ]
  (hΨ : ∀ (L : Plus A) (m : ℤ), L.IsGE m → (Ψ.obj L).IsGE m)

include hΨ

omit [P.IsClosedUnderIsomorphisms] in
/-- **The unit of the derived adjunction is invertible**, as soon as it is invertible on the
single objects of `ℬ`: dévissage along the truncation triangles of `D⁺(ℬ)`. -/
theorem isIso_unit_of_isIso_app_singleFunctor
    (hunit : ∀ X : P.FullSubcategory,
      IsIso (adj.unit.app ((Plus.singleFunctor P.FullSubcategory 0).obj X))) :
    IsIso adj.unit := by
  have h : ∀ K : Plus P.FullSubcategory, IsIso (adj.unit.app K) := by
    intro K
    obtain ⟨a, ha⟩ := K.2
    exact Plus.isIso_app_of_bounded_below adj.unit (fun L m hL ↦ hL)
      (fun L m hL ↦ hΨ _ m (P.ι.isGE_mapDerivedCategoryPlus_obj L m hL)) K a
      ((Plus.isGE_ι_obj_iff K a).1 ha) fun q ↦ hunit _
  exact NatIso.isIso_of_isIso_app _

omit [P.IsClosedUnderIsomorphisms] in
/-- **The counit of the derived adjunction is invertible at a bounded below object with
cohomology in `ℬ`**, as soon as it is invertible on the single objects of `ℬ`: dévissage along
the truncation triangles of `D⁺(𝒜)`. -/
theorem isIso_counit_app_of_derivedCategoryBPlus
    (hcounit : ∀ (M : A), P M → IsIso (adj.counit.app ((Plus.singleFunctor A 0).obj M)))
    (K : Plus A) (hK : derivedCategoryBPlus P (Plus.ι.obj K)) :
    IsIso (adj.counit.app K) := by
  obtain ⟨a, ha⟩ := K.2
  exact Plus.isIso_app_of_bounded_below adj.counit
    (fun L m hL ↦ P.ι.isGE_mapDerivedCategoryPlus_obj _ m (hΨ L m hL))
    (fun L m hL ↦ hL) K a ((Plus.isGE_ι_obj_iff K a).1 ha) fun q ↦ hcounit _ (hK.2 q)

/-- **[Stacks, Tag 06ZV] in general form: the comparison functor `D⁺(ℬ) ⥤ D⁺_ℬ(𝒜)` is an
equivalence**, for a strictly full subcategory `ℬ` closed under kernels, cokernels and finite
products whose inclusion has a right adjoint on `D⁺` inverting it on the heart.

Nothing below asks `ℬ` to be a weak Serre subcategory: `DerivedCategoryB.derivedCategoryBPlus`
is an object property for any `P`, and the dévissage uses the triangulated structure of the two
derived categories only, not of `D⁺_ℬ(𝒜)`.

Fullness and faithfulness are the invertibility of the unit, and essential surjectivity is the
invertibility of the counit at the objects of `D⁺_ℬ(𝒜)`; both come from the heart by the
dévissage `DerivedCategory.Plus.isIso_app_of_bounded_below`. -/
theorem isEquivalence_boundedBelowComparison
    (hunit : ∀ X : P.FullSubcategory,
      IsIso (adj.unit.app ((Plus.singleFunctor P.FullSubcategory 0).obj X)))
    (hcounit : ∀ (M : A), P M → IsIso (adj.counit.app ((Plus.singleFunctor A 0).obj M))) :
    (boundedBelowComparison P).IsEquivalence := by
  have hu : IsIso adj.unit := isIso_unit_of_isIso_app_singleFunctor P Ψ adj hΨ hunit
  have hff : (P.ι.mapDerivedCategoryPlus).FullyFaithful := adj.fullyFaithfulLOfIsIsoUnit
  have hfull : (P.ι.mapDerivedCategoryPlus).Full := hff.full
  have hfaithful : (P.ι.mapDerivedCategoryPlus).Faithful := hff.faithful
  have h₁ : (Plus.ι ⋙ P.ι.mapDerivedCategory).Full :=
    show (P.ι.mapDerivedCategoryPlus ⋙ Plus.ι).Full from inferInstance
  have h₂ : (Plus.ι ⋙ P.ι.mapDerivedCategory).Faithful :=
    show (P.ι.mapDerivedCategoryPlus ⋙ Plus.ι).Faithful from inferInstance
  have hFull : (boundedBelowComparison P).Full := by
    dsimp only [boundedBelowComparison]
    infer_instance
  have hFaithful : (boundedBelowComparison P).Faithful := by
    dsimp only [boundedBelowComparison]
    infer_instance
  have hSurj : (boundedBelowComparison P).EssSurj := by
    refine ⟨fun Y ↦ ?_⟩
    obtain ⟨n, hn⟩ := (isBoundedBelow_iff_exists_isGE Y.1).1 Y.2.1
    let K : Plus A := ⟨Y.1, ⟨n, hn⟩⟩
    have := isIso_counit_app_of_derivedCategoryBPlus P Ψ adj hΨ hcounit K Y.2
    exact ⟨Ψ.obj K, ⟨(derivedCategoryBPlus P).fullyFaithfulι.preimageIso
      (Plus.ι.mapIso (asIso (adj.counit.app K)))⟩⟩
  exact { faithful := hFaithful, full := hFull, essSurj := hSurj }

/-- **[Stacks, Tag 06ZV] in general form, as an equivalence of categories.** -/
noncomputable def boundedBelowEquivalence
    (hunit : ∀ X : P.FullSubcategory,
      IsIso (adj.unit.app ((Plus.singleFunctor P.FullSubcategory 0).obj X)))
    (hcounit : ∀ (M : A), P M → IsIso (adj.counit.app ((Plus.singleFunctor A 0).obj M))) :
    Plus P.FullSubcategory ≌ (derivedCategoryBPlus P).FullSubcategory :=
  have := isEquivalence_boundedBelowComparison P Ψ adj hΨ hunit hcounit
  (boundedBelowComparison P).asEquivalence

/-- The functor of the equivalence is the canonical comparison functor. -/
theorem boundedBelowEquivalence_functor
    (hunit : ∀ X : P.FullSubcategory,
      IsIso (adj.unit.app ((Plus.singleFunctor P.FullSubcategory 0).obj X)))
    (hcounit : ∀ (M : A), P M → IsIso (adj.counit.app ((Plus.singleFunctor A 0).obj M))) :
    (boundedBelowEquivalence P Ψ adj hΨ hunit hcounit).functor = boundedBelowComparison P :=
  rfl

/-- The quasi-inverse of the equivalence is the inverse of the canonical comparison functor. -/
theorem boundedBelowEquivalence_inverse
    (hunit : ∀ X : P.FullSubcategory,
      IsIso (adj.unit.app ((Plus.singleFunctor P.FullSubcategory 0).obj X)))
    (hcounit : ∀ (M : A), P M → IsIso (adj.counit.app ((Plus.singleFunctor A 0).obj M))) :
    letI := isEquivalence_boundedBelowComparison P Ψ adj hΨ hunit hcounit
    (boundedBelowEquivalence P Ψ adj hΨ hunit hcounit).inverse = (boundedBelowComparison P).inv :=
  rfl

end Equivalence

end DerivedCategoryB

end
