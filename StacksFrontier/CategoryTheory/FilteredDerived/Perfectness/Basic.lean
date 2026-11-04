module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.RingTheory.Finiteness.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Homology.Perfect.Defs

/-!
# Perfect complexes over a ring

For a ring `R`, the perfect homotopy category `K_perf(R)` consists of the bounded cochain
complexes of finite projective left `R`-modules, with morphisms taken up to homotopy. Its
canonical functor to the derived category `D(R)` is fully faithful, and its essential image
is the full subcategory `D_perf(R)` of perfect objects.

## Main definitions

* `CategoryTheory.FilteredDerived.finiteProjectiveComplex`: being a bounded complex with finite
  projective terms.
* `CategoryTheory.FilteredDerived.PerfectHomotopyCategory`: the category `K_perf(R)` of bounded
  complexes of finite projective modules up to homotopy.
* `CategoryTheory.FilteredDerived.perfectComplexFunctor`: its canonical functor to the derived
  category.
* `CategoryTheory.FilteredDerived.PerfectDerivedCategory`: the full subcategory `D_perf(R)` of
  perfect objects of the derived category.

## Main results

* `CategoryTheory.FilteredDerived.perfectComplexFunctorFullyFaithful`: the canonical functor
  `K_perf(R) ⥤ D(R)` is fully faithful.
* `CategoryTheory.FilteredDerived.isPerfect_iff`: perfect objects are characterized by finite
  projective representatives.
* `CategoryTheory.FilteredDerived.isPerfect_iff_exists_perfectHomotopyObject`: the perfect
  objects are exactly the essential image of the canonical functor.

## References

* [Stacks Project, Tag 03TH](https://stacks.math.columbia.edu/tag/03TH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

/-- The property of a cochain complex of `R`-modules of being bounded with finite projective
terms. -/
public abbrev finiteProjectiveComplex (R : Type u) [Ring R] :
    ObjectProperty (CochainComplex (ModuleCat.{v} R) ℤ) :=
  fun K ↦
    ((CochainComplex.plus (ModuleCat.{v} R) K) ∧
      (CochainComplex.minus (ModuleCat.{v} R) K)) ∧
    ∀ i : ℤ, Module.Projective R (K.X i) ∧ Module.Finite R (K.X i)

/-- The bounded complexes of finite projective `R`-modules, regarded in the homotopy category. -/
@[sga "4½ Rapport 4.3" "partial"]
public abbrev perfectHomotopyProperty (R : Type u) [Ring R] :
    ObjectProperty (HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)) :=
  (finiteProjectiveComplex.{u, v} R).strictMap
    (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ))

/-- The category `K_perf(R)` of bounded complexes of finite projective `R`-modules, with
morphisms up to homotopy. -/
@[stacks 03TH "the category K_perf", sga "4½ Rapport 4.3" "K_parf(Λ)"]
public abbrev PerfectHomotopyCategory (R : Type u) [Ring R] :=
  (perfectHomotopyProperty.{u, v} R).FullSubcategory

/-- The canonical functor from `K_perf(R)` to `D(R)`. -/
@[stacks 03TH "the functor to D(R)", implicit_reducible]
public def perfectComplexFunctor (R : Type u) [Ring R] :
    PerfectHomotopyCategory.{u, v} R ⥤ DerivedCategory (ModuleCat.{v} R) :=
  (perfectHomotopyProperty.{u, v} R).ι ⋙ DerivedCategory.Qh

/-- An object of `K_perf(R)` is the image of a bounded complex of finite projective modules. -/
private lemma exists_finiteProjectiveComplex_of_perfectHomotopyProperty (R : Type u) [Ring R]
    (K : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ))
    (hK : perfectHomotopyProperty.{u, v} R K) :
    ∃ L, finiteProjectiveComplex.{u, v} R L ∧
      (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).obj L = K :=
  (ObjectProperty.strictMap_iff _ _ K).mp hK

/-- A bounded complex of finite projective modules representing an object of `K_perf(R)` is
K-projective. -/
public lemma isKProjective_obj (R : Type u) [Ring R]
    (K : PerfectHomotopyCategory.{u, v} R) : CochainComplex.IsKProjective K.obj.as := by
  obtain ⟨L, ⟨⟨_, ⟨d, hd⟩⟩, hproj⟩, h⟩ :=
    exists_finiteProjectiveComplex_of_perfectHomotopyProperty R K.obj K.property
  have h' : L = K.obj.as := congr_arg CategoryTheory.Quotient.as h
  rw [← h']
  let : L.IsStrictlyLE d := hd
  let (i : ℤ) : Module.Projective R (L.X i) := (hproj i).1
  let (i : ℤ) : Projective (L.X i) := inferInstance
  exact CochainComplex.isKProjective_of_projective L d

/-- The canonical functor from perfect complexes up to homotopy to the derived category is fully
faithful. -/
@[stacks 03TH "full faithfulness",
  sga "4 XVII 5.5.6.3" "more general",
  sga "4½ Rapport 4.3",
  sga "6 I 4.10" "Clause (i), special case",
  sga "6 I 4.12.2" "Case C = R-modules",
  sga "6 II 1.1" "c), special case"]
public def perfectComplexFunctorFullyFaithful (R : Type u) [Ring R] :
    (perfectComplexFunctor.{u, v} R).FullyFaithful :=
  ((Functor.FullyFaithful.nonempty_iff_map_bijective (perfectComplexFunctor.{u, v} R)).2
    (fun ⟨Kobj, hK⟩ ⟨Lobj, hL⟩ ↦ by
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Kobj
      obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Lobj
      let K' : PerfectHomotopyCategory.{u, v} R :=
        ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩
      let : CochainComplex.IsKProjective K := by
        rw [← HomotopyCategory.quotient_obj_as K]
        exact isKProjective_obj.{u, v} R K'
      change Function.Bijective
        (DerivedCategory.Qh.map ∘ (perfectHomotopyProperty.{u, v} R).ι.map)
      exact (CochainComplex.IsKProjective.Qh_map_bijective K
          ((HomotopyCategory.quotient _ _).obj L)).comp
          ((perfectHomotopyProperty.{u, v} R).fullyFaithfulι.map_bijective K'
            ⟨(HomotopyCategory.quotient _ _).obj L, hL⟩))).some

/-- The canonical functor from perfect complexes is full. -/
public instance perfectComplexFunctor_full (R : Type u) [Ring R] :
    (perfectComplexFunctor.{u, v} R).Full :=
  (perfectComplexFunctorFullyFaithful.{u, v} R).full

/-- The canonical functor from perfect complexes is faithful. -/
public instance perfectComplexFunctor_faithful (R : Type u) [Ring R] :
    (perfectComplexFunctor.{u, v} R).Faithful :=
  (perfectComplexFunctorFullyFaithful.{u, v} R).faithful

/-- A derived object is perfect exactly when it is isomorphic to the image of a bounded
complex of finite projective modules. -/
@[stacks 03TH "perfect objects", sga "4½ Rapport 4.3" "D_parf(Λ)"]
public lemma isPerfect_iff (R : Type u) [Ring R]
    (X : DerivedCategory (ModuleCat.{v} R)) :
    StacksDraft.Perfect.IsPerfect X ↔
      ∃ K : CochainComplex (ModuleCat.{v} R) ℤ,
        finiteProjectiveComplex.{u, v} R K ∧ Nonempty (DerivedCategory.Q.obj K ≅ X) := by
  constructor
  · rintro ⟨P, a, b, ha, hb, hfinite, hprojective, ⟨e⟩⟩
    exact ⟨P, ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, fun i ↦ ⟨hprojective i, hfinite i⟩⟩, ⟨e.symm⟩⟩
  · rintro ⟨P, ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hterms⟩, ⟨e⟩⟩
    exact ⟨P, a, b, ha, hb, (fun i ↦ (hterms i).2), (fun i ↦ (hterms i).1), ⟨e.symm⟩⟩

/-- Perfect objects are exactly the essential image of the canonical functor from
`K_perf(R)`. -/
public lemma isPerfect_iff_exists_perfectHomotopyObject (R : Type u) [Ring R]
    (X : DerivedCategory (ModuleCat.{v} R)) :
    StacksDraft.Perfect.IsPerfect X ↔
      ∃ K : PerfectHomotopyCategory.{u, v} R,
        Nonempty ((perfectComplexFunctor.{u, v} R).obj K ≅ X) := by
  rw [isPerfect_iff]
  refine ⟨fun ⟨L, hL, ⟨e⟩⟩ ↦ ⟨⟨(HomotopyCategory.quotient _ _).obj L,
    (finiteProjectiveComplex.{u, v} R).strictMap_obj _ hL⟩,
    ⟨(DerivedCategory.quotientCompQhIso _).app L ≪≫ e⟩⟩, ?_⟩
  rintro ⟨⟨K, hK⟩, ⟨e⟩⟩
  obtain ⟨L, hL, rfl⟩ := exists_finiteProjectiveComplex_of_perfectHomotopyProperty R K hK
  exact ⟨L, hL, ⟨(DerivedCategory.quotientCompQhIso _).symm.app L ≪≫ e⟩⟩

/-- Perfectness is invariant under isomorphism in the derived category. -/
public instance isPerfect_isClosedUnderIsomorphisms (R : Type u) [Ring R] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DerivedCategory (ModuleCat.{v} R) ↦ StacksDraft.Perfect.IsPerfect K) where
  of_iso := by
    rintro X Y e ⟨P, a, b, ha, hb, hf, hp, ⟨f⟩⟩
    exact ⟨P, a, b, ha, hb, hf, hp, ⟨e.symm ≪≫ f⟩⟩

/-- The full subcategory `D_perf(R)` of perfect derived objects. -/
@[stacks 03TH "the category D_perf", sga "4½ Rapport 4.3" "D_parf(Λ)"]
public abbrev PerfectDerivedCategory (R : Type u) [Ring R] :=
  ObjectProperty.FullSubcategory
    (fun K : DerivedCategory (ModuleCat.{v} R) ↦ StacksDraft.Perfect.IsPerfect K)

end CategoryTheory.FilteredDerived
