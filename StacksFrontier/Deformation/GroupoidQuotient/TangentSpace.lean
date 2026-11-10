module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.LinearAlgebra.Quotient.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Groupoid.Basic
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.GroupoidQuotient.DeformationCategory
public import StacksFrontier.Deformation.GroupoidQuotient.RimSchlessinger
public import StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor
public import StacksFrontier.Deformation.TangentSpace.Predeformation

/-!
# The tangent space of the quotient of a groupoid in functors

For a smooth groupoid in deformation functors, the tangent space of its quotient is canonically
the cokernel of the difference between the source and target differentials: the sequence

`T_R --(ds - dt)--> T_U --dq--> T_Q`

is exact and `dq` is surjective, so `dq` induces an isomorphism `T_U / im(ds - dt) ≅ T_Q`.

## Main definitions

* `Deformation.objectFiber`: an element of a set-valued functor as an object of the strict
  fibre of its category of elements.
* `Deformation.quotientFiberObject`: the same for the quotient category.
* `Deformation.quotientTangentEquiv`: the identification of the quotient tangent space with
  the cokernel of the difference of the two differentials.

## Main results

* `Deformation.objectFiber_surjective` and `Deformation.quotientFiberObject_surjective`: every
  object of the respective fibre arises this way.
* `Deformation.quotientFiberIsoOfArrow`: an arrow of the groupoid induces an isomorphism of the
  corresponding objects of the quotient fibre.
* `Deformation.arrowOfQuotientFiberHom`: conversely, a morphism of the quotient fibre comes from
  an arrow with the prescribed source and target.

## Implementation notes

Tangent spaces are taken through the associated functors of isomorphism classes of the
categories of elements and of the quotient category. The identification is characterized by the
canonical map from objects to the quotient, so it is not merely an abstract isomorphism of
vector spaces; that characterization also determines it uniquely.

## References

* [Stacks Project, Tag 06KU](https://stacks.math.columbia.edu/tag/06KU)
-/

@[expose] public section

namespace Deformation

/-! ### Objects of the strict fibres of a category of elements and of a quotient -/

section
open CategoryTheory

/-- An element of a set-valued functor, as an object of the strict fibre of its category of
elements. This is a section of `Deformation.elementsFiberValue`. -/
public def objectFiber {C : Type*} [Category C] {F : C ⥤ Type*} (A : C)
    (x : F.obj A) : Functor.Fiber (Functor.Elements.π F) A :=
  ⟨F.elementsMk A x, rfl⟩

/-- Every object of the strict fibre of a category of elements is of this form. -/
public theorem objectFiber_surjective {C : Type*} [Category C] {F : C ⥤ Type*} (A : C)
    (X : Functor.Fiber (Functor.Elements.π F) A) :
    ∃ x, X = objectFiber A x := by
  rcases X with ⟨⟨x⟩, rfl⟩
  exact ⟨x, rfl⟩

/-- An object of the groupoid over `A`, as an object of the strict fibre of the quotient
category over `A`. -/
public def quotientFiberObject {C : Type*} [Category C] (G : GroupoidInFunctors C)
    (A : C) (x : G.objects.obj A) :
    Functor.Fiber (Grothendieck.forget (evaluationFunctor G)) A :=
  ⟨⟨A, x⟩, rfl⟩

/-- Every object of the strict fibre of the quotient category is of this form. -/
public theorem quotientFiberObject_surjective {C : Type*} [Category C]
    (G : GroupoidInFunctors C) (A : C)
    (X : Functor.Fiber (Grothendieck.forget (evaluationFunctor G)) A) :
    ∃ x, X = quotientFiberObject G A x := by
  rcases X with ⟨⟨B, x⟩, rfl⟩
  exact ⟨x, rfl⟩

/-- An arrow of the groupoid over `A` with source `x` and target `y` makes the corresponding
objects of the quotient fibre isomorphic. -/
public noncomputable def quotientFiberIsoOfArrow {C : Type*} [Category C]
    (G : GroupoidInFunctors C) (A : C) {x y : G.objects.obj A}
    (r : G.arrows.obj A) (hs : G.source.app A r = x) (ht : G.target.app A r = y) :
    quotientFiberObject G A x ≅ quotientFiberObject G A y := by
  let _ : Groupoid (G.objects.obj A) := G.evaluationGroupoid A
  let a : x ⟶ y := (G.evaluationArrowEquiv A x y).symm ⟨r, hs, ht⟩
  let e₂ : ((evaluationFunctor G).map (𝟙 A)).toFunctor.obj x ≅ y := by
    change G.objects.map (𝟙 A) x ≅ y
    exact (eqToIso (G.objects.map_id_apply A x)).trans (asIso a)
  let e : (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ≅ ⟨A, y⟩ :=
    Grothendieck.isoMk (Iso.refl A) e₂
  let _ : (Grothendieck.forget (evaluationFunctor G)).IsHomLift (𝟙 A) e.hom :=
    IsHomLift.map _ e.hom
  let _ : (Grothendieck.forget (evaluationFunctor G)).IsHomLift (𝟙 A) e.inv :=
    IsHomLift.map _ e.inv
  exact ⟨Functor.Fiber.homMk _ A e.hom, Functor.Fiber.homMk _ A e.inv,
    Functor.Fiber.hom_ext e.hom_inv_id, Functor.Fiber.hom_ext e.inv_hom_id⟩

/-- A morphism between two objects of the quotient fibre over `A` comes from an arrow of the
groupoid with the prescribed source and target. -/
public noncomputable def arrowOfQuotientFiberHom {C : Type*} [Category C]
    (G : GroupoidInFunctors C) (A : C) {x y : G.objects.obj A}
    (f : quotientFiberObject G A x ⟶ quotientFiberObject G A y) :
    {r : G.arrows.obj A // G.source.app A r = x ∧ G.target.app A r = y} := by
  let p := Grothendieck.forget (evaluationFunctor G)
  change {φ : (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨A, y⟩ //
    p.IsHomLift (𝟙 A) φ} at f
  rcases f with ⟨⟨base, fiber⟩, hLift⟩
  let f : (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨A, y⟩ := ⟨base, fiber⟩
  let _ : p.IsHomLift (𝟙 A) f := hLift
  have hb : base = 𝟙 A :=
    (IsHomLift.fac' p (𝟙 A) f).trans (by simp only [Category.id_comp, eqToHom_trans]; rfl)
  subst base
  exact G.evaluationArrowEquiv A x y
    (eqToHom (G.objects.map_id_apply A x).symm ≫ fiber)

end

/-! ### The tangent space of the quotient -/

section
open CategoryTheory

universe u w

/-- The canonical tangent space of a smooth quotient is the cokernel of
the source-minus-target differential. -/
@[stacks 06KU "quotient_tangent_space"]
public noncomputable def quotientTangentEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hG : GroupoidInFunctors.IsSmooth G)
    (hU : IsDeformationFunctor G.objects)
    (hR : IsDeformationFunctor G.arrows) :
    let 𝓡 := BasedCategory.ofFunctor (Functor.Elements.π G.arrows)
    let 𝓤 := BasedCategory.ofFunctor (Functor.Elements.π G.objects)
    let 𝓠 := BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G))
    let h𝓡 := ((isDeformationCategory_iff G.arrows).2 hR).predeformation
    let h𝓤 := ((isDeformationCategory_iff G.objects).2 hU).predeformation
    let h𝓠 := quotient_isPredeformationCategory G hU hR
    let s2𝓡 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓡 h𝓡.cofibered (schlessingerConditionS2_of_satisfiesRS hR.2) (Or.inl h𝓡)
    let s2𝓤 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓤 h𝓤.cofibered (schlessingerConditionS2_of_satisfiesRS hU.2) (Or.inl h𝓤)
    let s2𝓠 := schlessingerConditionS2_of_isIsomorphismClasses
      𝓠 h𝓠.cofibered
      (schlessingerConditionS2_of_satisfiesRS (quotient_satisfiesRS G hG hU.2 hR.2))
      (Or.inl h𝓠)
    letI : Fact (IsPredeformationCategory 𝓡.p) := ⟨h𝓡⟩
    letI : Fact (IsPredeformationCategory 𝓤.p) := ⟨h𝓤⟩
    letI : Fact (IsPredeformationCategory 𝓠.p) := ⟨h𝓠⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓡 h𝓡.cofibered))) := ⟨s2𝓡⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓤 h𝓤.cofibered))) := ⟨s2𝓤⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓠 h𝓠.cofibered))) := ⟨s2𝓠⟩
    let TR := artinianTangentSpace Λ k (isomorphismClasses 𝓡 h𝓡.cofibered)
    let TU := artinianTangentSpace Λ k (isomorphismClasses 𝓤 h𝓤.cofibered)
    let TQ := artinianTangentSpace Λ k (isomorphismClasses 𝓠 h𝓠.cofibered)
    let ds : TR →ₗ[k] TU := IsLinearMap.mk'
      (differential h𝓡.cofibered h𝓤.cofibered (elementsBasedFunctor G.source))
      (differential_isLinearMap 𝓡 𝓤 h𝓡 h𝓤 s2𝓡 s2𝓤 (elementsBasedFunctor G.source))
    let dt : TR →ₗ[k] TU := IsLinearMap.mk'
      (differential h𝓡.cofibered h𝓤.cofibered (elementsBasedFunctor G.target))
      (differential_isLinearMap 𝓡 𝓤 h𝓡 h𝓤 s2𝓡 s2𝓤 (elementsBasedFunctor G.target))
    let dq : TU →ₗ[k] TQ := IsLinearMap.mk'
      (differential h𝓤.cofibered h𝓠.cofibered
        (⟨quotientMorphism G, quotientMorphism_over G⟩ : BasedFunctor 𝓤 𝓠))
      (differential_isLinearMap 𝓤 𝓠 h𝓤 h𝓠 s2𝓤 s2𝓠
        (⟨quotientMorphism G, quotientMorphism_over G⟩ : BasedFunctor 𝓤 𝓠))
    { e : (TU ⧸ LinearMap.range (ds - dt)) ≃ₗ[k] TQ //
      ∀ x : TU, e (Submodule.Quotient.mk x) = dq x } := by
  classical
  let 𝓡 := BasedCategory.ofFunctor (Functor.Elements.π G.arrows)
  let 𝓤 := BasedCategory.ofFunctor (Functor.Elements.π G.objects)
  let 𝓠 := BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G))
  let h𝓡 := ((isDeformationCategory_iff G.arrows).2 hR).predeformation
  let h𝓤 := ((isDeformationCategory_iff G.objects).2 hU).predeformation
  let h𝓠 := quotient_isPredeformationCategory G hU hR
  let s2𝓡 := schlessingerConditionS2_of_isIsomorphismClasses
    𝓡 h𝓡.cofibered (schlessingerConditionS2_of_satisfiesRS hR.2) (Or.inl h𝓡)
  let s2𝓤 := schlessingerConditionS2_of_isIsomorphismClasses
    𝓤 h𝓤.cofibered (schlessingerConditionS2_of_satisfiesRS hU.2) (Or.inl h𝓤)
  let s2𝓠 := schlessingerConditionS2_of_isIsomorphismClasses
    𝓠 h𝓠.cofibered
    (schlessingerConditionS2_of_satisfiesRS (quotient_satisfiesRS G hG hU.2 hR.2))
    (Or.inl h𝓠)
  letI : Fact (IsPredeformationCategory 𝓡.p) := ⟨h𝓡⟩
  letI : Fact (IsPredeformationCategory 𝓤.p) := ⟨h𝓤⟩
  letI : Fact (IsPredeformationCategory 𝓠.p) := ⟨h𝓠⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓡 h𝓡.cofibered))) := ⟨s2𝓡⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓤 h𝓤.cofibered))) := ⟨s2𝓤⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓠 h𝓠.cofibered))) := ⟨s2𝓠⟩
  let TR := artinianTangentSpace Λ k (isomorphismClasses 𝓡 h𝓡.cofibered)
  let TU := artinianTangentSpace Λ k (isomorphismClasses 𝓤 h𝓤.cofibered)
  let TQ := artinianTangentSpace Λ k (isomorphismClasses 𝓠 h𝓠.cofibered)
  let ds : TR →ₗ[k] TU := IsLinearMap.mk'
    (differential h𝓡.cofibered h𝓤.cofibered (elementsBasedFunctor G.source))
    (differential_isLinearMap 𝓡 𝓤 h𝓡 h𝓤 s2𝓡 s2𝓤 (elementsBasedFunctor G.source))
  let dt : TR →ₗ[k] TU := IsLinearMap.mk'
    (differential h𝓡.cofibered h𝓤.cofibered (elementsBasedFunctor G.target))
    (differential_isLinearMap 𝓡 𝓤 h𝓡 h𝓤 s2𝓡 s2𝓤 (elementsBasedFunctor G.target))
  let dq : TU →ₗ[k] TQ := IsLinearMap.mk'
    (differential h𝓤.cofibered h𝓠.cofibered
      (⟨quotientMorphism G, quotientMorphism_over G⟩ : BasedFunctor 𝓤 𝓠))
    (differential_isLinearMap 𝓤 𝓠 h𝓤 h𝓠 s2𝓤 s2𝓠
      (⟨quotientMorphism G, quotientMorphism_over G⟩ : BasedFunctor 𝓤 𝓠))
  let ε := augmentedDualNumbers (Λ := Λ) (k := k)
  have ds_class (r : G.arrows.obj ε) :
      ds (classOf 𝓡 h𝓡.cofibered (objectFiber ε r)) =
        classOf 𝓤 h𝓤.cofibered (objectFiber ε (G.source.app ε r)) := by
    exact mapIsomorphismClasses_classOf h𝓡.cofibered h𝓤.cofibered
      (elementsBasedFunctor G.source) (objectFiber ε r)
  have dt_class (r : G.arrows.obj ε) :
      dt (classOf 𝓡 h𝓡.cofibered (objectFiber ε r)) =
        classOf 𝓤 h𝓤.cofibered (objectFiber ε (G.target.app ε r)) := by
    exact mapIsomorphismClasses_classOf h𝓡.cofibered h𝓤.cofibered
      (elementsBasedFunctor G.target) (objectFiber ε r)
  have dq_class (x : G.objects.obj ε) :
      dq (classOf 𝓤 h𝓤.cofibered (objectFiber ε x)) =
        classOf 𝓠 h𝓠.cofibered (quotientFiberObject G ε x) := by
    exact mapIsomorphismClasses_classOf h𝓤.cofibered h𝓠.cofibered
      (⟨quotientMorphism G, quotientMorphism_over G⟩ : BasedFunctor 𝓤 𝓠)
      (objectFiber ε x)
  have quotient_classes_of_arrow {x y : G.objects.obj ε} (r : G.arrows.obj ε)
      (hs : G.source.app ε r = x) (ht : G.target.app ε r = y) :
      classOf 𝓠 h𝓠.cofibered (quotientFiberObject G ε x) =
        classOf 𝓠 h𝓠.cofibered (quotientFiberObject G ε y) := by
    apply (Equiv.cast (isomorphismClasses_obj 𝓠 h𝓠.cofibered ε)).injective
    calc
      _ = Quotient.mk (isIsomorphicSetoid (Functor.Fiber 𝓠.p ε))
          (quotientFiberObject G ε x) := by
            simpa using classOf_eq 𝓠 h𝓠.cofibered (quotientFiberObject G ε x)
      _ = Quotient.mk (isIsomorphicSetoid (Functor.Fiber 𝓠.p ε))
          (quotientFiberObject G ε y) :=
            Quotient.sound ⟨quotientFiberIsoOfArrow G ε r hs ht⟩
      _ = _ := by
            simpa using (classOf_eq 𝓠 h𝓠.cofibered
              (quotientFiberObject G ε y)).symm
  have object_representative (x : TU) :
      ∃ u : G.objects.obj ε, x = classOf 𝓤 h𝓤.cofibered (objectFiber ε u) := by
    obtain ⟨X, hX⟩ := classOf_surjective 𝓤 h𝓤.cofibered ε x
    obtain ⟨u, rfl⟩ := objectFiber_surjective ε X
    exact ⟨u, hX.symm⟩
  have arrow_representative (r : TR) :
      ∃ a : G.arrows.obj ε, r = classOf 𝓡 h𝓡.cofibered (objectFiber ε a) := by
    obtain ⟨X, hX⟩ := classOf_surjective 𝓡 h𝓡.cofibered ε r
    obtain ⟨a, rfl⟩ := objectFiber_surjective ε X
    exact ⟨a, hX.symm⟩
  have hExact : Function.Exact (ds - dt) dq := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      obtain ⟨u, hu⟩ := object_representative x
      obtain ⟨u₀, hu₀⟩ := object_representative (0 : TU)
      have hq : dq (classOf 𝓤 h𝓤.cofibered (objectFiber ε u)) =
          dq (classOf 𝓤 h𝓤.cofibered (objectFiber ε u₀)) := by
        rw [← hu, hx, ← hu₀, map_zero]
      have hq' :
          classOf 𝓠 h𝓠.cofibered (quotientFiberObject G ε u) =
            classOf 𝓠 h𝓠.cofibered (quotientFiberObject G ε u₀) := by
        rw [← dq_class u, hq, dq_class u₀]
      have hmk :
          Quotient.mk (isIsomorphicSetoid (Functor.Fiber 𝓠.p ε))
              (quotientFiberObject G ε u) =
            Quotient.mk (isIsomorphicSetoid (Functor.Fiber 𝓠.p ε))
              (quotientFiberObject G ε u₀) := by
        calc
          _ = cast (isomorphismClasses_obj 𝓠 h𝓠.cofibered ε)
              (classOf 𝓠 h𝓠.cofibered (quotientFiberObject G ε u)) :=
                (classOf_eq 𝓠 h𝓠.cofibered (quotientFiberObject G ε u)).symm
          _ = cast (isomorphismClasses_obj 𝓠 h𝓠.cofibered ε)
              (classOf 𝓠 h𝓠.cofibered (quotientFiberObject G ε u₀)) :=
                congrArg _ hq'
          _ = _ := classOf_eq 𝓠 h𝓠.cofibered (quotientFiberObject G ε u₀)
      obtain ⟨i⟩ := (Quotient.exact hmk : Nonempty
        (quotientFiberObject G ε u ≅ quotientFiberObject G ε u₀))
      let r := arrowOfQuotientFiberHom G ε (x := u) (y := u₀) i.hom
      refine LinearMap.mem_range.mpr ⟨classOf 𝓡 h𝓡.cofibered (objectFiber ε r.1), ?_⟩
      rw [LinearMap.sub_apply, ds_class r.1, dt_class r.1, r.2.1, r.2.2, ← hu, ← hu₀]
      simp
    · intro x hx
      rw [LinearMap.mem_ker]
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
      obtain ⟨a, ha⟩ := arrow_representative z
      rw [LinearMap.sub_apply, ha, map_sub, ds_class a, dt_class a,
        dq_class (G.source.app ε a), dq_class (G.target.app ε a)]
      rw [quotient_classes_of_arrow a rfl rfl]
      simp
  have hSurj : Function.Surjective dq := by
    intro y
    obtain ⟨X, hX⟩ := classOf_surjective 𝓠 h𝓠.cofibered ε y
    obtain ⟨x, rfl⟩ := quotientFiberObject_surjective G ε X
    exact ⟨classOf 𝓤 h𝓤.cofibered (objectFiber ε x), (dq_class x).trans hX⟩
  refine ⟨hExact.linearEquivOfSurjective hSurj, ?_⟩
  intro x
  change (hExact.linearEquivOfSurjective hSurj) (Submodule.Quotient.mk x) = dq x
  rw [Function.Exact.linearEquivOfSurjective_apply]
  exact Submodule.liftQ_apply _ _ x

end

end Deformation
