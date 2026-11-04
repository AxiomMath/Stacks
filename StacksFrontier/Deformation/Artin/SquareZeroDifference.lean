module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.LocalRing.Pullback
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.CategoryTheory.Functor.IsoFiber
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong

/-!
# Differences of lifts across a square-zero extension

Let `f : A' → A` be a surjection of commutative rings with square-zero kernel `I`. Two
elements of `A'` with the same image in `A` differ by an element of `I`, so the self-fibre
product `A' ×_A A'` is canonically isomorphic to the fibre product `A' ×_A A[I]` of `f`
with the projection of the trivial square-zero extension `A[I]`. That isomorphism is the
algebraic form of the statement that the lifts of an object across a square-zero thickening,
when there is one, form a torsor under the lifts across the trivial thickening.

This file records that isomorphism, both as a ring isomorphism and — once the two fibre
products are presented as affine objects of a big fppf site — as an isomorphism of objects
over the original thickening. It also specializes the Rim–Schlessinger comparison of
`Deformation.Artin.SatisfiesRSStar` to the iso-fibre over a fixed object, which is the form
in which (RS*) is used to compare lifts.

## Main definitions

* `Deformation.Artin.kerDifference` — the kernel-valued difference of two elements of the
  self-fibre product of a ring homomorphism.
* `Deformation.Artin.squareZeroDifferenceEquiv` — the ring isomorphism
  `A' ×_A A' ≅ A' ×_A A[I]` sending `(a₁, a₂)` to `(a₁, (f a₁, a₂ - a₁))`.
* `Deformation.Artin.squareZeroDifferenceOverIso` — the same isomorphism between two affine
  objects of the site presenting the two fibre products, as an isomorphism over the original
  thickening.

## Main results

* `Deformation.Artin.kerDifference_add` — differences telescope along a triple of elements
  with a common image.
* `Deformation.Artin.exists_squareZeroLiftEquivalence` — under (RS*), the lifts of an object
  across the pushout of a square-zero surjection are pairs of lifts across its two branches,
  by restriction along the two projections.
* `Deformation.Artin.exists_selfPullbackLiftEquivalence` — the self-fibre product case.
* `Deformation.Artin.exists_differenceTransportLiftEquivalence` — restriction along the
  difference isomorphism is an equivalence of the two categories of lifts it compares.

## Implementation notes

The square-zero kernel carries its canonical module structure over the quotient ring,
`Stacks.Smooth.kerModule`, and the trivial square-zero extension needs in addition the
induced right action and its centrality, which are supplied as local instances.

Lift categories are iso-fibres, `CategoryTheory.Functor.IsoFiber`, rather than strict
fibres of the pullback functors: a chosen pullback along a composite agrees with the
iterated chosen pullbacks only up to the canonical comparison isomorphism, so a strict
fibre would depend on the choice. The comparisons produced below are therefore stated with
the canonical comparison isomorphisms inserted, and the components of the resulting
equivalences are identified only up to `HEq`, since the two sides live over objects that are
equal rather than syntactically identical.

Affine objects of the site are presented by ring isomorphisms of their global sections;
compatibility of such a presentation with the maps to the original thickening is what makes
the difference isomorphism an isomorphism over that thickening, and hence over the base
scheme. The hypothesis `hκS` of `Deformation.Artin.squareZeroDifferenceOverIso` records the
remaining compatibility with the structure morphisms to the base, which cannot be deduced
from the global-section data alone.

## References

* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped RightActions

namespace Deformation.Artin

/-- The induced right action of the quotient ring on a square-zero kernel. -/
local instance kerModuleOpposite {R' R : Type*} [CommRing R'] [CommRing R] (f : R' →+* R)
    [Module R (RingHom.ker f)] : Module Rᵐᵒᵖ (RingHom.ker f) :=
  Module.oppositeOfCommSemiring R (RingHom.ker f)

/-- The canonical action of the quotient ring on a square-zero kernel is central. -/
local instance kerIsCentralScalar {R' R : Type*} [CommRing R'] [CommRing R] (f : R' →+* R)
    [Module R (RingHom.ker f)] : IsCentralScalar R (RingHom.ker f) :=
  Module.isCentralScalar_oppositeOfCommSemiring R (RingHom.ker f)

/-! ### The difference of two lifts of an element -/

section Algebra

universe u

variable {A' A : Type u} [CommRing A'] [CommRing A]

/-- The kernel-valued difference `a₂ - a₁` of a point `(a₁, a₂)` of the self-fibre product
of `f`. -/
public def kerDifference (f : A' →+* A) (x : f.pullback f) : RingHom.ker f :=
  ⟨x.1.2 - x.1.1, by
    have hx : f x.1.1 = f x.1.2 := x.2
    change f (x.1.2 - x.1.1) = 0
    rw [map_sub, ← hx, sub_self]⟩

/-- Differences telescope along a triple of elements with a common image. -/
public theorem kerDifference_add (f : A' →+* A) (a₁ a₂ a₃ : A')
    (h₁₂ : f a₁ = f a₂) (h₂₃ : f a₂ = f a₃) :
    kerDifference f ⟨(a₁, a₃), h₁₂.trans h₂₃⟩ =
      kerDifference f ⟨(a₁, a₂), h₁₂⟩ + kerDifference f ⟨(a₂, a₃), h₂₃⟩ := by
  apply Subtype.ext
  simp [kerDifference]

/-- A square-zero kernel is annihilated by itself. -/
private theorem ker_mul_ker_eq_zero (f : A' →+* A) (hsq : RingHom.ker f ^ 2 = ⊥)
    (x y : RingHom.ker f) : (x : A') * (y : A') = 0 := by
  have hxy : (x : A') * (y : A') ∈ RingHom.ker f ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul x.2 y.2
  rw [hsq] at hxy
  exact Ideal.mem_bot.mp hxy

/-- Multiplication by any lift computes the canonical action of the quotient ring on a
square-zero kernel, elementwise. -/
private theorem kerModule_smul_val (f : A' →+* A) (hf : Function.Surjective f)
    (hsq : RingHom.ker f ^ 2 = ⊥) (a : A') (i : RingHom.ker f) :
    letI := Stacks.Smooth.kerModule hf hsq
    ((f a • i : RingHom.ker f) : A') = a * (i : A') := by
  let := Stacks.Smooth.kerModule hf hsq
  rw [Stacks.Smooth.kerModule_smul hf hsq a i]
  rfl

/-- **The difference isomorphism of a square-zero surjection.** The self-fibre product of a
surjection with square-zero kernel `I` is isomorphic to its fibre product with the trivial
square-zero extension `A[I]`, by `(a₁, a₂) ↦ (a₁, (f a₁, a₂ - a₁))`. The isomorphism
commutes with the first projection. -/
public noncomputable def squareZeroDifferenceEquiv (f : A' →+* A)
    (hf : Function.Surjective f) (hsq : RingHom.ker f ^ 2 = ⊥) :
    letI := Stacks.Smooth.kerModule hf hsq
    { e : f.pullback f ≃+*
        f.pullback (TrivSqZeroExt.fstHom A A (RingHom.ker f)).toRingHom //
      ∀ x, (e x).1.1 = x.1.1 ∧
        (e x).1.2 =
          ((f x.1.1, kerDifference f x) : TrivSqZeroExt A (RingHom.ker f)) } := by
  letI := Stacks.Smooth.kerModule hf hsq
  let φ : f.pullback f →+*
      f.pullback (TrivSqZeroExt.fstHom A A (RingHom.ker f)).toRingHom :=
    { toFun x := ⟨(x.1.1, (f x.1.1, kerDifference f x)), rfl⟩
      map_one' := by
        apply Subtype.ext
        refine Prod.ext (by simp) (TrivSqZeroExt.ext ?_ ?_) <;> simp [kerDifference]
      map_mul' x y := by
        apply Subtype.ext
        refine Prod.ext rfl (TrivSqZeroExt.ext (map_mul f _ _) ?_)
        have hi : ((f x.1.1 •> kerDifference f y : RingHom.ker f) : A') =
            x.1.1 * (kerDifference f y : A') :=
          kerModule_smul_val f hf hsq x.1.1 (kerDifference f y)
        have hj : ((kerDifference f x <• f y.1.1 : RingHom.ker f) : A') =
            (kerDifference f x : A') * y.1.1 := by
          rw [op_smul_eq_smul, kerModule_smul_val f hf hsq y.1.1 (kerDifference f x)]
          exact mul_comm _ _
        have hxy : (kerDifference f x : A') * (kerDifference f y : A') = 0 :=
          ker_mul_ker_eq_zero f hsq _ _
        have hx : x.1.2 = x.1.1 + (kerDifference f x : A') := by
          simp [kerDifference]
        have hy : y.1.2 = y.1.1 + (kerDifference f y : A') := by
          simp [kerDifference]
        apply Subtype.ext
        change x.1.2 * y.1.2 - x.1.1 * y.1.1 =
          ((f x.1.1 •> kerDifference f y : RingHom.ker f) : A') +
            ((kerDifference f x <• f y.1.1 : RingHom.ker f) : A')
        rw [hx, hy, hi, hj]
        calc
          (x.1.1 + (kerDifference f x : A')) * (y.1.1 + (kerDifference f y : A')) -
                x.1.1 * y.1.1 =
              x.1.1 * (kerDifference f y : A') + (kerDifference f x : A') * y.1.1 +
                (kerDifference f x : A') * (kerDifference f y : A') := by ring
          _ = x.1.1 * (kerDifference f y : A') + (kerDifference f x : A') * y.1.1 := by
              rw [hxy, add_zero]
      map_zero' := by
        apply Subtype.ext
        refine Prod.ext (by simp) (TrivSqZeroExt.ext ?_ ?_) <;> simp [kerDifference]
      map_add' x y := by
        apply Subtype.ext
        refine Prod.ext rfl (TrivSqZeroExt.ext (map_add f _ _) (Subtype.ext ?_))
        change x.1.2 + y.1.2 - (x.1.1 + y.1.1) =
          ((kerDifference f x + kerDifference f y : RingHom.ker f) : A')
        simp only [AddMemClass.coe_add, kerDifference]
        ring }
  let ψ : f.pullback (TrivSqZeroExt.fstHom A A (RingHom.ker f)).toRingHom →
      f.pullback f := fun y => ⟨(y.1.1, y.1.1 + (y.1.2.2 : A')), by
    change f y.1.1 = f (y.1.1 + (y.1.2.2 : A'))
    rw [map_add, RingHom.mem_ker.mp y.1.2.2.2, add_zero]⟩
  have hleft : ∀ x, ψ (φ x) = x := by
    intro x
    refine Subtype.ext (Prod.ext rfl ?_)
    change x.1.1 + (x.1.2 - x.1.1) = x.1.2
    ring
  have hright : ∀ y, φ (ψ y) = y := by
    intro y
    refine Subtype.ext (Prod.ext rfl (TrivSqZeroExt.ext y.2 (Subtype.ext ?_)))
    change y.1.1 + (y.1.2.2 : A') - y.1.1 = (y.1.2.2 : A')
    ring
  refine ⟨RingEquiv.ofBijective φ
    ⟨fun x y hxy => (hleft x).symm.trans ((congrArg ψ hxy).trans (hleft y)),
      fun y => ⟨ψ y, hright y⟩⟩, fun x => ⟨rfl, rfl⟩⟩

end Algebra

/-! ### Comparison of lifts under the Rim–Schlessinger condition -/

section Lifts

open Functor

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : Type w} [Category X] {p : X ⥤ BigFppfOver B S hS}

/-- **The Rim–Schlessinger comparison in the iso-fibre.** Under (RS*), restriction along the
two projections identifies the lifts of a fixed object across the pushout of a square-zero
surjection with pairs of lifts across its two branches. -/
public theorem exists_squareZeroLiftEquivalence
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
    (U V W Z : BigAffineFppf B S hS)
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    (hpb : IsPullback ((BigAffineFppf.toScheme B S hS).map i).appTop
      ((BigAffineFppf.toScheme B S hS).map j).appTop
      ((BigAffineFppf.toScheme B S hS).map f).appTop
      ((BigAffineFppf.toScheme B S hS).map g).appTop)
    (hsurj : Function.Surjective
      (((BigAffineFppf.toScheme B S hS).map g).appTop.hom))
    (hsq : RingHom.ker (((BigAffineFppf.toScheme B S hS).map g).appTop.hom) ^ 2 = ⊥) :
    letI : p.IsFibered := hp.isFibered
    let c := Functor.chosenPullbacks p
    let ι := BigAffineFppf.inclusion B S hS
    ∀ x : p.Fiber (ι.obj U),
      ∃ E : IsoFiber (c.pullbackFunctor (ι.map (f ≫ i))) x ≌
          (IsoFiber (c.pullbackFunctor (ι.map f)) x ×
            IsoFiber (c.pullbackFunctor (ι.map g)) x),
        (∀ t,
          ((E.functor.obj t).1).1.left = (c.pullbackFunctor (ι.map i)).obj t.1.left ∧
          ((E.functor.obj t).2).1.left = (c.pullbackFunctor (ι.map j)).obj t.1.left) ∧
        (∀ t t' (m : t ⟶ t'),
          HEq ((E.functor.map m).1.1.left)
            ((c.pullbackFunctor (ι.map i)).map m.1.left) ∧
          HEq ((E.functor.map m).2.1.left)
            ((c.pullbackFunctor (ι.map j)).map m.1.left)) ∧
        (∀ t,
          HEq ((E.functor.obj t).1).1.hom
            (((c.pullbackFunctorCompIso (ι.map f) (ι.map i)).symm.app t.1.left).hom ≫
              t.1.hom) ∧
          HEq ((E.functor.obj t).2).1.hom
            (((c.pullbackFunctorCompIso (ι.map g) (ι.map j)).symm.app t.1.left).hom ≫
              eqToHom (congrArg (fun k => (c.pullbackFunctor k).obj t.1.left)
                (show ι.map g ≫ ι.map j = ι.map (f ≫ i) from by
                  simpa only [Functor.map_comp] using congrArg ι.map h.symm)) ≫
              t.1.hom)) := by
  let : p.IsFibered := hp.isFibered
  intro c ι x
  let F := c.pullbackFunctor (ι.map f)
  let G := c.pullbackFunctor (ι.map g)
  let L := c.pullbackFunctor (ι.map (f ≫ i))
  let E₀ := fiberSquareComparison p c (ι.map f) (ι.map g) (ι.map i) (ι.map j)
    (by simpa only [Functor.map_comp] using congrArg ι.map h)
  let : E₀.IsEquivalence := hRS U V W Z f g i j h hpb hsurj hsq
  let P := categoricalPullbackFst F G
  have hmap : ι.map f ≫ ι.map i = ι.map (f ≫ i) := ι.map_comp f i
  let α : E₀ ⋙ P ≅ L ⋙ 𝟭 _ :=
    (c.pullbackFunctorCompIso (ι.map f) (ι.map i)).symm ≪≫
      eqToIso (congrArg c.pullbackFunctor hmap) ≪≫ L.rightUnitor.symm
  let : IsIso α.hom := α.isIso_hom
  let : IsIso (𝟙 x) := inferInstance
  let A₀ : CostructuredArrow L x ⥤ CostructuredArrow P x :=
    CostructuredArrow.map₂ (S := L) (T := x) (U := P) (V := x)
      (F := E₀) (G := 𝟭 _) α.hom (𝟙 x)
  let : A₀.IsEquivalence := by
    change (CostructuredArrow.map₂ α.hom (𝟙 x)).IsEquivalence
    infer_instance
  let : IsGroupoid (p.Fiber (ι.obj U)) := hp.fiber_isGroupoid (ι.obj U)
  have hA₀ : (IsIsoCostructuredArrow P x).inverseImage A₀.asEquivalence.functor =
      IsIsoCostructuredArrow L x := by
    ext t
    change IsIso (A₀.obj t).hom ↔ IsIso t.hom
    exact ⟨fun _ => IsGroupoid.all_isIso _, fun _ => IsGroupoid.all_isIso _⟩
  let Q := costructuredArrowCategoricalPullbackEquiv F G x (hp.fiber_isGroupoid (ι.obj U))
  have hQ : (IsIsoCostructuredArrowPair F G x).inverseImage Q.functor =
      IsIsoCostructuredArrow P x := by
    ext t
    change (IsIso (Q.functor.obj t).1.hom ∧ IsIso (Q.functor.obj t).2.hom) ↔ IsIso t.hom
    refine ⟨fun _ => inferInstance, fun _ => ⟨inferInstance, inferInstance⟩⟩
  refine ⟨(A₀.asEquivalence.congrFullSubcategory hA₀).trans
    ((Q.congrFullSubcategory (by simpa only [Q] using hQ)).trans
      (isoFiberProdEquivalence F G x)), ?_, ?_, ?_⟩
  · intro t
    exact ⟨rfl, rfl⟩
  · intro t t' m
    exact ⟨HEq.rfl, HEq.rfl⟩
  · intro t
    refine ⟨?_, ?_⟩
    · change HEq ((Q.functor.obj (A₀.obj t.obj)).1.hom) _
      simp only [Q, A₀, costructuredArrowCategoricalPullbackEquiv_functor_obj_fst_hom,
        CostructuredArrow.map₂_obj_hom]
      refine heq_of_eq ?_
      simp only [α, L, eqToIso_refl, Iso.refl_trans, id_obj, Functor.id_map, Category.comp_id,
        comp_obj, Iso.app_hom, Iso.symm_hom]
      exact congrArg (· ≫ t.obj.hom) (Category.comp_id _)
    · change HEq ((Q.functor.obj (A₀.obj t.obj)).2.hom) _
      simp only [Q, A₀, costructuredArrowCategoricalPullbackEquiv_functor_obj_snd_hom,
        CostructuredArrow.map₂_obj_hom]
      refine heq_of_eq ?_
      simp only [α, L, E₀, fiberSquareComparison,
        CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback,
        CostructuredArrow.map₂_obj_left]
      cat_disch

/-- For a self-fibre product of a square-zero surjection, restriction along the two
projections identifies its lifts with two lifts across the original surjection. -/
public theorem exists_selfPullbackLiftEquivalence
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
    (U V Z : BigAffineFppf B S hS)
    (r : U ⟶ V) (q₁ q₂ : V ⟶ Z) (h : r ≫ q₁ = r ≫ q₂)
    (hpb : IsPullback ((BigAffineFppf.toScheme B S hS).map q₁).appTop
      ((BigAffineFppf.toScheme B S hS).map q₂).appTop
      ((BigAffineFppf.toScheme B S hS).map r).appTop
      ((BigAffineFppf.toScheme B S hS).map r).appTop)
    (hsurj : Function.Surjective
      (((BigAffineFppf.toScheme B S hS).map r).appTop.hom))
    (hsq : RingHom.ker (((BigAffineFppf.toScheme B S hS).map r).appTop.hom) ^ 2 = ⊥) :
    letI : p.IsFibered := hp.isFibered
    let c := Functor.chosenPullbacks p
    let ι := BigAffineFppf.inclusion B S hS
    ∀ x : p.Fiber (ι.obj U),
      ∃ E : IsoFiber (c.pullbackFunctor (ι.map (r ≫ q₁))) x ≌
          (IsoFiber (c.pullbackFunctor (ι.map r)) x ×
            IsoFiber (c.pullbackFunctor (ι.map r)) x),
        (∀ t,
          ((E.functor.obj t).1).1.left = (c.pullbackFunctor (ι.map q₁)).obj t.1.left ∧
          ((E.functor.obj t).2).1.left = (c.pullbackFunctor (ι.map q₂)).obj t.1.left) ∧
        (∀ t t' (m : t ⟶ t'),
          HEq ((E.functor.map m).1.1.left)
            ((c.pullbackFunctor (ι.map q₁)).map m.1.left) ∧
          HEq ((E.functor.map m).2.1.left)
            ((c.pullbackFunctor (ι.map q₂)).map m.1.left)) ∧
        (∀ t,
          HEq ((E.functor.obj t).1).1.hom
            (((c.pullbackFunctorCompIso (ι.map r) (ι.map q₁)).symm.app t.1.left).hom ≫
              t.1.hom) ∧
          HEq ((E.functor.obj t).2).1.hom
            (((c.pullbackFunctorCompIso (ι.map r) (ι.map q₂)).symm.app t.1.left).hom ≫
              eqToHom (congrArg (fun k => (c.pullbackFunctor k).obj t.1.left)
                (show ι.map r ≫ ι.map q₂ = ι.map (r ≫ q₁) from by
                  simpa only [Functor.map_comp] using congrArg ι.map h.symm)) ≫
              t.1.hom)) :=
  exists_squareZeroLiftEquivalence hp hRS U V V Z r r q₁ q₂ h hpb hsurj hsq

end Lifts

/-! ### The difference isomorphism of affine objects over a thickening -/

section Over

universe u

variable {A' A : Type u} [CommRing A'] [CommRing A]

/-- An isomorphism of the global sections of two affine schemes induces an isomorphism of
the schemes in the opposite direction. -/
public noncomputable def isoOfGlobalSectionsEquiv {Y Z : Scheme.{u}} [IsAffine Y]
    [IsAffine Z] (e : Γ(Y, (⊤ : Y.Opens)) ≃+* Γ(Z, (⊤ : Z.Opens))) : Z ≅ Y :=
  Z.isoSpec ≪≫ Scheme.Spec.mapIso e.toCommRingCatIso.op ≪≫ Y.isoSpec.symm

/-- The isomorphism of affine schemes induced by an isomorphism of global sections realizes
that isomorphism on global sections. -/
public theorem isoOfGlobalSectionsEquiv_hom_appTop {Y Z : Scheme.{u}} [IsAffine Y]
    [IsAffine Z] (e : Γ(Y, (⊤ : Y.Opens)) ≃+* Γ(Z, (⊤ : Z.Opens))) :
    (isoOfGlobalSectionsEquiv e).hom.appTop.hom = e.toRingHom := by
  have hm : Spec.map (isoOfGlobalSectionsEquiv e).hom.appTop =
      Spec.map (CommRingCat.ofHom e.toRingHom) := by
    apply (cancel_epi Z.isoSpec.hom).1
    calc
      Z.isoSpec.hom ≫ Spec.map (isoOfGlobalSectionsEquiv e).hom.appTop =
          (isoOfGlobalSectionsEquiv e).hom ≫ Y.isoSpec.hom :=
        Scheme.isoSpec_hom_naturality _
      _ = Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.toRingHom) := by
        simp [isoOfGlobalSectionsEquiv]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hm)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The difference isomorphism as an isomorphism over the thickening.** Two affine objects
of the site presenting the self-fibre product of a square-zero surjection and its fibre
product with the trivial square-zero extension are isomorphic over the thickening, by the
difference isomorphism of global sections. -/
public noncomputable def squareZeroDifferenceOverIso
    (U U₁ U₂ : BigAffineFppf B S hS) (q₁ : U ⟶ U₁) (q₂ : U ⟶ U₂)
    (f : A' →+* A) (hf : Function.Surjective f) (hsq : RingHom.ker f ^ 2 = ⊥)
    (κU : Γ((BigAffineFppf.toScheme B S hS).obj U, ⊤) ≃+* A')
    (κ₁ : Γ((BigAffineFppf.toScheme B S hS).obj U₁, ⊤) ≃+* f.pullback f)
    (κ₂ : letI := Stacks.Smooth.kerModule hf hsq
      Γ((BigAffineFppf.toScheme B S hS).obj U₂, ⊤) ≃+*
        f.pullback (TrivSqZeroExt.fstHom A A (RingHom.ker f)).toRingHom)
    (hκ₁ : ∀ a, κU (((BigAffineFppf.toScheme B S hS).map q₁).appTop.hom a) = (κ₁ a).1.1)
    (hκ₂ : ∀ a, κU (((BigAffineFppf.toScheme B S hS).map q₂).appTop.hom a) = (κ₂ a).1.1)
    (hκS : letI := Stacks.Smooth.kerModule hf hsq
      let T := BigAffineFppf.toScheme B S hS
      let e := κ₁.trans ((squareZeroDifferenceEquiv f hf hsq).val.trans κ₂.symm)
      (T.obj U₂).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        (T.obj U₁).isoSpec.inv ≫ B.inclusion.map U₁.obj.hom =
          B.inclusion.map U₂.obj.hom) :
    { e : U₂ ≅ U₁ // q₂ ≫ e.hom = q₁ ∧
        ∀ a, κ₂ (((BigAffineFppf.toScheme B S hS).map e.hom).appTop.hom a) =
          (squareZeroDifferenceEquiv f hf hsq).val (κ₁ a) } := by
  letI := Stacks.Smooth.kerModule hf hsq
  let T := BigAffineFppf.toScheme B S hS
  let ringEquiv := κ₁.trans ((squareZeroDifferenceEquiv f hf hsq).val.trans κ₂.symm)
  let αIso := isoOfGlobalSectionsEquiv ringEquiv
  let α := αIso.hom
  have hαApp : α.appTop.hom = ringEquiv.toRingHom :=
    isoOfGlobalSectionsEquiv_hom_appTop ringEquiv
  have hringEquiv (a) : κ₂ (ringEquiv a) =
      (squareZeroDifferenceEquiv f hf hsq).val (κ₁ a) := by
    change κ₂ (κ₂.symm ((squareZeroDifferenceEquiv f hf hsq).val (κ₁ a))) = _
    exact RingEquiv.apply_symm_apply _ _
  have hbase : α ≫ B.inclusion.map U₁.obj.hom = B.inclusion.map U₂.obj.hom := by
    change (T.obj U₂).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ringEquiv.toRingHom) ≫
      (T.obj U₁).isoSpec.inv ≫ B.inclusion.map U₁.obj.hom = B.inclusion.map U₂.obj.hom
    exact hκS
  let α' : U₂.obj.left ≅ U₁.obj.left := B.inclusion.preimageIso αIso
  have hα'map : B.inclusion.map α'.hom = α := by
    simp only [α', α, Functor.preimageIso_hom, Functor.map_preimage]
  have hbase' : α'.hom ≫ U₁.obj.hom = U₂.obj.hom := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hα'map]
    exact hbase
  let e : U₂ ≅ U₁ := Functor.preimageIso
    (F := BigAffineFppf.inclusion B S hS) (Over.isoMk α' hbase')
  have hEmap : T.map e.hom = α := by
    change B.inclusion.map ((BigFppfOver.forget B S hS).map
      ((BigAffineFppf.inclusion B S hS).map e.hom)) = α
    simp only [e, Functor.preimageIso_hom, Functor.map_preimage, Over.forget_map,
      Over.isoMk_hom_left]
    exact hα'map
  have hring (a) : (T.map q₂).appTop.hom (ringEquiv a) = (T.map q₁).appTop.hom a := by
    apply κU.injective
    calc
      κU ((T.map q₂).appTop.hom (ringEquiv a)) = (κ₂ (ringEquiv a)).1.1 := hκ₂ _
      _ = (κ₁ a).1.1 := by
        rw [hringEquiv a]
        exact ((squareZeroDifferenceEquiv f hf hsq).property (κ₁ a)).1
      _ = κU ((T.map q₁).appTop.hom a) := (hκ₁ a).symm
  have happ : (T.map (q₂ ≫ e.hom)).appTop = (T.map q₁).appTop := by
    ext a
    simp only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rw [hEmap, hαApp]
    exact hring a
  refine ⟨e, Functor.map_injective T (ext_of_isAffine happ), fun a => ?_⟩
  rw [hEmap, hαApp]
  exact hringEquiv a

/-- Restriction along the difference isomorphism is an equivalence between the lifts across
the two fibre products it compares. -/
public theorem exists_differenceTransportLiftEquivalence
    {X : Type*} [Category X] (p : X ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (D U U₁ U₂ : BigAffineFppf B S hS) (d : D ⟶ U) (q₁ : U ⟶ U₁) (q₂ : U ⟶ U₂)
    (f : A' →+* A) (hf : Function.Surjective f) (hsq : RingHom.ker f ^ 2 = ⊥)
    (κU : Γ((BigAffineFppf.toScheme B S hS).obj U, ⊤) ≃+* A')
    (κ₁ : Γ((BigAffineFppf.toScheme B S hS).obj U₁, ⊤) ≃+* f.pullback f)
    (κ₂ : letI := Stacks.Smooth.kerModule hf hsq
      Γ((BigAffineFppf.toScheme B S hS).obj U₂, ⊤) ≃+*
        f.pullback (TrivSqZeroExt.fstHom A A (RingHom.ker f)).toRingHom)
    (hκ₁ : ∀ a, κU (((BigAffineFppf.toScheme B S hS).map q₁).appTop.hom a) = (κ₁ a).1.1)
    (hκ₂ : ∀ a, κU (((BigAffineFppf.toScheme B S hS).map q₂).appTop.hom a) = (κ₂ a).1.1)
    (hκS : letI := Stacks.Smooth.kerModule hf hsq
      let T := BigAffineFppf.toScheme B S hS
      let e := κ₁.trans ((squareZeroDifferenceEquiv f hf hsq).val.trans κ₂.symm)
      (T.obj U₂).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        (T.obj U₁).isoSpec.inv ≫ B.inclusion.map U₁.obj.hom =
          B.inclusion.map U₂.obj.hom) :
    letI : p.IsFibered := hp.isFibered
    let c := Functor.chosenPullbacks p
    let ι := BigAffineFppf.inclusion B S hS
    let e := (squareZeroDifferenceOverIso U U₁ U₂ q₁ q₂ f hf hsq κU κ₁ κ₂ hκ₁ hκ₂ hκS).val
    let he : q₂ ≫ e.hom = q₁ :=
      (squareZeroDifferenceOverIso U U₁ U₂ q₁ q₂ f hf hsq κU κ₁ κ₂ hκ₁ hκ₂ hκS).property.1
    ∀ x : p.Fiber (ι.obj D),
      ∃ E : Functor.IsoFiber (c.pullbackFunctor (ι.map (d ≫ q₁))) x ≌
          Functor.IsoFiber (c.pullbackFunctor (ι.map (d ≫ q₂))) x,
        (∀ t, (E.functor.obj t).1.left = (c.pullbackFunctor (ι.map e.hom)).obj t.1.left) ∧
        (∀ t t' (m : t ⟶ t'),
          HEq (E.functor.map m).1.left
            ((c.pullbackFunctor (ι.map e.hom)).map m.1.left)) ∧
        (∀ t,
          HEq (E.functor.obj t).1.hom
            (((c.pullbackFunctorCompIso (ι.map (d ≫ q₂)) (ι.map e.hom)).symm.app
              t.1.left).hom ≫
              eqToHom (congrArg (fun k => (c.pullbackFunctor k).obj t.1.left)
                (show ι.map (d ≫ q₂) ≫ ι.map e.hom = ι.map (d ≫ q₁) from by
                  simpa only [Functor.map_comp] using
                    congrArg ι.map (show (d ≫ q₂) ≫ e.hom = d ≫ q₁ from by
                      rw [Category.assoc, he]))) ≫
              t.1.hom)) := by
  let : p.IsFibered := hp.isFibered
  intro c ι e he x
  let e' := ι.map e.hom
  let F := c.pullbackFunctor e'
  let FInv := c.pullbackFunctor (ι.map e.inv)
  let H₁ := c.pullbackFunctor (ι.map (d ≫ q₁))
  let H₂ := c.pullbackFunctor (ι.map (d ≫ q₂))
  have h₁ : ι.map e.inv ≫ e' = 𝟙 (ι.obj U₁) := by
    rw [← ι.map_comp, e.inv_hom_id, ι.map_id]
  have h₂ : e' ≫ ι.map e.inv = 𝟙 (ι.obj U₂) := by
    rw [← ι.map_comp, e.hom_inv_id, ι.map_id]
  let : F.IsEquivalence := Functor.IsEquivalence.mk' FInv
    ((c.pullbackFunctorIdIso (ι.obj U₁)).symm ≪≫
      (eqToIso (congrArg c.pullbackFunctor h₁)).symm ≪≫
        c.pullbackFunctorCompIso (ι.map e.inv) e')
    (((c.pullbackFunctorIdIso (ι.obj U₂)).symm ≪≫
      (eqToIso (congrArg c.pullbackFunctor h₂)).symm ≪≫
        c.pullbackFunctorCompIso e' (ι.map e.inv)).symm)
  have hcomp : ι.map (d ≫ q₂) ≫ e' = ι.map (d ≫ q₁) := by
    rw [← ι.map_comp, Category.assoc, he]
  let α : F ⋙ H₂ ≅ H₁ ⋙ 𝟭 _ :=
    (c.pullbackFunctorCompIso (ι.map (d ≫ q₂)) e').symm ≪≫
      eqToIso (congrArg c.pullbackFunctor hcomp) ≪≫ H₁.rightUnitor.symm
  let : IsIso α.hom := α.isIso_hom
  let : IsIso (𝟙 x) := inferInstance
  let A₀ : CostructuredArrow H₁ x ⥤ CostructuredArrow H₂ x :=
    CostructuredArrow.map₂ (S := H₁) (T := x) (U := H₂) (V := x)
      (F := F) (G := 𝟭 _) α.hom (𝟙 x)
  let : A₀.IsEquivalence := by
    change (CostructuredArrow.map₂ α.hom (𝟙 x)).IsEquivalence
    infer_instance
  let : IsGroupoid (p.Fiber (ι.obj D)) := hp.fiber_isGroupoid (ι.obj D)
  refine ⟨A₀.asEquivalence.congrFullSubcategory (by
    ext t
    change IsIso (A₀.obj t).hom ↔ IsIso t.hom
    exact ⟨fun _ => IsGroupoid.all_isIso _, fun _ => IsGroupoid.all_isIso _⟩),
    fun t => rfl, fun t t' m => HEq.rfl, fun t => ?_⟩
  change HEq ((A₀.asEquivalence.congrFullSubcategory _).functor.obj t).1.hom
    (((c.pullbackFunctorCompIso (ι.map (d ≫ q₂)) e').symm.app t.1.left).hom ≫
      eqToHom (congrArg (fun k => (c.pullbackFunctor k).obj t.1.left) hcomp) ≫ t.1.hom)
  dsimp [Equivalence.congrFullSubcategory, A₀, CostructuredArrow.map₂,
    Functor.asEquivalence]
  change HEq (α.hom.app t.1.left ≫ (𝟭 _).map t.1.hom ≫ 𝟙 x) _
  simp [α, H₁]

end Over

end Deformation.Artin
