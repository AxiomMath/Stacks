module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.DerivationOrbits
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.LiftsOfObjects.Smoothness.TangentIsomorphism
public import StacksFrontier.Deformation.PredeformationTangent.DerivationMap
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.RimSchlessingerCategory.Prorepresentable
public import StacksFrontier.Deformation.Schlessinger.MiniversalExistence
public import StacksFrontier.Deformation.TangentSpace.Derivations
public import StacksFrontier.Deformation.TangentSpace.Predeformation
import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
import StacksFrontier.Deformation.Predeformation.Basic
import StacksFrontier.Deformation.Smooth.IsomorphismClasses
import StacksFrontier.Deformation.TangentSpace.SquareZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Schlessinger's prorepresentability criterion

A set-valued functor on the category `𝒞_Λ` of Artinian local `Λ`-algebras with residue field
`k` is prorepresentable exactly when it is a deformation functor, its tangent space is a
finite-dimensional `k`-vector space, and the canonical map `Der_Λ(k, k) → TF` is injective.

## Main results

* `Deformation.isProrepresentableULift_iff_isDeformationFunctor`: Schlessinger's criterion for a
  functor whose values lie in a universe unrelated to the morphism universe of `𝒞_Λ`.
* `Deformation.isProrepresentable_iff_isDeformationFunctor`: Schlessinger's criterion.

## Implementation notes

The tangent space is that of the functor of fibrewise isomorphism classes of the category of
elements of `F`; the deformation-functor hypothesis supplies its canonical `k`-vector space
structure through the Rim–Schlessinger condition, which is why the two finiteness and
injectivity clauses are stated under a binder for that hypothesis.

The isomorphism criterion for a smooth morphism of deformation functors is available only when
the carriers of the Artinian algebras live in the universe of the residue field, so the final
step compares `F` with the restricted representable functor of the base of the versal object
after transporting both along the equivalence of `𝒞_Λ` over `k` with `𝒞_Λ` over `ULift k`.

Two pairs of descriptions of one object occur throughout and are reconciled by making the
relevant definitions reducible for this file. A fibre of the category of elements of `F` is
described both as a fibre of `CategoryTheory.BasedCategory.ofFunctor` of its projection and as a
subtype of dependent pairs, and the square-zero object of `𝒞_Λ` attached to a module `V` is
described both through `Deformation.squareZeroExtensionArtinian` and as the trivial square-zero
extension `TrivSqZeroExt k V` whose first and second coordinates the computations use.

## References

* [Stacks Project, Tag 06JM](https://stacks.math.columbia.edu/tag/06JM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Deformation

universe u v w x y

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
set_option linter.deprecated false in
attribute [local implicit_reducible] CategoryTheory.CategoryOfElements.π
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
attribute [local implicit_reducible] squareZeroExtensionArtinian


/-- Condition (RS) transfers along a natural bijection of set-valued functors. -/
private theorem satisfiesRS_of_equiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type x}
    {G : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type y}
    (e : ∀ A, F.obj A ≃ G.obj A)
    (he : ∀ {A B} (f : A ⟶ B) (a : F.obj A),
      e B (F.map f a) = G.map f (e A a))
    (hG : SatisfiesRS (CategoryOfElements.π G)) :
    SatisfiesRS (CategoryOfElements.π F) := by
  refine ⟨categoryOfElements_projection_isCofibered _, ?_⟩
  intro x₁ x₂ x f₁ f₂ hf₂
  let toG (z : F.Elements) : G.Elements := G.elementsMk z.1 (e z.1 z.2)
  let mapG {z w : F.Elements} (m : z ⟶ w) : toG z ⟶ toG w :=
    Functor.Elements.homMk m.hom (by
      calc
        G.map m.hom (e z.1 z.2) = e w.1 (F.map m.hom z.2) := (he m.hom z.2).symm
        _ = e w.1 w.2 := by rw [m.map_val])
  let f₁G := mapG f₁
  let f₂G := mapG f₂
  have hf₂G : Function.Surjective ((CategoryOfElements.π G).map f₂G).hom := by
    simpa [f₂G, mapG, toG, CategoryOfElements.π] using hf₂
  obtain ⟨cG, ⟨hcG⟩, ⟨hcpG⟩⟩ := hG.2 f₁G f₂G hf₂G
  let y : F.Elements := F.elementsMk cG.pt.1 ((e cG.pt.1).symm cG.pt.2)
  have hy (z : F.Elements) (m : cG.pt ⟶ toG z) : F.map m.hom y.2 = z.2 := by
    apply (e z.1).injective
    calc
      e z.1 (F.map m.hom y.2) = G.map m.hom (e cG.pt.1 y.2) := he m.hom y.2
      _ = G.map m.hom cG.pt.2 := by simp [y]
      _ = e z.1 z.2 := m.map_val
  let m₁ : y ⟶ x₁ := Functor.Elements.homMk cG.fst.hom (hy x₁ cG.fst)
  let m₂ : y ⟶ x₂ := Functor.Elements.homMk cG.snd.hom (hy x₂ cG.snd)
  let c : PullbackCone f₁ f₂ := PullbackCone.mk m₁ m₂ (by
    apply Functor.Elements.hom_ext
    exact congrArg (fun q : cG.pt ⟶ toG x => q.hom) cG.condition)
  let sG (s : PullbackCone f₁ f₂) : PullbackCone f₁G f₂G :=
    PullbackCone.mk (mapG s.fst) (mapG s.snd)
      (by
        apply Functor.Elements.hom_ext
        exact congrArg (fun q : s.pt ⟶ x => q.hom) s.condition)
  let baseLift (s : PullbackCone f₁ f₂) : s.pt.1 ⟶ cG.pt.1 :=
    (hcG.lift (sG s)).hom
  have baseLift_fst (s : PullbackCone f₁ f₂) : baseLift s ≫ cG.fst.hom = s.fst.hom := by
    have h := congrArg (fun q : (sG s).pt ⟶ toG x₁ => q.hom)
      (hcG.fac (sG s) WalkingCospan.left)
    change (hcG.lift (sG s)).hom ≫ cG.fst.hom = s.fst.hom at h
    simpa only [baseLift, sG, PullbackCone.mk, Functor.elementsMk] using h
  have baseLift_snd (s : PullbackCone f₁ f₂) : baseLift s ≫ cG.snd.hom = s.snd.hom := by
    have h := congrArg (fun q : (sG s).pt ⟶ toG x₂ => q.hom)
      (hcG.fac (sG s) WalkingCospan.right)
    change (hcG.lift (sG s)).hom ≫ cG.snd.hom = s.snd.hom at h
    simpa only [baseLift, sG, PullbackCone.mk, Functor.elementsMk] using h
  let lift (s : PullbackCone f₁ f₂) : s.pt ⟶ y := by
    have hval : F.map (baseLift s) s.pt.2 = y.2 := by
      apply (e y.1).injective
      calc
        e y.1 (F.map (baseLift s) s.pt.2) =
            G.map (baseLift s) (e s.pt.1 s.pt.2) :=
              he (baseLift s) s.pt.2
        _ = cG.pt.2 := by
          have h := (hcG.lift (sG s)).map_val
          change G.map (baseLift s) (e s.pt.1 s.pt.2) = cG.pt.2 at h
          exact h
        _ = e y.1 y.2 := by simp [y]
    exact Functor.Elements.homMk (baseLift s) hval
  have hc : IsLimit c := by
    refine PullbackCone.IsLimit.mk (eq := c.condition) (lift := lift) ?_ ?_ ?_
    · intro s
      apply Functor.Elements.hom_ext
      show (lift s).hom ≫ cG.fst.hom = s.fst.hom
      exact baseLift_fst s
    · intro s
      apply Functor.Elements.hom_ext
      show (lift s).hom ≫ cG.snd.hom = s.snd.hom
      exact baseLift_snd s
    · intro s m hm₁ hm₂
      apply Functor.Elements.hom_ext
      apply PullbackCone.IsLimit.hom_ext hcpG
      · have hm := congrArg (fun q : s.pt ⟶ x₁ => q.hom) hm₁
        change m.hom ≫ cG.fst.hom = s.fst.hom at hm
        calc
          m.hom ≫ cG.fst.hom = s.fst.hom := hm
          _ = (lift s).hom ≫ cG.fst.hom := (baseLift_fst s).symm
      · have hm := congrArg (fun q : s.pt ⟶ x₂ => q.hom) hm₂
        change m.hom ≫ cG.snd.hom = s.snd.hom at hm
        calc
          m.hom ≫ cG.snd.hom = s.snd.hom := hm
          _ = (lift s).hom ≫ cG.snd.hom := (baseLift_snd s).symm
  refine ⟨c, ⟨hc⟩, ?_⟩
  refine ⟨?_⟩
  have hcone : c.map (CategoryOfElements.π F) ≅ cG.map (CategoryOfElements.π G) := by
    refine PullbackCone.ext (Iso.refl _) ?_ ?_ <;> rfl
  exact IsLimit.ofIsoLimit hcpG hcone.symm



/-- A morphism of elements lifts its underlying morphism of the base. -/
private theorem isHomLift_homMk {C : Type u} [Category.{v} C] (F : C ⥤ Type x)
    {X Y : F.Elements} (f : X.1 ⟶ Y.1) (h : F.map f X.2 = Y.2) :
    (CategoryOfElements.π F).IsHomLift f (Functor.Elements.homMk (x := X) (y := Y) f h) :=
  IsHomLift.of_fac _ _ _ rfl rfl (by simp [CategoryOfElements.π])

/-- A morphism of elements lifting `f` has underlying morphism `f`. -/
private theorem val_eq_of_isHomLift {C : Type u} [Category.{v} C] (F : C ⥤ Type x)
    {X Y : F.Elements} (f : X.1 ⟶ Y.1) (g : X ⟶ Y) (h : (CategoryOfElements.π F).IsHomLift f g) :
    g.hom = f := by
  simpa only [CategoryOfElements.π, Functor.Elements.π_map, eqToHom_refl, Category.id_comp,
    Category.comp_id] using
    IsHomLift.fac' (CategoryOfElements.π F) f g

/-- The fibrewise isomorphism class of an element of `F.obj A`. -/
private def elementClass {C : Type u} [Category.{v} C] (F : C ⥤ Type x)
    (A : C) (a : F.obj A) :
    (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
      (categoryOfElements_projection_isCofibered F)).obj A :=
  classOf _ _ ⟨F.elementsMk A a, rfl⟩

/-- Two elements of `F.obj A` have the same fibrewise class only if they are equal: an
arrow of the fibre of a category of elements over the identity is the identity. -/
private theorem elementClass_bijective {C : Type u} [Category.{v} C]
    (F : C ⥤ Type x) (A : C) : Function.Bijective (elementClass F A) := by
  constructor
  · intro a b h
    have hq := congrArg
      (cast (isomorphismClasses_obj
        (BasedCategory.ofFunctor (CategoryOfElements.π F))
        (categoryOfElements_projection_isCofibered F) A)) h
    dsimp only [elementClass] at hq
    rw [classOf_eq, classOf_eq] at hq
    let xa : (CategoryOfElements.π F).Fiber A := ⟨F.elementsMk A a, rfl⟩
    let xb : (CategoryOfElements.π F).Fiber A := ⟨F.elementsMk A b, rfl⟩
    obtain ⟨i⟩ : Nonempty (xa ≅ xb) := Quotient.exact hq
    have hbase := val_eq_of_isHomLift F (𝟙 A) i.hom.1 i.hom.2
    have hval : F.map i.hom.1.hom a = b := i.hom.1.map_val
    rwa [hbase, F.map_id] at hval
  · intro z
    obtain ⟨⟨@⟨B, a⟩, hB⟩, hz⟩ := classOf_surjective
      (BasedCategory.ofFunctor (CategoryOfElements.π F))
      (categoryOfElements_projection_isCofibered F) A z
    change B = A at hB
    subst A
    exact ⟨a, hz⟩

/-- The values of a set-valued functor are the fibrewise isomorphism classes of its category
of elements. -/
private def elementClassEquiv {C : Type u} [Category.{v} C]
    (F : C ⥤ Type x) (A : C) :
    F.obj A ≃
      (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
        (categoryOfElements_projection_isCofibered F)).obj A :=
  Equiv.ofBijective (elementClass F A) (elementClass_bijective F A)

/-- Taking the fibrewise class of an element commutes with the functorial maps. -/
private theorem elementClass_natural {C : Type u} [Category.{v} C]
    (F : C ⥤ Type x) {A B : C} (f : A ⟶ B) (a : F.obj A) :
    elementClass F B (F.map f a) =
      (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
        (categoryOfElements_projection_isCofibered F)).map f
        (elementClass F A a) := by
  let g := Functor.Elements.homMk (x := F.elementsMk A a)
    (y := F.elementsMk B (F.map f a)) f rfl
  let : (BasedCategory.ofFunctor (CategoryOfElements.π F)).p.IsHomLift f g :=
    isHomLift_homMk F (X := F.elementsMk A a) (Y := F.elementsMk B (F.map f a)) f rfl
  exact (map_classOf (BasedCategory.ofFunctor (CategoryOfElements.π F))
    (categoryOfElements_projection_isCofibered F) f ⟨F.elementsMk A a, rfl⟩
    ⟨F.elementsMk B (F.map f a), rfl⟩ g).symm

/-- Transporting along an equality of functors commutes with their maps. -/
private theorem cast_map {C : Type u} [Category.{v} C] {F G : C ⥤ Type x}
    (h : F = G) {A B : C} (f : A ⟶ B) (a : F.obj A) :
    cast (congrArg (fun H : C ⥤ Type x ↦ H.obj B) h) (F.map f a) =
      G.map f (cast (congrArg (fun H : C ⥤ Type x ↦ H.obj A) h) a) := by
  cases h
  rfl

/-- The inverse of a natural bijection of set-valued functors is natural. -/
private theorem inverse_equiv_natural {C : Type u} [Category.{v} C]
    {F : C ⥤ Type x} {G : C ⥤ Type y}
    (e : ∀ A, F.obj A ≃ G.obj A)
    (he : ∀ {A B} (f : A ⟶ B) (a : F.obj A), e B (F.map f a) = G.map f (e A a))
    {A B : C} (f : A ⟶ B) (b : G.obj A) :
    (e B).symm (G.map f b) = F.map f ((e A).symm b) := by
  apply (e B).injective
  rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]

/-- A natural family of maps out of an additive and `k`-linear functor into the identity is
`k`-linear: additivity and homogeneity are read off from the biproduct and the scalar
multiples of the identity. -/
private def linearMapOfNaturality
    {k : Type w} [Field k]
    (L : FGModuleCat.{v} k ⥤ ModuleCat.{x} k) [L.Additive] [L.Linear k]
    (α : ∀ V : FGModuleCat.{v} k, L.obj V → V)
    (hα : ∀ {V W : FGModuleCat.{v} k} (f : V ⟶ W) (a : L.obj V),
      α W ((L.map f).hom a) = f.hom.hom (α V a))
    (V : FGModuleCat.{v} k) : L.obj V →ₗ[k] V where
  toFun := α V
  map_add' a b := by
    let P : FGModuleCat.{v} k := FGModuleCat.of k (V × V)
    let i₁ : V ⟶ P := FGModuleCat.ofHom (LinearMap.inl k V V)
    let i₂ : V ⟶ P := FGModuleCat.ofHom (LinearMap.inr k V V)
    let p₁ : P ⟶ V := FGModuleCat.ofHom (LinearMap.fst k V V)
    let p₂ : P ⟶ V := FGModuleCat.ofHom (LinearMap.snd k V V)
    let z : L.obj P := (L.map i₁).hom a + (L.map i₂).hom b
    have hi₁₁ : i₁ ≫ p₁ = 𝟙 V := by apply FGModuleCat.hom_ext; rfl
    have hi₂₁ : i₂ ≫ p₁ = 0 := by apply FGModuleCat.hom_ext; rfl
    have hi₁₂ : i₁ ≫ p₂ = 0 := by apply FGModuleCat.hom_ext; rfl
    have hi₂₂ : i₂ ≫ p₂ = 𝟙 V := by apply FGModuleCat.hom_ext; rfl
    have hz₁ : (L.map p₁).hom z = a := by
      simp only [z, map_add, ← ModuleCat.comp_apply, ← L.map_comp, hi₁₁, hi₂₁,
        L.map_id, Functor.map_zero, ModuleCat.hom_id, ModuleCat.hom_zero,
        LinearMap.id_apply, LinearMap.zero_apply, add_zero]
    have hz₂ : (L.map p₂).hom z = b := by
      simp only [z, map_add, ← ModuleCat.comp_apply, ← L.map_comp, hi₁₂, hi₂₂,
        L.map_id, Functor.map_zero, ModuleCat.hom_id, ModuleCat.hom_zero,
        LinearMap.id_apply, LinearMap.zero_apply, zero_add]
    have hsum : (L.map (p₁ + p₂)).hom z = a + b := by
      rw [L.map_add]
      change (L.map p₁).hom z + (L.map p₂).hom z = a + b
      rw [hz₁, hz₂]
    have h₁ := hα p₁ z
    have h₂ := hα p₂ z
    have h := hα (p₁ + p₂) z
    rw [hz₁] at h₁
    rw [hz₂] at h₂
    rw [hsum] at h
    exact h.trans (congrArg₂ (· + ·) h₁.symm h₂.symm)
  map_smul' r a := by
    have h := hα (r • 𝟙 V) a
    rwa [Functor.map_smul, L.map_id] at h

/-- Finite dimensionality is transported along an equality of carriers together with the
additive and scalar structures. -/
private theorem finiteDimensional_eqRec
    {k : Type w} [Field k] {A B : Type x} (h : A = B)
    (D : Σ G : AddCommGroup A, letI := G; Module k A)
    (hfinite : letI := D.1; letI := D.2; FiniteDimensional k A) :
    let E : Σ G : AddCommGroup B, letI := G; Module k B := h.rec D
    letI := E.1
    letI := E.2
    FiniteDimensional k B := by
  cases h
  exact hfinite

/-- A vector space over a field is a module over the opposite field, through the identity. -/
@[instance_reducible]
private def fgModuleOppositeModule {k : Type w} [Field k] (V : FGModuleCat.{v} k) :
    Module kᵐᵒᵖ V :=
  Module.compHom V
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }

attribute [local instance] fgModuleOppositeModule

/-- Scalar multiplication on a vector space over a field is central. -/
private theorem fgModuleCentralScalar {k : Type w} [Field k] (V : FGModuleCat.{v} k) :
    IsCentralScalar k V where
  op_smul_eq_smul _ _ := rfl

attribute [local instance] fgModuleCentralScalar

/-- A functor naturally isomorphic to the restricted representable functor of a complete local
algebra `R` has finite-dimensional tangent space: that space injects into the
finite-dimensional space of `Λ`-derivations `R → k`. -/
private theorem finiteDimensional_tangentSpace_of_equiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type x)
    (hp : IsPredeformationCategory (CategoryOfElements.π F))
    (hS2 : SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
        hp.cofibered)))
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (e : ∀ A, F.obj A ≃ (restrictedCoyoneda R).obj A)
    (he : ∀ {A B} (f : A ⟶ B) (a : F.obj A),
      e B (F.map f a) = (restrictedCoyoneda R).map f (e A a)) :
    let 𝓕 := BasedCategory.ofFunctor (CategoryOfElements.π F)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
    FiniteDimensional k (tangentSpaceArtinian Λ k
      (isomorphismClasses 𝓕 hp.cofibered)) := by
  let 𝓕 := BasedCategory.ofFunctor (CategoryOfElements.π F)
  let L := associatedTangentSpaceModuleStructure 𝓕 hp hS2
  let : L.functor.Additive := L.additive
  let : L.functor.Linear k := L.linear
  let S := squareZeroExtensionArtinian.{u, w, max v w} Λ k
  let c (V : FGModuleCat.{max v w} k) :=
    congrArg (fun H : FGModuleCat.{max v w} k ⥤ Type _ ↦ H.obj V) L.forget_comp
  let η (V : FGModuleCat.{max v w} k) :
      L.functor.obj V ≃ (restrictedCoyoneda R).obj (S.obj V) :=
    (Equiv.cast (c V)).trans ((elementClassEquiv F (S.obj V)).symm.trans (e (S.obj V)))
  have hη {V W : FGModuleCat.{max v w} k} (f : V ⟶ W) (a : L.functor.obj V) :
      η W ((L.functor.map f).hom a) =
        (restrictedCoyoneda R).map (S.map f) (η V a) := by
    show e _ ((elementClassEquiv F _).symm (cast (c W) ((L.functor.map f).hom a))) = _
    have hc := cast_map L.forget_comp f a
    change cast (c W) ((L.functor.map f).hom a) =
      (isomorphismClasses 𝓕 hp.cofibered).map (S.map f) (cast (c V) a) at hc
    rw [hc, inverse_equiv_natural (elementClassEquiv F) (fun g b ↦ elementClass_natural F g b)]
    exact he (S.map f) _
  let α (r : R) (V : FGModuleCat.{max v w} k) (a : L.functor.obj V) : V :=
    ((η V a).hom r).snd
  have hα (r : R) {V W : FGModuleCat.{max v w} k} (f : V ⟶ W)
      (a : L.functor.obj V) : α r W ((L.functor.map f).hom a) = f.hom.hom (α r V a) := by
    have h := congrArg (fun g => (g.hom r).snd) (hη f a)
    change α r W ((L.functor.map f).hom a) =
      (TrivSqZeroExt.map f.hom.hom ((η V a).hom r)).snd at h
    rwa [TrivSqZeroExt.snd_map] at h
  let V : FGModuleCat.{max v w} k := FGModuleCat.of k (ULift.{v} k)
  let : Algebra R k :=
    (residueHom R).toRingHom.toAlgebra
  let J : L.functor.obj V →ₗ[k] Derivation Λ R k :=
    { toFun := fun a ↦ tangentSpaceDerivationsLinearEquiv R
        (η V a)
      map_add' a b := by
        ext r
        simp only [Derivation.add_apply,
          tangentSpaceDerivationsLinearEquiv_apply]
        exact congrArg ULift.down ((linearMapOfNaturality L.functor (α r) (hα r) V).map_add a b)
      map_smul' t a := by
        ext r
        simp only [Derivation.smul_apply, RingHom.id_apply,
          tangentSpaceDerivationsLinearEquiv_apply]
        exact congrArg ULift.down ((linearMapOfNaturality L.functor (α r) (hα r) V).map_smul t a) }
  have hJ : Function.Injective J :=
    (tangentSpaceDerivationsLinearEquiv R).injective.comp
      (η V).injective
  let : Module.Finite k (Derivation Λ R k) := derivation_module_finite R.residueEquiv
  have hfinite : FiniteDimensional k (L.functor.obj V) := Module.Finite.of_injective J hJ
  exact finiteDimensional_eqRec (c V)
    ⟨(L.functor.obj V).isAddCommGroup, (L.functor.obj V).isModule⟩ hfinite

/-- The morphism `k → k[ε]` of `𝒞_Λ` with coordinates `a ↦ a + D(a) ε` attached to a
derivation `D` of the residue field. -/
private def dualNumbersDerivationHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (D : Derivation Λ k k) :
    residueFieldObject.{u, v, w} Λ k ⟶
      artinianDualNumbers.{u, w, v} Λ k :=
  ArtinianLocalAlgCat.homOfAlgHom
    { toFun := fun a ↦ ⟨a.down, ULift.up (D a.down)⟩
      map_one' := TrivSqZeroExt.ext rfl (ULift.ext D.map_one_eq_zero)
      map_mul' a b := TrivSqZeroExt.ext rfl (ULift.ext (D.leibniz a.down b.down))
      map_zero' := TrivSqZeroExt.ext rfl (ULift.ext D.map_zero)
      map_add' a b := TrivSqZeroExt.ext rfl (ULift.ext (D.map_add a.down b.down))
      commutes' r := TrivSqZeroExt.ext rfl (ULift.ext (D.map_algebraMap r)) }
    (fun _ ↦ rfl)

/-- The morphism attached to a derivation has the coordinates of that derivation. -/
private theorem dualNumbersDerivationHom_isDerivationMorphism
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (D : Derivation Λ k k) :
    IsDerivationMorphism D (dualNumbersDerivationHom.{u, v, w} D) :=
  fun _ ↦ ⟨rfl, rfl⟩

/-- For a functor naturally isomorphic to a restricted representable functor the derivation map
is injective: a derivation is recovered from the second coordinate of the algebra map it
induces on the dual numbers. -/
private theorem derivationToTangentSpace_injective_of_equiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type x)
    (hp : IsPredeformationCategory (CategoryOfElements.π F))
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (e : ∀ A, F.obj A ≃ (restrictedCoyoneda R).obj A)
    (he : ∀ {A B} (f : A ⟶ B) (a : F.obj A),
      e B (F.map f a) = (restrictedCoyoneda R).map f (e A a)) :
    Function.Injective (derivationToTangentSpace (CategoryOfElements.π F) hp) := by
  let := ((isPredeformationCategory_iff F).mp hp).some
  let a : F.obj (residueFieldObject.{u, v, w} Λ k) := default
  intro D E h
  have happly (δ : Derivation Λ k k) := derivationToTangentSpace_apply _ hp δ
    ⟨F.elementsMk _ a, rfl⟩ (dualNumbersDerivationHom δ) (dualNumbersDerivationHom_isDerivationMorphism δ)
  rw [happly D, happly E] at h
  change (isomorphismClasses _ _).map (dualNumbersDerivationHom D)
      (elementClass F _ a) =
      (isomorphismClasses _ _).map (dualNumbersDerivationHom E)
      (elementClass F _ a) at h
  rw [← elementClass_natural, ← elementClass_natural] at h
  have hval := (elementClass_bijective F _).1 h
  have hmaps := congrArg (e _) hval
  rw [he, he] at hmaps
  ext c
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R.residueEquiv.symm c)
  have hres : R.residueEquiv (IsLocalRing.residue R r) = c := by
    rw [hr, AlgEquiv.apply_symm_apply]
  have ha : ((e _ a).hom r).down = c := ((e _ a).residue_comm r).trans hres
  have hv := congrArg (fun f => (f.hom r).snd.down) hmaps
  change D (((e _ a).hom r).down) = E (((e _ a).hom r).down) at hv
  simpa only [ha] using hv

/-- The augmentation `k[ε] → k` of the dual numbers, as a morphism of `𝒞_Λ`. -/
private def tangentResidueMorphism
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    artinianDualNumbers.{u, w, v} Λ k ⟶
      residueFieldObject.{u, v, w} Λ k :=
  ArtinianLocalAlgCat.homOfAlgHom
    { toFun := fun a ↦ ULift.up a.fst
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl } (fun _ ↦ rfl)

/-- The morphism `k[ε] → k[ε ⊕ ε']` of `𝒞_Λ` with coordinates `a + bε ↦ a + bε + D(a)ε'`,
whose two projections are the identity and the twist by `D`. -/
private def derivationGraphMorphism
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (D : Derivation Λ k k) :
    artinianDualNumbers.{u, w, v} Λ k ⟶
      (squareZeroExtensionArtinian Λ k).obj
        (FGModuleCat.of k (ULift.{v} k × ULift.{v} k)) :=
  ArtinianLocalAlgCat.homOfAlgHom
    { toFun := fun a ↦ ⟨a.fst, (a.snd, ULift.up (D a.fst))⟩
      map_one' := TrivSqZeroExt.ext rfl (Prod.ext rfl (ULift.ext D.map_one_eq_zero))
      map_mul' _ _ := TrivSqZeroExt.ext rfl (Prod.ext rfl (ULift.ext (D.leibniz _ _)))
      map_zero' := TrivSqZeroExt.ext rfl (Prod.ext rfl (ULift.ext D.map_zero))
      map_add' _ _ := TrivSqZeroExt.ext rfl (Prod.ext rfl (ULift.ext (D.map_add _ _)))
      commutes' r :=
        TrivSqZeroExt.ext rfl (Prod.ext rfl (ULift.ext (D.map_algebraMap r))) }
    (fun _ ↦ rfl)

/-- The action of a derivation on the tangent space is the map induced on fibrewise
isomorphism classes by the twisting automorphism of the dual numbers. -/
private theorem derivationAction_eq_map
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {C : Type x} [Category.{y} C]
    (p : C ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (D : Derivation Λ k k) (z : predeformationTangentSpace p hp) :
    (derivationAction p hp).action (D, z) =
      (isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered).map
        ((derivationAction p hp).twistMap D) z := by
  obtain ⟨a, b, f, ha, hf, hb⟩ := (derivationAction p hp).action_pushforward D z
  let : (BasedCategory.ofFunctor p).p.IsHomLift
      ((derivationAction p hp).twistMap D) f :=
    IsHomLift.of_fac _ _ _ a.2 b.2 (by
      show _ = eqToHom a.2.symm ≫ p.map f ≫ eqToHom b.2
      rw [hf]
      simp)
  have h := map_classOf (BasedCategory.ofFunctor p) hp.cofibered
    ((derivationAction p hp).twistMap D) a b f
  exact (ha ▸ hb ▸ h).symm

/-- Injectivity of the derivation map makes the action of `Der_Λ(k, k)` on the tangent space
free: a derivation fixing a tangent vector has the same derivation map as the zero
derivation. -/
private theorem derivationAction_free
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type x)
    (hp : IsPredeformationCategory (CategoryOfElements.π F))
    (hS2 : SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (BasedCategory.ofFunctor (CategoryOfElements.π F))
        hp.cofibered)))
    (hinj : Function.Injective (derivationToTangentSpace (CategoryOfElements.π F) hp))
    (D : Derivation Λ k k) (y : predeformationTangentSpace (CategoryOfElements.π F) hp)
    (hfix : (derivationAction (CategoryOfElements.π F) hp).action (D, y) = y) :
    D = 0 := by
  let p := CategoryOfElements.π F
  let 𝓕 := BasedCategory.ofFunctor p
  let H := isomorphismClasses 𝓕 hp.cofibered
  let L := associatedTangentSpaceModuleStructure 𝓕 hp hS2
  let : L.functor.Additive := L.additive
  let S := squareZeroExtensionArtinian.{u, w, max v w} Λ k
  let V : FGModuleCat.{max v w} k := FGModuleCat.of k (ULift.{v} k)
  let P : FGModuleCat.{max v w} k := FGModuleCat.of k (ULift.{v} k × ULift.{v} k)
  let p₁ : P ⟶ V := FGModuleCat.ofHom (LinearMap.fst k _ _)
  let p₂ : P ⟶ V := FGModuleCat.ofHom (LinearMap.snd k _ _)
  let c (W : FGModuleCat.{max v w} k) :=
    congrArg (fun J : FGModuleCat.{max v w} k ⥤ Type _ ↦ J.obj W) L.forget_comp
  let z (δ : Derivation Λ k k) : L.functor.obj P :=
    cast (c P).symm (H.map (derivationGraphMorphism δ) y)
  have hc (f : P ⟶ V) (δ : Derivation Λ k k) :
      cast (c V) ((L.functor.map f).hom (z δ)) =
        H.map (derivationGraphMorphism δ ≫ S.map f) y := by
    have h := cast_map L.forget_comp f (z δ)
    change cast (c V) ((L.functor.map f).hom (z δ)) =
      H.map (S.map f) (cast (c P) (z δ)) at h
    simpa only [z, cast_cast, cast_eq, Functor.map_comp_apply] using h
  have hfirst (δ : Derivation Λ k k) : derivationGraphMorphism δ ≫ S.map p₁ =
      𝟙 (artinianDualNumbers.{u, w, v} Λ k) := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · show (TrivSqZeroExt.map p₁.hom.hom _).fst = a.fst
      rw [TrivSqZeroExt.fst_map]
      rfl
    · show (TrivSqZeroExt.map p₁.hom.hom _).snd = a.snd
      rw [TrivSqZeroExt.snd_map]
      rfl
  have hsecond (δ : Derivation Λ k k) : derivationGraphMorphism δ ≫ S.map p₂ =
      tangentResidueMorphism ≫ dualNumbersDerivationHom δ := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · show (TrivSqZeroExt.map p₂.hom.hom _).fst = a.fst
      rw [TrivSqZeroExt.fst_map]
      rfl
    · show (TrivSqZeroExt.map p₂.hom.hom _).snd = ULift.up (δ a.fst)
      rw [TrivSqZeroExt.snd_map]
      rfl
  have hsum (δ : Derivation Λ k k) : derivationGraphMorphism δ ≫ S.map (p₁ + p₂) =
      (derivationAction p hp).twistMap δ := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    have h := (derivationAction p hp).twistMap_eq δ a.fst a.snd.down
    have ha : TrivSqZeroExt.inl a.fst + TrivSqZeroExt.inr (ULift.up a.snd.down) = a :=
      TrivSqZeroExt.inl_fst_add_inr_snd_eq a
    rw [ha] at h
    rw [h]
    apply TrivSqZeroExt.ext
    · rfl
    · show (TrivSqZeroExt.map (p₁ + p₂).hom.hom _).snd = _
      rw [TrivSqZeroExt.snd_map]
      show a.snd + ULift.up (δ a.fst) = 0 + ULift.up (a.snd.down + δ a.fst)
      rw [zero_add]
      rfl
  have h₁ : (L.functor.map p₁).hom (z D) = (L.functor.map p₁).hom (z 0) := by
    refine (cast_inj (c V)).1 ?_
    rw [hc, hc, hfirst, hfirst]
  have hsum' : (L.functor.map (p₁ + p₂)).hom (z D) =
      (L.functor.map (p₁ + p₂)).hom (z 0) := by
    refine (cast_inj (c V)).1 ?_
    rw [hc, hc, hsum, hsum, ← derivationAction_eq_map, ← derivationAction_eq_map,
      hfix, (derivationAction p hp).zero_action]
  have h₂ : (L.functor.map p₂).hom (z D) = (L.functor.map p₂).hom (z 0) := by
    rw [L.functor.map_add] at hsum'
    change (L.functor.map p₁).hom (z D) + (L.functor.map p₂).hom (z D) =
      (L.functor.map p₁).hom (z 0) + (L.functor.map p₂).hom (z 0) at hsum'
    exact add_left_cancel ((congrArg (· + _) h₁).symm.trans hsum')
  let k₀ := residueFieldObject.{u, v, w} Λ k
  let := ((isPredeformationCategory_iff F).mp hp).some
  let : Unique (H.obj k₀) := (elementClassEquiv F k₀).symm.unique
  have hγ (δ : Derivation Λ k k) : cast (c V) ((L.functor.map p₂).hom (z δ)) =
      derivationToTangentSpace p hp δ := by
    rw [hc, hsecond, Functor.map_comp_apply, derivationToTangentSpace_apply p hp δ
      ⟨F.elementsMk k₀ default, rfl⟩ (dualNumbersDerivationHom δ)
      (dualNumbersDerivationHom_isDerivationMorphism δ)]
    exact congrArg (H.map (dualNumbersDerivationHom δ)) (Subsingleton.elim _ _)
  apply hinj
  rw [← hγ D, ← hγ 0, h₂]

/-- When the action of `Der_Λ(k, k)` on the tangent space is free, a tangent vector determines
the derivation whose differential it is. -/
private theorem derivationDifferentialGraph_left_unique
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {C : Type x} [Category.{y} C]
    (p : C ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (ξ : FormalObject p)
    (hξ : HasBijectiveDifferentialOnDerivationOrbits p hp ξ)
    (hfree : ∀ (δ : Derivation Λ k k) (z : predeformationTangentSpace p hp),
      (derivationAction p hp).action (δ, z) = z → δ = 0)
    {D E : Derivations ξ.base k}
    {z : predeformationTangentSpace p hp}
    (hD : derivationDifferentialGraph p hp ξ D z)
    (hE : derivationDifferentialGraph p hp ξ E z) : D = E := by
  obtain ⟨δ, hδ⟩ := (hξ.2.2.2 D E z z hD hE).mp
    ⟨0, ((derivationAction p hp).zero_action z).symm⟩
  obtain ⟨E', hE', hz⟩ := hξ.2.2.1 D δ z hD
  have heq : E' = E := DFunLike.ext _ _ fun r ↦ (hE' r).trans (hδ r).symm
  subst E'
  obtain ⟨_, _, huniq⟩ := hξ.1 E
  have hfix : (derivationAction p hp).action (δ, z) = z :=
    (huniq _ hz).trans (huniq _ hE).symm
  have hzero := hfree δ z hfix
  apply DFunLike.ext
  intro r
  simpa only [hzero, Derivation.zero_apply, add_zero] using (hδ r).symm

/-- A point of the restricted representable functor of `R` at the dual numbers is a
`Λ`-derivation of `R` into the residue field, by its second coordinate. -/
@[sga "7 VI 1.17" "partial"]
private def tangentPointDerivation
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (a : (restrictedCoyoneda R).obj
      (artinianDualNumbers.{u, w, v} Λ k)) :
    Derivations R k := by
  letI : Module Λ k := Module.compHom k (algebraMap Λ k)
  letI : Module R k := Module.compHom k
    (residueHom R).toRingHom
  exact
    {
      toFun r := (a.hom r).snd.down
      map_add' r s := by rw [map_add]; rfl
      map_smul' t r := by
        change (a.hom (t • r)).snd.down = (algebraMap Λ k t) * (a.hom r).snd.down
        rw [Algebra.smul_def, map_mul, a.hom.commutes]
        change (algebraMap Λ k t) * (a.hom r).snd.down + (a.hom r).fst * 0 = _
        simp
      map_one_eq_zero' := by
        change (a.hom 1).snd.down = 0
        rw [map_one]
        rfl
      leibniz' r s := by
        have hr := a.residue_comm r
        have hs := a.residue_comm s
        change (a.hom r).fst = residueHom R r at hr
        change (a.hom s).fst = residueHom R s at hs
        change (a.hom (r * s)).snd.down =
          residueHom R r * (a.hom s).snd.down +
          residueHom R s * (a.hom r).snd.down
        rw [map_mul]
        change (a.hom r).fst * (a.hom s).snd.down + (a.hom s).fst * (a.hom r).snd.down = _
        rw [hr, hs] }

/-- A point of the restricted representable functor at the dual numbers is determined by the
derivation it defines. -/
@[sga "3 VIIA 1.2.1" "Injectivity of u ↦ u∘E"]
private theorem tangentPointDerivation_injective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    Function.Injective (tangentPointDerivation.{u, v, w} R) := by
  intro a b h
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · exact (a.residue_comm r).trans (b.residue_comm r).symm
  · apply ULift.ext
    exact DFunLike.congr_fun h r

/-- For a formal object whose differential is bijective on derivation orbits, over a free
action, the associated morphism is bijective on tangent spaces. -/
private theorem associatedMap_bijective_of_derivationAction_free
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {C : Type x} [Category.{y} C]
    (p : C ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (ξ : FormalObject p)
    (hξ : HasBijectiveDifferentialOnDerivationOrbits p hp ξ)
    (hfree : ∀ (δ : Derivation Λ k k) (z : predeformationTangentSpace p hp),
      (derivationAction p hp).action (δ, z) = z → δ = 0)
    (P : ChosenPushforwards p) :
    Function.Bijective (fun a ↦ mapIsomorphismClasses
      (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base))
      hp.cofibered
      (associatedMorphism hp.cofibered ξ P).toBasedFunctor
      (artinianDualNumbers.{u, w, v} Λ k)
      (elementClass (restrictedCoyoneda ξ.base) _ a)) := by
  let f := fun a ↦ mapIsomorphismClasses
    (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base))
    hp.cofibered
    (associatedMorphism hp.cofibered ξ P).toBasedFunctor
    (artinianDualNumbers.{u, w, v} Λ k)
    (elementClass (restrictedCoyoneda ξ.base) _ a)
  have hgraph (a) : derivationDifferentialGraph p hp ξ
      (tangentPointDerivation ξ.base a) (f a) := ⟨P, a, fun _ ↦ rfl, rfl⟩
  refine ⟨fun a b hab ↦ ?_, fun z ↦ ?_⟩
  · apply tangentPointDerivation_injective ξ.base
    have hb := hgraph b
    change f a = f b at hab
    rw [← hab] at hb
    exact derivationDifferentialGraph_left_unique p hp ξ hξ hfree (hgraph a) hb
  · obtain ⟨D, Q, a, ha, hz⟩ := hξ.2.1 z
    have hD : tangentPointDerivation ξ.base a = D := DFunLike.ext _ _ ha
    obtain ⟨_, _, huniq⟩ := hξ.1 D
    exact ⟨a, (huniq _ (hD ▸ hgraph a)).trans (huniq _ ⟨Q, a, ha, hz⟩).symm⟩

/-- An isomorphism of residue fields over `Λ` induces a functor between the corresponding
categories of Artinian local algebras, by composing the prescribed identifications. -/
private def changeResidueField
    {Λ : Type u} {k : Type w} {k' : Type y}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (e : k ≃ₐ[Λ] k') :
    ArtinianLocalAlgCat.{u, v, w} Λ k ⥤
      ArtinianLocalAlgCat.{u, v, y} Λ k' where
  obj A := { carrier := A, residueEquiv := A.residueEquiv.trans e }
  map f :=
    { hom := f.hom
      isLocal := f.isLocal
      residue_comm := fun a ↦ congrArg e (f.residue_comm a) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Changing the residue field along an isomorphism is a full functor. -/
private theorem changeResidueFieldFull
    {Λ : Type u} {k : Type w} {k' : Type y}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (e : k ≃ₐ[Λ] k') : (changeResidueField.{u, v, w, y} e).Full where
  map_surjective f :=
    ⟨{ hom := f.hom
       isLocal := f.isLocal
       residue_comm := fun a ↦ e.injective (f.residue_comm a) }, rfl⟩

/-- Changing the residue field along an isomorphism is a faithful functor. -/
private theorem changeResidueFieldFaithful
    {Λ : Type u} {k : Type w} {k' : Type y}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (e : k ≃ₐ[Λ] k') : (changeResidueField.{u, v, w, y} e).Faithful where
  map_injective h := ArtinianLocalAlgCat.hom_ext (congrArg (fun f ↦ f.hom) h)

/-- Changing the residue field along an isomorphism is essentially surjective. -/
private theorem changeResidueFieldEssSurj
    {Λ : Type u} {k : Type w} {k' : Type y}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (e : k ≃ₐ[Λ] k') : (changeResidueField.{u, v, w, y} e).EssSurj where
  mem_essImage A := by
    let B : ArtinianLocalAlgCat.{u, v, w} Λ k :=
      { carrier := A, residueEquiv := A.residueEquiv.trans e.symm }
    refine ⟨B, ⟨{ hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }⟩⟩
    · exact
        { hom := AlgHom.id Λ A
          isLocal := isLocalHom_id _
          residue_comm := fun a ↦ (e.apply_symm_apply _).symm }
    · exact
        { hom := AlgHom.id Λ A
          isLocal := isLocalHom_id _
          residue_comm := fun a ↦ e.apply_symm_apply _ }
    · apply ArtinianLocalAlgCat.hom_ext
      rfl
    · apply ArtinianLocalAlgCat.hom_ext
      rfl

attribute [local instance] changeResidueFieldFull changeResidueFieldFaithful
  changeResidueFieldEssSurj

/-- Restricting the base along a full functor is full on categories of elements. -/
private theorem elementsPrecompFull {C : Type u} {D : Type w}
    [Category.{v} C] [Category.{y} D] (U : C ⥤ D) [U.Full]
    (F : D ⥤ Type x) : (Functor.Elements.precomp U F).Full where
  map_surjective {X Y} g := by
    refine ⟨⟨U.preimage g.hom, ?_⟩, ?_⟩
    · refine Eq.trans ?_ g.map_val
      exact congrArg (fun h : U.obj X.1 ⟶ U.obj Y.1 ↦ F.map h X.2)
        (U.map_preimage g.hom)
    · apply Functor.Elements.hom_ext
      exact U.map_preimage g.hom

/-- Restricting the base along a faithful functor is faithful on categories of elements. -/
private theorem elementsPrecompFaithful {C : Type u} {D : Type w}
    [Category.{v} C] [Category.{y} D] (U : C ⥤ D) [U.Faithful]
    (F : D ⥤ Type x) : (Functor.Elements.precomp U F).Faithful where
  map_injective h := by
    apply Functor.Elements.hom_ext
    exact U.map_injective (congrArg (fun f ↦ f.hom) h)

/-- Restricting the base along an essentially surjective functor is essentially surjective on
categories of elements. -/
private theorem elementsPrecompEssSurj {C : Type u} {D : Type w}
    [Category.{v} C] [Category.{y} D] (U : C ⥤ D) [U.EssSurj]
    (F : D ⥤ Type x) : (Functor.Elements.precomp U F).EssSurj where
  mem_essImage a := by
    let B := U.objPreimage a.1
    let e := U.objObjPreimageIso a.1
    refine ⟨(U ⋙ F).elementsMk B (F.map e.inv a.2), ⟨Functor.Elements.isoMk e ?_⟩⟩
    show F.map e.hom (F.map e.inv a.2) = a.2
    rw [← Functor.map_comp_apply, e.inv_hom_id, F.map_id]
    rfl

attribute [local instance] elementsPrecompFull elementsPrecompFaithful elementsPrecompEssSurj

/-- Condition (RS) is preserved by restricting the base along an equivalence that preserves
surjectivity of the underlying algebra maps. -/
private theorem satisfiesRS_precomp
    {Λ : Type u} {k : Type w} {k' : Type y}
    [CommRing Λ] [Field k] [Field k'] [Algebra Λ k] [Algebra Λ k']
    (U : ArtinianLocalAlgCat.{u, v, y} Λ k' ⥤
      ArtinianLocalAlgCat.{u, v, w} Λ k) [U.IsEquivalence]
    (hU : ∀ {A B : ArtinianLocalAlgCat.{u, v, y} Λ k'} (f : A ⟶ B), Function.Surjective f.hom →
      Function.Surjective (U.map f).hom)
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type x)
    (hF : SatisfiesRS (CategoryOfElements.π F)) :
    SatisfiesRS (CategoryOfElements.π (U ⋙ F)) := by
  refine ⟨categoryOfElements_projection_isCofibered _, ?_⟩
  intro a b c f g hg
  let E := Functor.Elements.precomp U F
  let : E.IsEquivalence := Functor.IsEquivalence.mk
  obtain ⟨s, ⟨hs⟩, ⟨hsp⟩⟩ := hF.2 (E.map f) (E.map g) (hU g.hom hg)
  let : HasLimit (cospan (E.map f) (E.map g)) := ⟨⟨s, hs⟩⟩
  let e : cospan f g ⋙ E ≅ cospan (E.map f) (E.map g) :=
    diagramIsoCospan (cospan f g ⋙ E)
  let : HasLimit (cospan f g ⋙ E) := hasLimit_of_iso e.symm
  let : HasLimit (cospan f g) := Adjunction.hasLimit_of_comp_equivalence _ E
  let q := CategoryOfElements.π F
  let p := CategoryOfElements.π (U ⋙ F)
  let : PreservesLimit (cospan (E.map f) (E.map g)) q :=
    preservesLimit_of_preserves_limit_cone hs
      ((s.isLimitMapConeEquiv q).symm hsp)
  let : PreservesLimit (cospan f g ⋙ E) q := preservesLimit_of_iso_diagram q e.symm
  let : PreservesLimit (cospan f g) (p ⋙ U) :=
    inferInstanceAs (PreservesLimit (cospan f g) (E ⋙ q))
  let : PreservesLimit (cospan f g) p := preservesLimit_of_reflects_of_preserves p U
  exact ⟨PullbackCone.mk (pullback.fst f g) (pullback.snd f g)
      (pullback.condition (f := f) (g := g)),
    ⟨pullbackIsPullback f g⟩, ⟨isLimitOfHasPullbackOfPreservesLimit p f g⟩⟩

/-- The map on values of set-valued functors underlying a based functor between their
categories of elements. -/
private def basedMapOnElements {C : Type u} [Category.{v} C]
    {F : C ⥤ Type x} {G : C ⥤ Type y}
    (φ : BasedFunctor (BasedCategory.ofFunctor (CategoryOfElements.π F))
      (BasedCategory.ofFunctor (CategoryOfElements.π G)))
    (A : C) (a : F.obj A) : G.obj A :=
  G.map (eqToHom (φ.w_obj (F.elementsMk A a))) (φ.obj (F.elementsMk A a)).2

/-- The map on values underlying a based functor is natural. -/
private theorem basedMapOnElements_natural {C : Type u} [Category.{v} C]
    {F : C ⥤ Type x} {G : C ⥤ Type y}
    (φ : BasedFunctor (BasedCategory.ofFunctor (CategoryOfElements.π F))
      (BasedCategory.ofFunctor (CategoryOfElements.π G)))
    {A B : C} (f : A ⟶ B) (a : F.obj A) :
    basedMapOnElements φ B (F.map f a) = G.map f (basedMapOnElements φ A a) := by
  let g := Functor.Elements.homMk (x := F.elementsMk A a)
    (y := F.elementsMk B (F.map f a)) f rfl
  let : (BasedCategory.ofFunctor (CategoryOfElements.π F)).p.IsHomLift f g :=
    isHomLift_homMk F (X := F.elementsMk A a) (Y := F.elementsMk B (F.map f a)) f rfl
  let := φ.preserves_isHomLift f g
  have hh := IsHomLift.fac' (BasedCategory.ofFunctor (CategoryOfElements.π G)).p f (φ.map g)
  have hv := (φ.map g).map_val
  dsimp only [basedMapOnElements]
  rw [← hv, ← Functor.map_comp_apply]
  have he : (φ.map g).hom ≫ eqToHom (φ.w_obj (F.elementsMk B (F.map f a))) =
      eqToHom (φ.w_obj (F.elementsMk A a)) ≫ f := by
    change (φ.map g).hom = _ at hh
    rw [hh]
    simp
  rw [he, Functor.map_comp_apply]

/-- The class of an object of the fibre of a category of elements is the class of the
corresponding element of the functor. -/
private theorem classOf_eq_elementClass {C : Type u} [Category.{v} C]
    (F : C ⥤ Type x) {A : C} (a : (CategoryOfElements.π F).Fiber A) :
    classOf (BasedCategory.ofFunctor (CategoryOfElements.π F))
        (categoryOfElements_projection_isCofibered F) a =
      elementClass F A (F.map (eqToHom a.2) a.1.2) := by
  rcases a with ⟨@⟨B, a⟩, h⟩
  change B = A at h
  subst A
  rw [eqToHom_refl, F.map_id]
  rfl

/-- A based functor acts on fibrewise classes through its map on values. -/
private theorem basedMapOnElements_class {C : Type u} [Category.{v} C]
    {F : C ⥤ Type x} {G : C ⥤ Type y}
    (φ : BasedFunctor (BasedCategory.ofFunctor (CategoryOfElements.π F))
      (BasedCategory.ofFunctor (CategoryOfElements.π G)))
    (A : C) (a : F.obj A) :
    mapIsomorphismClasses
      (categoryOfElements_projection_isCofibered F)
      (categoryOfElements_projection_isCofibered G) φ A (elementClass F A a) =
      elementClass G A (basedMapOnElements φ A a) := by
  rw [elementClass, mapIsomorphismClasses_classOf, classOf_eq_elementClass]
  rfl

/-- Smoothness of a based functor between categories of elements is the lifting property for
its map on values. -/
private theorem basedMapOnElements_lifts
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type x}
    {G : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type y}
    (φ : BasedFunctor (BasedCategory.ofFunctor (CategoryOfElements.π F))
      (BasedCategory.ofFunctor (CategoryOfElements.π G)))
    (hφ : IsSmooth φ)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f : B ⟶ A) (hf : Function.Surjective f.hom)
    (a : F.obj A) (b : G.obj B)
    (hab : basedMapOnElements φ A a = G.map f b) :
    ∃ c : F.obj B, F.map f c = a ∧ basedMapOnElements φ B c = b := by
  let x : F.Elements := F.elementsMk A a
  let y : G.Elements := G.elementsMk B b
  let g : y ⟶ φ.obj x :=
    ⟨f ≫ eqToHom (φ.w_obj x).symm, by
      rw [Functor.map_comp_apply, ← hab]
      show G.map (eqToHom (φ.w_obj x).symm)
        (G.map (eqToHom (φ.w_obj x)) (φ.obj x).2) = _
      rw [← Functor.map_comp_apply]
      simp⟩
  have hg : (CategoryOfElements.π G).IsHomLift f g := by
    apply IsHomLift.of_fac _ _ _ rfl (φ.w_obj x)
    show f = (f ≫ eqToHom (φ.w_obj x).symm) ≫ eqToHom (φ.w_obj x)
    simp
  obtain ⟨@⟨B', c⟩, h, i, hh, hi, _⟩ := hφ f hf y x g hg
  have hB : B' = B := by
    let : (CategoryOfElements.π F).IsHomLift f h := hh
    exact IsHomLift.domain_eq (CategoryOfElements.π F) f h
  subst B'
  have hhval : h.hom = f := by
    exact val_eq_of_isHomLift F f h (by exact hh)
  refine ⟨c, ?_, ?_⟩
  · simpa only [hhval] using h.map_val
  · have hival : i.hom = eqToHom (φ.w_obj (F.elementsMk B c)) := by
      let : (CategoryOfElements.π G).IsHomLift (𝟙 B) i := hi
      have hi' := IsHomLift.fac' (CategoryOfElements.π G) (𝟙 B) i
      simpa only [CategoryOfElements.π, Functor.Elements.π_map, eqToHom_refl, Category.id_comp,
        Category.comp_id] using hi'
    exact (congrArg (fun f ↦ G.map f (φ.obj (F.elementsMk B c)).2) hival).symm.trans i.map_val

/-- Conversely, the lifting property for a natural transformation of set-valued functors makes
the induced based functor on categories of elements smooth. -/
private theorem isSmooth_of_lifts
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F G : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type x}
    (α : F ⟶ G)
    (h : ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
      Function.Surjective f.hom →
      ∀ (a : F.obj A) (b : G.obj B), α.app A a = G.map f b →
        ∃ c : F.obj B, F.map f c = a ∧ α.app B c = b) :
    IsSmooth (elementsBasedFunctor α) := by
  dsimp [IsSmooth, elementsBasedFunctor]
  intro B A f hf
  intro y x g hg
  rcases y with @⟨B', b⟩
  rcases x with @⟨A', a⟩
  let := hg
  have hdom : B' = B := by
    simpa [BasedCategory.ofFunctor, CategoryOfElements.π] using
      IsHomLift.domain_eq
        (p := (BasedCategory.ofFunctor (Functor.Elements.π G)).p) f g
  have hcod : A' = A := by
    simpa [BasedCategory.ofFunctor, CategoryOfElements.π, CategoryOfElements.map] using
      IsHomLift.codomain_eq
        (p := (BasedCategory.ofFunctor (Functor.Elements.π G)).p) f g
  cases hdom.symm
  cases hcod.symm
  have hval : g.hom = f := val_eq_of_isHomLift G f g (by exact hg)
  obtain ⟨c, hc, hαc⟩ := h f hf a b (by
    simpa [hval, CategoryOfElements.map] using g.map_val.symm)
  refine ⟨F.elementsMk B c, ⟨f, hc⟩, ⟨𝟙 B, ?_⟩, ?_, ?_, ?_⟩
  · simpa [CategoryOfElements.map, Functor.map_id_apply] using hαc
  · exact isHomLift_homMk F (X := F.elementsMk B c) (Y := F.elementsMk A a) f hc
  · exact isHomLift_homMk G (X := G.elementsMk B (α.app B c)) (Y := G.elementsMk B b) (𝟙 B)
      (by simpa [Functor.map_id_apply] using hαc)
  · apply Functor.Elements.hom_ext
    show f = (𝟙 B) ≫ g.hom
    simp [hval]

/-- A natural family of maps bijective at one object is bijective at every isomorphic
object. -/
private theorem natural_bijective_of_iso
    {C : Type u} [Category.{v} C] {F : C ⥤ Type x} {G : C ⥤ Type y}
    (α : ∀ A, F.obj A → G.obj A)
    (hα : ∀ {A B} (f : A ⟶ B) (a : F.obj A), α B (F.map f a) = G.map f (α A a))
    {A B : C} (e : A ≅ B) (hB : Function.Bijective (α B)) :
    Function.Bijective (α A) := by
  have he : α A = (G.mapIso e).toEquiv.symm ∘ α B ∘ (F.mapIso e).toEquiv := by
    funext a
    show α A a = G.map e.inv (α B (F.map e.hom a))
    rw [hα, ← Functor.map_comp_apply, e.hom_inv_id, G.map_id]
    rfl
  rw [he]
  exact (G.mapIso e).toEquiv.symm.bijective.comp
    (hB.comp (F.mapIso e).toEquiv.bijective)

/-- An algebra isomorphism respecting the prescribed residue coordinates is an isomorphism
of `𝒞_Λ`. -/
private def isoOfAlgEquivOfResidue
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (e : A ≃ₐ[Λ] B)
    (he : ∀ a, B.residueEquiv (IsLocalRing.residue B (e a)) =
      A.residueEquiv (IsLocalRing.residue A a)) : A ≅ B where
  hom := { hom := e.toAlgHom, isLocal := isLocalHom_toRingHom e, residue_comm := he }
  inv :=
    { hom := e.symm.toAlgHom
      isLocal := isLocalHom_toRingHom e.symm
      residue_comm := fun b ↦ by simpa using (he (e.symm b)).symm }
  hom_inv_id := by
    apply ArtinianLocalAlgCat.hom_ext
    ext a
    exact e.symm_apply_apply a
  inv_hom_id := by
    apply ArtinianLocalAlgCat.hom_ext
    ext b
    exact e.apply_symm_apply b

/-- The residue field object over `ULift k` corresponds to the residue field object over `k`
under the change of residue field. -/
private def liftedResidueFieldIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    (changeResidueField (ULift.algEquiv (R := Λ) (A := k))).obj
      (residueFieldObject.{u, max v w, max v w} Λ (ULift.{v} k)) ≅
      residueFieldObject.{u, v, w} Λ k :=
  isoOfAlgEquivOfResidue
    { toFun := fun a ↦ ⟨a.down.down⟩
      invFun := fun a ↦ ⟨⟨a.down⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl } (fun _ ↦ rfl)

/-- The dual numbers over `ULift k` correspond to the dual numbers over `k` under the change
of residue field. -/
private def liftedDualNumbersIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    (changeResidueField (ULift.algEquiv (R := Λ) (A := k))).obj
      (augmentedDualNumbers (Λ := Λ) (k := ULift.{v} k)) ≅
      artinianDualNumbers.{u, w, v} Λ k :=
  isoOfAlgEquivOfResidue
    { toFun := fun a ↦ ⟨a.fst.down, a.snd⟩
      invFun := fun a ↦ ⟨ULift.up a.fst, a.snd⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl } (fun _ ↦ rfl)

/-- A deformation functor stays a deformation functor after changing the residue field to
`ULift k` and raising its values to a common universe. -/
private theorem isDeformationFunctor_lifted
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type x)
    (hG : IsDeformationFunctor G) :
    IsDeformationFunctor
      (changeResidueField (ULift.algEquiv (R := Λ) (A := k) : ULift.{v} k ≃ₐ[Λ] k) ⋙
        (G ⋙ uliftFunctor.{y, x})) := by
  let U := changeResidueField.{u, max v w}
    (ULift.algEquiv (R := Λ) (A := k) : ULift.{v} k ≃ₐ[Λ] k)
  let : U.IsEquivalence := Functor.IsEquivalence.mk
  let J := G ⋙ uliftFunctor.{y, x}
  have hJ : SatisfiesRS (CategoryOfElements.π J) :=
    satisfiesRS_of_equiv (fun _ ↦ Equiv.ulift) (fun _ _ ↦ rfl) hG.2
  refine ⟨?_, satisfiesRS_precomp U (fun _ hf ↦ hf) J hJ⟩
  let := hG.1.some
  let e := (G.mapIso (liftedResidueFieldIso.{u, v, w} (Λ := Λ) (k := k))).toEquiv
  refine ⟨?_⟩
  show Unique (ULift.{y} (G.obj (U.obj
    (residueFieldObject.{u, max v w, max v w} Λ (ULift.{v} k)))))
  exact (Equiv.ulift.{y, x}.trans e).unique

/-! ### Schlessinger's theorem -/

/-- Schlessinger's criterion, for a functor whose values lie in a universe unrelated to the
morphism universe of `𝒞_Λ`: such a functor is prorepresentable, after raising both sides to a
common universe, exactly when it is a deformation functor whose tangent space is a
finite-dimensional `k`-vector space on which the derivation map is injective. -/
@[sga "7 VI 1.11" "(i), special case"]
public theorem isProrepresentableULift_iff_isDeformationFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type x) :
    IsProrepresentableULift F ↔
      ∃ hF : IsDeformationFunctor F,
        let p := CategoryOfElements.π F
        let 𝓕 := BasedCategory.ofFunctor p
        let hD := (isDeformationCategory_iff F).2 hF
        let hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
          𝓕 hD
        letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
        letI : Fact (SchlessingerConditionS2
          (CategoryOfElements.π
            (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
        let T := tangentSpaceArtinian Λ k
          (isomorphismClasses 𝓕 hD.predeformation.cofibered)
        letI : AddCommGroup T := associatedTangentSpaceAddCommGroup 𝓕
        letI : Module k T := associatedTangentSpaceModule 𝓕
        FiniteDimensional k T ∧
          Function.Injective (derivationToTangentSpace p hD.predeformation) := by
  constructor
  · rintro ⟨R, ⟨e⟩⟩
    let E : ∀ A, F.obj A ≃ (restrictedCoyoneda R).obj A :=
      fun A ↦ Equiv.ulift.symm.trans ((e.app A).toEquiv.trans Equiv.ulift)
    have hE {A B} (f : A ⟶ B) (a : F.obj A) :
        E B (F.map f a) = (restrictedCoyoneda R).map f (E A a) :=
      congrArg (fun g : (F ⋙ uliftFunctor.{max v w, x}).obj A ⟶
          (restrictedCoyoneda R ⋙ uliftFunctor.{x, max v w}).obj B ↦
        (g (show (F ⋙ uliftFunctor.{max v w, x}).obj A from ⟨a⟩)).down) (e.hom.naturality f)
    have hF : IsDeformationFunctor F := by
      refine ⟨?_, satisfiesRS_of_equiv E hE (restrictedCoyoneda_satisfiesRS R)⟩
      let := (restrictedCoyoneda_isPredeformationFunctor R).some
      exact ⟨(E _).unique⟩
    refine ⟨hF, ?_, ?_⟩
    · let hD := (isDeformationCategory_iff F).2 hF
      exact finiteDimensional_tangentSpace_of_equiv F hD.predeformation
        (Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory _ hD) R E hE
    · exact derivationToTangentSpace_injective_of_equiv F
        ((isDeformationCategory_iff F).2 hF).predeformation
        R E hE
  · rintro ⟨hF, hfinite, hinj⟩
    let 𝓕 := BasedCategory.ofFunctor (CategoryOfElements.π F)
    have hD := (isDeformationCategory_iff F).2 hF
    let : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨hD.predeformation⟩
    let : Fact (SchlessingerConditionS2 (CategoryOfElements.π
        (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
      ⟨Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD⟩
    let : FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k
        (isomorphismClasses 𝓕 hD.predeformation.cofibered)) := hfinite
    obtain ⟨ξ, hξ, horbits⟩ :=
      exists_minimalVersal_hasBijectiveDifferentialOnDerivationOrbits Λ k
        𝓕 hD.predeformation (schlessingerConditionS1_of_satisfiesRS hF.2)
        (schlessingerConditionS2_of_satisfiesRS hF.2) inferInstance
    let P := chosenPushforwardsOfCofibered (CategoryOfElements.π F) hD.predeformation.cofibered
    have hsmooth := hξ.1 P
    have hfree := derivationAction_free F hD.predeformation
      (Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD) hinj
    have hbij := associatedMap_bijective_of_derivationAction_free
      (CategoryOfElements.π F) hD.predeformation ξ horbits hfree P
    let φ := (associatedMorphism hD.predeformation.cofibered ξ P).toBasedFunctor
    have hpoint : Function.Bijective (basedMapOnElements φ (artinianDualNumbers Λ k)) := by
      have hcomp : (fun a ↦ mapIsomorphismClasses
          (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base))
          hD.predeformation.cofibered φ (artinianDualNumbers Λ k)
          (elementClass (restrictedCoyoneda ξ.base) _ a)) =
          (elementClass F _) ∘ basedMapOnElements φ _ :=
        funext fun a ↦ basedMapOnElements_class φ _ a
      rw [hcomp] at hbij
      exact hbij.of_comp_left (elementClass_bijective F _).injective
    let H := restrictedCoyoneda ξ.base
    let H' := H ⋙ uliftFunctor.{x, max v w}
    let F' := F ⋙ uliftFunctor.{max v w, x}
    let α : H' ⟶ F' :=
      { app := fun A ↦ ↾(fun a ↦ ULift.up (basedMapOnElements φ A a.down))
        naturality := fun A B f ↦ by
          ext a
          exact congrArg ULift.up (basedMapOnElements_natural φ f a.down) }
    let U := changeResidueField.{u, max v w}
      (ULift.algEquiv (R := Λ) (A := k) : ULift.{v} k ≃ₐ[Λ] k)
    let : U.IsEquivalence := Functor.IsEquivalence.mk
    let β := Functor.whiskerLeft U α
    have hβ : IsSmooth (elementsBasedFunctor β) := by
      apply isSmooth_of_lifts
      intro B A f hf a b hab
      obtain ⟨c, hc, hφc⟩ := basedMapOnElements_lifts φ hsmooth (U.map f) hf
        a.down b.down (congrArg ULift.down hab)
      exact ⟨ULift.up c, congrArg ULift.up hc, congrArg ULift.up hφc⟩
    have hdβ : Function.Bijective
        (β.app (augmentedDualNumbers (Λ := Λ) (k := ULift.{v} k))) := by
      have hb := natural_bijective_of_iso (basedMapOnElements φ)
        (fun f a ↦ basedMapOnElements_natural φ f a)
        (liftedDualNumbersIso.{u, v, w} (Λ := Λ) (k := k)) hpoint
      exact Equiv.ulift.symm.bijective.comp (hb.comp Equiv.ulift.bijective)
    have : IsIso β := isIso_of_isSmooth_of_tangent_bijective
      (isDeformationFunctor_lifted H ⟨restrictedCoyoneda_isPredeformationFunctor ξ.base,
        restrictedCoyoneda_satisfiesRS ξ.base⟩) (isDeformationFunctor_lifted F hF) β hβ hdβ
    have : IsIso α := by
      apply (NatTrans.isIso_iff_isIso_app α).2
      intro A
      apply (NatTrans.isIso_app_iff_of_iso α (U.objObjPreimageIso A)).1
      exact inferInstanceAs (IsIso (β.app (U.objPreimage A)))
    exact ⟨ξ.base, ⟨(asIso α).symm⟩⟩

/-- **Schlessinger's theorem.** A set-valued functor on the category of Artinian local
`Λ`-algebras with residue field `k` is prorepresentable exactly when it is a deformation
functor, its tangent space is a finite-dimensional `k`-vector space, and the canonical map
from the `Λ`-derivations of `k` to that tangent space is injective. -/
@[stacks 06JM, sga "7 VI 2.18"]
public theorem isProrepresentable_iff_isDeformationFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w)) :
    IsProrepresentable F ↔
      ∃ hF : IsDeformationFunctor F,
        let p := CategoryOfElements.π F
        let 𝓕 := BasedCategory.ofFunctor p
        let hD := (isDeformationCategory_iff F).2 hF
        let hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
          𝓕 hD
        letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
        letI : Fact (SchlessingerConditionS2
          (CategoryOfElements.π
            (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
        let T := tangentSpaceArtinian Λ k
          (isomorphismClasses 𝓕 hD.predeformation.cofibered)
        letI : AddCommGroup T := associatedTangentSpaceAddCommGroup 𝓕
        letI : Module k T := associatedTangentSpaceModule 𝓕
        FiniteDimensional k T ∧
          Function.Injective (derivationToTangentSpace p hD.predeformation) :=
  (isProrepresentableULift_iff F).symm.trans
    (isProrepresentableULift_iff_isDeformationFunctor.{u, v, w, max v w} F)

end Deformation
