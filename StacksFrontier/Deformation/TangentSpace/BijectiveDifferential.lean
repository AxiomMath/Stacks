module

public import Mathlib.RingTheory.Derivation.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.FormalObject.YonedaEquivalence
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.TangentSpace.Derivations
public import StacksFrontier.Deformation.TangentSpace.Predeformation

/-!
# The differential of a formal object, and when it is bijective (Stacks 06IM)

Let `p : F ⥤ 𝒞_Λ` be cofibered in groupoids and let `ξ` be a formal object of `p`. The
morphism associated to `ξ` by Tag 06HC goes from the category of elements of the functor
prorepresented by `ξ.base` to `F`, and it induces a map on the associated
isomorphism-class functors. Evaluating that map at the dual numbers, and identifying the
source with `Λ`-derivations of `ξ.base` by Tag 06IC, gives the **differential of `ξ`**:
a map from derivations of the complete local algebra to the tangent space of `p`.

Writing the associated morphism down requires a choice of pushforwards, but the induced
map on isomorphism classes does not depend on it: two choices give associated morphisms
that are isomorphic as based functors, by the Tag 06SK Yoneda equivalence, and isomorphic
based functors induce the same map on isomorphism classes. So the bijectivity of the
differential is an intrinsic condition on `ξ`, which is what `HasBijectiveDifferential`
records.

In the universe where the direct tangent-space model of Tag 06II lives — the dual numbers
built on `k` itself rather than on `ULift k` — the two models are identified by the
image under the square-zero extension functor of `ULift.moduleEquiv`, and the condition
is exactly bijectivity of the Tag 06II differential.

## Main definitions

* `Deformation.derivationToTangent`: the differential of a formal object, for a given
  choice of pushforwards.
* `Deformation.HasBijectiveDifferential`: **Stacks 06IM**, the intrinsic bijectivity
  condition.

## Main results

* `Deformation.mapIsomorphismClasses_eq_of_iso`: isomorphic based functors induce the same
  map on isomorphism classes.
* `Deformation.derivationToTangent_independent`: the differential does not depend on the
  choice of pushforwards.
* `Deformation.hasBijectiveDifferential_iff_differential_bijective`: in the direct model,
  the condition is bijectivity of `Deformation.differential`.
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w uF vF u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- The map from derivations of the base ring to tangent vectors of the
predeformation category determined by a formal object. -/
public noncomputable def derivationToTangent
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ : Deformation.FormalObject p)
    (pushforwards : Deformation.ChosenPushforwards p) :
    letI : Algebra ξ.base k :=
      (Deformation.residueHom ξ.base).toRingHom.toAlgebra
    Derivation Λ ξ.base k →
      Deformation.tangentSpaceArtinian Λ k
        (Deformation.isomorphismClasses (BasedCategory.ofFunctor p) hp) := by
  letI : Algebra ξ.base k :=
    (Deformation.residueHom ξ.base).toRingHom.toAlgebra
  intro d
  let x := (Deformation.tangentSpaceDerivationsLinearEquiv
    ξ.base).symm d
  let φ := Deformation.associatedMorphism
    hp ξ pushforwards
  exact Deformation.mapIsomorphismClasses
    (Deformation.categoryOfElements_projection_isCofibered
      (Deformation.restrictedCoyoneda ξ.base)) hp φ.toBasedFunctor
    (Deformation.artinianDualNumbers Λ k)
    (Deformation.classOf
      (BasedCategory.ofFunctor
        (Functor.Elements.π (Deformation.restrictedCoyoneda ξ.base)))
      (Deformation.categoryOfElements_projection_isCofibered
        (Deformation.restrictedCoyoneda ξ.base))
      ⟨(Deformation.restrictedCoyoneda ξ.base).elementsMk
        (Deformation.artinianDualNumbers Λ k) x, rfl⟩)

/-- **Stacks Project, Tag 06IM.** The differential of the morphism associated
to a formal object is bijective from `Λ`-derivations to its tangent space. -/
@[stacks 06IM]
public def HasBijectiveDifferential
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ : Deformation.FormalObject p) : Prop :=
  ∃ pushforwards : Deformation.ChosenPushforwards p,
    Function.Bijective (derivationToTangent hp ξ pushforwards)

private noncomputable def associatedMorphisms_iso
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ : Deformation.FormalObject p)
    (P Q : Deformation.ChosenPushforwards p) :
    (Deformation.associatedMorphism hp ξ P).toBasedFunctor ≅
      (Deformation.associatedMorphism hp ξ Q).toBasedFunctor := by
  let E := Deformation.representableMorphismFormalObjectEquivalence p hp ξ.base
  let φ := (Deformation.associatedMorphism hp ξ P).toBasedFunctor
  let ψ := (Deformation.associatedMorphism hp ξ Q).toBasedFunctor
  let eφ := Classical.choice
    (Deformation.associatedMorphism_maps_to hp ξ E P)
  let eψ := Classical.choice
    (Deformation.associatedMorphism_maps_to hp ξ E Q)
  exact (E.equivalence.unitIso.app φ) ≪≫
    E.equivalence.inverse.mapIso (eφ ≪≫ eψ.symm) ≪≫
    (E.equivalence.unitIso.app ψ).symm

/-- Isomorphic based functors induce the same map on isomorphism classes over every object of
the base: the comparison 2-cell is vertical, so it is an isomorphism inside each fibre. -/
public theorem mapIsomorphismClasses_eq_of_iso
    {C : Type u} [Category.{v} C]
    {𝓕 : BasedCategory.{v₁, u₁} C} {𝓖 : BasedCategory.{v₂, u₂} C}
    (h𝓕 : Deformation.IsCofiberedInGroupoids 𝓕.p)
    (h𝓖 : Deformation.IsCofiberedInGroupoids 𝓖.p)
    (φ ψ : BasedFunctor 𝓕 𝓖) (i : φ ≅ ψ) (A : C) :
    Deformation.mapIsomorphismClasses h𝓕 h𝓖 φ A =
      Deformation.mapIsomorphismClasses h𝓕 h𝓖 ψ A := by
  funext z
  obtain ⟨x, rfl⟩ := Deformation.classOf_surjective 𝓕 h𝓕 A z
  rw [Deformation.mapIsomorphismClasses_classOf, Deformation.mapIsomorphismClasses_classOf]
  exact Deformation.classOf_eq_of_isIsomorphic 𝓖 h𝓖 _ _
    ⟨⟨⟨i.hom.toNatTrans.app x.1, i.hom.isHomLift x.2⟩,
      ⟨i.inv.toNatTrans.app x.1, i.inv.isHomLift x.2⟩,
      Subtype.ext (congrArg (fun α : φ ⟶ φ => α.toNatTrans.app x.1) i.hom_inv_id),
      Subtype.ext (congrArg (fun α : ψ ⟶ ψ => α.toNatTrans.app x.1) i.inv_hom_id)⟩⟩

private noncomputable def dualNumberModelIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    Deformation.artinianDualNumbers.{u, w, w} Λ k ≅
      Deformation.augmentedDualNumbers (Λ := Λ) (k := k) :=
  (Deformation.squareZeroExtensionArtinian Λ k).mapIso
    (ULift.moduleEquiv : ULift.{w} k ≃ₗ[k] k).toFGModuleCatIso

private noncomputable def tangentModelEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : Deformation.ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ Type u₂) :
    Deformation.tangentSpaceArtinian Λ k F ≃ Deformation.artinianTangentSpace Λ k F := by
  change F.obj (Deformation.artinianDualNumbers.{u, w, w} Λ k) ≃
    F.obj (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))
  exact Equiv.ofBijective (F.map dualNumberModelIso.hom)
    (ConcreteCategory.bijective_of_isIso (F.mapIso dualNumberModelIso).hom)

private theorem bijective_iff_equiv_conjugate
    {α β γ δ : Type*} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
    (f : α → γ) (g : β → δ) (h : e₂ ∘ f = g ∘ e₁) :
    Function.Bijective f ↔ Function.Bijective g := by
  rw [← Equiv.comp_bijective f e₂, h, Equiv.bijective_comp]

private noncomputable def elementsClassEquiv
    {C : Type u} [Category.{v} C] {F : C ⥤ Type w} (A : C)
    (h : Deformation.IsCofiberedInGroupoids (Functor.Elements.π F)) :
    F.obj A ≃
      (Deformation.isomorphismClasses
        (BasedCategory.ofFunctor (Functor.Elements.π F)) h).obj A := by
  let B := BasedCategory.ofFunctor (Functor.Elements.π F)
  let point (x : F.obj A) :=
    Deformation.classOf B h ⟨F.elementsMk A x, rfl⟩
  refine Equiv.ofBijective point ⟨?_, ?_⟩
  · intro x y hxy
    let fx : Functor.Fiber (Functor.Elements.π F) A := ⟨F.elementsMk A x, rfl⟩
    let fy : Functor.Fiber (Functor.Elements.π F) A := ⟨F.elementsMk A y, rfl⟩
    obtain ⟨i⟩ := Quotient.exact (((Deformation.classOf_eq B h fx).symm.trans
      (congrArg (Equiv.cast (Deformation.isomorphismClasses_obj B h A)) hxy)).trans
      (Deformation.classOf_eq B h fy))
    have hbase : i.hom.val.hom = 𝟙 A := by
      have : (Functor.Elements.π F).IsHomLift (𝟙 A) i.hom.val := i.hom.property
      have hfac := IsHomLift.fac' (p := Functor.Elements.π F) (R := A) (S := A) (𝟙 A) i.hom.val
      exact hfac.trans (by rw [Category.id_comp, eqToHom_trans]; rfl)
    have hval := i.hom.val.map_val
    change F.map (i.hom.val.hom) x = y at hval
    rw [hbase] at hval
    exact (Functor.map_id_apply F A x).symm.trans hval
  · intro z
    obtain ⟨x, hx⟩ := Deformation.classOf_surjective B h A z
    rcases x with ⟨@⟨A', x⟩, hA⟩
    change A' = A at hA
    cases hA
    exact ⟨x, hx⟩

/-- The tangent map of a formal object is independent of the pushforwards used
to present its associated morphism. -/
public theorem derivationToTangent_independent
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ : Deformation.FormalObject p)
    (P Q : Deformation.ChosenPushforwards p) :
    derivationToTangent hp ξ P = derivationToTangent hp ξ Q := by
  let : Algebra ξ.base k := (Deformation.residueHom ξ.base).toRingHom.toAlgebra
  funext d
  exact congrFun (mapIsomorphismClasses_eq_of_iso
    (Deformation.categoryOfElements_projection_isCofibered (Deformation.restrictedCoyoneda ξ.base))
    hp _ _ (associatedMorphisms_iso hp ξ P Q) (Deformation.artinianDualNumbers Λ k)) _

/-- In the direct tangent-space model, the condition is exactly bijectivity of
the differential of the associated morphism. -/
public theorem hasBijectiveDifferential_iff_differential_bijective
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, w, w} Λ k}
    (hp : Deformation.IsCofiberedInGroupoids p)
    (ξ : Deformation.FormalObject p)
    (pushforwards : Deformation.ChosenPushforwards p) :
    HasBijectiveDifferential hp ξ ↔
      Function.Bijective
        (Deformation.differential
          (Deformation.categoryOfElements_projection_isCofibered
            (Deformation.restrictedCoyoneda ξ.base)) hp
        (Deformation.associatedMorphism
            hp ξ pushforwards).toBasedFunctor) := by
  let : Algebra ξ.base k :=
    (Deformation.residueHom ξ.base).toRingHom.toAlgebra
  let e :=
    (Deformation.tangentSpaceDerivationsLinearEquiv ξ.base).toEquiv
  let hsource := Deformation.categoryOfElements_projection_isCofibered
    (Deformation.restrictedCoyoneda ξ.base)
  let Fsource := Deformation.isomorphismClasses
    (BasedCategory.ofFunctor (Functor.Elements.π (Deformation.restrictedCoyoneda ξ.base)))
    hsource
  let Ftarget := Deformation.isomorphismClasses (BasedCategory.ofFunctor p) hp
  let esource := tangentModelEquiv Fsource
  let etarget := tangentModelEquiv Ftarget
  let epoint := elementsClassEquiv (Deformation.artinianDualNumbers Λ k) hsource
  let dom := e.symm.trans (epoint.trans esource)
  let φ := (Deformation.associatedMorphism
    hp ξ pushforwards).toBasedFunctor
  have hcomparison : etarget ∘ derivationToTangent hp ξ pushforwards =
      Deformation.differential hsource hp φ ∘ dom := by
    funext d
    let z := Deformation.classOf
      (BasedCategory.ofFunctor (Functor.Elements.π (Deformation.restrictedCoyoneda ξ.base)))
      hsource ⟨(Deformation.restrictedCoyoneda ξ.base).elementsMk
        (Deformation.artinianDualNumbers Λ k) (e.symm d), rfl⟩
    change Ftarget.map dualNumberModelIso.hom
        (Deformation.mapIsomorphismClasses hsource hp φ
          (Deformation.artinianDualNumbers Λ k) z) =
      Deformation.mapIsomorphismClasses hsource hp φ
        (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))
        (Fsource.map dualNumberModelIso.hom z)
    exact (Deformation.mapIsomorphismClasses_naturality
      (h𝓕 := hsource) (h𝓖 := hp) (φ := φ) dualNumberModelIso.hom z).symm
  have hbijiff := bijective_iff_equiv_conjugate dom etarget
    (derivationToTangent hp ξ pushforwards)
    (Deformation.differential hsource hp φ) hcomparison
  exact ⟨fun ⟨P, hP⟩ => hbijiff.mp
      (by rwa [← derivationToTangent_independent hp ξ P pushforwards]),
    fun h => ⟨pushforwards, hbijiff.mpr h⟩⟩

end Deformation
