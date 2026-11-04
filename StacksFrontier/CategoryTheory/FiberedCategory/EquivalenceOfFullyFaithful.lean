module

public import StacksFrontier.CategoryTheory.FiberedCategory.BasedFunctorWhiskering
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A fully faithful functor over a base, surjective up to vertical isomorphism, is an equivalence

Let `Θ : 𝒳 ⥤ᵇ 𝒴` be a functor of categories over `𝒮` whose underlying functor is fully faithful,
and suppose that every object `y` of `𝒴` is isomorphic to some `Θ x` by an isomorphism lying
over an identity of `𝒮`. Then `Θ` is an equivalence of categories over `𝒮`
(`CategoryTheory.BasedCategory.Equivalence`): the inverse sends `y` to the chosen `x`, a
morphism to the preimage of its conjugate by the chosen isomorphisms, and it commutes strictly
with the projections because the chosen isomorphisms lie over identities.

Consequently postcomposition with `Θ` is an equivalence of the categories of based functors
from any category over `𝒮`.

## Main definitions

* `CategoryTheory.BasedCategory.Equivalence.ofFullyFaithfulLift`: the equivalence over `𝒮`.

## Main results

* `CategoryTheory.BasedCategory.Equivalence.isEquivalence_postcompFunctor_of_fullyFaithful`:
  postcomposition with `Θ` is an equivalence of categories of based functors.
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

namespace BasedCategory.Equivalence

variable (Θ : 𝒳 ⥤ᵇ 𝒴) (hΘ : Θ.toFunctor.FullyFaithful) (x : 𝒴.obj → 𝒳.obj)
  (e : ∀ y, Θ.obj (x y) ≅ y) (he : ∀ y, 𝒴.p.IsHomLift (𝟙 (𝒴.p.obj y)) (e y).hom)

/-- The underlying functor of the inverse: `y ↦ x y`, and a morphism goes to the preimage of
its conjugate by the chosen isomorphisms. -/
def inverseFunctor : 𝒴.obj ⥤ 𝒳.obj where
  obj := x
  map {y y'} f := hΘ.preimage ((e y).hom ≫ f ≫ (e y').inv)
  map_id y := hΘ.map_injective (by simp)
  map_comp {y y' y''} f g := hΘ.map_injective (by simp)

/-- `Θ` sends the image of `f` under `inverseFunctor` to the conjugate of `f` by the chosen
isomorphisms. -/
theorem map_inverseFunctor {y y' : 𝒴.obj} (f : y ⟶ y') :
    Θ.map ((inverseFunctor Θ hΘ x e).map f) = (e y).hom ≫ f ≫ (e y').inv :=
  hΘ.map_preimage _

include he in
/-- The chosen object `x y` lies over the same object of `𝒮` as `y`. -/
theorem p_obj_x (y : 𝒴.obj) : 𝒳.p.obj (x y) = 𝒴.p.obj y :=
  (Θ.w_obj (x y)).symm.trans (IsHomLift.domain_eq 𝒴.p (𝟙 (𝒴.p.obj y)) (e y).hom)

include he in
/-- The image of `f` under `inverseFunctor` lies over `𝒴.p.map f`. -/
theorem isHomLift_inverseFunctor_map {y y' : 𝒴.obj} (f : y ⟶ y') :
    𝒳.p.IsHomLift (𝒴.p.map f) ((inverseFunctor Θ hΘ x e).map f) := by
  have h1 : 𝒴.p.IsHomLift (𝟙 (𝒴.p.obj y')) (e y').inv := by
    have := he y'
    infer_instance
  have h0 := he y
  have h2 : 𝒴.p.IsHomLift (𝒴.p.map f) (Θ.map ((inverseFunctor Θ hΘ x e).map f)) := by
    rw [map_inverseFunctor]
    exact IsHomLift.comp_lift_id_left' 𝒴.p (𝒴.p.obj y) (e y).hom (𝒴.p.map f) (f ≫ (e y').inv)
  exact BasedFunctor.isHomLift_map Θ (𝒴.p.map f) _

/-- The inverse, a functor over `𝒮`. -/
def basedInverse : 𝒴 ⥤ᵇ 𝒳 where
  toFunctor := inverseFunctor Θ hΘ x e
  w := by
    refine Functor.ext (fun y => p_obj_x Θ x e he y) (fun y y' f => ?_)
    have := isHomLift_inverseFunctor_map Θ hΘ x e he f
    exact IsHomLift.fac' 𝒳.p (𝒴.p.map f) ((inverseFunctor Θ hΘ x e).map f)

/-- **A fully faithful functor over `𝒮`, every object of whose target is vertically isomorphic
to an object of its image, is an equivalence over `𝒮`.** -/
@[ega "0 8.1.5" "more general"]
def ofFullyFaithfulLift : BasedCategory.Equivalence 𝒳 𝒴 where
  functor := Θ
  inverse := basedInverse Θ hΘ x e he
  unitIso := BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun a => hΘ.preimageIso (e (Θ.obj a))) (fun {a a'} g =>
      hΘ.map_injective (by
        change Θ.map (hΘ.preimage ((e (Θ.obj a)).hom ≫ Θ.map g ≫ (e (Θ.obj a')).inv) ≫
            hΘ.preimage (e (Θ.obj a')).hom) = Θ.map (hΘ.preimage (e (Θ.obj a)).hom ≫ g)
        rw [Functor.map_comp, Functor.map_comp, hΘ.map_preimage, hΘ.map_preimage,
          hΘ.map_preimage]
        simp)))
    (fun a => by
      change 𝒳.p.IsHomLift (𝟙 _) (hΘ.preimage (e (Θ.obj a)).hom)
      have h := he (Θ.obj a)
      rw [Θ.w_obj a] at h
      have h' : 𝒴.p.IsHomLift (𝟙 (𝒳.p.obj a)) (Θ.map (hΘ.preimage (e (Θ.obj a)).hom)) := by
        rw [hΘ.map_preimage]
        exact h
      exact BasedFunctor.isHomLift_map Θ _ _)
  counitIso := BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun y => e y) (fun {y y'} f => by
      change Θ.map (hΘ.preimage ((e y).hom ≫ f ≫ (e y').inv)) ≫ (e y').hom = (e y).hom ≫ f
      rw [hΘ.map_preimage]
      simp))
    (fun y => he y)

include hΘ e he in
/-- **Postcomposition with a fully faithful functor over `𝒮` which is surjective up to vertical
isomorphism is an equivalence of categories of based functors.** -/
@[sga "1 VI 4.5" "more general"]
theorem isEquivalence_postcompFunctor_of_fullyFaithful
    (𝒵 : BasedCategory.{v₄, u₄} 𝒮) :
    (BasedFunctor.postcompFunctor 𝒵 Θ).IsEquivalence :=
  (BasedCategory.Equivalence.ofFullyFaithfulLift Θ hΘ x e he).isEquivalence_postcompFunctor 𝒵

end BasedCategory.Equivalence

end CategoryTheory

end
