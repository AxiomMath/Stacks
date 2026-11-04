module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids

/-!
# Representability of the presheaf of isomorphism classes

Two facts about the presheaf `\overline{𝒮} : U ↦ Ob(𝒮_U)/≅` of isomorphism classes of a fibred
category.

The first is invariance: a pair of 1-morphisms over `𝒞` between categories fibred in groupoids
which are mutually inverse *on objects* induces an isomorphism of the two presheaves of
isomorphism classes.

The second compares two notions of representability: a representing object of the presheaf
`CategoryTheory.Functor.isoClassPresheaf` in the sense of `CategoryTheory.Functor.RepresentableBy`
is one in the sense of `StacksRepresentableCFG.IsoClassRepresentableBy`, a natural family of
bijections `Ob(𝒮_U)/≅ ≃ Mor_𝒞(U, X)` (Stacks 02Y3).

## Main results

* `CategoryTheory.Functor.isoClassPresheafIso`: the isomorphism of presheaves of isomorphism
  classes induced by 1-morphisms mutually inverse on objects.
* `StacksRepresentableCFG.isoClassRepresentableBy_of_representableBy`: a representing object for
  the presheaf `CategoryTheory.Functor.isoClassPresheaf` is a representing object in the sense of
  Stacks 02Y3.
-/

@[expose] public section

open Opposite CategoryTheory

universe u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{u₂} 𝒞] {𝒮 : Type u₂} [Category.{u₂} 𝒮] {𝒯 : Type u₂}
  [Category.{u₂} 𝒯]

/-- The presheaves of isomorphism classes of two categories fibred in groupoids over `𝒞` are
isomorphic as soon as there are 1-morphisms `Φ`, `Ψ` over `𝒞` between them which are mutually
inverse on objects. The two maps are `[x] ↦ [Φ x]` and `[z] ↦ [Ψ z]`
(`CategoryTheory.Functor.isoClassMap`). -/
noncomputable def isoClassPresheafIso {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} [p.IsFibered] [q.IsFibered]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    {Φ : 𝒮 ⥤ 𝒯} (hΦ : Φ ⋙ q = p) {Ψ : 𝒯 ⥤ 𝒮} (hΨ : Ψ ⋙ p = q)
    (hΨΦ : ∀ x : 𝒮, Ψ.obj (Φ.obj x) = x) (hΦΨ : ∀ z : 𝒯, Φ.obj (Ψ.obj z) = z) :
    p.isoClassPresheaf ≅ q.isoClassPresheaf where
  hom := isoClassMap (isFibredOneMorphism_of_isFiberedInGroupoids hq hΦ)
  inv := isoClassMap (isFibredOneMorphism_of_isFiberedInGroupoids hp hΨ)
  hom_inv_id := by
    ext V t
    induction t using _root_.Quotient.ind with
    | _ x =>
      exact congrArg (isoClassMk p) (Subtype.ext (by
        rw [fiberFunctorOfCompEq_obj_val, fiberFunctorOfCompEq_obj_val, hΨΦ]))
  inv_hom_id := by
    ext V t
    induction t using _root_.Quotient.ind with
    | _ z =>
      exact congrArg (isoClassMk q) (Subtype.ext (by
        rw [fiberFunctorOfCompEq_obj_val, fiberFunctorOfCompEq_obj_val, hΦΨ]))

end CategoryTheory.Functor

namespace StacksRepresentableCFG

variable {𝒞 : Type u₁} [Category.{u₂} 𝒞] {𝒮 : Type u₂} [Category.{u₃} 𝒮]

/-- A representing object for the presheaf of isomorphism classes, in the sense of
`CategoryTheory.Functor.RepresentableBy`, is a representing object in the sense of Stacks 02Y3,
with bijections the inverses of `homEquiv`. -/
def isoClassRepresentableBy_of_representableBy {p : 𝒮 ⥤ 𝒞} [p.IsFibered] {X : 𝒞}
    (h : p.isoClassPresheaf.RepresentableBy X) : IsoClassRepresentableBy p X where
  equiv U := (h.homEquiv (X := U)).symm
  naturality {U V} f x y hpb := by
    obtain ⟨φ, hφ, hsc⟩ := hpb
    have hy : Functor.isoClassMk p y = p.isoClassPresheaf.map f.op (Functor.isoClassMk p x) := by
      rw [Functor.isoClassPresheaf_map_isoClassMk]
      exact Functor.isoClassMk_eq_pullbackFiber_of_isCartesian f x y φ hφ inferInstance
    have hcomp : h.homEquiv (f ≫ h.homEquiv.symm (Functor.isoClassMk p x))
        = p.isoClassPresheaf.map f.op (Functor.isoClassMk p x) := by
      rw [h.homEquiv_comp, Equiv.apply_symm_apply]
    exact (Equiv.symm_apply_eq _).2 (hy.trans hcomp.symm)

end StacksRepresentableCFG
