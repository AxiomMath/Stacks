module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPullback

/-!
# The restriction of a quotient across the base change to a thickening

Let `(X ⟶ Y, F)` be the data of Stacks 082M and let `h : T ⟶ T'` be a morphism of test schemes
over `Y`, for instance the closed immersion of a first order thickening. The base-change map
`X_T ⟶ X_{T'}` carries `F_{T'}` to `F_T`: `F_{T'}|_{X_T} ≅ F_T`, the comparison of the two base
changes underlying the functoriality of the functor of quotients (Stacks 082N). This file records
that identification and reads the condition "the quotient `F_{T'} ⟶ F_{T'}/K'` restricts to the
quotient `F_T ⟶ F_T/K`" — the pullback of quotients of
`AlgebraicGeometry.Space.QuotientSituation.quotientPullback` — as a condition on the kernel of
the restricted projection `F_{T'}|_{X_T} ⟶ (F_{T'}/K')|_{X_T}`.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation.restrictBaseChangeModuleIso`: `F_{T'}|_{X_T} ≅ F_T`.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.quotientPullback_eq_iff`: the pullback of the
  quotient by `K'` along `h` is the quotient by `K` exactly when the kernel of the restricted
  projection is the image of `K` in `F_{T'}|_{X_T}`.

## References

* [Stacks Project, Tag 082N](https://stacks.math.columbia.edu/tag/082N)
* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type*} [Category C] [Abelian C]

/-- The kernel of `e ≫ g`, carried along the isomorphism `e`, is the kernel of `g`. -/
theorem Subobject.map_hom_kernelSubobject_iso_comp {A B Z : C} (e : A ≅ B) (g : B ⟶ Z) :
    (Subobject.map e.hom).obj (kernelSubobject (e.hom ≫ g)) = kernelSubobject g := by
  change (Subobject.map e.hom).obj (Subobject.mk (kernel.ι (e.hom ≫ g))) =
    Subobject.mk (kernel.ι g)
  rw [Subobject.map_mk]
  exact Subobject.mk_eq_mk_of_comm _ _ (kernelIsIsoComp e.hom g) (by simp)

/-- The image of a subobject `K ⊂ A` under a monomorphism `f : A ⟶ B` is `K` itself, as an
object. -/
noncomputable def Subobject.mapUnderlyingIso {A B : C} (f : A ⟶ B) [Mono f] (K : Subobject A) :
    ((Subobject.map f).obj K : C) ≅ (K : C) :=
  Subobject.isoOfEqMk _ (K.arrow ≫ f) (by
    conv_lhs => rw [← Subobject.mk_arrow K]
    exact Subobject.map_mk _ _)

omit [Abelian C] in
/-- The isomorphism `Subobject.mapUnderlyingIso f K`, followed by the inclusion of `K` and by `f`,
is the inclusion of the image subobject `(Subobject.map f).obj K`. -/
theorem Subobject.mapUnderlyingIso_hom_comp {A B : C} (f : A ⟶ B) [Mono f] (K : Subobject A) :
    (Subobject.mapUnderlyingIso f K).hom ≫ K.arrow ≫ f = ((Subobject.map f).obj K).arrow :=
  Subobject.ofLEMk_comp _

/-- Carrying a subobject `K ⊂ A` along an isomorphism `e : A ≅ B` does not change its quotient:
`B/e(K) ≅ A/K`. -/
noncomputable def Subobject.cokernelArrowMapIso {A B : C} (e : A ≅ B) (K : Subobject A) :
    cokernel ((Subobject.map e.hom).obj K).arrow ≅ cokernel K.arrow :=
  cokernel.mapIso _ _ (Subobject.mapUnderlyingIso e.hom K) e.symm (by
    rw [← Subobject.mapUnderlyingIso_hom_comp, Category.assoc, Category.assoc, Iso.symm_hom,
      Iso.hom_inv_id, Category.comp_id])

/-- The projection onto `B/e(K)` followed by `Subobject.cokernelArrowMapIso e K` is `e⁻¹`
followed by the projection onto `A/K`. -/
theorem Subobject.π_cokernelArrowMapIso_hom {A B : C} (e : A ≅ B) (K : Subobject A) :
    cokernel.π ((Subobject.map e.hom).obj K).arrow ≫ (Subobject.cokernelArrowMapIso e K).hom =
      e.inv ≫ cokernel.π K.arrow := by
  simp [Subobject.cokernelArrowMapIso, cokernel.mapIso]

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS) {T T' : SchemesOver D.Y} (h : T ⟶ T')

/-- **`F_{T'}|_{X_T} ≅ F_T`**: the inverse image of `F_{T'}` along the base-change map
`X_T ⟶ X_{T'}` of a morphism `T ⟶ T'` of test schemes is `F_T`, by the comparison of the two base
changes (`AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison`). -/
noncomputable def restrictBaseChangeModuleIso :
    (modulePullback B S hS (D.relativeMap h)).obj (D.baseChangeModule T') ≅
      D.baseChangeModule T :=
  ((D.baseChangeComparison h).app D.F).symm

/-- Shortcut: `F_T ≅ F_{T'}|_{X_T}` is a monomorphism (instance search times out without it). -/
instance (priority := high) mono_restrictBaseChangeModuleIso_inv :
    Mono (D.restrictBaseChangeModuleIso h).inv :=
  IsIso.mono_of_iso _

/-- **The restriction of a quotient of `F_{T'}` to `X_T` is a given quotient of `F_T`** exactly
when the kernel of `F_{T'}|_{X_T} ⟶ (F_{T'}/K')|_{X_T}` is the image of `K` under
`F_T ≅ F_{T'}|_{X_T}`. The left hand side is the functoriality of the functor of quotients of
Stacks 082N. -/
theorem quotientPullback_eq_iff (K' : Subobject (D.baseChangeModule T'))
    (K : Subobject (D.baseChangeModule T)) :
    D.quotientPullback h K' = K ↔
      Subobject.mk (kernel.ι ((modulePullback B S hS (D.relativeMap h)).map
        (cokernel.π K'.arrow))) = (Subobject.map (D.restrictBaseChangeModuleIso h).inv).obj K := by
  have key : (Subobject.map (D.restrictBaseChangeModuleIso h).inv).obj (D.quotientPullback h K') =
      Subobject.mk (kernel.ι ((modulePullback B S hS (D.relativeMap h)).map
        (cokernel.π K'.arrow))) :=
    Subobject.map_hom_kernelSubobject_iso_comp ((D.baseChangeComparison h).app D.F) _
  rw [← key]
  exact ⟨fun hK => hK ▸ rfl, fun hK => Subobject.map_obj_injective _ hK⟩

end QuotientSituation

end AlgebraicGeometry.Space

end
