module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback

/-!
# The small étale site of the spectrum of an algebraically closed field

Let `T` be the object of the big fppf site over `S` given by the spectrum of an algebraically
closed field `k`. The identity chart is the terminal object of the small étale site of the
representable algebraic space `h_T`, and every covering sieve of it contains the identity: an
étale covering of `Spec k` has a member admitting a section, because an étale scheme over an
algebraically closed field is a disjoint union of copies of `Spec k`.

## Main results

* `AlgebraicGeometry.Space.idChart_mem_of_mem_geometricPoint`: every covering sieve of the
  identity chart of `h_T` contains the identity, for `T` the site object of a geometric point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The tautological geometric point of the representable presheaf of the site object of a
geometric point. -/
def GeometricPoint.tautological {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : GeometricPoint B S hS F) : GeometricPoint B S hS (yoneda.obj p.val.siteObject) :=
  ⟨{ carrier := p.val.carrier
     contained := p.val.contained
     toBase := p.val.toBase
     value := 𝟙 p.val.siteObject }, p.property⟩

/-- **Every covering sieve of the terminal chart of `h_T`, for `T` the spectrum of an
algebraically closed field, contains the identity.** The tautological lift of the geometric point
to the identity chart lifts further through any covering family, and such a further lift is a
section over the identity chart. -/
theorem idChart_mem_of_mem_geometricPoint {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : GeometricPoint B S hS F) {R : Sieve (idChart B S hS p.val.siteObject)}
    (hR : R ∈ SmallEtale.topology B S hS (yoneda.obj p.val.siteObject)
      (idChart B S hS p.val.siteObject)) :
    R.arrows (𝟙 _) := by
  let x := GeometricPoint.tautological B S hS p
  let Φ := etaleSitePoint B S hS (yoneda.obj p.val.siteObject) x
    (isAlgebraicSpace_yoneda B S hS p.val.siteObject)
  let x₀ : (geometricFiber B S hS (yoneda.obj p.val.siteObject) x).obj
      (idChart B S hS p.val.siteObject) := ⟨𝟙 _, rfl⟩
  obtain ⟨V, f, hf, y, hy⟩ := Φ.jointly_surjective R hR x₀
  let s : idChart B S hS p.val.siteObject ⟶ V :=
    ObjectProperty.homMk (CostructuredArrow.homMk y.1 (by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp]
      exact (congrArg (V.obj.hom.app _) (yonedaEquiv_yoneda_map y.1)).trans y.2))
  have hsf : s ≫ f = 𝟙 _ := (isTerminal_idChart B S hS p.val.siteObject).hom_ext _ _
  exact hsf ▸ R.downward_closed hf s

end AlgebraicGeometry.Space

end
