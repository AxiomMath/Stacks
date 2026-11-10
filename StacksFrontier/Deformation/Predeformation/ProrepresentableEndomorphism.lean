module

public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Formal.Groupoid.LimitPreserving
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.TangentSpace.FunctorMap
public import StacksFrontier.Deformation.VersalObject.MinimalVersalDescent
public import StacksFrontier.RingTheory.Noetherian.Endomorphism

/-!
# Endomorphisms of prorepresentable functors (Stacks 06KP)

An endomorphism `φ : U ⟶ U` of a prorepresentable functor on Artinian local `Λ`-algebras
whose differential `dφ : TU → TU` is bijective is itself an isomorphism.

The proof is the one in the source. Writing `U ≅ \underline{R}|_{𝒞_Λ}` for a Noetherian
complete local algebra `R`, the endomorphism transports to an endomorphism `ψ` of the
restricted representable functor. Restriction to Artinian algebras is fully faithful on
limit-preserving functors — its left adjoint is completion and the counit is an isomorphism
by Stacks 06HB — so `ψ` is the restriction of an endomorphism of the corepresentable functor
of `R` on all of `\widehat{𝒞}_Λ`, hence by Yoneda is precomposition with a morphism
`f : R ⟶ R`. Bijectivity of the differential makes restriction of residue-field-valued
derivations along `f` injective, so `f` is surjective by Stacks 06SD, hence bijective because
a surjective endomorphism of a Noetherian ring is injective, hence an isomorphism; and then
so are `ψ` and `φ`.

## Main results

* `Deformation.isIso_of_tangentSpace_bijective`: **Stacks 06KP**.

## Implementation notes

The tangent space of a functor is its value on the dual numbers, so the differential of a
natural endomorphism is its component there. The dual numbers are taken in an arbitrary
carrier universe containing the residue field, so the criterion applies to prorepresentable
functors in all of those universes; bijectivity of the component expresses that the
differential is an isomorphism of tangent spaces without choosing an inverse.

## References

* [Stacks Project, Tag 06KP](https://stacks.math.columbia.edu/tag/06KP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Stacks Project, Tag 06KP.** An endomorphism of a prorepresentable functor on Artinian
local `Λ`-algebras whose differential — its component at the dual numbers — is bijective is an
isomorphism. -/
@[stacks 06KP]
theorem isIso_of_tangentSpace_bijective
    (U : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w))
    (hU : IsProrepresentable U) (φ : U ⟶ U)
    (hφ : Function.Bijective (φ.app (artinianDualNumbers Λ k))) :
    IsIso φ := by
  obtain ⟨R, ⟨e⟩⟩ := hU
  let G : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w) := restrictedCoyoneda R
  let ψ : G ⟶ G := e.inv ≫ φ ≫ e.hom
  let X := artinianDualNumbers.{u, w, v} Λ k
  have hψbij : Function.Bijective (ψ.app X) := by
    change Function.Bijective
      ((ConcreteCategory.hom (e.hom.app X)) ∘ (ConcreteCategory.hom (φ.app X)) ∘
        (ConcreteCategory.hom (e.inv.app X)))
    exact ((isIso_iff_bijective (e.hom.app X)).mp inferInstance).comp
      (hφ.comp ((isIso_iff_bijective (e.inv.app X)).mp inferInstance))
  let Gc : CompleteLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w) :=
    coyoneda.obj (Opposite.op R)
  let cIso : (cofiberedCompletion (Λ := Λ) (k := k)).obj G ≅ Gc :=
    cofiberedCompletionRestrictionIso Gc
  let adj := cofiberedCompletionAdjunction (Λ := Λ) (k := k)
  let ψc := (cofiberedCompletion (Λ := Λ) (k := k)).map ψ
  let θ : Gc ⟶ Gc := cIso.inv ≫ ψc ≫ cIso.hom
  let f : R ⟶ R := coyonedaEquiv θ
  have hθ : θ = coyoneda.map f.op := coyonedaEquiv.injective (coyonedaEquiv_coyoneda_map f).symm
  have htri : Functor.whiskerLeft artinianToComplete cIso.inv ≫ adj.counit.app G = 𝟙 G := by
    have hunit : cIso.inv = adj.unit.app Gc := by
      simp [adj, cIso]
    have ht := adj.left_triangle_components Gc
    rw [← hunit] at ht
    simpa [adj, G, Gc, restrictedCoyoneda] using ht
  have hcounit : Functor.whiskerLeft artinianToComplete ψc ≫ adj.counit.app G =
      adj.counit.app G ≫ ψ := by
    simpa [adj, ψc] using adj.counit.naturality ψ
  have htApp (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
      cIso.inv.app (artinianToComplete.obj A) ≫ (adj.counit.app G).app A = 𝟙 _ := by
    simpa [adj, G, Gc, restrictedCoyoneda] using congrArg (fun t => t.app A) htri
  have hεeq (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
      (adj.counit.app G).app A = cIso.hom.app (artinianToComplete.obj A) := by
    simpa using congrArg (cIso.hom.app (artinianToComplete.obj A) ≫ ·) (htApp A)
  have hψeq : ψ = restrictedCoyonedaMap f := by
    ext A x
    have hcp := congrArg (fun g => g (cIso.inv.app (artinianToComplete.obj A) x))
      (congrArg (fun t => t.app A) hcounit)
    have hEval : (adj.counit.app G).app A (cIso.inv.app (artinianToComplete.obj A) x) = x :=
      congrArg (fun g => g x) (htApp A)
    calc
      ψ.app A x = ψ.app A
          ((adj.counit.app G).app A (cIso.inv.app (artinianToComplete.obj A) x)) := by
        rw [hEval]
      _ = (adj.counit.app G).app A
          (ψc.app (artinianToComplete.obj A)
            (cIso.inv.app (artinianToComplete.obj A) x)) := by simpa using hcp.symm
      _ = (restrictedCoyonedaMap f).app A x := by
        rw [hεeq A]
        change θ.app (artinianToComplete.obj A) x = (restrictedCoyonedaMap f).app A x
        rw [hθ]
        rfl
  have htan : Function.Injective (tangentSpaceMapArtinian f) := by
    intro x y hxy
    apply hψbij.1
    rw [hψeq]
    refine CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun z => ?_)
    rw [tangentSpaceMapArtinian_apply, tangentSpaceMapArtinian_apply] at hxy
    change (x.hom.comp f.hom) z = (y.hom.comp f.hom) z
    exact congrArg (fun g : R ⟶ artinianToComplete.obj X => g.hom z) hxy
  have hresidueAlgebra := congrArg
    (fun q : R →ₐ[Λ] k => q.toRingHom.toAlgebra) (residueAlgHom_eq_residueHom R)
  cases hresidueAlgebra
  let : Algebra R k := (residueAlgHom R).toRingHom.toAlgebra
  let ER := tangentSpaceDerivationsLinearEquiv R
  have hcomap : Function.Injective (ResidueDerivation.comap f) := by
    intro d₁ d₂ hd
    have hxy : tangentSpaceMapArtinian f (ER.symm d₁) =
        tangentSpaceMapArtinian f (ER.symm d₂) := by
      refine ER.injective (DFunLike.ext _ _ fun r => ?_)
      rw [tangentSpaceMapArtinian_apply, tangentSpaceMapArtinian_apply]
      change (tangentSpaceDerivationsLinearEquiv R (f ≫ ER.symm d₁)) r =
        (tangentSpaceDerivationsLinearEquiv R (f ≫ ER.symm d₂)) r
      rw [tangentSpaceDerivationsLinearEquiv_precomp,
        tangentSpaceDerivationsLinearEquiv_precomp, ER.apply_symm_apply d₁,
        ER.apply_symm_apply d₂]
      exact congrArg (fun d : ResidueDerivation R => d r) hd
    exact ER.symm.injective (htan hxy)
  have : IsIso f := CompleteLocalAlgCat.isIso_of_bijective_hom f
    (surjective_endomorphism_noetherian_bijective R f.hom.toRingHom
      (surjective_of_residueDerivation_comap_injective f hcomap))
  have hcomp (g h : R ⟶ R) : restrictedCoyonedaMap (g ≫ h) =
      restrictedCoyonedaMap h ≫ restrictedCoyonedaMap g := by
    ext A x
    rfl
  have hid : restrictedCoyonedaMap (𝟙 R) = 𝟙 _ := by
    ext A x
    rfl
  have : IsIso ψ := by
    rw [hψeq]
    exact ⟨restrictedCoyonedaMap (inv f), by rw [← hcomp, IsIso.inv_hom_id, hid],
      by rw [← hcomp, IsIso.hom_inv_id, hid]⟩
  rw [show φ = e.hom ≫ ψ ≫ e.inv by simp [ψ]]
  infer_instance

end Deformation

end
