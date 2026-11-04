module

public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentAffine
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# The global sections of an inverse adjoint transpose over an affine base

Let `φ : R ⟶ T` be a morphism of commutative rings, `F` a module on `Spec R` and `G` a module
on `Spec T`. A morphism `g : F ⟶ (Spec.map φ)_* G` has an inverse adjoint transpose
`θ = ((pullbackPushforwardAdjunction (Spec.map φ)).homEquiv F G).symm g`, a morphism
`(Spec.map φ)^* F ⟶ G`. The transpose is produced by an adjunction and so carries no formula,
while `g` is by assumption something one can compute with. This file transfers the formula
across the adjunction on global sections.

The transfer is immediate once the right objects are named. The defining property of the
transpose is `η_F ≫ (Spec.map φ)_* θ = g` for the unit `η` of the adjunction; global sections
of a direct image along `Spec.map φ` are global sections, so applying `Γ(-, ⊤)` to that equation
reads as `Γ(θ) ∘ Γ(η_F) = Γ(g)`, and `Γ(η_F)` is `Stacks.Sites.specSectionsMap`, which
`Stacks.Sites.sectionsPullbackIso_specSectionsMap` identifies with `m ↦ 1 ⊗ₜ m` under
`Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`. So `Γ(θ)` is, up to that
identification, the `T`-linear extension of `Γ(g)`, and in particular it is determined by `Γ(g)`.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.moduleSpecΓ_transpose_specSectionsMap`: the
  global sections of the transpose compose with the canonical map on sections to give the
  global sections of `g`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.moduleSpecΓ_transpose_tmul`: **the formula.**
  The global sections of the transpose send the section of the inverse image corresponding to
  `1 ⊗ₜ m` to `Γ(g) m`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.moduleSpecΓ_transpose_eq`: consequently the
  global sections of the transpose are any `T`-linear map extending `Γ(g)`, read through
  `sectionsPullbackIso`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension`: **the
  criterion.** If some `T`-linear map `T ⊗_R Γ(F, ⊤) ⟶ Γ(G, ⊤)` extending `Γ(g)` is invertible,
  then the transpose `θ` is invertible, both modules being quasi-coherent.

## Implementation notes

`Γ((Spec.map φ)_* N, ⊤)` and `Γ(N, ⊤)` are the same type but not the same expression, so a
composite in which that identification is implicit is not matched by `rw`. Every step below is
therefore taken on *elements* rather than on morphisms, exactly as in
`StacksFrontier/AlgebraicGeometry/Topologies/FpqcQuasicoherentAffine.lean`, and
`Stacks.AlgebraicGeometry.SectionsColimit.moduleSpecΓFunctor_map_pushforward_apply` is what
carries the identification.

The criterion is stated with the extension as an explicit argument rather than constructed from
`Γ(g)`, because the extension that arises in practice is already available as an isomorphism of
modules built from algebra, and asking for it in that form avoids proving that the canonically
constructed extension agrees with it.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct ChangeOfRings
open Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.TwistChartLocality

open Stacks.AlgebraicGeometry.SectionsColimit Stacks.Sites

variable {R T : CommRingCat.{u}} (φ : R ⟶ T) (F : (Spec R).Modules) (G : (Spec T).Modules)
  (g : F ⟶ (pushforward (Spec.map φ)).obj G)

/-- The inverse adjoint transpose of `g : F ⟶ (Spec.map φ)_* G`, a morphism
`(Spec.map φ)^* F ⟶ G`. -/
public def transpose : (pullback (Spec.map φ)).obj F ⟶ G :=
  ((pullbackPushforwardAdjunction (Spec.map φ)).homEquiv F G).symm g

/-- The defining property of the transpose: it is the unique morphism whose direct image,
preceded by the unit of the adjunction, is `g`. -/
public theorem unit_comp_pushforward_transpose :
    (pullbackPushforwardAdjunction (Spec.map φ)).unit.app F ≫
      (pushforward (Spec.map φ)).map (transpose φ F G g) = g := by
  have h := ((pullbackPushforwardAdjunction (Spec.map φ)).homEquiv F G).apply_symm_apply g
  rwa [Adjunction.homEquiv_unit] at h

/-- **The global sections of the transpose, on the image of the canonical map on sections.**
Applying `Γ(-, ⊤)` to the defining property of the transpose. -/
public theorem moduleSpecΓ_transpose_specSectionsMap (m : ToType (moduleSpecΓFunctor.obj F)) :
    moduleSpecΓFunctor.map (transpose φ F G g) (specSectionsMap φ F m) =
      moduleSpecΓFunctor.map g m := by
  have h := congrArg moduleSpecΓFunctor.map (unit_comp_pushforward_transpose φ F G g)
  rw [Functor.map_comp] at h
  have h2 := ConcreteCategory.congr_hom h m
  simp only [ConcreteCategory.comp_apply] at h2
  rw [moduleSpecΓFunctor_map_pushforward_apply] at h2
  exact h2

/-- **The global sections of the transpose, on a pure tensor.** Under the identification of the
global sections of the inverse image with `T ⊗_R Γ(F, ⊤)`, the transpose sends `1 ⊗ₜ m` to
`Γ(g) m`. -/
public theorem moduleSpecΓ_transpose_tmul [F.IsQuasicoherent]
    (m : ToType (moduleSpecΓFunctor.obj F)) :
    moduleSpecΓFunctor.map (transpose φ F G g)
        ((sectionsPullbackIso φ F).inv ((1 : T) ⊗ₜ[(R : Type u), φ.hom] m)) =
      moduleSpecΓFunctor.map g m := by
  have h : (sectionsPullbackIso φ F).inv ((1 : T) ⊗ₜ[(R : Type u), φ.hom] m) =
      specSectionsMap φ F m := by
    have h1 := sectionsPullbackIso_specSectionsMap φ F m
    refine Eq.trans (congrArg (ConcreteCategory.hom (sectionsPullbackIso φ F).inv) h1.symm) ?_
    exact ConcreteCategory.congr_hom (sectionsPullbackIso φ F).hom_inv_id _
  rw [h]
  exact moduleSpecΓ_transpose_specSectionsMap φ F G g m

/-- **The global sections of the transpose are any extension of the global sections of `g`.**
A `T`-linear map out of `T ⊗_R Γ(F, ⊤)` agreeing with `Γ(g)` on the pure tensors `1 ⊗ₜ m` is
the global sections of the transpose, read through `sectionsPullbackIso`. -/
public theorem moduleSpecΓ_transpose_eq [F.IsQuasicoherent]
    (e : (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj F) ⟶
      moduleSpecΓFunctor.obj G)
    (he : ∀ m : ToType (moduleSpecΓFunctor.obj F),
      e ((1 : T) ⊗ₜ[(R : Type u), φ.hom] m) = moduleSpecΓFunctor.map g m) :
    moduleSpecΓFunctor.map (transpose φ F G g) = (sectionsPullbackIso φ F).hom ≫ e := by
  have key : (sectionsPullbackIso φ F).inv ≫ moduleSpecΓFunctor.map (transpose φ F G g) = e := by
    refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
    refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
    exact Eq.trans (moduleSpecΓ_transpose_tmul φ F G g m) (he m).symm
  rw [← key, Iso.hom_inv_id_assoc]

/-- **The criterion.** If some `T`-linear map `T ⊗_R Γ(F, ⊤) ⟶ Γ(G, ⊤)` agreeing with `Γ(g)` on
the pure tensors `1 ⊗ₜ m` is invertible, then the inverse adjoint transpose of `g` is
invertible. Both modules are required to be quasi-coherent, invertibility on an affine scheme
being detected on global sections only there. -/
public theorem isIso_transpose_of_isIso_extension [F.IsQuasicoherent] [G.IsQuasicoherent]
    (e : (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj F) ⟶
      moduleSpecΓFunctor.obj G)
    (he : ∀ m : ToType (moduleSpecΓFunctor.obj F),
      e ((1 : T) ⊗ₜ[(R : Type u), φ.hom] m) = moduleSpecΓFunctor.map g m)
    [IsIso e] : IsIso (transpose φ F G g) := by
  refine AffineBaseChange.isIso_of_isIso_moduleSpecΓ _ ?_
  rw [moduleSpecΓ_transpose_eq φ F G g e he]
  infer_instance

end Stacks.AlgebraicGeometry.TwistChartLocality

end
