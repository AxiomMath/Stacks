module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.IsTensorProduct
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic

/-!
# Base change of the sections of a quasi-coherent module along an inclusion of affine opens

Let `F` be a quasi-coherent `𝒪_X`-module on a scheme `X` and let `V ≤ U` be affine opens.
Restriction

  `Γ(F, U) ⟶ Γ(F, V)`

exhibits the sections over `V` as the base change of the sections over `U`:

  `Γ(F, V) = Γ(X, V) ⊗_{Γ(X, U)} Γ(F, U)`.

This is the module content of [Stacks, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9) for an
inclusion of affine opens. For sheaves of algebras it gives a pushout square of commutative rings,
and through `Spec` a cartesian square of affine schemes.

## Main definitions

* `AlgebraicGeometry.affineRestrictSectionsBaseChangeIso`: the isomorphism
  `Γ(X, V) ⊗_{Γ(X, U)} Γ(F, U) ≅ Γ(F, V)` for affine opens `V ≤ U`.

## Main results

* `AlgebraicGeometry.affineRestrictSectionsBaseChangeIso_hom_one_tmul`: **the normalisation.**
  The isomorphism sends `1 ⊗ a` to the restriction of `a`, which identifies it as the canonical
  comparison.
* `AlgebraicGeometry.isBaseChange_restrict_of_isAffineOpen`: **the module form.** Restriction
  exhibits `Γ(F, V)` as the base change of `Γ(F, U)`.
* `AlgebraicGeometry.isPushout_sections_of_isAffineOpen` and
  `AlgebraicGeometry.isPushout_commRingCat_sections_of_isAffineOpen`: **the algebra form.** For
  commutative rings `A`, `B` identified with the two section groups as modules, with `A ⟶ B`
  restriction of sections, the square `Γ(X, U) → A`, `Γ(X, V) → B` is a pushout of commutative
  rings.
* `AlgebraicGeometry.isPullback_SpecMap_sections_of_isAffineOpen`: that pushout read through
  `Spec`, as a cartesian square of affine schemes.
* `AlgebraicGeometry.IsBaseChange.of_linearEquiv`: a base change transports along linear
  equivalences on both sides.
* `AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso`: an isomorphism out of
  `ModuleCat.extendScalars f`, normalized on `1 ⊗ m`, is a base change.

## Implementation notes

Two transparency hazards shape the statements.

First, the `R`-module structure that `ModuleCat.extendScalars f` puts on `S ⊗[R] M` is
`Module.compHom _ f`, which is only *definitionally* the structure coming from an `Algebra R S`
instance whose `algebraMap` is `f`. Comparing the two is cheap at abstract types and ruinous at a
concrete sheaf-section type — it exhausts the recursion limit, or the kernel's reduction budget,
on its own. So the comparison is isolated in
`AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso`, proved once at abstract types and
*applied*; for the same reason the transport along `eA` and `eB` is isolated in
`AlgebraicGeometry.IsBaseChange.of_linearEquiv` rather than done by `rw` at the sheaf types.

Second, the `Γ(X, U)`-algebra structure on `Γ(X, V)` and the `Γ(X, U)`-module structure on
`Γ(F, V)` are restrictions of scalars along the restriction maps of the structure sheaf, and are
not instances. They are taken as instance-implicit hypotheses together with the equations pinning
them down, in the shape a caller that has just built them by `RingHom.toAlgebra` or
`Module.compHom` supplies; the restriction map itself is a parameter pinned by its values, for the
same reason. The two rings of the algebra statement are likewise taken abstractly and related to
the section groups by linear equivalences: the section groups carry no ring structure as an
instance, and a caller has one only in whatever shape its own construction produced.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry

namespace ModuleCat

/-- **An isomorphism out of an extension of scalars exhibits its target as a base change.** If the
algebra structure of `S` over `R` is `f.toAlgebra` and `e : S ⊗[R, f] M ≅ N` sends `1 ⊗ m` to
`g m`, then `g` exhibits `N` as the base change of `M` to `S`. -/
public theorem isBaseChange_of_extendScalarsIso {R S M N : Type u} [CommRing R] [CommRing S]
    [inst : Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [Module R N] [IsScalarTower R S N] (f : R →+* S) (hf : inst = f.toAlgebra)
    (e : (ModuleCat.extendScalars f).obj (ModuleCat.of R M) ≅ ModuleCat.of S N)
    (g : M →ₗ[R] N) (he : ∀ m : M, e.hom ((1 : S) ⊗ₜ[R, f] m) = g m) :
    IsBaseChange S g := by
  subst hf
  let _ : Algebra R S := f.toAlgebra
  exact IsBaseChange.of_equiv e.toLinearEquiv he

end ModuleCat

/-- **A base change transports along linear equivalences on both sides.** If `ρ : M ⟶ N`
exhibits `N` as `S ⊗[R] M` and `g : M' ⟶ N'` agrees with `ρ` under linear equivalences
`M' ≃ M` and `N' ≃ N`, then `g` exhibits `N'` as `S ⊗[R] M'`. -/
public theorem IsBaseChange.of_linearEquiv {R S M M' N N' : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    {ρ : M →ₗ[R] N} (h : IsBaseChange S ρ) (eA : M' ≃ₗ[R] M) (eB : N' ≃ₗ[S] N)
    (g : M' →ₗ[R] N') (hg : ∀ m : M', eB (g m) = ρ (eA m)) :
    IsBaseChange S g := by
  refine IsBaseChange.of_equiv
    (((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) eA).trans h.equiv).trans
      eB.symm) (fun m => ?_)
  simp only [LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, IsBaseChange.equiv_tmul, one_smul]
  rw [← hg m, eB.symm_apply_apply]

variable {X : Scheme.{u}}

/-- Restriction along the identity morphism is restriction of sections. -/
public theorem Scheme.Hom.appLE_id (U V : X.Opens) (h : V ≤ (𝟙 X :) ⁻¹ᵁ U) (h' : V ≤ U) :
    Scheme.Hom.appLE (𝟙 X) U V h = X.presheaf.map (homOfLE h').op := rfl

variable (F : X.Modules) [F.IsQuasicoherent] {U V : X.Opens}

/-- **The sections of a quasi-coherent module over an inclusion of affine opens, as a base
change.** For affine opens `V ≤ U` of a scheme `X` and `F` quasi-coherent, extending the scalars
of `Γ(F, U)` along the restriction map `Γ(X, U) ⟶ Γ(X, V)` gives the sections of `F` over `V`.
This is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` for the identity morphism,
followed by the comparison of the pullback along `𝟙 X` with `F` itself. -/
public def affineRestrictSectionsBaseChangeIso
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ (𝟙 X :) ⁻¹ᵁ U) :
    (ModuleCat.extendScalars (Scheme.Hom.appLE (𝟙 X) U V hVU).hom).obj
        (ModuleCat.of Γ(X, U) Γ(F, U)) ≅ ModuleCat.of Γ(X, V) Γ(F, V) :=
  affinePullbackSectionsBaseChangeIso (𝟙 X) F hU hV hVU ≪≫
    (pullbackIdSectionsEquiv F V).toModuleIso

/-- **The normalisation.** `AlgebraicGeometry.affineRestrictSectionsBaseChangeIso` sends `1 ⊗ a`
to the restriction of the section `a`. -/
public theorem affineRestrictSectionsBaseChangeIso_hom_one_tmul
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ (𝟙 X :) ⁻¹ᵁ U) (hVU' : V ≤ U)
    (a : Γ(F, U)) :
    (affineRestrictSectionsBaseChangeIso F hU hV hVU).hom
        ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U), (Scheme.Hom.appLE (𝟙 X) U V hVU).hom] a) =
      F.presheaf.map (homOfLE hVU').op a :=
  (congrArg (fun t => pullbackIdSectionsEquiv F V t)
      (affinePullbackSectionsBaseChangeIso_one_tmul (𝟙 X) F hU hV hVU a)).trans
    (pullbackIdSectionsEquiv_pullbackSection F U V hVU hVU' a)

/-- **The sections of a quasi-coherent module on an affine open base change to the sections on a
smaller affine open.** This is the module half of Stacks Tag 01I9 for an inclusion of affine
opens: restriction `Γ(F, U) ⟶ Γ(F, V)` exhibits `Γ(F, V)` as `Γ(X, V) ⊗_{Γ(X, U)} Γ(F, U)`. -/
public theorem isBaseChange_restrict_of_isAffineOpen
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
    [inst : Algebra Γ(X, U) Γ(X, V)]
    (halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) Γ(X, V) r = X.presheaf.map (homOfLE hVU).op r)
    [Module Γ(X, U) Γ(F, V)] [IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, V))
    (hρ : ∀ a, ρ a = F.presheaf.map (homOfLE hVU).op a) :
    IsBaseChange Γ(X, V) ρ := by
  have hVU2 : V ≤ (𝟙 X :) ⁻¹ᵁ U := by simpa using hVU
  refine ModuleCat.isBaseChange_of_extendScalarsIso
    (Scheme.Hom.appLE (𝟙 X) U V hVU2).hom (Algebra.algebra_ext _ _ halg)
    (affineRestrictSectionsBaseChangeIso F hU hV hVU2) ρ (fun a => ?_)
  rw [hρ]
  exact affineRestrictSectionsBaseChangeIso_hom_one_tmul F hU hV hVU2 hVU a

/-- **The sections of a quasi-coherent sheaf of algebras base change on an inclusion of affine
opens.** For affine opens `V ≤ U` and commutative rings `A`, `B` identified with `Γ(F, U)` and
`Γ(F, V)` as modules in such a way that `A ⟶ B` is restriction of sections, the square

```
Γ(X, U) ⟶ A
   |        |
   v        v
Γ(X, V) ⟶ B
```

is a pushout of commutative rings. -/
public theorem isPushout_sections_of_isAffineOpen
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
    [inst : Algebra Γ(X, U) Γ(X, V)]
    (halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) Γ(X, V) r = X.presheaf.map (homOfLE hVU).op r)
    [Module Γ(X, U) Γ(F, V)] [IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, V))
    (hρ : ∀ a, ρ a = F.presheaf.map (homOfLE hVU).op a)
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra Γ(X, U) A] [Algebra Γ(X, V) B] [Algebra A B] [Algebra Γ(X, U) B]
    [IsScalarTower Γ(X, U) A B] [IsScalarTower Γ(X, U) Γ(X, V) B]
    (eA : A ≃ₗ[Γ(X, U)] Γ(F, U)) (eB : B ≃ₗ[Γ(X, V)] Γ(F, V))
    (he : ∀ a : A, eB (algebraMap A B a) = F.presheaf.map (homOfLE hVU).op (eA a)) :
    Algebra.IsPushout Γ(X, U) Γ(X, V) A B :=
  ⟨IsBaseChange.of_linearEquiv (isBaseChange_restrict_of_isAffineOpen F hU hV hVU halg ρ hρ)
    eA eB (IsScalarTower.toAlgHom Γ(X, U) A B).toLinearMap
    (fun a => by rw [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', he a, hρ])⟩

/-- **The pushout square of commutative rings.** Under the hypotheses of
`AlgebraicGeometry.isPushout_sections_of_isAffineOpen`, the square of the algebra maps
`Γ(X, U) → Γ(X, V)`, `Γ(X, U) → A`, `Γ(X, V) → B` and `A → B` is a pushout in `CommRingCat`. -/
public theorem isPushout_commRingCat_sections_of_isAffineOpen
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
    [inst : Algebra Γ(X, U) Γ(X, V)]
    (halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) Γ(X, V) r = X.presheaf.map (homOfLE hVU).op r)
    [Module Γ(X, U) Γ(F, V)] [IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, V))
    (hρ : ∀ a, ρ a = F.presheaf.map (homOfLE hVU).op a)
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra Γ(X, U) A] [Algebra Γ(X, V) B] [Algebra A B] [Algebra Γ(X, U) B]
    [IsScalarTower Γ(X, U) A B] [IsScalarTower Γ(X, U) Γ(X, V) B]
    (eA : A ≃ₗ[Γ(X, U)] Γ(F, U)) (eB : B ≃ₗ[Γ(X, V)] Γ(F, V))
    (he : ∀ a : A, eB (algebraMap A B a) = F.presheaf.map (homOfLE hVU).op (eA a)) :
    CategoryTheory.IsPushout
      (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X, V)))
      (CommRingCat.ofHom (algebraMap Γ(X, U) A))
      (CommRingCat.ofHom (algebraMap Γ(X, V) B))
      (CommRingCat.ofHom (algebraMap A B)) :=
  have := isPushout_sections_of_isAffineOpen F hU hV hVU halg ρ hρ eA eB he
  CommRingCat.isPushout_of_isPushout Γ(X, U) Γ(X, V) A B

/-- **The cartesian square of affine schemes.** `Spec B` is the base change of `Spec A` along
`V ⟶ U`, read through the affine identifications of `U` and `V`. -/
public theorem isPullback_SpecMap_sections_of_isAffineOpen
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
    [inst : Algebra Γ(X, U) Γ(X, V)]
    (halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) Γ(X, V) r = X.presheaf.map (homOfLE hVU).op r)
    [Module Γ(X, U) Γ(F, V)] [IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, V))
    (hρ : ∀ a, ρ a = F.presheaf.map (homOfLE hVU).op a)
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra Γ(X, U) A] [Algebra Γ(X, V) B] [Algebra A B] [Algebra Γ(X, U) B]
    [IsScalarTower Γ(X, U) A B] [IsScalarTower Γ(X, U) Γ(X, V) B]
    (eA : A ≃ₗ[Γ(X, U)] Γ(F, U)) (eB : B ≃ₗ[Γ(X, V)] Γ(F, V))
    (he : ∀ a : A, eB (algebraMap A B a) = F.presheaf.map (homOfLE hVU).op (eA a)) :
    CategoryTheory.IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X, V))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) A))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_commRingCat_sections_of_isAffineOpen F hU hV hVU halg ρ hρ eA eB he)

end AlgebraicGeometry

end
