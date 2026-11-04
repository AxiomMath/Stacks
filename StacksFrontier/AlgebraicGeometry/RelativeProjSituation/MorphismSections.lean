module

public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic

/-!
# Base change of the sections of a quasi-coherent module along a morphism of schemes

Let `f : Y ⟶ X` be a morphism of schemes, `F` a quasi-coherent `𝒪_X`-module, `U ⊆ X` and
`V ⊆ Y` affine opens with `V ≤ f⁻¹U`. Pulling a section back,

  `Γ(F, U) ⟶ Γ(f^*F, V)`,

exhibits the sections of the pullback over `V` as the base change of the sections of `F` over
`U`:

  `Γ(f^*F, V) = Γ(Y, V) ⊗_{Γ(X, U)} Γ(F, U)`.

An affine open of `Y` need not map into any one affine open of `X`, so the pair `(U, V)` is an
explicit datum rather than an inclusion.

## Main results

* `AlgebraicGeometry.isBaseChange_pullbackSection_of_isAffineOpen`: **the module form.** Pulling
  sections back exhibits `Γ(f^*F, V)` as the base change of `Γ(F, U)`.
* `AlgebraicGeometry.isPushout_pullbackSections_of_isAffineOpen` and
  `AlgebraicGeometry.isPushout_commRingCat_pullbackSections_of_isAffineOpen`: **the algebra
  form.** For commutative rings `A`, `B` identified with the two section groups as modules, with
  `A ⟶ B` the pullback of sections, the square `Γ(X, U) → A`, `Γ(Y, V) → B` is a pushout of
  commutative rings.
* `AlgebraicGeometry.isPullback_SpecMap_pullbackSections_of_isAffineOpen`: that pushout read
  through `Spec`, as a cartesian square of affine schemes.

## Implementation notes

`Algebra.IsPushout R S A B` is defined as a base change of modules, so an identification of
sections normalized on `1 ⊗ a` is already an isomorphism of rings and no multiplicativity has to
be checked.

The `Γ(X, U)`-algebra structure on `Γ(Y, V)` and the `Γ(X, U)`-module structure on
`Γ(f^*F, V)` are restriction of scalars along `AlgebraicGeometry.Scheme.Hom.appLE`, which depends
on the inclusion `V ≤ f⁻¹U`; that inclusion does not appear in the type of an `Algebra` or
`Module`, so these cannot be instances and are taken as instance-implicit hypotheses together
with the equations pinning them down.

The rings `A` and `B` of the algebra form are taken abstractly and related to the section groups
by linear equivalences, because the section groups of a sheaf of modules carry no ring structure
as an instance.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent]
  {U : X.Opens} {V : Y.Opens}

/-- **The sections of the pullback of a quasi-coherent module over a compatible pair of affine
opens, as a base change.** For `U ⊆ X` and `V ⊆ Y` affine with `V ≤ f⁻¹U` and `F`
quasi-coherent, extending the scalars of `Γ(F, U)` along `f.appLE U V` gives the sections of
`f^*F` over `V`. -/
public theorem isBaseChange_pullbackSection_of_isAffineOpen
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    [inst : Algebra Γ(X, U) Γ(Y, V)]
    (halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) Γ(Y, V) r = (f.appLE U V hVU).hom r)
    [Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj F, V)]
    [IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ((Scheme.Modules.pullback f).obj F, V))
    (hρ : ∀ a, ρ a = Scheme.Modules.pullbackSection f F U V hVU a) :
    IsBaseChange Γ(Y, V) ρ :=
  ModuleCat.isBaseChange_of_extendScalarsIso (f.appLE U V hVU).hom
    (Algebra.algebra_ext _ _ halg)
    (affinePullbackSectionsBaseChangeIso f F hU hV hVU) ρ
    (fun a => (affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV hVU a).trans (hρ a).symm)

/-- **The sections of a quasi-coherent sheaf of algebras base change along a morphism.** For
affine opens `U ⊆ X`, `V ⊆ Y` with `V ≤ f⁻¹U` and commutative rings `A`, `B` identified with
`Γ(F, U)` and `Γ(f^*F, V)` as modules in such a way that `A ⟶ B` is the pullback of sections,
the square

```
Γ(X, U) ⟶ A
   |        |
   v        v
Γ(Y, V) ⟶ B
```

is a pushout of commutative rings. -/
public theorem isPushout_pullbackSections_of_isAffineOpen
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    [inst : Algebra Γ(X, U) Γ(Y, V)]
    (halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) Γ(Y, V) r = (f.appLE U V hVU).hom r)
    [Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj F, V)]
    [IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ((Scheme.Modules.pullback f).obj F, V))
    (hρ : ∀ a, ρ a = Scheme.Modules.pullbackSection f F U V hVU a)
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra Γ(X, U) A] [Algebra Γ(Y, V) B] [Algebra A B] [Algebra Γ(X, U) B]
    [IsScalarTower Γ(X, U) A B] [IsScalarTower Γ(X, U) Γ(Y, V) B]
    (eA : A ≃ₗ[Γ(X, U)] Γ(F, U)) (eB : B ≃ₗ[Γ(Y, V)] Γ((Scheme.Modules.pullback f).obj F, V))
    (he : ∀ a : A, eB (algebraMap A B a) = Scheme.Modules.pullbackSection f F U V hVU (eA a)) :
    Algebra.IsPushout Γ(X, U) Γ(Y, V) A B :=
  ⟨IsBaseChange.of_linearEquiv
    (isBaseChange_pullbackSection_of_isAffineOpen f F hU hV hVU halg ρ hρ) eA eB
    (IsScalarTower.toAlgHom Γ(X, U) A B).toLinearMap
    (fun a => by rw [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', he a, hρ])⟩

/-- **The pushout square of commutative rings.** Under the hypotheses of
`AlgebraicGeometry.isPushout_pullbackSections_of_isAffineOpen`, the square of `CommRingCat`
formed by `Γ(X, U) ⟶ Γ(Y, V)`, `Γ(X, U) ⟶ A`, `Γ(Y, V) ⟶ B` and `A ⟶ B` is a pushout. -/
public theorem isPushout_commRingCat_pullbackSections_of_isAffineOpen
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    [inst : Algebra Γ(X, U) Γ(Y, V)]
    (halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) Γ(Y, V) r = (f.appLE U V hVU).hom r)
    [Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj F, V)]
    [IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ((Scheme.Modules.pullback f).obj F, V))
    (hρ : ∀ a, ρ a = Scheme.Modules.pullbackSection f F U V hVU a)
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra Γ(X, U) A] [Algebra Γ(Y, V) B] [Algebra A B] [Algebra Γ(X, U) B]
    [IsScalarTower Γ(X, U) A B] [IsScalarTower Γ(X, U) Γ(Y, V) B]
    (eA : A ≃ₗ[Γ(X, U)] Γ(F, U)) (eB : B ≃ₗ[Γ(Y, V)] Γ((Scheme.Modules.pullback f).obj F, V))
    (he : ∀ a : A, eB (algebraMap A B a) = Scheme.Modules.pullbackSection f F U V hVU (eA a)) :
    CategoryTheory.IsPushout
      (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(Y, V)))
      (CommRingCat.ofHom (algebraMap Γ(X, U) A))
      (CommRingCat.ofHom (algebraMap Γ(Y, V) B))
      (CommRingCat.ofHom (algebraMap A B)) :=
  have := isPushout_pullbackSections_of_isAffineOpen f F hU hV hVU halg ρ hρ eA eB he
  CommRingCat.isPushout_of_isPushout Γ(X, U) Γ(Y, V) A B

/-- **The cartesian square of affine schemes.** `Spec B` is the base change of `Spec A` along
`Spec Γ(Y, V) ⟶ Spec Γ(X, U)`. -/
public theorem isPullback_SpecMap_pullbackSections_of_isAffineOpen
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    [inst : Algebra Γ(X, U) Γ(Y, V)]
    (halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) Γ(Y, V) r = (f.appLE U V hVU).hom r)
    [Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj F, V)]
    [IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ((Scheme.Modules.pullback f).obj F, V))
    (hρ : ∀ a, ρ a = Scheme.Modules.pullbackSection f F U V hVU a)
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra Γ(X, U) A] [Algebra Γ(Y, V) B] [Algebra A B] [Algebra Γ(X, U) B]
    [IsScalarTower Γ(X, U) A B] [IsScalarTower Γ(X, U) Γ(Y, V) B]
    (eA : A ≃ₗ[Γ(X, U)] Γ(F, U)) (eB : B ≃ₗ[Γ(Y, V)] Γ((Scheme.Modules.pullback f).obj F, V))
    (he : ∀ a : A, eB (algebraMap A B a) = Scheme.Modules.pullbackSection f F U V hVU (eA a)) :
    CategoryTheory.IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(Y, V))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) A))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_commRingCat_pullbackSections_of_isAffineOpen f F hU hV hVU halg ρ hρ eA eB he)

end AlgebraicGeometry

end
