module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.BLinear

/-!
# Tag 0AX0: derived coextension of scalars along a finite map is dualizing

Let `f : A → B` be a finite homomorphism of Noetherian rings and let `ω` be a dualizing complex
over `A`. [stacks 0AX0] asserts that `RHom_A(B, ω)` is a dualizing complex over `B`. Of its three
conditions (the three fields of `Dualizing.IsDualizingComplex`), finite injective dimension and
finiteness of the cohomology are
`Dualizing.hasFiniteInjectiveDimension_derivedHom_obj` and
`Dualizing.finiteCohomology_derivedHom_obj`; the homothety condition is the Hom computation

`Hom_{D(B)}(RHom_A(B, ω), RHom_A(B, ω)[n]) = Hom_{D(A)}(RHom_A(B, ω), ω[n]) = H^n(B)` ,

whose vanishing half is `Dualizing.subsingleton_hom_derivedHom_shift`. This file closes the
degree-zero half and with it the tag.

The degree-zero statement needed downstream is `B`-linear, and `B`-linearity is a real part of the
content rather than a formality: the chain of identifications produces an `A`-linear isomorphism
`End_{D(B)}(RHom_A(B, ω)) ≃ₗ[A] B` on its own, and an `A`-linear isomorphism is not enough, since a
`B`-algebra `E` with `E ≃ₗ[A] B` need not have `B ≃ E` (take `A = k`, `B = k[x]/(x²)`,
`E = k[y]/(y²)` with `x ↦ 0`). So the `B`-action is tracked at every step:

* through the adjunction of [stacks 0A70], by `CategoryTheory.Adjunction.homEquiv_naturality_left`;
* through the identification of `RHom_A(B, ω)` with the internal derived Hom `RHom_A(B[0], ω)`, by
  `Dualizing.restrictScalarsDerivedHomIso_smul`, which is where the `B`-structure crosses into the
  first variable of the internal Hom;
* through the adjunction-level description `Dualizing.homUnitAddEquiv` of morphisms into `ω`, by
  `Dualizing.homUnitAddEquiv_naturality`;
* through the biduality theorem of [stacks 0A7C] at `B[0]`, by
  `Dualizing.bidualityMor_naturality`.

That leaves `Hom_{D(A)}(1, B[0])`, with `b` acting by multiplication by `b` on `B[0]`, and this
file identifies it with `B`: the tensor unit of `D(A)` is the lifted ring in degree zero
(`Dualizing.derivedTensorUnitIsoSingle`), the single-complex functor is fully faithful, and
`A`-linear maps out of the lifted ring are their values at `1`.

## Main definitions

* `Dualizing.derivedTensorUnitModule` — the `A`-module underlying the tensor unit of `D(A)`.
* `Dualizing.derivedTensorUnitIsoSingle` — the tensor unit of `D(A)` is `ULift A` in degree zero.
* `Dualizing.derivedTensorUnitModuleHom`, `Dualizing.singleHomAddEquiv` — the two remaining
  identifications.

## Main results

* `Dualizing.nonempty_endLinearEquiv_derivedHom` — the degree-zero half of the Hom computation,
  `B`-linearly.
* `Dualizing.isDualizingComplex_derivedHom_of_finite` — [stacks 0AX0].

## References

* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

section Unit

variable (A : Type u) [CommRing A]

/-- The `A`-module underlying the tensor unit of `D(A)`: the lifted ring `ULift A`, viewed as an
`A`-module along `A ≃+* ULift A`. -/
abbrev derivedTensorUnitModule : ModuleCat.{max v u} A :=
  (scalarsDown.{u, v} A).obj (ModuleCat.of (ULift.{max v u} A) (ULift.{max v u} A))

/-- **The tensor unit of `D(A)` is the lifted ring in degree zero.** -/
def derivedTensorUnitIsoSingle :
    StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (derivedTensorUnitModule.{u, v} A) :=
  (scalarsDown.{u, v} A).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat.{max v u} (ULift.{max v u} A)) 0).obj
        (ModuleCat.of (ULift.{max v u} A) (ULift.{max v u} A))) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor (scalarsDown.{u, v} A) 0).app
        (ModuleCat.of (ULift.{max v u} A) (ULift.{max v u} A))) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} A) 0).app
      (derivedTensorUnitModule.{u, v} A)).symm

/-- **`A`-linear maps out of the unit module are their values at `1`.** -/
def derivedTensorUnitModuleHom (M : ModuleCat.{max v u} A) :
    (derivedTensorUnitModule.{u, v} A ⟶ M) ≃+ (M : Type (max v u)) where
  toFun h := h.hom (ULift.up 1)
  invFun x := ModuleCat.ofHom
    { toFun := fun y => y.down • x
      map_add' := fun y z => add_smul y.down z.down x
      map_smul' := fun a y => mul_smul a y.down x }
  left_inv h := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun y => ?_
    have hy : (y.down : A) •
        (ULift.up 1 : (derivedTensorUnitModule.{u, v} A : Type (max v u))) = y :=
      ULift.ext (mul_one y.down)
    change (y.down : A) • h.hom (ULift.up 1) = h.hom y
    exact (map_smul h.hom y.down (ULift.up 1)).symm.trans (congrArg h.hom hy)
  right_inv x := one_smul A x
  map_add' h h' := rfl

/-- Morphisms of single complexes in degree zero are morphisms of modules. -/
def singleHomAddEquiv (P M : ModuleCat.{max v u} A) :
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj P ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M) ≃+ (P ⟶ M) where
  toFun ψ := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).preimage ψ
  invFun g := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map g
  left_inv ψ := Functor.map_preimage _ _
  right_inv g := Functor.preimage_map _
  map_add' ψ ψ' := by
    apply (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map_injective
    rw [Functor.map_add, Functor.map_preimage, Functor.map_preimage, Functor.map_preimage]

/-- Taking preimages along a fully faithful functor commutes with postcomposition. -/
theorem preimage_comp_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.Full]
    [F.Faithful] {P M N : C} (ψ : F.obj P ⟶ F.obj M) (g : M ⟶ N) :
    F.preimage (ψ ≫ F.map g) = F.preimage ψ ≫ g := by
  rw [Functor.preimage_comp, Functor.preimage_map]

/-- The equivalence `singleHomAddEquiv` sends the composite of `ψ` with the image of a module
map `g` to the composite of the image of `ψ` with `g`. -/
theorem singleHomAddEquiv_comp_map (P M N : ModuleCat.{max v u} A)
    (ψ : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj P ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M) (g : M ⟶ N) :
    singleHomAddEquiv.{u, v} A P N
        (ψ ≫ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map g) =
      singleHomAddEquiv.{u, v} A P M ψ ≫ g :=
  preimage_comp_map _ ψ g

end Unit

section Final

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Multiplication by `b` on the `A`-module `Dualizing.targetAsModule`, read on the
underlying `ULift B`. -/
theorem targetMul_apply (f : A →+* B) (b : B)
    (x : (targetAsModule.{u, v} f : Type (max v u))) :
    (targetMul.{u, v} f b).hom x = ULift.up (b * x.down) := rfl

/-- **The derived endomorphism module of `RHom_A(B, ω)` is `B`, `B`-linearly.** This is the
degree-zero half of the Hom computation of [stacks 0AX0], with the `B`-linearity tracked through
every step. -/
theorem nonempty_endLinearEquiv_derivedHom [IsNoetherianRing A] (f : A →+* B) (hf : f.Finite)
    (ω : DerivedCategory (ModuleCat.{max v u} A)) (hω : IsDualizingComplex ω) :
    Nonempty (End ((derivedHom.{u, v, u} f).obj ω) ≃ₗ[B] B) := by
  obtain ⟨E, hE⟩ := exists_endAddEquiv_hom_derivedTensorUnit.{u, v} f hf hω
  set S := DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0
  set uIso := derivedTensorUnitIsoSingle.{u, v} A
  set Θ := E.trans ((precompAddEquiv uIso (targetSingle.{u, v} f)).symm.trans
    ((singleHomAddEquiv.{u, v} A (derivedTensorUnitModule.{u, v} A) (targetAsModule.{u, v} f)).trans
      ((derivedTensorUnitModuleHom.{u, v} A (targetAsModule.{u, v} f)).trans AddEquiv.ulift)))
    with hΘ
  have hsmul : ∀ (b : B) (φ : End ((derivedHom.{u, v, u} f).obj ω)), Θ (b • φ) = b * Θ φ := by
    intro b φ
    have h1 : (precompAddEquiv uIso (targetSingle.{u, v} f)).symm (E φ ≫ S.map
          (targetMul.{u, v} f b)) =
        (precompAddEquiv uIso (targetSingle.{u, v} f)).symm (E φ) ≫ S.map
          (targetMul.{u, v} f b) := by
      change uIso.inv ≫ E φ ≫ S.map (targetMul.{u, v} f b) =
        (uIso.inv ≫ E φ) ≫ S.map (targetMul.{u, v} f b)
      rw [Category.assoc]
    rw [hΘ]
    simp only [AddEquiv.trans_apply]
    rw [hE b φ, h1, singleHomAddEquiv_comp_map]
    rfl
  exact ⟨{ Θ with map_smul' := hsmul }⟩

/-- **Stacks Project, Tag 0AX0.** For a finite homomorphism of Noetherian rings and a dualizing
complex `ω` over the source, `RHom_A(B, ω)` is a dualizing complex over `B`.

Noetherianity of `B` follows from that of `A` and finiteness of `f`, but it is a hypothesis here
because `Dualizing.IsDualizingComplex` is only stated over a Noetherian ring, so the conclusion
cannot be written down without it. -/
@[stacks 0AX0, stacks 0A7I "the surjective case, a surjection being a finite ring map"]
theorem isDualizingComplex_derivedHom_of_finite [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : f.Finite) (ω : DerivedCategory (ModuleCat.{max v u} A))
    (hω : IsDualizingComplex ω) :
    IsDualizingComplex ((derivedHom.{u, v, u} f).obj ω) :=
  isDualizingComplex_derivedHom_of_finite_of_endLinearEquiv.{u, v} f hf ω hω
    (nonempty_endLinearEquiv_derivedHom.{u, v} f hf ω hω).some

end Final

end Dualizing

end
