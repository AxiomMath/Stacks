module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators

/-!
# The ideal of denominators embeds in the structure sheaf

Let `X` be a scheme, `L` an invertible sheaf of `𝒪_X`-modules and `s` a meromorphic section of
`L`. The inclusion of the ideal of denominators of `s` in `𝒪_X` is injective. Since that ideal
is the fibre product of `𝒪_X` and `L` over `K_X(L)`, its first projection is injective exactly
when the canonical map `L ⟶ K_X(L)` is, and that is the content of this file: extension of
scalars along `𝒪_X ⟶ K_X` does not collapse an invertible module, because `𝒪_X ⟶ K_X` is
injective and tensoring by an invertible module is an equivalence.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.toExtendScalars`: for a presheaf of `A₁`-modules `N`, the
  map `x ↦ 1 ⊗ x` from `N` into the sheafified extension of scalars `(A₂ ⊗_{A₁} N)^#`.
* `Stacks.Sheaves.RingedToposModules.ringMod`, `ringModHom`: the target ring `A₂` read as a
  presheaf of `A₁`-modules, and `θ : A₁ ⟶ A₂` read as a morphism of presheaves of
  `A₁`-modules; `ringModSheaf` and `ringModSheafHom` are the same data for sheaves.

## Main results

* `AlgebraicGeometry.denominatorIdeal_inclusion_mono`: the inclusion of the ideal of
  denominators of a meromorphic section of an invertible sheaf into the structure sheaf is a
  monomorphism.
* `AlgebraicGeometry.mono_toMeromorphicSectionSheafAsModule`: the canonical map
  `L ⟶ K_X(L)` is a monomorphism for invertible `L`. This is what the previous statement
  reduces to.
* `CategoryTheory.Adjunction.mono_unit_app_of_map_injective`: the unit of an adjunction at `X`
  is a monomorphism as soon as the left adjoint is injective on morphisms with target `X`.
* `Stacks.Sheaves.RingedToposModules.mono_unit_of_isLocallyInjective`: the unit of the
  change-of-rings adjunction for sheaves of modules is a monomorphism at `L` whenever
  `x ↦ 1 ⊗ x` is locally injective on `L`.
* `Stacks.Sheaves.RingedToposModules.isLocallyInjective_unitHom`: that local injectivity holds
  for an invertible `L` whenever `θ` is injective on sections.

## Implementation notes

The route taken here does not evaluate the unit of
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`, although it could: that
adjunction is built from the presheaf-level term
  `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, and
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`
gives its sections as `x ↦ toSheafify (1 ⊗ x)`. For any adjunction `F ⊣ G` the map
`u ↦ u ≫ unit` is the composite
of `F.map` with the hom-equivalence, so the unit at `X` is a monomorphism exactly when `F.map`
is injective on morphisms with target `X`
(`CategoryTheory.Adjunction.mono_unit_app_of_map_injective`). For extension of scalars `F.map`
is the sheafification of `a ⊗ x ↦ a ⊗ φ(x)`, which *is* computable, and testing it on
`a = 1` turns injectivity of `F.map` into local injectivity of `x ↦ 1 ⊗ x`.

That local injectivity is where invertibility enters. The presheaf
`(A₂ ⊗_{A₁} N)` restricted to `A₁` is, definitionally, the monoidal product
`ringMod θ ⊗ N` of presheaves of `A₁`-modules, and `x ↦ 1 ⊗ x` is the left unitor followed by
`ringModHom θ ▷ N`. Sheafifying the latter is tensoring on the right by `L` applied to
`ringModSheafHom θ`, which is a monomorphism because `θ` is injective on sections; tensoring on
the right by an invertible module is an equivalence
(`Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor_iff`), so it preserves
that monomorphism. A morphism of presheaves of modules whose sheafification is a monomorphism
is locally injective, by `Stacks.Sheaves.RingedToposModules.isLocallyInjective_of_mono_sheafify`.

Invertibility is `AlgebraicGeometry.SheafOfModules.IsInvertible`, the form the ideal of
denominators is stated with; regularity of the section is not needed for this clause, and is
not assumed.

The other assertions of Tag 02P0 — quasi-coherence of the ideal and the nowhere dense closed
supports of the two cokernels — are **not** in this file; they rest on the affine-local
description of the ideal, which the source obtains by shrinking `X` until `L` is trivial and
`s = a/b` with `a`, `b` nonzerodivisors.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory TensorProduct

universe v u

namespace CategoryTheory.Adjunction

/-- The unit of an adjunction at `X` is a monomorphism as soon as the left adjoint is injective
on morphisms with target `X`. Both conditions say that `u ↦ u ≫ unit` is injective, the
hom-equivalence identifying that map with `F.map`. -/
theorem mono_unit_app_of_map_injective {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) (X : A)
    (h : ∀ (W : A) (p q : W ⟶ X), F.map p = F.map q → p = q) :
    Mono (adj.unit.app X) where
  right_cancellation {W} p q hpq := by
    refine h W p q ((adj.homEquiv W (F.obj X)).injective ?_)
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, adj.unit_naturality p,
      adj.unit_naturality q]
    exact hpq

end CategoryTheory.Adjunction

namespace Stacks.PresheafOfModules.ChangeOfRings

/-- Extension of scalars acts on a pure tensor by acting on the second factor. -/
lemma changeOfRings_map_app_tmul {C : Type u} [Category.{v} C]
    {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (θ : O₁ ⟶ O₂)
    {G H : Stacks.PresheafOfModules.ChangeOfRings.PMod O₁} (φ : G ⟶ H) (X : Cᵒᵖ) (a : O₂.obj X) (x :
      G.obj X) :
    letI := (θ.app X).hom.toAlgebra
    (((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).map φ).app X).hom (a ⊗ₜ[O₁.obj X] x)
      = a ⊗ₜ[O₁.obj X] ((φ.app X).hom x) :=
  Stacks.PresheafOfModules.ChangeOfRings.cofHom_app_tmul θ φ X a x

end Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.Sheaves.RingedToposModules

section General

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The canonical map `N ⟶ (A₂ ⊗[A₁] N)^#` into the sheafified extension of scalars: `x ↦ 1 ⊗ x`
followed by the sheafification unit. -/
def toExtendScalars (N : Stacks.PresheafOfModules.ChangeOfRings.PMod A₁) :
    N ⟶ (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars θ).obj
      ((SheafOfModules.forget (commRingSheaf J A₂ h₂) ⋙
        PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J A₂ h₂).obj)).obj
          ((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
            ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj N))) :=
  Stacks.PresheafOfModules.ChangeOfRings.unitHom θ
    ((PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂)
      (𝟙 _)).unit.app ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj N))

/-- On sections over `V`, `toExtendScalars` sends `x` to the image of `1 ⊗ x` under the
sheafification unit. -/
lemma toExtendScalars_app_apply (N : Stacks.PresheafOfModules.ChangeOfRings.PMod A₁) (V : Cᵒᵖ) (x :
  N.obj V) :
    letI := (θ.app V).hom.toAlgebra
    ((toExtendScalars J θ h₂ N).app V).hom x =
      (((PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂)
        (𝟙 _)).unit.app ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj N)).app V).hom
          ((1 : A₂.obj V) ⊗ₜ[A₁.obj V] x) := by
  let := (θ.app V).hom.toAlgebra
  exact Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply θ _ V x

/-- `toExtendScalars` is the map `x ↦ 1 ⊗ x` followed by the restriction of scalars of the
sheafification unit. -/
lemma toExtendScalars_eq (N : Stacks.PresheafOfModules.ChangeOfRings.PMod A₁) :
    toExtendScalars J θ h₂ N = Stacks.PresheafOfModules.ChangeOfRings.unitHom θ (𝟙 _) ≫
      (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars θ).map
        ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
            ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj N)) := rfl

/-- If `x ↦ 1 ⊗ x` into the sheafified extension of scalars is injective on sections over every
object, then extension of scalars is injective on morphisms with target `L`. -/
theorem extendScalars_map_injective
    {M L : SheafOfModules.{u} (commRingSheaf J A₁ h₁)}
    (hinj : ∀ V, Function.Injective ((toExtendScalars J θ h₂ L.val).app V).hom)
    (p q : M ⟶ L)
    (hpq : (extendScalars J θ h₁ h₂).map p = (extendScalars J θ h₁ h₂).map q) : p = q := by
  apply (SheafOfModules.fullyFaithfulForget (commRingSheaf J A₁ h₁)).map_injective
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let := (θ.app V).hom.toAlgebra
  set fp := (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).map
    ((SheafOfModules.forget (commRingSheaf J A₁ h₁)).map p) with hfp
  set fq := (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).map
    ((SheafOfModules.forget (commRingSheaf J A₁ h₁)).map q) with hfq
  set un := (PresheafOfModules.sheafificationAdjunction
    (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
      ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj L.val) with hun
  have hpq' : (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map fp =
      (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map fq := hpq
  have h1 := (PresheafOfModules.sheafificationAdjunction
    (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit_naturality fp
  have h2 := (PresheafOfModules.sheafificationAdjunction
    (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit_naturality fq
  rw [hpq'] at h1
  have hC := congrArg (fun (m : _ ⟶ _) => (m.app V).hom ((1 : A₂.obj V) ⊗ₜ[A₁.obj V] x))
    (h1.symm.trans h2)
  have hA : ∀ f : M ⟶ L, (un.app V).hom
      ((((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).map
        ((SheafOfModules.forget (commRingSheaf J A₁ h₁)).map f)).app V).hom
          ((1 : A₂.obj V) ⊗ₜ[A₁.obj V] x)) =
      (un.app V).hom ((1 : A₂.obj V) ⊗ₜ[A₁.obj V]
        (((SheafOfModules.forget (commRingSheaf J A₁ h₁)).map f).app V).hom x) := fun f =>
    congrArg _ (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings_map_app_tmul θ _ V 1 x)
  refine hinj V ((toExtendScalars_app_apply J θ h₂ L.val V _).trans
    (((hA p).symm.trans (hC.trans (hA q))).trans
      (toExtendScalars_app_apply J θ h₂ L.val V _).symm))

/-- The unit of the change-of-rings adjunction at `L` is a monomorphism as soon as `x ↦ 1 ⊗ x`
is injective on sections of `L` over every object. -/
theorem mono_extendRestrictScalarsAdjunction_unit_app
    (L : SheafOfModules.{u} (commRingSheaf J A₁ h₁))
    (hinj : ∀ V, Function.Injective ((toExtendScalars J θ h₂ L.val).app V).hom) :
    Mono ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L) :=
  Adjunction.mono_unit_app_of_map_injective _ L
    fun _ p q h => extendScalars_map_injective J θ h₁ h₂ hinj p q h

/-- Over a sheaf `L`, local injectivity of the map into the sheafified extension of scalars is
injectivity on sections. -/
theorem toExtendScalars_app_injective (L : SheafOfModules.{u} (commRingSheaf J A₁ h₁))
    (h : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (toExtendScalars J θ h₂ L.val))) (V : Cᵒᵖ) :
    Function.Injective ((toExtendScalars J θ h₂ L.val).app V).hom := by
  have hsep : Presieve.IsSeparated J
      ((PresheafOfModules.toPresheaf (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁)).obj
        L.val ⋙
        forget AddCommGrpCat) := by
    refine Presieve.IsSheaf.isSeparated ((CategoryTheory.isSheaf_iff_isSheaf_of_type J _).mp ?_)
    exact ((sheafCompose J (forget AddCommGrpCat.{u})).obj
      (⟨(PresheafOfModules.toPresheaf (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁)).obj
        L.val, L.isSheaf⟩ :
        Sheaf J AddCommGrpCat.{u})).2
  exact (Presheaf.isLocallyInjective_iff_injective_of_separated J _ hsep).mp h V

/-- The unit of the change-of-rings adjunction at `L` is a monomorphism as soon as the presheaf
map `x ↦ 1 ⊗ x` is locally injective. -/
theorem mono_unit_of_isLocallyInjective (L : SheafOfModules.{u} (commRingSheaf J A₁ h₁))
    (hnu : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map
      (Stacks.PresheafOfModules.ChangeOfRings.unitHom θ (𝟙
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj L.val))))) :
    Mono ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L) := by
  have := hnu
  have hsh : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁)).map
        ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars θ).map
          ((PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂)
            (𝟙 _)).unit.app ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj L.val))))
              := by
    show Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj
        L.val).presheaf)
    infer_instance
  refine mono_extendRestrictScalarsAdjunction_unit_app J θ h₁ h₂ L fun V =>
    toExtendScalars_app_injective J θ h₁ h₂ L ?_ V
  rw [toExtendScalars_eq, Functor.map_comp]
  infer_instance

end General

section Small

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The monoidal structure on presheaves of `A₁`-modules. -/
noncomputable local instance :
    MonoidalCategory (PresheafOfModules.{u} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
      A₁)) := inferInstance

/-- `A₂`, read as a presheaf of `A₁`-modules along `θ`. -/
def ringMod : Stacks.PresheafOfModules.ChangeOfRings.PMod A₁ :=
  (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars θ).obj (PresheafOfModules.unit
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))

/-- The unit section of `A₂` read as a presheaf of `A₁`-modules. -/
def ringModOne : (ringMod θ).sections :=
  PresheafOfModules.sectionsMk (fun X => (1 : A₂.obj X))
    (fun {_ _} f => PresheafOfModules.unit_map_one
      (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂) f)

/-- `θ`, read as a morphism of presheaves of `A₁`-modules `A₁ ⟶ A₂`. -/
def ringModHom : PresheafOfModules.unit (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁) ⟶
  ringMod θ :=
  (ringMod θ).unitHomEquiv.symm (ringModOne θ)

/-- On sections over `X`, `ringModHom θ` is `θ`. -/
lemma ringModHom_app_apply (X : Cᵒᵖ) (a : A₁.obj X) :
    ((ringModHom θ).app X).hom a = (θ.app X).hom a := by
  have h : ((ringModHom θ).app X).hom a = (θ.app X).hom a * (1 : A₂.obj X) := rfl
  rw [h, mul_one]

/-- The map `x ↦ 1 ⊗ x` into the extension of scalars is the left unitor followed by tensoring
`θ` on the right by `N`. -/
lemma unitHom_eq (N : Stacks.PresheafOfModules.ChangeOfRings.PMod A₁) :
    Stacks.PresheafOfModules.ChangeOfRings.unitHom θ (𝟙
      ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj N)) =
      (λ_ N).inv ≫ (ringModHom θ ▷ N) := by
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let := (θ.app V).hom.toAlgebra
  have hL : ((Stacks.PresheafOfModules.ChangeOfRings.unitHom θ (𝟙
    ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj N))).app V).hom x
      = (1 : A₂.obj V) ⊗ₜ[A₁.obj V] x := Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply θ (𝟙
        _) V x
  have hR : (((λ_ N).inv ≫ (ringModHom θ ▷ N)).app V).hom x
      = ((ringModHom θ).app V).hom (1 : A₁.obj V) ⊗ₜ[A₁.obj V] x := rfl
  rw [hL]
  exact (hR.trans (congrArg (fun z : A₂.obj V => z ⊗ₜ[A₁.obj V] x)
    ((ringModHom_app_apply θ V 1).trans (map_one (θ.app V).hom)))).symm

/-- A morphism of presheaves of modules whose sheafification is a monomorphism is locally
injective. -/
theorem isLocallyInjective_of_mono_sheafify
    {M N : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
      h₁).obj}
    (f : M ⟶ N) (hf : Mono ((Stacks.SheafOfModules.TensorSheafification.sheafify A₁ h₁).map f)) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
        h₁).obj).map f) := by
  have hA : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
        h₁).obj).map
        ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction A₁ h₁).unit.app M)) := by
    show Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J M.presheaf)
    infer_instance
  have hB : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
        h₁).obj).map
        ((SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁).obj)).map
              ((Stacks.SheafOfModules.TensorSheafification.sheafify A₁ h₁).map f))) :=
    Presheaf.isLocallyInjective_of_injective J _
      fun V => SheafOfModules.app_injective_of_mono hf V
  have hnat := (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction A₁ h₁).unit_naturality
    f
  have fac : (PresheafOfModules.toPresheaf
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁).obj).map f ≫
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
        h₁).obj).map
        ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction A₁ h₁).unit.app N) =
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
        h₁).obj).map
        ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction A₁ h₁).unit.app M) ≫
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
        h₁).obj).map
        ((SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁).obj)).map
              ((Stacks.SheafOfModules.TensorSheafification.sheafify A₁ h₁).map f)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ hnat.symm
  exact Presheaf.isLocallyInjective_of_isLocallyInjective_fac J fac

/-- `A₂`, read as a sheaf of `A₁`-modules along `θ`. -/
def ringModSheaf : SheafOfModules.{u} (commRingSheaf J A₁ h₁) :=
  (SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj
    (SheafOfModules.unit (commRingSheaf J A₂ h₂))

/-- `θ`, read as a morphism of sheaves of `A₁`-modules `A₁ ⟶ A₂`. -/
def ringModSheafHom :
    SheafOfModules.unit (commRingSheaf J A₁ h₁) ⟶ ringModSheaf J θ h₁ h₂ :=
  (SheafOfModules.fullyFaithfulForget (commRingSheaf J A₁ h₁)).preimage (ringModHom θ)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- The underlying morphism of presheaves of `ringModSheafHom` is `ringModHom θ`. -/
lemma forget_map_ringModSheafHom :
    (SheafOfModules.forget (commRingSheaf J A₁ h₁)).map (ringModSheafHom J θ h₁ h₂) =
      ringModHom θ :=
  (SheafOfModules.fullyFaithfulForget (commRingSheaf J A₁ h₁)).map_preimage _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- If `θ` is injective on sections over every object, then `ringModSheafHom` is a
monomorphism. -/
lemma mono_ringModSheafHom (hθ : ∀ V : Cᵒᵖ, Function.Injective (θ.app V).hom) :
    Mono (ringModSheafHom J θ h₁ h₂) := by
  refine SheafOfModules.mono_of_forall_app_injective _ fun V a b hab => ?_
  refine hθ V ?_
  have ha : ((ringModHom θ).app V).hom a = (θ.app V).hom a := ringModHom_app_apply θ V a
  have hb : ((ringModHom θ).app V).hom b = (θ.app V).hom b := ringModHom_app_apply θ V b
  exact ha.symm.trans (hab.trans hb)

include h₂ in
/-- For an invertible sheaf of `A₁`-modules `L` and a morphism of sheaves of rings `θ` which is
injective on sections, the map `x ↦ 1 ⊗ x` from `L` into the extension of scalars is locally
injective. -/
theorem isLocallyInjective_unitHom
    (L : SheafOfModules.{u} (commRingSheaf J A₁ h₁))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible A₁ h₁ L)
    (hθ : ∀ V : Cᵒᵖ, Function.Injective (θ.app V).hom) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
        h₁).obj).map
        (Stacks.PresheafOfModules.ChangeOfRings.unitHom θ (𝟙
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj L.val)))) := by
  have := hL
  let tensorRing : Sheaf J CommRingCat.{u} :=
    ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩
  have hleft : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} tensorRing).obj
      L).IsEquivalence :=
    AlgebraicGeometry.SheafOfModules.tensorLeftFunctor_isEquivalence A₁ h₁ L
  have hright : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} tensorRing).flip.obj
      L).IsEquivalence :=
    (Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor_iff A₁ h₁ L).mpr hleft
  have hmono0 := mono_ringModSheafHom J θ h₁ h₂ hθ
  have hmono : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      tensorRing).flip.obj L).map (ringModSheafHom J θ h₁ h₂)) :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} tensorRing).flip.obj
      L).mono_map_iff_mono (ringModSheafHom J θ h₁ h₂)).mpr hmono0
  have hm2 : Mono ((Stacks.SheafOfModules.TensorSheafification.sheafify A₁ h₁).map (ringModHom θ ▷
    L.val)) := by
    rw [← forget_map_ringModSheafHom J θ h₁ h₂]
    exact hmono
  have hli := isLocallyInjective_of_mono_sheafify J h₁ (ringModHom θ ▷ L.val) hm2
  have hiso : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
        h₁).obj).map
        (λ_ L.val).inv) := by
    have hunit : ∀ (V : Cᵒᵖ) (z : L.val.obj V),
        (((λ_ L.val).hom).app V).hom ((((λ_ L.val).inv).app V).hom z) = z := fun V z =>
      congrArg (fun (m : L.val ⟶ L.val) => (m.app V).hom z) (λ_ L.val).inv_hom_id
    exact Presheaf.isLocallyInjective_of_injective J _ fun V a b hab =>
      (hunit V a).symm.trans ((congrArg _ hab).trans (hunit V b))
  have e : (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf
    A₁ h₁).obj).map
        (Stacks.PresheafOfModules.ChangeOfRings.unitHom θ (𝟙
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj L.val))) =
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
        h₁).obj).map
          ((λ_ L.val).inv) ≫
        (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
          h₁).obj).map
          (ringModHom θ ▷ L.val) := by
    rw [unitHom_eq θ L.val]
    exact Functor.map_comp _ _ _
  rw [e]
  exact Presheaf.isLocallyInjective_comp J
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
      h₁).obj).map (λ_ L.val).inv)
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁
      h₁).obj).map
      (ringModHom θ ▷ L.val))

end Small

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The canonical map from an invertible sheaf of modules to its sheaf of meromorphic sections
is a monomorphism: it is the unit of extension of scalars along the injection
`𝒪_X ⟶ K_X`, and tensoring by an invertible module preserves that injectivity. -/
theorem mono_toMeromorphicSectionSheafAsModule
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) :
    Mono (toMeromorphicSectionSheafAsModule X L) :=
  Stacks.Sheaves.RingedToposModules.mono_unit_of_isLocallyInjective
    (Opens.grothendieckTopology X) X.toTotalQuotientSheaf.hom
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).property L
    (Stacks.Sheaves.RingedToposModules.isLocallyInjective_unitHom
      (Opens.grothendieckTopology X) X.toTotalQuotientSheaf.hom
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.totalQuotientSheaf).property
      L hL fun V => toTotalQuotientSheaf_app_injective X V.unop)

/-- **Stacks Project, Tag 02P0**, injectivity of the ideal inclusion. For an invertible sheaf of
modules `L` and a meromorphic section `s` of `L`, the ideal of denominators of `s` embeds in the
structure sheaf. -/
@[stacks 02P0 "inclusion is injective"]
theorem denominatorIdeal_inclusion_mono
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (s : MeromorphicSection X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) :
    Mono (denominatorIdealι X L s) := by
  have := mono_toMeromorphicSectionSheafAsModule X L hL
  exact pullback.fst_of_mono

end AlgebraicGeometry
