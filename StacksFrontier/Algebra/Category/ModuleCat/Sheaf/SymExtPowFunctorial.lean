module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras

/-!
# The functorial action of the sectionwise symmetric and exterior powers

`PresheafOfModules.symPow n` and `PresheafOfModules.extPow n` are the presheaves of sectionwise
symmetric and exterior powers of a presheaf of modules. This file defines their action on morphisms
of presheaves of modules, together with the equations that determine it on the spanning families:
a product of `n` degree-one generators for the symmetric power, and an ordered wedge of `n`
degree-one generators for the exterior power.

## Main definitions

* `PresheafOfModules.symPowMap` and `extPowMap`: the action of `symPow n` and `extPow n` on a
  morphism of presheaves of modules, built sectionwise from `SymPow.symMapₛₗ` and
  `ExteriorAlgebra.powMapₛₗ` at the identity ring homomorphism.

## Main results

* `PresheafOfModules.symPowMap_app_coe` and `extPowMap_app_coe`: the sections of the induced
  morphism, read through the sectionwise identifications `symPowSections` / `extPowSections`, are
  `SymmetricAlgebra.mapₛₗ` and `ExteriorAlgebra.mapₛₗ` of the morphism's own sections.
* `PresheafOfModules.symPowMap_app_prod_ι` and `extPowMap_app_ιMulti`: the induced morphism on a
  product, respectively an ordered wedge, of degree-one generators. Those families span, so these
  determine the morphism.
* `PresheafOfModules.symPowMap_comp` and `extPowMap_comp`: functoriality in the morphism variable.
* `PresheafOfModules.symPowMap_id` and `extPowMap_id`: the action on an identity morphism is the
  identity. Together with the previous pair these say that `symPow n` and `extPow n` are
  functorial.

## Implementation notes

Naturality is proved by factoring twice. The naturality square asks that `mapₛₗ` of the morphism
commute with `mapₛₗ` of the restriction maps. Both composites are `mapₛₗ` of the same semilinear
map `G.restrictₛₗ f ∘ α.app X`, by `SymmetricAlgebra.mapₛₗ_eq_comp` (respectively
`ExteriorAlgebra.mapₛₗ_eq_comp`) applied to the two factorizations of that map; the only
mathematical input is the naturality of `α`.

`symPowMap_id` and `extPowMap_id` are proved by `mapₛₗ_eq_self` with its last argument, the
element of the algebra, given explicitly. Left as a metavariable, unification reduces the
right-hand side through the `RingCon` quotient underlying the reducible `SymmetricAlgebra`, which
exhausts the heartbeat limit.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w a

namespace PresheafOfModules

section Functorial

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The action of `PresheafOfModules.symPow n` on a morphism of presheaves of modules. -/
noncomputable def symPowMap (n : ℕ)
    {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G) :
    symPow n F ⟶ symPow n G where
  app X := ModuleCat.ofHom (SymPow.symMapₛₗ n (RingHom.id _) (α.app X).hom)
  naturality {X Y} f := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    have h1 := SymmetricAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (α.app Y).hom
      ((G.restrictₛₗ f).comp (α.app X).hom) (fun _ => rfl)
      (fun m => by rw [LinearMap.comp_apply, PresheafOfModules.restrictₛₗ_apply,
        PresheafOfModules.restrictₛₗ_apply, naturality_apply])
      (↑(PresheafOfModules.symPowSections n F X x) : SymmetricAlgebra _ _)
    have h2 := SymmetricAlgebra.mapₛₗ_eq_comp (α.app X).hom (G.restrictₛₗ f)
      ((G.restrictₛₗ f).comp (α.app X).hom) (fun _ => rfl) (fun _ => rfl)
      (↑(PresheafOfModules.symPowSections n F X x) : SymmetricAlgebra _ _)
    exact h1.symm.trans h2))

/-- Read through `symPowSections`, the sections of `symPowMap n α` are the image under
`SymmetricAlgebra.mapₛₗ` of the sections of `α`. -/
@[simp]
theorem symPowMap_app_coe (n : ℕ)
    {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G) (X : Cᵒᵖ)
    (x : (symPow n F).obj X) :
    (symPowSections n G X ((symPowMap n α).app X x) :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (G.obj X)) =
      SymmetricAlgebra.mapₛₗ (RingHom.id _) (α.app X).hom (symPowSections n F X x) := rfl

/-- `symPowMap n α` sends a product of degree-one generators `∏ ι (s i)` to `∏ ι (α (s i))`. -/
theorem symPowMap_app_prod_ι (n : ℕ)
    {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G) (X : Cᵒᵖ)
    (s : Fin n → F.obj X) (x : (symPow n F).obj X)
    (hx : (symPowSections n F X x :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      ∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i)) :
    (symPowSections n G X ((symPowMap n α).app X x) :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (G.obj X)) =
      ∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (G.obj X)
        (α.app X (s i)) := by
  rw [symPowMap_app_coe, hx, map_prod]
  exact Finset.prod_congr rfl fun i _ => SymmetricAlgebra.mapₛₗ_ι _ _ (s i)

/-- `symPowMap n` preserves composition of morphisms. -/
theorem symPowMap_comp (n : ℕ)
    {F G H : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G) (β : G ⟶ H) :
    symPowMap n (α ≫ β) = symPowMap n α ≫ symPowMap n β := by
  refine PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
  exact SymmetricAlgebra.mapₛₗ_eq_comp (α.app X).hom (β.app X).hom ((α ≫ β).app X).hom
    (fun _ => rfl) (fun _ => rfl) _

/-- `symPowMap n` sends the identity morphism of `F` to the identity of `symPow n F`. -/
theorem symPowMap_id (n : ℕ) (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    symPowMap n (𝟙 F) = 𝟙 (symPow n F) := by
  refine PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
  exact SymmetricAlgebra.mapₛₗ_eq_self (PresheafOfModules.Hom.app (𝟙 F) X).hom
    (fun _ => rfl) (fun _ => rfl)
    (↑(PresheafOfModules.symPowSections n F X x) : SymmetricAlgebra _ _)

/-- The action of `PresheafOfModules.extPow n` on a morphism of presheaves of modules. -/
noncomputable def extPowMap (n : ℕ)
    {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G) :
    extPow n F ⟶ extPow n G where
  app X := ModuleCat.ofHom (ExteriorAlgebra.powMapₛₗ n (RingHom.id _) (α.app X).hom)
  naturality {X Y} f := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    have h1 := ExteriorAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (α.app Y).hom
      ((G.restrictₛₗ f).comp (α.app X).hom) (fun _ => rfl)
      (fun m => by rw [LinearMap.comp_apply, PresheafOfModules.restrictₛₗ_apply,
        PresheafOfModules.restrictₛₗ_apply, naturality_apply])
      (↑(PresheafOfModules.extPowSections n F X x) : ExteriorAlgebra _ _)
    have h2 := ExteriorAlgebra.mapₛₗ_eq_comp (α.app X).hom (G.restrictₛₗ f)
      ((G.restrictₛₗ f).comp (α.app X).hom) (fun _ => rfl) (fun _ => rfl)
      (↑(PresheafOfModules.extPowSections n F X x) : ExteriorAlgebra _ _)
    exact h1.symm.trans h2))

/-- Read through `extPowSections`, the sections of `extPowMap n α` are the image under
`ExteriorAlgebra.mapₛₗ` of the sections of `α`. -/
@[simp]
theorem extPowMap_app_coe (n : ℕ)
    {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G) (X : Cᵒᵖ)
    (x : (extPow n F).obj X) :
    (extPowSections n G X ((extPowMap n α).app X x) :
        ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (G.obj X)) =
      ExteriorAlgebra.mapₛₗ (RingHom.id _) (α.app X).hom (extPowSections n F X x) := rfl

/-- `extPowMap n α` sends the wedge `ιMulti s` of degree-one generators to `ιMulti (α ∘ s)`. -/
theorem extPowMap_app_ιMulti (n : ℕ)
    {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G) (X : Cᵒᵖ)
    (s : Fin n → F.obj X) (x : (extPow n F).obj X)
    (hx : (extPowSections n F X x :
        ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      ExteriorAlgebra.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n s) :
    (extPowSections n G X ((extPowMap n α).app X x) :
        ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (G.obj X)) =
      ExteriorAlgebra.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n fun i => α.app X (s i) := by
  rw [extPowMap_app_coe, hx, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply,
    map_list_prod, List.map_ofFn]
  exact congrArg
    (fun g : Fin n → ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (G.obj X) =>
      (List.ofFn g).prod)
    (funext fun i => ExteriorAlgebra.mapₛₗ_ι _ _ (s i))

/-- `extPowMap n` preserves composition of morphisms. -/
theorem extPowMap_comp (n : ℕ)
    {F G H : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G) (β : G ⟶ H) :
    extPowMap n (α ≫ β) = extPowMap n α ≫ extPowMap n β := by
  refine PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
  exact ExteriorAlgebra.mapₛₗ_eq_comp (α.app X).hom (β.app X).hom ((α ≫ β).app X).hom
    (fun _ => rfl) (fun _ => rfl) _

/-- `extPowMap n` sends the identity morphism of `F` to the identity of `extPow n F`. -/
theorem extPowMap_id (n : ℕ) (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    extPowMap n (𝟙 F) = 𝟙 (extPow n F) := by
  refine PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
  exact ExteriorAlgebra.mapₛₗ_eq_self (PresheafOfModules.Hom.app (𝟙 F) X).hom
    (fun _ => rfl) (fun _ => rfl)
    (↑(PresheafOfModules.extPowSections n F X x) : ExteriorAlgebra _ _)

end Functorial

end PresheafOfModules

end
