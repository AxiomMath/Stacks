module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDescFiber
public import StacksFrontier.LinearAlgebra.PerfectPairingCanonicalElement
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.PointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# A fibrewise perfect pairing of sheaves of modules is an exact pairing

Let `(C, J)` be a site with a conservative family `P` of points, `R` a commutative ring, and let
`F`, `G` be sheaves of `R`-modules with the tensor product of
`CategoryTheory.Sheaf.monoidalCategory`. Let `ev : F ⊗ G ⟶ 𝟙` be a pairing. If `G` is locally
constant of finite type and, at every point
`Φ` of the family, the fibre `G_Φ` is finitely generated projective and the induced pairing
`F_Φ × G_Φ → R` is perfect, then `ev` is the evaluation of an exact pairing between `G` and `F`:
there is a coevaluation `η : 𝟙 ⟶ G ⊗ F` satisfying both zigzag identities. In particular
`- ⊗ G` is left adjoint to `- ⊗ F` (`CategoryTheory.tensorRightAdjunction`).

The coevaluation is glued from local data. On each fibre the perfect pairing determines a unique
*canonical* element `c_Φ ∈ (G ⊗ F)_Φ`, the one whose contraction `G_Φ → G_Φ` is the identity
(`Stacks.PerfectPairing.exists_canonical`). A section of `G ⊗ F` is canonical if all its germs
are. Canonical sections exist near every point: a germ representing `c_Φ` is canonical on a
neighbourhood, because `G` is generated there by finitely many sections coming from a
trivialization, and the finitely many sections measuring the failure of the first zigzag identity
on them have zero germ at `Φ`, hence vanish nearby. Canonical sections are unique, since sections
are determined by their germs at a conservative family of points, so they glue to a canonical
section over every object, and these form a morphism `𝟙 ⟶ G ⊗ F`. The zigzag identities are
checked on fibres, the fibre functors being jointly faithful and monoidal.

## Main definitions

* `Stacks.SheafDuality.contraction`: the contraction `(G ⊗ F) ⊗ G ⟶ G` along `ev`.
* `Stacks.SheafDuality.fiberPairing`: the pairing `F_Φ × G_Φ → R` induced by `ev`.
* `Stacks.SheafDuality.IsCanonical`, `Stacks.SheafDuality.IsCanonicalSection`: canonical germs and
  sections.
* `Stacks.SheafDuality.tmulSection`: the tensor product of two sections, as a section of the
  tensor product.
* `Stacks.SheafDuality.coevaluation`: the coevaluation glued from canonical sections.
* `Stacks.SheafDuality.exactPairing`, `Stacks.SheafDuality.exactPairingOfPerfect`: the exact
  pairing.

## Main results

* `Stacks.SheafDuality.germ_tmulSection`: the germ of a tensor product of sections.
* `Stacks.SheafDuality.eq_of_germ_eq`: sections are determined by their germs.
* `Stacks.SheafDuality.exists_isCanonicalSection`: gluing canonical sections.
* `Stacks.SheafDuality.exists_isCanonicalSection_near`: canonical sections exist locally.
* `Stacks.SheafDuality.coevaluation_whiskerRight_contraction`,
  `Stacks.SheafDuality.whiskerLeft_coevaluation_contractionDual`: the zigzag identities.

## Implementation notes

Sheaves take values in `ModuleCat.{w} R` with `R : Type`, the points are relative to the same
universe `w`, and the module category carries the large-universe monoidal structure
`ModuleCat.liftedModuleMonoidal`, whose unit is `ULift R`. A single universe is used so that the
monoidal structure on sheaves is never elaborated at a universe metavariable, where instance
search would pick the same-universe structure of Mathlib instead.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite Functor TensorProduct

universe w v₁ u₁ u

namespace Stacks.SheafDuality

section Elementwise

/-! ### Monoidal functors into modules, on elements -/

variable {R : Type u} [CommRing R] {D : Type*} [Category D] [MonoidalCategory D]
  (Ψ : D ⥤ ModuleCat.{max w u} R) [Ψ.Monoidal]

open Functor.LaxMonoidal

/-- The left unitor of a monoidal functor into modules, on elements. -/
theorem map_leftUnitor_μ_ε (X : D) (r : R) (x : Ψ.obj X) :
    (Ψ.map (λ_ X).hom).hom ((μ Ψ (𝟙_ D) X).hom ((ε Ψ).hom (ULift.up r) ⊗ₜ x)) = r • x :=
  (ConcreteCategory.congr_hom (left_unitality Ψ X) (ULift.up r ⊗ₜ x)).symm

/-- The right unitor of a monoidal functor into modules, on elements. -/
theorem map_rightUnitor_μ_ε (X : D) (r : R) (x : Ψ.obj X) :
    (Ψ.map (ρ_ X).hom).hom ((μ Ψ X (𝟙_ D)).hom (x ⊗ₜ (ε Ψ).hom (ULift.up r))) = r • x :=
  (ConcreteCategory.congr_hom (right_unitality Ψ X) (x ⊗ₜ ULift.up r)).symm

/-- The associator of a monoidal functor into modules, on elements. -/
theorem map_associator_μ_μ (X Y Z : D) (x : Ψ.obj X) (y : Ψ.obj Y) (z : Ψ.obj Z) :
    (Ψ.map (α_ X Y Z).hom).hom ((μ Ψ (X ⊗ Y) Z).hom ((μ Ψ X Y).hom (x ⊗ₜ y) ⊗ₜ z)) =
      (μ Ψ X (Y ⊗ Z)).hom (x ⊗ₜ (μ Ψ Y Z).hom (y ⊗ₜ z)) :=
  ConcreteCategory.congr_hom (associativity Ψ X Y Z) ((x ⊗ₜ y) ⊗ₜ z)

/-- The inverse associator of a monoidal functor into modules, on elements. -/
theorem map_associator_inv_μ_μ (X Y Z : D) (x : Ψ.obj X) (y : Ψ.obj Y) (z : Ψ.obj Z) :
    (Ψ.map (α_ X Y Z).inv).hom ((μ Ψ X (Y ⊗ Z)).hom (x ⊗ₜ (μ Ψ Y Z).hom (y ⊗ₜ z))) =
      (μ Ψ (X ⊗ Y) Z).hom ((μ Ψ X Y).hom (x ⊗ₜ y) ⊗ₜ z) := by
  rw [← map_associator_μ_μ Ψ X Y Z x y z, ← ConcreteCategory.comp_apply, ← Ψ.map_comp,
    Iso.hom_inv_id, Ψ.map_id]
  rfl

/-- Whiskering on the left, through a monoidal functor into modules, on elements. -/
theorem map_whiskerLeft_μ (X : D) {Y Y' : D} (f : Y ⟶ Y') (x : Ψ.obj X) (y : Ψ.obj Y) :
    (Ψ.map (X ◁ f)).hom ((μ Ψ X Y).hom (x ⊗ₜ y)) = (μ Ψ X Y').hom (x ⊗ₜ (Ψ.map f).hom y) :=
  (ConcreteCategory.congr_hom (μ_natural_right Ψ X f) (x ⊗ₜ y)).symm

/-- Whiskering on the right, through a monoidal functor into modules, on elements. -/
theorem map_whiskerRight_μ {X X' : D} (f : X ⟶ X') (Y : D) (x : Ψ.obj X) (y : Ψ.obj Y) :
    (Ψ.map (f ▷ Y)).hom ((μ Ψ X Y).hom (x ⊗ₜ y)) = (μ Ψ X' Y).hom ((Ψ.map f).hom x ⊗ₜ y) :=
  (ConcreteCategory.congr_hom (μ_natural_left Ψ f Y) (x ⊗ₜ y)).symm

/-- The value of a monoidal functor into modules at the unit is free of rank one, generated by
the image of `1` under the unit constraint. -/
def unitEquiv : Ψ.obj (𝟙_ D) ≃ₗ[R] R :=
  (Functor.Monoidal.εIso Ψ).symm.toLinearEquiv.trans ULift.moduleEquiv

/-- The unit constraint sends the image of `u` under `unitEquiv` back to `u`. -/
theorem ε_unitEquiv (u : Ψ.obj (𝟙_ D)) : (ε Ψ).hom (ULift.up (unitEquiv Ψ u)) = u :=
  ConcreteCategory.congr_hom (Functor.Monoidal.εIso Ψ).inv_hom_id u

/-- `unitEquiv` sends the image of `r` under the unit constraint to `r`. -/
theorem unitEquiv_ε (r : R) : unitEquiv Ψ ((ε Ψ).hom (ULift.up r)) = r :=
  congrArg ULift.down (ConcreteCategory.congr_hom (Functor.Monoidal.εIso Ψ).hom_inv_id
    (ULift.up r))

end Elementwise


section Fibers

/-! ### The fibrewise contractions of a pairing `F ⊗ G ⟶ 𝟙` -/

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type} [CommRing R]
  [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)]
  [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{w} R)]

attribute [local instance] Sheaf.monoidalCategory


open Functor.LaxMonoidal

/-- The fibre functor at a point of the site, on sheaves of `R`-modules. -/
abbrev moduleFiber (R : Type) [CommRing R] (Φ : J.Point.{w}) :
    Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
  Φ.sheafFiber

variable {F G : Sheaf J (ModuleCat.{w} R)} (ev : F ⊗ G ⟶ 𝟙_ _)

/-- The contraction `(G ⊗ F) ⊗ G ⟶ G` of the middle two factors along `ev`. -/
def contraction : (G ⊗ F) ⊗ G ⟶ G :=
  (α_ G F G).hom ≫ G ◁ ev ≫ (ρ_ G).hom

/-- The contraction `F ⊗ (G ⊗ F) ⟶ F` of the first two factors along `ev`. -/
def contractionDual : F ⊗ (G ⊗ F) ⟶ F :=
  (α_ F G F).inv ≫ ev ▷ F ≫ (λ_ F).hom

variable (Φ : J.Point.{w})

/-- The pairing `F_Φ × G_Φ → R` induced by `ev` on the fibres at `Φ`. -/
def fiberPairing : (moduleFiber R Φ).obj F →ₗ[R] (moduleFiber R Φ).obj G →ₗ[R] R :=
  TensorProduct.curry ((unitEquiv (moduleFiber R Φ)).toLinearMap ∘ₗ
    (μ (moduleFiber R Φ) F G ≫ (moduleFiber R Φ).map ev).hom)

omit [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)] in
/-- The pairing `ev` on fibres: `b ⊗ g ↦ ⟨b, g⟩`, read through the unit constraint. -/
theorem map_ev_μ (b : (moduleFiber R Φ).obj F) (g : (moduleFiber R Φ).obj G) :
    ((moduleFiber R Φ).map ev).hom ((μ (moduleFiber R Φ) F G).hom (b ⊗ₜ g)) =
      (ε (moduleFiber R Φ)).hom (ULift.up (fiberPairing ev Φ b g)) :=
  (ε_unitEquiv (moduleFiber R Φ) _).symm

omit [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)] in
/-- The contraction on fibres: `(a ⊗ b) ⊗ g ↦ ⟨b, g⟩ • a`. -/
theorem map_contraction_μ_μ (a : (moduleFiber R Φ).obj G) (b : (moduleFiber R Φ).obj F)
    (g : (moduleFiber R Φ).obj G) :
    ((moduleFiber R Φ).map (contraction ev)).hom
        ((μ (moduleFiber R Φ) (G ⊗ F) G).hom ((μ (moduleFiber R Φ) G F).hom (a ⊗ₜ b) ⊗ₜ g)) =
      fiberPairing ev Φ b g • a := by
  simp only [contraction, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [map_associator_μ_μ, map_whiskerLeft_μ, map_ev_μ, map_rightUnitor_μ_ε]

omit [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)] in
/-- The dual contraction on fibres: `f ⊗ (a ⊗ b) ↦ ⟨f, a⟩ • b`. -/
theorem map_contractionDual_μ_μ (f : (moduleFiber R Φ).obj F) (a : (moduleFiber R Φ).obj G)
    (b : (moduleFiber R Φ).obj F) :
    ((moduleFiber R Φ).map (contractionDual ev)).hom
        ((μ (moduleFiber R Φ) F (G ⊗ F)).hom (f ⊗ₜ (μ (moduleFiber R Φ) G F).hom (a ⊗ₜ b))) =
      fiberPairing ev Φ f a • b := by
  simp only [contractionDual, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [map_associator_inv_μ_μ, map_whiskerRight_μ, map_ev_μ, map_leftUnitor_μ_ε]

/-- An element of the fibre of `G ⊗ F` is *canonical* at `Φ` if contracting with it is the
identity of the fibre of `G`. -/
def IsCanonical (d : (moduleFiber R Φ).obj (G ⊗ F)) : Prop :=
  ∀ g, ((moduleFiber R Φ).map (contraction ev)).hom
    ((μ (moduleFiber R Φ) (G ⊗ F) G).hom (d ⊗ₜ g)) = g

omit [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)] in
/-- The contraction on fibres is the contraction `Stacks.PerfectPairing.contract` of the fibre
pairing. -/
theorem map_contraction_μ_eq_contract (d : (moduleFiber R Φ).obj G ⊗[R] (moduleFiber R Φ).obj F)
    (g : (moduleFiber R Φ).obj G) :
    ((moduleFiber R Φ).map (contraction ev)).hom
        ((μ (moduleFiber R Φ) (G ⊗ F) G).hom ((μ (moduleFiber R Φ) G F).hom d ⊗ₜ g)) =
      Stacks.PerfectPairing.contract (fiberPairing ev Φ) d g := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [map_contraction_μ_μ]; rfl
  | add x y hx hy => simp only [_root_.map_add, add_tmul, hx, hy, LinearMap.add_apply]

omit [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)] in
/-- The dual contraction on fibres is the contraction `Stacks.PerfectPairing.contractDual` of
the fibre pairing. -/
theorem map_contractionDual_μ_eq_contractDual (f : (moduleFiber R Φ).obj F)
    (d : (moduleFiber R Φ).obj G ⊗[R] (moduleFiber R Φ).obj F) :
    ((moduleFiber R Φ).map (contractionDual ev)).hom
        ((μ (moduleFiber R Φ) F (G ⊗ F)).hom (f ⊗ₜ (μ (moduleFiber R Φ) G F).hom d)) =
      Stacks.PerfectPairing.contractDual (fiberPairing ev Φ) d f := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [map_contractionDual_μ_μ]; rfl
  | add x y hx hy => simp only [_root_.map_add, tmul_add, hx, hy, LinearMap.add_apply]

omit [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)] in
/-- **The canonical element of a fibre.** If the fibre of `G` at `Φ` is finitely generated
projective and the fibre pairing is perfect, the fibre of `G ⊗ F` has exactly one canonical
element, and the dual contraction with it is the identity of the fibre of `F`. -/
theorem existsUnique_isCanonical [Module.Finite R ((moduleFiber R Φ).obj G)]
    [Module.Projective R ((moduleFiber R Φ).obj G)] (hp : Function.Bijective (fiberPairing ev Φ)) :
    ∃ c, IsCanonical ev Φ c ∧ (∀ d, IsCanonical ev Φ d → d = c) ∧
      ∀ f, ((moduleFiber R Φ).map (contractionDual ev)).hom
        ((μ (moduleFiber R Φ) F (G ⊗ F)).hom (f ⊗ₜ c)) = f := by
  obtain ⟨c, hc, hu, hd⟩ := Stacks.PerfectPairing.exists_canonical hp
  have hiso : Function.Bijective (μ (moduleFiber R Φ) G F).hom :=
    (ConcreteCategory.bijective_of_isIso (μ (moduleFiber R Φ) G F))
  refine ⟨(μ (moduleFiber R Φ) G F).hom c, fun g => ?_, fun d h => ?_, fun f => ?_⟩
  · rw [map_contraction_μ_eq_contract]; exact hc g
  · obtain ⟨d, rfl⟩ := hiso.2 d
    refine congrArg _ (hu d fun g => ?_)
    rw [← map_contraction_μ_eq_contract]; exact h g
  · rw [map_contractionDual_μ_eq_contractDual]; exact hd f

/-- Morphisms out of a tensor product of sheaves agree if their fibres agree on tensors of
elements, at the points of a jointly faithful family. -/
private theorem hom_ext_of_forall_fiber_tmul {ι : Type*} {Φ : ι → J.Point.{w}}
    (hΦ : JointlyFaithful fun i => moduleFiber R (Φ i)) {X Y Z : Sheaf J (ModuleCat.{w} R)}
    {f g : X ⊗ Y ⟶ Z}
    (h : ∀ i x y,
      ((moduleFiber R (Φ i)).map f).hom ((μ (moduleFiber R (Φ i)) X Y).hom (x ⊗ₜ y)) =
        ((moduleFiber R (Φ i)).map g).hom ((μ (moduleFiber R (Φ i)) X Y).hom (x ⊗ₜ y))) :
    f = g := by
  have := ‹HasColimitsOfSize.{w, w} (ModuleCat.{w} R)›
  exact hΦ.map_injective fun i => (cancel_epi (μ (moduleFiber R (Φ i)) X Y)).1
    (ModuleCat.hom_ext (TensorProduct.ext' (h i)))

end Fibers

section Germs

/-! ### Germs of sections, and of tensor products of sections -/

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type} [CommRing R]
  [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)]
  [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{w} R)]

attribute [local instance] Sheaf.monoidalCategory


open Functor.LaxMonoidal

/-- The germ at `x ∈ Φ(U)` of a section over `U` of a sheaf of modules. -/
abbrev germ (Φ : J.Point.{w}) {U : C} (x : Φ.fiber.obj U)
    (P : Sheaf J (ModuleCat.{w} R)) : P.obj.obj (op U) →ₗ[R] (moduleFiber R Φ).obj P :=
  (Φ.toPresheafFiber U x P.obj).hom

omit [LocallySmall.{w} C] [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{w} R)] in
/-- The germ at `y` of the restriction of a section along `f` is the germ of the section at the
image of `y`. -/
theorem germ_map (Φ : J.Point.{w}) {U V : C} (f : V ⟶ U) (y : Φ.fiber.obj V)
    (P : Sheaf J (ModuleCat.{w} R)) (a : P.obj.obj (op U)) :
    germ Φ y P ((P.obj.map f.op).hom a) = germ Φ (Φ.fiber.map f y) P a :=
  ConcreteCategory.congr_hom (Φ.toPresheafFiber_w f y P.obj) a

omit [LocallySmall.{w} C] [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{w} R)] in
/-- Germs are natural in the sheaf: the fibre of a morphism sends the germ of a section to the
germ of its image. -/
theorem germ_naturality (Φ : J.Point.{w}) {U : C} (x : Φ.fiber.obj U)
    {P Q : Sheaf J (ModuleCat.{w} R)} (g : P ⟶ Q) (a : P.obj.obj (op U)) :
    ((moduleFiber R Φ).map g).hom (germ Φ x P a) = germ Φ x Q ((g.hom.app (op U)).hom a) :=
  ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality g.hom U x) a

variable (A B : Sheaf J (ModuleCat.{w} R))

/-- The sheafification of the sectionwise tensor product of two sheaves is their tensor
product. -/
def tensorComparison :
    (presheafToSheaf J (ModuleCat.{w} R)).obj (A.obj ⊗ B.obj) ≅ A ⊗ B :=
  (Functor.Monoidal.μIso (presheafToSheaf J (ModuleCat.{w} R)) A.obj B.obj).symm ≪≫
    (sheafificationIso A ⊗ᵢ sheafificationIso B).symm

/-- The tensor product of two sections over the same object, as a section of the tensor product
of the sheaves. -/
def tmulSection (U : Cᵒᵖ) : A.obj.obj U →ₗ[R] B.obj.obj U →ₗ[R] (A ⊗ B).obj.obj U :=
  TensorProduct.curry (((tensorComparison A B).hom.hom.app U).hom ∘ₗ
    ((toSheafify J (A.obj ⊗ B.obj)).app U).hom)

omit [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)]
  [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)] in
/-- The tensor product of sections commutes with restriction. -/
theorem tmulSection_map {U V : Cᵒᵖ} (f : U ⟶ V) (a : A.obj.obj U) (b : B.obj.obj U) :
    ((A ⊗ B).obj.map f).hom (tmulSection A B U a b) =
      tmulSection A B V ((A.obj.map f).hom a) ((B.obj.map f).hom b) := by
  have h1 := ConcreteCategory.congr_hom ((tensorComparison A B).hom.hom.naturality f)
    (((toSheafify J (A.obj ⊗ B.obj)).app U).hom (a ⊗ₜ b))
  have h2 := ConcreteCategory.congr_hom ((toSheafify J (A.obj ⊗ B.obj)).naturality f) (a ⊗ₜ b)
  exact h1.symm.trans (congrArg ((tensorComparison A B).hom.hom.app V).hom h2.symm)

omit [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)]
  [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)] in
/-- The morphism of presheaves induced by `tmulSection` is the unit of sheafification followed
by `tensorComparison`. -/
theorem presheafTensorDesc_tmulSection :
    Sheaf.presheafTensorDesc.{w, v₁, u₁, 0} (H := (A ⊗ B).obj) (tmulSection A B)
        (tmulSection_map A B) =
      toSheafify J (A.obj ⊗ B.obj) ≫ (tensorComparison A B).hom.hom := by
  ext U : 2
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  rfl

omit [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)]
  [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)] in
/-- The morphism of sheaves induced by `tmulSection` is the identity of `A ⊗ B`. -/
theorem tensorDesc_tmulSection :
    Sheaf.tensorDesc.{w, v₁, u₁, 0} (H := A ⊗ B) (tmulSection A B) (tmulSection_map A B) =
      𝟙 (A ⊗ B) := by
  have h : ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _).symm
      (Sheaf.presheafTensorDesc.{w, v₁, u₁, 0} (H := (A ⊗ B).obj) (tmulSection A B)
        (tmulSection_map A B)) =
        (tensorComparison A B).hom := by
    rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app,
      presheafTensorDesc_tmulSection]
    rfl
  rw [Sheaf.tensorDesc, h, tensorComparison]
  simp

/-- **The germ of a tensor product of sections** is the tensor product of the germs, read
through the monoidal structure of the fibre functor. -/
theorem germ_tmulSection (Φ : J.Point.{w}) {U : C} (x : Φ.fiber.obj U)
    (a : A.obj.obj (op U)) (b : B.obj.obj (op U)) :
    germ Φ x (A ⊗ B) (tmulSection A B (op U) a b) =
      (μ (moduleFiber R Φ) A B).hom (germ Φ x A a ⊗ₜ germ Φ x B b) := by
  have h := Sheaf.sheafFiber_tensorDesc_tmul.{w, w, v₁, u₁, 0} (H := A ⊗ B) Φ (tmulSection A B)
    (tmulSection_map A B) U x a b
  rw [tensorDesc_tmulSection, CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h.symm

end Germs

section Glue

/-! ### Gluing sections which are canonical at every point -/

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type} [CommRing R]
  [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)]
  [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{w} R)]
  [PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{w} R))]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]
  {P : ObjectProperty (J.Point.{w})} (hP : P.IsConservativeFamilyOfPoints)
  [ObjectProperty.Small.{w} P] [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

attribute [local instance] Sheaf.monoidalCategory

include hP in
/-- A sieve is covering as soon as every element of the fibre of every point of a conservative
family lifts along one of its arrows. -/
theorem mem_of_forall_lift {U : C} (S : Sieve U)
    (h : ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj U),
      ∃ (V : C) (f : V ⟶ U) (y : Φ.obj.fiber.obj V), S f ∧ Φ.obj.fiber.map f y = x) :
    S ∈ J U := by
  obtain ⟨I, Y, f, rfl⟩ := S.exists_eq_ofArrows
  rw [hP.jointly_reflect_ofArrows_mem_of_small]
  intro Φ x
  obtain ⟨V, g, y, ⟨Z, p, q, ⟨i⟩, rfl⟩, rfl⟩ := h Φ x
  exact ⟨i, Φ.obj.fiber.map p y, by simp⟩

include hP in
omit [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{w} R)] in
/-- **Sections are determined by their germs** at the points of a conservative family. -/
theorem eq_of_germ_eq {H : Sheaf J (ModuleCat.{w} R)} {U : C} {a b : H.obj.obj (op U)}
    (h : ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj U),
      germ Φ.obj x H a = germ Φ.obj x H b) : a = b := by
  have hS : Presheaf.equalizerSieve (F := H.obj) (X := op U) a b ∈ J U :=
    mem_of_forall_lift hP _ fun Φ x => by
      obtain ⟨V, f, y, hy, hab⟩ := (Φ.obj.toPresheafFiber_eq_iff' U x a b).1 (h Φ x)
      exact ⟨V, f, y, hab, hy⟩
  have hsh := (isSheaf_iff_isSheaf_of_type J _).1
    ((sheafCompose J (forget (ModuleCat.{w} R))).obj H).property
  exact (hsh _ hS).isSeparatedFor.ext fun V f hf => hf

variable {F G : Sheaf J (ModuleCat.{w} R)} (ev : F ⊗ G ⟶ 𝟙_ _)

variable (P) in
/-- A section of `G ⊗ F` is *canonical* if its germ at every point of the family is canonical. -/
def IsCanonicalSection {V : C} (t : (G ⊗ F).obj.obj (op V)) : Prop :=
  ∀ (Φ : P.FullSubcategory) (y : Φ.obj.fiber.obj V),
    IsCanonical ev Φ.obj (germ Φ.obj y (G ⊗ F) t)

omit [PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{w} R))]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]
  [ObjectProperty.Small.{w} P] [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)] in
/-- The restriction of a canonical section is canonical. -/
theorem IsCanonicalSection.map {V W : C} {t : (G ⊗ F).obj.obj (op V)}
    (ht : IsCanonicalSection P ev t) (f : W ⟶ V) :
    IsCanonicalSection P ev (((G ⊗ F).obj.map f.op).hom t) := fun Φ y => by
  rw [germ_map]
  exact ht Φ _

include hP in
/-- If canonical germs are unique, then any two canonical sections over the same object are
equal. -/
theorem IsCanonicalSection.eq
    (hu : ∀ (Φ : P.FullSubcategory) (d d'), IsCanonical ev Φ.obj d → IsCanonical ev Φ.obj d' →
      d = d')
    {V : C} {t t' : (G ⊗ F).obj.obj (op V)} (ht : IsCanonicalSection P ev t)
    (ht' : IsCanonicalSection P ev t') : t = t' :=
  eq_of_germ_eq hP fun Φ y => hu Φ _ _ (ht Φ y) (ht' Φ y)

include hP in
/-- **Gluing canonical sections.** If canonical germs are unique and canonical sections exist
near every element of every fibre, then there is a canonical section over every object. -/
theorem exists_isCanonicalSection
    (hu : ∀ (Φ : P.FullSubcategory) (d d'), IsCanonical ev Φ.obj d → IsCanonical ev Φ.obj d' →
      d = d')
    (hloc : ∀ (Φ : P.FullSubcategory) (U : C) (x : Φ.obj.fiber.obj U),
      ∃ (V : C) (f : V ⟶ U) (y : Φ.obj.fiber.obj V), Φ.obj.fiber.map f y = x ∧
        ∃ t : (G ⊗ F).obj.obj (op V), IsCanonicalSection P ev t)
    (U : C) : ∃ t : (G ⊗ F).obj.obj (op U), IsCanonicalSection P ev t := by
  let S : Sieve U :=
    { arrows := fun V _ => ∃ t : (G ⊗ F).obj.obj (op V), IsCanonicalSection P ev t
      downward_closed := fun {_ _} _ ⟨t, ht⟩ g => ⟨_, ht.map ev g⟩ }
  have hS : S ∈ J U := mem_of_forall_lift hP S fun Φ x => by
    obtain ⟨V, f, y, hy, ht⟩ := hloc Φ U x
    exact ⟨V, f, y, ht, hy⟩
  have hsh := (isSheaf_iff_isSheaf_of_type J _).1
    ((sheafCompose J (forget (ModuleCat.{w} R))).obj (G ⊗ F)).property _ hS
  let fam : Presieve.FamilyOfElements ((G ⊗ F).obj ⋙ forget (ModuleCat.{w} R)) S.arrows :=
    fun _ _ hf => hf.choose
  have hc : fam.Compatible := fun _ _ _ g₁ g₂ _ _ h₁ h₂ _ =>
    IsCanonicalSection.eq hP ev hu (h₁.choose_spec.map ev g₁) (h₂.choose_spec.map ev g₂)
  obtain ⟨t, ht⟩ : ∃ t : (G ⊗ F).obj.obj (op U), ∀ (V : C) (f : V ⟶ U) (hf : S.arrows f),
      ((G ⊗ F).obj.map f.op).hom t = hf.choose :=
    ⟨hsh.amalgamate fam hc, fun _ f hf => hsh.valid_glue hc f hf⟩
  refine ⟨t, fun Φ z => ?_⟩
  obtain ⟨V, f, hf, y, rfl⟩ := Φ.obj.jointly_surjective S hS z
  rw [← germ_map, ht V f hf]
  exact hf.choose_spec Φ y

end Glue

section Local

/-! ### Local sections of a locally constant sheaf generate its fibres -/

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type} [CommRing R]
  [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)]
  [PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{w} R))]
  [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- The section over `V` of a sheaf `G` attached, through a trivialization of `G` over `V`, to an
element of the constant value. -/
def constSection {G : Sheaf J (ModuleCat.{w} R)} {V : C} {E : ModuleCat.{w} R}
    (e : (constantSheaf (J.over V) (ModuleCat.{w} R)).obj E ≅
      (J.overPullback (ModuleCat.{w} R) V).obj G) :
    E →ₗ[R] G.obj.obj (op V) :=
  (e.hom.hom.app (op (Over.mk (𝟙 V)))).hom ∘ₗ
    ((toSheafify (J.over V) ((Functor.const _).obj E)).app (op (Over.mk (𝟙 V)))).hom

/-- Through the identification of the fibre of a trivialized sheaf with the constant value, the
germ of the section attached to `m` is `m`. -/
theorem sheafFiberIsoOfConstantOver_germ_constSection {G : Sheaf J (ModuleCat.{w} R)} {V : C}
    {E : ModuleCat.{w} R}
    (e : (constantSheaf (J.over V) (ModuleCat.{w} R)).obj E ≅
      (J.overPullback (ModuleCat.{w} R) V).obj G)
    (Ψ : J.Point.{w}) (y : Ψ.fiber.obj V) (m : E) :
    (Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver Ψ y G E e).hom.hom
        ((Ψ.toPresheafFiber V y G.obj).hom (constSection e m)) = m := by
  let y' : (Ψ.over y).fiber.obj (Over.mk (𝟙 V)) :=
    ⟨y, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 (by simp)⟩
  have ha : (Ψ.over y).toPresheafFiber (Over.mk (𝟙 V)) y' ((Over.forget V).op ⋙ G.obj) ≫
      ((GrothendieckTopology.Point.presheafFiberOverIso Ψ y (ModuleCat.{w} R)).app G.obj).hom =
        Ψ.toPresheafFiber V y G.obj :=
    Functor.Final.ι_colimitIso_hom (GrothendieckTopology.Point.overElements Ψ y).op
      ((CategoryOfElements.π Ψ.fiber).op ⋙ G.obj) (op ⟨Over.mk (𝟙 V), y'⟩)
  let c := ((toSheafify (J.over V) ((Functor.const _).obj E)).app (op (Over.mk (𝟙 V)))).hom m
  let d := (e.hom.hom.app (op (Over.mk (𝟙 V)))).hom c
  let κ := (Sites.constantSheafFiberIso (Ψ.over y) E).hom.hom
  -- the constant value of the germ of the constant section
  have hc : κ (((Ψ.over y).toPresheafFiber (Over.mk (𝟙 V)) y'
        (sheafify (J.over V) ((Functor.const _).obj E))).hom c) = m := by
    have h1 := ConcreteCategory.congr_hom ((Ψ.over y).toPresheafFiber_naturality
      (toSheafify (J.over V) ((Functor.const _).obj E)) (Over.mk (𝟙 V)) y') m
    have h2 := ConcreteCategory.congr_hom
      (Sites.presheafFiber_map_toSheafify_comp_constantSheafFiberIso (Ψ.over y) E)
      (((Ψ.over y).toPresheafFiber (Over.mk (𝟙 V)) y' ((Functor.const _).obj E)).hom m)
    have h3 := ConcreteCategory.congr_hom
      (Sites.constantPresheafFiberIso_ι (Ψ.over y) E (Over.mk (𝟙 V)) y') m
    exact (congrArg κ h1.symm).trans (h2.trans h3)
  -- transport through the trivialization
  have he : (e.inv.hom.app (op (Over.mk (𝟙 V)))).hom d = c :=
    ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op (Over.mk (𝟙 V))))
      e.hom_inv_id) c
  have hb := ConcreteCategory.congr_hom ((Ψ.over y).toPresheafFiber_naturality e.inv.hom
    (Over.mk (𝟙 V)) y') d
  -- the comparison of fibres along the localization
  have hi := ConcreteCategory.congr_hom
    (((Ψ.sheafFiberOverIso y (ModuleCat.{w} R)).app G).hom_inv_id)
    (((Ψ.over y).toPresheafFiber (Over.mk (𝟙 V)) y' ((Over.forget V).op ⋙ G.obj)).hom d)
  have ha' := ConcreteCategory.congr_hom ha d
  refine (congrArg (fun z => κ (((Ψ.over y).sheafFiber.map e.inv).hom
    (((Ψ.sheafFiberOverIso y (ModuleCat.{w} R)).app G).inv.hom z))) ha'.symm).trans ?_
  refine (congrArg (fun z => κ (((Ψ.over y).sheafFiber.map e.inv).hom z)) hi).trans ?_
  refine (congrArg κ hb).trans ?_
  exact (congrArg (fun z => κ (((Ψ.over y).toPresheafFiber (Over.mk (𝟙 V)) y'
    (sheafify (J.over V) ((Functor.const _).obj E))).hom z)) he).trans hc

/-- The germs of the sections attached to a trivialization exhaust the fibre. -/
theorem exists_germ_constSection_eq {G : Sheaf J (ModuleCat.{w} R)} {V : C}
    {E : ModuleCat.{w} R}
    (e : (constantSheaf (J.over V) (ModuleCat.{w} R)).obj E ≅
      (J.overPullback (ModuleCat.{w} R) V).obj G)
    (Ψ : J.Point.{w}) (y : Ψ.fiber.obj V)
    (g : (Ψ.presheafFiber (A := ModuleCat.{w} R)).obj G.obj) :
    ∃ m : E, (Ψ.toPresheafFiber V y G.obj).hom (constSection e m) = g :=
  ⟨(Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver Ψ y G E e).hom.hom g,
    (ConcreteCategory.bijective_of_isIso
      (Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver Ψ y G E e).hom).1
      (sheafFiberIsoOfConstantOver_germ_constSection e Ψ y _)⟩

omit [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).WEqualsLocallyBijective (ModuleCat.{w} R)] in
/-- Finitely many sections with vanishing germs vanish together on a smaller neighbourhood. -/
theorem exists_map_eq_zero_of_germ_eq_zero (Φ : J.Point.{w}) {H : Cᵒᵖ ⥤ ModuleCat.{w} R}
    {W : C} (w₀ : Φ.fiber.obj W) {n : ℕ} (σ : Fin n → H.obj (op W))
    (hσ : ∀ j, (Φ.toPresheafFiber W w₀ H).hom (σ j) = 0) :
    ∃ (W' : C) (h : W' ⟶ W) (w' : Φ.fiber.obj W'), Φ.fiber.map h w' = w₀ ∧
      ∀ j, (H.map h.op).hom (σ j) = 0 := by
  induction n with
  | zero => exact ⟨W, 𝟙 W, w₀, by simp, fun j => j.elim0⟩
  | succ n ih =>
    obtain ⟨W₁, h₁, w₁, hw₁, h0⟩ := ih (fun j => σ j.castSucc) (fun j => hσ _)
    have h1 : (Φ.toPresheafFiber W₁ w₁ H).hom ((H.map h₁.op).hom (σ (Fin.last n))) =
        (Φ.toPresheafFiber W₁ w₁ H).hom 0 := by
      rw [map_zero]
      refine (ConcreteCategory.congr_hom (Φ.toPresheafFiber_w h₁ w₁ H) (σ (Fin.last n))).trans ?_
      rw [hw₁]
      exact hσ _
    obtain ⟨W₂, f, w₂, hw₂, h2⟩ := (Φ.toPresheafFiber_eq_iff' W₁ w₁ _ _).1 h1
    refine ⟨W₂, f ≫ h₁, w₂, by simp [hw₂, hw₁], fun j => ?_⟩
    rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact h2.trans (map_zero _)
    · rw [h0 i, map_zero]

/-- The fibres of a locally constant sheaf of finite type are finitely generated. -/
theorem finite_sheafFiber_of_isFiniteTypeLocallyConstant {G : Sheaf J (ModuleCat.{w} R)}
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J G) (Φ : J.Point.{w}) :
    Module.Finite R ((moduleFiber R Φ).obj G) := by
  obtain ⟨⟨X, x⟩⟩ : Nonempty Φ.fiber.Elements := IsCofiltered.nonempty
  obtain ⟨I, V, f, hcov, htriv⟩ := hG X
  obtain ⟨Y₀, g, ⟨Z, p, q, ⟨i⟩, rfl⟩, y₀, -⟩ := Φ.jointly_surjective _ hcov x
  obtain ⟨E, hE, ⟨e⟩⟩ := htriv i
  have : Module.Finite R E := hE
  exact Module.Finite.equiv (Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver Φ
    (Φ.fiber.map p y₀) G E e).toLinearEquiv.symm

end Local

section Existence

/-! ### Canonical sections exist near every point -/

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type} [CommRing R]
  [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)]
  [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{w} R)]
  [PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{w} R))]
  [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).WEqualsLocallyBijective (ModuleCat.{w} R)]
  {P : ObjectProperty (J.Point.{w})}

attribute [local instance] Sheaf.monoidalCategory


open Functor.LaxMonoidal

variable {F G : Sheaf J (ModuleCat.{w} R)} (ev : F ⊗ G ⟶ 𝟙_ _)

/-- **Canonical sections exist near every point**, for `G` locally constant of finite type, as
soon as every fibre has a canonical element. -/
theorem exists_isCanonicalSection_near
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J G)
    (hex : ∀ (Φ : P.FullSubcategory), ∃ c, IsCanonical ev Φ.obj c)
    (Φ : P.FullSubcategory) (U : C) (x : Φ.obj.fiber.obj U) :
    ∃ (V : C) (f : V ⟶ U) (y : Φ.obj.fiber.obj V), Φ.obj.fiber.map f y = x ∧
      ∃ t : (G ⊗ F).obj.obj (op V), IsCanonicalSection P ev t := by
  obtain ⟨I, V, f, hcov, htriv⟩ := hG U
  obtain ⟨Y₀, g, ⟨Z, p, q, ⟨i⟩, rfl⟩, y₀, hy₀⟩ := Φ.obj.jointly_surjective _ hcov x
  obtain ⟨E, hE, ⟨e⟩⟩ := htriv i
  have : Module.Finite R E := hE
  obtain ⟨n, gen, hgen⟩ := Module.Finite.exists_fin (R := R) (M := E)
  obtain ⟨c, hc⟩ := hex Φ
  obtain ⟨W₀, w₀, t₀, ht₀⟩ := Φ.obj.toPresheafFiber_jointly_surjective (P := (G ⊗ F).obj) c
  let a : Φ.obj.fiber.Elements := Φ.obj.fiber.elementsMk (V i) (Φ.obj.fiber.map p y₀)
  let b : Φ.obj.fiber.Elements := Φ.obj.fiber.elementsMk W₀ w₀
  let ka := IsCofiltered.minToLeft a b
  let kb := IsCofiltered.minToRight a b
  let W₁ : C := (IsCofiltered.min a b).1
  let w₁ : Φ.obj.fiber.obj W₁ := (IsCofiltered.min a b).2
  let t₁ : (G ⊗ F).obj.obj (op W₁) := ((G ⊗ F).obj.map kb.1.op).hom t₀
  have ht₁ : germ Φ.obj w₁ (G ⊗ F) t₁ = c := by rwa [germ_map, kb.2]
  let gj : Fin n → G.obj.obj (op W₁) := fun j => (G.obj.map ka.1.op).hom (constSection e (gen j))
  let κ : ∀ W : C, ((G ⊗ F) ⊗ G).obj.obj (op W) →ₗ[R] G.obj.obj (op W) :=
    fun W => ((contraction ev).hom.app (op W)).hom
  let σ : Fin n → G.obj.obj (op W₁) := fun j =>
    κ W₁ (tmulSection (G ⊗ F) G (op W₁) t₁ (gj j)) - gj j
  have hσ : ∀ j, (Φ.obj.toPresheafFiber W₁ w₁ G.obj).hom (σ j) = 0 := by
    intro j
    show germ Φ.obj w₁ G (σ j) = 0
    simp only [σ, _root_.map_sub]
    rw [sub_eq_zero, ← germ_naturality, germ_tmulSection, ht₁]
    exact hc _
  obtain ⟨W₂, k, w₂, hw₂, h0⟩ := exists_map_eq_zero_of_germ_eq_zero Φ.obj w₁ σ hσ
  refine ⟨W₂, k ≫ ka.1 ≫ f i, w₂, ?_, ((G ⊗ F).obj.map k.op).hom t₁, fun Ψ z g => ?_⟩
  · simp only [FunctorToTypes.map_comp_apply, hw₂]
    show Φ.obj.fiber.map (f i) (Φ.obj.fiber.map ka.1 w₁) = _
    rw [ka.2]
    simpa using hy₀
  · let z₁ : Ψ.obj.fiber.obj (V i) := Ψ.obj.fiber.map (k ≫ ka.1) z
    obtain ⟨m, rfl⟩ := exists_germ_constSection_eq e Ψ.obj z₁ g
    have key : (((moduleFiber R Ψ.obj).map (contraction ev)).hom ∘ₗ
        (μ (moduleFiber R Ψ.obj) (G ⊗ F) G).hom ∘ₗ
        (TensorProduct.mk R _ _ (germ Ψ.obj z (G ⊗ F) (((G ⊗ F).obj.map k.op).hom t₁)))) ∘ₗ
          (germ Ψ.obj z₁ G ∘ₗ constSection e) = germ Ψ.obj z₁ G ∘ₗ constSection e := by
      refine LinearMap.ext_on_range hgen fun j => ?_
      show ((moduleFiber R Ψ.obj).map (contraction ev)).hom
        ((μ (moduleFiber R Ψ.obj) (G ⊗ F) G).hom
        (germ Ψ.obj z (G ⊗ F) (((G ⊗ F).obj.map k.op).hom t₁) ⊗ₜ
          germ Ψ.obj z₁ G (constSection e (gen j)))) = germ Ψ.obj z₁ G (constSection e (gen j))
      have h1 : germ Ψ.obj z₁ G (constSection e (gen j)) =
          germ Ψ.obj z G ((G.obj.map k.op).hom (gj j)) := by
        rw [germ_map, germ_map, ← FunctorToTypes.map_comp_apply]
      have h2 : ((contraction ev).hom.app (op W₂)).hom
          ((((G ⊗ F) ⊗ G).obj.map k.op).hom (tmulSection (G ⊗ F) G (op W₁) t₁ (gj j))) =
            (G.obj.map k.op).hom (((contraction ev).hom.app (op W₁)).hom
              (tmulSection (G ⊗ F) G (op W₁) t₁ (gj j))) :=
        ConcreteCategory.congr_hom ((contraction ev).hom.naturality k.op) _
      have h3 : ((contraction ev).hom.app (op W₁)).hom
          (tmulSection (G ⊗ F) G (op W₁) t₁ (gj j)) = σ j + gj j := by
        simp only [σ, κ, sub_add_cancel]
      rw [h1, ← germ_tmulSection, germ_naturality, ← tmulSection_map, h2, h3, _root_.map_add,
        h0 j, zero_add]
    exact LinearMap.congr_fun key m

end Existence

section Coevaluation

/-! ### The coevaluation, glued from canonical sections -/

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type} [CommRing R]
  [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} (ModuleCat.{w} R)]
  [HasProducts.{w} (ModuleCat.{w} R)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : ModuleCat.{w} R, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{w} R)]
  [PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{w} R))]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]
  [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).WEqualsLocallyBijective (ModuleCat.{w} R)]
  {P : ObjectProperty (J.Point.{w})} (hP : P.IsConservativeFamilyOfPoints)
  [ObjectProperty.Small.{w} P] [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

attribute [local instance] Sheaf.monoidalCategory


open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {F G : Sheaf J (ModuleCat.{w} R)} (ev : F ⊗ G ⟶ 𝟙_ _)
  (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J G)
  (hfib : ∀ Φ : P.FullSubcategory, ∃ c, IsCanonical ev Φ.obj c ∧
    (∀ d, IsCanonical ev Φ.obj d → d = c) ∧
    ∀ f, ((moduleFiber R Φ.obj).map (contractionDual ev)).hom
      ((μ (moduleFiber R Φ.obj) F (G ⊗ F)).hom (f ⊗ₜ c)) = f)

include hP hG hfib in
/-- A canonical section of `G ⊗ F` exists over every object. -/
theorem exists_canonicalSection (U : C) :
    ∃ t : (G ⊗ F).obj.obj (op U), IsCanonicalSection P ev t := by
  have hu : ∀ (Φ : P.FullSubcategory) (d d'), IsCanonical ev Φ.obj d →
      IsCanonical ev Φ.obj d' → d = d' := fun Φ d d' hd hd' => by
    obtain ⟨c, -, hc, -⟩ := hfib Φ
    rw [hc d hd, hc d' hd']
  exact exists_isCanonicalSection hP ev hu
    (exists_isCanonicalSection_near ev hG fun Φ => (hfib Φ).imp fun _ h => h.1) U

/-- The canonical section of `G ⊗ F` over `U`. -/
def canonicalSection (U : C) : (G ⊗ F).obj.obj (op U) :=
  (exists_canonicalSection hP ev hG hfib U).choose

/-- The canonical section is canonical. -/
theorem isCanonicalSection_canonicalSection (U : C) :
    IsCanonicalSection P ev (canonicalSection hP ev hG hfib U) :=
  (exists_canonicalSection hP ev hG hfib U).choose_spec

/-- The restriction of the canonical section over `U` along `f : V ⟶ U` is the canonical
section over `V`. -/
theorem map_canonicalSection {U V : C} (f : V ⟶ U) :
    ((G ⊗ F).obj.map f.op).hom (canonicalSection hP ev hG hfib U) =
      canonicalSection hP ev hG hfib V := by
  refine IsCanonicalSection.eq hP ev (fun Φ d d' hd hd' => ?_)
    ((isCanonicalSection_canonicalSection hP ev hG hfib U).map ev f)
    (isCanonicalSection_canonicalSection hP ev hG hfib V)
  obtain ⟨c, -, hc, -⟩ := hfib Φ
  rw [hc d hd, hc d' hd']

/-- The canonical sections, as a morphism out of the constant presheaf on `R`. -/
def coevaluationPresheaf : 𝟙_ (Cᵒᵖ ⥤ ModuleCat.{w} R) ⟶ (G ⊗ F).obj where
  app U := ModuleCat.ofHom ((LinearMap.toSpanSingleton R _
    (canonicalSection hP ev hG hfib U.unop)) ∘ₗ ULift.moduleEquiv.toLinearMap)
  naturality U V f := by
    ext r
    change r.down • canonicalSection hP ev hG hfib V.unop =
      ((G ⊗ F).obj.map f).hom (r.down • canonicalSection hP ev hG hfib U.unop)
    rw [_root_.map_smul, ← map_canonicalSection hP ev hG hfib f.unop]
    rfl

/-- **The coevaluation** `𝟙 ⟶ G ⊗ F`, the global canonical section. -/
def coevaluation : 𝟙_ (Sheaf J (ModuleCat.{w} R)) ⟶ G ⊗ F :=
  ε (presheafToSheaf J (ModuleCat.{w} R)) ≫
    ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _).symm
      (coevaluationPresheaf hP ev hG hfib)

/-- The fibre of the coevaluation at a point, on the generator of the fibre of the unit, is the
germ of the canonical section. -/
theorem ε_comp_map_coevaluation (Φ : J.Point.{w}) {X : C} (x : Φ.fiber.obj X) :
    ε (moduleFiber R Φ) ≫ (moduleFiber R Φ).map (coevaluation hP ev hG hfib) =
      (coevaluationPresheaf hP ev hG hfib).app (op X) ≫ Φ.toPresheafFiber X x (G ⊗ F).obj := by
  let L := presheafToSheaf J (ModuleCat.{w} R)
  let e := Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{w} R)
  have hε : ε (moduleFiber R Φ) = ε (Φ.presheafFiber (A := ModuleCat.{w} R)) ≫
      e.inv.app _ ≫ (moduleFiber R Φ).map (η L) :=
    Localization.Monoidal.functorMonoidalOfComp_ε L J.W (moduleFiber R Φ) Φ.presheafFiber
  have hc : e.inv.app (G ⊗ F).obj ≫
      (moduleFiber R Φ).map ((sheafificationAdjunction J (ModuleCat.{w} R)).counit.app (G ⊗ F)) =
        𝟙 _ := by
    show Φ.presheafFiber.map (toSheafify J (G ⊗ F).obj) ≫
      Φ.presheafFiber.map ((sheafToPresheaf J _).map
        ((sheafificationAdjunction J (ModuleCat.{w} R)).counit.app (G ⊗ F))) = _
    rw [← Φ.presheafFiber.map_comp]
    have h3 := (sheafificationAdjunction J (ModuleCat.{w} R)).right_triangle_components (G ⊗ F)
    rw [sheafificationAdjunction_unit_app] at h3
    exact (congrArg Φ.presheafFiber.map h3).trans (Φ.presheafFiber.map_id _)
  have hnat : e.inv.app _ ≫ (moduleFiber R Φ).map (L.map (coevaluationPresheaf hP ev hG hfib)) =
      Φ.presheafFiber.map (coevaluationPresheaf hP ev hG hfib) ≫ e.inv.app _ :=
    (e.inv.naturality (coevaluationPresheaf hP ev hG hfib)).symm
  rw [hε, coevaluation, Adjunction.homEquiv_counit]
  simp only [Category.assoc, Functor.map_comp]
  rw [← (moduleFiber R Φ).map_comp_assoc, Monoidal.η_ε, CategoryTheory.Functor.map_id,
    Category.id_comp,
    reassoc_of% hnat, hc]
  refine Eq.trans ?_ (Φ.toPresheafFiber_naturality (coevaluationPresheaf hP ev hG hfib) X x)
  rw [← Φ.toPresheafFiber_ε X x]
  exact congrArg _ (Category.comp_id _)

/-- The fibre of the coevaluation is `R`-linear on the fibre of the unit: its value at the
image of `r` is `r` times its value at the image of `1`. -/
theorem map_coevaluation_ε_eq (Φ : J.Point.{w}) (r : R) :
    ((moduleFiber R Φ).map (coevaluation hP ev hG hfib)).hom
        ((ε (moduleFiber R Φ)).hom (ULift.up r)) =
      r • ((moduleFiber R Φ).map (coevaluation hP ev hG hfib)).hom
        ((ε (moduleFiber R Φ)).hom (ULift.up 1)) := by
  have : (ULift.up r : ULift.{w} R) = r • ULift.up 1 := by ext; simp
  rw [this, _root_.map_smul, _root_.map_smul]

/-- The fibre of the coevaluation at a point of the family sends the generator of the fibre of
the unit to a canonical element. -/
theorem isCanonical_map_coevaluation (Φ : P.FullSubcategory) :
    IsCanonical ev Φ.obj
      (((moduleFiber R Φ.obj).map (coevaluation hP ev hG hfib)).hom
        ((ε (moduleFiber R Φ.obj)).hom (ULift.up 1))) := by
  obtain ⟨⟨X, x⟩⟩ : Nonempty Φ.obj.fiber.Elements := IsCofiltered.nonempty
  have h := ConcreteCategory.congr_hom (ε_comp_map_coevaluation hP ev hG hfib Φ.obj x)
    (ULift.up 1)
  change ((moduleFiber R Φ.obj).map (coevaluation hP ev hG hfib)).hom
      ((ε (moduleFiber R Φ.obj)).hom (ULift.up 1)) =
    germ Φ.obj x (G ⊗ F) ((1 : R) • canonicalSection hP ev hG hfib X) at h
  rw [h, one_smul]
  exact isCanonicalSection_canonicalSection hP ev hG hfib X Φ x

variable [AB5OfSize.{w, w} (ModuleCat.{w} R)]

/-- The first zigzag identity, contracted: `(η ▷ G) ≫ contraction = λ`. -/
theorem coevaluation_whiskerRight_contraction :
    coevaluation hP ev hG hfib ▷ G ≫ contraction ev = (λ_ G).hom := by
  refine hom_ext_of_forall_fiber_tmul (hP.jointlyFaithful _) fun Φ u g => ?_
  rw [← ε_unitEquiv (moduleFiber R Φ.obj) u]
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [map_whiskerRight_μ, map_coevaluation_ε_eq, ← smul_tmul', _root_.map_smul, _root_.map_smul,
    isCanonical_map_coevaluation hP ev hG hfib Φ g, map_leftUnitor_μ_ε]

/-- The second zigzag identity, contracted: `(F ◁ η) ≫ contractionDual = ρ`. -/
theorem whiskerLeft_coevaluation_contractionDual :
    F ◁ coevaluation hP ev hG hfib ≫ contractionDual ev = (ρ_ F).hom := by
  refine hom_ext_of_forall_fiber_tmul (hP.jointlyFaithful _) fun Φ f u => ?_
  rw [← ε_unitEquiv (moduleFiber R Φ.obj) u]
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  obtain ⟨c, -, hc, hd⟩ := hfib Φ
  rw [map_whiskerLeft_μ, map_coevaluation_ε_eq, tmul_smul, _root_.map_smul, _root_.map_smul,
    hc _ (isCanonical_map_coevaluation hP ev hG hfib Φ), hd, map_rightUnitor_μ_ε]

/-- **A fibrewise perfect pairing is an exact pairing**: the coevaluation glued from canonical
sections and the given pairing `ev : F ⊗ G ⟶ 𝟙` satisfy the two zigzag identities. -/
@[instance_reducible]
def exactPairing : ExactPairing G F where
  coevaluation' := coevaluation hP ev hG hfib
  evaluation' := ev
  coevaluation_evaluation' := by
    rw [← cancel_mono (λ_ F).hom]
    simpa [contractionDual, Category.assoc] using
      whiskerLeft_coevaluation_contractionDual hP ev hG hfib
  evaluation_coevaluation' := by
    rw [← cancel_mono (ρ_ G).hom]
    simpa [contraction, Category.assoc] using
      coevaluation_whiskerRight_contraction hP ev hG hfib

/-- **A fibrewise perfect pairing with a locally constant sheaf of finite type with flat fibres
is an exact pairing**, over a noetherian ring: on a site with a conservative family of points,
if `G` is locally constant of finite type with flat fibres and `ev : F ⊗ G ⟶ 𝟙` induces a
perfect pairing on every fibre, then `ev` is the evaluation of an exact pairing between `G` and
`F`. -/
@[instance_reducible]
def exactPairingOfPerfect [IsNoetherianRing R]
    (hflat : ∀ Φ : P.FullSubcategory, Module.Flat R ((moduleFiber R Φ.obj).obj G))
    (hp : ∀ Φ : P.FullSubcategory, Function.Bijective (fiberPairing ev Φ.obj)) :
    ExactPairing G F :=
  exactPairing hP ev hG fun Φ => by
    have := finite_sheafFiber_of_isFiniteTypeLocallyConstant hG Φ.obj
    have := hflat Φ
    have := Module.finitePresentation_of_finite R ((moduleFiber R Φ.obj).obj G)
    have := Module.Flat.projective_of_finitePresentation (R := R) (M := (moduleFiber R Φ.obj).obj G)
    exact existsUnique_isCanonical ev Φ.obj (hp Φ)

/-- The evaluation of `exactPairingOfPerfect` is `ev`. -/
theorem exactPairingOfPerfect_evaluation [IsNoetherianRing R]
    (hflat : ∀ Φ : P.FullSubcategory, Module.Flat R ((moduleFiber R Φ.obj).obj G))
    (hp : ∀ Φ : P.FullSubcategory, Function.Bijective (fiberPairing ev Φ.obj)) :
    letI := exactPairingOfPerfect hP ev hG hflat hp
    ε_ G F = ev :=
  rfl

end Coevaluation

end Stacks.SheafDuality
