module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearSourceNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsLocalIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksCore.Tactic.StacksAttribute

/-! # Pullback of a tensor product of sheaves of modules along a morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. **Stacks 03EL** is the
canonical isomorphism

`f^*(F ⊗_{O_D} G) ≅ f^*F ⊗_{O_C} f^*G`,

natural in the two sheaves of `O_D`-modules `F` and `G`.

The proof is the chain of bijections recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTensor`. For a sheaf of
`O_C`-modules `N`:

1. `Hom_{O_C}(f^*(F ⊗ G), N) = Hom_{O_D}(F ⊗ G, f_*N)` — Stacks 03D7;
2. `Hom_{O_D}(F ⊗ G, f_*N) = Bilin_{O_D}(F × G, f_*N)` — the universal property of the tensor
   product sheaf;
3. `Bilin_{O_D}(F × G, f_*N) = Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, N|_{f⁻¹O_D})` — the step the source
   calls the interesting one, Stacks 03D3;
4. `Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, N|) = Hom_{f⁻¹O_D}(f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G, N|)` — the universal
   property again, over the inverse-image structure sheaf;
5. `Hom_{f⁻¹O_D}(f⁻¹F ⊗ f⁻¹G, N|) = Hom_{O_C}(O_C ⊗_{f⁻¹O_D} (f⁻¹F ⊗ f⁻¹G), N)` — Stacks 03CZ;
6. `Hom_{O_C}(O_C ⊗_{f⁻¹O_D} (f⁻¹F ⊗ f⁻¹G), N) = Hom_{O_C}(f^*F ⊗_{O_C} f^*G, N)` — base change
   of a tensor product, Stacks 03CU.

Each link is natural in `N` and in the pair `(F, G)`, so
`CategoryTheory.Functor.natIsoOfHomEquiv` turns the composite into an isomorphism of bifunctors.
Step 5 is where the pullback of Stacks 03D6 part (2) factors as the inverse image followed by
extension of scalars, and step 6 is where that extension of scalars is seen to be monoidal.

## Main definitions

* `Stacks.SheafOfModules.pullbackTensorHomEquiv`: the composite bijection, assembled from the six
  steps `pullbackTensorStep1` … `pullbackTensorStep6`.
* `Stacks.SheafOfModules.pullbackTensorIso`: **Tag 03EL**, the natural isomorphism of bifunctors.
* `Stacks.Sheaves.RingedToposModules.moduleSheafifyUnit`: the canonical map on local sections
  into a sheafification of presheaves of modules, at the spelling of the sheaf of rings this file
  works in.
* `Stacks.SheafOfModules.pullbackTensorTranspose`: the adjoint transpose over `f⁻¹O_D` of the
  comparison of Tag 03EL, i.e. the last two steps of the chain run backwards from the identity.

## Main results

* `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_naturality`: base change of a
  tensor product of sheaves of modules is natural in the two modules.
* `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_moduleSheafifyUnit_tmul_tmul`:
  **the section formula for step 6**, `a ⊗ₜ (x ⊗ₜ y) ↦ (a ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)` read through the
  canonical maps on local sections. Its two sheafification legs are computed separately by
  `Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso_hom_moduleSheafifyUnit_tmul` and
  `Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso_hom_moduleSheafifyUnit_tmul`,
  and its middle factor is the presheaf-level base change of Tag 03CU, which is objectwise
  `TensorProduct.AlgebraTensorModule.distribBaseChange`.
* `Stacks.SheafOfModules.pullbackTensorHomEquiv_naturality` and
  `Stacks.SheafOfModules.pullbackTensorHomEquiv_precomp`: the composite bijection is natural in
  the sheaf of values and in the two source modules.
* `Stacks.SheafOfModules.pullbackTensorTranspose_val_app_moduleSheafifyUnit_tmul`: **the
  pure-tensor formula for steps 5 and 6**, `η(a ⊗ₜ b) ↦ η(ν(a) ⊗ₜ ν(b))` for the unit `ν` of
  Tag 03CZ. This is the `unit(a) ⊗ₜ unit(b)` shape the pure-tensor formula for the comparison of
  Tag 03EL has to have, established over `f⁻¹O_D`.

## Implementation notes

The six steps are separate definitions, each with its type written out, rather than one long
`Equiv.trans`. The reason is not readability: the objects at the seams have two spellings each —
`(Stacks.SheafOfModules.Tensor.sheafTensor Y.J).obj (F, G)` against
`Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O.obj _ F G`,
`Stacks.SheafOfModules.Tensor.ringSheaf Y.O` against
`Stacks.Sheaves.RingedToposModules.commRingSheaf Y.J Y.O.obj _`,
`(pushforwardModules f).obj N` against `(directImageModules _ _).obj ((restrictScalars _).obj N)` —
and the two members of each pair are definitionally equal only at *default* transparency, because
`CategoryTheory.sheafCompose` and `Stacks.SheafOfModules.TensorSheafification.structureSheaf` are
plain definitions. Written as a single `Equiv.trans` the composite elaborates (elaboration checks
definitional equality at default transparency) but is then opaque to `rw` and to `simp`, which
unify at `reducible`: even
`Equiv.trans_apply` fails to fire on it, and Lean reports that the goal is not type-correct at the
`implicit` level. Declaring each step at one chosen spelling of its source and target, so that
consecutive steps agree *syntactically*, absorbs every one of those definitional equalities into
the declared types once and makes the naturality proofs ordinary rewrites. This is the
"make the two share one spelling by construction" move, applied to the seams of a composite rather
than to a single call site.

Likewise `Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso_hom_eq` and
`Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality` restate two facts of
Tag 05NA with the sheaf of rings spelled `Stacks.Sheaves.RingedToposModules.commRingSheaf J A h`
rather than `Stacks.SheafOfModules.TensorSheafification.structureSheaf A h`; both hold by
definition. The point is that `commRingSheaf` is an `abbrev`, so instance search can see through
`(commRingSheaf J A h).obj` to `A ⋙ forget₂ _ _` and find the monoidal structure on presheaves of
modules, whereas it cannot see through
`(Stacks.SheafOfModules.TensorSheafification.structureSheaf A h).obj`, and the monoidal product
`⊗ₘ` of Tag 05NA's own statements therefore fails to elaborate when it is reached from outside
that file.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
  Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

/-! ## Three pieces of category-theoretic bookkeeping -/

namespace Stacks.SheafOfModules

section Squares

universe v₁ u₁

variable {D : Type u₁} [Category.{v₁} D]

/-- Two commuting squares side by side commute. -/
lemma square_horiz_paste {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : D} {m : X₁ ⟶ X₂} {p : Y₁ ⟶ Y₂} {n : Z₁ ⟶ Z₂}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {g₁ : Y₁ ⟶ Z₁} {g₂ : Y₂ ⟶ Z₂}
    (h₁ : m ≫ f₂ = f₁ ≫ p) (h₂ : p ≫ g₂ = g₁ ≫ n) :
    m ≫ f₂ ≫ g₂ = (f₁ ≫ g₁) ≫ n := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- A square whose two horizontal edges are the inverse of an isomorphism followed by a morphism
commutes as soon as the square of the isomorphisms and the square of the morphisms do. -/
lemma square_of_inv_comp {X X' Y Y' Z Z' : D} (e : X ≅ Y) (e' : X' ≅ Y')
    (g : X ⟶ Z) (g' : X' ⟶ Z') {m : Y ⟶ Y'} {m' : X ⟶ X'} {n : Z ⟶ Z'}
    (h₁ : m' ≫ e'.hom = e.hom ≫ m) (h₂ : m' ≫ g' = g ≫ n) :
    m ≫ e'.inv ≫ g' = (e.inv ≫ g) ≫ n := by
  rw [← cancel_epi e.hom, ← Category.assoc, ← h₁, Category.assoc, Iso.hom_inv_id_assoc, h₂,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- A naturality square for the forward maps of two isomorphisms gives one for their inverses. -/
lemma inv_square_of_hom_square {X X' Y Y' : D} (e : X ≅ Y) (e' : X' ≅ Y')
    {m : X ⟶ X'} {n : Y ⟶ Y'} (h : m ≫ e'.hom = e.hom ≫ n) :
    e.inv ≫ m = n ≫ e'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A functor carries a commuting square to a commuting square. -/
private lemma map_comp_congr_comp {E : Type*} [Category E] (Φ : D ⥤ E) {X₁ X₂ Y₁ Y₂ : D}
    {a : X₁ ⟶ X₂} {b : X₂ ⟶ Y₂} {c : X₁ ⟶ Y₁} {d : Y₁ ⟶ Y₂} (h : a ≫ b = c ≫ d) :
    Φ.map a ≫ Φ.map b = Φ.map c ≫ Φ.map d := by
  rw [← Φ.map_comp, h, Φ.map_comp]

end Squares

end Stacks.SheafOfModules

/-! ## The sheafification unit of presheaves of modules, at the spelling of this file -/

namespace Stacks.Sheaves.RingedToposModules

universe w v u

section SheafifyUnit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A : Cᵒᵖ ⥤ CommRingCat.{w}} (h : Presheaf.IsSheaf J (ringPresheaf A))

/-- **The canonical map on local sections into a sheafification of presheaves of modules**,
`P(V) ⟶ P^#(V)`: the unit of the sheafification adjunction, with the sheaf of rings spelled
`Stacks.Sheaves.RingedToposModules.commRingSheaf J A h` rather than
`Stacks.SheafOfModules.TensorSheafification.structureSheaf A h`.

This is `PresheafOfModules.sheafifyUnit` at the comparison map `𝟙`, and it is the same morphism
as `Stacks.SheafOfModules.TensorSheafification.toSheafify A h P`; only the spelling of the index
differs. The spelling is load-bearing for every statement below in which the target of the unit
is a tensor factor: `commRingSheaf` is an `abbrev`, so instance search sees through
`(commRingSheaf J A h).obj` to `A ⋙ forget₂ _ _` and finds Mathlib's monoidal structure on
presheaves of modules, whereas it cannot see through the plain definition
`(Stacks.SheafOfModules.TensorSheafification.structureSheaf A h).obj` and `⊗` then fails to
elaborate. This is the difficulty recorded in the implementation notes above, met once here
rather than at each use. -/
abbrev moduleSheafifyUnit (P : PresheafOfModules.{w} (ringPresheaf A)) :
    P ⟶ (SheafOfModules.forget (commRingSheaf J A h) ⋙
        PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J A h).obj)).obj
      ((PresheafOfModules.sheafification (R := commRingSheaf J A h) (𝟙 _)).obj P) :=
  PresheafOfModules.sheafifyUnit (R := commRingSheaf J A h) (𝟙 _) P

/-- **The sheafification of a morphism of presheaves of modules, read on the image of a local
section under the sheafification unit.** This is naturality of that unit, and it is the one fact
every section formula below is assembled from: the image of a local section determines the
sheafified morphism on it. -/
lemma sheafification_map_moduleSheafifyUnit_app
    {P Q : PresheafOfModules.{w} (ringPresheaf A)} (m : P ⟶ Q) (V : Cᵒᵖ) (x : P.obj V) :
    ((PresheafOfModules.sheafification (R := commRingSheaf J A h) (𝟙 _)).map m).val.app V
        ((moduleSheafifyUnit h P).app V x) =
      (moduleSheafifyUnit h Q).app V (m.app V x) :=
  (congrArg (fun k ↦ k.app V x)
    ((PresheafOfModules.sheafificationAdjunction
      (R := commRingSheaf J A h) (𝟙 _)).unit.naturality m)).symm

end SheafifyUnit

end Stacks.Sheaves.RingedToposModules

/-! ## Tag 05NA at the spelling instance search can see through -/

namespace Stacks.SheafOfModules.TensorSheafification

universe w v u

section Spelling

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (h𝒪 : Presheaf.IsSheaf J (ringPresheaf 𝒪))

/-- The comparison isomorphism of Tag 05NA is the sheafification of the tensor of the two
sheafification units. This is `Stacks.SheafOfModules.TensorSheafification.tensorSheafifyComparison`
  with the sheaf of rings
spelled as the underlying sheaf of rings of a presheaf of commutative rings. -/
lemma tensorSheafifyIso_hom_eq (P Q : PresheafOfModules.{w} (ringPresheaf 𝒪)) :
    (tensorSheafifyIso 𝒪 h𝒪 P Q).hom =
      (PresheafOfModules.sheafification (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).map
        ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app P ⊗ₘ
          (PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app Q) := rfl

/-- The unit of the sheafification of presheaves of modules is natural. -/
lemma sheafificationUnit_naturality {P P' : PresheafOfModules.{w} (ringPresheaf 𝒪)} (a : P ⟶ P') :
    a ≫ (PresheafOfModules.sheafificationAdjunction
        (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app P' =
      (PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app P ≫
        ((PresheafOfModules.sheafification (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).map a).val :=
  (PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.naturality a

/-- **The comparison isomorphism of Tag 05NA is natural in both presheaves of modules.** -/
lemma tensorSheafifyIso_hom_naturality {P P' Q Q' : PresheafOfModules.{w} (ringPresheaf 𝒪)}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    (PresheafOfModules.sheafification (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).map (a ⊗ₘ b) ≫
        (tensorSheafifyIso 𝒪 h𝒪 P' Q').hom =
      (tensorSheafifyIso 𝒪 h𝒪 P Q).hom ≫
        (PresheafOfModules.sheafification (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).map
          (((PresheafOfModules.sheafification (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).map a).val ⊗ₘ
            ((PresheafOfModules.sheafification (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).map b).val) := by
  rw [tensorSheafifyIso_hom_eq, tensorSheafifyIso_hom_eq]
  refine Stacks.SheafOfModules.map_comp_congr_comp _ ?_
  rw [MonoidalCategory.tensorHom_comp_tensorHom, sheafificationUnit_naturality,
    sheafificationUnit_naturality]
  exact (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm

/-- **The comparison isomorphism of Tag 05NA on local sections**: it carries the image under the
sheafification unit of the pure tensor of two local sections to the pure tensor of their images
under the two sheafification units,

`η_{P ⊗ Q}(x ⊗ₜ y) ↦ η_{P^# ⊗ Q^#}(η_P(x) ⊗ₜ η_Q(y))`.

The comparison is the sheafification of `η_P ⊗ₘ η_Q` by
`Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso_hom_eq`, so this is naturality of
the sheafification unit followed by the objectwise formula for a tensor product of two morphisms
of modules, which is definitional. -/
lemma tensorSheafifyIso_hom_moduleSheafifyUnit_tmul
    (P Q : PresheafOfModules.{w} (ringPresheaf 𝒪)) (V : Cᵒᵖ) (x : P.obj V) (y : Q.obj V) :
    (tensorSheafifyIso 𝒪 h𝒪 P Q).hom.val.app V
        ((moduleSheafifyUnit h𝒪 (P ⊗ Q)).app V (x ⊗ₜ[(ringPresheaf 𝒪).obj V] y)) =
      (moduleSheafifyUnit h𝒪
          ((SheafOfModules.forget (commRingSheaf J 𝒪 h𝒪) ⋙
              PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J 𝒪 h𝒪).obj)).obj
            ((PresheafOfModules.sheafification (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).obj P) ⊗
            (SheafOfModules.forget (commRingSheaf J 𝒪 h𝒪) ⋙
              PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J 𝒪 h𝒪).obj)).obj
            ((PresheafOfModules.sheafification (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).obj Q))).app V
        ((moduleSheafifyUnit h𝒪 P).app V x ⊗ₜ[(ringPresheaf 𝒪).obj V]
          (moduleSheafifyUnit h𝒪 Q).app V y) := by
  rw [tensorSheafifyIso_hom_eq]
  exact Stacks.Sheaves.RingedToposModules.sheafification_map_moduleSheafifyUnit_app h𝒪
    (moduleSheafifyUnit h𝒪 P ⊗ₘ moduleSheafifyUnit h𝒪 Q) V _

end Spelling

end Stacks.SheafOfModules.TensorSheafification

/-! ## Base change of a tensor product is natural -/

namespace Stacks.Sheaves.RingedToposModules

universe w v u

section ExtendScalarsNat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))

/-- **Extension of scalars commutes with sheafification, naturally.** The comparison
`(A₂ ⊗_{p,A₁} P)^# ≅ A₂ ⊗_{A₁} P^#` of
`Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso` is natural in `P`, because it is the
sheafification of the change-of-rings image of a sheafification unit. -/
lemma extendScalarsSheafifyIso_hom_naturality
    {P Q : PresheafOfModules.{w} (ringPresheaf A₁)} (m : P ⟶ Q) :
    (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
          ((changeOfRings θ).map m) ≫ (extendScalarsSheafifyIso θ h₁ h₂ Q).hom =
      (extendScalarsSheafifyIso θ h₁ h₂ P).hom ≫
        (extendScalars J θ h₁ h₂).map
          ((PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).map m) := by
  exact Stacks.SheafOfModules.map_comp_congr_comp _ (Stacks.SheafOfModules.map_comp_congr_comp _
    ((PresheafOfModules.sheafificationAdjunction
      (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.naturality m))

/-- **The unit of the adjunction of Tag 03CZ on local sections**: a local section `x` of `L`
goes to the image of `1 ⊗ₜ x` under the canonical map into the sheafification.

This is `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`
with the sheafification unit spelled `Stacks.Sheaves.RingedToposModules.moduleSheafifyUnit`
rather than `CategoryTheory.toSheafify`, which is the form the section formulas of this file
compose with. -/
lemma extendRestrictScalarsAdjunction_unit_app_val_app_moduleSheafifyUnit
    (L : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : Cᵒᵖ) (x : L.val.obj V) :
    letI := (θ.app V).hom.toAlgebra
    ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L).val.app V x =
      (moduleSheafifyUnit h₂ ((changeOfRings θ).obj L.val)).app V
        ((1 : A₂.obj V) ⊗ₜ[A₁.obj V] x) := by
  let := (θ.app V).hom.toAlgebra
  refine Eq.trans (congrArg (fun m ↦ (PresheafOfModules.Hom.app m V) x)
    (forget_map_extendRestrictScalarsAdjunction_unit_app J θ h₁ h₂ L)) ?_
  exact congrArg ((moduleSheafifyUnit h₂ ((changeOfRings θ).obj L.val)).app V)
    (changeOfRingsAdjunction_unit_app_apply θ L.val V x)

/-- **The sheafification comparison for extension of scalars, on local sections.** The
comparison `(A₂ ⊗_{p,A₁} P)^# ≅ A₂ ⊗_{A₁} P^#` of
`Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso` carries the image under the
sheafification unit of a pure tensor `a ⊗ₜ t` to the image under the sheafification unit of
`a ⊗ₜ η_P(t)`:

`η_{A₂ ⊗ P}(a ⊗ₜ t) ↦ η_{A₂ ⊗ P^#}(a ⊗ₜ η_P(t))`.

The comparison is by construction the sheafification of the change-of-rings image of the
sheafification unit of `P`, so this is naturality of the sheafification unit followed by the
formula `a ⊗ₜ t ↦ a ⊗ₜ m(t)` for the change-of-rings image of a morphism,
`Stacks.PresheafOfModules.ChangeOfRings.cofHom_app_tmul`. -/
lemma extendScalarsSheafifyIso_hom_moduleSheafifyUnit_tmul
    (P : PresheafOfModules.{w} (ringPresheaf A₁)) (V : Cᵒᵖ) (a : A₂.obj V) (t : P.obj V) :
    letI := (θ.app V).hom.toAlgebra
    (extendScalarsSheafifyIso θ h₁ h₂ P).hom.val.app V
        ((moduleSheafifyUnit h₂ ((changeOfRings θ).obj P)).app V (a ⊗ₜ[A₁.obj V] t)) =
      (moduleSheafifyUnit h₂ ((changeOfRings θ).obj
          ((PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj P).val)).app V
        (a ⊗ₜ[A₁.obj V] ((moduleSheafifyUnit h₁ P).app V t)) := by
  let := (θ.app V).hom.toAlgebra
  refine Eq.trans
    (sheafification_map_moduleSheafifyUnit_app h₂ (changeOfRingsUnit θ h₁ P) V _) ?_
  exact congrArg ((moduleSheafifyUnit h₂ _).app V)
    (cofHom_app_tmul θ (moduleSheafifyUnit h₁ P) V a t)

/-- **The two sheafification legs of base change of a tensor product cancel.** Base change of a
tensor product is by construction the sheafification comparison for extension of scalars read
backwards, then the presheaf-level base change of Tag 03CU, then the comparison of Tag 05NA; so
precomposing it with the sheafification comparison leaves the last two factors, both of which
have a formula on local sections.

This is the form in which the section formula below uses the definition: it is the only place
the inverse of the first leg occurs, and here it is cancelled rather than computed.

The `_cancelInv` suffix distinguishes this from
`Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso_hom_comp_extendScalarsTensorIso_hom`
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExtendScalarsTensorValue.lean`, which states the
same equality and was proved independently downstream. The duplicate is deliberate and not a
shadow: that module imports this one, so the two cannot be merged by an import, and whichever is
retired should be the downstream copy. -/
lemma extendScalarsSheafifyIso_hom_comp_extendScalarsTensorIso_hom_cancelInv
    (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (extendScalarsSheafifyIso θ h₁ h₂ (F.val ⊗ G.val)).hom ≫
        (extendScalarsTensorIso θ h₁ h₂ F G).hom =
      (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
          (changeOfRingsTensorObjIso θ F.val G.val).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso A₂ h₂
          ((changeOfRings θ).obj F.val) ((changeOfRings θ).obj G.val)).hom :=
  Iso.hom_inv_id_assoc (extendScalarsSheafifyIso θ h₁ h₂ (F.val ⊗ G.val))
    ((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
        (changeOfRingsTensorObjIso θ F.val G.val).hom ≫
      (Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso A₂ h₂
        ((changeOfRings θ).obj F.val) ((changeOfRings θ).obj G.val)).hom)

/-- **Base change of a tensor product of sheaves of modules, on local sections.** This is the
section formula for step 6 of the chain of Tag 03EL, and it is the pure-tensor formula

`a ⊗ₜ (x ⊗ₜ y) ↦ (a ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)`,

read through the canonical maps on sections. Precisely: the comparison
`A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)` of
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` carries the image of
`a ⊗ₜ η_{F ⊗ G}(x ⊗ₜ y)` under the canonical map
`A₂(V) ⊗_{A₁(V)} (F ⊗_{A₁} G)(V) ⟶ (A₂ ⊗_{A₁} (F ⊗_{A₁} G))(V)` to the image of
`η_{A₂ ⊗ F}(a ⊗ₜ x) ⊗ₜ η_{A₂ ⊗ G}(1 ⊗ₜ y)` under the canonical map
`(A₂ ⊗_{A₁} F)(V) ⊗_{A₂(V)} (A₂ ⊗_{A₁} G)(V) ⟶ ((A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G))(V)`.

The three factors of the comparison contribute one step each: the first is cancelled by
`extendScalarsSheafifyIso_hom_comp_extendScalarsTensorIso_hom_cancelInv` against
`extendScalarsSheafifyIso_hom_moduleSheafifyUnit_tmul`; the middle one is the presheaf-level
base change of Tag 03CU, which is objectwise
`TensorProduct.AlgebraTensorModule.distribBaseChange` and hence carries `a ⊗ₜ (x ⊗ₜ y)` to
`(a ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)` definitionally; and the last is
`Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso_hom_moduleSheafifyUnit_tmul`.

The asymmetry — the scalar `a` goes into the left factor and a `1` is produced on the right — is
the asymmetry of `distribBaseChange` and not an artefact: the two sides of the comparison are
tensor products over different rings, and the scalar has to be spent on one factor. -/
lemma extendScalarsTensorIso_hom_moduleSheafifyUnit_tmul_tmul
    (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : Cᵒᵖ) (a : A₂.obj V)
    (x : F.val.obj V) (y : G.val.obj V) :
    letI := (θ.app V).hom.toAlgebra
    (extendScalarsTensorIso θ h₁ h₂ F G).hom.val.app V
        ((moduleSheafifyUnit h₂ ((changeOfRings θ).obj
            ((PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj
              (F.val ⊗ G.val)).val)).app V
          (a ⊗ₜ[A₁.obj V]
            ((moduleSheafifyUnit h₁ (F.val ⊗ G.val)).app V
              (x ⊗ₜ[(ringPresheaf A₁).obj V] y)))) =
      (moduleSheafifyUnit h₂
          ((SheafOfModules.forget (commRingSheaf J A₂ h₂) ⋙
              PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J A₂ h₂).obj)).obj
            ((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
              ((changeOfRings θ).obj F.val)) ⊗
            (SheafOfModules.forget (commRingSheaf J A₂ h₂) ⋙
              PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J A₂ h₂).obj)).obj
            ((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
              ((changeOfRings θ).obj G.val)))).app V
        ((moduleSheafifyUnit h₂ ((changeOfRings θ).obj F.val)).app V (a ⊗ₜ[A₁.obj V] x)
          ⊗ₜ[(ringPresheaf A₂).obj V]
          (moduleSheafifyUnit h₂ ((changeOfRings θ).obj G.val)).app V
            ((1 : A₂.obj V) ⊗ₜ[A₁.obj V] y)) := by
  let := (θ.app V).hom.toAlgebra
  refine Eq.trans (congrArg ((extendScalarsTensorIso θ h₁ h₂ F G).hom.val.app V)
    (extendScalarsSheafifyIso_hom_moduleSheafifyUnit_tmul θ h₁ h₂ (F.val ⊗ G.val) V a
      (x ⊗ₜ[(ringPresheaf A₁).obj V] y)).symm) ?_
  refine Eq.trans (congrArg (fun k ↦ (SheafOfModules.Hom.val k).app V
      ((moduleSheafifyUnit h₂ ((changeOfRings θ).obj (F.val ⊗ G.val))).app V
        (a ⊗ₜ[A₁.obj V] (x ⊗ₜ[(ringPresheaf A₁).obj V] y))))
    (extendScalarsSheafifyIso_hom_comp_extendScalarsTensorIso_hom_cancelInv θ h₁ h₂ F G)) ?_
  refine Eq.trans (congrArg
    ((Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso A₂ h₂
      ((changeOfRings θ).obj F.val) ((changeOfRings θ).obj G.val)).hom.val.app V)
    (sheafification_map_moduleSheafifyUnit_app h₂
      (changeOfRingsTensorObjIso θ F.val G.val).hom V
      (a ⊗ₜ[A₁.obj V] (x ⊗ₜ[(ringPresheaf A₁).obj V] y)))) ?_
  exact Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso_hom_moduleSheafifyUnit_tmul
    A₂ h₂ ((changeOfRings θ).obj F.val) ((changeOfRings θ).obj G.val) V
    (a ⊗ₜ[A₁.obj V] x) ((1 : A₂.obj V) ⊗ₜ[A₁.obj V] y)

variable {F F' G G' : SheafOfModules.{w} (commRingSheaf J A₁ h₁)}

/-- **Base change of a tensor product of sheaves of modules is natural in both modules.** This
is the naturality that `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` is missing, and
it is step 6 of the chain of Tag 03EL. The three links are the naturality of the sheafification
comparison for extension of scalars, the naturality of the presheaf-level base-change comparison
of Tag 03CU, and the naturality of the comparison of Tag 05NA. -/
lemma extendScalarsTensorIso_hom_naturality (u : F ⟶ F') (v : G ⟶ G') :
    (extendScalars J θ h₁ h₂).map
          ((PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).map
            (u.val ⊗ₘ v.val)) ≫ (extendScalarsTensorIso θ h₁ h₂ F' G').hom =
      (extendScalarsTensorIso θ h₁ h₂ F G).hom ≫
        (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
          (((extendScalars J θ h₁ h₂).map u).val ⊗ₘ
            ((extendScalars J θ h₁ h₂).map v).val) := by
  have hi := Stacks.SheafOfModules.map_comp_congr_comp
    (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _))
    (changeOfRingsTensorObjIso_naturality θ u.val v.val)
  have hii := Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso_hom_naturality A₂ h₂
    ((changeOfRings θ).map u.val) ((changeOfRings θ).map v.val)
  exact Stacks.SheafOfModules.square_of_inv_comp
    (extendScalarsSheafifyIso θ h₁ h₂ (F.val ⊗ G.val))
    (extendScalarsSheafifyIso θ h₁ h₂ (F'.val ⊗ G'.val)) _ _
    (extendScalarsSheafifyIso_hom_naturality θ h₁ h₂ (u.val ⊗ₘ v.val))
    (Stacks.SheafOfModules.square_horiz_paste hi hii)

end ExtendScalarsNat

end Stacks.Sheaves.RingedToposModules

/-! ## The chain of bijections of Tag 03EL -/

namespace Stacks.SheafOfModules

universe w w' v u v' u'

section Chain

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The inverse image of the structure sheaf of the target of a morphism of ringed topoi is a
sheaf, read as the sheaf condition on the underlying presheaf of rings of a presheaf of
commutative rings. -/
lemma isSheaf_inverseImageStructureCommRing :
    Presheaf.IsSheaf X.J (ringPresheaf (inverseImageStructureCommRing f)) :=
  (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property

/-- The tensor product of two sheaves of modules over the inverse image `f⁻¹O_D` of the structure
sheaf of the target. The source ring here is a presheaf of commutative rings with a sheaf
condition on its underlying presheaf of rings, which is the only form in which `f⁻¹O_D` is
available. -/
abbrev inverseImageTensorSheaf
    (F G : SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(inverseImageStructureCommRing f),
      Presheaf.isSheaf_of_isSheaf_comp _ (inverseImageStructureCommRing f)
        (forget₂ CommRingCat RingCat) (isSheaf_inverseImageStructureCommRing f)⟩).obj F).obj G)

/-- The functorial action of the tensor product over the inverse image `f⁻¹O_D` of the structure
sheaf of the target, in the spelling the chain of Tag 03EL uses. -/
abbrev inverseImageTensorSheafMap
    {A A' B B' : SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (a : A ⟶ A') (b : B ⟶ B') :
    inverseImageTensorSheaf f A B ⟶ inverseImageTensorSheaf f A' B' :=
  (PresheafOfModules.sheafification
    (R := commRingSheaf X.J (inverseImageStructureCommRing f)
      (isSheaf_inverseImageStructureCommRing f)) (𝟙 _)).map (a.val ⊗ₘ b.val)

variable (F F' G G' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (N N' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **Step 1 of the chain of Tag 03EL**: `Hom_{O_C}(f^*(F ⊗ G), N) = Hom_{O_D}(F ⊗ G, f_*N)`,
the adjunction of Stacks 03D7. -/
def pullbackTensorStep1 :
    ((f.pullbackModules).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
        Y.O).obj F).obj G) ⟶ N) ≃
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj F).obj G ⟶
        (pushforwardModules f).obj N) :=
  (pullbackAdjPushforwardModules f).homEquiv _ N

/-- **Step 2 of the chain of Tag 03EL**: `Hom_{O_D}(F ⊗ G, f_*N) = Bilin_{O_D}(F × G, f_*N)`,
the universal property of the tensor product sheaf over `O_D`. -/
def pullbackTensorStep2 :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj F).obj G ⟶
        (pushforwardModules f).obj N) ≃
      { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N) //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q } :=
  (bilinearEquivTensorSheafHom (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
    (F := F) (G := G) (N := (pushforwardModules f).obj N)).symm

/-- **Step 3 of the chain of Tag 03EL**:
`Bilin_{O_D}(F × G, f_*N) = Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, N|_{f⁻¹O_D})`, the step the source calls
the interesting one. -/
def pullbackTensorStep3 :
    { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
      moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N) //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q } ≃
      { q : moduleSheaf
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) ⨯
          moduleSheaf
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
          moduleSheaf
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) //
        IsBilinearPairing
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q } :=
  (inverseImageBilinearEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F G
    ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)).symm

/-- **Step 4 of the chain of Tag 03EL**:
`Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, N|) = Hom_{f⁻¹O_D}(f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G, N|)`, the universal
property of the tensor product sheaf over `f⁻¹O_D`. -/
def pullbackTensorStep4 :
    { q : moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) ⨯
        moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
        moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) //
      IsBilinearPairing
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q } ≃
      (inverseImageTensorSheaf f
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
        (SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) :=
  bilinearEquivTensorSheafHom (hA := isSheaf_inverseImageStructureCommRing f)
    (F := (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
    (G := (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)
    (N := (SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)

/-- **Step 5 of the chain of Tag 03EL**:
`Hom_{f⁻¹O_D}(f⁻¹F ⊗ f⁻¹G, N|) = Hom_{O_C}(O_C ⊗_{f⁻¹O_D} (f⁻¹F ⊗ f⁻¹G), N)`, the
extension-restriction adjunction of Stacks 03CZ. -/
def pullbackTensorStep5 :
    (inverseImageTensorSheaf f
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
        (SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) ≃
      ((extendScalarsFSharp f).obj (inverseImageTensorSheaf f
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)) ⟶ N) :=
  ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).homEquiv _ N).symm

/-- **Step 6 of the chain of Tag 03EL**:
`Hom_{O_C}(O_C ⊗_{f⁻¹O_D} (f⁻¹F ⊗ f⁻¹G), N) = Hom_{O_C}(f^*F ⊗_{O_C} f^*G, N)`, base change of a
tensor product. -/
def pullbackTensorStep6 :
    ((extendScalarsFSharp f).obj (inverseImageTensorSheaf f
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)) ⟶ N) ≃
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj ((f.pullbackModules).obj
          F)).obj
          ((f.pullbackModules).obj G) ⟶ N) :=
  Iso.homFromEquiv (extendScalarsTensorIso (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))

/-- **The chain of bijections of Tag 03EL.** Morphisms out of the pullback of a tensor product
are morphisms out of the tensor product of the pullbacks, in six steps. -/
def pullbackTensorHomEquiv :
    ((f.pullbackModules).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj F).obj G) ⟶ N) ≃
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
        ((f.pullbackModules).obj F)).obj ((f.pullbackModules).obj G) ⟶ N) :=
  (pullbackTensorStep1 f F G N).trans ((pullbackTensorStep2 f F G N).trans
    ((pullbackTensorStep3 f F G N).trans ((pullbackTensorStep4 f F G N).trans
      ((pullbackTensorStep5 f F G N).trans (pullbackTensorStep6 f F G N)))))

/-! ### Naturality of the six steps in the sheaf of values -/

variable {N N'}

/-- Step 1 is natural in the sheaf of values. -/
lemma pullbackTensorStep1_naturality
    (g : (f.pullbackModules).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
        Y.O).obj F).obj G) ⟶ N)
    (k : N ⟶ N') :
    pullbackTensorStep1 f F G N' (g ≫ k) =
      pullbackTensorStep1 f F G N g ≫ (pushforwardModules f).map k :=
  (pullbackAdjPushforwardModules f).homEquiv_naturality_right g k

omit [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Step 2 is natural in the sheaf of values. -/
lemma pullbackTensorStep2_naturality
    (t : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj F).obj G ⟶
        (pushforwardModules f).obj
        N)
    (k : N ⟶ N') :
    pullbackTensorStep2 f F G N' (t ≫ (pushforwardModules f).map k) =
      ⟨(pullbackTensorStep2 f F G N t).1 ≫
          (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
            ((pushforwardModules f).map k),
        (pullbackTensorStep2 f F G N t).2.comp ((pushforwardModules f).map k)⟩ :=
  bilinearEquivTensorSheafHom_symm_naturality (hA :=
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) t
    ((pushforwardModules f).map k)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 3 is natural in the sheaf of values. -/
lemma pullbackTensorStep3_naturality
    (p : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
      moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N) //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q }) (k : N ⟶ N') :
    pullbackTensorStep3 f F G N'
        ⟨p.1 ≫
          (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((pushforwardModules f).map k),
          p.2.comp ((pushforwardModules f).map k)⟩ =
      ⟨(pullbackTensorStep3 f F G N p).1 ≫
          (moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            ((SheafOfModules.restrictScalars f.fSharpInverseImage).map k),
        (pullbackTensorStep3 f F G N p).2.comp
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).map k)⟩ :=
  inverseImageBilinearEquiv_symm_naturality f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) p
    ((SheafOfModules.restrictScalars f.fSharpInverseImage).map k)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 4 is natural in the sheaf of values. -/
lemma pullbackTensorStep4_naturality
    (q :
      { q : moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) ⨯
        moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
        moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) //
      IsBilinearPairing
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q })
    (k : N ⟶ N') :
    pullbackTensorStep4 f F G N'
        ⟨q.1 ≫ (moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
              ((SheafOfModules.restrictScalars f.fSharpInverseImage).map k),
          q.2.comp ((SheafOfModules.restrictScalars f.fSharpInverseImage).map k)⟩ =
      pullbackTensorStep4 f F G N q ≫
        (SheafOfModules.restrictScalars f.fSharpInverseImage).map k :=
  bilinearEquivTensorSheafHom_naturality (hA := isSheaf_inverseImageStructureCommRing f) q
    ((SheafOfModules.restrictScalars f.fSharpInverseImage).map k)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 5 is natural in the sheaf of values. -/
lemma pullbackTensorStep5_naturality
    (y : inverseImageTensorSheaf f
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
      (SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) (k : N ⟶ N') :
    pullbackTensorStep5 f F G N'
        (y ≫ (SheafOfModules.restrictScalars f.fSharpInverseImage).map k) =
      pullbackTensorStep5 f F G N y ≫ k :=
  (extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).homEquiv_naturality_right_symm y k

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 6 is natural in the sheaf of values. -/
lemma pullbackTensorStep6_naturality
    (z : (extendScalarsFSharp f).obj (inverseImageTensorSheaf f
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)) ⟶
          N) (k : N ⟶ N') :
    pullbackTensorStep6 f F G N' (z ≫ k) = pullbackTensorStep6 f F G N z ≫ k :=
  (Category.assoc (extendScalarsTensorIso (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
    ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).inv z k).symm

/-- **The chain of bijections of Tag 03EL is natural in the sheaf of values.** -/
lemma pullbackTensorHomEquiv_naturality
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O))
        ⋙ f.pullbackModules).obj (F, G) ⟶ N)
    (k : N ⟶ N') :
    pullbackTensorHomEquiv f F G N' (g ≫ k) = pullbackTensorHomEquiv f F G N g ≫ k := by
  simp only [pullbackTensorHomEquiv, Equiv.trans_apply]
  rw [pullbackTensorStep1_naturality, pullbackTensorStep2_naturality,
    pullbackTensorStep3_naturality, pullbackTensorStep4_naturality,
    pullbackTensorStep5_naturality, pullbackTensorStep6_naturality]

/-! ### Naturality of the six steps in the two source modules -/

variable {F F' G G'}

/-- Step 1 is natural in the two source modules. -/
lemma pullbackTensorStep1_precomp (u : F ⟶ F') (v : G ⟶ G')
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (g : (f.pullbackModules).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
        Y.O).obj F').obj G') ⟶
        N) :
    pullbackTensorStep1 f F G N
        ((f.pullbackModules).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).map u).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj _).map v)) ≫ g) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).map u).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj _).map v) ≫
        pullbackTensorStep1 f F' G' N g :=
  (pullbackAdjPushforwardModules f).homEquiv_naturality_left _ g

omit [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Step 2 is natural in the two source modules. -/
lemma pullbackTensorStep2_precomp (u : F ⟶ F') (v : G ⟶ G')
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (t : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj F').obj G' ⟶
      (pushforwardModules f).obj N) :
    pullbackTensorStep2 f F G N
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).map u).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj _).map v) ≫ t) =
      ⟨prod.map ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
            ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v) ≫
          (pullbackTensorStep2 f F' G' N t).1,
        (pullbackTensorStep2 f F' G' N t).2.precomp u v⟩ :=
  (congrArg (fun morphism ↦ pullbackTensorStep2 f F G N (morphism ≫ t))
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Y.O u v)).trans
      (bilinearEquivTensorSheafHom_symm_precomp (hA :=
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) t u v)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 3 is natural in the two source modules. -/
lemma pullbackTensorStep3_precomp (u : F ⟶ F') (v : G ⟶ G')
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (p : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F' ⨯
      moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G' ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N) //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q }) :
    pullbackTensorStep3 f F G N
        ⟨prod.map ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
            ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v) ≫
              p.1, p.2.precomp u v⟩ =
      ⟨prod.map ((moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u))
            ((moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v)) ≫
          (pullbackTensorStep3 f F' G' N p).1,
        (pullbackTensorStep3 f F' G' N p).2.precomp _ _⟩ :=
  inverseImageBilinearEquiv_symm_precomp f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) u v p

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 4 is natural in the two source modules. -/
lemma pullbackTensorStep4_precomp (u : F ⟶ F') (v : G ⟶ G')
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (q :
      { q : moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F') ⨯
        moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G') ⟶
        moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) //
      IsBilinearPairing
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q }) :
    pullbackTensorStep4 f F G N
        ⟨prod.map ((moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u))
            ((moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v)) ≫ q.1,
          q.2.precomp _ _⟩ =
      inverseImageTensorSheafMap f
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v) ≫
        pullbackTensorStep4 f F' G' N q :=
  bilinearEquivTensorSheafHom_precomp (hA := isSheaf_inverseImageStructureCommRing f) q
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 5 is natural in the two source modules. -/
lemma pullbackTensorStep5_precomp (u : F ⟶ F') (v : G ⟶ G')
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (y : inverseImageTensorSheaf f
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F')
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G') ⟶
      (SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) :
    pullbackTensorStep5 f F G N
        (inverseImageTensorSheafMap f
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v) ≫ y) =
      (extendScalarsFSharp f).map (inverseImageTensorSheafMap f
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v)) ≫
        pullbackTensorStep5 f F' G' N y :=
  (extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).homEquiv_naturality_left_symm _ y

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 6 is natural in the two source modules: this is the naturality of base change of a
tensor product, read for the inverses of the comparison isomorphisms. -/
lemma pullbackTensorStep6_precomp (u : F ⟶ F') (v : G ⟶ G')
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (z : (extendScalarsFSharp f).obj (inverseImageTensorSheaf f
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F')
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G')) ⟶ N) :
    pullbackTensorStep6 f F G N
        ((extendScalarsFSharp f).map (inverseImageTensorSheafMap f
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v)) ≫ z) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map ((f.pullbackModules).map
          u)).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj _).map
        ((f.pullbackModules).map v)) ≫
        pullbackTensorStep6 f F' G' N z := by
  refine Eq.trans ?_ (congrArg (fun morphism ↦
    morphism ≫ pullbackTensorStep6 f F' G' N z)
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.O
        ((f.pullbackModules).map u) ((f.pullbackModules).map v)).symm)
  exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun m ↦ m ≫ z) (inv_square_of_hom_square _ _
        (extendScalarsTensorIso_hom_naturality (fSharpCommRing f)
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v))))).trans
    (Category.assoc _ _ _)

/-- **The chain of bijections of Tag 03EL is natural in the two source modules.** -/
lemma pullbackTensorHomEquiv_precomp (u : F ⟶ F') (v : G ⟶ G')
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O))
        ⋙ f.pullbackModules).obj (F', G') ⟶ N) :
    pullbackTensorHomEquiv f F G N
        ((f.pullbackModules).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).map u).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj _).map v)) ≫ g) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map ((f.pullbackModules).map
          u)).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj _).map
        ((f.pullbackModules).map v)) ≫
        pullbackTensorHomEquiv f F' G' N g := by
  simp only [pullbackTensorHomEquiv, Equiv.trans_apply]
  rw [pullbackTensorStep1_precomp, pullbackTensorStep2_precomp, pullbackTensorStep3_precomp,
    pullbackTensorStep4_precomp, pullbackTensorStep5_precomp, pullbackTensorStep6_precomp]

/-! ### Tag 03EL -/

/-- The inverse of the chain of bijections of Tag 03EL is natural in the sheaf of values. -/
lemma pullbackTensorHomEquiv_symm_naturality
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (g : (Functor.prod (f.pullbackModules) (f.pullbackModules) ⋙
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O))).obj (F,
          G) ⟶ N) (k : N ⟶
          N') :
    (pullbackTensorHomEquiv f F G N').symm (g ≫ k) =
      (pullbackTensorHomEquiv f F G N).symm g ≫ k :=
  (pullbackTensorHomEquiv f F G N').injective (by
    rw [Equiv.apply_symm_apply, pullbackTensorHomEquiv_naturality, Equiv.apply_symm_apply])

/-- The inverse of the chain of bijections of Tag 03EL is natural in the two source modules. -/
lemma pullbackTensorHomEquiv_symm_precomp
    {F F' G G' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (u : F ⟶ F') (v : G ⟶ G') (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (g : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
      ((f.pullbackModules).obj F')).obj ((f.pullbackModules).obj G') ⟶ N) :
    (pullbackTensorHomEquiv f F G N).symm
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map
          ((f.pullbackModules).map u)).app ((f.pullbackModules).obj G) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
              ((f.pullbackModules).obj F')).map ((f.pullbackModules).map v)) ≫ g) =
      (f.pullbackModules).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).map u).app G ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj F').map v) ≫
        (pullbackTensorHomEquiv f F' G' N).symm g :=
  (Equiv.symm_apply_eq (pullbackTensorHomEquiv f F G N)).2
    ((congrArg (fun morphism ↦
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map
        ((f.pullbackModules).map u)).app ((f.pullbackModules).obj G) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
            ((f.pullbackModules).obj F')).map ((f.pullbackModules).map v)) ≫ morphism)
      (Equiv.apply_symm_apply (pullbackTensorHomEquiv f F' G' N) g).symm).trans
        (pullbackTensorHomEquiv_precomp f u v N
          ((pullbackTensorHomEquiv f F' G' N).symm g)).symm)

/-- **Stacks 03EL.** For a morphism of ringed topoi
`(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, the pullback of a tensor product of sheaves of
`O_D`-modules is the tensor product of their pullbacks,

`f^*(F ⊗_{O_D} G) ≅ f^*F ⊗_{O_C} f^*G`,

naturally in `F` and in `G`. The comparison is the one determined by the chain of bijections
`Stacks.SheafOfModules.pullbackTensorHomEquiv`, whose naturality in the sheaf of values turns it
into a morphism of sheaves of modules and whose naturality in `F` and `G` makes that morphism a
natural transformation. -/
@[stacks 03EL, sga "4 IV 13.4" "special case"]
def pullbackTensorIso :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O)) ⋙
        f.pullbackModules ≅
      Functor.prod (f.pullbackModules) (f.pullbackModules) ⋙
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O)) :=
  Functor.natIsoOfHomEquiv (fun FG N ↦ (pullbackTensorHomEquiv f FG.1 FG.2 N).symm)
    (fun FG _ _ k g ↦ pullbackTensorHomEquiv_symm_naturality f FG.1 FG.2 g k)
    (fun uv N g ↦ by
      obtain ⟨u, v⟩ := uv
      exact pullbackTensorHomEquiv_symm_precomp f u v N g)

/-! ### Steps 5 and 6 of the chain, evaluated on a pure tensor -/

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [HasWeakSheafify Y.J AddCommGrpCat]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Step 6 read backwards at the identity is the comparison of base change of a tensor
product**, `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`. Step 6 is precomposition
with the inverse of that isomorphism, so this is `Iso.inv_hom_id`. -/
lemma pullbackTensorStep6_symm_id
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (pullbackTensorStep6 f F G
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
            ((f.pullbackModules).obj F)).obj ((f.pullbackModules).obj G))).symm (𝟙 _) =
      (extendScalarsTensorIso (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).hom :=
  (Equiv.symm_apply_eq (pullbackTensorStep6 f F G
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
        ((f.pullbackModules).obj F)).obj ((f.pullbackModules).obj G)))).2
    (Iso.inv_hom_id (extendScalarsTensorIso (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))).symm

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [HasWeakSheafify Y.J AddCommGrpCat]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Step 5 read backwards, on local sections.** Step 5 is the adjunction of Tag 03CZ, and its
inverse is the forward hom-set bijection `w ↦ unit ≫ w`; so on a local section it is the unit of
that adjunction followed by `w`. True by definition. -/
lemma pullbackTensorStep5_symm_val_app
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (w : (extendScalarsFSharp f).obj (inverseImageTensorSheaf f
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)) ⟶ N)
    (V : X.Cᵒᵖ)
    (z : (inverseImageTensorSheaf f
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
      ((inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).val.obj V) :
    ((pullbackTensorStep5 f F G N).symm w).val.app V z =
      w.val.app V
        (((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          (inverseImageTensorSheaf f
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))).val.app V z) :=
  rfl

/-- **The adjoint transpose over `f⁻¹O_D` of the comparison of Tag 03EL**: the morphism
`f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G ⟶ (f^*F ⊗_{O_C} f^*G)|_{f⁻¹O_D}` obtained by running the last two steps of
the chain backwards from the identity.

It is declared rather than written inline on purpose: its definition is the composite of two
`Equiv.symm`s applied to `𝟙`, and a statement which carries that composite inline is one whose
elaboration exhausts the budget — the unifier has to whnf the two steps through the inverse-image
structure sheaf. Declaring it once absorbs that into a declared type. -/
def pullbackTensorTranspose
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    inverseImageTensorSheaf f
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
      (SheafOfModules.restrictScalars f.fSharpInverseImage).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
          ((f.pullbackModules).obj F)).obj ((f.pullbackModules).obj G)) :=
  (pullbackTensorStep5 f F G
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
          ((f.pullbackModules).obj F)).obj ((f.pullbackModules).obj G))).symm
    ((pullbackTensorStep6 f F G
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
          ((f.pullbackModules).obj F)).obj ((f.pullbackModules).obj G))).symm (𝟙 _))

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [HasWeakSheafify Y.J AddCommGrpCat]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The pure-tensor formula for steps 5 and 6 of the chain of Tag 03EL**: the adjoint transpose
over `f⁻¹O_D` of the comparison carries the image of a pure tensor `a ⊗ₜ b` of local sections of
the two inverse images to the pure tensor of their images under the unit of Tag 03CZ,

`η(a ⊗ₜ b) ↦ η(ν(a) ⊗ₜ ν(b))`,

where `ν : f⁻¹F ⟶ (O_C ⊗_{f⁻¹O_D} f⁻¹F)|` is that unit, `a ↦ 1 ⊗ₜ a` on sections. This is the
`unit(a) ⊗ₜ unit(b)` shape the pure-tensor formula for the comparison of Tag 03EL has to have,
established for the two steps of the chain which produce it.

The three inputs are `pullbackTensorStep6_symm_id`, `pullbackTensorStep5_symm_val_app` together
with the unit formula
`extendRestrictScalarsAdjunction_unit_app_val_app_moduleSheafifyUnit` of
`Stacks.Sheaves.RingedToposModules`, and the section formula for step 6,
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_moduleSheafifyUnit_tmul_tmul`, used
at the scalar `1`. -/
lemma pullbackTensorTranspose_val_app_moduleSheafifyUnit_tmul
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (V : X.Cᵒᵖ)
    (a :
      ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).val.obj V)
    (b :
      ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G).val.obj V) :
    (pullbackTensorTranspose f F G).val.app V
        ((moduleSheafifyUnit (isSheaf_inverseImageStructureCommRing f)
            (((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).val ⊗
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G).val)).app V
          (a ⊗ₜ[(ringPresheaf (inverseImageStructureCommRing f)).obj V] b)) =
      (moduleSheafifyUnit (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
          ((SheafOfModules.forget
            (commRingSheaf X.J X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) ⋙
              PresheafOfModules.restrictScalars
                (𝟙
                  (commRingSheaf X.J X.O.obj
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).obj)).obj
            ((PresheafOfModules.sheafification
                (R :=
                  commRingSheaf X.J X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
                  (𝟙 _)).obj
              ((changeOfRings (fSharpCommRing f)).obj
                ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).val)) ⊗
            (SheafOfModules.forget
              (commRingSheaf X.J X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) ⋙
              PresheafOfModules.restrictScalars
                (𝟙
                  (commRingSheaf X.J X.O.obj
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).obj)).obj
            ((PresheafOfModules.sheafification
                (R :=
                  commRingSheaf X.J X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
                  (𝟙 _)).obj
              ((changeOfRings (fSharpCommRing f)).obj
                ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G).val)))).app V
        ((((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (isSheaf_inverseImageStructureCommRing f)
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)).val.app V a)
          ⊗ₜ[(ringPresheaf X.O.obj).obj V]
          (((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (isSheaf_inverseImageStructureCommRing f)
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).val.app V b)) := by
  refine Eq.trans (congrArg (fun w ↦ (SheafOfModules.Hom.val
      ((pullbackTensorStep5 f F G
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
            ((f.pullbackModules).obj F)).obj ((f.pullbackModules).obj G))).symm w)).app V
      ((moduleSheafifyUnit (isSheaf_inverseImageStructureCommRing f)
          (((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).val ⊗
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G).val)).app V
        (a ⊗ₜ[(ringPresheaf (inverseImageStructureCommRing f)).obj V] b)))
    (pullbackTensorStep6_symm_id f F G)) ?_
  refine Eq.trans (pullbackTensorStep5_symm_val_app f F G _ _ V _) ?_
  refine Eq.trans (congrArg ((extendScalarsTensorIso (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
      ((inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).hom.val.app V)
    (extendRestrictScalarsAdjunction_unit_app_val_app_moduleSheafifyUnit (fSharpCommRing f)
      (isSheaf_inverseImageStructureCommRing f)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property _ V _)) ?_
  exact extendScalarsTensorIso_hom_moduleSheafifyUnit_tmul_tmul (fSharpCommRing f)
    (isSheaf_inverseImageStructureCommRing f) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) V 1 a b

/-- The comparison of Tag 03EL is the morphism which the chain of bijections carries to the
identity: `(pullbackTensorIso f).hom.app (F, G)` is the preimage, under
`Stacks.SheafOfModules.pullbackTensorHomEquiv` at the target `f^*F ⊗_{O_C} f^*G`, of the identity
of that target. This is the statement to start from when pinning the comparison down on local
sections. -/
lemma pullbackTensorIso_hom_app
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (pullbackTensorIso f).hom.app (F, G) =
      (pullbackTensorHomEquiv f F G
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
            ((f.pullbackModules).obj F)).obj
              ((f.pullbackModules).obj G))).symm
        (𝟙
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj
          ((f.pullbackModules).obj F)).obj
            ((f.pullbackModules).obj G))) := rfl

end Chain

end Stacks.SheafOfModules

end
