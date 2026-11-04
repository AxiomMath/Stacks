module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.UnitCase

/-!
# The projection formula when the module on the target is free of finite rank

For a morphism of ringed spaces `f : Z ⟶ X`,
`StacksFrontier/AlgebraicGeometry/ProjectionFormula/Basic.lean` builds the canonical map

`Stacks.AffineProjectionFormula.projectionFormulaMap f 𝒢 ℋ : f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)`

and `ProjectionFormula/UnitCase.lean` proves it invertible, for an arbitrary morphism of ringed
spaces and with no hypothesis on `𝒢`, when `ℋ` is the structure sheaf `𝒪_X`.  This file upgrades
that from rank one to **finite rank**: the map is invertible whenever `ℋ` is a finite biproduct of
copies of `𝒪_X`, and hence whenever `ℋ` is isomorphic to one.

[Stacks, Tag 01E8] proves its projection formula by the sentence *"This is clear when
`ℰ = 𝒪_Y^{⊕ n}`, and follows in general by working locally on `Y`"*.  The statements below are the
first half of that sentence, in full; what they do not supply is the locality, for which see the
implementation notes.

## The argument

Invertibility of the projection-formula map at a finite biproduct follows from invertibility at
each summand by a completely general fact about natural transformations, proved here as
`Stacks.AffineProjectionFormula.isIso_app_biproduct`: *a natural transformation of additive
functors which is invertible at each of finitely many objects is invertible at their biproduct.*
Its inverse is written down,

`∑ j, G(π j) ≫ (α_{f j})⁻¹ ≫ F(ι j)`,

and the two triangle identities are the naturality of `α` at the projections and at the
inclusions together with `CategoryTheory.Limits.biproduct.total` and additivity of `F` and of `G`.

To apply it, the projection-formula map has to be exhibited as a natural transformation in `ℋ`,
which is `projectionFormulaNatTrans`, and the two functors it compares have to be additive:

* `H ↦ f_*𝒢 ⊗ H` is additive because **tensoring with a fixed sheaf of modules is additive**,
  which is `tensorSheaf_map_add_right` below;
* `H ↦ f_*(𝒢 ⊗ f^*H)` is additive because `f^*` and `f_*` are, both being adjoints, and because
  of the same fact about the tensor product.

## Main results

* `Stacks.AffineProjectionFormula.tensorSheaf_map_add_right` and `tensorSheaf_map_add_left`:
  **the tensor product of sheaves of modules on a ringed space is additive in each argument.**
  Proved from the canonical tensor API: `Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`
  reads the uncurried tensor of two morphisms as the sheafification of the objectwise
  `PresheafOfModules.tensorHom`, where additivity in one slot is
  `PresheafOfModules.tensorHom_add_left`, respectively `tensorHom_add_right`, and sheafification
  is additive.
* `Stacks.AffineProjectionFormula.isIso_app_biproduct`: **the biproduct reducer**, for an
  arbitrary natural transformation of additive functors between preadditive categories.
* `Stacks.AffineProjectionFormula.projectionFormulaNatTrans`: the projection-formula map as a
  natural transformation in the module on the target.
* `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_biproduct`: invertibility of the
  projection-formula map at a finite biproduct follows from invertibility at each summand.
* `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_biproduct_structureModule`:
  **the projection formula at `ℋ = 𝒪_X^{⊕ n}`, for an arbitrary morphism of ringed spaces and
  with no hypothesis on `𝒢`.**
* `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_iso_biproduct_structureModule`:
  the same whenever `ℋ` is isomorphic to a finite biproduct of copies of `𝒪_X`, i.e. whenever
  `ℋ` is free of finite rank.

## Implementation notes

*No `stacks` attribute is attached, and the gap is in the statement.*  [Stacks, Tag 01E8] asks
for `ℰ ⊗ R^q f_*ℱ ≅ R^q f_*(f^*ℰ ⊗ ℱ)` for every `q ≥ 0` and every **finite locally free** `ℰ`,
together with an isomorphism in `D^+(Y)` functorial in `ℱ`.  What is proved here is the case
`q = 0` at a **free** `ℰ`, which carries a hypothesis the tag does not, so by the covering-set
rule none of these declarations is a member of the covering set of that tag.  The locality on
`X` that removes the globality of the hypothesis is `ProjectionFormula/Locality.lean`, and the
tag's `q = 0` clause is carried on
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree` in
`ProjectionFormula/FiniteLocallyFree.lean`.

*The biproduct reducer needs no preservation hypothesis.*  Conjugating by
`CategoryTheory.Functor.mapBiproduct` would ask for `PreservesBiproduct`, which an additive
functor does have — `CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive` is a Mathlib
instance — but the explicit inverse above needs only `Functor.Additive`, through
`CategoryTheory.Functor.map_sum` and `CategoryTheory.Functor.map_id`, so the reducer is stated
with additivity alone.

*Tensoring with a fixed module cannot be made additive by composing.*  The functor
`H ↦ f_*𝒢 ⊗ H` is `CategoryTheory.Prod.sectR _ _ ⋙
CategoryTheory.Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)`, and
`Prod.sectR` is **not** additive — it carries `φ + ψ` to `(𝟙, φ + ψ)` while the sum of its values
is `(2 • 𝟙, φ + ψ)` — so the additivity of the composite has to be proved for the composite, and
that is what `tensorSheaf_map_add_right` is for.

*The naturality of the projection-formula map in the module on the target is
`projectionFormulaMap_natural` with the first argument the identity*, after rewriting
`CategoryTheory.Functor.map_id` to remove `f_*(𝟙 𝒢)`.  Note the explicit parenthesisation in
`pushforwardTensorPullbackFunctor`: `⋙` is right-associative, so the additivity instance for
`Prod.sectR 𝒢 _ ⋙ Functor.uncurry.obj (Tensor.sheafTensor Z.sheaf)` is found only when that
composite is bracketed as a unit.

*Both tensoring composites carry an explicit type ascription.*
`Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf`, the ring over which the canonical tensor
bifunctor is indexed, and `Stacks.RingedSpace.structureRingSheaf Z`, the ring over which
`pullbackFunctor` and `pushforwardFunctor` are indexed, are the same sheaf of rings by `rfl` —
both are `CategoryTheory.Sheaf.toRingCat _ Z.sheaf`.  But `Tensor.ringSheaf` is a plain `def`
while `structureRingSheaf` is an `abbrev`, so instance search, which unfolds only reducible
definitions, does not see through the former.  Left to itself the elaborator types the
tensoring composite at `Tensor.ringSheaf Z.sheaf` and then no additivity instance matches; the
ascription pins it at `structureRingSheaf Z` instead, which is the spelling
`tensorSheafSectR_additive` is stated at and the one the adjoint functors already use.

*Finite biproducts of sheaves of modules on a ringed space.*  `HasFiniteProducts` is already an
instance at this spelling while `HasFiniteBiproducts` is not;
`hasFiniteBiproducts_structureRingSheaf` supplies the latter from the former, as
`StacksTag03EU.hasFiniteBiproducts_sheafOfModules` does at the general `SheafOfModules`
spelling.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open PresheafOfModules (Hom)
open scoped TensorProduct
open scoped CategoryTheory.Prod

namespace Stacks.AffineProjectionFormula

universe v₁ v₂ u₁ u₂ u

/-! ### The biproduct reducer -/

/-- **A natural transformation of additive functors which is invertible at each of finitely many
objects is invertible at their biproduct.**

The inverse is `∑ j, G(π j) ≫ (α_{f j})⁻¹ ≫ F(ι j)`.  Composing it with `α` on either side, the
naturality of `α` at the projections, respectively at the inclusions, cancels the two copies of
`α_{f j}`, leaving `∑ j, F(π j ≫ ι j)`, respectively `∑ j, G(π j ≫ ι j)`; additivity turns the
sum into the image of `∑ j, π j ≫ ι j = 𝟙`.

No preservation hypothesis is needed: additivity of `F` and of `G` is used only through
`CategoryTheory.Functor.map_sum` and `CategoryTheory.Functor.map_id`. -/
theorem isIso_app_biproduct {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D] {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    {J : Type} [Finite J] (f : J → C) [HasBiproduct f] (h : ∀ j, IsIso (α.app (f j))) :
    IsIso (α.app (⨁ f)) := by
  have : ∀ j, IsIso (α.app (f j)) := h
  obtain ⟨_⟩ := nonempty_fintype J
  refine ⟨∑ j : J, G.map (biproduct.π f j) ≫ inv (α.app (f j)) ≫ F.map (biproduct.ι f j),
    ?_, ?_⟩
  · have step : ∀ j : J, α.app (⨁ f) ≫
        (G.map (biproduct.π f j) ≫ inv (α.app (f j)) ≫ F.map (biproduct.ι f j))
          = F.map (biproduct.π f j ≫ biproduct.ι f j) := by
      intro j
      rw [← Category.assoc, ← α.naturality (biproduct.π f j), F.map_comp]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [Preadditive.comp_sum, Finset.sum_congr rfl fun j _ => step j, ← F.map_sum,
      biproduct.total, F.map_id]
  · have step : ∀ j : J, (G.map (biproduct.π f j) ≫ inv (α.app (f j)) ≫ F.map (biproduct.ι f j))
        ≫ α.app (⨁ f) = G.map (biproduct.π f j ≫ biproduct.ι f j) := by
      intro j
      rw [G.map_comp]
      simp only [Category.assoc, α.naturality (biproduct.ι f j), IsIso.inv_hom_id_assoc]
    rw [Preadditive.sum_comp, Finset.sum_congr rfl fun j _ => step j, ← G.map_sum,
      biproduct.total, G.map_id]

/-! ### Additivity of the tensor product of sheaves of modules -/

section Tensor

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The uncurried tensor of morphisms is additive as soon as the objectwise `tensorHom`s are, since
sheafification is additive. -/
private theorem sheafTensor_uncurry_map_add_of_tensorHom_add
    {A A' M N : SheafOfModules.{u} (structureRingSheaf X)} (u₁ u₂ u₃ : A ⟶ A')
    (φ₁ φ₂ φ₃ : M ⟶ N)
    (h : PresheafOfModules.tensorHom (O := X.sheaf.obj) u₁.val φ₁.val =
      PresheafOfModules.tensorHom (O := X.sheaf.obj) u₂.val φ₂.val +
        PresheafOfModules.tensorHom (O := X.sheaf.obj) u₃.val φ₃.val) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
      (u₁ ×ₘ φ₁) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
          (u₂ ×ₘ φ₂) +
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
          (u₃ ×ₘ φ₃) := by
  let : (PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).Additive :=
    PresheafOfModules.sheafification_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)
  refine (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u}
    X.sheaf u₁ φ₁).trans ?_
  refine Eq.trans ?_ (congrArg₂ HAdd.hAdd
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u} X.sheaf u₂ φ₂)
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u} X.sheaf u₃ φ₃)).symm
  rw [h]
  exact Functor.map_add _

/-- **The tensor product of sheaves of modules on a ringed space is additive in its second
argument.** This follows from the canonical tensor-map additivity and the additivity of
sheafification. -/
theorem tensorSheaf_map_add_right {A A' : SheafOfModules.{u} (structureRingSheaf X)} (u : A ⟶ A')
    {M N : SheafOfModules.{u} (structureRingSheaf X)} (φ ψ : M ⟶ N) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
      (u ×ₘ (φ + ψ)) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
          (u ×ₘ φ) +
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map (u ×ₘ ψ) :=
  sheafTensor_uncurry_map_add_of_tensorHom_add _ _ _ _ _ _
    (PresheafOfModules.tensorHom_add_right (O := X.sheaf.obj) u.val φ.val ψ.val)

/-- **The tensor product of sheaves of modules on a ringed space is additive in its first
argument**, the mirror of `tensorSheaf_map_add_right`. -/
theorem tensorSheaf_map_add_left {M N : SheafOfModules.{u} (structureRingSheaf X)} (φ ψ : M ⟶ N)
    {B B' : SheafOfModules.{u} (structureRingSheaf X)} (v : B ⟶ B') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
      ((φ + ψ) ×ₘ v) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
          (φ ×ₘ v) +
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map (ψ ×ₘ v) :=
  sheafTensor_uncurry_map_add_of_tensorHom_add _ _ _ _ _ _
    (PresheafOfModules.tensorHom_add_left (O := X.sheaf.obj) φ.val ψ.val v.val)

/-- **Tensoring with a fixed sheaf of modules on the left is an additive functor.** -/
instance tensorSheafSectR_additive (A : SheafOfModules.{u} (structureRingSheaf X)) :
    ((Prod.sectR A (SheafOfModules.{u} (structureRingSheaf X)) ⋙
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)) :
      SheafOfModules.{u} (structureRingSheaf X) ⥤
        SheafOfModules.{u} (structureRingSheaf X))).Additive where
  map_add := tensorSheaf_map_add_right (𝟙 A) _ _

/-- **Tensoring with a fixed sheaf of modules on the right is an additive functor.** -/
instance tensorSheafSectL_additive (B : SheafOfModules.{u} (structureRingSheaf X)) :
    ((Prod.sectL (SheafOfModules.{u} (structureRingSheaf X)) B ⋙
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)) :
      SheafOfModules.{u} (structureRingSheaf X) ⥤
        SheafOfModules.{u} (structureRingSheaf X))).Additive where
  map_add := tensorSheaf_map_add_left _ _ (𝟙 B)

/-- Sheaves of modules on a ringed space have finite biproducts, `HasFiniteProducts` being an
instance at this spelling while `HasFiniteBiproducts` is not. -/
instance hasFiniteBiproducts_structureRingSheaf :
    HasFiniteBiproducts (SheafOfModules.{u} (structureRingSheaf X)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end Tensor

/-! ### Additivity of pushforward and of pullback -/

section Adjoints

variable {X Z : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ X)

/-- **The direct image of sheaves of modules along a morphism of ringed spaces is additive**,
being a right adjoint and therefore preserving binary products. -/
instance pushforwardFunctor_additive : (pushforwardFunctor f).Additive := by
  have : (pushforwardFunctor f).IsRightAdjoint := (pullbackAdjunction f).isRightAdjoint
  have : PreservesLimitsOfShape (Discrete WalkingPair) (pushforwardFunctor f) :=
    (Adjunction.ofIsRightAdjoint
      (pushforwardFunctor f)).rightAdjoint_preservesLimits.preservesLimitsOfShape
  exact Functor.additive_of_preserves_binary_products _

end Adjoints

/-! ### The projection-formula map as a natural transformation in the module on the target -/

section NatTrans

variable {X Z : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ X)
  (G : SheafOfModules.{u} (structureRingSheaf Z))

/-- The source of the projection-formula map as a functor of the module on the target,
`ℋ ↦ f_*𝒢 ⊗_{𝒪_X} ℋ`. -/
abbrev tensorPushforwardFunctor :
    SheafOfModules.{u} (structureRingSheaf X) ⥤ SheafOfModules.{u} (structureRingSheaf X) :=
  Prod.sectR ((pushforwardFunctor f).obj G) (SheafOfModules.{u} (structureRingSheaf X)) ⋙
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))

/-- The target of the projection-formula map as a functor of the module on the target,
`ℋ ↦ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)`.  The inner composite is bracketed so that the additivity instance
for tensoring with a fixed module is found. -/
abbrev pushforwardTensorPullbackFunctor :
    SheafOfModules.{u} (structureRingSheaf X) ⥤ SheafOfModules.{u} (structureRingSheaf X) :=
  pullbackFunctor f ⋙ ((Prod.sectR G (SheafOfModules.{u} (structureRingSheaf Z)) ⋙
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)) :
    SheafOfModules.{u} (structureRingSheaf Z) ⥤
      SheafOfModules.{u} (structureRingSheaf Z))) ⋙ pushforwardFunctor f

/-- **The projection-formula map as a natural transformation in the module on the target.**  Its
naturality is `Stacks.AffineProjectionFormula.projectionFormulaMap_natural` with the module on
the source held fixed. -/
def projectionFormulaNatTrans :
    tensorPushforwardFunctor f G ⟶ pushforwardTensorPullbackFunctor f G where
  app H := projectionFormulaMap f G H
  naturality := by
    intro H H' k
    have h := projectionFormulaMap_natural f (𝟙 G) k
    rw [CategoryTheory.Functor.map_id] at h
    exact h

/-- The components of `projectionFormulaNatTrans` are the projection-formula maps. -/
@[simp]
lemma projectionFormulaNatTrans_app (H : SheafOfModules.{u} (structureRingSheaf X)) :
    (projectionFormulaNatTrans f G).app H = projectionFormulaMap f G H := rfl

end NatTrans

/-! ### The projection formula at a module free of finite rank -/

section FiniteFree

variable {X Z : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ X)
  (G : SheafOfModules.{u} (structureRingSheaf Z))

/-- **Invertibility of the projection-formula map at a finite biproduct follows from
invertibility at each summand.**  This is the biproduct reducer applied to
`projectionFormulaNatTrans`, whose source and target functors are additive. -/
theorem isIso_projectionFormulaMap_biproduct {J : Type} [Finite J]
    (H : J → SheafOfModules.{u} (structureRingSheaf X))
    (h : ∀ j, IsIso (projectionFormulaMap f G (H j))) :
    IsIso (projectionFormulaMap f G (⨁ H)) :=
  isIso_app_biproduct (projectionFormulaNatTrans f G) H h

/-- **The projection formula at `ℋ = 𝒪_X^{⊕ n}`, for an arbitrary morphism of ringed spaces and
with no hypothesis on `𝒢`**: the canonical map
`f_*𝒢 ⊗_{𝒪_X} 𝒪_X^{⊕ n} ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*(𝒪_X^{⊕ n}))` is an isomorphism.

This is the `q = 0`, `ℰ = 𝒪_Y^{⊕ n}` case of [Stacks, Tag 01E8] — the whole of the first sentence
of that tag's proof. -/
theorem isIso_projectionFormulaMap_biproduct_structureModule (J : Type) [Finite J] :
    IsIso (projectionFormulaMap f G (⨁ fun _ : J => structureModule X)) :=
  isIso_projectionFormulaMap_biproduct f G _
    fun _ => isIso_projectionFormulaMap_structureModule f G

/-- **The projection formula whenever the module on the target is free of finite rank**, that is,
isomorphic to a finite biproduct of copies of `𝒪_X`.  This is the local situation that a
locality argument for the finite locally free case of [Stacks, Tag 01E8] would reduce to. -/
theorem isIso_projectionFormulaMap_of_iso_biproduct_structureModule {J : Type} [Finite J]
    {H : SheafOfModules.{u} (structureRingSheaf X)}
    (e : (⨁ fun _ : J => structureModule X) ≅ H) :
    IsIso (projectionFormulaMap f G H) :=
  isIso_projectionFormulaMap_of_iso f G e
    (isIso_projectionFormulaMap_biproduct_structureModule f G J)

end FiniteFree

end Stacks.AffineProjectionFormula

end
