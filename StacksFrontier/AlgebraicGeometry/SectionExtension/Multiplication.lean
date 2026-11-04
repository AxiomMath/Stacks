module

public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Ring

/-!
# Multiplying global sections of the tensor powers of an invertible sheaf, over an open

Let `X` be a ringed space whose stalks are local rings and let `L` be an invertible sheaf of
`𝒪_X`-modules. [Stacks, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV) multiplies a
global section of `L^{⊗ a}` by a global section of `L^{⊗ b}` to give a global section of
`L^{⊗ (a + b)}`. This file carries out the same multiplication **sectionwise**, over an
arbitrary open, and draws the two consequences that the global construction cannot state:
the multiplication is `𝒪_X(U)`-bilinear on sections over `U`, and the nonvanishing locus of a
product is the intersection of the two nonvanishing loci.

## Main definitions

* `Stacks.SheafOfModules.Invertible.tensorPowerModule'`: the tensor power of Tag 01CU ascribed
  at `SheafOfModules (structureSheafRing X)`.
* `Stacks.SheafOfModules.Invertible.tensorSheafPowerMulIso'`: the multiplication isomorphism
  `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}` of Tag 01CU, at that spelling.
* `Stacks.SheafOfModules.Invertible.sectionMulOver`: the product of a section of `L^{⊗ a}` and
  a section of `L^{⊗ b}` **over an open**.
* `Stacks.SheafOfModules.Invertible.sectionMul'` and `sectionPow'`: the product of two global
  sections and the power of one, through `sectionMulOver`.

## Main results

* `Stacks.SheafOfModules.Invertible.sectionMulOver_smul_left` and `sectionMulOver_smul_right`:
  the product over an open is `𝒪_X(U)`-bilinear.
* `Stacks.SheafOfModules.Invertible.nonvanishingLocus_sectionMul'`: **`X_{s t} = X_s ∩ X_t`**,
  and `nonvanishingLocus_sectionPow'`: `X_{s^k} = X_s` for `k ≥ 1`.
* `Stacks.SheafOfModules.Invertible.sectionPow'_eval_eq_of_smul_eq`: if `h • q = p` over an
  open `V`, then `h ^ k • q ^ k = p ^ k` over `V`.

## Implementation notes

**This is a second realization of the multiplication of Tag 01CV, and the identification with the
first is not proved here.** `Stacks.SheafOfModules.Invertible.sectionMul` of
`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Basic.lean` builds the same product out of the
monoidal structure on sheaves of modules, which is a `LocalizedMonoidal` category; nothing in the
development evaluates a monoidal section product over an open, and without such a rule neither the
bilinearity nor the multiplicativity of nonvanishing loci is reachable --
`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Basic.lean` records the second of those as
deliberately absent, saying it "needs the local description of the tensor product of invertible
sheaves". That local description is exactly `Stacks.SheafOfModules.tensorSections`, whose value over
every open is the image of an elementary tensor, so both facts are immediate at this spelling.

The identification `sectionMul' = sectionMul` reduces to the single computation

  `SheafOfModules.unitHomEquiv ((λ_ 𝟙).inv ≫ (s ⊗ₘ t) ≫ (tensorObjIso _ _ _ _).hom)
    = tensorSections _ _ s t`,

i.e. that the monoidal tensor of two global sections is the elementary tensor. It is not true by
`rfl` and is not proved here; no statement outside this file mentions either product.

**Why the ascription `tensorPowerModule'`.** `tensorPower X.presheaf _ L n` is only
definitionally an object of `SheafOfModules (structureSheafRing X)`, so the `Γ(X, U)`-module
structure on its sections is not found by instance search; at the ascribed spelling it is. This
is the same device as `Stacks.SheafOfModules.Invertible.tensorPowerModule` of
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/InversePairingLinear.lean`, which ascribes
at `X.Modules` for a scheme -- that spelling gives the `RingCat` carrier and does **not** serve
the `Γ(X, U)`-action the Tag 01CY trivialization API uses, so it cannot be reused here.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
  Stacks.SheafOfModules.monoidalPreadditive Stacks.SheafOfModules.braidedCategory

section Helpers

variable {X : RingedSpace.{u, u}}

/-- `toTensorSheafSection` is `Γ(X, U)`-linear: it is the application of a morphism of
presheaves of modules. The scalar acting on the right is ascribed at
`(Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj U`, which is
`X.presheaf.obj U` by one iota step; the module structure on the sections of a `sheafTensor`
object is the one carried by that spelling, and instance search does not cross the
difference. -/
theorem toTensorSheafSection_smul (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (c : X.presheaf.obj U)
    (z : TensorProduct (X.presheaf.obj U) (F.val.obj U) (G.val.obj U)) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G U (c • z)
      = @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf
            (⟨X.presheaf, X.IsSheaf⟩ :
              Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})).obj.obj U) _ _ c
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G U z) :=
  map_smul ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
    ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val)))).app U).hom c z

/-- `toTensorSheafSection` is additive. -/
theorem toTensorSheafSection_sub (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ)
    (z w : TensorProduct (X.presheaf.obj U) (F.val.obj U) (G.val.obj U)) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G U (z - w)
      = Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G U z
        - Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G U w :=
  map_sub ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
    ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val)))).app U).hom z w

/-- A morphism of sheaves of modules acts linearly on sections over an open. -/
theorem hom_app_smul {F H : SheafOfModules.{u} (structureSheafRing X)} (φ : F ⟶ H)
    (U : (Opens X.carrier)ᵒᵖ) (c : X.presheaf.obj U) (z : F.val.obj U) :
    (φ.val.app U).hom (c • z) = c • (φ.val.app U).hom z :=
  map_smul (φ.val.app U).hom c z

/-- A morphism of sheaves of modules is additive on sections over an open. -/
theorem hom_app_sub {F H : SheafOfModules.{u} (structureSheafRing X)} (φ : F ⟶ H)
    (U : (Opens X.carrier)ᵒᵖ) (z w : F.val.obj U) :
    (φ.val.app U).hom (z - w) = (φ.val.app U).hom z - (φ.val.app U).hom w :=
  map_sub (φ.val.app U).hom z w

/-- A global section is determined by its value over `⊤`. -/
theorem sectionsOfTop_eval_top_self (M : SheafOfModules.{u} (structureSheafRing X))
    (s : M.sections) : Stacks.SheafOfModules.sectionsOfTop M (s.eval (op ⊤)) = s := by
  refine PresheafOfModules.sections_ext _ _ fun W => ?_
  exact PresheafOfModules.sections_property s (homOfLE (le_top (a := W.unop))).op

end Helpers

/-- The `n`-th integer tensor power of an invertible module sheaf on a ringed space, ascribed
at `SheafOfModules (structureSheafRing X)`. -/
noncomputable abbrev tensorPowerModule' {X : RingedSpace.{u, u}}
    (L : SheafOfModules.{u} (structureSheafRing X))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X).property L] (n : ℤ) :
    SheafOfModules.{u} (structureSheafRing X) :=
  tensorPower X.presheaf (structureSheafRing X).property L n

variable {X : RingedSpace.{u, u}}
  (L : SheafOfModules.{u} (structureSheafRing X))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X).property L]

local notation "Lpow[" n "]" => tensorPowerModule' L ((n : ℕ) : ℤ)

/-- Every tensor power of an invertible module sheaf is invertible, in the class
`Stacks.SheafOfModules.IsInvertible` that `nonvanishingOpen` keys on and at the ascribed
spelling `tensorPowerModule'`. -/
instance isInvertible_tensorPowerModule' (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property
      (tensorPowerModule' L n) := by
  obtain ⟨F, hF, ⟨u⟩⟩ := (tensorPower_isInvertible X.presheaf
    (structureSheafRing X).property L n).exists_tensorFunctor
  exact ⟨F, hF, ⟨{ ι := u.ι, bijective := u.bijective }⟩⟩

/-- The multiplication isomorphism `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}` of Tag 01CU, ascribed
at `SheafOfModules (structureSheafRing X)`. -/
noncomputable def tensorSheafPowerMulIso' (a b : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) (structureSheafRing X).property⟩).obj
      (Lpow[a])).obj (Lpow[b])) ≅ Lpow[a + b] :=
  tensorSheafPowerMulIso X.presheaf (structureSheafRing X).property L a b

/-- The sectionwise product of a section of `L^{⊗ a}` and a section of `L^{⊗ b}`. -/
noncomputable def sectionMulOver (a b : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : Lpow[a].val.obj U) (y : Lpow[b].val.obj U) : Lpow[a + b].val.obj U :=
  (((tensorSheafPowerMulIso' L a b).hom.val.app U)).hom
    (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X Lpow[a] Lpow[b] U (x
      ⊗ₜ[X.presheaf.obj U] y))

/-- The product of two global sections of tensor powers. -/
noncomputable def sectionMul' {a b : ℕ} (s : Lpow[a].sections) (t : Lpow[b].sections) :
    Lpow[a + b].sections :=
  SheafOfModules.sectionsMap (tensorSheafPowerMulIso' L a b).hom
    (Stacks.SheafOfModules.tensorSections Lpow[a] Lpow[b] s t)

/-- The product of two global sections, evaluated over `U`, is the product over `U` of their
values. -/
theorem sectionMul'_eval {a b : ℕ} (s : Lpow[a].sections) (t : Lpow[b].sections)
    (U : (Opens X.carrier)ᵒᵖ) :
    (sectionMul' L s t).eval U = sectionMulOver L a b U (s.eval U) (t.eval U) := rfl

/-- The multiplication map of `L^{⊗ a} ⊗ L^{⊗ b}` after `toTensorSheafSection` is
`𝒪_X(U)`-linear. -/
private theorem mulIso'_toTensorSheafSection_smul (a b : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (c : X.presheaf.obj U)
    (z : TensorProduct (X.presheaf.obj U) (Lpow[a].val.obj U) (Lpow[b].val.obj U)) :
    ((tensorSheafPowerMulIso' L a b).hom.val.app U).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X Lpow[a] Lpow[b] U
          (c • z))
      = c • ((tensorSheafPowerMulIso' L a b).hom.val.app U).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X Lpow[a] Lpow[b] U
          z) :=
  (congrArg _ (toTensorSheafSection_smul Lpow[a] Lpow[b] U c z)).trans
    (hom_app_smul (tensorSheafPowerMulIso' L a b).hom U c _)

/-- The product over `U` is `𝒪_X(U)`-linear in its first argument. -/
theorem sectionMulOver_smul_left (a b : ℕ) (U : (Opens X.carrier)ᵒᵖ) (c : X.presheaf.obj U)
    (x : Lpow[a].val.obj U) (y : Lpow[b].val.obj U) :
    sectionMulOver L a b U (c • x) y = c • sectionMulOver L a b U x y := by
  unfold sectionMulOver
  rw [← mulIso'_toTensorSheafSection_smul, TensorProduct.smul_tmul']

/-- The product over `U` is `𝒪_X(U)`-linear in its second argument. -/
theorem sectionMulOver_smul_right (a b : ℕ) (U : (Opens X.carrier)ᵒᵖ) (c : X.presheaf.obj U)
    (x : Lpow[a].val.obj U) (y : Lpow[b].val.obj U) :
    sectionMulOver L a b U x (c • y) = c • sectionMulOver L a b U x y := by
  unfold sectionMulOver
  rw [← mulIso'_toTensorSheafSection_smul, TensorProduct.tmul_smul]

/-- The product over `U` commutes with subtraction in its second argument. -/
theorem sectionMulOver_sub_right (a b : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : Lpow[a].val.obj U) (y y' : Lpow[b].val.obj U) :
    sectionMulOver L a b U x (y - y')
      = sectionMulOver L a b U x y - sectionMulOver L a b U x y' :=
  (congrArg (fun z => ((tensorSheafPowerMulIso' L a b).hom.val.app U).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X Lpow[a] Lpow[b] U z))
      (TensorProduct.tmul_sub x y y')).trans
    ((congrArg ((tensorSheafPowerMulIso' L a b).hom.val.app U).hom
        (toTensorSheafSection_sub Lpow[a] Lpow[b] U (x ⊗ₜ[X.presheaf.obj U] y)
          (x ⊗ₜ[X.presheaf.obj U] y'))).trans
      (hom_app_sub (tensorSheafPowerMulIso' L a b).hom U _ _))

/-! ### Powers of a global section -/

/-- The `k`-th power of a global section of `L^{⊗ n}`, a global section of `L^{⊗ (n * k)}`. -/
noncomputable def sectionPow' {n : ℕ} (s : Lpow[n].sections) : (k : ℕ) → Lpow[n * k].sections
  | 0 => sectionOne X.presheaf (structureSheafRing X).property L
  | k + 1 => sectionMul' L (sectionPow' s k) s

/-- The zeroth power of a global section is the unit section `sectionOne`. -/
theorem sectionPow'_zero {n : ℕ} (s : Lpow[n].sections) :
    sectionPow' L s 0 = sectionOne X.presheaf (structureSheafRing X).property L := rfl

/-- The `(k + 1)`-th power of `s` is the product of its `k`-th power with `s`. -/
theorem sectionPow'_succ {n : ℕ} (s : Lpow[n].sections) (k : ℕ) :
    sectionPow' L s (k + 1) = sectionMul' L (sectionPow' L s k) s := rfl

/-- The unit section of `L^{⊗ 0}` is the unit section `unitSections X` of the structure
sheaf. -/
theorem sectionOne_eq_unitSections :
    sectionOne X.presheaf (structureSheafRing X).property L
      = Stacks.SheafOfModules.unitSections X := rfl

/-- If `h • q = p` over `V`, then `h ^ k • q ^ k = p ^ k` over `V`. -/
theorem sectionPow'_eval_eq_of_smul_eq {n : ℕ} (p q : Lpow[n].sections)
    (V : Opens X.carrier) (h : X.presheaf.obj (op V))
    (hh : h • q.eval (op V) = p.eval (op V)) (k : ℕ) :
    (sectionPow' L p k).eval (op V) = h ^ k • (sectionPow' L q k).eval (op V) := by
  induction k with
  | zero => simp [sectionPow']
  | succ k ih =>
      rw [sectionPow'_succ, sectionPow'_succ, sectionMul'_eval, sectionMul'_eval, ih, ← hh,
        sectionMulOver_smul_left, sectionMulOver_smul_right, pow_succ, ← smul_smul]

/-! ### Nonvanishing loci -/

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- The nonvanishing locus of a product of global sections is the intersection of their
nonvanishing loci: `X_{s t} = X_s ∩ X_t`. -/
theorem nonvanishingLocus_sectionMul' {a b : ℕ} (s : Lpow[a].sections) (t : Lpow[b].sections) :
    Stacks.SheafOfModules.nonvanishingLocus _ (sectionMul' L s t)
      = Stacks.SheafOfModules.nonvanishingLocus _ s
        ∩ Stacks.SheafOfModules.nonvanishingLocus _ t :=
  (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap (e := tensorSheafPowerMulIso' L a b)
      (s := Stacks.SheafOfModules.tensorSections Lpow[a] Lpow[b] s t)).trans
    (Stacks.SheafOfModules.nonvanishingLocus_tensorSections _ _ s t)

/-- The zeroth power of a global section vanishes nowhere. -/
theorem nonvanishingLocus_sectionPow'_zero {n : ℕ} (s : Lpow[n].sections) :
    Stacks.SheafOfModules.nonvanishingLocus Lpow[n * 0] (sectionPow' L s 0) = Set.univ :=
  Stacks.SheafOfModules.nonvanishingLocus_unitSections X

/-- For `k ≥ 1`, the nonvanishing locus of `s ^ k` is that of `s`: `X_{s^k} = X_s`. -/
theorem nonvanishingLocus_sectionPow' {n : ℕ} (s : Lpow[n].sections) (k : ℕ) (hk : 1 ≤ k) :
    Stacks.SheafOfModules.nonvanishingLocus _ (sectionPow' L s k)
      = Stacks.SheafOfModules.nonvanishingLocus _ s := by
  induction k with
  | zero => exact absurd hk (by simp)
  | succ k ih =>
      refine (nonvanishingLocus_sectionMul' L (sectionPow' L s k) s).trans ?_
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        rw [nonvanishingLocus_sectionPow'_zero L s]
        exact Set.univ_inter _
      · rw [ih hk0, Set.inter_self]

end Stacks.SheafOfModules.Invertible

end
