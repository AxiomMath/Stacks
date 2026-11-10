module

public import StacksFrontier.RingTheory.NaiveCotangent.TwoTermFlatBaseChange
public import StacksFrontier.RingTheory.NaiveCotangent.FlatBaseChangeQuasiIso

/-!
# The naive cotangent complex for a flat base change followed by a localization

Let `R → A` and `R → B` be ring maps with `B` flat over `R`, and let `C` be a localization of
`B ⊗_R A`.  Then the canonical map of two-term complexes of `C`-modules

`NL_{A/R} ⊗_A C ⟶ NL_{C/B}`

is a quasi-isomorphism.

This is the ring-level statement behind flat base change for the naive cotangent complex of a
*cartesian* square of schemes: if

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

is cartesian with `g` flat, then the local ring of `X'` at a point `x'` is a localization of
`𝒪_{X,g'(x')} ⊗_{𝒪_{Y,y}} 𝒪_{Y',f'(x')}` and `𝒪_{Y,y} → 𝒪_{Y',f'(x')}` is flat, which is
exactly the hypothesis of `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_base`
below.  It is the flat-base analogue of
`NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_atPrime`, where the localization of the base
is replaced by a flat base change.

The proof factors the comparison through `NL_{(B ⊗_R A)/B} ⊗_{B ⊗_R A} C`:

* `NL_{A/R} ⊗_A (B ⊗_R A) ⟶ NL_{(B ⊗_R A)/B}` is a quasi-isomorphism by flat base change,
  Stacks 00S4, in the form `FlatBaseChangeNL.statement3_isQuasiIso`;
* base changing it along the localization `B ⊗_R A → C` keeps it a quasi-isomorphism, because a
  localization is flat (`NaiveCotangent.IsQuasiIso.baseChange`);
* `NL_{(B ⊗_R A)/B} ⊗_{B ⊗_R A} C ⟶ NL_{C/B}` is a quasi-isomorphism by localization of the
  target over a fixed base, Stacks 00S7;
* and the source of the first base changed map is identified with `NL_{A/R} ⊗_A C` by
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`.

## Main definitions

* `NaiveCotangent.cancelBaseChangeChainMap`: the identification
  `(NL(α) ⊗_A D) ⊗_D C ≅ NL(α) ⊗_A C` of two-term complexes, for a tower `A → D → C`.

## Main results

* `NaiveCotangent.IsQuasiIso.of_comp_right`: a chain map whose composite with a
  quasi-isomorphism on the right is a quasi-isomorphism is itself one.
* `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_canHom`: flat base change, Stacks 00S4, in
  the `NaiveCotangent.nlExtensionBaseChangeMap` packaging.
* `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_base`: **the comparison
  `NL_{A/R} ⊗_A C ⟶ NL_{C/B}` is a quasi-isomorphism** when `B` is flat over `R` and `C` is a
  localization of `B ⊗_R A`.

## Implementation notes

`Algebra.TensorProduct.rightAlgebra`, the `A`-algebra structure on `B ⊗_R A`, is a local
instance here as it is in `StacksFrontier.RingTheory.NaiveCotangent.BaseChange`; it is what makes
`B ⊗_R A` a target for base change of `NL_{A/R}`.

Everything is in one universe, for the reason recorded in
`StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget`: the two complexes must be
objects of a single `NaiveCotangent.TwoTerm C`, and their terms are built from `MvPolynomial A R`
and `MvPolynomial C B`.

## References

* [Stacks Project, Tag 00S4](https://stacks.math.columbia.edu/tag/00S4), the naive cotangent
  complex and flat base change.
* [Stacks Project, Tag 00S7](https://stacks.math.columbia.edu/tag/00S7), the naive cotangent
  complex and localization of the target.
* [Stacks Project, Tag 0FJZ](https://stacks.math.columbia.edu/tag/0FJZ), flat base change for the
  naive cotangent complex of a morphism of schemes.
-/

@[expose] public section

namespace NaiveCotangent

open Algebra TensorProduct

noncomputable section

/-!
## Cancelling a quasi-isomorphism on the right
-/

section Cancel

variable {S : Type*} [CommRing S] {A B D : TwoTerm S}

/-- **Cancelling a quasi-isomorphism on the right.**  If `f` and `g ∘ f` are quasi-isomorphisms
then so is `g`: the maps induced on `H₁` and on `H₀` compose, and a bijection composed with a
bijection on the right is a bijection exactly when the left factor is. -/
theorem IsQuasiIso.of_comp_right {f : ChainMap A B} {g : ChainMap B D} (hf : IsQuasiIso f)
    (hgf : IsQuasiIso (g.comp f)) : IsQuasiIso g := by
  refine ⟨(Function.Bijective.of_comp_iff g.onH₁ hf.1).mp ?_,
    (Function.Bijective.of_comp_iff g.onH₀ hf.2).mp ?_⟩
  · rw [← LinearMap.coe_comp, ← ChainMap.onH₁_comp]
    exact hgf.1
  · rw [← LinearMap.coe_comp, ← ChainMap.onH₀_comp]
    exact hgf.2

end Cancel

/-!
## Cancelling an intermediate base change
-/

section CancelBaseChange

variable {A D C : Type*} [CommRing A] [CommRing D] [CommRing C] [Algebra A D] [Algebra D C]
  [Algebra A C] [IsScalarTower A D C]

/-- Cancelling an intermediate base change commutes with the base change of a linear map: both
sides send `c ⊗ (d ⊗ m)` to `(d • c) ⊗ f m`.  Stated over bare modules, so that the
`TensorProduct.inductionOn` of the proof sees the tensor products rather than the fields of a
`NaiveCotangent.TwoTerm`. -/
theorem cancelBaseChange_baseChange_comm {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (z : C ⊗[D] (D ⊗[A] M)) :
    LinearMap.baseChange C f (AlgebraTensorModule.cancelBaseChange A D C C M z) =
      AlgebraTensorModule.cancelBaseChange A D C C N
        (LinearMap.baseChange C (LinearMap.baseChange D f) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c y =>
    induction y using TensorProduct.inductionOn with
    | tmul d x =>
      rw [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        AlgebraTensorModule.cancelBaseChange_tmul]
    | add y₁ y₂ hy₁ hy₂ => simp only [tmul_add, map_add, hy₁, hy₂]
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]

variable {R : Type*} [CommRing R] [Algebra R A] (P : Extension R A)

/-- **The intermediate base change cancels.**  For a tower `A → D → C` the two-term complex
`(NL(α) ⊗_A D) ⊗_D C` is `NL(α) ⊗_A C`, by
`TensorProduct.AlgebraTensorModule.cancelBaseChange` in each degree. -/
def cancelBaseChangeChainMap :
    ChainMap ((nlExtensionBaseChange P D).baseChange C) (nlExtensionBaseChange P C) where
  f₁ := (AlgebraTensorModule.cancelBaseChange A D C C P.Cotangent).toLinearMap
  f₀ := (AlgebraTensorModule.cancelBaseChange A D C C P.CotangentSpace).toLinearMap
  comm := LinearMap.ext fun z => cancelBaseChange_baseChange_comm P.cotangentComplex z

/-- The cancellation of an intermediate base change is a quasi-isomorphism: it is degreewise
bijective. -/
theorem isQuasiIso_cancelBaseChangeChainMap :
    IsQuasiIso (cancelBaseChangeChainMap (D := D) (C := C) P) :=
  isQuasiIso_of_bijective _
    (AlgebraTensorModule.cancelBaseChange A D C C P.Cotangent).bijective
    (AlgebraTensorModule.cancelBaseChange A D C C P.CotangentSpace).bijective

end CancelBaseChange

/-!
## Cancelling an intermediate base change in a composite comparison
-/

section Glue

variable {A D C : Type*} [CommRing A] [CommRing D] [CommRing C] [Algebra A D] [Algebra D C]
  [Algebra A C] [IsScalarTower A D C]
  {M N T₀ : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [Module D N] [IsScalarTower A D N]
  [AddCommGroup T₀] [Module A T₀] [Module D T₀] [Module C T₀]
  [IsScalarTower D C T₀] [IsScalarTower A C T₀]

/-- **The composite of two base changed comparisons, after cancelling the intermediate base
change.**  Let `A → D → C` be a tower, let `φ : M → N` be `A`-linear and `ψ : N → T₀` be
`D`-linear, and let `χ = ψ ∘ φ`.  Then the `C`-linear extension of `χ` on `C ⊗_A M`, read through
the cancellation `C ⊗_D (D ⊗_A M) ≅ C ⊗_A M`, is the `C`-linear extension of `ψ` composed with
the base change to `C` of the `D`-linear extension of `φ`.

Both sides send `c ⊗ (d ⊗ m)` to `(d • c) • χ m`; the two spellings of that scalar differ by the
commutativity of `C`. -/
theorem liftBaseChange_cancelBaseChange (φ : M →ₗ[A] N) (ψ : N →ₗ[D] T₀) (χ : M →ₗ[A] T₀)
    (hχ : ∀ m, χ m = ψ (φ m)) (z : C ⊗[D] (D ⊗[A] M)) :
    χ.liftBaseChange C (AlgebraTensorModule.cancelBaseChange A D C C M z) =
      ψ.liftBaseChange C (LinearMap.baseChange C (φ.liftBaseChange D) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c y =>
    induction y using TensorProduct.inductionOn with
    | tmul d x =>
      rw [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.liftBaseChange_tmul,
        LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
        LinearMap.liftBaseChange_tmul, hχ x, map_smul, smul_assoc, smul_comm]
    | add y₁ y₂ hy₁ hy₂ => simp only [tmul_add, map_add, hy₁, hy₂]
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]

end Glue

/-!
## Flat base change and a localization of the target
-/

section FlatBaseLocalizedTarget

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **Flat base change for the naive cotangent complex**, Stacks 00S4, in the packaging of
`NaiveCotangent.nlExtensionBaseChangeMap`: for `B` flat over `R` the canonical map
`NL_{A/R} ⊗_A (B ⊗_R A) ⟶ NL_{(B ⊗_R A)/B}` is a quasi-isomorphism.

This is `FlatBaseChangeNL.statement3_isQuasiIso` read through the identifications
`NaiveCotangent.nlExtensionBaseChange (Generators.self R A).toExtension (B ⊗_R A) =
FlatBaseChangeNL.twoTerm (FlatBaseChangeNL.nlCanDiffBaseChange B)` and
`FlatBaseChangeNL.twoTerm (Generators.self B (B ⊗_R A)).toExtension.cotangentComplex =
NaiveCotangent.nlOfExtension (Generators.self B (B ⊗_R A)).toExtension`, both of which hold by
definition, the chain map being pinned down by its two components. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_canHom [Module.Flat R B] :
    IsQuasiIso (nlExtensionBaseChangeMap (T := B ⊗[R] A)
      (FlatBaseChangeNL.canHom (R := R) (S := A) B)) := by
  obtain ⟨f, h1, h0, hq⟩ := FlatBaseChangeNL.statement3_isQuasiIso (R := R) (S := A) B
  have hf : f = nlExtensionBaseChangeMap (T := B ⊗[R] A)
      (FlatBaseChangeNL.canHom (R := R) (S := A) B) := ChainMap.ext h1 h0
  exact hf ▸ hq

variable {C : Type u} [CommRing C] [Algebra R C] [Algebra A C] [Algebra B C]
  [Algebra (B ⊗[R] A) C] [IsScalarTower R A C] [IsScalarTower R B C]
  [IsScalarTower A (B ⊗[R] A) C] [IsScalarTower B (B ⊗[R] A) C]

/-- The canonical morphism of extensions `NL_{A/R} → NL_{C/B}` through
`NL_{(B ⊗_R A)/B}`: flat base change along `R → B` followed by the default morphism to the
canonical presentation of the localization `C`. -/
abbrev flatBaseLocalizedHom :
    ((Generators.self R A).toExtension).Hom ((Generators.self B C).toExtension) :=
  (((Generators.self B (B ⊗[R] A)).defaultHom (Generators.self B C)).toExtensionHom).comp
    (FlatBaseChangeNL.canHom (R := R) (S := A) B)

omit [IsScalarTower R A C] in
/-- The comparison attached to `NaiveCotangent.flatBaseLocalizedHom` factors, after cancelling
the intermediate base change along `B ⊗_R A → C`, as the base change to `C` of flat base change
followed by localization of the target. -/
theorem nlExtensionBaseChangeMap_flatBaseLocalizedHom_comp_cancel :
    (nlExtensionBaseChangeMap (T := C) (flatBaseLocalizedHom (R := R) (A := A) (B := B)
          (C := C))).comp
        (cancelBaseChangeChainMap (C := C) (D := B ⊗[R] A) ((Generators.self R A).toExtension)) =
      (nlExtensionBaseChangeMap (T := C)
            (((Generators.self B (B ⊗[R] A)).defaultHom
              (Generators.self B C)).toExtensionHom)).comp
        ((nlExtensionBaseChangeMap (T := B ⊗[R] A)
          (FlatBaseChangeNL.canHom (R := R) (S := A) B)).baseChange C) := by
  -- the scalar towers on the terms of the two extensions.  Instance search does not find these
  -- on its own in this context, so they are supplied; being `Prop`-valued classes they are
  -- interchangeable with whatever the statement was elaborated against.
  have : IsScalarTower A (B ⊗[R] A)
      ((Generators.self B (B ⊗[R] A)).toExtension).Cotangent :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A (B ⊗[R] A)
      ((Generators.self B (B ⊗[R] A)).toExtension).CotangentSpace := isScalarTower_left
  have : IsScalarTower A C ((Generators.self B C).toExtension).Cotangent :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (B ⊗[R] A) C ((Generators.self B C).toExtension).Cotangent :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A C ((Generators.self B C).toExtension).CotangentSpace :=
    isScalarTower_left
  have : IsScalarTower (B ⊗[R] A) C ((Generators.self B C).toExtension).CotangentSpace :=
    isScalarTower_left
  refine ChainMap.ext (LinearMap.ext fun z => ?_) (LinearMap.ext fun z => ?_)
  · exact liftBaseChange_cancelBaseChange
      (Extension.Cotangent.map (FlatBaseChangeNL.canHom (R := R) (S := A) B))
      (Extension.Cotangent.map
        (((Generators.self B (B ⊗[R] A)).defaultHom (Generators.self B C)).toExtensionHom))
      (Extension.Cotangent.map (flatBaseLocalizedHom (R := R) (A := A) (B := B) (C := C)))
      (fun m => by simp [flatBaseLocalizedHom, Extension.Cotangent.map_comp]) z
  · exact liftBaseChange_cancelBaseChange
      (Extension.CotangentSpace.map (FlatBaseChangeNL.canHom (R := R) (S := A) B))
      (Extension.CotangentSpace.map
        (((Generators.self B (B ⊗[R] A)).defaultHom (Generators.self B C)).toExtensionHom))
      (Extension.CotangentSpace.map (flatBaseLocalizedHom (R := R) (A := A) (B := B) (C := C)))
      (fun m => by simp [flatBaseLocalizedHom, Extension.CotangentSpace.map_comp_apply]) z

/-- **The naive cotangent complex for a flat base change followed by a localization.**  Let
`R → A` be a ring map, let `R → B` be flat, and let `C` be a localization of `B ⊗_R A` at a
multiplicative subset, compatibly with the maps out of `A` and `B`.  Then the canonical map of
two-term complexes of `C`-modules

`NL_{A/R} ⊗_A C ⟶ NL_{C/B}`

is a quasi-isomorphism.  The statement holds for every morphism of extensions `h` inducing it:
any two are homotopic, so the maps induced on `H₁` and `H₀` agree.

This declaration carries **no** `@[stacks]` attribute: it is the ring-level input to flat base
change for the naive cotangent complex of a morphism of schemes (Stacks 0FJZ), not that
statement, which also requires the identification of the stalks of a cartesian square. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_of_flat_base [Module.Flat R B]
    (M : Submonoid (B ⊗[R] A)) [IsLocalization M C]
    (h : ((Generators.self R A).toExtension).Hom ((Generators.self B C).toExtension)) :
    IsQuasiIso (nlExtensionBaseChangeMap (T := C) h) := by
  have : Module.Flat (B ⊗[R] A) C := IsLocalization.flat C M
  refine isQuasiIso_nlExtensionBaseChangeMap_congr h
    (flatBaseLocalizedHom (R := R) (A := A) (B := B) (C := C)) ?_
  refine IsQuasiIso.of_comp_right
    (isQuasiIso_cancelBaseChangeChainMap (D := B ⊗[R] A) (C := C)
      ((Generators.self R A).toExtension)) ?_
  rw [nlExtensionBaseChangeMap_flatBaseLocalizedHom_comp_cancel]
  exact (isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization M _).comp
    (isQuasiIso_nlExtensionBaseChangeMap_canHom.baseChange C)

end FlatBaseLocalizedTarget

end

end NaiveCotangent

end
