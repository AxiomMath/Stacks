module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCoefficientChange
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationFiltration

/-!
# `Ō` and the powers of its augmentation ideal, read as presheaves of `𝒪`-modules

Work on the small model `CommAlgCat.smallBoundedPolynomialSite A B κ` of the polynomial site
`C_{B/A}`. The library carries the presheaf `Ō = 𝒪 ⊗_A B̲` and the powers `𝒦ⁿ` of its
augmentation ideal in the shape

`(smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} ↥B`

of presheaves of `B`-modules, which is the shape the homology `H_i(C_{B/A}, -) = (L_i colim)(-)`
of the site is taken in (`StacksFrontier.Cotangent.SurjectionSiteAugmentationFiltration`). The
change of coefficients of [Stacks, Tag 08QJ] is on the other hand stated for presheaves of
`𝒪`-modules, in the shape

`PresheafOfModules.{u} (CommAlgCat.smallPolynomialStructurePresheaf A B κ)`.

This file builds `Ō` and `𝒦ⁿ` in the second shape and identifies the underlying abelian
presheaves of the two readings, so that a statement proved about `Lπ_!` of the `𝒪`-module can be
transported to `L_i colim` of the presheaf of `B`-modules.

## The identification

Over an object `(P, α)` of the site the sections of `Ō` are `B ⊗_A P`, on which the polynomial
algebra `P = 𝒪(P, α)` acts through the ring map `p ↦ 1 ⊗ p`
(`CommAlgCat.smallSiteStructureToQuotient`); `𝒦ⁿ(P, α)` is an ideal of that ring, hence stable
under the action. Feeding the *already existing* abelian presheaf

`CommAlgCat.smallPolynomialAugmentationIdealPow A B κ n ⋙ forget₂ (ModuleCat ↥B) AddCommGrpCat`

to `PresheafOfModules.ofPresheaf` together with that action makes the identification of item 3
hold by `rfl`: `PresheafOfModules.ofPresheaf_presheaf` says that the underlying abelian presheaf
of the result is the functor it was built from, on the nose. So no comparison isomorphism is
introduced anywhere, and the compatibility of the identification with the inclusions
`𝒦ⁿ⁺¹ ⊆ 𝒦ⁿ ⊆ Ō` is likewise an equality: those morphisms of `𝒪`-modules are built with
`PresheafOfModules.homMk` from the whiskerings of the inclusions of `B`-modules that the library
already has.

## Main definitions

* `CommAlgCat.smallSiteStructureToQuotient`: the ring map `𝒪(X) ⟶ Ō(X)`, `p ↦ 1 ⊗ p`, along which
  `𝒪(X)` acts on the sections of `Ō` and of `𝒦ⁿ`.
* `CommAlgCat.smallPolynomialQuotientStructureModule`: **`Ō` as a presheaf of `𝒪`-modules.**
* `CommAlgCat.smallPolynomialAugmentationIdealPowStructureModule`: **`𝒦ⁿ` as a presheaf of
  `𝒪`-modules.**
* `CommAlgCat.smallPolynomialAugmentationIdealPowStructureIncl`,
  `CommAlgCat.smallPolynomialAugmentationIdealPowStructureOfLE` and
  `CommAlgCat.smallPolynomialAugmentationIdealPowStructureι`: the inclusions `𝒦ⁿ⁺¹ ⟶ 𝒦ⁿ`,
  `𝒦ᵐ ⟶ 𝒦ⁿ` for `n ≤ m`, and `𝒦ⁿ ⟶ Ō`, as morphisms of `𝒪`-modules.
* `CommAlgCat.smallPolynomialAugmentationIdealPowStructureSingle`: `𝒦ⁿ` placed in cohomological
  degree zero, which is the object [Stacks, Tag 08QJ] is stated at.

## Main results

* `CommAlgCat.smallPolynomialQuotientStructureModule_presheaf` and
  `CommAlgCat.smallPolynomialAugmentationIdealPowStructureModule_presheaf`: **the bridge.** The
  underlying abelian presheaf of each of the two `𝒪`-modules is the one underlying the presheaf
  of `B`-modules of the same name, by `rfl`.
* `CommAlgCat.toPresheaf_map_smallPolynomialAugmentationIdealPowStructureIncl` and its two
  companions: the bridge is compatible with all three families of inclusions, again by `rfl`.
* `CommAlgCat.isIso_derivedColimitTensorComparison_smallPolynomialAugmentationIdealPow`:
  [Stacks, Tag 08QJ] at `𝒦ⁿ`, with no hypothesis left undischarged — the comparison
  `Lπ_!(𝒦ⁿ) ⟶ Lπ_!(𝒦ⁿ ⊗^L_𝒪 B̲)` is an isomorphism in `D(Ab)`.

## Implementation notes

The `𝒪(X)`-module structures are `@[instance_reducible]` definitions rather than instances,
installed by `letI` where they are needed, as in
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite`: the sections of `Ō` already
carry a `B`-module structure and an action of the full ring `B ⊗_A P`, and a global instance for
a third ring of scalars on the same type is not wanted.

Computing `𝒦ⁿ ⊗^L_𝒪 B̲` is not done here; this file only puts `𝒦ⁿ` on the side of the gap
where [Stacks, Tag 08QJ] can reach it.

## References

* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace Stacks

/-- Let `M` carry module structures over two rings `R` and `S`, and let `p` be an `S`-submodule
of `M` whose carrier is stable under the `R`-action. Then `p` is an `R`-module. No compatibility
between the two actions is assumed: this is used to read an ideal of `Ō(U)`, which the library
holds as a `B`-submodule, as a module over the polynomial algebra `𝒪(U)`. -/
@[instance_reducible]
def submoduleModuleOfSMulMem {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R M] [Module S M] (p : Submodule S M)
    (hp : ∀ (r : R) (x : M), x ∈ p → r • x ∈ p) : Module R ↥p where
  smul r x := ⟨r • (x : M), hp r x x.2⟩
  one_smul x := Subtype.ext (one_smul R (x : M))
  mul_smul r s x := Subtype.ext (mul_smul r s (x : M))
  smul_zero r := Subtype.ext (smul_zero r)
  smul_add r x y := Subtype.ext (smul_add r (x : M) (y : M))
  add_smul r s x := Subtype.ext (add_smul r s (x : M))
  zero_smul x := Subtype.ext (zero_smul R (x : M))

/-- The action of `Stacks.submoduleModuleOfSMulMem` is the restriction of the action on the
ambient module. -/
lemma coe_submoduleModuleOfSMulMem_smul {R S M : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M] [Module S M] (p : Submodule S M)
    (hp : ∀ (r : R) (x : M), x ∈ p → r • x ∈ p) (r : R) (x : ↥p) :
    letI := submoduleModuleOfSMulMem p hp
    ((r • x : ↥p) : M) = r • (x : M) := rfl

end Stacks

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-! ### The ring map `𝒪 ⟶ Ō` -/

/-- **The ring map `𝒪(X) ⟶ Ō(X)`**, `p ↦ 1 ⊗ p`: the structure map of `Ō(X) = B ⊗_A 𝒪(X)` as an
algebra over the second tensor factor. It is along this map that the polynomial algebra `𝒪(X)`
acts on the sections of `Ō` and of the powers of its augmentation ideal. -/
def smallSiteStructureToQuotient (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) :
    ((smallPolynomialStructurePresheaf A B κ).obj X : Type u) →+*
      ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u) :=
  (Algebra.TensorProduct.includeRight (R := A) (A := (B : Type u))
    (B := ((((smallSiteToOver A B κ).obj X).left : CommAlgCat.{u} A) : Type u))).toRingHom

/-- The ring map `𝒪(X) ⟶ Ō(X)` sends `p` to `1 ⊗ p`. -/
lemma smallSiteStructureToQuotient_apply (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ)
    (p : ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)) :
    smallSiteStructureToQuotient A B κ X p = (1 : (B : Type u)) ⊗ₜ[A]
      (show ((((smallSiteToOver A B κ).obj X).left : CommAlgCat.{u} A) : Type u) from p) := rfl

/-- **The ring map `𝒪 ⟶ Ō` is natural**: the transition maps of `Ō` are the base change of
those of `𝒪`, so they carry `1 ⊗ p` to `1 ⊗ f(p)`. -/
lemma smallSiteStructureToQuotient_naturality
    {X Y : (smallBoundedPolynomialSite A B κ)ᵒᵖ} (f : X ⟶ Y)
    (p : ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)) :
    ((smallPolynomialQuotientAlgebra A B κ).map f).hom
        (smallSiteStructureToQuotient A B κ X p) =
      smallSiteStructureToQuotient A B κ Y ((smallPolynomialStructurePresheaf A B κ).map f p) :=
  rfl

/-! ### `Ō` as a presheaf of `𝒪`-modules -/

/-- **The `𝒪(X)`-module structure on `Ō(X) = B ⊗_A 𝒪(X)`**: `𝒪(X)` acts by multiplication
through the ring map `CommAlgCat.smallSiteStructureToQuotient`. -/
@[instance_reducible]
def smallPolynomialQuotientModuleStructure (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) :
    Module ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)
      ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u) :=
  Module.compHom _ (smallSiteStructureToQuotient A B κ X)

/-- The action of `𝒪(X)` on `Ō(X)` is multiplication by the image of the acting element. -/
lemma smallPolynomialQuotientModuleStructure_smul (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ)
    (r : ((smallPolynomialStructurePresheaf A B κ).obj X : Type u))
    (m : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) :
    letI := smallPolynomialQuotientModuleStructure A B κ X
    r • m = smallSiteStructureToQuotient A B κ X r * m := rfl

/-- **The transition maps of `Ō` are semilinear over those of `𝒪`.** Both are ring maps, and the
square identifying the two readings of `1 ⊗ p` is
`CommAlgCat.smallSiteStructureToQuotient_naturality`. -/
lemma smallPolynomialQuotientModule_map_smul
    {X Y : (smallBoundedPolynomialSite A B κ)ᵒᵖ} (f : X ⟶ Y)
    (r : ((smallPolynomialStructurePresheaf A B κ).obj X : Type u))
    (m : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) :
    letI := smallPolynomialQuotientModuleStructure A B κ X
    letI := smallPolynomialQuotientModuleStructure A B κ Y
    ((smallPolynomialQuotientAlgebra A B κ).map f).hom (r • m) =
      (smallPolynomialStructurePresheaf A B κ).map f r •
        ((smallPolynomialQuotientAlgebra A B κ).map f).hom m := by
  change ((smallPolynomialQuotientAlgebra A B κ).map f).hom
      (smallSiteStructureToQuotient A B κ X r * m) =
    smallSiteStructureToQuotient A B κ Y ((smallPolynomialStructurePresheaf A B κ).map f r) *
      ((smallPolynomialQuotientAlgebra A B κ).map f).hom m
  rw [map_mul, smallSiteStructureToQuotient_naturality]

/-- **`Ō = 𝒪 ⊗_A B̲` as a presheaf of `𝒪`-modules.** Its underlying abelian presheaf is, on the
nose, the one underlying `CommAlgCat.smallPolynomialQuotientModule`. -/
def smallPolynomialQuotientStructureModule :
    PresheafOfModules.{u} (smallPolynomialStructurePresheaf A B κ) :=
  letI : ∀ X : (smallBoundedPolynomialSite A B κ)ᵒᵖ,
      Module ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)
        ((smallPolynomialQuotientModule A B κ ⋙
          forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).obj X : Type u) :=
    fun X => smallPolynomialQuotientModuleStructure A B κ X
  PresheafOfModules.ofPresheaf
    (smallPolynomialQuotientModule A B κ ⋙
      forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u})
    (fun _ _ f r m => smallPolynomialQuotientModule_map_smul A B κ f r m)

/-- **The bridge for `Ō`.** The underlying abelian presheaf of `Ō` read as a presheaf of
`𝒪`-modules is the one underlying `Ō` read as a presheaf of `B`-modules. -/
@[simp]
lemma smallPolynomialQuotientStructureModule_presheaf :
    (smallPolynomialQuotientStructureModule A B κ).presheaf =
      smallPolynomialQuotientModule A B κ ⋙
        forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u} := rfl

/-- `CommAlgCat.smallPolynomialQuotientStructureModule_presheaf`, in the spelling
`PresheafOfModules.toPresheaf` that the consumers of [Stacks, Tag 08QJ] use. -/
lemma toPresheaf_obj_smallPolynomialQuotientStructureModule :
    (PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B κ)).obj
        (smallPolynomialQuotientStructureModule A B κ) =
      smallPolynomialQuotientModule A B κ ⋙
        forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u} := rfl

/-! ### `𝒦ⁿ` as a presheaf of `𝒪`-modules -/

/-- **The `𝒪(X)`-module structure on `𝒦ⁿ(X)`.** The sections of `𝒦ⁿ` are an ideal of the ring
`Ō(X)`, hence stable under multiplication by the image of `𝒪(X)`. -/
@[instance_reducible]
def smallPolynomialAugmentationIdealPowModuleStructure (n : ℕ)
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) :
    Module ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)
      ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X) :=
  letI := smallPolynomialQuotientModuleStructure A B κ X
  Stacks.submoduleModuleOfSMulMem (smallPolynomialAugmentationIdealPowSubmodule A B κ n X)
    (fun r x hx => show smallSiteStructureToQuotient A B κ X r * x ∈
      smallPolynomialAugmentationIdeal A B κ X ^ n from Ideal.mul_mem_left _ _ hx)

/-- **The transition maps of `𝒦ⁿ` are semilinear over those of `𝒪`**: they are the restrictions
of the transition maps of `Ō`, which are, by
`CommAlgCat.smallPolynomialQuotientModule_map_smul`. -/
lemma smallPolynomialAugmentationIdealPow_map_smul (n : ℕ)
    {X Y : (smallBoundedPolynomialSite A B κ)ᵒᵖ} (f : X ⟶ Y)
    (r : ((smallPolynomialStructurePresheaf A B κ).obj X : Type u))
    (m : ((smallPolynomialAugmentationIdealPow A B κ n ⋙
      forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).obj X : Type u)) :
    letI : ∀ Z : (smallBoundedPolynomialSite A B κ)ᵒᵖ,
        Module ((smallPolynomialStructurePresheaf A B κ).obj Z : Type u)
          ((smallPolynomialAugmentationIdealPow A B κ n ⋙
            forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).obj Z : Type u) :=
      fun Z => smallPolynomialAugmentationIdealPowModuleStructure A B κ n Z
    (smallPolynomialAugmentationIdealPow A B κ n ⋙
        forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).map f (r • m) =
      (smallPolynomialStructurePresheaf A B κ).map f r •
        (smallPolynomialAugmentationIdealPow A B κ n ⋙
          forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).map f m := by
  exact Subtype.ext <| smallPolynomialQuotientModule_map_smul A B κ f r
    (show ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X) from m).1

/-- **`𝒦ⁿ`, the `n`-th power of the augmentation ideal of `Ō`, as a presheaf of `𝒪`-modules.**
Its underlying abelian presheaf is, on the nose, the one underlying
`CommAlgCat.smallPolynomialAugmentationIdealPow`. -/
def smallPolynomialAugmentationIdealPowStructureModule (n : ℕ) :
    PresheafOfModules.{u} (smallPolynomialStructurePresheaf A B κ) :=
  letI : ∀ X : (smallBoundedPolynomialSite A B κ)ᵒᵖ,
      Module ((smallPolynomialStructurePresheaf A B κ).obj X : Type u)
        ((smallPolynomialAugmentationIdealPow A B κ n ⋙
          forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).obj X : Type u) :=
    fun X => smallPolynomialAugmentationIdealPowModuleStructure A B κ n X
  PresheafOfModules.ofPresheaf
    (smallPolynomialAugmentationIdealPow A B κ n ⋙
      forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u})
    (fun _ _ f r m => smallPolynomialAugmentationIdealPow_map_smul A B κ n f r m)

/-- **The bridge for `𝒦ⁿ`.** The underlying abelian presheaf of `𝒦ⁿ` read as a presheaf of
`𝒪`-modules is the one underlying `𝒦ⁿ` read as a presheaf of `B`-modules. This is what lets a
statement about `Lπ_!` of the `𝒪`-module be transported to `L_i colim` of the presheaf of
`B`-modules in which the homology of `C_{B/A}` is taken. -/
@[simp]
lemma smallPolynomialAugmentationIdealPowStructureModule_presheaf (n : ℕ) :
    (smallPolynomialAugmentationIdealPowStructureModule A B κ n).presheaf =
      smallPolynomialAugmentationIdealPow A B κ n ⋙
        forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u} := rfl

/-- `CommAlgCat.smallPolynomialAugmentationIdealPowStructureModule_presheaf`, in the spelling
`PresheafOfModules.toPresheaf` that the consumers of [Stacks, Tag 08QJ] use. -/
lemma toPresheaf_obj_smallPolynomialAugmentationIdealPowStructureModule (n : ℕ) :
    (PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B κ)).obj
        (smallPolynomialAugmentationIdealPowStructureModule A B κ n) =
      smallPolynomialAugmentationIdealPow A B κ n ⋙
        forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u} := rfl

/-! ### The inclusions of the filtration -/

/-- **The inclusion `𝒦ᵐ ⊆ 𝒦ⁿ` for `n ≤ m`**, as a map of presheaves of `B`-modules. The library
has only the one-step inclusion `𝒦ⁿ⁺¹ ⊆ 𝒦ⁿ`; this is the same construction at an arbitrary pair
of steps, from the antitonicity of the filtration. -/
def smallPolynomialAugmentationIdealPowOfLE {m n : ℕ} (h : n ≤ m) :
    smallPolynomialAugmentationIdealPow A B κ m ⟶ smallPolynomialAugmentationIdealPow A B κ n :=
  Stacks.submoduleFunctorIncl _ _ _ _ _
    (smallPolynomialAugmentationIdealPowSubmodule_antitone A B κ h)

/-- The inclusion `𝒦ⁿ⁺¹ ⊆ 𝒦ⁿ` of `B`-modules is the one-step case of
`CommAlgCat.smallPolynomialAugmentationIdealPowOfLE`. -/
lemma smallPolynomialAugmentationIdealPowOfLE_succ (n : ℕ) :
    smallPolynomialAugmentationIdealPowOfLE A B κ (Nat.le_succ n) =
      smallPolynomialAugmentationIdealPowIncl A B κ n := rfl

/-- **The inclusion `𝒦ⁿ⁺¹ ⟶ 𝒦ⁿ` of presheaves of `𝒪`-modules.** It is the inclusion of
presheaves of `B`-modules that the library already has, carrying the extra linearity; in
particular the two have the same underlying map of abelian presheaves. -/
def smallPolynomialAugmentationIdealPowStructureIncl (n : ℕ) :
    smallPolynomialAugmentationIdealPowStructureModule A B κ (n + 1) ⟶
      smallPolynomialAugmentationIdealPowStructureModule A B κ n :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (smallPolynomialAugmentationIdealPowIncl A B κ n)
      (forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}))
    (fun _ _ _ => Subtype.ext rfl)

/-- **The inclusion `𝒦ᵐ ⟶ 𝒦ⁿ` of presheaves of `𝒪`-modules, for `n ≤ m`.** -/
def smallPolynomialAugmentationIdealPowStructureOfLE {m n : ℕ} (h : n ≤ m) :
    smallPolynomialAugmentationIdealPowStructureModule A B κ m ⟶
      smallPolynomialAugmentationIdealPowStructureModule A B κ n :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (smallPolynomialAugmentationIdealPowOfLE A B κ h)
      (forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}))
    (fun _ _ _ => Subtype.ext rfl)

/-- **The inclusion `𝒦ⁿ ⟶ Ō` of presheaves of `𝒪`-modules.** -/
def smallPolynomialAugmentationIdealPowStructureι (n : ℕ) :
    smallPolynomialAugmentationIdealPowStructureModule A B κ n ⟶
      smallPolynomialQuotientStructureModule A B κ :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (smallPolynomialAugmentationIdealPowι A B κ n)
      (forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}))
    (fun _ _ _ => rfl)

/-- **The bridge is compatible with the inclusions `𝒦ⁿ⁺¹ ⊆ 𝒦ⁿ`**: the map of abelian presheaves
underlying the inclusion of `𝒪`-modules is the whiskering of the inclusion of `B`-modules. -/
@[simp]
lemma toPresheaf_map_smallPolynomialAugmentationIdealPowStructureIncl (n : ℕ) :
    (PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B κ)).map
        (smallPolynomialAugmentationIdealPowStructureIncl A B κ n) =
      Functor.whiskerRight (smallPolynomialAugmentationIdealPowIncl A B κ n)
        (forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}) := rfl

/-- **The bridge is compatible with the inclusions `𝒦ᵐ ⊆ 𝒦ⁿ`** for `n ≤ m`. -/
@[simp]
lemma toPresheaf_map_smallPolynomialAugmentationIdealPowStructureOfLE {m n : ℕ} (h : n ≤ m) :
    (PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B κ)).map
        (smallPolynomialAugmentationIdealPowStructureOfLE A B κ h) =
      Functor.whiskerRight (smallPolynomialAugmentationIdealPowOfLE A B κ h)
        (forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}) := rfl

/-- **The bridge is compatible with the inclusion `𝒦ⁿ ⊆ Ō`.** -/
@[simp]
lemma toPresheaf_map_smallPolynomialAugmentationIdealPowStructureι (n : ℕ) :
    (PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B κ)).map
        (smallPolynomialAugmentationIdealPowStructureι A B κ n) =
      Functor.whiskerRight (smallPolynomialAugmentationIdealPowι A B κ n)
        (forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}) := rfl

/-! ### The change of coefficients of [Stacks, Tag 08QJ] at `Ō` and at `𝒦ⁿ` -/

attribute [local instance] HasDerivedCategory.standard

section Standard

/-- **`𝒦ⁿ` placed in cohomological degree zero**, on the small model at the cardinal bounding the
standard resolution: the object of `D(Mod(𝒪))` that [Stacks, Tag 08QJ] is stated at. -/
abbrev smallPolynomialAugmentationIdealPowStructureSingle (n : ℕ) :
    DerivedCategory (PresheafOfModules.{u}
      (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B))) :=
  DerivedCategory.Q.obj
    ((HomologicalComplex.single (PresheafOfModules.{u}
      (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B)))
        (ComplexShape.up ℤ) 0).obj
      (smallPolynomialAugmentationIdealPowStructureModule A B
        (standardResolutionVarCardinal A B) n))

/-- **[Stacks, Tag 08QJ] at `𝒦ⁿ`.** For the augmentation `𝒪 ⟶ B̲` on the small model of
`C_{B/A}` at the cardinal bounding the standard resolution, the canonical comparison

`Lπ_!(𝒦ⁿ) ⟶ Lπ_!(𝒦ⁿ ⊗^L_𝒪 B̲)`

is an isomorphism in `D(Ab)`, for `𝒦ⁿ` placed in cohomological degree zero.

Nothing is assumed: this is
`CommAlgCat.isIso_derivedColimitTensorComparison_smallPolynomialAugmentation`, which has both
hypotheses of [Stacks, Tag 08RX] discharged, applied to the `𝒪`-module
`CommAlgCat.smallPolynomialAugmentationIdealPowStructureModule`. Together with
`CommAlgCat.smallPolynomialAugmentationIdealPowStructureModule_presheaf`, which says that this
`𝒪`-module has the same underlying abelian presheaf as the presheaf of `B`-modules `𝒦ⁿ` of
`StacksFrontier.Cotangent.SurjectionSiteAugmentationFiltration`, this is the form in which the
change of coefficients applies to the filtration of `Ō`. -/
theorem isIso_derivedColimitTensorComparison_smallPolynomialAugmentationIdealPow (n : ℕ) :
    IsIso ((Stacks.ChaoticSite.derivedColimitTensorComparison
        (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))).app
      (smallPolynomialAugmentationIdealPowStructureSingle A B n)) :=
  isIso_derivedColimitTensorComparison_smallPolynomialAugmentation A B
    (smallPolynomialAugmentationIdealPowStructureModule A B
      (standardResolutionVarCardinal A B) n)

/-- **[Stacks, Tag 08QJ] at `Ō`.** The same statement for `Ō` itself, which is the `n = 0` step
of the filtration. -/
theorem isIso_derivedColimitTensorComparison_smallPolynomialQuotient :
    IsIso ((Stacks.ChaoticSite.derivedColimitTensorComparison
        (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))).app
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single (PresheafOfModules.{u}
          (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B)))
            (ComplexShape.up ℤ) 0).obj
          (smallPolynomialQuotientStructureModule A B
            (standardResolutionVarCardinal A B))))) :=
  isIso_derivedColimitTensorComparison_smallPolynomialAugmentation A B
    (smallPolynomialQuotientStructureModule A B (standardResolutionVarCardinal A B))

end Standard

end CommAlgCat

end
