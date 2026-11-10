module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDualEval

/-!
# The canonical map `can : p^*(M^∨) → (p^*M)^∨` on the blowup

Let `p : X → Spec(A)` be the blowup of `Spec(A)` in `I`, `Yₙ` the `n`-th thickening of the
exceptional divisor and `M` an `A/Iⁿ`-module, with `p^*M = 𝒪_{Yₙ} ⊗ p^*(M~)`
(`thickeningPullback`) and `(p^*M)^∨ = SheafHom(p^*(M~), 𝒪_{Yₙ})` (`blowupDual`). This file
constructs the canonical map of [Stacks, Tag 0GAB]

`can : p^*(M^∨) ⟶ (p^*M)^∨`,

proves that it is natural in `M` and an isomorphism at a finite free module, and deduces the last
clause of Tag 0GAB: for an `(A, n, c)`-module `M` the kernel and the cokernel of `can` are killed
by every `a ∈ I^c`.

## The construction

`can` is pinned down by its evaluations: for every `z ∈ M` the square of the proof of
[Stacks, Tag 0GAC]

`e_{p^*z} ∘ can = (p^*(M^∨) --p^*e_z--> p^*(A/Iⁿ) = 𝒪_{Yₙ})`

commutes (`blowupDualEval_comp_blowupCan`), and the evaluations `e_{p^*z}` are jointly faithful
on maps into `(p^*M)^∨` (`blowupDual_hom_ext`). Existence is the general construction
`blowupDualLift`: an `A`-linear family `z ↦ e z` of maps `E ⟶ 𝒪_{Yₙ}` defines, through
`p^* ⊣ Γ(X, -)`, a map `p^*(M~) ⟶ SheafHom(E, 𝒪_{Yₙ})`, whose transpose is a map
`E ⟶ (p^*M)^∨` with evaluations `e z` (`blowupDualLift_comp_blowupDualEval`).

Naturality, invertibility at `A/Iⁿ` and the `A`-linearity of the dual are then all checked
after evaluation; invertibility at `(A/Iⁿ)^{⊕r}` follows by additivity, and the annihilation of
the kernel and cokernel is the diagram chase of `IsANCModule.exists_finFree_factorization`, as
in the source.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupDualLift`: the map into `(p^*M)^∨` with prescribed
  evaluations.
* `Stacks.LocalCohomology.UniformityIII.blowupCan`: **`can : p^*(M^∨) ⟶ (p^*M)^∨`**, and
  `blowupCanNatTrans`, the same as a natural transformation of functors
  `(Mod(A/Iⁿ))ᵒᵖ ⥤ Mod(𝒪_X)`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.blowupDual_hom_ext`: maps into `(p^*M)^∨` are determined
  by their evaluations.
* `Stacks.LocalCohomology.UniformityIII.blowupDualEval_comp_blowupCan`: `e_{p^*z} ∘ can = p^*e_z`.
* `Stacks.LocalCohomology.UniformityIII.blowupCan_naturality`: `can` is functorial in `M`.
* `Stacks.LocalCohomology.UniformityIII.isIso_blowupCan_finFree`: `can` is an isomorphism at a
  finite free `A/Iⁿ`-module.
* `Stacks.LocalCohomology.UniformityIII.globalSmulCenter_app_kernel_blowupCan` and
  `globalSmulCenter_app_cokernel_blowupCan`: for an `(A, n, c)`-module and `a ∈ I^c`,
  multiplication by `a` is zero on the kernel and on the cokernel of `can`.

## References

* [Stacks Project, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.RegularSequence (globalSmulCenter)

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

variable {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ)

/-! ### Maps into an internal Hom are determined by their pairings -/

/-- **Maps into an internal Hom are determined by their pairings.** -/
theorem blowupHom_ext {F G H : (blowupScheme I).Modules} {f g : F ⟶ blowupHom I G H}
    (h : ∀ (U : (blowupScheme I).Opens) (x : F.val.obj (op U)) (y : G.val.obj (op U)),
      blowupPairing I f U x y = blowupPairing I g U x y) : f = g := by
  rw [← (blowupCurry I).apply_symm_apply f, ← (blowupCurry I).apply_symm_apply g]
  congr 1
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext (blowupScheme I).toRingedSpace
    fun U x y => ?_
  exact (blowupCurry_symm_tmul I f U.unop x y).trans
    ((h U.unop x y).trans (blowupCurry_symm_tmul I g U.unop x y).symm)

/-- Maps `𝒪_X ⟶ SheafHom(G, H)` are determined by their pairings, with the sections of `𝒪_X`
read as functions. -/
theorem blowupHom_ext_unit {G H : (blowupScheme I).Modules} {f g : blowupUnit I ⟶ blowupHom I G H}
    (h : ∀ (U : (blowupScheme I).Opens) (r : Γ(blowupScheme I, U)) (y : Γ(G, U)),
      blowupPairing I f U
          (Stacks.SheafOfModules.OnSpace.unitSection (blowupScheme I).toRingedSpace (op U) r) y =
        blowupPairing I g U
          (Stacks.SheafOfModules.OnSpace.unitSection (blowupScheme I).toRingedSpace (op U) r) y) :
    f = g :=
  blowupHom_ext I fun U r y => h U r y

/-- **The map `𝒪_X ⟶ SheafHom(E, H)` attached to `φ : E ⟶ H`**: the curry of
`𝒪_X ⊗ E ≅ E --φ--> H`. -/
def blowupHomOfUnit {E H : (blowupScheme I).Modules} (φ : E ⟶ H) :
    blowupUnit I ⟶ blowupHom I E H :=
  blowupCurry I ((λ_ E).hom ≫ φ)

/-- The map attached to `φ` pairs a function `r` and a section `x` to `φ(r • x)`. -/
theorem blowupPairing_blowupHomOfUnit {E H : (blowupScheme I).Modules} (φ : E ⟶ H)
    (U : (blowupScheme I).Opens) (r : Γ(blowupScheme I, U)) (x : Γ(E, U)) :
    blowupPairing I (blowupHomOfUnit I φ) U
        (Stacks.SheafOfModules.OnSpace.unitSection (blowupScheme I).toRingedSpace (op U) r) x =
      (φ.val.app (op U)).hom (r • x) := by
  refine (blowupPairing_blowupCurry I ((λ_ E).hom ≫ φ) U _ x).trans ?_
  exact congrArg (φ.val.app (op U)).hom
    (Stacks.SheafOfModules.OnSpace.leftUnitor_tmul (blowupScheme I).toRingedSpace E (op U) r x)

/-- `φ ↦ (𝒪_X ⟶ SheafHom(E, H))` is injective. -/
theorem blowupHomOfUnit_injective {E H : (blowupScheme I).Modules} :
    Function.Injective (blowupHomOfUnit I (E := E) (H := H)) := fun _ _ h =>
  ((λ_ E).cancel_iso_hom_left _ _).1 ((blowupCurry I).injective h)

/-- `φ ↦ (𝒪_X ⟶ SheafHom(E, H))` is additive. -/
theorem blowupHomOfUnit_add {E H : (blowupScheme I).Modules} (φ ψ : E ⟶ H) :
    blowupHomOfUnit I (φ + ψ) = blowupHomOfUnit I φ + blowupHomOfUnit I ψ :=
  blowupHom_ext_unit I fun U r x => (blowupPairing_blowupHomOfUnit I (φ + ψ) U r x).trans
    (congrArg₂ (· + ·) (blowupPairing_blowupHomOfUnit I φ U r x).symm
      (blowupPairing_blowupHomOfUnit I ψ U r x).symm)

/-- `φ ↦ (𝒪_X ⟶ SheafHom(E, H))` carries precomposition with multiplication by a global function
to precomposition with the same multiplication on `𝒪_X`. -/
theorem blowupHomOfUnit_globalSmulCenter {E H : (blowupScheme I).Modules} (φ : E ⟶ H)
    (s : Γ(blowupScheme I, ⊤)) :
    blowupHomOfUnit I ((globalSmulCenter (blowupScheme I) s).app E ≫ φ) =
      (globalSmulCenter (blowupScheme I) s).app (blowupUnit I) ≫ blowupHomOfUnit I φ := by
  refine blowupHom_ext_unit I fun U r x => ?_
  refine (blowupPairing_blowupHomOfUnit I _ U r x).trans ?_
  refine (congrArg (φ.val.app (op U)).hom
    (mul_smul ((blowupScheme I).presheaf.map U.leTop.op s) r x)).symm.trans ?_
  exact (blowupPairing_blowupHomOfUnit I φ U
    ((blowupScheme I).presheaf.map U.leTop.op s * r) x).symm

/-! ### Global sections as maps out of the structure sheaf -/

/-- The global section `1` of `𝒪_X`, as an element of the `A`-module `Γ(X, 𝒪_X)`: the value at
`1` of the map `A → Γ(X, 𝒪_X)` that `p^*(A~) ≅ 𝒪_X` corresponds to under `p^* ⊣ Γ(X, -)`. -/
def blowupUnitSection : (blowupΓmod I).obj (blowupUnit I) :=
  ((blowupPullbackAdjunction I).homEquiv (ModuleCat.of A A) _ (blowupPullbackSelfIso I).hom).hom
    (1 : A)

/-- The global section of `H` attached to a map `𝒪_X ⟶ H`: the image of `1`. -/
def blowupUnitHomSection {H : (blowupScheme I).Modules} (g : blowupUnit I ⟶ H) :
    (blowupΓmod I).obj H :=
  (blowupΓmod I).map g (blowupUnitSection I)

/-- Under `p^* ⊣ Γ(X, -)`, the map `A → Γ(X, H)` attached to `p^*(A~) ≅ 𝒪_X --g--> H` sends `1` to
the section attached to `g`. -/
theorem blowupPullbackAdjunction_homEquiv_selfIso_apply_one {H : (blowupScheme I).Modules}
    (g : blowupUnit I ⟶ H) :
    ((blowupPullbackAdjunction I).homEquiv (ModuleCat.of A A) H
      ((blowupPullbackSelfIso I).hom ≫ g)).hom (1 : A) = blowupUnitHomSection I g := by
  unfold blowupUnitHomSection blowupUnitSection
  rw [blowupPullbackAdjunction_homEquiv_naturality_right]
  rfl

/-- The section attached to a sum of maps is the sum of the sections. -/
theorem blowupUnitHomSection_add {H : (blowupScheme I).Modules} (g g' : blowupUnit I ⟶ H) :
    blowupUnitHomSection I (g + g') = blowupUnitHomSection I g + blowupUnitHomSection I g' :=
  rfl

/-- `blowupUnitHomSection` carries multiplication by the pulled back function `a` to the scalar
`a`. -/
theorem blowupUnitHomSection_globalSmulCenter {H : (blowupScheme I).Modules}
    (g : blowupUnit I ⟶ H) (a : A) :
    blowupUnitHomSection I
        ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app (blowupUnit I) ≫ g) =
      a • blowupUnitHomSection I g :=
  (congrArg ((blowupΓmod I).map g)
      (blowupΓmod_map_globalSmulCenter I a _ (blowupUnitSection I))).trans
    (((blowupΓmod I).map g).hom.map_smul a (blowupUnitSection I))

/-! ### Maps into the dual with prescribed evaluations -/

section Lift

variable {N : ModuleCat.{u} (A ⧸ I ^ n)}

/-- `A → M`, `1 ↦ z`, sends `1` to `z`. -/
theorem resModulePointMap_apply_one (z : resModule I n N) :
    (resModulePointMap I n N z).hom (1 : A) = z := by
  change (Ideal.Quotient.mk (I ^ n) (1 : A)) • (z : (N : Type u)) = z
  rw [map_one, one_smul]

/-- `p^*(1 ↦ z) = p^*(A~) ≅ 𝒪_X --p^*z--> p^*M`. -/
theorem blowupPullback_map_resModulePointMap (z : resModule I n N) :
    (blowupPullback I).map (resModulePointMap I n N z) =
      (blowupPullbackSelfIso I).hom ≫ blowupPointSection I n N z := by
  unfold blowupPointSection
  exact (Iso.hom_inv_id_assoc _ _).symm

/-- **Maps out of `p^*M` are determined on the sections `p^*z`**, `z ∈ M`, by `p^* ⊣ Γ(X, -)`. -/
theorem blowupModPullback_hom_ext {H : (blowupScheme I).Modules}
    {φ ψ : (blowupModPullback I n).obj N ⟶ H}
    (h : ∀ z : resModule I n N, blowupPointSection I n N z ≫ φ = blowupPointSection I n N z ≫ ψ) :
    φ = ψ := by
  apply ((blowupPullbackAdjunction I).homEquiv _ _).injective
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  have key : ∀ χ : (blowupModPullback I n).obj N ⟶ H,
      ((blowupPullbackAdjunction I).homEquiv _ _ χ).hom z =
        ((blowupPullbackAdjunction I).homEquiv _ _
          ((blowupPullbackSelfIso I).hom ≫ blowupPointSection I n N z ≫ χ)).hom 1 := by
    intro χ
    rw [← Category.assoc, ← blowupPullback_map_resModulePointMap,
      blowupPullbackAdjunction_homEquiv_naturality_left]
    exact (congrArg ((blowupPullbackAdjunction I).homEquiv _ _ χ).hom
      (resModulePointMap_apply_one I n z)).symm
  rw [key, key, h]

/-- The section `p^*z` evaluated at a function `r` is `r` times its value at `1`. -/
theorem blowupPointSection_app_unitSection (z : resModule I n N) (U : (blowupScheme I).Opens)
    (r : Γ(blowupScheme I, U)) :
    ((blowupPointSection I n N z).val.app (op U)).hom
        (Stacks.SheafOfModules.OnSpace.unitSection (blowupScheme I).toRingedSpace (op U) r) =
      r • (show Γ((blowupModPullback I n).obj N, U) from
        ((blowupPointSection I n N z).val.app (op U)).hom
          (Stacks.SheafOfModules.OnSpace.unitSection (blowupScheme I).toRingedSpace (op U) 1)) :=
  (congrArg ((blowupPointSection I n N z).val.app (op U)).hom (mul_one r).symm).trans
    (((blowupPointSection I n N z).val.app (op U)).hom.map_smul r _)

/-- **The transpose of a map into the dual, on the section `p^*z`**, is the map attached to the
composite with the evaluation `e_{p^*z}`. -/
theorem blowupPointSection_comp_blowupTranspose {E : (blowupScheme I).Modules}
    (f : E ⟶ blowupDual I n N) (z : resModule I n N) :
    blowupPointSection I n N z ≫ blowupTranspose I f =
      blowupHomOfUnit I (f ≫ blowupDualEval I n N z) := by
  refine blowupHom_ext_unit I fun U r x => ?_
  let fx : Γ(blowupDual I n N, U) := (f.val.app (op U)).hom x
  let y : Γ((blowupModPullback I n).obj N, U) := ((blowupPointSection I n N z).val.app (op U)).hom
    (Stacks.SheafOfModules.OnSpace.unitSection (blowupScheme I).toRingedSpace (op U) 1)
  have h1 : blowupPairing I (blowupPointSection I n N z ≫ blowupTranspose I f) U
      (Stacks.SheafOfModules.OnSpace.unitSection (blowupScheme I).toRingedSpace (op U) r) x =
      blowupPairing I (𝟙 (blowupDual I n N)) U fx (r • y) :=
    (blowupPairing_blowupTranspose I f U _ x).trans
      (congrArg (blowupPairing I f U x) (blowupPointSection_app_unitSection I n z U r))
  have h2 : blowupPairing I (𝟙 (blowupDual I n N)) U fx (r • y) =
      r • (show Γ(thickeningSheaf I n, U) from
        blowupPairing I (𝟙 (blowupDual I n N)) U fx y) :=
    Stacks.PresheafOfModules.InternalHom.pairing_smul_right (blowupScheme I).sheaf.obj
      (𝟙 (blowupDual I n N) : blowupDual I n N ⟶ blowupDual I n N).val U r fx y
  have h3 : blowupPairing I (𝟙 (blowupDual I n N)) U fx y =
      ((blowupDualEval I n N z).val.app (op U)).hom fx :=
    (blowupDualEval_app I n N z U fx).symm
  have h4 : blowupPairing I (blowupHomOfUnit I (f ≫ blowupDualEval I n N z)) U
      (Stacks.SheafOfModules.OnSpace.unitSection (blowupScheme I).toRingedSpace (op U) r) x =
      ((blowupDualEval I n N z).val.app (op U)).hom (r • fx) :=
    (blowupPairing_blowupHomOfUnit I _ U r x).trans
      (congrArg ((blowupDualEval I n N z).val.app (op U)).hom
        ((f.val.app (op U)).hom.map_smul r x))
  rw [h1, h2, h3, h4]
  exact (((blowupDualEval I n N z).val.app (op U)).hom.map_smul r fx).symm

/-- **Maps into `(p^*M)^∨` are determined by their evaluations** `e_{p^*z}`, `z ∈ M`: their
transposes agree on every section `p^*z` (`blowupPointSection_comp_blowupTranspose`), hence agree
(`blowupModPullback_hom_ext`). -/
theorem blowupDual_hom_ext {E : (blowupScheme I).Modules} {f g : E ⟶ blowupDual I n N}
    (h : ∀ z : resModule I n N, f ≫ blowupDualEval I n N z = g ≫ blowupDualEval I n N z) :
    f = g := by
  rw [← blowupTranspose_blowupTranspose I f, ← blowupTranspose_blowupTranspose I g]
  congr 1
  refine blowupModPullback_hom_ext I n fun z => ?_
  rw [blowupPointSection_comp_blowupTranspose, blowupPointSection_comp_blowupTranspose, h]

/-- The `A`-linear map `M → Γ(X, SheafHom(E, 𝒪_{Yₙ}))` attached to an `A`-linear family
`z ↦ e z` of maps `E ⟶ 𝒪_{Yₙ}`. -/
def blowupLiftSections {E : (blowupScheme I).Modules}
    (e : resModule I n N → (E ⟶ thickeningSheaf I n))
    (he_add : ∀ z z', e (z + z') = e z + e z')
    (he_smul : ∀ (a : A) (z : resModule I n N),
      e (a • z) = (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app E ≫ e z) :
    resModule I n N →ₗ[A] (blowupΓmod I).obj (blowupHom I E (thickeningSheaf I n)) where
  toFun z := blowupUnitHomSection I (blowupHomOfUnit I (e z))
  map_add' z z' := by rw [he_add, blowupHomOfUnit_add, blowupUnitHomSection_add]
  map_smul' a z := by
    rw [he_smul, blowupHomOfUnit_globalSmulCenter, blowupUnitHomSection_globalSmulCenter]
    rfl

/-- `blowupLiftSections` as a morphism of `A`-modules. -/
abbrev blowupLiftSectionsHom {E : (blowupScheme I).Modules}
    (e : resModule I n N → (E ⟶ thickeningSheaf I n))
    (he_add : ∀ z z', e (z + z') = e z + e z')
    (he_smul : ∀ (a : A) (z : resModule I n N),
      e (a • z) = (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app E ≫ e z) :
    resModule I n N ⟶ (blowupΓmod I).obj (blowupHom I E (thickeningSheaf I n)) :=
  ModuleCat.ofHom (X := resModule I n N)
    (Y := (blowupΓmod I).obj (blowupHom I E (thickeningSheaf I n)))
    (blowupLiftSections I n e he_add he_smul)

/-- **The map into `(p^*M)^∨` with prescribed evaluations**: the transpose of the map
`p^*M ⟶ SheafHom(E, 𝒪_{Yₙ})` that `blowupLiftSections` defines under `p^* ⊣ Γ(X, -)`. -/
def blowupDualLift {E : (blowupScheme I).Modules}
    (e : resModule I n N → (E ⟶ thickeningSheaf I n))
    (he_add : ∀ z z', e (z + z') = e z + e z')
    (he_smul : ∀ (a : A) (z : resModule I n N),
      e (a • z) = (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app E ≫ e z) :
    E ⟶ blowupDual I n N :=
  blowupTranspose I (((blowupPullbackAdjunction I).homEquiv _ _).symm
    (blowupLiftSectionsHom I n e he_add he_smul))

/-- On the section `p^*z`, the adjoint map is the map attached to `e z`. -/
theorem blowupPointSection_comp_homEquiv_symm {E : (blowupScheme I).Modules}
    (e : resModule I n N → (E ⟶ thickeningSheaf I n))
    (he_add : ∀ z z', e (z + z') = e z + e z')
    (he_smul : ∀ (a : A) (z : resModule I n N),
      e (a • z) = (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app E ≫ e z)
    (z : resModule I n N) :
    blowupPointSection I n N z ≫ ((blowupPullbackAdjunction I).homEquiv _ _).symm
        (blowupLiftSectionsHom I n e he_add he_smul) =
      blowupHomOfUnit I (e z) := by
  have h : (blowupPullback I).map (resModulePointMap I n N z) ≫
      ((blowupPullbackAdjunction I).homEquiv _ _).symm
        (blowupLiftSectionsHom I n e he_add he_smul) =
      (blowupPullbackSelfIso I).hom ≫ blowupHomOfUnit I (e z) := by
    apply ((blowupPullbackAdjunction I).homEquiv _ _).injective
    rw [blowupPullbackAdjunction_homEquiv_naturality_left, Equiv.apply_symm_apply]
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change blowupLiftSections I n e he_add he_smul ((resModulePointMap I n N z).hom 1) =
      ((blowupPullbackAdjunction I).homEquiv _ _
        ((blowupPullbackSelfIso I).hom ≫ blowupHomOfUnit I (e z))).hom (1 : A)
    rw [resModulePointMap_apply_one, blowupPullbackAdjunction_homEquiv_selfIso_apply_one]
    rfl
  rw [blowupPullback_map_resModulePointMap, Category.assoc] at h
  exact (cancel_epi _).1 h

/-- **The evaluations of `blowupDualLift` are the prescribed maps.** -/
theorem blowupDualLift_comp_blowupDualEval {E : (blowupScheme I).Modules}
    (e : resModule I n N → (E ⟶ thickeningSheaf I n))
    (he_add : ∀ z z', e (z + z') = e z + e z')
    (he_smul : ∀ (a : A) (z : resModule I n N),
      e (a • z) = (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app E ≫ e z)
    (z : resModule I n N) :
    blowupDualLift I n e he_add he_smul ≫ blowupDualEval I n N z = e z := by
  have h := blowupPointSection_comp_blowupTranspose I n (blowupDualLift I n e he_add he_smul) z
  rw [blowupDualLift, blowupTranspose_blowupTranspose,
    blowupPointSection_comp_homEquiv_symm I n e he_add he_smul] at h
  exact (blowupHomOfUnit_injective I h).symm

end Lift

/-! ### The canonical map -/

section Can

/-- The dual `M^∨ = Hom_{A/Iⁿ}(M, A/Iⁿ)`, as an object of `Mod(A/Iⁿ)`. -/
abbrev modDual (N : ModuleCat.{u} (A ⧸ I ^ n)) : ModuleCat.{u} (A ⧸ I ^ n) :=
  ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) N)

/-- `p^*(e_z) : p^*(M^∨) ⟶ p^*(A/Iⁿ) = 𝒪_{Yₙ}`, the pullback of evaluation at `z`. -/
abbrev blowupCanEval (N : ModuleCat.{u} (A ⧸ I ^ n)) (z : resModule I n N) :
    (thickeningPullback I n).obj (modDual I n N) ⟶ thickeningSheaf I n :=
  (thickeningPullback I n).map (dualEvalAt I N z) ≫ (thickeningPullbackUnitIso I n).hom

/-- `z ↦ p^*(e_z)` is additive. -/
theorem blowupCanEval_add (N : ModuleCat.{u} (A ⧸ I ^ n)) (z z' : resModule I n N) :
    blowupCanEval I n N (z + z') = blowupCanEval I n N z + blowupCanEval I n N z' :=
  (congrArg (fun φ => (thickeningPullback I n).map φ ≫ (thickeningPullbackUnitIso I n).hom)
    (dualEvalAt_add I N z z')).trans
    ((congrArg (· ≫ (thickeningPullbackUnitIso I n).hom)
      (CategoryTheory.Functor.map_add (F := thickeningPullback I n) (f := dualEvalAt I N z)
        (g := dualEvalAt I N z'))).trans
      (Preadditive.add_comp _ _ _ _ _ _))

/-- `z ↦ p^*(e_z)` is `A`-linear. -/
theorem blowupCanEval_smul (N : ModuleCat.{u} (A ⧸ I ^ n)) (a : A) (z : resModule I n N) :
    blowupCanEval I n N (a • z) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫ blowupCanEval I n N z :=
  (congrArg (fun φ => (thickeningPullback I n).map φ ≫ (thickeningPullbackUnitIso I n).hom)
    (dualEvalAt_smul I N (Ideal.Quotient.mk (I ^ n) a) z)).trans
    ((congrArg (· ≫ (thickeningPullbackUnitIso I n).hom)
      (thickeningPullback_map_smul I n (dualEvalAt I N z) a)).trans (Category.assoc _ _ _))

/-- **The canonical map `can : p^*(M^∨) ⟶ (p^*M)^∨` of [Stacks, Tag 0GAB]**: the map whose
evaluation at every `z ∈ M` is `p^*(e_z)` (`blowupDualEval_comp_blowupCan`). -/
def blowupCan (N : ModuleCat.{u} (A ⧸ I ^ n)) :
    (thickeningPullback I n).obj (modDual I n N) ⟶ blowupDual I n N :=
  blowupDualLift I n (blowupCanEval I n N) (blowupCanEval_add I n N) (blowupCanEval_smul I n N)

/-- **The commuting square of the proof of Tag 0GAC**: `e_{p^*z} ∘ can = p^*(e_z)`; evaluating
`can(t)` against `z` is evaluating `t` against `z`. -/
theorem blowupDualEval_comp_blowupCan (N : ModuleCat.{u} (A ⧸ I ^ n)) (z : resModule I n N) :
    blowupCan I n N ≫ blowupDualEval I n N z =
      (thickeningPullback I n).map (dualEvalAt I N z) ≫ (thickeningPullbackUnitIso I n).hom :=
  blowupDualLift_comp_blowupDualEval I n _ _ _ z

/-- **`can` is functorial in `M`** ([Stacks, Tag 0GAB]): for `u : M ⟶ M'`,
`can_M ∘ p^*(u^∨) = (p^*u)^∨ ∘ can_{M'}`. -/
theorem blowupCan_naturality {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N') :
    (thickeningPullback I n).map ((moduleDual (A ⧸ I ^ n)).map f.op) ≫ blowupCan I n N =
      blowupCan I n N' ≫ blowupDualMap I n f := by
  refine blowupDual_hom_ext I n fun z => ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun g => (thickeningPullback I n).map ((moduleDual (A ⧸ I ^ n)).map f.op) ≫ g)
    (blowupDualEval_comp_blowupCan I n N z)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun g => blowupCan I n N' ≫ g)
    (blowupDualMap_comp_blowupDualEval I n f z)).symm
  refine Eq.trans ?_ (blowupDualEval_comp_blowupCan I n N' (f z)).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg (· ≫ (thickeningPullbackUnitIso I n).hom) ?_
  refine ((thickeningPullback I n).map_comp _ _).symm.trans ?_
  exact congrArg (thickeningPullback I n).map (ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- `(p^*(a • 𝟙))^∨` is multiplication by `a` on `(p^*M)^∨`. -/
theorem blowupDualMap_smul_id (N : ModuleCat.{u} (A ⧸ I ^ n)) (a : A) :
    blowupDualMap I n (Ideal.Quotient.mk (I ^ n) a • 𝟙 N) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app (blowupDual I n N) :=
  blowupDual_hom_ext I n fun z =>
    (blowupDualMap_comp_blowupDualEval I n _ z).trans ((blowupDualEval_smul I n N a z).trans
      ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).naturality _))

/-- `D_u` is additive in `u`. -/
theorem blowupDualMap_add {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f g : N ⟶ N') :
    blowupDualMap I n (f + g) = blowupDualMap I n f + blowupDualMap I n g :=
  blowupDual_hom_ext I n fun z =>
    (blowupDualMap_comp_blowupDualEval I n (f + g) z).trans
      ((blowupDualEval_add I n N' (f z) (g z)).trans
        ((congrArg₂ (· + ·) (blowupDualMap_comp_blowupDualEval I n f z).symm
          (blowupDualMap_comp_blowupDualEval I n g z).symm).trans
          (Preadditive.add_comp _ _ _ _ _ _).symm))

/-- The dual functor `M ↦ (p^*M)^∨` is additive. -/
instance additive_blowupDualFunctor : (blowupDualFunctor I n).Additive where
  map_add {_ _ f g} := blowupDualMap_add I n f.unop g.unop

/-- **`can` as a natural transformation** `M ↦ p^*(M^∨)` to `M ↦ (p^*M)^∨` of functors
`(Mod(A/Iⁿ))ᵒᵖ ⥤ Mod(𝒪_X)`. -/
def blowupCanNatTrans :
    moduleDual (A ⧸ I ^ n) ⋙ thickeningPullback I n ⟶ blowupDualFunctor I n where
  app N := blowupCan I n N.unop
  naturality _ _ f := blowupCan_naturality I n f.unop

/-- The component of `blowupCanNatTrans` at `M` is `can` at `M`. -/
theorem blowupCanNatTrans_app (N : ModuleCat.{u} (A ⧸ I ^ n)) :
    (blowupCanNatTrans I n).app (op N) = blowupCan I n N :=
  rfl

/-- **`can` is an isomorphism at `A/Iⁿ`.** The inverse is `e_{p^*1}` followed by the inverse of
`p^*(e_1) : p^*((A/Iⁿ)^∨) ⟶ 𝒪_{Yₙ}`, which is invertible as `e_1 : (A/Iⁿ)^∨ → A/Iⁿ` is. -/
theorem isIso_blowupCan_self :
    IsIso (blowupCan I n (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n))) := by
  let R := ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n)
  let one : resModule I n R := (1 : A ⧸ I ^ n)
  have hiso : IsIso (dualEvalAt I R one) :=
    (LinearMap.ringLmapEquivSelf (A ⧸ I ^ n) (A ⧸ I ^ n) (A ⧸ I ^ n)).toModuleIso.isIso_hom
  have : IsIso (blowupCanEval I n R one) := by
    unfold blowupCanEval
    infer_instance
  refine ⟨blowupDualEval I n R one ≫ inv (blowupCanEval I n R one), ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ inv (blowupCanEval I n R one))
        (blowupDualEval_comp_blowupCan I n R one)).trans
        (IsIso.hom_inv_id _))
  · refine blowupDual_hom_ext I n fun z => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (show A ⧸ I ^ n from z)
    have hz : a • one = z := (mul_one _).trans ha
    have key : blowupDualEval I n R one ≫ inv (blowupCanEval I n R one) ≫
        blowupCanEval I n R z = blowupDualEval I n R z := by
      calc blowupDualEval I n R one ≫ inv (blowupCanEval I n R one) ≫ blowupCanEval I n R z
          = blowupDualEval I n R one ≫ inv (blowupCanEval I n R one) ≫
              (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫
                blowupCanEval I n R one := by rw [← hz, blowupCanEval_smul]
        _ = blowupDualEval I n R one ≫
              (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫
                inv (blowupCanEval I n R one) ≫ blowupCanEval I n R one := by
            rw [CatCenter.naturality_assoc]
        _ = blowupDualEval I n R one ≫
              (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ := by
            rw [IsIso.inv_hom_id, Category.comp_id]
        _ = blowupDualEval I n R z := by rw [← blowupDualEval_smul, hz]
    rw [Category.id_comp, Category.assoc, Category.assoc, blowupDualEval_comp_blowupCan]
    exact key

/-- **`can` is an isomorphism at a finite free `A/Iⁿ`-module** ([Stacks, Tag 0GAB]): it is one at
`A/Iⁿ` and both sides are additive in `M`. -/
theorem isIso_blowupCan_finFree (r : ℕ) :
    IsIso (blowupCan I n (finFreeModule (A ⧸ I ^ n) r)) := by
  have : IsIso ((blowupCanNatTrans I n).app (op (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n)))) :=
    isIso_blowupCan_self I n
  exact isIso_app_of_sum_id (blowupCanNatTrans I n)
    (fun i => (finFreeIncl (A ⧸ I ^ n) r i).op) (fun i => (finFreeProj (A ⧸ I ^ n) r i).op)
    (by
      refine Quiver.Hom.unop_inj ?_
      rw [unop_sum, unop_id]
      exact (Finset.sum_congr rfl fun i _ => rfl).trans
        (sum_finFreeProj_comp_finFreeIncl (A ⧸ I ^ n) r))

end Can

/-! ### The kernel and the cokernel of `can` are killed by `I^c` -/

section Annihilation

variable {I n} {c : ℕ}

/-- For an `(A, n, c)`-module `M` and `a ∈ I^c`, multiplication by `a` on `M` factors, in the
opposite category, through a finite free module at which `can` is an isomorphism. -/
private theorem exists_blowupCan_factorization {M : ModuleCat.{u} (A ⧸ I ^ n)}
    (hM : IsANCModule I n c M) {a : A} (ha : a ∈ I ^ c) :
    ∃ (r : ℕ) (α : M ⟶ finFreeModule (A ⧸ I ^ n) r) (β : finFreeModule (A ⧸ I ^ n) r ⟶ M),
      IsIso ((blowupCanNatTrans I n).app (op (finFreeModule (A ⧸ I ^ n) r))) ∧
        β.op ≫ α.op = ((Ideal.Quotient.mk (I ^ n) a) • 𝟙 M).op := by
  obtain ⟨r, α, β, hαβ⟩ := hM.exists_finFree_factorization
    (Ideal.mem_map_of_mem (Ideal.Quotient.mk (I ^ n)) ha)
  exact ⟨r, α, β, isIso_blowupCan_finFree I n r, by rw [← op_comp, hαβ]⟩

/-- **The kernel of `can` is killed by `I^c`** ([Stacks, Tag 0GAB]): for an `(A, n, c)`-module
`M` and `a ∈ I^c`, multiplication by `a` is zero on `ker(can_M)`. The source's argument:
`a : M → M` factors through a finite free module, at which `can` is an isomorphism. -/
theorem globalSmulCenter_app_kernel_blowupCan {M : ModuleCat.{u} (A ⧸ I ^ n)}
    (hM : IsANCModule I n c M) {a : A} (ha : a ∈ I ^ c) :
    (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app (kernel (blowupCan I n M)) = 0 := by
  obtain ⟨r, α, β, _, e⟩ := exists_blowupCan_factorization hM ha
  have h := kernel_ι_comp_map_eq_zero (blowupCanNatTrans I n) β.op α.op
  have h2 : (moduleDual (A ⧸ I ^ n) ⋙ thickeningPullback I n).map
      ((Ideal.Quotient.mk (I ^ n) a) • 𝟙 M).op =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ :=
    (congrArg (thickeningPullback I n).map
      (moduleDual_map_op_smul_id _ M (Ideal.Quotient.mk (I ^ n) a))).trans
      ((thickeningPullback_map_smul I n (𝟙 _) a).trans
        ((congrArg (_ ≫ ·) ((thickeningPullback I n).map_id _)).trans (Category.comp_id _)))
  rw [e, h2] at h
  rw [← cancel_mono (kernel.ι (blowupCan I n M)), zero_comp]
  exact ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).naturality
    (kernel.ι (blowupCan I n M))).symm.trans h

/-- **The cokernel of `can` is killed by `I^c`** ([Stacks, Tag 0GAB]). -/
theorem globalSmulCenter_app_cokernel_blowupCan {M : ModuleCat.{u} (A ⧸ I ^ n)}
    (hM : IsANCModule I n c M) {a : A} (ha : a ∈ I ^ c) :
    (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app
      (cokernel (blowupCan I n M)) = 0 := by
  obtain ⟨r, α, β, _, e⟩ := exists_blowupCan_factorization hM ha
  have h := map_comp_cokernel_π_eq_zero (blowupCanNatTrans I n) β.op α.op
  have h2 : (blowupDualFunctor I n).map ((Ideal.Quotient.mk (I ^ n) a) • 𝟙 M).op =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app (blowupDual I n M) :=
    blowupDualMap_smul_id I n M a
  rw [e, h2] at h
  rw [← cancel_epi (cokernel.π (blowupCan I n M)), comp_zero]
  exact ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).naturality
    (cokernel.π (blowupCan I n M))).trans h

end Annihilation

end Stacks.LocalCohomology.UniformityIII

end
