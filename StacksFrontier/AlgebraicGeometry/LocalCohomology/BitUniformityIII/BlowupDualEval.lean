module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDual
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupModuleSituation
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.InternalHom

/-!
# Currying on the blowup, and evaluation of `(p^*M)^∨` at the elements of `M`

Let `p : X → Spec(A)` be the blowup of `Spec(A)` in `I` and `M` an `A/Iⁿ`-module, with dual
`(p^*M)^∨ = SheafHom(p^*M, 𝒪_{Yₙ})` (`blowupDual`). The proof of [Stacks, Tag 0GAC] evaluates
sections of `(p^*M)^∨` against the elements of `M`: an element `z ∈ M` gives a global section
`p^*z` of `p^*M`, and pairing with it is a map `e_{p^*z} : (p^*M)^∨ → 𝒪_{Yₙ}` (the `e_{p^*z}` of
the commuting square in that proof). This file builds `e_{p^*z}` from the currying bijection
`Hom(F ⊗ G, H) = Hom(F, SheafHom(G, H))` of [Stacks, Tag 01CN], as the uncurried identity
(the evaluation pairing) composed with `p^*z`, and computes it on sections.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupCurry`: currying on the blowup.
* `Stacks.LocalCohomology.UniformityIII.blowupPairing`: the pairing attached to a morphism into
  an internal Hom, and `blowupTranspose`, the transposed morphism.
* `Stacks.LocalCohomology.UniformityIII.blowupPointSection`: the section `p^*z : 𝒪_X ⟶ p^*M`.
* `Stacks.LocalCohomology.UniformityIII.blowupDualEval`: `e_{p^*z} : (p^*M)^∨ ⟶ 𝒪_{Yₙ}`.
* `Stacks.LocalCohomology.UniformityIII.blowupEvDual`: evaluation of sections of the twisted
  dual `(p^*M)^∨(q)` against the elements of `M`, valued in `I^q/I^{q+n}` (the `evDual` of
  `CanDualSituation`).

## Main results

* `Stacks.LocalCohomology.UniformityIII.blowupPairing_blowupCurry`,
  `blowupCurry_symm_tmul`: currying on local pure tensors.
* `Stacks.LocalCohomology.UniformityIII.blowupDualEval_app`: `e_{p^*z}` is evaluation at `p^*z`
  on sections.
* `Stacks.LocalCohomology.UniformityIII.blowupPointSection_comp`,
  `blowupPointSection_add`, `blowupPointSection_smul`: `p^*z` is natural and linear in `z`.
* `Stacks.LocalCohomology.UniformityIII.blowupDualMap_comp_blowupDualEval`: `e_{p^*z} ∘ D_u =
  e_{p^*(u z)}`.
* `Stacks.LocalCohomology.UniformityIII.blowupDualEval_add`, `blowupDualEval_smul`: `e_{p^*z}`
  is linear in `z`.
* `Stacks.LocalCohomology.UniformityIII.blowupEvDual_whiskerLeft`: the evaluation of the
  twisted dual is natural in the twist (the field `evDual_Hdualtr` of `CanDualSituation`).

## References

* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.RegularSequence (globalSmulCenter)
open Stacks.SheafOfModules.OnSpace (tensorObjTmul)


universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### Currying and the evaluation pairing on the blowup -/

/-- The internal Hom `SheafHom(G, H)` on the blowup. -/
abbrev blowupHom (G H : (blowupScheme I).Modules) : (blowupScheme I).Modules :=
  (Stacks.Algebraization.sheafHomFunctor (blowupScheme I) G).obj H

/-- **Currying** ([Stacks, Tag 01CN]): a morphism `F ⊗ G ⟶ H` is a morphism
`F ⟶ SheafHom(G, H)`. -/
def blowupCurry {F G H : (blowupScheme I).Modules} :
    (F ⊗ G ⟶ H) ≃ (F ⟶ blowupHom I G H) :=
  Stacks.SheafOfModules.tensorHomEquiv (blowupScheme I).toRingedSpace F G H

/-- The pairing `F(U) × G(U) → H(U)` attached to a morphism `F ⟶ SheafHom(G, H)`: a section of
`F` is sent to a local homomorphism `G|_U ⟶ H|_U`, which is evaluated at a section of `G`. -/
abbrev blowupPairing {F G H : (blowupScheme I).Modules} (f : F ⟶ blowupHom I G H)
    (U : (blowupScheme I).Opens) (x : F.val.obj (op U)) (y : G.val.obj (op U)) :
    H.val.obj (op U) :=
  Stacks.PresheafOfModules.InternalHom.pairing (blowupScheme I).sheaf.obj f.val U x y

/-- **The curried morphism pairs as the morphism does on local pure tensors.** -/
theorem blowupPairing_blowupCurry {F G H : (blowupScheme I).Modules} (t : F ⊗ G ⟶ H)
    (U : (blowupScheme I).Opens) (x : F.val.obj (op U)) (y : G.val.obj (op U)) :
    blowupPairing I (blowupCurry I t) U x y =
      (t.val.app (op U)).hom (tensorObjTmul (blowupScheme I).toRingedSpace F G (op U) x y) :=
  Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry (blowupScheme I).toRingedSpace t U x y

/-- **The uncurried morphism on local pure tensors is the pairing.** -/
theorem blowupCurry_symm_tmul {F G H : (blowupScheme I).Modules} (f : F ⟶ blowupHom I G H)
    (U : (blowupScheme I).Opens) (x : F.val.obj (op U)) (y : G.val.obj (op U)) :
    (((blowupCurry I).symm f).val.app (op U)).hom
        (tensorObjTmul (blowupScheme I).toRingedSpace F G (op U) x y) =
      blowupPairing I f U x y := by
  have h := blowupPairing_blowupCurry I ((blowupCurry I).symm f) U x y
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- **The transpose** of a morphism into an internal Hom: `F ⟶ SheafHom(G, H)` gives
`G ⟶ SheafHom(F, H)`, with the same pairing read the other way round. -/
def blowupTranspose {F G H : (blowupScheme I).Modules} (f : F ⟶ blowupHom I G H) :
    G ⟶ blowupHom I F H :=
  ⟨Stacks.PresheafOfModules.InternalHom.transposeHom (blowupScheme I).sheaf.obj f.val⟩

/-- Transposing twice is the identity. -/
theorem blowupTranspose_blowupTranspose {F G H : (blowupScheme I).Modules}
    (f : F ⟶ blowupHom I G H) : blowupTranspose I (blowupTranspose I f) = f :=
  _root_.SheafOfModules.hom_ext
    (Stacks.PresheafOfModules.InternalHom.transposeHom_involutive _ f.val)

/-- The transpose pairs as the morphism does, with the arguments exchanged. -/
theorem blowupPairing_blowupTranspose {F G H : (blowupScheme I).Modules}
    (f : F ⟶ blowupHom I G H) (U : (blowupScheme I).Opens) (y : G.val.obj (op U))
    (x : F.val.obj (op U)) :
    blowupPairing I (blowupTranspose I f) U y x = blowupPairing I f U x y := by
  show Stacks.PresheafOfModules.InternalHom.pairing _ f.val U x
    (G.val.map (𝟙 U).op y) = _
  rw [op_id, G.val.map_id]
  rfl

/-- The transpose on a section, at a slice object `V ⟶ U`: the pairing of the restrictions. -/
theorem blowupTranspose_app_app {F G H : (blowupScheme I).Modules} (f : F ⟶ blowupHom I G H)
    (U : (blowupScheme I).Opens) (y : G.val.obj (op U)) (V : (Over U)ᵒᵖ)
    (x : F.val.obj (op V.unop.left)) :
    ((((blowupTranspose I f).val.app (op U)).hom y).app V).hom x =
      blowupPairing I f V.unop.left x (G.val.map V.unop.hom.op y) :=
  rfl

/-! ### The global sections of `p^*M` attached to elements, and evaluation -/

/-- The structure sheaf `𝒪_X` of the blowup, as an `𝒪_X`-module: the unit of the tensor
product. -/
abbrev blowupUnit : (blowupScheme I).Modules :=
  𝟙_ (blowupScheme I).Modules

/-- `p^*(A~) ≅ 𝒪_X`. -/
def blowupPullbackSelfIso :
    (blowupPullback I).obj (ModuleCat.of A A) ≅ blowupUnit I :=
  (Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).mapIso
      (tildeSelf (R := CommRingCat.of A)) ≪≫
    Scheme.Modules.pullbackUnitIso (Stacks.Blowup.toSpec I)

/-- `M ↦ p^*M` is additive: `M ↦ M~` and the pullback are. -/
instance additive_blowupPullback : (blowupPullback I).Additive :=
  haveI := Stacks.AlgebraicGeometry.TopDegreeBaseChange.additive_tildeFunctor (CommRingCat.of A)
  inferInstanceAs (tilde.functor (CommRingCat.of A) ⋙
    Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).Additive

variable (n : ℕ)

/-- **The global section `p^*z` of `p^*M` attached to `z ∈ M`**, as a morphism `𝒪_X ⟶ p^*M`: the
pullback of `A → M`, `1 ↦ z`. -/
def blowupPointSection (N : ModuleCat.{u} (A ⧸ I ^ n)) (z : resModule I n N) :
    blowupUnit I ⟶ (blowupModPullback I n).obj N :=
  (blowupPullbackSelfIso I).inv ≫ (blowupPullback I).map (resModulePointMap I n N z)

/-- `p^*u` carries the section attached to `z` to the section attached to `u z`. -/
theorem blowupPointSection_comp {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N')
    (z : resModule I n N) :
    blowupPointSection I n N z ≫ (blowupModPullback I n).map f =
      blowupPointSection I n N' (f z) := by
  unfold blowupPointSection
  rw [Category.assoc]
  congr 1
  rw [← resModulePointMap_comp]
  exact ((blowupPullback I).map_comp _ _).symm

/-- The section attached to a sum is the sum of the sections. -/
theorem blowupPointSection_add (N : ModuleCat.{u} (A ⧸ I ^ n)) (z z' : resModule I n N) :
    blowupPointSection I n N (z + z') =
      blowupPointSection I n N z + blowupPointSection I n N z' := by
  unfold blowupPointSection
  rw [resModulePointMap_add, Functor.map_add, Preadditive.comp_add]

/-- **Evaluation at `z`**, `e_{p^*z} : (p^*M)^∨ ⟶ 𝒪_{Yₙ}`: the dual paired with the global section
of `p^*M` attached to `z`. -/
def blowupDualEval (N : ModuleCat.{u} (A ⧸ I ^ n)) (z : resModule I n N) :
    blowupDual I n N ⟶ thickeningSheaf I n :=
  (ρ_ (blowupDual I n N)).inv ≫ (blowupDual I n N ◁ blowupPointSection I n N z) ≫
    (blowupCurry I).symm (𝟙 (blowupDual I n N))

/-- **Evaluation on sections**: `e_{p^*z}` sends a local homomorphism `φ : p^*M|_U ⟶ 𝒪_{Yₙ}|_U` to
its value at the restriction of `p^*z`. -/
theorem blowupDualEval_app (N : ModuleCat.{u} (A ⧸ I ^ n)) (z : resModule I n N)
    (U : (blowupScheme I).Opens) (x : (blowupDual I n N).val.obj (op U)) :
    ((blowupDualEval I n N z).val.app (op U)).hom x =
      blowupPairing I (𝟙 (blowupDual I n N)) U x
        (((blowupPointSection I n N z).val.app (op U)).hom
          (Stacks.SheafOfModules.OnSpace.unitSection (blowupScheme I).toRingedSpace (op U) 1)) := by
  show (((blowupCurry I).symm (𝟙 (blowupDual I n N))).val.app (op U)).hom
    (((blowupDual I n N ◁ blowupPointSection I n N z).val.app (op U)).hom
      ((((ρ_ (blowupDual I n N)).inv).val.app (op U)).hom x)) = _
  refine (congrArg (fun w => (((blowupCurry I).symm (𝟙 (blowupDual I n N))).val.app (op U)).hom
    (((blowupDual I n N ◁ blowupPointSection I n N z).val.app (op U)).hom w))
    (Stacks.SheafOfModules.OnSpace.rightUnitor_inv_apply (blowupScheme I).toRingedSpace
      (blowupDual I n N) (op U) x)).trans ?_
  refine (congrArg (fun w => (((blowupCurry I).symm (𝟙 (blowupDual I n N))).val.app (op U)).hom w)
    (Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul (blowupScheme I).toRingedSpace
      (blowupDual I n N) (blowupPointSection I n N z) (op U) x _)).trans ?_
  exact blowupCurry_symm_tmul I (𝟙 (blowupDual I n N)) U x _

/-- **Evaluation is natural in `M`**: `D_u = (p^*u)^∨` followed by evaluation at `z` is evaluation
at `u z`. -/
theorem blowupDualMap_comp_blowupDualEval {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N')
    (z : resModule I n N) :
    blowupDualMap I n f ≫ blowupDualEval I n N z = blowupDualEval I n N' (f z) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨U⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show ((blowupDualEval I n N z).val.app (op U)).hom
      (((blowupDualMap I n f).val.app (op U)).hom x) =
    ((blowupDualEval I n N' _).val.app (op U)).hom x
  refine (blowupDualEval_app I n N z U _).trans ?_
  refine Eq.trans ?_ (blowupDualEval_app I n N' (f z) U x).symm
  refine Eq.trans ?_ (congrArg (fun ψ : blowupUnit I ⟶ (blowupModPullback I n).obj N' =>
    blowupPairing I (𝟙 (blowupDual I n N')) U x ((ψ.val.app (op U)).hom
      (Stacks.SheafOfModules.OnSpace.unitSection (blowupScheme I).toRingedSpace (op U) 1)))
    (blowupPointSection_comp I n f z))
  rfl

/-! ### Scalars -/

/-- **`p^*` takes the scalar `a` to multiplication by the pulled back function `a`.** -/
theorem blowupPullback_map_smul {M M' : ModuleCat.{u} A} (f : M ⟶ M') (a : A) :
    (blowupPullback I).map (a • f) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫
        (blowupPullback I).map f := by
  let : Linear A (blowupScheme I).Modules :=
    modulesLinear A (Stacks.Blowup.blowUpOver I)
  let : Linear A (Spec (CommRingCat.of A)).Modules :=
    modulesLinear A (Stacks.AlgebraicGeometry.TopDegreeBaseChange.specBase A)
  have : (tilde.functor (CommRingCat.of A)).Linear A :=
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.linear_tildeFunctor A
  have : (Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).Linear A :=
    over_pullback_linear A (Stacks.AlgebraicGeometry.TopDegreeBaseChange.toSpecBase A
      (Stacks.Blowup.blowUpOver I))
  have : (blowupPullback I).Linear A := inferInstanceAs ((tilde.functor (CommRingCat.of A) ⋙
    Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).Linear A)
  rw [Functor.map_smul]
  rfl

/-- The section attached to `a • z` is the section attached to `z`, multiplied by `a`. -/
theorem blowupPointSection_smul (N : ModuleCat.{u} (A ⧸ I ^ n)) (a : A) (z : resModule I n N) :
    blowupPointSection I n N (a • z) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app (blowupUnit I) ≫
        blowupPointSection I n N z := by
  unfold blowupPointSection
  rw [resModulePointMap_smul, blowupPullback_map_smul, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).naturality
    (blowupPullbackSelfIso I).inv

/-- **Multiplication by a global function commutes with tensoring on the left**: on `E ⊗ F` it
is `E` tensored with multiplication on `F`. -/
theorem whiskerLeft_globalSmulCenter_app (E F : (blowupScheme I).Modules)
    (r : Γ(blowupScheme I, ⊤)) :
    E ◁ (globalSmulCenter (blowupScheme I) r).app F =
      (globalSmulCenter (blowupScheme I) r).app (E ⊗ F) := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext (blowupScheme I).toRingedSpace
    (f := E ◁ (globalSmulCenter (blowupScheme I) r).app F)
    (g := (globalSmulCenter (blowupScheme I) r).app (E ⊗ F)) fun U e s => ?_
  refine (Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul (blowupScheme I).toRingedSpace E
    ((globalSmulCenter (blowupScheme I) r).app F) U e s).trans ?_
  refine (Stacks.SheafOfModules.OnSpace.tensorObjTmul_smul_right (blowupScheme I).toRingedSpace
    E F U ((blowupScheme I).presheaf.map U.unop.leTop.op r) e s).trans ?_
  exact (smul_tensorObjTmul (blowupScheme I).toRingedSpace E F U
    ((blowupScheme I).presheaf.map U.unop.leTop.op r) e s).symm

/-- **Evaluation at `a • z` is evaluation at `z` followed by multiplication by `a`.** -/
theorem blowupDualEval_smul (N : ModuleCat.{u} (A ⧸ I ^ n)) (a : A) (z : resModule I n N) :
    blowupDualEval I n N (a • z) =
      blowupDualEval I n N z ≫
        (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app (thickeningSheaf I n) := by
  refine Eq.trans ?_ ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).naturality
    (blowupDualEval I n N z)).symm
  show _ = (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app (blowupDual I n N) ≫
    blowupDualEval I n N z
  unfold blowupDualEval
  have h := (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).naturality
    (ρ_ (blowupDual I n N)).inv
  rw [blowupPointSection_smul, MonoidalCategory.whiskerLeft_comp,
    whiskerLeft_globalSmulCenter_app, Category.assoc, reassoc_of% h]

/-- Evaluation is additive in the element. -/
theorem blowupDualEval_add (N : ModuleCat.{u} (A ⧸ I ^ n)) (z z' : resModule I n N) :
    blowupDualEval I n N (z + z') = blowupDualEval I n N z + blowupDualEval I n N z' := by
  unfold blowupDualEval
  rw [← Preadditive.comp_add, ← Preadditive.add_comp]
  congr 2
  rw [blowupPointSection_add]
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext (blowupScheme I).toRingedSpace fun U e s => ?_
  refine (Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul (blowupScheme I).toRingedSpace _
    _ U e s).trans ?_
  refine (congrArg (Stacks.SheafOfModules.OnSpace.tensorObjSection
    (blowupScheme I).toRingedSpace _ _ U) (TensorProduct.tmul_add e _ _)).trans ?_
  refine (map_add _ _ _).trans ?_
  exact congrArg₂ (· + ·)
    (Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul (blowupScheme I).toRingedSpace _ _ U e s).symm
    (Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul (blowupScheme I).toRingedSpace _ _ U e s).symm

/-! ### The evaluation dictionary of the twisted dual -/

section Dictionary

variable [IsNoetherianRing A]

/-- **Evaluating a section of `(p^*M)^∨(q)` against the elements of `M`**, for `q ≥ q₀` with `q₀`
having the defining property of `q(S)`: `σ` and `z ∈ M` give the section `e_{p^*z}(σ)` of
`𝒪_{Yₙ}(q)`, read in `I^q/I^{q+n}` through Tag 0GA7(2). This is the `evDual` of
`Stacks.LocalCohomology.UniformityIII.CanDualSituation`. -/
def blowupEvDual (m : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀) {q : ℕ} (hq : q₀ ≤ q)
    (N : ModuleCat.{u} (A ⧸ I ^ (m + 1))) :
    blowupHmod I 0 (blowupDual I (m + 1) N ⊗ blowupTwistInt I q) →ₗ[A]
      (resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) :=
  LinearMap.mk₂' A A
    (fun σ z => (LinearEquiv.ofBijective (cdivMod I m q) (bijective_cdivMod_of_le I h hq)).symm
      (blowupHmodMap I 0 (blowupDualEval I (m + 1) N z ▷ blowupTwistInt I q) σ))
    (fun σ σ' z => by rw [map_add, map_add])
    (fun a σ z => by rw [map_smul, map_smul])
    (fun σ z z' => by
      rw [blowupDualEval_add, add_whiskerRight_blowupTwistInt, blowupHmodMap_add, map_add])
    (fun a σ z => by
      rw [blowupDualEval_smul, MonoidalCategory.comp_whiskerRight, blowupHmodMap_comp_apply,
        globalSmulCenter_app_whiskerRight, blowupHmodMap_zero_globalSmulCenter, map_smul])

/-- The defining formula of `blowupEvDual`. -/
theorem blowupEvDual_apply (m : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀) {q : ℕ} (hq : q₀ ≤ q)
    (N : ModuleCat.{u} (A ⧸ I ^ (m + 1)))
    (σ : blowupHmod I 0 (blowupDual I (m + 1) N ⊗ blowupTwistInt I q))
    (z : resModule I (m + 1) N) :
    blowupEvDual I m h hq N σ z =
      (LinearEquiv.ofBijective (cdivMod I m q) (bijective_cdivMod_of_le I h hq)).symm
        (blowupHmodMap I 0 (blowupDualEval I (m + 1) N z ▷ blowupTwistInt I q) σ) :=
  rfl

/-- **The evaluation of the twisted dual is natural in the twist** (the field `evDual_Hdualtr`
of `CanDualSituation`): twisting down and then evaluating is evaluating and then mapping
`I^q/I^{q+n} → I^{q'}/I^{q'+n}`. -/
theorem blowupEvDual_whiskerLeft (m : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀) {q q' : ℕ}
    (hq : q₀ ≤ q) (hq' : q₀ ≤ q') (hle : q' ≤ q) (h' : (q' : ℤ) ≤ q)
    (N : ModuleCat.{u} (A ⧸ I ^ (m + 1)))
    (σ : blowupHmod I 0 (blowupDual I (m + 1) N ⊗ blowupTwistInt I q)) :
    blowupEvDual I m h hq' N
        (blowupHmodMap I 0 (blowupDual I (m + 1) N ◁ blowupTwistLE I h') σ) =
      (powQuotLe I hle).comp (blowupEvDual I m h hq N σ) := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply, blowupEvDual_apply, blowupEvDual_apply,
    ← blowupHmodMap_whiskerRight_whiskerLeft_apply]
  obtain ⟨w, hw⟩ := (bijective_cdivMod_of_le I h hq).2
    (blowupHmodMap I 0 (blowupDualEval I (m + 1) N z ▷ blowupTwistInt I q) σ)
  rw [← hw, blowupHmodMap_whiskerLeft_cdivMod I m h' hle,
    LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.ofBijective_symm_apply_apply]

end Dictionary

end Stacks.LocalCohomology.UniformityIII

end
