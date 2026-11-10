module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricSquareFiltration
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact
public import StacksFrontier.LinearAlgebra.SymmetricPower.TensorSquareCauchy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafStalkMaps

/-!
# The sequence `0 → ⋀²ℰ ⊗ ⋀²ℱ → Sym²(ℰ ⊗ ℱ) → Sym²ℰ ⊗ Sym²ℱ → 0` of sheaves of modules

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and `ℰ`, `ℱ` sheaves of
`O♯`-modules with chosen symmetric and exterior algebras, and a chosen symmetric algebra of
`ℰ ⊗ ℱ`. The proof of the multiplicativity of the second Adams operation (Stacks Tag 0FEJ) uses
the short exact sequence

`0 → ⋀²ℰ ⊗ ⋀²ℱ --α--> Sym²(ℰ ⊗ ℱ) --φ--> Sym²ℰ ⊗ Sym²ℱ → 0`,

`φ((e ⊗ f)(e' ⊗ f')) = ee' ⊗ ff'` and
`α((e ∧ e') ⊗ (f ∧ f')) = (e ⊗ f)(e' ⊗ f') - (e ⊗ f')(e' ⊗ f)`.
**This file constructs `α` and `φ` and proves the sequence short exact** whenever the stalks of
`ℰ` and `ℱ` are free (`shortExact_cauchy`). No hypothesis on `2` is made.

## Construction

Neither map is given by a universal property of sheaves of graded algebras. Each is the descent
along an epimorphism of a map built from the monoidal structure of the sheafified tensor product
(`SheafOfModules.TensorStalkMaps`):

* `φ` descends `π = (sq_ℰ ⊗ sq_ℱ) ∘ middleFour : (ℰ ⊗ ℱ) ⊗ (ℰ ⊗ ℱ) ⟶ Sym²ℰ ⊗ Sym²ℱ` along the
  square map `sq : (ℰ ⊗ ℱ) ⊗ (ℰ ⊗ ℱ) ⟶ Sym²(ℰ ⊗ ℱ)`;
* `α` descends `(ℰ ⊗ ℰ) ⊗ (ℱ ⊗ ℱ) ⟶ Sym²(ℰ ⊗ ℱ)`,
  `(e ⊗ e') ⊗ (f ⊗ f') ↦ (e ⊗ f)(e' ⊗ f') - (e ⊗ f')(e' ⊗ f)`, along the tensor product of the two
  exterior square maps.

That the kernels are killed, and every property of the resulting sequence, is read on stalks,
where the maps are the module-level `SymPow.cauchyφ` and `SymPow.cauchyα` of
`StacksFrontier.LinearAlgebra.SymmetricPower.TensorSquareCauchy`.

## Main results

* `SheafOfModules.SymSquareTensor.sq`, `wsq`: the square maps `ℳ ⊗ ℳ ⟶ Sym² ℳ` and
  `ℳ ⊗ ℳ ⟶ ⋀² ℳ`, with their stalks `SymPow.sqMul` and `SymPow.wedgeMul`.
* `SheafOfModules.SymSquareTensor.cauchyφSheaf`, `cauchyαSheaf`: the two maps, with their stalks.
* `SheafOfModules.SymSquareTensor.shortExact_cauchy`: **the sequence is short exact.**

## References

* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace SheafOfModules.SymSquareTensor

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-- The category of sheaves of `O♯`-modules, at the spelling `toRingCat` of the sheaf of rings. -/
abbrev Mods (Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}) :=
  SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)

/-- The tensor product of two sheaves of modules, typed at the spelling `toRingCat` of the sheaf of
rings so that the preadditive and abelian structures are found. -/
noncomputable abbrev tens (A B : Mods Osharp) : Mods Osharp :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A).obj B

/-- Post-composing `map f g` with `congr e₁ e₂` is `map u v` after `congr a₁ a₂`, when this holds
on each factor. -/
private theorem congr_map_apply_eq {R M N M' N' M₀ N₀ P Q : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup M₀]
    [AddCommGroup N₀] [AddCommGroup P] [AddCommGroup Q] [Module R M] [Module R N] [Module R M']
    [Module R N'] [Module R M₀] [Module R N₀] [Module R P] [Module R Q]
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (e₁ : M' ≃ₗ[R] P) (e₂ : N' ≃ₗ[R] Q)
    (u : M₀ →ₗ[R] P) (v : N₀ →ₗ[R] Q) (a₁ : M ≃ₗ[R] M₀) (a₂ : N ≃ₗ[R] N₀)
    (hu : ∀ m, e₁ (f m) = u (a₁ m)) (hv : ∀ n, e₂ (g n) = v (a₂ n)) (w : M ⊗[R] N) :
    TensorProduct.congr e₁ e₂ (TensorProduct.map f g w) =
      TensorProduct.map u v (TensorProduct.congr a₁ a₂ w) := by
  have : (TensorProduct.congr e₁ e₂).toLinearMap ∘ₗ TensorProduct.map f g =
      TensorProduct.map u v ∘ₗ (TensorProduct.congr a₁ a₂).toLinearMap :=
    TensorProduct.ext' fun a b => by simp [hu, hv]
  exact DFunLike.congr_fun this w

section Square

variable {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (ι : M ⟶ A.piece 1) (hA : GradedAlgebra.IsSymmetricAlgebra A ι)

/-- The composite `𝟙 ℳ ≫ 0 : ℳ ⟶ ℳ` is zero. -/
theorem hqpSq : 𝟙 M ≫ (0 : M ⟶ M) = 0 := Limits.comp_zero

/-- The multiplication `ℳ ⊗ Sym¹ ℳ ⟶ Sym² ℳ`: the first map of the complex of Tag 01CJ for the
presentation `ℳ --id--> ℳ --0--> ℳ`. -/
abbrev mulOne := (SymPresentation.symComplex ι ι hA hA (𝟙 M) 0 (hqpSq (M := M)) 1).f

/-- **The square map `ℳ ⊗ ℳ ⟶ Sym² ℳ`**, `m ⊗ m' ↦ m · m'`. -/
def sq : tens M M ⟶ A.piece ((1 + 1 : ℕ) : ℤ) :=
  Stacks.Duality.tensorLeftHom M ι ≫ mulOne ι hA

/-- **The stalk of the square map is `SymPow.sqMul id`.** -/
theorem symmetricPowerStalkEquiv_stalkMapL_sq (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp M M).presheaf x)) :
    symmetricPowerStalkEquiv A ι hA (1 + 1) x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (sq ι hA)) z) =
      SymPow.sqMul LinearMap.id (PresheafOfModules.tensorSheafStalkEquiv Osharp M M x z) := by
  refine Eq.trans (congrArg (symmetricPowerStalkEquiv A ι hA (1 + 1) x)
    (SymSquareFiltration.stalkMapL_comp _ _ x z)) ?_
  refine (SymPresentation.symmetricPowerStalkEquiv_symComplex_f ι ι hA hA (𝟙 M) 0
    (hqpSq (M := M)) 1 x _).trans ?_
  have h1 := Stacks.Duality.tensorSheafStalkEquiv_stalkMapL_tensorLeft M ι x z
  have key : (TensorProduct.congr (LinearEquiv.refl ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x))
        (symmetricPowerStalkEquiv A ι hA 1 x)).toLinearMap ∘ₗ
        LinearMap.lTensor ↑(TopCat.Presheaf.stalk M.val.presheaf x)
          (PresheafOfModules.stalkMapL x ι.val) =
      LinearMap.lTensor ↑(TopCat.Presheaf.stalk M.val.presheaf x) (SymPow.ιOne _ _) := by
    refine TensorProduct.ext' fun a b => ?_
    exact congrArg (fun y => a ⊗ₜ y)
      (SymSquareFiltration.symmetricPowerStalkEquiv_stalkMapL_generator ι hA x b)
  have h2 : SymPresentation.symTensorStalkEquiv ι hA 1 x
      (PresheafOfModules.stalkMapL x (SymPresentation.valHom (Stacks.Duality.tensorLeftHom M ι))
        z) =
      LinearMap.lTensor _ (SymPow.ιOne _ _)
        (PresheafOfModules.tensorSheafStalkEquiv Osharp M M x z) :=
    (congrArg (TensorProduct.congr (LinearEquiv.refl _ _)
      (symmetricPowerStalkEquiv A ι hA 1 x)) h1).trans (DFunLike.congr_fun key _)
  refine (congrArg (SymPow.symMulMap 1 (PresheafOfModules.stalkMapL x
    (SymPresentation.valHom (𝟙 M)))) h2).trans ?_
  exact congrArg (fun φ => SymPow.symMulMap 1 φ (LinearMap.lTensor _ (SymPow.ιOne _ _)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp M M x z)))
    (SymSquareFiltration.stalkMapL_id_eq x)

/-- The square map is an epimorphism. -/
theorem epi_sq : Epi (sq ι hA) := by
  refine (SymPresentation.epi_iff_surjective_stalkMapL _).2 fun x t => ?_
  obtain ⟨w, hw⟩ := SymPow.sqMul_id_surjective (symmetricPowerStalkEquiv A ι hA (1 + 1) x t)
  refine ⟨(PresheafOfModules.tensorSheafStalkEquiv Osharp M M x).symm w,
    (symmetricPowerStalkEquiv A ι hA (1 + 1) x).injective ?_⟩
  refine (symmetricPowerStalkEquiv_stalkMapL_sq ι hA x _).trans ?_
  exact (congrArg (SymPow.sqMul LinearMap.id)
    ((PresheafOfModules.tensorSheafStalkEquiv Osharp M M x).apply_symm_apply w)).trans hw

end Square

section Wedge

variable {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (κ : M ⟶ A.piece 1) (hA : GradedAlgebra.IsExteriorAlgebra A κ)

/-- The exterior generator on the germ of a local section. -/
theorem exteriorPowerStalkEquiv_germ_generator (x : ↥X) (U : Opens ↥X) (hU : x ∈ U)
    (s : M.val.obj (op U)) :
    exteriorPowerStalkEquiv A κ hA 1 x
        (TopCat.Presheaf.germ (A.piece 1).val.presheaf U x hU (κ.val.app (op U) s)) =
      SymPow.ιOneExt _ _ (TopCat.Presheaf.germ M.val.presheaf U x hU s) := by
  have h := exteriorPowerStalkEquiv_germ_homogeneousProd A κ hA 1 x U hU (fun _ => s)
  have h2 : A.toPresheafGradedAlgebra.homogeneousProd (op U) 1 (fun _ => κ.val.app (op U) s) =
      κ.val.app (op U) s :=
    SymSquareFiltration.homogeneousProd_one A.toPresheafGradedAlgebra (op U) _
  refine Eq.trans ?_ (h.trans ?_)
  · exact congrArg (fun z => exteriorPowerStalkEquiv A κ hA 1 x
      (TopCat.Presheaf.germ (A.piece ((1 : ℕ) : ℤ)).val.presheaf U x hU z)) h2.symm
  · refine Subtype.ext ?_
    simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, SymPow.ιOneExt]

/-- The stalk of the exterior generator `M ⟶ ⋀¹ M` is the generator `Mₓ → ⋀¹ Mₓ`. -/
theorem exteriorPowerStalkEquiv_stalkMapL_generator (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    exteriorPowerStalkEquiv A κ hA 1 x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom κ) t) =
      SymPow.ιOneExt _ _ t := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf t
  exact (congrArg (exteriorPowerStalkEquiv A κ hA 1 x)
    (PresheafOfModules.stalkMapL_germ x (SymPresentation.valHom κ) U hU s)).trans
    (exteriorPowerStalkEquiv_germ_generator κ hA x U hU s)

/-- The composite `𝟙 ℳ ≫ 0 : ℳ ⟶ ℳ` is zero. -/
alias hqpWedge := hqpSq

/-- The exterior multiplication `ℳ ⊗ ⋀¹ ℳ ⟶ ⋀² ℳ` of Tag 01CJ. -/
abbrev wedgeOne := (ExtPresentation.extComplex κ κ hA hA 0 (𝟙 M) (hqpWedge (M := M)) 1).f

/-- **The exterior square map `ℳ ⊗ ℳ ⟶ ⋀² ℳ`**, `m ⊗ m' ↦ m ∧ m'`. -/
def wsq : tens M M ⟶
    A.piece ((1 + 1 : ℕ) : ℤ) :=
  Stacks.Duality.tensorLeftHom M κ ≫ wedgeOne κ hA

/-- **The stalk of the exterior square map is `SymPow.wedgeMul`.** -/
theorem exteriorPowerStalkEquiv_stalkMapL_wsq (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp M M).presheaf x)) :
    exteriorPowerStalkEquiv A κ hA (1 + 1) x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (wsq κ hA)) z) =
      SymPow.wedgeMul (PresheafOfModules.tensorSheafStalkEquiv Osharp M M x z) := by
  refine Eq.trans (congrArg (exteriorPowerStalkEquiv A κ hA (1 + 1) x)
    (SymSquareFiltration.stalkMapL_comp _ _ x z)) ?_
  refine (ExtPresentation.exteriorPowerStalkEquiv_extComplex_f κ κ hA hA 0 (𝟙 M)
    (hqpWedge (M := M)) 1 x _).trans ?_
  have h1 := Stacks.Duality.tensorSheafStalkEquiv_stalkMapL_tensorLeft M κ x z
  have key : (TensorProduct.congr (LinearEquiv.refl ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x))
        (exteriorPowerStalkEquiv A κ hA 1 x)).toLinearMap ∘ₗ
        LinearMap.lTensor ↑(TopCat.Presheaf.stalk M.val.presheaf x)
          (PresheafOfModules.stalkMapL x κ.val) =
      LinearMap.lTensor ↑(TopCat.Presheaf.stalk M.val.presheaf x) (SymPow.ιOneExt _ _) := by
    refine TensorProduct.ext' fun a b => ?_
    exact congrArg (fun y => a ⊗ₜ y) (exteriorPowerStalkEquiv_stalkMapL_generator κ hA x b)
  have h2 : ExtPresentation.extTensorStalkEquiv κ hA 1 x
      (PresheafOfModules.stalkMapL x (SymPresentation.valHom (Stacks.Duality.tensorLeftHom M κ))
        z) =
      LinearMap.lTensor _ (SymPow.ιOneExt _ _)
        (PresheafOfModules.tensorSheafStalkEquiv Osharp M M x z) :=
    (congrArg (TensorProduct.congr (LinearEquiv.refl _ _)
      (exteriorPowerStalkEquiv A κ hA 1 x)) h1).trans (DFunLike.congr_fun key _)
  refine (congrArg (ExtPow.beta 1 (PresheafOfModules.stalkMapL x
    (SymPresentation.valHom (𝟙 M)))) h2).trans ?_
  exact congrArg (fun φ => ExtPow.beta 1 φ (LinearMap.lTensor _ (SymPow.ιOneExt _ _)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp M M x z)))
    (SymSquareFiltration.stalkMapL_id_eq x)

/-- The exterior square map is an epimorphism. -/
theorem epi_wsq : Epi (wsq κ hA) := by
  refine (SymPresentation.epi_iff_surjective_stalkMapL _).2 fun x t => ?_
  obtain ⟨w, hw⟩ := SymPow.wedgeMul_surjective (exteriorPowerStalkEquiv A κ hA (1 + 1) x t)
  refine ⟨(PresheafOfModules.tensorSheafStalkEquiv Osharp M M x).symm w,
    (exteriorPowerStalkEquiv A κ hA (1 + 1) x).injective ?_⟩
  refine (exteriorPowerStalkEquiv_stalkMapL_wsq κ hA x _).trans ?_
  exact (congrArg SymPow.wedgeMul
    ((PresheafOfModules.tensorSheafStalkEquiv Osharp M M x).apply_symm_apply w)).trans hw

end Wedge

/-! ### Module-level lemmas -/

/-- `Sym² h` commutes with the square maps: `Sym² h (sqMul u) = sqMul ((h ⊗ h) u)`. -/
theorem _root_.SymPow.symMap_sqMul {S N P : Type*} [CommRing S] [AddCommGroup N] [Module S N]
    [AddCommGroup P] [Module S P] (h : N →ₗ[S] P) (u : N ⊗[S] N) :
    SymPow.symMap (1 + 1) h (SymPow.sqMul LinearMap.id u) =
      SymPow.sqMul LinearMap.id (TensorProduct.map h h u) := by
  have hlin : SymPow.symMap (1 + 1) h ∘ₗ SymPow.sqMul LinearMap.id =
      SymPow.sqMul LinearMap.id ∘ₗ TensorProduct.map h h := by
    refine TensorProduct.ext' fun e e' => Subtype.ext ?_
    change SymPow.symAlgMap h (SymmetricAlgebra.ι S N e * SymmetricAlgebra.ι S N e') =
      SymmetricAlgebra.ι S P (h e) * SymmetricAlgebra.ι S P (h e')
    rw [map_mul, SymPow.symAlgMap_ι, SymPow.symAlgMap_ι]
  exact DFunLike.congr_fun hlin u

section Stalk

variable {M N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The stalk of a difference of morphisms is the difference of their stalks. -/
theorem stalkMapL_sub (a b : M ⟶ N) (x : ↥X) (t : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    PresheafOfModules.stalkMapL x (SymPresentation.valHom (a - b)) t =
      PresheafOfModules.stalkMapL x (SymPresentation.valHom a) t -
        PresheafOfModules.stalkMapL x (SymPresentation.valHom b) t := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf t
  refine (PresheafOfModules.stalkMapL_germ x _ U hU s).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· - ·) (PresheafOfModules.stalkMapL_germ x _ U hU s).symm
    (PresheafOfModules.stalkMapL_germ x _ U hU s).symm)
  refine Eq.trans ?_ (map_sub _ _ _)
  rfl

/-- A composite of morphisms of sheaves of modules vanishes once it vanishes on every stalk. -/
theorem comp_eq_zero_of_stalkMapL {P : SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)} (p : M ⟶ N) (φ : N ⟶ P)
    (h : ∀ (x : ↥X) (t : ↑(TopCat.Presheaf.stalk M.val.presheaf x)),
      PresheafOfModules.stalkMapL x (SymPresentation.valHom φ)
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom p) t) = 0) :
    p ≫ φ = 0 :=
  SymSquareFiltration.eq_of_stalkMapL_eq _ _ fun x t =>
    (SymSquareFiltration.stalkMapL_comp p φ x t).trans
      ((h x t).trans (SymSquareFiltration.stalkMapL_zero x t).symm)

/-- If `p ≫ φ = Φ`, then on every stalk the stalk of `φ` after that of `p` is the stalk of `Φ`. -/
theorem stalkMapL_of_comp_eq {P : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X)
    Osharp)} (p : M ⟶ N) (φ : N ⟶ P) (Φ : M ⟶ P) (h : p ≫ φ = Φ) (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    PresheafOfModules.stalkMapL x (SymPresentation.valHom φ)
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom p) t) =
      PresheafOfModules.stalkMapL x (SymPresentation.valHom Φ) t :=
  (SymSquareFiltration.stalkMapL_comp p φ x t).symm.trans
    (congrArg (fun ψ : M ⟶ P => PresheafOfModules.stalkMapL x (SymPresentation.valHom ψ) t) h)

/-- On every stalk, `p` vanishes on the image of the stalk of `kernel.ι p`. -/
theorem stalkMapL_kernelι (p : M ⟶ N) (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (kernel p).val.presheaf x)) :
    PresheafOfModules.stalkMapL x (SymPresentation.valHom p)
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (kernel.ι p)) z) = 0 :=
  (SymSquareFiltration.stalkMapL_comp (kernel.ι p) p x z).symm.trans
    ((congrArg (fun φ : kernel p ⟶ N => PresheafOfModules.stalkMapL x (SymPresentation.valHom φ) z)
      (kernel.condition p)).trans (SymSquareFiltration.stalkMapL_zero x z))

end Stalk

/-! ### The Cauchy sequence of sheaves -/

section Cauchy



open SheafOfModules.TensorStalkMaps

variable {E F : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {AE AF AW BE BF : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (ιE : E ⟶ AE.piece 1) (hE : GradedAlgebra.IsSymmetricAlgebra AE ιE)
  (ιF : F ⟶ AF.piece 1) (hF : GradedAlgebra.IsSymmetricAlgebra AF ιF)
  (ιW : ((tens E F)) ⟶ AW.piece 1) (hW : GradedAlgebra.IsSymmetricAlgebra AW ιW)
  (κE : E ⟶ BE.piece 1) (hBE : GradedAlgebra.IsExteriorAlgebra BE κE)
  (κF : F ⟶ BF.piece 1) (hBF : GradedAlgebra.IsExteriorAlgebra BF κF)

/-- The stalk of `tensorHom f g`, read through `congr e₁ e₂` on the target, is `map u v` of the
stalk of the source, when `f` and `g` satisfy this on their stalks. -/
private theorem congr_tensorSheafStalkEquiv_stalkMapL_tensorHom {A A' B B' : Mods Osharp}
    (f : A ⟶ A') (g : B ⟶ B') (x : ↥X) {P Q P₀ Q₀ : Type*} [AddCommGroup P] [AddCommGroup Q]
    [AddCommGroup P₀] [AddCommGroup Q₀] [Module ↑(TopCat.Presheaf.stalk Osharp.obj x) P]
    [Module ↑(TopCat.Presheaf.stalk Osharp.obj x) Q]
    [Module ↑(TopCat.Presheaf.stalk Osharp.obj x) P₀]
    [Module ↑(TopCat.Presheaf.stalk Osharp.obj x) Q₀]
    (e₁ : ↑(TopCat.Presheaf.stalk A'.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)] P)
    (e₂ : ↑(TopCat.Presheaf.stalk B'.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)] Q)
    (u : P₀ →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)] P)
    (v : Q₀ →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)] Q)
    (a₁ : ↑(TopCat.Presheaf.stalk A.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)] P₀)
    (a₂ : ↑(TopCat.Presheaf.stalk B.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)] Q₀)
    (hu : ∀ a, e₁ (PresheafOfModules.stalkMapL x f.val a) = u (a₁ a))
    (hv : ∀ b, e₂ (PresheafOfModules.stalkMapL x g.val b) = v (a₂ b))
    (y : ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp A B).presheaf x)) :
    TensorProduct.congr e₁ e₂ (PresheafOfModules.tensorSheafStalkEquiv Osharp A' B' x
        (PresheafOfModules.stalkMapL x (tensorHom f g).val y)) =
      TensorProduct.map u v (TensorProduct.congr a₁ a₂
        (PresheafOfModules.tensorSheafStalkEquiv Osharp A B x y)) :=
  (congrArg (TensorProduct.congr e₁ e₂) (tensorSheafStalkEquiv_stalkMapL_tensorHom f g x y)).trans
    (congr_map_apply_eq _ _ e₁ e₂ u v a₁ a₂ hu hv _)

/-- The stalk of `Sym²(ℰ ⊗ ℱ)`, as `Sym²(ℰₓ ⊗ ℱₓ)`. -/
def symWStalk (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (AW.piece ((1 + 1 : ℕ) : ℤ)).val.presheaf x) ≃ₗ[
      ↑(TopCat.Presheaf.stalk Osharp.obj x)]
      SymPow.symmetricPower (1 + 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
        (↑(TopCat.Presheaf.stalk E.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
          ↑(TopCat.Presheaf.stalk F.val.presheaf x)) :=
  (symmetricPowerStalkEquiv AW ιW hW (1 + 1) x).trans
    (SymPow.symmetricPowerCongr (1 + 1) (PresheafOfModules.tensorSheafStalkEquiv Osharp E F x))

/-- The stalk of `Sym² ℰ ⊗ Sym² ℱ`. -/
def symSymStalk (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp (AE.piece ((1 + 1 : ℕ) : ℤ))
      (AF.piece ((1 + 1 : ℕ) : ℤ))).presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      SymPow.symmetricPower (1 + 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk E.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        SymPow.symmetricPower (1 + 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
  (PresheafOfModules.tensorSheafStalkEquiv Osharp _ _ x).trans
    (TensorProduct.congr (symmetricPowerStalkEquiv AE ιE hE (1 + 1) x)
      (symmetricPowerStalkEquiv AF ιF hF (1 + 1) x))

/-- The stalk of `⋀² ℰ ⊗ ⋀² ℱ`. -/
def extExtStalk (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp (BE.piece ((1 + 1 : ℕ) : ℤ))
      (BF.piece ((1 + 1 : ℕ) : ℤ))).presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(1 + 1) ↑(TopCat.Presheaf.stalk E.val.presheaf x)
        ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(1 + 1)
          ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
  (PresheafOfModules.tensorSheafStalkEquiv Osharp _ _ x).trans
    (TensorProduct.congr (exteriorPowerStalkEquiv BE κE hBE (1 + 1) x)
      (exteriorPowerStalkEquiv BF κF hBF (1 + 1) x))

/-- The square map of `ℰ ⊗ ℱ`, read on stalks. -/
theorem symWStalk_stalkMapL_sq (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp ((tens E F)) ((tens E F))).presheaf x)) :
    symWStalk ιW hW x (PresheafOfModules.stalkMapL x (SymPresentation.valHom (sq ιW hW)) t) =
      SymPow.sqMul LinearMap.id (tensorTensorStalkEquiv E F E F x t) :=
  (congrArg (SymPow.symmetricPowerCongr (1 + 1)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp E F x))
    (symmetricPowerStalkEquiv_stalkMapL_sq ιW hW x t)).trans
    (SymPow.symMap_sqMul _ _)

/-- `π : (ℰ ⊗ ℱ) ⊗ (ℰ ⊗ ℱ) ⟶ Sym² ℰ ⊗ Sym² ℱ`, `(e ⊗ f) ⊗ (e' ⊗ f') ↦ ee' ⊗ ff'`. -/
def cauchyπ : tens (tens E F) (tens E F) ⟶
    tens (AE.piece ((1 + 1 : ℕ) : ℤ)) (AF.piece ((1 + 1 : ℕ) : ℤ)) :=
  middleFour E F E F ≫ tensorHom (sq ιE hE) (sq ιF hF)

/-- On stalks, `π` is `SymPow.cauchyφ` composed with the square map of `ℰ ⊗ ℱ`. -/
theorem symSymStalk_stalkMapL_cauchyπ (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp ((tens E F)) ((tens E F))).presheaf x)) :
    symSymStalk ιE hE ιF hF x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (cauchyπ ιE hE ιF hF)) t) =
      SymPow.cauchyφ (symWStalk ιW hW x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (sq ιW hW)) t)) := by
  refine Eq.trans (congrArg (symSymStalk ιE hE ιF hF x)
    (SymSquareFiltration.stalkMapL_comp _ _ x t)) ?_
  refine Eq.trans ?_ (congrArg SymPow.cauchyφ (symWStalk_stalkMapL_sq ιW hW x t)).symm
  refine Eq.trans ?_ (DFunLike.congr_fun (SymPow.cauchyφ_comp_sqMul (S := ↑(TopCat.Presheaf.stalk
    Osharp.obj x))) _).symm
  have h1 := congr_tensorSheafStalkEquiv_stalkMapL_tensorHom (sq ιE hE) (sq ιF hF) x
    (symmetricPowerStalkEquiv AE ιE hE (1 + 1) x) (symmetricPowerStalkEquiv AF ιF hF (1 + 1) x)
    (SymPow.sqMul LinearMap.id) (SymPow.sqMul LinearMap.id)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp E E x)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp F F x)
    (symmetricPowerStalkEquiv_stalkMapL_sq ιE hE x) (symmetricPowerStalkEquiv_stalkMapL_sq ιF hF x)
    (PresheafOfModules.stalkMapL x (middleFour E F E F).val t)
  exact h1.trans (congrArg
    (TensorProduct.map (SymPow.sqMul LinearMap.id) (SymPow.sqMul LinearMap.id))
    (tensorTensorStalkEquiv_stalkMapL_middleFour E F E F x t))

/-- **The Segre map `φ : Sym²(ℰ ⊗ ℱ) ⟶ Sym² ℰ ⊗ Sym² ℱ`**, the descent of `π` along the square
map of `ℰ ⊗ ℱ`. -/
def cauchyφSheaf : AW.piece ((1 + 1 : ℕ) : ℤ) ⟶
    (tens (AE.piece ((1 + 1 : ℕ) : ℤ)) (AF.piece ((1 + 1 : ℕ) : ℤ))) :=
  haveI : Epi (C := Mods Osharp) (sq ιW hW) := epi_sq ιW hW
  Abelian.epiDesc (C := Mods Osharp) (sq ιW hW) (cauchyπ ιE hE ιF hF) (by
    refine SymSquareFiltration.eq_of_stalkMapL_eq _ _ fun x z => ?_
    refine (symSymStalk ιE hE ιF hF x).injective ?_
    refine (congrArg (symSymStalk ιE hE ιF hF x)
      (SymSquareFiltration.stalkMapL_comp _ _ x z)).trans ?_
    refine (symSymStalk_stalkMapL_cauchyπ ιE hE ιF hF ιW hW x _).trans ?_
    refine Eq.trans ?_ (congrArg (symSymStalk ιE hE ιF hF x)
      (SymSquareFiltration.stalkMapL_zero x z)).symm
    refine Eq.trans ?_ (map_zero _).symm
    exact (congrArg (fun y => SymPow.cauchyφ (symWStalk ιW hW x y))
      (stalkMapL_kernelι (sq ιW hW) x z)).trans
      ((congrArg SymPow.cauchyφ (map_zero _)).trans (map_zero _)))

/-- The Segre map `φ` composed with the square map of `ℰ ⊗ ℱ` is `π`. -/
theorem sq_comp_cauchyφSheaf :
    sq ιW hW ≫ cauchyφSheaf ιE hE ιF hF ιW hW = cauchyπ ιE hE ιF hF := by
  have : Epi (C := Mods Osharp) (sq ιW hW) := epi_sq ιW hW
  exact Abelian.comp_epiDesc (C := Mods Osharp) _ _ _

attribute [irreducible] cauchyφSheaf

/-- **The stalk of the Segre map is `SymPow.cauchyφ`.** -/
theorem symSymStalk_stalkMapL_cauchyφSheaf (x : ↥X)
    (u : ↑(TopCat.Presheaf.stalk (AW.piece ((1 + 1 : ℕ) : ℤ)).val.presheaf x)) :
    symSymStalk ιE hE ιF hF x
        (PresheafOfModules.stalkMapL x
          (SymPresentation.valHom (cauchyφSheaf ιE hE ιF hF ιW hW)) u) =
      SymPow.cauchyφ (symWStalk ιW hW x u) := by
  refine ((SymPresentation.epi_iff_surjective_stalkMapL (sq ιW hW)).1 (epi_sq ιW hW) x u).elim
    fun t ht => ?_
  subst ht
  refine (congrArg (symSymStalk ιE hE ιF hF x)
    (stalkMapL_of_comp_eq _ _ _ (sq_comp_cauchyφSheaf ιE hE ιF hF ιW hW) x t)).trans ?_
  exact symSymStalk_stalkMapL_cauchyπ ιE hE ιF hF ιW hW x t

/-- `(ℰ ⊗ ℰ) ⊗ (ℱ ⊗ ℱ) ⟶ Sym²(ℰ ⊗ ℱ)`, `(e ⊗ e') ⊗ (f ⊗ f') ↦ (e ⊗ f)(e' ⊗ f')`: the
middle-four interchange followed by the square map. -/
def middleFourSq : tens (tens E E) (tens F F) ⟶ AW.piece ((1 + 1 : ℕ) : ℤ) :=
  middleFour E E F F ≫ sq ιW hW

/-- `𝟙 ⊗ σ : (ℰ ⊗ ℰ) ⊗ (ℱ ⊗ ℱ) ⟶ (ℰ ⊗ ℰ) ⊗ (ℱ ⊗ ℱ)`, the symmetry on the second factor. -/
def braidRightSheaf : tens (tens E E) (tens F F) ⟶ tens (tens E E) (tens F F) :=
  tensorHom (𝟙 (tens E E)) (braid F F)

/-- `(ℰ ⊗ ℰ) ⊗ (ℱ ⊗ ℱ) ⟶ Sym²(ℰ ⊗ ℱ)`, `(e ⊗ e') ⊗ (f ⊗ f') ↦ (e ⊗ f')(e' ⊗ f)`. -/
def braidMiddleFourSq : tens (tens E E) (tens F F) ⟶ AW.piece ((1 + 1 : ℕ) : ℤ) :=
  braidRightSheaf (E := E) (F := F) ≫ middleFourSq ιW hW

/-- `(ℰ ⊗ ℰ) ⊗ (ℱ ⊗ ℱ) ⟶ Sym²(ℰ ⊗ ℱ)`,
`(e ⊗ e') ⊗ (f ⊗ f') ↦ (e ⊗ f)(e' ⊗ f') - (e ⊗ f')(e' ⊗ f)`. -/
def cauchyαQuadSheaf : tens (tens E E) (tens F F) ⟶ AW.piece ((1 + 1 : ℕ) : ℤ) :=
  middleFourSq ιW hW - braidMiddleFourSq ιW hW

/-- On stalks, `𝟙 ⊗ σ` on `(ℰ ⊗ ℰ) ⊗ (ℱ ⊗ ℱ)` is the symmetry on the second factor of
`(ℰₓ ⊗ ℰₓ) ⊗ (ℱₓ ⊗ ℱₓ)`. -/
theorem tensorTensorStalkEquiv_stalkMapL_braidRight (x : ↥X)
    (y : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp ((tens E E)) ((tens F F))).presheaf x)) :
    tensorTensorStalkEquiv E E F F x
        (PresheafOfModules.stalkMapL x (tensorHom (𝟙 ((tens E E))) (braid F F)).val y) =
      LinearMap.lTensor _ (TensorProduct.comm _ _ _).toLinearMap
        (tensorTensorStalkEquiv E E F F x y) := by
  exact congr_tensorSheafStalkEquiv_stalkMapL_tensorHom (𝟙 (tens E E)) (braid F F) x
    (PresheafOfModules.tensorSheafStalkEquiv Osharp E E x)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp F F x) LinearMap.id
    (TensorProduct.comm _ _ _).toLinearMap (PresheafOfModules.tensorSheafStalkEquiv Osharp E E x)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp F F x)
    (fun a => congrArg (PresheafOfModules.tensorSheafStalkEquiv Osharp E E x)
      (SymSquareFiltration.stalkMapL_id x a))
    (tensorSheafStalkEquiv_stalkMapL_braid F F x) y

/-- On stalks, the middle-four interchange followed by the square map is
`(e ⊗ e') ⊗ (f ⊗ f') ↦ (e ⊗ f)(e' ⊗ f')`. -/
theorem symWStalk_stalkMapL_middleFour_sq (x : ↥X)
    (y : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp ((tens E E)) ((tens F F))).presheaf x)) :
    symWStalk ιW hW x (PresheafOfModules.stalkMapL x
        (SymPresentation.valHom (middleFour E E F F ≫ sq ιW hW)) y) =
      SymPow.sqMul LinearMap.id (TensorProduct.tensorTensorTensorComm _ _ _ _ _
        (tensorTensorStalkEquiv E E F F x y)) :=
  (congrArg (symWStalk ιW hW x) (SymSquareFiltration.stalkMapL_comp _ _ x y)).trans
    ((symWStalk_stalkMapL_sq ιW hW x _).trans (congrArg (SymPow.sqMul LinearMap.id)
      (tensorTensorStalkEquiv_stalkMapL_middleFour E E F F x y)))

/-- On stalks, `middleFourSq` is `(e ⊗ e') ⊗ (f ⊗ f') ↦ (e ⊗ f)(e' ⊗ f')`. -/
theorem symWStalk_stalkMapL_middleFourSq (x : ↥X)
    (y : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp ((tens E E)) ((tens F F))).presheaf x)) :
    symWStalk ιW hW x (PresheafOfModules.stalkMapL x
        (SymPresentation.valHom (middleFourSq ιW hW)) y) =
      SymPow.sqMul LinearMap.id (TensorProduct.tensorTensorTensorComm _ _ _ _ _
        (tensorTensorStalkEquiv E E F F x y)) :=
  symWStalk_stalkMapL_middleFour_sq ιW hW x y

/-- On stalks, `braidRightSheaf` is the symmetry on the second factor of
`(ℰₓ ⊗ ℰₓ) ⊗ (ℱₓ ⊗ ℱₓ)`. -/
theorem tensorTensorStalkEquiv_stalkMapL_braidRightSheaf (x : ↥X)
    (y : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp ((tens E E)) ((tens F F))).presheaf x)) :
    tensorTensorStalkEquiv E E F F x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (braidRightSheaf (E := E) (F := F)))
          y) =
      LinearMap.lTensor _ (TensorProduct.comm _ _ _).toLinearMap
        (tensorTensorStalkEquiv E E F F x y) :=
  tensorTensorStalkEquiv_stalkMapL_braidRight x y

/-- On stalks, `braidMiddleFourSq` is `(e ⊗ e') ⊗ (f ⊗ f') ↦ (e ⊗ f')(e' ⊗ f)`. -/
theorem symWStalk_stalkMapL_braidMiddleFourSq (x : ↥X)
    (y : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp ((tens E E)) ((tens F F))).presheaf x)) :
    symWStalk ιW hW x (PresheafOfModules.stalkMapL x
        (SymPresentation.valHom (braidMiddleFourSq ιW hW)) y) =
      SymPow.sqMul LinearMap.id (TensorProduct.tensorTensorTensorComm _ _ _ _ _
        (LinearMap.lTensor _ (TensorProduct.comm _ _ _).toLinearMap
          (tensorTensorStalkEquiv E E F F x y))) := by
  have h1 := stalkMapL_of_comp_eq (braidRightSheaf (E := E) (F := F)) (middleFourSq ιW hW)
    (braidMiddleFourSq ιW hW) rfl x y
  have h2 := symWStalk_stalkMapL_middleFourSq ιW hW x (PresheafOfModules.stalkMapL x
    (SymPresentation.valHom (braidRightSheaf (E := E) (F := F))) y)
  have h3 := tensorTensorStalkEquiv_stalkMapL_braidRightSheaf (E := E) (F := F) x y
  exact ((congrArg (symWStalk ιW hW x) h1).symm.trans h2).trans
    (congrArg (fun z => SymPow.sqMul LinearMap.id
      (TensorProduct.tensorTensorTensorComm _ _ _ _ _ z)) h3)

/-- On stalks, `cauchyαQuadSheaf` is
`(e ⊗ e') ⊗ (f ⊗ f') ↦ (e ⊗ f)(e' ⊗ f') - (e ⊗ f')(e' ⊗ f)`. -/
theorem symWStalk_stalkMapL_cauchyαQuadSheaf (x : ↥X)
    (y : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp ((tens E E)) ((tens F F))).presheaf x)) :
    symWStalk ιW hW x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (cauchyαQuadSheaf ιW hW)) y) =
      (SymPow.sqMul LinearMap.id ∘ₗ ((TensorProduct.tensorTensorTensorComm _ _ _ _ _).toLinearMap -
        (TensorProduct.tensorTensorTensorComm _ _ _ _ _).toLinearMap ∘ₗ
          LinearMap.lTensor _ (TensorProduct.comm _ _ _).toLinearMap))
        (tensorTensorStalkEquiv E E F F x y) := by
  refine (congrArg (symWStalk ιW hW x) (stalkMapL_sub _ _ x y)).trans ?_
  refine (map_sub _ _ _).trans ?_
  refine Eq.trans (congrArg₂ (· - ·) (symWStalk_stalkMapL_middleFourSq ιW hW x y)
    (symWStalk_stalkMapL_braidMiddleFourSq ιW hW x y)) ?_
  exact (map_sub (SymPow.sqMul LinearMap.id) _ _).symm

/-- `(ℰ ⊗ ℰ) ⊗ (ℱ ⊗ ℱ) ⟶ ⋀² ℰ ⊗ ⋀² ℱ`, the tensor product of the two exterior square maps. -/
abbrev wedgeWedge : tens (tens E E) (tens F F) ⟶
    tens (BE.piece ((1 + 1 : ℕ) : ℤ)) (BF.piece ((1 + 1 : ℕ) : ℤ)) :=
  tensorHom (wsq κE hBE) (wsq κF hBF)

/-- On stalks, `wedgeWedge` is `SymPow.wedgeMul ⊗ SymPow.wedgeMul`. -/
theorem extExtStalk_stalkMapL_wedgeWedge (x : ↥X)
    (y : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp ((tens E E)) ((tens F F))).presheaf x)) :
    extExtStalk κE hBE κF hBF x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (wedgeWedge κE hBE κF hBF)) y) =
      TensorProduct.map SymPow.wedgeMul SymPow.wedgeMul (tensorTensorStalkEquiv E E F F x y) :=
  congr_tensorSheafStalkEquiv_stalkMapL_tensorHom (wsq κE hBE) (wsq κF hBF) x
    (exteriorPowerStalkEquiv BE κE hBE (1 + 1) x) (exteriorPowerStalkEquiv BF κF hBF (1 + 1) x)
    SymPow.wedgeMul SymPow.wedgeMul (PresheafOfModules.tensorSheafStalkEquiv Osharp E E x)
    (PresheafOfModules.tensorSheafStalkEquiv Osharp F F x)
    (exteriorPowerStalkEquiv_stalkMapL_wsq κE hBE x)
    (exteriorPowerStalkEquiv_stalkMapL_wsq κF hBF x) y

/-- On stalks, `cauchyαQuadSheaf` is `SymPow.cauchyα` composed with the stalk of `wedgeWedge`. -/
theorem symWStalk_stalkMapL_cauchyαQuadSheaf' (x : ↥X)
    (y : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp ((tens E E)) ((tens F F))).presheaf x)) :
    symWStalk ιW hW x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (cauchyαQuadSheaf ιW hW)) y) =
      SymPow.cauchyα (extExtStalk κE hBE κF hBF x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (wedgeWedge κE hBE κF hBF)) y)) :=
  (symWStalk_stalkMapL_cauchyαQuadSheaf ιW hW x y).trans
    ((DFunLike.congr_fun (SymPow.cauchyα_comp_map_wedgeMul (S := ↑(TopCat.Presheaf.stalk
      Osharp.obj x))) _).symm.trans
      (congrArg SymPow.cauchyα (extExtStalk_stalkMapL_wedgeWedge κE hBE κF hBF x y).symm))

/-- `(ℰ ⊗ ℰ) ⊗ (ℱ ⊗ ℱ) ⟶ Sym²(ℰ ⊗ ℱ)` vanishes on the kernel of `wedgeWedge`: on stalks it
factors through `⋀² ℰₓ ⊗ ⋀² ℱₓ` as `SymPow.cauchyα`. -/
theorem kernelι_wedgeWedge_comp_cauchyαQuadSheaf :
    kernel.ι (C := Mods Osharp) (wedgeWedge κE hBE κF hBF) ≫ cauchyαQuadSheaf ιW hW = 0 :=
  comp_eq_zero_of_stalkMapL _ _ fun x z => (symWStalk ιW hW x).injective <|
    ((symWStalk_stalkMapL_cauchyαQuadSheaf' ιW hW κE hBE κF hBF x _).trans
      ((congrArg (fun y => SymPow.cauchyα (extExtStalk κE hBE κF hBF x y))
        (stalkMapL_kernelι (wedgeWedge κE hBE κF hBF) x z)).trans
        ((congrArg SymPow.cauchyα (map_zero _)).trans (map_zero _)))).trans (map_zero _).symm

/-- **`α : ⋀² ℰ ⊗ ⋀² ℱ ⟶ Sym²(ℰ ⊗ ℱ)`**, the descent along `wedgeWedge`. -/
def cauchyαSheaf : (tens (BE.piece ((1 + 1 : ℕ) : ℤ)) (BF.piece ((1 + 1 : ℕ) : ℤ))) ⟶
    AW.piece ((1 + 1 : ℕ) : ℤ) :=
  haveI := epi_wsq κE hBE
  haveI := epi_wsq κF hBF
  haveI : Epi (C := Mods Osharp) (wedgeWedge κE hBE κF hBF) :=
    epi_tensorHom (wsq κE hBE) (wsq κF hBF)
  Abelian.epiDesc (C := Mods Osharp) (wedgeWedge κE hBE κF hBF)
    (cauchyαQuadSheaf ιW hW) (kernelι_wedgeWedge_comp_cauchyαQuadSheaf ιW hW κE hBE κF hBF)

/-- The map `α` composed with `wedgeWedge` is `cauchyαQuadSheaf`. -/
theorem wedgeWedge_comp_cauchyαSheaf :
    wedgeWedge κE hBE κF hBF ≫ cauchyαSheaf ιW hW κE hBE κF hBF = cauchyαQuadSheaf ιW hW := by
  have := epi_wsq κE hBE
  have := epi_wsq κF hBF
  have : Epi (C := Mods Osharp) (wedgeWedge κE hBE κF hBF) :=
    epi_tensorHom (wsq κE hBE) (wsq κF hBF)
  exact Abelian.comp_epiDesc (C := Mods Osharp) _ _ _

attribute [irreducible] cauchyαSheaf

/-- **The stalk of `α` is `SymPow.cauchyα`.** -/
theorem symWStalk_stalkMapL_cauchyαSheaf (x : ↥X)
    (u : ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp
      (BE.piece ((1 + 1 : ℕ) : ℤ)) (BF.piece ((1 + 1 : ℕ) : ℤ))).presheaf x)) :
    symWStalk ιW hW x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom
          (cauchyαSheaf ιW hW κE hBE κF hBF)) u) =
      SymPow.cauchyα (extExtStalk κE hBE κF hBF x u) := by
  have := epi_wsq κE hBE
  have := epi_wsq κF hBF
  refine ((SymPresentation.epi_iff_surjective_stalkMapL (wedgeWedge κE hBE κF hBF)).1
    (epi_tensorHom (wsq κE hBE) (wsq κF hBF)) x u).elim fun t ht => ?_
  subst ht
  refine (congrArg (symWStalk ιW hW x)
    (stalkMapL_of_comp_eq _ _ _ (wedgeWedge_comp_cauchyαSheaf ιW hW κE hBE κF hBF) x t)).trans ?_
  exact symWStalk_stalkMapL_cauchyαQuadSheaf' ιW hW κE hBE κF hBF x t

/-- The composite `φ ∘ α : ⋀² ℰ ⊗ ⋀² ℱ ⟶ Sym² ℰ ⊗ Sym² ℱ` is zero. -/
theorem cauchyαSheaf_comp_cauchyφSheaf :
    cauchyαSheaf ιW hW κE hBE κF hBF ≫ cauchyφSheaf ιE hE ιF hF ιW hW = 0 :=
  comp_eq_zero_of_stalkMapL _ _ fun x z => (symSymStalk ιE hE ιF hF x).map_eq_zero_iff.1 <|
    (symSymStalk_stalkMapL_cauchyφSheaf ιE hE ιF hF ιW hW x _).trans <|
      (congrArg SymPow.cauchyφ (symWStalk_stalkMapL_cauchyαSheaf ιW hW κE hBE κF hBF x z)).trans
        (DFunLike.congr_fun (SymPow.cauchyφ_comp_cauchyα (S := ↑(TopCat.Presheaf.stalk
          Osharp.obj x))) _)

/-- **The sequence `0 → ⋀²ℰ ⊗ ⋀²ℱ → Sym²(ℰ ⊗ ℱ) → Sym²ℰ ⊗ Sym²ℱ → 0` is short exact** when
every stalk of `ℰ` and of `ℱ` is free. -/
theorem shortExact_cauchy
    (hfE : ∀ x : ↥X, Module.Free ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (hfF : ∀ x : ↥X, Module.Free ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk F.val.presheaf x)) :
    (ShortComplex.mk (cauchyαSheaf ιW hW κE hBE κF hBF) (cauchyφSheaf ιE hE ιF hF ιW hW)
      (cauchyαSheaf_comp_cauchyφSheaf ιE hE ιF hF ιW hW κE hBE κF hBF)).ShortExact := by
  have hmono : Mono (cauchyαSheaf ιW hW κE hBE κF hBF) := by
    rw [AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap]
    intro x a b hab
    have := hfE x
    have := hfF x
    have hab' := (SymPresentation.stalkMap_apply _ x a).symm.trans
      (hab.trans (SymPresentation.stalkMap_apply _ x b))
    refine (extExtStalk κE hBE κF hBF x).injective (SymPow.cauchyα_injective ?_)
    exact (symWStalk_stalkMapL_cauchyαSheaf ιW hW κE hBE κF hBF x a).symm.trans
      ((congrArg (symWStalk ιW hW x) hab').trans
        (symWStalk_stalkMapL_cauchyαSheaf ιW hW κE hBE κF hBF x b))
  have hepi : Epi (cauchyφSheaf ιE hE ιF hF ιW hW) := by
    refine (SymPresentation.epi_iff_surjective_stalkMapL _).2 fun x t => ?_
    obtain ⟨w, hw⟩ := SymPow.cauchyφ_surjective (symSymStalk ιE hE ιF hF x t)
    refine ⟨(symWStalk ιW hW x).symm w, (symSymStalk ιE hE ιF hF x).injective ?_⟩
    refine (symSymStalk_stalkMapL_cauchyφSheaf ιE hE ιF hF ιW hW x _).trans ?_
    exact (congrArg SymPow.cauchyφ ((symWStalk ιW hW x).apply_symm_apply w)).trans hw
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact _).2 fun x => ?_
  refine (ShortComplex.moduleCat_exact_iff _).2 fun t ht => ?_
  have ht' : SymPow.cauchyφ (symWStalk ιW hW x t) = 0 :=
    (symSymStalk_stalkMapL_cauchyφSheaf ιE hE ιF hF ιW hW x t).symm.trans
      ((congrArg (symSymStalk ιE hE ιF hF x) ht).trans (map_zero _))
  refine ((SetLike.ext_iff.mp (SymPow.range_cauchyα (S := ↑(TopCat.Presheaf.stalk Osharp.obj x))
    (E := ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (F := ↑(TopCat.Presheaf.stalk F.val.presheaf x)))
    (symWStalk ιW hW x t)).2 ht').elim fun w hw => ?_
  refine ⟨(extExtStalk κE hBE κF hBF x).symm w, (symWStalk ιW hW x).injective ?_⟩
  refine (symWStalk_stalkMapL_cauchyαSheaf ιW hW κE hBE κF hBF x _).trans ?_
  exact (congrArg SymPow.cauchyα ((extExtStalk κE hBE κF hBF x).apply_symm_apply w)).trans hw

end Cauchy

end SheafOfModules.SymSquareTensor

end
