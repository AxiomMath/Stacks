module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPresentationExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeStalkSplitting
public import StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantSource
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationShortExact
public import StacksFrontier.LinearAlgebra.SymmetricPower.SquareFiltration

/-!
# The first step of the filtration of `Sym² ℱ` along a short exact sequence

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and
`0 → ℰ --f--> ℱ --g--> 𝒢 → 0` a short exact sequence of sheaves of `O♯`-modules with `𝒢` finite
locally free. Stacks Tag 01CJ gives the exact sequence

`ℰ ⊗ Sym¹ ℱ --μ_ℱ--> Sym² ℱ --Sym²(g)--> Sym² 𝒢 --> 0`

(`SheafOfModules.SymPresentation.symmetricPresentation_exact`), and the presentation
`ℰ --id--> ℰ --> 0` gives the multiplication `μ_ℰ : ℰ ⊗ Sym¹ ℰ ⟶ Sym² ℰ`. **This file proves that
`1 ⊗ Sym¹(f)` identifies the kernel of `μ_ℰ` with the kernel of `μ_ℱ`**, and that `μ_ℰ` is an
epimorphism. Together with the sequence above this is the sheaf-level filtration of `Sym² ℱ`
that the additivity of the second Adams operation (Stacks Tag 0FEJ) runs on: the image of `μ_ℱ`
is the first filtration step, and its class is computed from `μ_ℰ`.

## Main results

* `SheafOfModules.SymSquareFiltration.incl_comp_mulF`: the square
  `μ_ℱ ∘ (1 ⊗ Sym¹ f) = Sym²(f) ∘ μ_ℰ`.
* `SheafOfModules.SymSquareFiltration.mono_incl`: `1 ⊗ Sym¹ f` is a monomorphism.
* `SheafOfModules.SymSquareFiltration.epi_mulE`: `μ_ℰ` is an epimorphism.
* `SheafOfModules.SymSquareFiltration.kernelMulIso`: **`ker μ_ℰ ≅ ker μ_ℱ`**, compatibly with the
  inclusions into `ℰ ⊗ Sym¹ ℰ` and `ℰ ⊗ Sym¹ ℱ`.

## Implementation notes

Everything is read on stalks, where the sequence splits because the stalk of `𝒢` is free. The
inclusion `ker μ_ℱ ⊆ im(1 ⊗ Sym¹ f)` is the module-level
`SymPow.exists_lTensor_symMap_eq_of_symMulMap_eq_zero`; it turns into a factorization of
`ker μ_ℱ ⟶ ℰ ⊗ Sym¹ ℱ` through the monomorphism `1 ⊗ Sym¹ f` by
`Stacks.AlgebraicGeometry.ProjEulerSequence.factorThruMono`. That `Sym²(f)` is a monomorphism
(`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.mono_pieceMap_of_shortExact`) then pins the
factorization inside `ker μ_ℰ`. No identification of either kernel with `⋀² ℰ` is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace SheafOfModules.SymSquareFiltration

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-! ### Stalkwise helpers -/

section Helpers

variable {M N P : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The stalk map of the identity is the identity. -/
theorem stalkMapL_id (x : ↥X) (t : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    PresheafOfModules.stalkMapL x (SymPresentation.valHom (𝟙 M)) t = t := by
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf t
  exact PresheafOfModules.stalkMapL_germ x _ U hU y

theorem stalkMapL_id_eq (x : ↥X) :
    PresheafOfModules.stalkMapL x (SymPresentation.valHom (𝟙 M)) = LinearMap.id :=
  LinearMap.ext (stalkMapL_id x)

/-- The stalk map of a composite. -/
theorem stalkMapL_comp (u : M ⟶ N) (v : N ⟶ P) (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    PresheafOfModules.stalkMapL x (SymPresentation.valHom (u ≫ v)) t =
      PresheafOfModules.stalkMapL x (SymPresentation.valHom v)
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom u) t) := by
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf t
  refine Eq.trans (PresheafOfModules.stalkMapL_germ x _ U hU y) ?_
  refine Eq.trans ?_ (congrArg (PresheafOfModules.stalkMapL x (SymPresentation.valHom v))
    (PresheafOfModules.stalkMapL_germ x (SymPresentation.valHom u) U hU y)).symm
  exact (PresheafOfModules.stalkMapL_germ x (SymPresentation.valHom v) U hU _).symm

/-- The stalk map of a zero morphism vanishes. -/
theorem stalkMapL_zero (x : ↥X) (t : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    PresheafOfModules.stalkMapL x (SymPresentation.valHom (0 : M ⟶ N)) t = 0 := by
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf t
  refine Eq.trans (PresheafOfModules.stalkMapL_germ x _ U hU y) ?_
  exact Eq.trans (congrArg (TopCat.Presheaf.germ N.val.presheaf U x hU)
    (zero_val_app_apply (op U) y)) (map_zero _)

/-- Two morphisms of sheaves of modules with the same stalk maps are equal. -/
theorem eq_of_stalkMapL_eq (u v : M ⟶ N)
    (h : ∀ (x : ↥X) (t : ↑(TopCat.Presheaf.stalk M.val.presheaf x)),
      PresheafOfModules.stalkMapL x (SymPresentation.valHom u) t =
        PresheafOfModules.stalkMapL x (SymPresentation.valHom v) t) : u = v := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  exact TopCat.Presheaf.section_ext
    ((AlgebraicGeometry.SheafOfModules.toTopSheaf
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).obj N) V.unop _ _ fun y hy =>
    (PresheafOfModules.stalkMapL_germ y (SymPresentation.valHom u) V.unop hy s).symm.trans
      ((h y _).trans (PresheafOfModules.stalkMapL_germ y (SymPresentation.valHom v) V.unop hy s))

end Helpers

/-! ### The degree-one generator is an isomorphism -/

section Generator

/-- The ordered product of a single degree-one local section is that section. -/
theorem homogeneousProd_one {C' : Type u} [Category.{u} C'] {O : C'ᵒᵖ ⥤ CommRingCat.{u}}
    {Pc : ℤ → PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)}
    (A : Stacks.GradedAlgebra Pc) (U : C'ᵒᵖ) (z : Fin 1 → (Pc 1).obj U) :
    A.homogeneousProd U 1 z = z 0 :=
  eq_of_heq (A.one_mul 1 U (z 0))

variable {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (gen : M ⟶ A.piece 1) (hA : GradedAlgebra.IsSymmetricAlgebra A gen)

/-- The generator on the germ of a local section. -/
theorem symmetricPowerStalkEquiv_germ_generator (x : ↥X) (U : Opens ↥X) (hU : x ∈ U)
    (s : M.val.obj (op U)) :
    (symmetricPowerStalkEquiv A gen hA 1 x
        (TopCat.Presheaf.germ (A.piece 1).val.presheaf U x hU (gen.val.app (op U) s)) :
          SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x)) =
      SymmetricAlgebra.ι _ _ (TopCat.Presheaf.germ M.val.presheaf U x hU s) := by
  have h := symmetricPowerStalkEquiv_germ_homogeneousProd A gen hA 1 x U hU (fun _ => s)
  have h2 : A.toPresheafGradedAlgebra.homogeneousProd (op U) 1 (fun _ => gen.val.app (op U) s) =
      gen.val.app (op U) s := homogeneousProd_one A.toPresheafGradedAlgebra (op U) _
  refine Eq.trans ?_ (h.trans (Fin.prod_univ_one _))
  exact congrArg (fun z => (symmetricPowerStalkEquiv A gen hA 1 x
    (TopCat.Presheaf.germ (A.piece ((1 : ℕ) : ℤ)).val.presheaf U x hU z) :
      SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x))) h2.symm

/-- The stalk of the generator `M ⟶ Sym¹ M` is the generator `Mₓ → Sym¹ Mₓ`. -/
theorem symmetricPowerStalkEquiv_stalkMapL_generator (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    symmetricPowerStalkEquiv A gen hA 1 x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom gen) t) =
      SymPow.ιOne _ _ t := by
  refine (TopCat.Presheaf.exists_germ_eq M.val.presheaf t).elim fun U h1 => h1.elim fun hU h2 =>
    h2.elim fun s hs => ?_
  subst hs
  refine Subtype.ext ?_
  exact (congrArg (fun z => (symmetricPowerStalkEquiv A gen hA 1 x z :
    SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk M.val.presheaf x)))
    (PresheafOfModules.stalkMapL_germ x (SymPresentation.valHom gen) U hU s)).trans
    (symmetricPowerStalkEquiv_germ_generator gen hA x U hU s)

include hA in
/-- **The degree-one generator of a symmetric algebra is an isomorphism `M ≅ Sym¹ M`**: on every
stalk it is the generator `Mₓ → Sym¹ Mₓ`, which is bijective (`SymPow.ιOne_bijective`). -/
theorem isIso_generator : IsIso gen := by
  rw [AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap]
  intro x
  have hb := SymPow.ιOne_bijective (S := ↑(TopCat.Presheaf.stalk Osharp.obj x))
    (N := ↑(TopCat.Presheaf.stalk M.val.presheaf x))
  have key : ∀ t : ↑(TopCat.Presheaf.stalk M.val.presheaf x), symmetricPowerStalkEquiv A gen hA 1 x
      ((AlgebraicGeometry.SheafOfModules.stalkMap _ x gen).hom t) = SymPow.ιOne _ _ t := fun t =>
    (congrArg (symmetricPowerStalkEquiv A gen hA 1 x)
      (SymPresentation.stalkMap_apply gen x t)).trans
      (symmetricPowerStalkEquiv_stalkMapL_generator gen hA x t)
  refine ⟨fun a b hab => hb.1 ((key a).symm.trans ((congrArg _ hab).trans (key b))), fun y => ?_⟩
  obtain ⟨t, ht⟩ := hb.2 (symmetricPowerStalkEquiv A gen hA 1 x y)
  exact ⟨t, (symmetricPowerStalkEquiv A gen hA 1 x).injective ((key t).trans ht)⟩

end Generator

/-! ### The three maps -/

variable {E F G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {AE AF AG : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (ιE : E ⟶ AE.piece 1) (ιF : F ⟶ AF.piece 1) (ιG : G ⟶ AG.piece 1)
  (hE : GradedAlgebra.IsSymmetricAlgebra AE ιE) (hF : GradedAlgebra.IsSymmetricAlgebra AF ιF)
  (hG : GradedAlgebra.IsSymmetricAlgebra AG ιG)
  (f : E ⟶ F) (g : F ⟶ G) (hfg : f ≫ g = 0) (k : ℕ)

include hfg in
theorem hqpE : 𝟙 E ≫ f ≫ g = 0 :=
  (Category.id_comp (f ≫ g)).trans hfg

/-- The multiplication `μ_ℱ : ℰ ⊗ Symᵏ ℱ ⟶ Sym^{k+1} ℱ`, `e ⊗ y ↦ f(e) · y`: the first map of
the complex of Tag 01CJ for the presentation `ℰ --f--> ℱ --g--> 𝒢`. -/
abbrev mulF := (SymPresentation.symComplex ιF ιG hF hG f g hfg k).f

/-- The multiplication `μ_ℰ : ℰ ⊗ Symᵏ ℰ ⟶ Sym^{k+1} ℰ`. It is the first map of the complex of
Tag 01CJ for the presentation `ℰ --id--> ℰ --f ≫ g--> 𝒢`, whose second map plays no role. -/
abbrev mulE := (SymPresentation.symComplex ιE ιG hE hG (𝟙 E) (f ≫ g) (hqpE f g hfg) k).f

/-- `1 ⊗ Symᵏ(f) : ℰ ⊗ Symᵏ ℰ ⟶ ℰ ⊗ Symᵏ ℱ`. -/
abbrev incl := Stacks.Duality.tensorLeftHom E (hE.pieceMap hF f (k : ℤ))

/-- `Sym^{k+1}(f) : Sym^{k+1} ℰ ⟶ Sym^{k+1} ℱ`. -/
abbrev sq := hE.pieceMap hF f ((k + 1 : ℕ) : ℤ)

/-! ### Their stalks -/

/-- The stalk map of `valHom` is the stalk map of the underlying morphism. -/
theorem stalkMapL_valHom {M N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X)
    Osharp)} (u : M ⟶ N) (x : ↥X) (t : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    PresheafOfModules.stalkMapL x (SymPresentation.valHom u) t =
      PresheafOfModules.stalkMapL x u.val t :=
  rfl

/-- **The stalk of `1 ⊗ Symᵏ f` is `1 ⊗ Symᵏ fₓ`.** -/
theorem symTensorStalkEquiv_stalkMapL_incl (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp E (AE.piece (k : ℤ))).presheaf x)) :
    SymPresentation.symTensorStalkEquiv ιF hF k x
        (PresheafOfModules.stalkMapL x (incl ιE ιF hE hF f k).val z) =
      LinearMap.lTensor _ (SymPow.symMap k (PresheafOfModules.stalkMapL x f.val))
        (SymPresentation.symTensorStalkEquiv ιE hE k x z) := by
  have h1 := Stacks.Duality.tensorSheafStalkEquiv_stalkMapL_tensorLeft E
    (hE.pieceMap hF f (k : ℤ)) x z
  have key : (TensorProduct.congr (LinearEquiv.refl ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E.val.presheaf x))
        (symmetricPowerStalkEquiv AF ιF hF k x)).toLinearMap ∘ₗ
        LinearMap.lTensor ↑(TopCat.Presheaf.stalk E.val.presheaf x)
          (PresheafOfModules.stalkMapL x (hE.pieceMap hF f (k : ℤ)).val) =
      LinearMap.lTensor ↑(TopCat.Presheaf.stalk E.val.presheaf x)
          (SymPow.symMap k (PresheafOfModules.stalkMapL x f.val)) ∘ₗ
        (TensorProduct.congr (LinearEquiv.refl ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk E.val.presheaf x))
          (symmetricPowerStalkEquiv AE ιE hE k x)).toLinearMap := by
    refine TensorProduct.ext' fun a b => ?_
    exact congrArg (fun y => a ⊗ₜ y)
      (symmetricPowerStalkEquiv_stalkMapL_pieceMap ιE ιF hE hF f k x b)
  exact (congrArg (TensorProduct.congr (LinearEquiv.refl _ _)
    (symmetricPowerStalkEquiv AF ιF hF k x)) h1).trans (DFunLike.congr_fun key _)

/-- The stalk of `μ_ℰ` is the multiplication `Eₓ ⊗ Symᵏ Eₓ → Sym^{k+1} Eₓ`. -/
theorem symmetricPowerStalkEquiv_stalkMapL_mulE (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp E (AE.piece (k : ℤ))).presheaf x)) :
    symmetricPowerStalkEquiv AE ιE hE (k + 1) x
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom (mulE ιE ιG hE hG f g hfg k)) z) =
      SymPow.symMulMap k LinearMap.id (SymPresentation.symTensorStalkEquiv ιE hE k x z) :=
  (SymPresentation.symmetricPowerStalkEquiv_symComplex_f ιE ιG hE hG (𝟙 E) (f ≫ g)
    (hqpE f g hfg) k x z).trans
    (congrArg (fun φ => SymPow.symMulMap k φ (SymPresentation.symTensorStalkEquiv ιE hE k x z))
      (stalkMapL_id_eq x))

/-- **The square `μ_ℱ ∘ (1 ⊗ Symᵏ f) = Sym^{k+1}(f) ∘ μ_ℰ`.** -/
theorem incl_comp_mulF :
    incl ιE ιF hE hF f k ≫ mulF ιF ιG hF hG f g hfg k =
      mulE ιE ιG hE hG f g hfg k ≫ sq ιE ιF hE hF f k := by
  refine eq_of_stalkMapL_eq _ _ fun x z => ?_
  refine (symmetricPowerStalkEquiv AF ιF hF (k + 1) x).injective ?_
  refine Eq.trans (congrArg (symmetricPowerStalkEquiv AF ιF hF (k + 1) x)
    (stalkMapL_comp _ _ x z)) ?_
  refine Eq.trans ?_ (congrArg (symmetricPowerStalkEquiv AF ιF hF (k + 1) x)
    (stalkMapL_comp _ _ x z)).symm
  refine Eq.trans (SymPresentation.symmetricPowerStalkEquiv_symComplex_f ιF ιG hF hG f g hfg k x
    _) ?_
  refine Eq.trans (congrArg (SymPow.symMulMap k (PresheafOfModules.stalkMapL x
    (SymPresentation.valHom f))) (symTensorStalkEquiv_stalkMapL_incl ιE ιF hE hF f k x z)) ?_
  refine Eq.trans ?_
    (symmetricPowerStalkEquiv_stalkMapL_pieceMap ιE ιF hE hF f (k + 1) x _).symm
  refine Eq.trans ?_ (congrArg (SymPow.symMap (k + 1) (PresheafOfModules.stalkMapL x f.val))
    (symmetricPowerStalkEquiv_stalkMapL_mulE ιE ιG hE hG f g hfg k x z)).symm
  exact DFunLike.congr_fun (SymPow.symMulMap_comp_lTensor_symMap k
    (PresheafOfModules.stalkMapL x f.val)) _

/-! ### Monomorphy, epimorphy, and the kernels -/

/-- **`μ_ℰ` is an epimorphism**: `Sym^{k+1} Eₓ` is spanned by products of an element of `Eₓ` with
one of `Symᵏ Eₓ`. -/
theorem epi_mulE : Epi (mulE ιE ιG hE hG f g hfg k) := by
  refine (SymPresentation.epi_iff_surjective_stalkMapL _).2 fun x t => ?_
  obtain ⟨w, hw⟩ := SymPow.symMulMap_id_surjective k
    (symmetricPowerStalkEquiv AE ιE hE (k + 1) x t)
  refine ⟨(SymPresentation.symTensorStalkEquiv ιE hE k x).symm w,
    (symmetricPowerStalkEquiv AE ιE hE (k + 1) x).injective ?_⟩
  refine (symmetricPowerStalkEquiv_stalkMapL_mulE ιE ιG hE hG f g hfg k x _).trans ?_
  exact (congrArg (SymPow.symMulMap k LinearMap.id)
    ((SymPresentation.symTensorStalkEquiv ιE hE k x).apply_symm_apply w)).trans hw

section ShortExact

variable (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]

include hS in
/-- **`1 ⊗ Symᵏ f` is a monomorphism**: on every stalk `fₓ` has a retraction. -/
theorem mono_incl : Mono (incl ιE ιF hE hF f k) := by
  rw [AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap]
  intro x a b hab
  obtain ⟨r, hr⟩ :=
    Stacks.SheafOfModules.TopWedge.exists_stalkMapL_leftInverse_of_shortExact f g hfg hS x
  refine (SymPresentation.symTensorStalkEquiv ιE hE k x).injective ?_
  refine SymPow.lTensor_symMap_injective k _ r hr ?_
  exact (symTensorStalkEquiv_stalkMapL_incl ιE ιF hE hF f k x a).symm.trans
    ((congrArg (SymPresentation.symTensorStalkEquiv ιF hF k x) hab).trans
      (symTensorStalkEquiv_stalkMapL_incl ιE ιF hE hF f k x b))

include hS in
/-- **`Sym^{k+1}(f)` is a monomorphism.** -/
theorem mono_sq : Mono (sq ιE ιF hE hF f k) :=
  GradedAlgebra.IsSymmetricAlgebra.mono_pieceMap_of_shortExact ιE ιF hE hF f g hfg hS (k + 1)

variable (hk : k = 1)

include hS hk in
/-- In degree `k + 1 = 2`, on every stalk, the kernel of `μ_ℱ` lies in the image of
`1 ⊗ Sym¹ f`. -/
theorem exists_stalkMapL_incl_eq (x : ↥X)
    (w : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp E (AF.piece (k : ℤ))).presheaf x))
    (hw : PresheafOfModules.stalkMapL x (SymPresentation.valHom (mulF ιF ιG hF hG f g hfg k)) w =
      0) :
    ∃ q, PresheafOfModules.stalkMapL x (incl ιE ιF hE hF f k).val q = w := by
  obtain ⟨-, hsurj, hex⟩ := Stacks.SheafOfModules.TopWedge.stalkMapL_shortExact f g hfg hS x
  obtain ⟨r, hr⟩ :=
    Stacks.SheafOfModules.TopWedge.exists_stalkMapL_leftInverse_of_shortExact f g hfg hS x
  have : Module.Free ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk G.val.presheaf x) := Stacks.SheafOfModules.TopWedge.free_stalk G x
  have : Module.Projective ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk G.val.presheaf x) := Module.Projective.of_free
  have hexact : Function.Exact (PresheafOfModules.stalkMapL x f.val)
      (PresheafOfModules.stalkMapL x g.val) :=
    LinearMap.exact_iff.2 hex.symm
  have hz : SymPow.symMulMap k (PresheafOfModules.stalkMapL x f.val)
      (SymPresentation.symTensorStalkEquiv ιF hF k x w) = 0 :=
    (SymPresentation.symmetricPowerStalkEquiv_symComplex_f ιF ιG hF hG f g hfg k x
      w).symm.trans ((congrArg (symmetricPowerStalkEquiv AF ιF hF (k + 1) x) hw).trans
        (map_zero _))
  obtain ⟨w₀, hw₀⟩ := SymPow.exists_lTensor_symMap_eq_of_symMulMap_eq_zero k hk _ _ hexact hsurj
    r hr _ hz
  refine ⟨(SymPresentation.symTensorStalkEquiv ιE hE k x).symm w₀,
    (SymPresentation.symTensorStalkEquiv ιF hF k x).injective ?_⟩
  refine (symTensorStalkEquiv_stalkMapL_incl ιE ιF hE hF f k x _).trans ?_
  exact (congrArg (LinearMap.lTensor _ (SymPow.symMap k (PresheafOfModules.stalkMapL x f.val)))
    ((SymPresentation.symTensorStalkEquiv ιE hE k x).apply_symm_apply w₀)).trans hw₀

include hS hk in
/-- The inclusion of `ker μ_ℱ` factors through `1 ⊗ Sym¹ f`, stalkwise. -/
theorem kernel_ι_mulF_factor (y : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (kernel (mulF ιF ιG hF hG f g hfg k)).val.presheaf y)) :
    ∃ q, PresheafOfModules.stalkMapL y (incl ιE ιF hE hF f k).val q =
      PresheafOfModules.stalkMapL y (kernel.ι (mulF ιF ιG hF hG f g hfg k)).val z := by
  refine exists_stalkMapL_incl_eq ιE ιF ιG hE hF hG f g hfg k hS hk y _ ?_
  refine (stalkMapL_comp (kernel.ι (mulF ιF ιG hF hG f g hfg k)) _ y z).symm.trans ?_
  exact (congrArg (fun φ => PresheafOfModules.stalkMapL y (SymPresentation.valHom φ) z)
    (kernel.condition (mulF ιF ιG hF hG f g hfg k))).trans (stalkMapL_zero y z)

/-- The factorization of `ker μ_ℱ ⟶ ℰ ⊗ Sym¹ ℱ` through `1 ⊗ Sym¹ f`. -/
def kernelLiftIncl : kernel (mulF ιF ιG hF hG f g hfg k) ⟶
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj E).obj (AE.piece (k : ℤ)) :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.factorThruMono (incl ιE ιF hE hF f k)
    (mono_incl ιE ιF hE hF f g hfg k hS) (kernel.ι (mulF ιF ιG hF hG f g hfg k))
    (kernel_ι_mulF_factor ιE ιF ιG hE hF hG f g hfg k hS hk)

theorem kernelLiftIncl_comp :
    kernelLiftIncl ιE ιF ιG hE hF hG f g hfg k hS hk ≫ incl ιE ιF hE hF f k =
      kernel.ι (mulF ιF ιG hF hG f g hfg k) :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.factorThruMono_comp _ _ _ _

theorem kernelLiftIncl_comp_mulE :
    kernelLiftIncl ιE ιF ιG hE hF hG f g hfg k hS hk ≫ mulE ιE ιG hE hG f g hfg k = 0 := by
  have := mono_sq ιE ιF hE hF f g hfg k hS
  refine (cancel_mono (sq ιE ιF hE hF f k)).1 ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun φ => kernelLiftIncl ιE ιF ιG hE hF hG f g hfg k hS hk ≫ φ)
    (incl_comp_mulF ιE ιF ιG hE hF hG f g hfg k).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun φ => φ ≫ mulF ιF ιG hF hG f g hfg k)
    (kernelLiftIncl_comp ιE ιF ιG hE hF hG f g hfg k hS hk)).trans ?_
  exact (kernel.condition _).trans (zero_comp).symm

omit [Mono f] [Epi g] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree G] in
theorem kernel_ι_incl_comp_mulF :
    (kernel.ι (mulE ιE ιG hE hG f g hfg k) ≫ incl ιE ιF hE hF f k) ≫
      mulF ιF ιG hF hG f g hfg k = 0 := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun φ => kernel.ι (mulE ιE ιG hE hG f g hfg k) ≫ φ)
    (incl_comp_mulF ιE ιF ιG hE hF hG f g hfg k)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (fun φ => φ ≫ sq ιE ιF hE hF f k) (kernel.condition _)).trans zero_comp

/-- `ker μ_ℰ ⟶ ker μ_ℱ`, induced by `1 ⊗ Symᵏ f`. -/
def kernelMulHom : kernel (mulE ιE ιG hE hG f g hfg k) ⟶ kernel (mulF ιF ιG hF hG f g hfg k) :=
  kernel.lift _ (kernel.ι _ ≫ incl ιE ιF hE hF f k) (kernel_ι_incl_comp_mulF ιE ιF ιG hE hF hG f g
    hfg k)

omit [Mono f] [Epi g] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree G] in
theorem kernelMulHom_ι : kernelMulHom ιE ιF ιG hE hF hG f g hfg k ≫
    kernel.ι (mulF ιF ιG hF hG f g hfg k) =
      kernel.ι (mulE ιE ιG hE hG f g hfg k) ≫ incl ιE ιF hE hF f k :=
  kernel.lift_ι _ _ _

/-- `ker μ_ℱ ⟶ ker μ_ℰ`, the factorization through `1 ⊗ Sym¹ f`. -/
def kernelMulInv : kernel (mulF ιF ιG hF hG f g hfg k) ⟶ kernel (mulE ιE ιG hE hG f g hfg k) :=
  kernel.lift _ (kernelLiftIncl ιE ιF ιG hE hF hG f g hfg k hS hk)
    (kernelLiftIncl_comp_mulE ιE ιF ιG hE hF hG f g hfg k hS hk)

theorem kernelMulInv_ι : kernelMulInv ιE ιF ιG hE hF hG f g hfg k hS hk ≫
    kernel.ι (mulE ιE ιG hE hG f g hfg k) = kernelLiftIncl ιE ιF ιG hE hF hG f g hfg k hS hk :=
  kernel.lift_ι _ _ _

/-- **`ker μ_ℰ ≅ ker μ_ℱ`** in degree `k + 1 = 2`, through `1 ⊗ Sym¹ f`. -/
def kernelMulIso : kernel (mulE ιE ιG hE hG f g hfg k) ≅ kernel (mulF ιF ιG hF hG f g hfg k) where
  hom := kernelMulHom ιE ιF ιG hE hF hG f g hfg k
  inv := kernelMulInv ιE ιF ιG hE hF hG f g hfg k hS hk
  hom_inv_id := by
    have := mono_incl ιE ιF hE hF f g hfg k hS
    refine (cancel_mono (kernel.ι (mulE ιE ιG hE hG f g hfg k))).1 ?_
    refine (cancel_mono (incl ιE ιF hE hF f k)).1 ?_
    have h : kernelMulHom ιE ιF ιG hE hF hG f g hfg k ≫
        (kernelMulInv ιE ιF ιG hE hF hG f g hfg k hS hk ≫ kernel.ι (mulE ιE ιG hE hG f g hfg k)) ≫
          incl ιE ιF hE hF f k =
        kernel.ι (mulE ιE ιG hE hG f g hfg k) ≫ incl ιE ιF hE hF f k :=
      (congrArg (fun φ => kernelMulHom ιE ιF ιG hE hF hG f g hfg k ≫ φ)
        ((congrArg (fun φ => φ ≫ incl ιE ιF hE hF f k)
          (kernelMulInv_ι ιE ιF ιG hE hF hG f g hfg k hS hk)).trans
          (kernelLiftIncl_comp ιE ιF ιG hE hF hG f g hfg k hS hk))).trans
        (kernelMulHom_ι ιE ιF ιG hE hF hG f g hfg k)
    refine Eq.trans ?_ (h.trans (congrArg (fun φ => φ ≫ incl ιE ιF hE hF f k)
      (Category.id_comp (kernel.ι (mulE ιE ιG hE hG f g hfg k)))).symm)
    exact (congrArg (fun φ => φ ≫ incl ιE ιF hE hF f k) (Category.assoc _ _ _)).trans
      (Category.assoc _ _ _)
  inv_hom_id := by
    refine (cancel_mono (kernel.ι (mulF ιF ιG hF hG f g hfg k))).1 ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun φ => kernelMulInv ιE ιF ιG hE hF hG f g hfg k hS hk ≫ φ)
      (kernelMulHom_ι ιE ιF ιG hE hF hG f g hfg k)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun φ => φ ≫ incl ιE ιF hE hF f k)
      (kernelMulInv_ι ιE ιF ιG hE hF hG f g hfg k hS hk)).trans ?_
    exact (kernelLiftIncl_comp ιE ιF ιG hE hF hG f g hfg k hS hk).trans
      (Category.id_comp _).symm

end ShortExact

end SheafOfModules.SymSquareFiltration

end
