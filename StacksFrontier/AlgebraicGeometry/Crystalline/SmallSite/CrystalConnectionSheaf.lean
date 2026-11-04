module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionOpenSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionTensorSections

/-!
# The canonical connection of a crystal on `Cris(X/S)`, and the Leibniz rule

Fix a global crystalline situation of [Stacks, Tag 07MF], a crystal `F` in `𝒪_{X/S}`-modules on
the small crystalline site `Cris(X/S)` (`...SmallSite.IsSheafCrystal`) and an object
`(U, T, δ)` with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2].  The proof
of [Stacks, Tag 07J6] defines

`∇(s) = p₁^* s - c(p₀^* s)`,

a section of `F_{T'}` killed by pulling back along the diagonal `i`, hence a section of
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}`, the kernel of `p₀_* F_{T'} ⟶ F_T`.  This module builds it on the
sections over every open `W` of `T` (`...SmallSite.crystalConnectionApp`), as the inverse of the
identification `...SmallSite.firstOrderKernelIso` applied to `p₁^* s - p₀^* s`; proves that it
commutes with restriction, so is a morphism of sheaves of abelian groups
`∇ : F_T ⟶ F_T ⊗_{𝒪_T} Ω_{T/S,δ}` (`...SmallSite.crystalConnection`); and proves the Leibniz rule
`∇(f s) = f ∇(s) + s ⊗ d f` (`...SmallSite.crystalConnectionApp_smul`), "using the description of
`d` in Remark 07J2", i.e. `p₁(f) - p₀(f) = d f` in `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`.

## Main definitions

* `...SmallSite.crystalConnectionRaw` — the recipe `s ↦ p₁^* s - p₀^* s` on sections.
* `...SmallSite.crystalConnectionApp` and `...SmallSite.crystalConnection` — the connection, on
  sections over an open and as a morphism of sheaves of abelian groups on `T`.

## Main results

* `...SmallSite.firstOrderTensorInclusion_crystalConnectionApp` — the canonical morphism
  `F_T ⊗ Ω ⟶ p₀_* F_{T'}` carries `∇(s)` to `p₁^* s - p₀^* s`.
* `...SmallSite.crystalConnectionRaw_cocycle` — the curvature identity
  `q₀₁^* ∇(s) + q₁₂^* ∇(s) = q₀₂^* ∇(s)` on the second-order thickening.
* `...SmallSite.crystalConnectionApp_smul` — **the Leibniz rule**.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open TopologicalSpace

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

namespace GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (M : SheafOfModules.{u} (structureSheaf S))
  (A : CrystallineThickening S)

/-- **A morphism of modules on a scheme, on the sections over one open, as an additive map.** -/
abbrev schemeModulesValAppHom {X : Scheme.{u}} {N N' : X.Modules} (φ : N ⟶ N')
    (W : (X.Opens)ᵒᵖ) : N.val.obj W →+ N'.val.obj W :=
  (φ.val.app W).hom.toAddMonoidHom

/-! ### The morphisms of the two universal thickenings, restricted over an open -/

section Restrict

variable (W : A.obj.thickening.target.scheme.Opens)

/-- **`p₀ : T' ⟶ T` of [Stacks, Tag 07J2], restricted over an open `W` of `T`**, in
`Cris(X/S)`.  `p₀` is the identity on underlying spaces, so the preimage of `W` is `W`. -/
abbrev firstOrderCrysRestrictP₀ :
    (firstOrderThickeningCrysObject S A).restrictOpen W ⟶ A.restrictOpen W :=
  CrystallineThickening.restrictOpenMap (firstOrderThickeningCrysP₀ S A) W

/-- **`p₁ : T' ⟶ T`, restricted over an open.** -/
abbrev firstOrderCrysRestrictP₁ :
    (firstOrderThickeningCrysObject S A).restrictOpen W ⟶ A.restrictOpen W :=
  CrystallineThickening.restrictOpenMap (firstOrderThickeningCrysP₁ S A) W

/-- **The diagonal `i : T ⟶ T'`, restricted over an open.** -/
abbrev firstOrderCrysRestrictι :
    A.restrictOpen W ⟶ (firstOrderThickeningCrysObject S A).restrictOpen W :=
  CrystallineThickening.restrictOpenMap (firstOrderThickeningCrysι S A) W

/-- **`q₀₁ : T'' ⟶ T'` of [Stacks, Tag 07J3], restricted over an open.** -/
abbrev secondOrderCrysRestrictQ₀₁ :
    (secondOrderThickeningCrysObject S A).restrictOpen W ⟶
      (firstOrderThickeningCrysObject S A).restrictOpen W :=
  CrystallineThickening.restrictOpenMap (secondOrderThickeningCrysQ₀₁ S A) W

/-- **`q₁₂ : T'' ⟶ T'`, restricted over an open.** -/
abbrev secondOrderCrysRestrictQ₁₂ :
    (secondOrderThickeningCrysObject S A).restrictOpen W ⟶
      (firstOrderThickeningCrysObject S A).restrictOpen W :=
  CrystallineThickening.restrictOpenMap (secondOrderThickeningCrysQ₁₂ S A) W

/-- **`q₀₂ : T'' ⟶ T'`, restricted over an open.** -/
abbrev secondOrderCrysRestrictQ₀₂ :
    (secondOrderThickeningCrysObject S A).restrictOpen W ⟶
      (firstOrderThickeningCrysObject S A).restrictOpen W :=
  CrystallineThickening.restrictOpenMap (secondOrderThickeningCrysQ₀₂ S A) W

/-- **`q₀ : T'' ⟶ T`, restricted over an open.** -/
abbrev secondOrderCrysRestrictQ₀ :
    (secondOrderThickeningCrysObject S A).restrictOpen W ⟶ A.restrictOpen W :=
  CrystallineThickening.restrictOpenMap (secondOrderThickeningCrysQ₀ S A) W

/-- **`q₁ : T'' ⟶ T`, restricted over an open.** -/
abbrev secondOrderCrysRestrictQ₁ :
    (secondOrderThickeningCrysObject S A).restrictOpen W ⟶ A.restrictOpen W :=
  CrystallineThickening.restrictOpenMap (secondOrderThickeningCrysQ₁ S A) W

/-- **`q₂ : T'' ⟶ T`, restricted over an open.** -/
abbrev secondOrderCrysRestrictQ₂ :
    (secondOrderThickeningCrysObject S A).restrictOpen W ⟶ A.restrictOpen W :=
  CrystallineThickening.restrictOpenMap (secondOrderThickeningCrysQ₂ S A) W

/-- **`p₀ ∘ i = id`** over an open, in `Cris(X/S)`. -/
theorem firstOrderCrysRestrictι_comp_P₀ :
    firstOrderCrysRestrictι A W ≫ firstOrderCrysRestrictP₀ A W = 𝟙 (A.restrictOpen W) :=
  ObjectProperty.hom_ext _ (firstOrderRestrictι_comp_P₀ A.obj W)

/-- **`p₁ ∘ i = id`** over an open, in `Cris(X/S)`. -/
theorem firstOrderCrysRestrictι_comp_P₁ :
    firstOrderCrysRestrictι A W ≫ firstOrderCrysRestrictP₁ A W = 𝟙 (A.restrictOpen W) :=
  ObjectProperty.hom_ext _ (firstOrderRestrictι_comp_P₁ A.obj W)

/-- **`p₀ ∘ q₀₁ = q₀`** over an open, in `Cris(X/S)`. -/
theorem secondOrderCrysRestrictQ₀₁_comp_P₀ :
    secondOrderCrysRestrictQ₀₁ A W ≫ firstOrderCrysRestrictP₀ A W =
      secondOrderCrysRestrictQ₀ A W :=
  ObjectProperty.hom_ext _ (secondOrderRestrictQ₀₁_comp_P₀ A.obj W)

/-- **`p₁ ∘ q₀₁ = q₁`** over an open, in `Cris(X/S)`. -/
theorem secondOrderCrysRestrictQ₀₁_comp_P₁ :
    secondOrderCrysRestrictQ₀₁ A W ≫ firstOrderCrysRestrictP₁ A W =
      secondOrderCrysRestrictQ₁ A W :=
  ObjectProperty.hom_ext _ (secondOrderRestrictQ₀₁_comp_P₁ A.obj W)

/-- **`p₀ ∘ q₁₂ = q₁`** over an open, in `Cris(X/S)`. -/
theorem secondOrderCrysRestrictQ₁₂_comp_P₀ :
    secondOrderCrysRestrictQ₁₂ A W ≫ firstOrderCrysRestrictP₀ A W =
      secondOrderCrysRestrictQ₁ A W :=
  ObjectProperty.hom_ext _ (secondOrderRestrictQ₁₂_comp_P₀ A.obj W)

/-- **`p₁ ∘ q₁₂ = q₂`** over an open, in `Cris(X/S)`. -/
theorem secondOrderCrysRestrictQ₁₂_comp_P₁ :
    secondOrderCrysRestrictQ₁₂ A W ≫ firstOrderCrysRestrictP₁ A W =
      secondOrderCrysRestrictQ₂ A W :=
  ObjectProperty.hom_ext _ (secondOrderRestrictQ₁₂_comp_P₁ A.obj W)

/-- **`p₀ ∘ q₀₂ = q₀`** over an open, in `Cris(X/S)`. -/
theorem secondOrderCrysRestrictQ₀₂_comp_P₀ :
    secondOrderCrysRestrictQ₀₂ A W ≫ firstOrderCrysRestrictP₀ A W =
      secondOrderCrysRestrictQ₀ A W :=
  ObjectProperty.hom_ext _ (secondOrderRestrictQ₀₂_comp_P₀ A.obj W)

/-- **`p₁ ∘ q₀₂ = q₂`** over an open, in `Cris(X/S)`. -/
theorem secondOrderCrysRestrictQ₀₂_comp_P₁ :
    secondOrderCrysRestrictQ₀₂ A W ≫ firstOrderCrysRestrictP₁ A W =
      secondOrderCrysRestrictQ₂ A W :=
  ObjectProperty.hom_ext _ (secondOrderRestrictQ₀₂_comp_P₁ A.obj W)

end Restrict

/-! ### The difference of the two restrictions -/

/-- **The recipe of [Stacks, Tag 07J6] on the sections over an open `W` of `T`**:
`s ↦ p₁^* s - p₀^* s`, a section of `F` over the restriction of `(U, T', δ')` to `W`. -/
def crystalConnectionRaw (W : A.obj.thickening.target.scheme.Opens) :
    M.val.obj (op (A.restrictOpen W)) →+
      M.val.obj (op ((firstOrderThickeningCrysObject S A).restrictOpen W)) :=
  AddMonoidHom.mk'
    (fun s ↦ (crystalRestrict M (firstOrderCrysRestrictP₁ A W) s :
        M.val.obj (op ((firstOrderThickeningCrysObject S A).restrictOpen W))) -
      crystalRestrict M (firstOrderCrysRestrictP₀ A W) s)
    (fun s t ↦ by
      rw [map_add, map_add]
      abel)

/-- Unfolding of `...SmallSite.crystalConnectionRaw`. -/
theorem crystalConnectionRaw_apply (W : A.obj.thickening.target.scheme.Opens)
    (s : M.val.obj (op (A.restrictOpen W))) :
    crystalConnectionRaw M A W s =
      (crystalRestrict M (firstOrderCrysRestrictP₁ A W) s :
        M.val.obj (op ((firstOrderThickeningCrysObject S A).restrictOpen W))) -
        crystalRestrict M (firstOrderCrysRestrictP₀ A W) s := rfl

/-- **Restricting `∇(s)` along a morphism into the first-order thickening gives the difference of
the two composites.** -/
theorem crystalRestrict_crystalConnectionRaw {B : CrystallineThickening S}
    (W : A.obj.thickening.target.scheme.Opens)
    (g : B ⟶ (firstOrderThickeningCrysObject S A).restrictOpen W) (g₀ g₁ : B ⟶ A.restrictOpen W)
    (h₀ : g ≫ firstOrderCrysRestrictP₀ A W = g₀) (h₁ : g ≫ firstOrderCrysRestrictP₁ A W = g₁)
    (s : M.val.obj (op (A.restrictOpen W))) :
    crystalRestrict M g (crystalConnectionRaw M A W s) =
      crystalRestrict M g₁ s - crystalRestrict M g₀ s := by
  rw [crystalConnectionRaw_apply, map_sub, crystalRestrict_comp, crystalRestrict_comp, h₀, h₁]

/-- **The values of the recipe are killed by restriction along the diagonal**: both projections
retract the diagonal. -/
theorem crystalRestrict_ι_crystalConnectionRaw (W : A.obj.thickening.target.scheme.Opens)
    (s : M.val.obj (op (A.restrictOpen W))) :
    crystalRestrict M (firstOrderCrysRestrictι A W) (crystalConnectionRaw M A W s) = 0 := by
  rw [crystalRestrict_crystalConnectionRaw M A W (firstOrderCrysRestrictι A W) _ _
      (firstOrderCrysRestrictι_comp_P₀ A W) (firstOrderCrysRestrictι_comp_P₁ A W),
    sub_self]

/-- Restricting a morphism of `Cris(X/S)` over an open commutes with shrinking the open. -/
private theorem restrictOpenLE_comp_restrictOpenMap {B B' : CrystallineThickening S}
    (g : B ⟶ B') {V V' : B'.obj.thickening.target.scheme.Opens} (h : V ≤ V') :
    CrystallineThickening.restrictOpenLE B (g.hom.targetHom.hom.preimage_mono h) ≫
        CrystallineThickening.restrictOpenMap g V' =
      CrystallineThickening.restrictOpenMap g V ≫ CrystallineThickening.restrictOpenLE B' h :=
  ObjectProperty.hom_ext _ (Thickening.restrictOpenLE_restrictOpenMap g.hom h)

/-- **The recipe commutes with restriction to a smaller open.** -/
theorem crystalConnectionRaw_naturality {W W' : A.obj.thickening.target.scheme.Opens}
    (h : W' ≤ W) (s : M.val.obj (op (A.restrictOpen W))) :
    crystalRestrict M (CrystallineThickening.restrictOpenLE (firstOrderThickeningCrysObject S A) h)
        (crystalConnectionRaw M A W s) =
      crystalConnectionRaw M A W'
        (crystalRestrict M (CrystallineThickening.restrictOpenLE A h) s) := by
  refine (crystalRestrict_crystalConnectionRaw M A W _ _ _
    (restrictOpenLE_comp_restrictOpenMap (firstOrderThickeningCrysP₀ S A) h)
    (restrictOpenLE_comp_restrictOpenMap (firstOrderThickeningCrysP₁ S A) h) s).trans ?_
  rw [crystalConnectionRaw_apply, crystalRestrict_comp, crystalRestrict_comp]
  rfl

/-- **The curvature identity of [Stacks, Tag 07J6]**: the three restrictions of `∇(s)` to the
second-order thickening of [Stacks, Tag 07J3] satisfy `q₀₁^* ∇(s) + q₁₂^* ∇(s) = q₀₂^* ∇(s)`.
By the six relations of the remark they are `q₁^* s - q₀^* s`, `q₂^* s - q₁^* s` and
`q₂^* s - q₀^* s`.  No hypothesis on `F`. -/
theorem crystalConnectionRaw_cocycle (W : A.obj.thickening.target.scheme.Opens)
    (s : M.val.obj (op (A.restrictOpen W))) :
    crystalRestrict M (secondOrderCrysRestrictQ₀₁ A W) (crystalConnectionRaw M A W s) +
        crystalRestrict M (secondOrderCrysRestrictQ₁₂ A W) (crystalConnectionRaw M A W s) =
      crystalRestrict M (secondOrderCrysRestrictQ₀₂ A W) (crystalConnectionRaw M A W s) := by
  rw [crystalRestrict_crystalConnectionRaw M A W (secondOrderCrysRestrictQ₀₁ A W) _ _
      (secondOrderCrysRestrictQ₀₁_comp_P₀ A W) (secondOrderCrysRestrictQ₀₁_comp_P₁ A W),
    crystalRestrict_crystalConnectionRaw M A W (secondOrderCrysRestrictQ₁₂ A W) _ _
      (secondOrderCrysRestrictQ₁₂_comp_P₀ A W) (secondOrderCrysRestrictQ₁₂_comp_P₁ A W),
    crystalRestrict_crystalConnectionRaw M A W (secondOrderCrysRestrictQ₀₂ A W) _ _
      (secondOrderCrysRestrictQ₀₂_comp_P₀ A W) (secondOrderCrysRestrictQ₀₂_comp_P₁ A W)]
  abel

/-! ### The connection, read in `F_T ⊗ Ω` -/

variable {M}

/-- **The canonical connection of [Stacks, Tag 07J6] on the sections over an open `W` of `T`**,
read in `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`: the recipe `p₁^* s - p₀^* s`, which lies in the kernel of
restriction along the diagonal, carried into `F_T ⊗ Ω` by the inverse of the identification
`...SmallSite.firstOrderKernelIso`. -/
def crystalConnectionApp (hM : IsSheafCrystal M) (W : A.obj.thickening.target.scheme.Opens) :
    (crysAmbientSchemeModules M A).val.obj (op W) →+
      (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) :=
  (schemeModulesValAppHom (firstOrderKernelIso M A hM).inv (op W)).comp
    ((schemeModulesValAppHom (firstOrderAmbientRetraction M A) (op W)).comp
      (crystalConnectionRaw M A W))

/-- **The canonical morphism `F_T ⊗ Ω ⟶ p₀_* F_{T'}` carries the connection back to
`p₁^* s - p₀^* s`**: the connection is the recipe of the tag, read where the tag reads it. -/
theorem firstOrderTensorInclusion_crystalConnectionApp (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens) (s : M.val.obj (op (A.restrictOpen W))) :
    (firstOrderTensorInclusion M A).val.app (op W) (crystalConnectionApp A hM W s) =
      crystalConnectionRaw M A W s := by
  have hhom : ∀ y : (firstOrderAmbientKernel M A).val.obj (op W),
      (firstOrderKernelComparison M A).val.app (op W)
        ((firstOrderKernelIso M A hM).inv.val.app (op W) y) = y := fun y ↦
    congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app (op W) y)
      (firstOrderKernelIso M A hM).inv_hom_id
  have hsub : ∀ y, (firstOrderAmbientRetraction M A ≫
        kernel.ι (firstOrderAmbientProjMap₀ M A)).val.app (op W) y =
      y - (firstOrderAmbientInclMap M A).val.app (op W)
        ((firstOrderAmbientProjMap₀ M A).val.app (op W) y) :=
    fun y ↦ (congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app (op W) y)
      (firstOrderAmbientRetraction_ι M A)).trans rfl
  have hι : (firstOrderAmbientProjMap₀ M A).val.app (op W) (crystalConnectionRaw M A W s) = 0 :=
    crystalRestrict_ι_crystalConnectionRaw M A W s
  have e1 : (firstOrderTensorInclusion M A).val.app (op W) (crystalConnectionApp A hM W s) =
      (kernel.ι (firstOrderAmbientProjMap₀ M A)).val.app (op W)
        ((firstOrderKernelComparison M A).val.app (op W)
          ((firstOrderKernelIso M A hM).inv.val.app (op W)
            ((firstOrderAmbientRetraction M A).val.app (op W)
              (crystalConnectionRaw M A W s)))) := rfl
  rw [e1, hhom]
  refine (hsub (crystalConnectionRaw M A W s)).trans ?_
  rw [hι, map_zero]
  exact sub_zero _

/-- **The connection commutes with restriction to a smaller open.** -/
theorem crystalConnectionApp_naturality (hM : IsSheafCrystal M)
    {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) :
    (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme A.obj.toBase.hom
          (crysAmbientSchemeModules M A)).val.map (homOfLE h).op
        (crystalConnectionApp A hM W s) =
      crystalConnectionApp A hM W' ((crysAmbientSchemeModules M A).val.map (homOfLE h).op s) := by
  have hr := PresheafOfModules.naturality_apply (firstOrderAmbientRetraction M A).val
    (homOfLE h).op (crystalConnectionRaw M A W s)
  have hi := PresheafOfModules.naturality_apply (firstOrderKernelIso M A hM).inv.val
    (homOfLE h).op ((firstOrderAmbientRetraction M A).val.app (op W)
      (crystalConnectionRaw M A W s))
  have hn := crystalConnectionRaw_naturality M A h s
  exact hi.symm.trans (congrArg
    (fun z ↦ (firstOrderKernelIso M A hM).inv.val.app (op W') z)
    (hr.symm.trans (congrArg
      (fun z ↦ (firstOrderAmbientRetraction M A).val.app (op W') z) hn)))

/-- **The canonical connection of a crystal of [Stacks, Tag 07J6], at an object of
`Cris(X/S)`**, as a morphism of sheaves of abelian groups on the ambient scheme `T`

`∇ : F_T ⟶ F_T ⊗_{𝒪_T} Ω_{T/S,δ}`,

whose value on a section `s` over an open `W` is `...SmallSite.crystalConnectionApp`. -/
def crystalConnection (hM : IsSheafCrystal M) :
    (SheafOfModules.toSheaf _).obj (crysAmbientSchemeModules M A) ⟶
      (SheafOfModules.toSheaf _).obj
        (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)) :=
  ObjectProperty.homMk
    { app := fun W ↦ AddCommGrpCat.ofHom (crystalConnectionApp A hM W.unop)
      naturality := fun W W' i ↦ by
        ext s
        exact (crystalConnectionApp_naturality A hM (leOfHom i.unop) s).symm }

/-- The canonical connection on the sections over an open. -/
@[simp]
theorem crystalConnection_app (hM : IsSheafCrystal M)
    (W : (A.obj.thickening.target.scheme.Opens)ᵒᵖ)
    (s : (crysAmbientSchemeModules M A).val.obj W) :
    (crystalConnection A hM).hom.app W s = crystalConnectionApp A hM W.unop s := rfl

/-! ### The ideal of the diagonal kills the image of `F_T ⊗ Ω` -/

variable (M) in
/-- **A divided power differential over an open of `T`, read as a section of `𝒪_{T'}` through
the ideal of the diagonal**, at the type of the scalars of the sections of `F_{T'}` over that
open. -/
abbrev firstOrderCrysIdealScalar (W : (A.obj.thickening.target.scheme.Opens)ᵒᵖ)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj W) :
    ↑((firstOrderThickeningCrysObject S A).obj.thickening.target.scheme.ringCatSheaf.obj.obj
      (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W.unop))) :=
  firstOrderIdealScalar A.obj.thickening.target S.S.scheme A.obj.toBase.hom W ω

variable (M) in
/-- **The ideal of the diagonal has square zero**: `(0, ω) · (0, η) = 0` in `𝒪_{T'}`. -/
theorem firstOrderCrysIdealScalar_mul_self (W : (A.obj.thickening.target.scheme.Opens)ᵒᵖ)
    (ω η : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj W) :
    firstOrderCrysIdealScalar A W ω * firstOrderCrysIdealScalar A W η = 0 := by
  have h := mul_firstOrderThickeningInr A.obj.thickening.target S.S.scheme A.obj.toBase.hom W
    (firstOrderThickeningInr A.obj.thickening.target S.S.scheme A.obj.toBase.hom W ω) η
  refine h.trans ?_
  have h0 : (PresheafOfModules.sqZeroExtFst (firstOrderThickeningInr A.obj.thickening.target
      S.S.scheme
      A.obj.toBase.hom W ω) : ↑(A.obj.thickening.target.scheme.sheaf.obj.obj W)) = 0 := rfl
  rw [h0]
  exact (congrArg (firstOrderThickeningInr A.obj.thickening.target S.S.scheme A.obj.toBase.hom W)
    (zero_smul _ (show ↑((dpDifferentialsModules A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom).obj W) from η))).trans (map_zero _)

variable (M) in
/-- The square-zero section `(0, ω)` of `𝒪_{T'}` acting on `F_{T'}` over an open, as an additive
map out of the sections of `F_T ⊗ Ω` through the canonical morphism. -/
abbrev firstOrderCrysIdealAction (V : A.obj.thickening.target.scheme.Opens)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op V)) :
    (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op V) →+
      ((Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A))).val.obj (op V) :=
  AddMonoidHom.mk' (fun z ↦ firstOrderCrysIdealScalar A (op V) ω •
      (show (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.obj
          (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ V)) from
        (firstOrderTensorInclusion M A).val.app (op V) z))
    (fun z z' ↦ by
      rw [map_add]
      exact smul_add (firstOrderCrysIdealScalar A (op V) ω)
        (show (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.obj
          (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ V)) from
          (firstOrderTensorInclusion M A).val.app (op V) z)
        (show (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.obj
          (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ V)) from
          (firstOrderTensorInclusion M A).val.app (op V) z'))

/-- **The ideal of the diagonal kills the image of `F_T ⊗ Ω` in `F_{T'}`**: `(0, ω) · ι(z) = 0`.
On a local pure tensor `x ⊗ η` this is `(0, ω) (0, η) p₀^* x = 0`; a section of the tensor
product sheaf is locally a sum of local pure tensors, and `F_{T'}` is a sheaf. -/
theorem firstOrderCrysIdealScalar_smul_firstOrderTensorInclusion
    (W : A.obj.thickening.target.scheme.Opens)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W))
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    firstOrderCrysIdealAction M A W ω z = 0 := by
  have key := tensor_sections_ext
    (G := (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).obj
      (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A))) (W := W)
    (fun V hV ↦ firstOrderCrysIdealAction M A V
      ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
        (homOfLE hV).op ω))
    (fun _ _ ↦ 0) ?_ ?_ ?_ z
  · have hω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
        (homOfLE (le_refl W)).op ω = ω :=
      PresheafOfModules.map_id_apply _ _ ω
    rw [hω] at key
    exact key
  · intro V V' hV hV' h y
    have h1 := (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.map_smul
      (homOfLE h).op (firstOrderCrysIdealScalar A (op V)
        ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE hV).op ω))
      (show (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.obj
          (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ V)) from
        (firstOrderTensorInclusion M A).val.app (op V) y)
    have h2 := PresheafOfModules.naturality_apply
      (firstOrderThickeningInrSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val
      (homOfLE h).op
      ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE hV).op ω)
    have h3 := PresheafOfModules.naturality_apply (firstOrderTensorInclusion M A).val
      (homOfLE h).op y
    have h4 : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE h).op
        ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE hV).op ω) =
        (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE hV').op ω := by
      rw [← PresheafOfModules.map_comp_apply]
      rfl
    refine h1.trans ?_
    have e1 : (firstOrderThickeningCrysObject S A).obj.thickening.target.scheme.ringCatSheaf.obj.map
          (homOfLE h).op (firstOrderCrysIdealScalar A (op V)
            ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
              (homOfLE hV).op ω)) =
        firstOrderCrysIdealScalar A (op V')
          ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
            (homOfLE hV').op ω) :=
      h2.symm.trans (congrArg (fun w ↦ (firstOrderThickeningInrSheaf A.obj.thickening.target
        S.S.scheme A.obj.toBase.hom).val.app (op V') w) h4)
    rw [e1]
    exact congrArg (fun w : (crysAmbientSchemeModules M
        (firstOrderThickeningCrysObject S A)).val.obj
          (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ V')) ↦
        firstOrderCrysIdealScalar A (op V')
          ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
            (homOfLE hV').op ω) • w) h3.symm
  · intro V V' hV hV' h y
    exact map_zero _
  · intro V hV a b
    change firstOrderCrysIdealScalar A (op V)
        ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE hV).op ω) •
      (show (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.obj
          (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ V)) from
        (firstOrderTensorInclusion M A).val.app (op V)
          (Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
            (crysAmbientSchemeModules M A)
            (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom)
            (op V) a b)) = 0
    rw [firstOrderTensorInclusion_tmul, ← mul_smul]
    have hm := firstOrderCrysIdealScalar_mul_self A (op V)
      ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
        (homOfLE hV).op ω) b
    exact (congrArg (fun r ↦ r • (show (crysAmbientSchemeModules M
        (firstOrderThickeningCrysObject S A)).val.obj
          (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ V)) from
        (firstOrderAmbientInclMap M A).val.app (op V) a)) hm).trans (zero_smul _ _)

/-! ### The Leibniz rule -/

section Leibniz

variable (M)

/-- `p₀^* s`, a section of `F_{T'}`. -/
abbrev firstOrderP₀Sec (W : A.obj.thickening.target.scheme.Opens)
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) : FirstOrderSec M A W :=
  crystalRestrict M (firstOrderCrysRestrictP₀ A W) s

/-- `p₁^* s`, a section of `F_{T'}`. -/
abbrev firstOrderP₁Sec (W : A.obj.thickening.target.scheme.Opens)
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) : FirstOrderSec M A W :=
  crystalRestrict M (firstOrderCrysRestrictP₁ A W) s

/-- The canonical morphism `F_T ⊗ Ω ⟶ p₀_* F_{T'}` on sections, valued in `F_{T'}`. -/
abbrev firstOrderTensorSec (W : A.obj.thickening.target.scheme.Opens)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) : FirstOrderSec M A W :=
  (firstOrderTensorInclusion M A).val.app (op W) z

/-- The canonical morphism `F_T ⊗ Ω ⟶ p₀_* F_{T'}` is additive on sections. -/
theorem firstOrderTensorSec_add (W : A.obj.thickening.target.scheme.Opens)
    (z z' : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    firstOrderTensorSec M A W (z + z') =
      firstOrderTensorSec M A W z + firstOrderTensorSec M A W z' :=
  ((firstOrderTensorInclusion M A).val.app (op W)).hom.map_add z z'

/-- **The local pure tensor `x ⊗ ω`** of a section `x` of `F_T` and a differential `ω` over the
same open, as a section of `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`. -/
abbrev firstOrderTensorTmul (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W))
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) :=
  Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
    (crysAmbientSchemeModules M A)
    (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom) (op W) x ω

variable {M}

/-- `p₀(f) = (f, 0)`, a section of `𝒪_{T'}`. -/
abbrev firstOrderP₀Scalar (W : A.obj.thickening.target.scheme.Opens)
    (f : ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op W))) :
    FirstOrderRing A W :=
  ((firstOrderThickeningP₀ A.obj.thickening.target S.S.scheme A.obj.toBase.hom).app (op W)).hom f

/-- `p₁(f) = (f, d f)`, a section of `𝒪_{T'}`. -/
abbrev firstOrderP₁Scalar (W : A.obj.thickening.target.scheme.Opens)
    (f : ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op W))) :
    FirstOrderRing A W :=
  ((firstOrderThickeningP₁ A.obj.thickening.target S.S.scheme A.obj.toBase.hom).app (op W)).hom f

/-- `(0, ω)`, a section of `𝒪_{T'}`. -/
abbrev firstOrderIdealSec (W : A.obj.thickening.target.scheme.Opens)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) : FirstOrderRing A W :=
  firstOrderIdealScalar A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op W) ω

/-- **`p₁(f) - p₀(f) = d f`** in `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`, [Stacks, Tag 07J2]. -/
theorem firstOrderP₁Scalar_eq (W : A.obj.thickening.target.scheme.Opens)
    (f : ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op W))) :
    firstOrderP₁Scalar A W f = firstOrderP₀Scalar A W f +
      firstOrderIdealSec A W (sheafApp A.obj.thickening.target S.S.scheme A.obj.toBase.hom W f) :=
  eq_add_of_sub_eq' (firstOrderThickeningP₁_sub_P₀ A.obj.thickening.target S.S.scheme
    A.obj.toBase.hom (op W) f)

variable (M)

/-- `p₀^*` is semilinear over `p₀ : 𝒪_T ⟶ 𝒪_{T'}`, `f ↦ (f, 0)`. -/
theorem firstOrderP₀Sec_smul (W : A.obj.thickening.target.scheme.Opens)
    (f : ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op W)))
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) :
    firstOrderP₀Sec M A W (f • s) = firstOrderP₀Scalar A W f • firstOrderP₀Sec M A W s :=
  ((crysAmbientFMap M (firstOrderThickeningCrysP₀ S A)).val.app (op W)).hom.map_smul f s

/-- `p₁^*` is semilinear over `p₁ : 𝒪_T ⟶ 𝒪_{T'}`, `f ↦ (f, d f)`. -/
theorem firstOrderP₁Sec_smul (W : A.obj.thickening.target.scheme.Opens)
    (f : ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op W)))
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) :
    firstOrderP₁Sec M A W (f • s) = firstOrderP₁Scalar A W f • firstOrderP₁Sec M A W s :=
  ((crysAmbientFMap M (firstOrderThickeningCrysP₁ S A)).val.app (op W)).hom.map_smul f s

/-- The canonical morphism is linear over `p₀ : 𝒪_T ⟶ 𝒪_{T'}`. -/
theorem firstOrderTensorSec_smul (W : A.obj.thickening.target.scheme.Opens)
    (f : ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op W)))
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    firstOrderTensorSec M A W (f • z) = firstOrderP₀Scalar A W f • firstOrderTensorSec M A W z :=
  ((firstOrderTensorInclusion M A).val.app (op W)).hom.map_smul f z

/-- **The canonical morphism on a local pure tensor**: `x ⊗ ω ↦ (0, ω) · p₀^* x`. -/
theorem firstOrderTensorSec_tmul (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W))
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    firstOrderTensorSec M A W (firstOrderTensorTmul M A W x ω) =
      firstOrderIdealSec A W ω • firstOrderP₀Sec M A W x :=
  firstOrderTensorInclusion_tmul M A (op W) x ω

/-- `(0, ω) · ι(z) = 0`, at the section spelling. -/
theorem firstOrderIdealSec_smul_tensorSec (W : A.obj.thickening.target.scheme.Opens)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W))
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    firstOrderIdealSec A W ω • firstOrderTensorSec M A W z = 0 :=
  firstOrderCrysIdealScalar_smul_firstOrderTensorInclusion (M := M) A W ω z

variable {M}

/-- The canonical morphism carries `∇(s)` to `p₁^* s - p₀^* s`, at the section spelling. -/
theorem firstOrderTensorSec_crystalConnectionApp (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) :
    firstOrderTensorSec M A W (crystalConnectionApp A hM W s) =
      firstOrderP₁Sec M A W s - firstOrderP₀Sec M A W s :=
  firstOrderTensorInclusion_crystalConnectionApp A hM W s

/-- **Stacks Project, Tag 07J6: the Leibniz rule.**  For an open `W` of the ambient scheme of an
object of `Cris(X/S)`, a function `f` and a section `s` of `F_T` over `W`,

`∇(f s) = f ∇(s) + s ⊗ d f`

in `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`, where `d = d_{T/S,δ}` is the universal divided power derivation.
The source: "It is easily verified that `∇(fs) = f∇(s) + s ⊗ d(f)` using the description of `d`
in Remark 07J2", i.e. `p₁(f) - p₀(f) = d f` in `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`; the remaining term
`d f · ∇(s)` vanishes because the ideal of the diagonal squares to zero. -/
theorem crystalConnectionApp_smul (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (f : ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op W)))
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) :
    crystalConnectionApp A hM W (f • s) =
      f • crystalConnectionApp A hM W s +
        firstOrderTensorTmul M A W s
          (sheafApp A.obj.thickening.target S.S.scheme A.obj.toBase.hom W f) := by
  apply injective_firstOrderTensorInclusion M A hM W
  change firstOrderTensorSec M A W (crystalConnectionApp A hM W (f • s)) =
    firstOrderTensorSec M A W (f • crystalConnectionApp A hM W s +
      firstOrderTensorTmul M A W s
        (sheafApp A.obj.thickening.target S.S.scheme A.obj.toBase.hom W f))
  have hann := firstOrderIdealSec_smul_tensorSec M A W
    (sheafApp A.obj.thickening.target S.S.scheme A.obj.toBase.hom W f)
    (crystalConnectionApp A hM W s)
  have hc := firstOrderTensorSec_crystalConnectionApp A hM W s
  have hc' := firstOrderTensorSec_crystalConnectionApp A hM W (f • s)
  have hsm := firstOrderTensorSec_smul M A W f (crystalConnectionApp A hM W s)
  have htm := firstOrderTensorSec_tmul M A W s
    (sheafApp A.obj.thickening.target S.S.scheme A.obj.toBase.hom W f)
  have hadd := firstOrderTensorSec_add M A W (f • crystalConnectionApp A hM W s)
    (firstOrderTensorTmul M A W s
      (sheafApp A.obj.thickening.target S.S.scheme A.obj.toBase.hom W f))
  have h0 := firstOrderP₀Sec_smul M A W f s
  have h1 := firstOrderP₁Sec_smul M A W f s
  have hp := firstOrderP₁Scalar_eq A W f
  refine hc'.trans (Eq.trans ?_ hadd.symm)
  refine Eq.trans ?_ (congrArg₂ (· + ·) hsm.symm htm.symm)
  rw [hc] at hann
  rw [hc, h0, h1, hp]
  set P₀ := firstOrderP₀Sec M A W s
  set P₁ := firstOrderP₁Sec M A W s
  set a := firstOrderP₀Scalar A W f
  set b := firstOrderIdealSec A W
    (sheafApp A.obj.thickening.target S.S.scheme A.obj.toBase.hom W f)
  have h2 : P₁ = P₀ + (P₁ - P₀) := by abel
  rw [h2, add_smul, smul_add, smul_add, hann]
  abel_nf

end Leibniz

end GlobalCrystallineSituation.SmallSite

end Crystalline

end

end
