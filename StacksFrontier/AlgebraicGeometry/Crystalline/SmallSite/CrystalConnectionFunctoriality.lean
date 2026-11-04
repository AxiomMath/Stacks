module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningFunctorial

/-!
# The canonical connection of a crystal on `Cris(X/S)` is functorial in the object

The proof of [Stacks, Tag 07J6] notes that the collection of connections
`∇ : Γ(T, F_T) → Γ(T, F_T ⊗_{𝒪_T} Ω_{T/S,δ})` over the objects `(U, T, δ)` of `Cris(X/S)` "is
functorial in `T` because the construction of `T'` is functorial in `T`", and this is what makes
it a connection on `Cris(X/S)`.  For a morphism `g : (U_B, T_B, δ_B) ⟶ (U_A, T_A, δ_A)` of
`Cris(X/S)` this module builds the transition map

`τ_g : F_{T_A} ⊗_{𝒪} Ω_{T_A} ⟶ g_*(F_{T_B} ⊗_{𝒪} Ω_{T_B})`

on sections (`...SmallSite.crystalTensorTransition`), as the restriction of `F` along the induced
morphism `g' : T_B' ⟶ T_A'` of first-order thickenings read through the identification of
[Stacks, Tag 07J6]; proves that it is `x ⊗ ω ↦ g^* x ⊗ g^* ω` on local pure tensors
(`...SmallSite.crystalTensorTransition_tmul`), commutes with restriction, and is the only such
family (`...SmallSite.eq_crystalTensorTransition`); and proves `τ_g ∘ ∇_A = ∇_B ∘ g^*`
(`...SmallSite.crystalTensorTransition_crystalConnectionApp`).

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open TopologicalSpace

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **The functoriality datum commutes with the diagonals**: for a morphism `g : A ⟶ B` of
`CRIS(X/S)`, `i_A ≫ g' = g ≫ i_B`. -/
theorem firstOrderThickeningSiteι_comp_siteMap {A B : Thickening S} (g : A ⟶ B) :
    firstOrderThickeningSiteι S A ≫ firstOrderThickeningSiteMap g =
      g ≫ firstOrderThickeningSiteι S B :=
  Thickening.Hom.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
    (DividedPowerScheme.Hom.ext (firstOrderThickeningι_comp_schemeMap g))

namespace SmallSite

variable {A B : CrystallineThickening S} (g : B ⟶ A)

/-- **The morphism `T_B' ⟶ T_A'` of `Cris(X/S)` induced by a morphism `g : T_B ⟶ T_A`**: the
functoriality of the first-order universal thickening of [Stacks, Tag 07J2]. -/
abbrev firstOrderCrysFunctorMap :
    firstOrderThickeningCrysObject S B ⟶ firstOrderThickeningCrysObject S A :=
  ObjectProperty.homMk (firstOrderThickeningSiteMap g.hom)

/-- **The induced morphism of first-order thickenings, restricted over an open `W` of `T_A`.** -/
abbrev firstOrderCrysFunctorRestrict (W : A.obj.thickening.target.scheme.Opens) :
    (firstOrderThickeningCrysObject S B).restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ W) ⟶
      (firstOrderThickeningCrysObject S A).restrictOpen W :=
  CrystallineThickening.restrictOpenMap (firstOrderCrysFunctorMap g) W

/-- A square of restrictions commutes if the underlying square does and the restrictions are
compatible with the structure morphisms, the last of which is monic. -/
private theorem comp_eq_comp_of_restrict_squares {C : Type*} [Category C]
    {X Y V Z X₀ Y₀ V₀ Z₀ : C} {h : X ⟶ Y} {r₁ : Y ⟶ Z} {r₂ : X ⟶ V} {r₃ : V ⟶ Z}
    {mX : X ⟶ X₀} {mY : Y ⟶ Y₀} {mV : V ⟶ V₀} {m : Z ⟶ Z₀} {g' : X₀ ⟶ Y₀} {p : Y₀ ⟶ Z₀}
    {q : X₀ ⟶ V₀} {g : V₀ ⟶ Z₀} [Mono m] (hh : h ≫ mY = mX ≫ g') (hp : g' ≫ p = q ≫ g)
    (e₁ : r₁ ≫ m = mY ≫ p) (e₂ : r₂ ≫ mV = mX ≫ q) (e₃ : r₃ ≫ m = mV ≫ g) :
    h ≫ r₁ = r₂ ≫ r₃ := by
  rw [← cancel_mono m, Category.assoc, Category.assoc, e₁, e₃, reassoc_of% hh, reassoc_of% e₂, hp]

/-- For a morphism `h` over the induced morphism `g'` of first-order thickenings,
`h ∘ p₀ = p₀ ∘ g` over an open. -/
theorem comp_firstOrderCrysRestrictP₀_of_comp_restrictOpenHom
    (W : A.obj.thickening.target.scheme.Opens)
    (h : (firstOrderThickeningCrysObject S B).restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ W) ⟶
      (firstOrderThickeningCrysObject S A).restrictOpen W)
    (hh : h ≫ (firstOrderThickeningCrysObject S A).restrictOpenHom W =
      (firstOrderThickeningCrysObject S B).restrictOpenHom (g.hom.targetHom.hom ⁻¹ᵁ W) ≫
        firstOrderCrysFunctorMap g) :
    h ≫ firstOrderCrysRestrictP₀ A W =
      firstOrderCrysRestrictP₀ B (g.hom.targetHom.hom ⁻¹ᵁ W) ≫
        CrystallineThickening.restrictOpenMap g W := by
  have hP₀ : firstOrderCrysFunctorMap g ≫ firstOrderThickeningCrysP₀ S A =
      firstOrderThickeningCrysP₀ S B ≫ g :=
    ObjectProperty.hom_ext _ (firstOrderThickeningSiteMap_comp_P₀ g.hom)
  exact comp_eq_comp_of_restrict_squares hh hP₀
    (CrystallineThickening.restrictOpenMap_restrictOpenHom _ W)
    (CrystallineThickening.restrictOpenMap_restrictOpenHom _ _)
    (CrystallineThickening.restrictOpenMap_restrictOpenHom _ W)

/-- For a morphism `h` over the induced morphism `g'` of first-order thickenings,
`h ∘ p₁ = p₁ ∘ g` over an open. -/
theorem comp_firstOrderCrysRestrictP₁_of_comp_restrictOpenHom
    (W : A.obj.thickening.target.scheme.Opens)
    (h : (firstOrderThickeningCrysObject S B).restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ W) ⟶
      (firstOrderThickeningCrysObject S A).restrictOpen W)
    (hh : h ≫ (firstOrderThickeningCrysObject S A).restrictOpenHom W =
      (firstOrderThickeningCrysObject S B).restrictOpenHom (g.hom.targetHom.hom ⁻¹ᵁ W) ≫
        firstOrderCrysFunctorMap g) :
    h ≫ firstOrderCrysRestrictP₁ A W =
      firstOrderCrysRestrictP₁ B (g.hom.targetHom.hom ⁻¹ᵁ W) ≫
        CrystallineThickening.restrictOpenMap g W := by
  have hP₁ : firstOrderCrysFunctorMap g ≫ firstOrderThickeningCrysP₁ S A =
      firstOrderThickeningCrysP₁ S B ≫ g :=
    ObjectProperty.hom_ext _ (firstOrderThickeningSiteMap_comp_P₁ g.hom)
  exact comp_eq_comp_of_restrict_squares hh hP₁
    (CrystallineThickening.restrictOpenMap_restrictOpenHom _ W)
    (CrystallineThickening.restrictOpenMap_restrictOpenHom _ _)
    (CrystallineThickening.restrictOpenMap_restrictOpenHom _ W)

variable (M : SheafOfModules.{u} (structureSheaf S))

/-- **The recipe `p₁^* s - p₀^* s` is natural in the object of `Cris(X/S)`**: for a morphism
`g : (U_B, T_B, δ_B) ⟶ (U_A, T_A, δ_A)`, an open `W` of `T_A`, and any morphism
`h : T_B'|_{g⁻¹ W} ⟶ T_A'|_W` lying over the induced morphism `g' : T_B' ⟶ T_A'` of the
first-order thickenings, restricting `∇(s)` along `h` is `∇(g^* s)`.  This is the source's
"functorial in `T` because the construction of `T'` is functorial in `T`". -/
theorem crystalConnectionRaw_naturality_obj (W : A.obj.thickening.target.scheme.Opens)
    (h : (firstOrderThickeningCrysObject S B).restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ W) ⟶
      (firstOrderThickeningCrysObject S A).restrictOpen W)
    (hh : h ≫ (firstOrderThickeningCrysObject S A).restrictOpenHom W =
      (firstOrderThickeningCrysObject S B).restrictOpenHom (g.hom.targetHom.hom ⁻¹ᵁ W) ≫
        firstOrderCrysFunctorMap g)
    (s : M.val.obj (op (A.restrictOpen W))) :
    crystalRestrict M h (crystalConnectionRaw M A W s) =
      crystalConnectionRaw M B (g.hom.targetHom.hom ⁻¹ᵁ W)
        (crystalRestrict M (CrystallineThickening.restrictOpenMap g W) s) := by
  rw [crystalRestrict_crystalConnectionRaw M A W h _ _
      (comp_firstOrderCrysRestrictP₀_of_comp_restrictOpenHom g W h hh)
      (comp_firstOrderCrysRestrictP₁_of_comp_restrictOpenHom g W h hh),
    crystalConnectionRaw_apply, crystalRestrict_comp, crystalRestrict_comp]
  rfl

variable {M}

/-- **Stacks Project, Tag 07J6: the connection is functorial in the object of `Cris(X/S)`.**  For a
morphism `g : (U_B, T_B, δ_B) ⟶ (U_A, T_A, δ_A)` of `Cris(X/S)`, an open `W` of `T_A`, a section
`s` of `F` over `(U_A, T_A, δ_A)|_W` and any morphism `h` over the induced morphism
`g' : T_B' ⟶ T_A'` of first-order thickenings, the canonical morphism
`F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ p₀_* F_{T'}` carries `∇_B(g^* s)` to the restriction along `h` of the
image of `∇_A(s)`.  The canonical morphism is injective (`...injective_firstOrderTensorInclusion`),
so this determines `∇_B(g^* s)` from `∇_A(s)`: the family of connections is compatible with the
transition maps of `T ↦ F_T ⊗ Ω_{T/S,δ}` induced from those of `F` on the first-order
thickenings, which is how the source deduces that it is a connection on `Cris(X/S)`. -/
theorem crystalConnectionApp_naturality_obj (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (h : (firstOrderThickeningCrysObject S B).restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ W) ⟶
      (firstOrderThickeningCrysObject S A).restrictOpen W)
    (hh : h ≫ (firstOrderThickeningCrysObject S A).restrictOpenHom W =
      (firstOrderThickeningCrysObject S B).restrictOpenHom (g.hom.targetHom.hom ⁻¹ᵁ W) ≫
        firstOrderCrysFunctorMap g)
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) :
    firstOrderTensorSec M B (g.hom.targetHom.hom ⁻¹ᵁ W)
        (crystalConnectionApp B hM (g.hom.targetHom.hom ⁻¹ᵁ W)
          (crystalRestrict M (CrystallineThickening.restrictOpenMap g W) s)) =
      crystalRestrict M h (firstOrderTensorSec M A W (crystalConnectionApp A hM W s)) := by
  rw [firstOrderTensorSec_crystalConnectionApp]
  exact (firstOrderTensorSec_crystalConnectionApp B hM (g.hom.targetHom.hom ⁻¹ᵁ W) _).trans
    (crystalConnectionRaw_naturality_obj g M W h hh s).symm

/-- A morphism `h` as in `...SmallSite.crystalConnectionApp_naturality_obj` exists: the
restriction of `T_B' ⟶ T_A'` over `W` factors through `T_A'|_W`. -/
theorem exists_firstOrderCrysFunctorRestrict (W : A.obj.thickening.target.scheme.Opens) :
    ∃ h : (firstOrderThickeningCrysObject S B).restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ W) ⟶
      (firstOrderThickeningCrysObject S A).restrictOpen W,
      h ≫ (firstOrderThickeningCrysObject S A).restrictOpenHom W =
        (firstOrderThickeningCrysObject S B).restrictOpenHom (g.hom.targetHom.hom ⁻¹ᵁ W) ≫
          firstOrderCrysFunctorMap g :=
  ⟨CrystallineThickening.restrictOpenMap (firstOrderCrysFunctorMap g) W,
    CrystallineThickening.restrictOpenMap_restrictOpenHom (firstOrderCrysFunctorMap g) W⟩

/-! ### The transition maps of `T ↦ F_T ⊗ Ω_{T/S,δ}` -/

/-- `g'` restricted over `W` composed with... the diagonal relation `i_B ≫ g' = g ≫ i_A` over an
open. -/
theorem firstOrderCrysRestrictι_comp_functorRestrict (W : A.obj.thickening.target.scheme.Opens) :
    firstOrderCrysRestrictι B (g.hom.targetHom.hom ⁻¹ᵁ W) ≫ firstOrderCrysFunctorRestrict g W =
      CrystallineThickening.restrictOpenMap g W ≫ firstOrderCrysRestrictι A W := by
  have hι : firstOrderThickeningCrysι S B ≫ firstOrderCrysFunctorMap g =
      g ≫ firstOrderThickeningCrysι S A :=
    ObjectProperty.hom_ext _ (firstOrderThickeningSiteι_comp_siteMap g.hom)
  have := CrystallineThickening.mono_restrictOpenHom (firstOrderThickeningCrysObject S A) W
  exact comp_eq_comp_of_restrict_squares
    (CrystallineThickening.restrictOpenMap_restrictOpenHom (firstOrderThickeningCrysι S B) _) hι
    (CrystallineThickening.restrictOpenMap_restrictOpenHom (firstOrderCrysFunctorMap g) W)
    (CrystallineThickening.restrictOpenMap_restrictOpenHom g W)
    (CrystallineThickening.restrictOpenMap_restrictOpenHom (firstOrderThickeningCrysι S A) W)

/-- **The transition map `F_{T_A} ⊗ Ω_{T_A} ⟶ g_*(F_{T_B} ⊗ Ω_{T_B})` along a morphism `g` of
`Cris(X/S)`**, on the sections over an open `W` of `T_A`: the restriction along the induced
morphism of first-order thickenings, read back in `F_{T_B} ⊗ Ω_{T_B}` through the identification
of [Stacks, Tag 07J6].  `...SmallSite.crystalTensorTransition_tmul` shows it is
`x ⊗ ω ↦ g^* x ⊗ g^* ω`. -/
def crystalTensorTransition (hM : IsSheafCrystal M) (W : A.obj.thickening.target.scheme.Opens) :
    (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) →+
      (firstOrderThickeningTensorDifferentials B.obj.thickening.target S.S.scheme
        B.obj.toBase.hom (crysAmbientSchemeModules M B)).val.obj
          (op (g.hom.targetHom.hom ⁻¹ᵁ W)) :=
  (schemeModulesValAppHom (firstOrderKernelIso M B hM).inv (op (g.hom.targetHom.hom ⁻¹ᵁ W))).comp
    ((schemeModulesValAppHom (firstOrderAmbientRetraction M B)
        (op (g.hom.targetHom.hom ⁻¹ᵁ W))).comp
      ((crystalRestrict M (firstOrderCrysFunctorRestrict g W)).toAddMonoidHom.comp
        (schemeModulesValAppHom (firstOrderTensorInclusion M A) (op W))))

/-- **The transition map is the restriction along `g'` read in `F ⊗ Ω`**: the canonical morphism
carries it to the restriction along `T_B' ⟶ T_A'` of the canonical morphism. -/
theorem firstOrderTensorSec_crystalTensorTransition (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    firstOrderTensorSec M B (g.hom.targetHom.hom ⁻¹ᵁ W) (crystalTensorTransition g hM W z) =
      crystalRestrict M (firstOrderCrysFunctorRestrict g W) (firstOrderTensorSec M A W z) := by
  set y := crystalRestrict M (firstOrderCrysFunctorRestrict g W) (firstOrderTensorSec M A W z)
  have hι : (firstOrderAmbientProjMap₀ M B).val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W)) y = 0 := by
    have h0 : (firstOrderAmbientProjMap₀ M A).val.app (op W) (firstOrderTensorSec M A W z) = 0 :=
      congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app (op W) z)
        (firstOrderTensorInclusion_projMap₀ M A) |>.trans rfl
    have e : (firstOrderAmbientProjMap₀ M B).val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W)) y =
        crystalRestrict M (CrystallineThickening.restrictOpenMap g W)
          ((firstOrderAmbientProjMap₀ M A).val.app (op W) (firstOrderTensorSec M A W z)) := by
      refine (crystalRestrict_comp M _ _ _).trans ?_
      refine (congrArg (fun k ↦ crystalRestrict M k (firstOrderTensorSec M A W z))
        (firstOrderCrysRestrictι_comp_functorRestrict g W)).trans ?_
      exact (crystalRestrict_comp M _ _ _).symm
    rw [e, h0]
    exact map_zero (crystalRestrict M (CrystallineThickening.restrictOpenMap g W))
  have hhom : ∀ w : (firstOrderAmbientKernel M B).val.obj (op (g.hom.targetHom.hom ⁻¹ᵁ W)),
      (firstOrderKernelComparison M B).val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W))
        ((firstOrderKernelIso M B hM).inv.val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W)) w) = w :=
    fun w ↦ congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app (op (g.hom.targetHom.hom ⁻¹ᵁ W)) w)
      (firstOrderKernelIso M B hM).inv_hom_id
  have hsub : ∀ y', (firstOrderAmbientRetraction M B ≫
        kernel.ι (firstOrderAmbientProjMap₀ M B)).val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W)) y' =
      y' - (firstOrderAmbientInclMap M B).val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W))
        ((firstOrderAmbientProjMap₀ M B).val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W)) y') :=
    fun y' ↦ (congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app
      (op (g.hom.targetHom.hom ⁻¹ᵁ W)) y') (firstOrderAmbientRetraction_ι M B)).trans rfl
  have e1 : firstOrderTensorSec M B (g.hom.targetHom.hom ⁻¹ᵁ W)
        (crystalTensorTransition g hM W z) =
      (kernel.ι (firstOrderAmbientProjMap₀ M B)).val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W))
        ((firstOrderKernelComparison M B).val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W))
          ((firstOrderKernelIso M B hM).inv.val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W))
            ((firstOrderAmbientRetraction M B).val.app (op (g.hom.targetHom.hom ⁻¹ᵁ W)) y))) :=
    rfl
  rw [e1, hhom]
  refine (hsub y).trans ?_
  rw [hι, map_zero]
  exact sub_zero _

/-- **Stacks Project, Tag 07J6: the connection commutes with the transition maps of `F` and of
`F ⊗ Ω`** along every morphism `g` of `Cris(X/S)`: `τ_g (∇_A s) = ∇_B (g^* s)`.  This is the
clause of the source that the collection of connections over the objects of the site "is
functorial in `T`", which is what makes it a connection on `Cris(X/S)`. -/
theorem crystalTensorTransition_crystalConnectionApp (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) :
    crystalTensorTransition g hM W (crystalConnectionApp A hM W s) =
      crystalConnectionApp B hM (g.hom.targetHom.hom ⁻¹ᵁ W)
        (crystalRestrict M (CrystallineThickening.restrictOpenMap g W) s) :=
  injective_firstOrderTensorInclusion M B hM (g.hom.targetHom.hom ⁻¹ᵁ W)
    ((firstOrderTensorSec_crystalTensorTransition g hM W _).trans
      (crystalConnectionApp_naturality_obj g hM W _
        (CrystallineThickening.restrictOpenMap_restrictOpenHom (firstOrderCrysFunctorMap g) W)
        s).symm)

/-- **`g' ∘ p₀ = p₀ ∘ g` over an open**. -/
theorem firstOrderCrysFunctorRestrict_comp_P₀ (W : A.obj.thickening.target.scheme.Opens) :
    firstOrderCrysFunctorRestrict g W ≫ firstOrderCrysRestrictP₀ A W =
      firstOrderCrysRestrictP₀ B (g.hom.targetHom.hom ⁻¹ᵁ W) ≫
        CrystallineThickening.restrictOpenMap g W :=
  comp_firstOrderCrysRestrictP₀_of_comp_restrictOpenHom g W _
    (CrystallineThickening.restrictOpenMap_restrictOpenHom (firstOrderCrysFunctorMap g) W)

variable (M) in
/-- `g'^* y` for a section `y` of `F_{T_A'}` over `W`, a section of `F_{T_B'}` over `g⁻¹ W`. -/
abbrev firstOrderFunctorSec (W : A.obj.thickening.target.scheme.Opens) (y : FirstOrderSec M A W) :
    FirstOrderSec M B (g.hom.targetHom.hom ⁻¹ᵁ W) :=
  crystalRestrict M (firstOrderCrysFunctorRestrict g W) y

/-- The map `(b, ω) ↦ (g^♯ b, g^* ω)` of the structure sheaves of the first-order thickenings. -/
abbrev firstOrderFunctorScalar (W : A.obj.thickening.target.scheme.Opens)
    (r : FirstOrderRing A W) : FirstOrderRing B (g.hom.targetHom.hom ⁻¹ᵁ W) :=
  (firstOrderThickeningMapApp g.hom (op W)).hom r

variable (M) in
/-- `g'^*` is semilinear over the map `(b, ω) ↦ (g^♯ b, g^* ω)` of the structure sheaves. -/
theorem firstOrderFunctorSec_smul (W : A.obj.thickening.target.scheme.Opens)
    (r : FirstOrderRing A W) (y : FirstOrderSec M A W) :
    firstOrderFunctorSec g M W (r • y) =
      firstOrderFunctorScalar g W r • firstOrderFunctorSec g M W y :=
  ((crysAmbientFMap M (firstOrderCrysFunctorMap g)).val.app (op W)).hom.map_smul r y

/-- **The transition map on a local pure tensor: `τ_g (x ⊗ ω) = g^* x ⊗ g^* ω`.**  So
`...SmallSite.crystalTensorTransition` is the transition map of `T ↦ F_T ⊗ Ω_{T/S,δ}`: the tensor
product of the transition map of `F` and the pullback of divided power differentials. -/
theorem crystalTensorTransition_tmul (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W))
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    crystalTensorTransition g hM W (firstOrderTensorTmul M A W x ω) =
      firstOrderTensorTmul M B (g.hom.targetHom.hom ⁻¹ᵁ W)
        (crystalRestrict M (CrystallineThickening.restrictOpenMap g W) x)
        ((dpDifferentialsMapSheaf g.hom).app W ω) := by
  apply injective_firstOrderTensorInclusion M B hM (g.hom.targetHom.hom ⁻¹ᵁ W)
  refine (firstOrderTensorSec_crystalTensorTransition g hM W _).trans ?_
  refine Eq.trans ?_ (firstOrderTensorSec_tmul M B (g.hom.targetHom.hom ⁻¹ᵁ W) _ _).symm
  refine (congrArg (firstOrderFunctorSec g M W) (firstOrderTensorSec_tmul M A W x ω)).trans ?_
  refine (firstOrderFunctorSec_smul g M W _ _).trans ?_
  have hsc : firstOrderFunctorScalar g W (firstOrderIdealSec A W ω) =
      firstOrderIdealSec B (g.hom.targetHom.hom ⁻¹ᵁ W)
        ((dpDifferentialsMapSheaf g.hom).app W ω) :=
    PresheafOfModules.sqZeroExt_ext (map_zero ((g.hom.targetHom.hom).app W).hom) rfl
  have hP : firstOrderFunctorSec g M W (firstOrderP₀Sec M A W x) =
      firstOrderP₀Sec M B (g.hom.targetHom.hom ⁻¹ᵁ W)
        (crystalRestrict M (CrystallineThickening.restrictOpenMap g W) x) :=
    (crystalRestrict_comp M _ _ _).trans
      ((congrArg (fun k ↦ crystalRestrict M k x)
        (firstOrderCrysFunctorRestrict_comp_P₀ g W)).trans (crystalRestrict_comp M _ _ _).symm)
  rw [hsc, hP]

/-- **The transition map commutes with restriction to a smaller open.** -/
theorem crystalTensorTransition_naturality (hM : IsSheafCrystal M)
    {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    (firstOrderThickeningTensorDifferentials B.obj.thickening.target S.S.scheme
          B.obj.toBase.hom (crysAmbientSchemeModules M B)).val.map
        (homOfLE (g.hom.targetHom.hom.preimage_mono h)).op (crystalTensorTransition g hM W z) =
      crystalTensorTransition g hM W'
        ((firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op z) := by
  apply injective_firstOrderTensorInclusion M B hM (g.hom.targetHom.hom ⁻¹ᵁ W')
  refine Eq.trans ?_ (firstOrderTensorSec_crystalTensorTransition g hM W' _).symm
  refine (PresheafOfModules.naturality_apply (firstOrderTensorInclusion M B).val
    (homOfLE (g.hom.targetHom.hom.preimage_mono h)).op _).trans ?_
  refine (congrArg _ (firstOrderTensorSec_crystalTensorTransition g hM W z)).trans ?_
  refine Eq.trans ?_ (congrArg (crystalRestrict M (firstOrderCrysFunctorRestrict g W'))
    (PresheafOfModules.naturality_apply (firstOrderTensorInclusion M A).val (homOfLE h).op
      z).symm)
  exact (crystalRestrict_comp M
      (CrystallineThickening.restrictOpenLE (firstOrderThickeningCrysObject S B)
        ((firstOrderCrysFunctorMap g).hom.targetHom.hom.preimage_mono h))
      (CrystallineThickening.restrictOpenMap (firstOrderCrysFunctorMap g) W)
      (firstOrderTensorSec M A W z)).trans
    ((congrArg (fun k ↦ crystalRestrict M k (firstOrderTensorSec M A W z))
      (CrystallineThickening.restrictOpenLE_restrictOpenMap (firstOrderCrysFunctorMap g)
        h)).trans (crystalRestrict_comp M
      (CrystallineThickening.restrictOpenMap (firstOrderCrysFunctorMap g) W')
      (CrystallineThickening.restrictOpenLE (firstOrderThickeningCrysObject S A) h)
      (firstOrderTensorSec M A W z)).symm)

/-- **The transition map is the only compatible family of additive maps given by
`x ⊗ ω ↦ g^* x ⊗ g^* ω`**: it is the transition map of `T ↦ F_T ⊗ Ω_{T/S,δ}`. -/
theorem eq_crystalTensorTransition (hM : IsSheafCrystal M)
    (E : ∀ W : A.obj.thickening.target.scheme.Opens,
      (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) →+
      (firstOrderThickeningTensorDifferentials B.obj.thickening.target S.S.scheme
        B.obj.toBase.hom (crysAmbientSchemeModules M B)).val.obj
          (op (g.hom.targetHom.hom ⁻¹ᵁ W)))
    (hE : ∀ {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W) z,
      (firstOrderThickeningTensorDifferentials B.obj.thickening.target S.S.scheme
          B.obj.toBase.hom (crysAmbientSchemeModules M B)).val.map
          (homOfLE (g.hom.targetHom.hom.preimage_mono h)).op (E W z) =
        E W' ((firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op z))
    (hrule : ∀ (W : A.obj.thickening.target.scheme.Opens) x ω,
      E W (firstOrderTensorTmul M A W x ω) =
        firstOrderTensorTmul M B (g.hom.targetHom.hom ⁻¹ᵁ W)
          (crystalRestrict M (CrystallineThickening.restrictOpenMap g W) x)
          ((dpDifferentialsMapSheaf g.hom).app W ω))
    (W : A.obj.thickening.target.scheme.Opens) :
    E W = crystalTensorTransition g hM W := by
  ext z
  exact tensor_sections_ext (M := crysAmbientSchemeModules M A)
    (N := dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom)
    (G := (Scheme.Modules.pushforward g.hom.targetHom.hom).obj
      (firstOrderThickeningTensorDifferentials B.obj.thickening.target S.S.scheme
        B.obj.toBase.hom (crysAmbientSchemeModules M B))) (W := W)
    (fun V _ ↦ E V) (fun V _ ↦ crystalTensorTransition g hM V)
    (fun V V' _ _ h y ↦ hE h y)
    (fun V V' _ _ h y ↦ crystalTensorTransition_naturality g hM h y)
    (fun V _ a b ↦ (hrule V a b).trans (crystalTensorTransition_tmul g hM V a b).symm) z

end SmallSite

end GlobalCrystallineSituation

end Crystalline

end

end
