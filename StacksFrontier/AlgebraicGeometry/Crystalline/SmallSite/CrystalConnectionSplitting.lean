module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderAmbientSplitting
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineComparisonAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme

/-!
# The restriction of a module on `Cris(X/S)` along the first-order universal thickening splits

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` and let `(U, T, δ)` be an object of
`Cris(X/S)` with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2], again an
object of `Cris(X/S)`.

The ambient schemes `T` and `T'` have the same underlying topological space, and `i : T ⟶ T'`,
`p₀ : T' ⟶ T` are the identity on it with `p₀ ∘ i = id`.  So the restriction of scalars
`p₀_* F_{T'}` of `F_{T'}` along `𝒪_T ⟶ 𝒪_{T'}` is the direct sum of `F_T` and of the kernel of
`i^* : p₀_* F_{T'} ⟶ F_T`,

`p₀_* F_{T'} ≅ ker(i^*) ⊞ F_T`,

split by `p₀^*`.  This is the module counterpart of the splitting
`𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}` of [Stacks, Tag 07J2], with no hypothesis on `F`; it is the first step
of the construction of the connection of [Stacks, Tag 07J6], which reads `∇(s) = p₁^* s - p₀^* s`
inside that kernel.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crystalRestrict` — the restriction map of `F` along a morphism of `Cris(X/S)`, as a semilinear
  map.
* `crysAmbientFMap` — **the `f`-map `F_{T'} ⟶ g_* F_T` of [Stacks, Tag 07IQ], read between
  sheaves of modules on the ambient schemes.**  Over an open `W` it is the restriction of `F`
  along the restriction of `g` over `W`.
* `firstOrderAmbientProjMap₀` and `firstOrderAmbientInclMap` — the maps `i^*` and `p₀^*`.
* `firstOrderAmbientKernel` — the kernel of `i^* : p₀_* F_{T'} ⟶ F_T`.
* `firstOrderAmbientSplitting` — the splitting of `0 ⟶ ker ⟶ p₀_* F_{T'} ⟶ F_T ⟶ 0` by `p₀^*`.

## Main results

* `firstOrderAmbientInclMap_comp_projMap` — `i^*` is a retraction of `p₀^*`.
* `firstOrderAmbientBiprodIso` — `p₀_* F_{T'} ≅ ker(i^*) ⊞ F_T`.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace SmallSite

open CohomologyRestriction

/-! ### Restriction along a morphism of `Cris(X/S)`, as a semilinear map -/

variable (M : SheafOfModules.{u} (structureSheaf S))

/-- **The restriction map of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` along a morphism of the
site**, as a map semilinear over the restriction map of the structure sheaf.  It is
`...SmallSite.crysSiteRestrict` with its semilinearity recorded in the type. -/
abbrev crystalRestrict {A B : CrystallineThickening S} (g : A ⟶ B) :
    M.val.obj (op B) →ₛₗ[crysSheafRingMap g.hom] M.val.obj (op A) :=
  M.val.restrictₛₗ g.op

/-- Restricting along a composite of morphisms of `Cris(X/S)` is restricting along the two
factors. -/
theorem crystalRestrict_comp {A B C : CrystallineThickening S} (g : A ⟶ B) (h : B ⟶ C)
    (x : M.val.obj (op C)) :
    crystalRestrict M g (crystalRestrict M h x) = crystalRestrict M (g ≫ h) x := by
  have hx := M.val.map_comp_apply h.op g.op x
  rw [← op_comp] at hx
  exact hx.symm

/-- Restricting along an identity of `Cris(X/S)` is the identity. -/
theorem crystalRestrict_id (A : CrystallineThickening S) (x : M.val.obj (op A)) :
    crystalRestrict M (𝟙 A) x = x :=
  PresheafOfModules.map_id_apply M.val (op A) x

/-- Restriction along two morphisms of `Cris(X/S)` with the same underlying morphism of
`CRIS(X/S)` agree. -/
theorem crystalRestrict_congr {A B : CrystallineThickening S} {g g' : A ⟶ B} (h : g.hom = g'.hom)
    (x : M.val.obj (op B)) : crystalRestrict M g x = crystalRestrict M g' x := by
  rw [ObjectProperty.hom_ext _ h]

/-! ### The `f`-map of [Stacks, Tag 07IQ] on the ambient schemes -/

/-- **Stacks Project, Tag 07IQ.**  The `f`-map `F_{T'} ⟶ g_* F_T` of a sheaf of
`𝒪_{X/S}`-modules on `Cris(X/S)` along a morphism `g` of `Cris(X/S)`, read between sheaves of
modules on the *ambient schemes*: the scalars are the structure sheaves of `T` and `T'` and the
pushforward is Mathlib's pushforward of modules along the morphism of schemes `T ⟶ T'`.

It is the `f`-map `...SmallSite.CohomologyRestriction.moduleFMapSheaf`, whose scalars live in the
restrictions of `𝒪_{X/S}` to the two ambient schemes, carried across the identifications of
those restrictions with the structure sheaves by
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePushforwardIso`.  Both steps are
the identity on sections, so this map is still the restriction map of `F` along the restriction
of `g` over each open. -/
def crysAmbientFMap {A B : CrystallineThickening S} (g : A ⟶ B) :
    crysAmbientSchemeModules M B ⟶
      (Scheme.Modules.pushforward g.hom.targetHom.hom).obj (crysAmbientSchemeModules M A) :=
  (SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso B.obj).inv).map
      (moduleFMapSheaf M g) ≫
    (Thickening.ambientSchemePushforwardIso g.hom).hom.app (moduleRestrictionSheaf M A)

/-- **The `f`-map on the ambient schemes is, over an open `W`, the restriction map of `F` along
the restriction of the morphism over `W`.** -/
theorem crysAmbientFMap_val_app {A B : CrystallineThickening S} (g : A ⟶ B)
    (W : (B.obj.thickening.target.scheme.Opens)ᵒᵖ)
    (x : (crysAmbientSchemeModules M B).val.obj W) :
    (crysAmbientFMap M g).val.app W x =
      crystalRestrict M (CrystallineThickening.restrictOpenMap g W.unop) x := rfl

/-! ### The morphisms of the first-order thickening, restricted over an open -/

variable (A : CrystallineThickening S)

/-- **`p₀ ∘ i = id`, restricted over an open of `T`.** -/
theorem restrictOpenMap_crysι_comp_crysP₀ (W : A.obj.thickening.target.scheme.Opens) :
    CrystallineThickening.restrictOpenMap (firstOrderThickeningCrysι S A)
          ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W) ≫
        CrystallineThickening.restrictOpenMap (firstOrderThickeningCrysP₀ S A) W =
      𝟙 (A.restrictOpen W) :=
  ObjectProperty.hom_ext _ (restrictOpenMap_siteι_comp_siteP₀ A.obj W)

/-! ### The two maps between `F_T` and `F_{T'}` -/

/-- **`i^* : F_{T'} ⟶ i_* F_T`**, the restriction along the diagonal `i : T ⟶ T'` of
[Stacks, Tag 07J2], as a morphism of sheaves of `𝒪_{T'}`-modules. -/
abbrev firstOrderAmbientProjMap :
    crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A) ⟶
      (Scheme.Modules.pushforward (firstOrderThickeningCrysι S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M A) :=
  crysAmbientFMap M (firstOrderThickeningCrysι S A)

/-- **`p₀^* : F_T ⟶ p₀_* F_{T'}`**, the restriction along `p₀ : T' ⟶ T` of [Stacks, Tag 07J2],
as a morphism of sheaves of `𝒪_T`-modules. -/
abbrev firstOrderAmbientInclMap :
    crysAmbientSchemeModules M A ⟶
      (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)) :=
  crysAmbientFMap M (firstOrderThickeningCrysP₀ S A)

/-- **`i^*`, read over the scalars of `T`.**  The restriction of scalars along `p₀` of
`...SmallSite.firstOrderAmbientProjMap`: a morphism of sheaves of `𝒪_T`-modules
`p₀_* F_{T'} ⟶ F_T`, the two restrictions of scalars composing to the identity because
`p₀ ∘ i = id`. -/
abbrev firstOrderAmbientProjMap₀ :
    (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)) ⟶
      crysAmbientSchemeModules M A :=
  (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).map
    (firstOrderAmbientProjMap M A)

/-- **`i^*` is a retraction of `p₀^*`.**  Over an open `W` both composites are the restriction of
`F` along the composite of the restrictions of `i` and `p₀` over `W`, which is an identity by
`...SmallSite.restrictOpenMap_crysι_comp_crysP₀`. -/
theorem firstOrderAmbientInclMap_comp_projMap :
    firstOrderAmbientInclMap M A ≫ firstOrderAmbientProjMap₀ M A =
      𝟙 (crysAmbientSchemeModules M A) := by
  ext W x
  exact (crystalRestrict_comp M _ _ x).trans
    ((crystalRestrict_congr M (congrArg (·.hom) (restrictOpenMap_crysι_comp_crysP₀ A W))
      x).trans (crystalRestrict_id M _ x))

/-! ### The kernel and the splitting -/

/-- **The kernel of `i^* : p₀_* F_{T'} ⟶ F_T`**, as a sheaf of `𝒪_T`-modules on the ambient
scheme of the object.  This is the sheaf that [Stacks, Tag 07J6] identifies with
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}`; the identification is
`...SmallSite.isIso_firstOrderKernelComparison_of_isSheafCrystal`. -/
abbrev firstOrderAmbientKernel : A.obj.thickening.target.scheme.Modules :=
  kernel (firstOrderAmbientProjMap₀ M A)

/-- The short complex `0 ⟶ ker(i^*) ⟶ p₀_* F_{T'} ⟶ F_T ⟶ 0` of sheaves of `𝒪_T`-modules. -/
def firstOrderAmbientShortComplex : ShortComplex A.obj.thickening.target.scheme.Modules :=
  ShortComplex.mk (kernel.ι (firstOrderAmbientProjMap₀ M A)) (firstOrderAmbientProjMap₀ M A)
    (kernel.condition _)

/-- **The retraction of the kernel inclusion.**  The idempotent `1 - i^* ∘ p₀^*` is killed by
`i^*`, because `i^* ∘ p₀^* = 1`, so it factors through the kernel. -/
def firstOrderAmbientRetraction :
    (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)) ⟶
      firstOrderAmbientKernel M A :=
  kernel.lift (firstOrderAmbientProjMap₀ M A)
    (𝟙 _ - firstOrderAmbientProjMap₀ M A ≫ firstOrderAmbientInclMap M A) (by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
        firstOrderAmbientInclMap_comp_projMap, Category.comp_id, sub_self])

/-- The retraction followed by the kernel inclusion is `1 - p₀^* ∘ i^*`. -/
@[reassoc (attr := simp)]
theorem firstOrderAmbientRetraction_ι
    (M : SheafOfModules.{u} (structureSheaf S)) (A : CrystallineThickening S) :
    firstOrderAmbientRetraction M A ≫ kernel.ι (firstOrderAmbientProjMap₀ M A) =
      𝟙 _ - firstOrderAmbientProjMap₀ M A ≫ firstOrderAmbientInclMap M A :=
  kernel.lift_ι _ _ _

/-- **The short complex is split by `p₀^*`.**  The retraction of the kernel inclusion is the
idempotent `1 - i^* ∘ p₀^*`, which kills `i^*` because `i^* ∘ p₀^* = 1`. -/
def firstOrderAmbientSplitting
    (M : SheafOfModules.{u} (structureSheaf S)) (A : CrystallineThickening S) :
    (firstOrderAmbientShortComplex M A).Splitting where
  r := firstOrderAmbientRetraction M A
  s := firstOrderAmbientInclMap M A
  f_r := by
    change kernel.ι (firstOrderAmbientProjMap₀ M A) ≫ firstOrderAmbientRetraction M A = 𝟙 _
    refine (cancel_mono (kernel.ι (firstOrderAmbientProjMap₀ M A))).1 ?_
    rw [Category.assoc, firstOrderAmbientRetraction_ι, Category.id_comp, Preadditive.comp_sub,
      Category.comp_id, ← Category.assoc, kernel.condition, Limits.zero_comp, sub_zero]
  s_g := firstOrderAmbientInclMap_comp_projMap M A
  id := by
    change firstOrderAmbientRetraction M A ≫ kernel.ι (firstOrderAmbientProjMap₀ M A) +
        firstOrderAmbientProjMap₀ M A ≫ firstOrderAmbientInclMap M A = 𝟙 _
    rw [firstOrderAmbientRetraction_ι, sub_add_cancel]

/-- **`p₀_* F_{T'}` is the direct sum of the kernel of `i^*` and of `F_T`.**  This is the
splitting of the square-zero extension `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}` of [Stacks, Tag 07J2] carried
to the module, with no hypothesis on `F` and none on the object. -/
def firstOrderAmbientBiprodIso :
    (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)) ≅
      firstOrderAmbientKernel M A ⊞ crysAmbientSchemeModules M A :=
  (firstOrderAmbientSplitting M A).isoBinaryBiproduct

/-- **The short complex is exact**, so the kernel of `i^*` is also the cokernel of `p₀^*`. -/
theorem exact_firstOrderAmbientShortComplex
    (M : SheafOfModules.{u} (structureSheaf S)) (A : CrystallineThickening S) :
    (firstOrderAmbientShortComplex M A).Exact :=
  (firstOrderAmbientSplitting M A).exact

/-- **`p₀^*` is a split monomorphism.** -/
theorem isSplitMono_firstOrderAmbientInclMap
    (M : SheafOfModules.{u} (structureSheaf S)) (A : CrystallineThickening S) :
    IsSplitMono (firstOrderAmbientInclMap M A) :=
  ⟨⟨⟨firstOrderAmbientProjMap₀ M A, firstOrderAmbientInclMap_comp_projMap M A⟩⟩⟩

/-- **`i^*` is a split epimorphism**, so `F_{T'} ⟶ i_* F_T` is surjective on sections over every
open of `T` after restriction of scalars along `p₀`. -/
theorem isSplitEpi_firstOrderAmbientProjMap₀
    (M : SheafOfModules.{u} (structureSheaf S)) (A : CrystallineThickening S) :
    IsSplitEpi (firstOrderAmbientProjMap₀ M A) :=
  ⟨⟨⟨firstOrderAmbientInclMap M A, firstOrderAmbientInclMap_comp_projMap M A⟩⟩⟩

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
