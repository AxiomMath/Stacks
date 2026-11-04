module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderAmbientCrystalComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderProjectionFormulaUnitSection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionSplitting

/-!
# The identification `F_T ⊗ Ω_{T/S,δ} ≅ ker(i^*)` of [Stacks, Tag 07J6] on `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` and let `(U, T, δ)` be an object
of `Cris(X/S)` with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2].

The proof of [Stacks, Tag 07J6] reads `∇(s) = p₁^* s - p₀^* s`, a section of `p₀_* F_{T'}` killed
by restriction along the diagonal, as a section of `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`, "because this is the
kernel of `p₁^* F_T → F_T` as `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`".  This module proves that
identification: for a crystal the canonical morphism

`F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker(i^* : p₀_* F_{T'} ⟶ F_T)`

is an isomorphism of sheaves of `𝒪_T`-modules.

## The chain

The canonical morphism is `F_T` tensored with the inclusion `Ω_{T/S,δ} ⟶ p₀_* 𝒪_{T'}`, followed
by the projection-formula morphism `F_T ⊗ p₀_* 𝒪_{T'} ⟶ p₀_* p₀^* F_T` of [Stacks, Tag 0FZE],
the direct image of the comparison map `c₀ : p₀^* F_T ⟶ F_{T'}` of [Stacks, Tag 07IQ], and the
retraction onto the kernel.  The projection formula holds at `p₀` for every module, `p₀` being
the identity on underlying spaces (`Crystalline.isIso_firstOrderThickeningProjectionFormulaMap`),
and `c₀` is invertible because `F` is a crystal.  The two short exact sequences
`0 ⟶ F_T ⊗ Ω ⟶ F_T ⊗ p₀_* 𝒪_{T'} ⟶ F_T ⟶ 0` and `0 ⟶ ker(i^*) ⟶ p₀_* F_{T'} ⟶ F_T ⟶ 0` are
split, and the isomorphism of their middle terms carries one section to the other, so it restricts
to an isomorphism of the kernels (`Stacks.ShortComplex.isIso_of_splitting_of_section_eq`).

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `ambientSchemeCrystalComparison` — the comparison map `c₀ : p₀^* F_T ⟶ F_{T'}`.
* `firstOrderKernelComparison` — the canonical morphism `F_T ⊗ Ω ⟶ ker(i^*)`.
* `firstOrderTensorInclusion` — the canonical morphism `F_T ⊗ Ω ⟶ p₀_* F_{T'}`, the previous one
  followed by the inclusion of the kernel.

## Main results

* `isIso_ambientSchemeCrystalComparison` — `c₀` is an isomorphism for a crystal.
* `isIso_firstOrderKernelComparison_of_isSheafCrystal` — **the identification of
  [Stacks, Tag 07J6]**: `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ≅ ker(i^*)` for a crystal.
* `injective_firstOrderTensorInclusion` — the canonical morphism `F_T ⊗ Ω ⟶ p₀_* F_{T'}` is
  injective on the sections over every open.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

namespace GlobalCrystallineSituation.SmallSite

open CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} (M : SheafOfModules.{u} (structureSheaf S))

/-! ### The comparison map of a crystal on the ambient schemes -/

/-- **Stacks Project, Tag 07IQ.**  For a crystal in `𝒪_{X/S}`-modules on `Cris(X/S)` the
comparison map `c_g : g^* F_{T'} ⟶ F_T` of a morphism `g` of `Cris(X/S)`, read between sheaves of
modules on the ambient schemes, is an isomorphism.  The crystal condition is invertibility of the
transpose of the same `f`-map along the adjunction for the restrictions of `𝒪_{X/S}`; the
transport is `Stacks.Adjunction.isIso_homEquiv_symm_comp_natIso`, exactly as on `CRIS(X/S)`. -/
theorem isIso_homEquiv_symm_crysAmbientFMap (hM : IsSheafCrystal M)
    {A B : CrystallineThickening S} (g : A ⟶ B) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction g.hom.targetHom.hom).homEquiv
        (crysAmbientSchemeModules M B) (crysAmbientSchemeModules M A)).symm
      (crysAmbientFMap M g)) :=
  Stacks.Adjunction.isIso_homEquiv_symm_comp_natIso
    (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso B.obj))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (Thickening.ringRestrictionSheafFMap g.hom))
    (Scheme.Modules.pullbackPushforwardAdjunction g.hom.targetHom.hom)
    (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A.obj))
    (Thickening.ambientSchemePushforwardIso g.hom) (moduleFMapSheaf M g)
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (Thickening.ringRestrictionSheafStructureIso B.obj)).isEquivalence_functor
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (Thickening.ringRestrictionSheafStructureIso A.obj)).isEquivalence_functor
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (Thickening.ringRestrictionSheafStructureIso A.obj)).isEquivalence_inverse
    (hM A B g)

variable (A : CrystallineThickening S)

/-- **The comparison map `c₀ : p₀^* F_T ⟶ F_{T'}` of [Stacks, Tag 07IQ]**, between sheaves of
modules on the ambient schemes: the adjoint transpose of `p₀^* : F_T ⟶ p₀_* F_{T'}`. -/
def ambientSchemeCrystalComparison :
    (Scheme.Modules.pullback (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M A) ⟶
      crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
    (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).homEquiv _ _).symm
      (firstOrderAmbientInclMap M A)

/-- **The comparison map recovers `p₀^*`** when composed with the unit of the adjunction. -/
theorem unit_comp_map_ambientSchemeCrystalComparison :
    (Scheme.Modules.pullbackPushforwardAdjunction
          (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).unit.app
        (crysAmbientSchemeModules M A) ≫
      (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).map
        (ambientSchemeCrystalComparison M A) =
    firstOrderAmbientInclMap M A := by
  have h : (Scheme.Modules.pullbackPushforwardAdjunction
      (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).homEquiv _ _
        (ambientSchemeCrystalComparison M A) = firstOrderAmbientInclMap M A :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- **For a crystal the comparison map `c₀` is an isomorphism.** -/
theorem isIso_ambientSchemeCrystalComparison (hM : IsSheafCrystal M) :
    IsIso (ambientSchemeCrystalComparison M A) :=
  isIso_homEquiv_symm_crysAmbientFMap M hM (firstOrderThickeningCrysP₀ S A)

/-! ### The comparison of the two middle terms -/

/-- **The comparison `F_T ⊗_{𝒪_T} p₀_* 𝒪_{T'} ⟶ p₀_* F_{T'}`**: the projection-formula morphism
followed by the direct image of `c₀`.  No hypothesis. -/
def firstOrderTensorToAmbient :
    firstOrderThickeningTensorUnitRestriction A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A) ⟶
      (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)) :=
  firstOrderThickeningProjectionFormulaMap A.obj.thickening.target S.S.scheme A.obj.toBase.hom
      (crysAmbientSchemeModules M A) ≫
    (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).map
      (ambientSchemeCrystalComparison M A)

/-- **The comparison of the middle terms is an isomorphism** once `c₀` is.  The projection
formula holds at `p₀` for every module, `p₀` being the identity on underlying spaces. -/
theorem isIso_firstOrderTensorToAmbient
    (M : SheafOfModules.{u} (structureSheaf S)) (A : CrystallineThickening S)
    (hc : IsIso (ambientSchemeCrystalComparison M A)) :
    IsIso (firstOrderTensorToAmbient M A) :=
  IsIso.comp_isIso' (isIso_firstOrderThickeningProjectionFormulaMap _ _ _ _)
    (((Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).mapIso
      (@asIso _ _ _ _ _ hc)).isIso_hom)

/-- **The comparison of the middle terms carries the section of one splitting to the section of
the other**: `F_T ⊗ (g ↦ (g, 0))`, read through the right unitor, goes to `p₀^*`. -/
theorem firstOrderTensorToAmbient_whiskerLeft_inlSheaf :
    (crysAmbientSchemeModules M A ◁
        firstOrderThickeningInlSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom) ≫
          firstOrderTensorToAmbient M A =
      (ρ_ (crysAmbientSchemeModules M A)).hom ≫ firstOrderAmbientInclMap M A := by
  have e1 : (crysAmbientSchemeModules M A ◁
        firstOrderThickeningInlSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom) ≫
          firstOrderTensorToAmbient M A =
      ((crysAmbientSchemeModules M A ◁
        firstOrderThickeningInlSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom) ≫
          firstOrderThickeningProjectionFormulaMap A.obj.thickening.target S.S.scheme
            A.obj.toBase.hom (crysAmbientSchemeModules M A)) ≫
        (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).map
          (ambientSchemeCrystalComparison M A) :=
    (Category.assoc _ _ _).symm
  rw [e1, whiskerLeft_inlSheaf_comp_firstOrderThickeningProjectionFormulaMap]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k ↦ (ρ_ (crysAmbientSchemeModules M A)).hom ≫ k)
      (unit_comp_map_ambientSchemeCrystalComparison M A))

/-! ### The comparison of the kernel with `F_T ⊗ Ω` -/

/-- **The canonical morphism `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker(i^* : p₀_* F_{T'} ⟶ F_T)`** that
[Stacks, Tag 07J6] uses when it reads `∇(s)` inside `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`: `F_T` tensored with
the inclusion of the ideal of the diagonal, the comparison of the middle terms, and the retraction
onto the kernel.  No hypothesis. -/
def firstOrderKernelComparison :
    firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme A.obj.toBase.hom
        (crysAmbientSchemeModules M A) ⟶
      firstOrderAmbientKernel M A :=
  firstOrderThickeningTensorInr A.obj.thickening.target S.S.scheme A.obj.toBase.hom
      (crysAmbientSchemeModules M A) ≫
    firstOrderTensorToAmbient M A ≫ firstOrderAmbientRetraction M A

/-- **The identification of [Stacks, Tag 07J6]**: for a crystal in `𝒪_{X/S}`-modules on
`Cris(X/S)` the canonical morphism `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker(i^* : p₀_* F_{T'} ⟶ F_T)` is
an isomorphism of sheaves of `𝒪_T`-modules. -/
theorem isIso_firstOrderKernelComparison_of_isSheafCrystal
    (M : SheafOfModules.{u} (structureSheaf S)) (A : CrystallineThickening S)
    (hM : IsSheafCrystal M) :
    IsIso (firstOrderKernelComparison M A) :=
  Stacks.ShortComplex.isIso_of_splitting_of_section_eq
    (firstOrderThickeningStructureTensorSplitting A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A))
    (firstOrderAmbientSplitting M A)
    (@asIso _ _ _ _ _
      (isIso_firstOrderTensorToAmbient M A (isIso_ambientSchemeCrystalComparison M A hM)))
    (ρ_ (crysAmbientSchemeModules M A)) (firstOrderTensorToAmbient_whiskerLeft_inlSheaf M A)

/-- **The identification `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ≅ ker(i^*)` of [Stacks, Tag 07J6]** for a
crystal, as an isomorphism whose forward map is the canonical morphism. -/
def firstOrderKernelIso (hM : IsSheafCrystal M) :
    firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme A.obj.toBase.hom
        (crysAmbientSchemeModules M A) ≅
      firstOrderAmbientKernel M A :=
  @asIso _ _ _ _ _ (isIso_firstOrderKernelComparison_of_isSheafCrystal M A hM)

/-- The forward map of the identification is the canonical morphism. -/
@[simp]
theorem firstOrderKernelIso_hom (hM : IsSheafCrystal M) :
    (firstOrderKernelIso M A hM).hom = firstOrderKernelComparison M A := rfl

/-! ### The canonical morphism `F_T ⊗ Ω ⟶ p₀_* F_{T'}` -/

/-- **The canonical morphism `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ p₀_* F_{T'}`**: the identification of
[Stacks, Tag 07J6] followed by the inclusion of the kernel of restriction along the diagonal.  No
hypothesis. -/
def firstOrderTensorInclusion :
    firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme A.obj.toBase.hom
        (crysAmbientSchemeModules M A) ⟶
      (Scheme.Modules.pushforward (firstOrderThickeningCrysP₀ S A).hom.targetHom.hom).obj
        (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)) :=
  firstOrderKernelComparison M A ≫ kernel.ι (firstOrderAmbientProjMap₀ M A)

/-- **The canonical morphism lands in the kernel of restriction along the diagonal.** -/
@[reassoc]
theorem firstOrderTensorInclusion_projMap₀ :
    firstOrderTensorInclusion M A ≫ firstOrderAmbientProjMap₀ M A = 0 := by
  rw [firstOrderTensorInclusion, Category.assoc, kernel.condition, comp_zero]

/-- **For a crystal the canonical morphism is a monomorphism.** -/
theorem mono_firstOrderTensorInclusion (hM : IsSheafCrystal M) :
    Mono (firstOrderTensorInclusion M A) := by
  have := isIso_firstOrderKernelComparison_of_isSheafCrystal M A hM
  exact mono_comp _ _

/-- **For a crystal the canonical morphism is injective on the sections over every open.**  The
inclusion of the kernel is split by the retraction `1 - p₀^* ∘ i^*`, and the identification is an
isomorphism. -/
theorem injective_firstOrderTensorInclusion (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens) :
    Function.Injective fun z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target
        S.S.scheme A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) ↦
      (firstOrderTensorInclusion M A).val.app (op W) z := by
  intro z z' hz
  have hr : firstOrderTensorInclusion M A ≫ firstOrderAmbientRetraction M A =
      firstOrderKernelComparison M A := by
    have := (firstOrderAmbientSplitting M A).f_r
    simp only [firstOrderTensorInclusion, Category.assoc]
    exact (congrArg (firstOrderKernelComparison M A ≫ ·) this).trans (Category.comp_id _)
  have hret : ∀ w, (firstOrderAmbientRetraction M A).val.app (op W)
      ((firstOrderTensorInclusion M A).val.app (op W) w) =
        (firstOrderKernelComparison M A).val.app (op W) w := fun w ↦
    congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app (op W) w) hr
  have hiso : ∀ w, (firstOrderKernelIso M A hM).inv.val.app (op W)
      ((firstOrderKernelComparison M A).val.app (op W) w) = w := fun w ↦
    congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app (op W) w)
      (firstOrderKernelIso M A hM).hom_inv_id
  simp only at hz
  rw [← hiso z, ← hiso z', ← hret, ← hret, hz]

end GlobalCrystallineSituation.SmallSite

end Crystalline

end

end
