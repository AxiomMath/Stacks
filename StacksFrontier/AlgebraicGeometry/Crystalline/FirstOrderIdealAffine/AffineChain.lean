module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealAffine.AmbientComparison

/-!
# The affine chain computing the base change of scalars of [Stacks, Tag 07J6]

This file holds the comparison map of [Stacks, Tag 07IQ] read over the structure sheaf of the
ambient scheme, the affine chain `D' ⊗_D Mod ⟶ F(U, T', δ')`, its identification with the base
change of scalars, and the resulting bijectivity of the canonical map of [Stacks, Tag 07J6] on an
object with affine ambient scheme, for a crystal with `F_T` quasi-coherent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe v₁ u₁ u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S))

variable (A : Thickening S)

/-! ### The comparison map read over the structure sheaf of the ambient scheme

The two halves of the chain are written over different sheaves of rings: the comparison map of
[Stacks, Tag 07IQ] lives over the restriction of `𝒪_{X/S}` to the ambient scheme, while
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` lives over the structure sheaf of that
scheme.  The adjunction of restrictions of scalars along
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso` carries the
first to the second, and does so without moving sections, so every normalisation already proved
survives the move.  That is what makes the chain composable: after it the whole computation is in
the `AlgebraicGeometry.Scheme.Modules` spelling, where `AlgebraicGeometry.Scheme.Modules.Hom.app`
and its semilinearity are available.
-/

/-- **The restriction of a morphism of the site to the whole of the two ambient schemes**, with
its source named at `⊤` rather than at the preimage of `⊤`, the two being equal.  Named for the
reason `Crystalline.GlobalCrystallineSituation.top_le_preimage_siteP₀` is: the term has to carry
the type at `⊤`, which `rw` otherwise refuses. -/
def restrictOpenMapTop {A B : Thickening S} (g : A ⟶ B) :
    A.restrictOpen ⊤ ⟶ B.restrictOpen ⊤ :=
  Thickening.restrictOpenMap g ⊤

/-- `Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_restrictOpenMap_top`, read at the
index `⊤`. -/
theorem moduleSiteRestrict_restrictOpenMapTop {A B : Thickening S} (g : A ⟶ B)
    (t : M.val.obj (op B)) :
    moduleSiteRestrict M (restrictOpenMapTop g) (moduleSiteRestrict M (B.restrictOpenHom ⊤) t) =
      moduleSiteRestrict M (A.restrictOpenHom ⊤) (moduleSiteRestrict M g t) :=
  moduleSiteRestrict_restrictOpenMap_top M g t

/-- **The inverse of the restriction of sections to the whole of the ambient scheme is semilinear
over the restriction map of the site**, stated on a section of `𝒪_{X/S}` over the object rather
than on a section of the structure sheaf of the ambient scheme. -/
theorem restrictOpenTopEquiv_symm_smul_site (B : Thickening S) (b : crysSheafRing S B)
    (z : M.val.obj (op (B.restrictOpen ⊤))) :
    (restrictOpenTopEquiv M B).symm (crysSheafRingMap (B.restrictOpenHom ⊤) b • z) =
      b • (restrictOpenTopEquiv M B).symm z := by
  rw [AddEquiv.symm_apply_eq, restrictOpenTopEquiv_apply, map_smulₛₗ,
    moduleSiteRestrict_restrictOpenTopEquiv_symm]

/-- Reading a section of the restricted sheaf in the spelling of the site is additive; it is the
identity. -/
theorem siteModuleSection_add (B : Thickening S) (x y : Γ(ambientSchemeModules M B, ⊤)) :
    siteModuleSection M B (x + y) = siteModuleSection M B x + siteModuleSection M B y := rfl

/-- `Crystalline.GlobalCrystallineSituation.siteModuleSection`, as an additive map. -/
def siteModuleSectionHom (B : Thickening S) :
    Γ(ambientSchemeModules M B, ⊤) →+ M.val.obj (op (B.restrictOpen ⊤)) :=
  AddMonoidHom.mk' (siteModuleSection M B) (siteModuleSection_add M B)

/-- That reading is a bijection, being the identity. -/
theorem bijective_siteModuleSectionHom (B : Thickening S) :
    Function.Bijective (siteModuleSectionHom M B) :=
  ⟨fun _ _ h ↦ h, fun y ↦ ⟨ambientModuleSection M B y, rfl⟩⟩

/-- **The comparison map `p₀^* F_T ⟶ F_{T'}` of [Stacks, Tag 07IQ] with both sides read over the
structure sheaf of the ambient scheme.**  It is the adjoint transpose of
`Crystalline.GlobalCrystallineSituation.affineFirstOrderComparison` through the adjunction of
restrictions of scalars along
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`; by
`Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso_homEquiv_val_app` it is the same map on
sections.  This is the spelling in which the comparison can be composed with
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`. -/
def ambientFirstOrderComparison :
    (Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
        (ambientSchemeModules M A) ⟶
      ambientSchemeModules M (firstOrderThickeningObject S A) :=
  (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
    (Thickening.ringRestrictionSheafStructureIso
      (firstOrderThickeningObject S A))).homEquiv _ _ (affineFirstOrderComparison M A)

/-- **The change of spelling does not move sections.** -/
theorem ambientFirstOrderComparison_val_app
    (W : ((firstOrderThickeningObject S A).thickening.target.scheme.Opens)ᵒᵖ)
    (y : ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
      (ambientSchemeModules M A)).val.obj W) :
    (ambientFirstOrderComparison M A).val.app W y =
      (affineFirstOrderComparison M A).val.app W y :=
  Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso_homEquiv_val_app _ _ W y

/-- The comparison map on sections over the whole of `T'`, as an additive map. -/
def ambientFirstOrderComparisonTop :
    Γ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
        (ambientSchemeModules M A), ⊤) →+
      Γ(ambientSchemeModules M (firstOrderThickeningObject S A), ⊤) :=
  AddMonoidHom.mk' (fun y ↦ (ambientFirstOrderComparison M A).app ⊤ y)
    (fun y y' ↦ map_add _ y y')

/-- **For a crystal that map is bijective**, being
`Crystalline.GlobalCrystallineSituation.affineFirstOrderComparison` on sections. -/
theorem bijective_ambientFirstOrderComparisonTop (hM : IsSheafCrystal M) :
    Function.Bijective (ambientFirstOrderComparisonTop M A) := by
  have h : (ambientFirstOrderComparisonTop M A : _ → _) =
      fun y ↦ (affineFirstOrderComparison M A).val.app (op ⊤) y :=
    funext fun y ↦ ambientFirstOrderComparison_val_app M A (op ⊤) y
  exact h ▸ bijective_affineFirstOrderComparison_val_app M hM A (op ⊤)

/-- The pullback along `p₀` of a section of `F_T` over the whole of `T`, as a section of
`p₀^* F_T` over the whole of `T'`, with its type named at the sections notation. -/
def ambientPullbackSectionTop (x : Γ(ambientSchemeModules M A, ⊤)) :
    Γ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
      (ambientSchemeModules M A), ⊤) :=
  Scheme.Modules.pullbackSection (firstOrderThickeningSiteP₀ S A).targetHom.hom
    (ambientSchemeModules M A) ⊤ ⊤ (top_le_preimage_siteP₀ A) x

/-- **The normalisation of the comparison map in the ambient spelling**: it carries the pullback
of a section to the restriction of that section along `p₀`.  This is
`Crystalline.GlobalCrystallineSituation.affineFirstOrderComparison_pullbackSection` moved across
the change of spelling. -/
theorem ambientFirstOrderComparison_pullbackSection
    (h : (⊤ : (firstOrderThickeningObject S A).thickening.target.scheme.Opens) ≤
      (firstOrderThickeningSiteP₀ S A).targetHom.hom ⁻¹ᵁ ⊤)
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    (ambientFirstOrderComparison M A).app ⊤
        (Scheme.Modules.pullbackSection (firstOrderThickeningSiteP₀ S A).targetHom.hom
          (ambientSchemeModules M A) ⊤ ⊤ h x) =
      ambientModuleSection M (firstOrderThickeningObject S A)
        (moduleSiteRestrict M (restrictOpenMapTop (firstOrderThickeningSiteP₀ S A))
          (siteModuleSection M A x)) :=
  (ambientFirstOrderComparison_val_app M A (op ⊤) _).trans
    (affineFirstOrderComparison_pullbackSection M A h (siteModuleSection M A x))

/-- The same normalisation, with the pullback of the section named. -/
theorem ambientFirstOrderComparison_ambientPullbackSectionTop
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    (ambientFirstOrderComparison M A).app ⊤ (ambientPullbackSectionTop M A x) =
      ambientModuleSection M (firstOrderThickeningObject S A)
        (moduleSiteRestrict M (restrictOpenMapTop (firstOrderThickeningSiteP₀ S A))
          (siteModuleSection M A x)) :=
  ambientFirstOrderComparison_pullbackSection M A (top_le_preimage_siteP₀ A) x

/-- **The tail of the chain**, after the base-change comparison: the sections of `p₀^* F_T` over
the whole of `T'` are carried to the sections of `F` over `(U, T', δ')`, by the comparison map
followed by the two changes of spelling. -/
def affineChainTailHom :
    Γ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
        (ambientSchemeModules M A), ⊤) →+
      M.val.obj (op (firstOrderThickeningObject S A)) :=
  ((restrictOpenTopEquiv M (firstOrderThickeningObject S A)).symm.toAddMonoidHom.comp
      (siteModuleSectionHom M (firstOrderThickeningObject S A))).comp
    (ambientFirstOrderComparisonTop M A)

/-- The tail of the chain, written out. -/
theorem affineChainTailHom_apply
    (y : Γ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
      (ambientSchemeModules M A), ⊤)) :
    affineChainTailHom M A y =
      (restrictOpenTopEquiv M (firstOrderThickeningObject S A)).symm
        (siteModuleSection M (firstOrderThickeningObject S A)
          ((ambientFirstOrderComparison M A).app ⊤ y)) := rfl

/-- **The tail of the chain is bijective for a crystal**: each of its three factors is. -/
theorem bijective_affineChainTailHom (hM : IsSheafCrystal M) :
    Function.Bijective (affineChainTailHom M A) :=
  ((restrictOpenTopEquiv M (firstOrderThickeningObject S A)).symm.bijective.comp
      (bijective_siteModuleSectionHom M (firstOrderThickeningObject S A))).comp
    (bijective_ambientFirstOrderComparisonTop M A hM)

/-- **The tail of the chain on a scalar multiple of a pullback of a section.**  This is the whole
of the computation that follows the base-change comparison: the comparison map is semilinear, its
normalisation applies to the pullback, and the two changes of spelling are semilinear. -/
theorem affineChainTailHom_smul_ambientPullbackSectionTop
    (t : crysSheafRing S (firstOrderThickeningObject S A))
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineChainTailHom M A
        (ambientRingSection (firstOrderThickeningObject S A) t •
          ambientPullbackSectionTop M A x) =
      t • (restrictOpenTopEquiv M (firstOrderThickeningObject S A)).symm
        (moduleSiteRestrict M (restrictOpenMapTop (firstOrderThickeningSiteP₀ S A))
          (siteModuleSection M A x)) := by
  rw [affineChainTailHom_apply, Scheme.Modules.Hom.app_smul,
    ambientFirstOrderComparison_ambientPullbackSectionTop, ambientModuleSection_smul,
    siteModuleSection_ambientModuleSection, restrictOpenTopEquiv_symm_smul_site]

/-- **The base change of scalars on a pure tensor, written in the form the tail of the chain
produces.**  The two restrictions of `s` to the whole of the ambient schemes agree with the
restriction along `p₀`, by
`Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_restrictOpenMapTop`. -/
theorem extensionSectionsMap_tmul_restrictOpenMapTop
    (t : crysSheafRing S (firstOrderThickeningObject S A)) (s : M.val.obj (op A)) :
    extensionSectionsMap M A (t ⊗ₜ[crysSheafRing S A] s) =
      t • (restrictOpenTopEquiv M (firstOrderThickeningObject S A)).symm
        (moduleSiteRestrict M (restrictOpenMapTop (firstOrderThickeningSiteP₀ S A))
          (siteModuleSection M A
            (ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s)))) := by
  rw [extensionSectionsMap_tmul, siteModuleSection_ambientModuleSection]
  refine congrArg (fun y ↦ t • y) (Eq.symm ?_)
  rw [AddEquiv.symm_apply_eq, restrictOpenTopEquiv_apply]
  exact moduleSiteRestrict_restrictOpenMapTop M (firstOrderThickeningSiteP₀ S A) s

/-! ### The chain on an affine object

On an object with affine ambient scheme and locally quasi-coherent `F` the three factors
`affineCrossEquiv`, `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at `⊤, ⊤` and the
tail above are each bijections, and
`Crystalline.GlobalCrystallineSituation.affineExtensionHom` is their composite, an additive map
`D' ⊗_D Mod ⟶ F(U, T', δ')`.  That that composite **is**
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap` is proved in the section after
this one, and with it bijectivity of the base-change map itself.
-/

/-- The ambient scheme of the first-order universal thickening of an affine object is affine, as
an instance. -/
instance isAffine_target_firstOrderThickeningObject [IsAffine A.thickening.target.scheme] :
    IsAffine (firstOrderThickeningObject S A).thickening.target.scheme :=
  isAffine_firstOrderThickeningObject A

section Affine

variable [IsAffine A.thickening.target.scheme]
  [(ambientSchemeModules M A).IsQuasicoherent]

/-- The affine base-change comparison of [Stacks, Tag 01I9] at the whole of the two ambient
schemes, which are affine. -/
abbrev affineBaseChangeTopIso :=
  affinePullbackSectionsBaseChangeIso (firstOrderThickeningSiteP₀ S A).targetHom.hom
    (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
    (top_le_preimage_siteP₀ A)

/-- `affineCross`, with its target named at the extension of scalars of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`.  The single bridge between the two
spellings of the tensor product. -/
def affineCrossModule :
    crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) →+
      ((ModuleCat.extendScalars ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteP₀ A)).hom).obj
        (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeModules M A, ⊤)) :
          Type u) :=
  affineCross M A

omit [IsAffine A.thickening.target.scheme]
  [SheafOfModules.IsQuasicoherent (ambientSchemeModules M A)] in
/-- The bridge is a bijection, being `affineCrossEquiv`. -/
theorem bijective_affineCrossModule : Function.Bijective (affineCrossModule M A) :=
  (affineCrossEquiv M A).bijective

omit [IsAffine A.thickening.target.scheme]
  [SheafOfModules.IsQuasicoherent (ambientSchemeModules M A)] in
/-- The bridge, on a pure tensor. -/
theorem affineCrossModule_tmul (t : crysSheafRing S (firstOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineCrossModule M A (t ⊗ₜ[crysSheafRing S A] s) =
      ambientRingSection (firstOrderThickeningObject S A) t ⊗ₜ[
        Γ(A.thickening.target.scheme, ⊤),
        ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteP₀ A)).hom]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s) :=
  affineCross_tmul M A t s

/-- The base-change comparison at `⊤, ⊤`, as an additive map. -/
def affineBaseChangeTopHom :
    ((ModuleCat.extendScalars ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤
        (top_le_preimage_siteP₀ A)).hom).obj
      (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeModules M A, ⊤)) :
        Type u) →+
      ((ModuleCat.of Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤)
        Γ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
          (ambientSchemeModules M A), ⊤)) : Type u) :=
  (affineBaseChangeTopIso M A).hom.hom.toAddMonoidHom

/-- The base-change comparison, written out. -/
theorem affineBaseChangeTopHom_apply
    (w : ((ModuleCat.extendScalars ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤
        (top_le_preimage_siteP₀ A)).hom).obj
      (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeModules M A, ⊤)) :
        Type u)) :
    affineBaseChangeTopHom M A w = (affineBaseChangeTopIso M A).hom w := rfl

/-- `ambientPullbackSectionTop`, with its type named at the codomain of the base-change
comparison.  The one bridge between the sections notation and the `ModuleCat` object whose
carrier it is. -/
def ambientPullbackSectionTopModule (x : Γ(ambientSchemeModules M A, ⊤)) :
    ((ModuleCat.of Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤)
      Γ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
        (ambientSchemeModules M A), ⊤)) : Type u) :=
  ambientPullbackSectionTop M A x

omit [IsAffine A.thickening.target.scheme]
  [SheafOfModules.IsQuasicoherent (ambientSchemeModules M A)] in
/-- `Crystalline.GlobalCrystallineSituation.affineChainTailHom_smul_ambientPullbackSectionTop`,
read at the codomain of the base-change comparison. -/
theorem affineChainTailHom_smul_ambientPullbackSectionTopModule
    (t : crysSheafRing S (firstOrderThickeningObject S A))
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineChainTailHom M A
        (ambientRingSection (firstOrderThickeningObject S A) t •
          ambientPullbackSectionTopModule M A x) =
      t • (restrictOpenTopEquiv M (firstOrderThickeningObject S A)).symm
        (moduleSiteRestrict M (restrictOpenMapTop (firstOrderThickeningSiteP₀ S A))
          (siteModuleSection M A x)) :=
  affineChainTailHom_smul_ambientPullbackSectionTop M A t x

/-- **The base-change comparison is bijective** under quasi-coherence and affineness, being an
isomorphism of `ModuleCat`. -/
theorem bijective_affineBaseChangeTopHom :
    Function.Bijective (affineBaseChangeTopHom M A) := by
  exact ConcreteCategory.bijective_of_isIso (affineBaseChangeTopIso M A).hom

/-- **The base-change comparison on the bridge, at a pure tensor.** -/
theorem affineBaseChangeTopHom_affineCrossModule_tmul
    (t : crysSheafRing S (firstOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineBaseChangeTopHom M A (affineCrossModule M A (t ⊗ₜ[crysSheafRing S A] s)) =
      affineBaseChangeTopHom M A
        (ambientRingSection (firstOrderThickeningObject S A) t ⊗ₜ[
          Γ(A.thickening.target.scheme, ⊤),
          ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤
            (top_le_preimage_siteP₀ A)).hom]
          ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s)) :=
  congrArg (fun w ↦ affineBaseChangeTopHom M A w) (affineCrossModule_tmul M A t s)

/-- **The affine chain, as an additive map `D' ⊗_D Mod ⟶ F(U, T', δ')`.** -/
def affineExtensionHom :
    crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) →+
      M.val.obj (op (firstOrderThickeningObject S A)) :=
  ((affineChainTailHom M A).comp (affineBaseChangeTopHom M A)).comp (affineCrossModule M A)

/-- **The chain is bijective** for a crystal, on an object with affine ambient scheme and with
`F_T` quasi-coherent: each of its three factors is.  That the chain is
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap`, and hence that that map is
bijective, is `Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMap` below. -/
theorem bijective_affineExtensionHom (hM : IsSheafCrystal M) :
    Function.Bijective (affineExtensionHom M A) :=
  ((bijective_affineChainTailHom M A hM).comp (bijective_affineBaseChangeTopHom M A)).comp
    (bijective_affineCrossModule M A)

/-! ### The chain is the base change of scalars

The one equation the chain still owes is that it **is**
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap`, and by additivity it is enough to
check that on a pure tensor.  The computation is three rewrites, but every one of them crosses
the boundary between two spellings of one tensor product: the carrier
`S ⊗_R ((ModuleCat.restrictScalars f).obj S)` of Mathlib's `ModuleCat.ExtendScalars`, and the
plain `S ⊗_R M` of the notation `⊗ₜ[R, f]` that `ModuleCat.ExtendScalars`'s own lemmas are stated
with.  The two are definitionally equal and the cost of seeing it is high enough that Mathlib
buys the crossing with a `backward.isDefEq.respectTransparency` option around its own
`ModuleCat.ExtendScalars` section.  Three devices keep each step below on one side of it.

* The comparison is applied through `Crystalline.GlobalCrystallineSituation.affineBaseChangeTopIso`
  *as a term*.  `Crystalline.GlobalCrystallineSituation.affineBaseChangeTopIso_eq` identifies that
  term with `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` by `rfl`, and *rewriting* with
  it makes the goal syntactically the statement of the normalisation, instead of asking the
  unifier to see through the abbreviation and the carrier in one step.
* The chain is applied as a *function*,
  `Crystalline.GlobalCrystallineSituation.affineExtensionFun`, rather than through the additive map
  `Crystalline.GlobalCrystallineSituation.affineBaseChangeTopHom`: the coercion of a `ModuleCat`
  morphism and the coercion of the `AddMonoidHom` built from it are then only ever compared at an
  argument that is a term with a constant at its head, never at a pure tensor.
* Each elaboration sits in its own declaration.  The heartbeat budget is counted per declaration,
  so a single proof performing the crossing three times pays for it three times over against one
  budget.
-/

/-- The base-change comparison at `⊤, ⊤` carries `1 ⊗ a` to the pullback of `a`.  This is
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul`, with its value named at the
`ModuleCat` object whose carrier it is. -/
theorem affineBaseChangeTop_one_tmul
    (a : Γ(ambientSchemeModules M A, (⊤ : A.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso (firstOrderThickeningSiteP₀ S A).targetHom.hom
        (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
        (top_le_preimage_siteP₀ A)).hom ((1 : Γ(
        (firstOrderThickeningObject S A).thickening.target.scheme,
        (⊤ : (firstOrderThickeningObject S A).thickening.target.scheme.Opens))) ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteP₀ A)).hom] a) = ambientPullbackSectionTopModule M A a :=
  affinePullbackSectionsBaseChangeIso_one_tmul (firstOrderThickeningSiteP₀ S A).targetHom.hom
    (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
    (top_le_preimage_siteP₀ A) a

/-- The base-change comparison at `⊤, ⊤` carries `t ⊗ a` to `t` times the pullback of `a`.  This
is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_tmul` followed by
`Crystalline.GlobalCrystallineSituation.affineBaseChangeTop_one_tmul`; it is a declaration of its
own so that the two elaborations are paid for out of two budgets. -/
theorem affineBaseChangeTop_tmul
    (r : Γ((firstOrderThickeningObject S A).thickening.target.scheme,
      (⊤ : (firstOrderThickeningObject S A).thickening.target.scheme.Opens)))
    (a : Γ(ambientSchemeModules M A, (⊤ : A.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso (firstOrderThickeningSiteP₀ S A).targetHom.hom
        (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
        (top_le_preimage_siteP₀ A)).hom (r ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteP₀ A)).hom] a) =
      r • ambientPullbackSectionTopModule M A a :=
  (affinePullbackSectionsBaseChangeIso_tmul (firstOrderThickeningSiteP₀ S A).targetHom.hom
    (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
    (top_le_preimage_siteP₀ A) r a).trans
      (congrArg (fun z ↦ r • z) (affineBaseChangeTop_one_tmul M A a))

/-- **The abbreviation naming the affine base-change comparison is that comparison.**  Trivial,
and stated because it is the one step that has to be taken as a *rewrite*: with it the goal
becomes syntactically the statement of
`Crystalline.GlobalCrystallineSituation.affineBaseChangeTop_tmul`, so that the unifier is never
asked to identify the abbreviation and the `ModuleCat.ExtendScalars` carrier of a pure tensor in
the same step. -/
theorem affineBaseChangeTopIso_eq :
    affineBaseChangeTopIso M A =
      affinePullbackSectionsBaseChangeIso (firstOrderThickeningSiteP₀ S A).targetHom.hom
        (ambientSchemeModules M A) (isAffineOpen_top _) (isAffineOpen_top _)
        (top_le_preimage_siteP₀ A) := rfl

/-- `Crystalline.GlobalCrystallineSituation.affineBaseChangeTop_tmul`, read through the
abbreviation the chain is written with. -/
theorem affineBaseChangeTopIso_hom_tmul
    (r : Γ((firstOrderThickeningObject S A).thickening.target.scheme,
      (⊤ : (firstOrderThickeningObject S A).thickening.target.scheme.Opens)))
    (a : Γ(ambientSchemeModules M A, (⊤ : A.thickening.target.scheme.Opens))) :
    (affineBaseChangeTopIso M A).hom (r ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤
          (top_le_preimage_siteP₀ A)).hom] a) =
      r • ambientPullbackSectionTopModule M A a := by
  rw [affineBaseChangeTopIso_eq]
  exact affineBaseChangeTop_tmul M A r a

/-- **The affine chain as a function**: the composite of the bridge, the base-change comparison
applied as a morphism of `ModuleCat`, and the tail.  This is
`Crystalline.GlobalCrystallineSituation.affineExtensionHom` with the middle factor not bundled as
an additive map, which is what lets the normalisation below be stated against
`Crystalline.GlobalCrystallineSituation.affineBaseChangeTopIso_hom_tmul`. -/
def affineExtensionFun
    (z : crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A]
      M.val.obj (op A)) : M.val.obj (op (firstOrderThickeningObject S A)) :=
  affineChainTailHom M A ((affineBaseChangeTopIso M A).hom (affineCrossModule M A z))

/-- The function and the additive map are the same map; bundling the middle factor is all that
separates them. -/
theorem affineExtensionFun_eq_affineExtensionHom
    (z : crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A]
      M.val.obj (op A)) :
    affineExtensionFun M A z = affineExtensionHom M A z := rfl

/-- **The chain and the base change of scalars agree on a pure tensor.**  The bridge carries
`t ⊗ s` to `t ⊗ p₀^* s`, the base-change comparison carries that to `t · p₀^* s`, and the tail
carries that to `t · p₀^* s` read over the object, which is
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap` at `t ⊗ s`. -/
theorem affineExtensionFun_tmul (t : crysSheafRing S (firstOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineExtensionFun M A (t ⊗ₜ[crysSheafRing S A] s) =
      extensionSectionsMap M A (t ⊗ₜ[crysSheafRing S A] s) := by
  have hcross : affineExtensionFun M A (t ⊗ₜ[crysSheafRing S A] s) =
      affineChainTailHom M A ((affineBaseChangeTopIso M A).hom
        (ambientRingSection (firstOrderThickeningObject S A) t ⊗ₜ[
          Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
          ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤
            (top_le_preimage_siteP₀ A)).hom]
          ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s))) :=
    congrArg (fun w ↦ affineChainTailHom M A ((affineBaseChangeTopIso M A).hom w))
      (affineCrossModule_tmul M A t s)
  have hcomp := congrArg (fun y ↦ affineChainTailHom M A y)
    (affineBaseChangeTopIso_hom_tmul M A (ambientRingSection (firstOrderThickeningObject S A) t)
      (ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s)))
  have htail := affineChainTailHom_smul_ambientPullbackSectionTopModule M A t
    (ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s))
  exact ((hcross.trans hcomp).trans htail).trans
    (extensionSectionsMap_tmul_restrictOpenMapTop M A t s).symm

/-- `Crystalline.GlobalCrystallineSituation.affineExtensionFun_tmul`, for the additive map. -/
theorem affineExtensionHom_tmul (t : crysSheafRing S (firstOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineExtensionHom M A (t ⊗ₜ[crysSheafRing S A] s) =
      extensionSectionsMap M A (t ⊗ₜ[crysSheafRing S A] s) :=
  (affineExtensionFun_eq_affineExtensionHom M A (t ⊗ₜ[crysSheafRing S A] s)).symm.trans
    (affineExtensionFun_tmul M A t s)

/-- **The affine chain is the base change of scalars**: two additive maps agreeing on every pure
tensor agree. -/
theorem extensionSectionsMap_eq_affineExtensionHom :
    (extensionSectionsMap M A : _ → _) = (affineExtensionHom M A : _ → _) := by
  funext w
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul t s => exact (affineExtensionHom_tmul M A t s).symm
  | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- **The base change of scalars `D' ⊗_D Mod ⟶ F(U, T', δ')` is bijective** for a crystal on an
object whose ambient scheme is affine and with `F_T` quasi-coherent.  This is the chain
`Crystalline.GlobalCrystallineSituation.bijective_affineExtensionHom` together with the
identification of the chain with
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap`. -/
theorem bijective_extensionSectionsMap (hM : IsSheafCrystal M) :
    Function.Bijective (extensionSectionsMap M A) := by
  rw [extensionSectionsMap_eq_affineExtensionHom M A]
  exact bijective_affineExtensionHom M A hM

/-- **The canonical map of [Stacks, Tag 07J6] on global sections is bijective** for a crystal on
an object whose ambient scheme is affine and with `F_T` quasi-coherent, by the equivalence of the
two bijectivity statements proved at the head of this module. -/
theorem bijective_firstOrderSectionsMap_of_isSheafCrystal (hM : IsSheafCrystal M) :
    Function.Bijective (firstOrderSectionsMap M A) :=
  (bijective_firstOrderSectionsMap_iff_bijective_extensionSectionsMap M A).mpr
    (bijective_extensionSectionsMap M A hM)

/-- **The datum of [Stacks, Tag 07J6] for a crystal on an object with affine ambient scheme and
quasi-coherent `F_T`** — the degree-one input of clause C5 of that tag, obtained from the source's
own crystal hypothesis rather than assumed. -/
def firstOrderIdealBaseChangeOfIsSheafCrystal (hM : IsSheafCrystal M) :
    FirstOrderIdealBaseChange M A :=
  firstOrderIdealBaseChangeOfBijective M A
    (bijective_firstOrderSectionsMap_of_isSheafCrystal M A hM)

end Affine

end Crystalline.GlobalCrystallineSituation

end

end
