module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingAtlasCechNerve
public import StacksFrontier.Examples.Spaces.ConstantZModTwoGroupSpacePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ClassifyingStackCechResolution
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DirectImageCompositeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SchemeStackBaseCostructuredArrow
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineObjectStructureSheafVanishingUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineObjectsFppfCovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.VanishingFromSectionsFormula
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact

/-!
# The direct images of the Čech terms of `B(ℤ/2)_S`

Let `S` be a scheme of a big fppf site, `G = (ℤ/2)_S = S ⊔ S` the constant group, `𝒳 = BG` its
classifying stack with atlas `π : S ⟶ BG`, and `f : 𝒳 ⟶ S` the structure morphism. For `n ≥ 0`
let `cₙ` be the `n`-th projection of the relative Čech nerve of `π`. This file shows that the
direct image `f_* cₙ,* cₙ⁻¹` has a sections formula: over an object `y` of the stack of `S`
lying over a scheme `T`, the comma category of `f ∘ cₙ` over `y` has the terminal object given
by the canonical tuple of the universal points of `G` on `T ×_S Gⁿ`, so

`Γ(y, f_* cₙ,* cₙ⁻¹ M) ≅ Γ(π(T ×_S Gⁿ), M)`

naturally in `M`. As `T ×_S Gⁿ` is affine when `T` is, the higher cohomology of the structure
sheaf of `𝒳` over `π(T ×_S Gⁿ)` vanishes, hence so do the higher right derived functors of
`f_* cₙ,* cₙ⁻¹` at the structure sheaf.

## Main definitions

* `AlgebraicGeometry.Stack.ClassifyingZModTwo.cechTerminal` and its terminality
  `AlgebraicGeometry.Stack.ClassifyingZModTwo.isTerminalCechTerminal`.
* `AlgebraicGeometry.Stack.ClassifyingZModTwo.cechCompositeSectionsIso`: the sections formula.

## Main results

* `AlgebraicGeometry.Stack.ClassifyingZModTwo.isZero_rightDerived_cechDirectImage_uliftUnit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicGeometry.Stack.ClassifyingAtlasCech Stacks.Examples

universe u w

namespace AlgebraicGeometry.Stack.ClassifyingZModTwo

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ additive_fppfModuleSheafPushforwardOfStacks

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} (hS : C.Contains S)

/-- `(ℤ/2)_S ⟶ S` is smooth. -/
theorem isSmooth_constantZModTwoGroup :
    Space.IsSmooth C S hS (constantZModTwoGroup hS).obj.X.hom :=
  SectionCoverData.isSmooth_groupSpace_hom hS _ _

/-- The classifying stack `B(ℤ/2)_S`. -/
abbrev stack : AlgebraicStacks.{u, w} C S hS :=
  classifyingAlgebraicStack.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS)

/-- The stack of the base `S`. -/
abbrev base : AlgebraicStacks.{u, w} C S hS :=
  schemeStack.{u, w} C S hS (Over.mk (𝟙 (C.obj hS)))

/-- The structure morphism `B(ℤ/2)_S ⟶ S`. -/
abbrev structureMap : stack.{u, w} hS ⟶ base.{u, w} hS :=
  structureMorphism C S hS (stack.{u, w} hS)

/-- The `n`-th projection of the relative Čech nerve of the atlas. -/
abbrev cechProjection (n : ℕ) :
    CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n ⥤
      (stack.{u, w} hS).val.val.obj :=
  Stacks.RelativeCech.Tuple.projection (stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS))
    (atlasFunctor.{u, w} _ (isSmooth_constantZModTwoGroup hS)) n

/-- The projections of the Čech nerve are continuous. -/
instance isContinuous_cechProjection (n : ℕ) :
    (cechProjection.{u, w} hS n).IsContinuous
      (BigFppfOver.associatedTopology C S hS
        (cechProjection.{u, w} hS n ⋙ (stack.{u, w} hS).val.val.p) .fppf)
      (BigFppfOver.associatedTopology C S hS (stack.{u, w} hS).val.val.p .fppf) :=
  Stacks.RelativeCech.tupleProjection_isContinuous C S hS
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.p
    (stack.{u, w} hS).val.val.p
    (classifyingAtlasFunctor.{u, w} _ (isSmooth_constantZModTwoGroup hS)) .fppf
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.isFiberedInGroupoids
    (stack.{u, w} hS).val.isFiberedInGroupoids
    (isFibredOneMorphism_classifyingAtlasFunctor.{u, w} _ (isSmooth_constantZModTwoGroup hS)) n

/-- The projections of the Čech nerve are cocontinuous. -/
instance isCocontinuous_cechProjection (n : ℕ) :
    (cechProjection.{u, w} hS n).IsCocontinuous
      (BigFppfOver.associatedTopology C S hS
        (cechProjection.{u, w} hS n ⋙ (stack.{u, w} hS).val.val.p) .fppf)
      (BigFppfOver.associatedTopology C S hS (stack.{u, w} hS).val.val.p .fppf) :=
  Stacks.RelativeCech.tupleProjection_isCocontinuous C S hS
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.p
    (stack.{u, w} hS).val.val.p
    (classifyingAtlasFunctor.{u, w} _ (isSmooth_constantZModTwoGroup hS)) .fppf
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.isFiberedInGroupoids
    (stack.{u, w} hS).val.isFiberedInGroupoids
    (isFibredOneMorphism_classifyingAtlasFunctor.{u, w} _ (isSmooth_constantZModTwoGroup hS)) n

/-- The inverse image `cₙ⁻¹` along the `n`-th projection of the Čech nerve. -/
abbrev cechInverseImage (n : ℕ) :=
  SheafOfModules.pushforward₀.{u, u + 1} (cechProjection.{u, w} hS n)
    (BigFppfOver.associatedTopology C S hS
      (cechProjection.{u, w} hS n ⋙ (stack.{u, w} hS).val.val.p) .fppf)
    (BigFppfOver.associatedTopology C S hS (stack.{u, w} hS).val.val.p .fppf)
    (Stacks.RelativeCech.moduleRingSheaf C S hS (stack.{u, w} hS).val.val.p
      (stack.{u, w} hS).val.isFiberedInGroupoids .fppf)

/-- The direct image `cₙ,*` along the `n`-th projection of the Čech nerve. -/
abbrev cechDirectImageProjection (n : ℕ) :=
  SheafOfModules.directImage.{u, u + 1} (cechProjection.{u, w} hS n)
    (BigFppfOver.associatedTopology C S hS
      (cechProjection.{u, w} hS n ⋙ (stack.{u, w} hS).val.val.p) .fppf)
    (BigFppfOver.associatedTopology C S hS (stack.{u, w} hS).val.val.p .fppf)
    (Stacks.RelativeCech.moduleRingSheaf C S hS (stack.{u, w} hS).val.val.p
      (stack.{u, w} hS).val.isFiberedInGroupoids .fppf)

/-- **The terminal arrow into an object `y` of the stack of the base**: the canonical tuple of the
universal points of `G` on `y.left ×_S Gⁿ`. -/
abbrev cechTerminal (y : (base.{u, w} hS).val.val.obj) (n : ℕ) :
    CostructuredArrow (cechProjection.{u, w} hS n ⋙
      CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom) y :=
  baseSliceCostructuredArrow (tupleProj.{u, w} _ (isSmooth_constantZModTwoGroup hS) n) y
    (terminalObj.{u, w} _ (isSmooth_constantZModTwoGroup hS) (powerObjProj y.left n)
      (powerObjPoint y.left n))

/-- **`cechTerminal y n` is terminal.** -/
def isTerminalCechTerminal (y : (base.{u, w} hS).val.val.obj) (n : ℕ) :
    IsTerminal (cechTerminal.{u, w} hS y n) :=
  isTerminalBaseSliceCostructuredArrow
    (isTerminalCanonicalTuple _ (isSmooth_constantZModTwoGroup hS)
      (existsUnique_powerObj y.left n))

/-- The object of `B(ℤ/2)_S` computing the sections of `f_* cₙ,* cₙ⁻¹` over `y`: the trivial
torsor over `y.left ×_S Gⁿ`. -/
abbrev cechSectionsObj (y : (base.{u, w} hS).val.val.obj) (n : ℕ) :
    (stack.{u, w} hS).val.val.obj :=
  (atlasFunctor.{u, w} _ (isSmooth_constantZModTwoGroup hS)).obj (atlasObj (powerObj y.left n))

/-- The relative Čech complex along the atlas of `B(ℤ/2)_S`. -/
abbrev cechComplex :
    fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS) ⥤
      CochainComplex (fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS)) ℕ :=
  classifyingCechComplex.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS)

/-- The functor `M ↦ f_* cₙ,* cₙ⁻¹ M`: the degree `n` term of the relative Čech complex followed
by the direct image along the structure morphism. -/
abbrev cechDirectImage (n : ℕ) :
    fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS) ⥤
      fppfModulesUnivLE.{u, w, u + 1} C S hS (base.{u, w} hS) :=
  cechComplex.{u, w} hS ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) n ⋙
    fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS)

/-- The topology of the `n`-th term of the relative Čech nerve. -/
abbrev cechTopology (n : ℕ) :
    GrothendieckTopology
      (CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n) :=
  associatedTopology C S hS (cechProjection.{u, w} hS n ⋙ (stack.{u, w} hS).val.val.p)
    (C.baseTopology .fppf)

/-- The ring sheaf on the `n`-th term of the relative Čech nerve: the inverse image of the
structure sheaf of `B(ℤ/2)_S`. -/
abbrev cechRing (n : ℕ) :=
  compositeRing C S hS (stack.{u, w} hS).val.val.p (stack.{u, w} hS).val.isFiberedInGroupoids
    (cechProjection.{u, w} hS n) (cechTopology.{u, w} hS n)

/-- The composite `f_* cₙ,*` of the direct image along the `n`-th projection of the Čech nerve
and the direct image along the structure morphism. -/
abbrev cechCompositeDirectImage (n : ℕ) :=
  compositeDirectImage C S hS (stack.{u, w} hS).val.val.p (base.{u, w} hS).val.val.p
    (stack.{u, w} hS).val.isFiberedInGroupoids (base.{u, w} hS).val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom)
    (CatFiberedInGroupoids.homFunctor_comp_p (structureMap.{u, w} hS).hom)
    (cechProjection.{u, w} hS n) (cechTopology.{u, w} hS n)

/-- The component at `(a, φ)` of a section of `f_* cₙ,* N` over `y`. -/
abbrev cechEval (n : ℕ) (N : SheafOfModules.{u + 1} (cechRing.{u, w} hS n))
    {y : (base.{u, w} hS).val.val.obj}
    (a : CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n)
    (φ : (CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom).obj
      ((cechProjection.{u, w} hS n).obj a) ⟶ y)
    (s : ((cechCompositeDirectImage.{u, w} hS n).obj N).val.presheaf.obj (op y)) :
    N.val.presheaf.obj (op a) :=
  compositeSectionsEval C S hS (stack.{u, w} hS).val.val.p (base.{u, w} hS).val.val.p
    (stack.{u, w} hS).val.isFiberedInGroupoids (base.{u, w} hS).val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom)
    (CatFiberedInGroupoids.homFunctor_comp_p (structureMap.{u, w} hS).hom)
    (cechProjection.{u, w} hS n) (cechTopology.{u, w} hS n) N a φ s

/-- The components of a section of `f_* cₙ,* N` are compatible with the morphisms of the Čech
nerve. -/
theorem cechEval_comp (n : ℕ) (N : SheafOfModules.{u + 1} (cechRing.{u, w} hS n))
    {y : (base.{u, w} hS).val.val.obj}
    {a a' : CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n}
    (k : a ⟶ a')
    (φ' : (CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom).obj
      ((cechProjection.{u, w} hS n).obj a') ⟶ y)
    (s : ((cechCompositeDirectImage.{u, w} hS n).obj N).val.presheaf.obj (op y)) :
    ConcreteCategory.hom (N.val.presheaf.map k.op) (cechEval.{u, w} hS n N a' φ' s) =
      cechEval.{u, w} hS n N a ((CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom).map
        ((cechProjection.{u, w} hS n).map k) ≫ φ') s :=
  compositeSectionsEval_comp (B := C) (S := S) (hS := hS) (q := (stack.{u, w} hS).val.val.p)
    (r := (base.{u, w} hS).val.val.p) (hq := (stack.{u, w} hS).val.isFiberedInGroupoids)
    (hr := (base.{u, w} hS).val.isFiberedInGroupoids)
    (F := CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom)
    (hF := CatFiberedInGroupoids.homFunctor_comp_p (structureMap.{u, w} hS).hom)
    (c := cechProjection.{u, w} hS n) (J := cechTopology.{u, w} hS n) N k φ' s

/-- The structure sheaf of rings of the stack of the base. -/
abbrev cechBaseRing :=
  ringStructureSheafCore C S hS (base.{u, w} hS).val.val.p (base.{u, w} hS).val.isFiberedInGroupoids
    (C.baseTopology .fppf) (C.baseTopology_le_topology .fppf)

/-- The components of a restricted section of `f_* cₙ,* N` are the components at the
composites. -/
theorem cechEval_map (n : ℕ) (N : SheafOfModules.{u + 1} (cechRing.{u, w} hS n))
    {y y' : (base.{u, w} hS).val.val.obj} (g : y' ⟶ y)
    (a : CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n)
    (φ : (CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom).obj
      ((cechProjection.{u, w} hS n).obj a) ⟶ y')
    (s : ((cechCompositeDirectImage.{u, w} hS n).obj N).val.presheaf.obj (op y)) :
    cechEval.{u, w} hS n N a φ
        (ConcreteCategory.hom (((cechCompositeDirectImage.{u, w} hS n).obj N).val.presheaf.map
          g.op) s) =
      cechEval.{u, w} hS n N a (φ ≫ g) s :=
  compositeSectionsEval_map (B := C) (S := S) (hS := hS) (q := (stack.{u, w} hS).val.val.p)
    (r := (base.{u, w} hS).val.val.p) (hq := (stack.{u, w} hS).val.isFiberedInGroupoids)
    (hr := (base.{u, w} hS).val.isFiberedInGroupoids)
    (F := CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom)
    (hF := CatFiberedInGroupoids.homFunctor_comp_p (structureMap.{u, w} hS).hom)
    (c := cechProjection.{u, w} hS n) (J := cechTopology.{u, w} hS n) N g a φ s

/-- The functor underlying the structure morphism `B(ℤ/2)_S ⟶ S`. -/
abbrev structureFunctor := CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom

/-- The direct image along the structure morphism, on sheaves of modules over the structure
sheaf of `B(ℤ/2)_S` in the form used by `cechCompositeDirectImage`. -/
abbrev cechOuterDirectImage :=
  moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} C S hS (stack.{u, w} hS).val.val.p
    (base.{u, w} hS).val.val.p (stack.{u, w} hS).val.isFiberedInGroupoids
    (base.{u, w} hS).val.isFiberedInGroupoids (structureFunctor.{u, w} hS)
    (CatFiberedInGroupoids.homFunctor_comp_p (structureMap.{u, w} hS).hom)
    (C.baseTopology .fppf) (C.baseTopology_le_topology .fppf)

/-- The structure modules of `B(ℤ/2)_S` in the form used by `cechCompositeDirectImage`. -/
abbrev StackModule :=
  SheafOfModules.{u + 1} (ringStructureSheafCore C S hS (stack.{u, w} hS).val.val.p
    (stack.{u, w} hS).val.isFiberedInGroupoids (C.baseTopology .fppf)
    (C.baseTopology_le_topology .fppf))

/-- The comparison of the sections of `f_* X` with the right Kan extension. -/
abbrev cechOuterIso (X : StackModule.{u, w} hS) (y : (base.{u, w} hS).val.val.obj) :=
  outerSectionsIso C S hS (stack.{u, w} hS).val.val.p (base.{u, w} hS).val.val.p
    (stack.{u, w} hS).val.isFiberedInGroupoids (base.{u, w} hS).val.isFiberedInGroupoids
    (structureFunctor.{u, w} hS)
    (CatFiberedInGroupoids.homFunctor_comp_p (structureMap.{u, w} hS).hom) X y

/-- Restriction along the structure functor is left adjoint to compatible families. -/
abbrev structureSectionsAdjunction :=
  sectionsAdjunction.{u + 1, u, u} (structureFunctor.{u, w} hS).op

/-- Restriction along the structure functor is left adjoint to right Kan extension. -/
abbrev structureRanAdjunction :=
  (structureFunctor.{u, w} hS).op.ranAdjunction AddCommGrpCat.{u + 1}

/-- The legs of the right Kan extension at the image of a section, as morphisms. -/
theorem cechOuterIso_hom_comp_ranπ (X : StackModule.{u, w} hS)
    (y : (base.{u, w} hS).val.val.obj)
    (j : StructuredArrow (op y) (structureFunctor.{u, w} hS).op) :
    (cechOuterIso.{u, w} hS X y).hom ≫
        Stacks.SheafOfModules.ranπ (structureFunctor.{u, w} hS).op X.val.presheaf (op y) j =
      ((sectionsFunctor.{u + 1, u, u} (structureFunctor.{u, w} hS).op).obj X.val.presheaf).map
          j.hom ≫
        ((structureSectionsAdjunction.{u, w} hS).counit.app X.val.presheaf).app j.right := by
  have h := congr_app (Adjunction.rightAdjointUniq_hom_app_counit
    (structureSectionsAdjunction.{u, w} hS) (structureRanAdjunction.{u, w} hS) X.val.presheaf)
    j.right
  rw [Functor.ranAdjunction_counit] at h
  have hn := ((Adjunction.rightAdjointUniq (structureSectionsAdjunction.{u, w} hS)
    (structureRanAdjunction.{u, w} hS)).hom.app X.val.presheaf).naturality j.hom
  change ((Adjunction.rightAdjointUniq (structureSectionsAdjunction.{u, w} hS)
      (structureRanAdjunction.{u, w} hS)).hom.app X.val.presheaf).app (op y) ≫
      ((structureFunctor.{u, w} hS).op.ran.obj X.val.presheaf).map j.hom ≫
      ((structureFunctor.{u, w} hS).op.ranCounit.app X.val.presheaf).app j.right = _
  rw [← Category.assoc, ← hn, Category.assoc]
  exact congrArg (_ ≫ ·) h

/-- **The legs of the right Kan extension at the image of a section of `f_* X` are its
components** as a compatible family of sections, through the identification of the two right
adjoints of restriction along `f` (Stacks 06WD). -/
theorem ranπ_cechOuterIso_hom_apply (X : StackModule.{u, w} hS)
    (y : (base.{u, w} hS).val.val.obj)
    (j : StructuredArrow (op y) (structureFunctor.{u, w} hS).op)
    (s : ((cechOuterDirectImage.{u, w} hS).obj X).val.presheaf.obj (op y)) :
    ConcreteCategory.hom
        (Stacks.SheafOfModules.ranπ (structureFunctor.{u, w} hS).op X.val.presheaf (op y) j)
        (ConcreteCategory.hom (cechOuterIso.{u, w} hS X y).hom s) =
      (show compatibleSections (structureFunctor.{u, w} hS).op X.val.presheaf (op y) from
        s).val j.right j.hom :=
  (ConcreteCategory.comp_apply _ _ s).symm.trans
    ((ConcreteCategory.congr_hom (cechOuterIso_hom_comp_ranπ.{u, w} hS X y j) s).trans
      (congrArg ((show compatibleSections (structureFunctor.{u, w} hS).op X.val.presheaf (op y)
        from s).val j.right) (Category.comp_id j.hom)))

/-- **The component of a section of `f_* cₙ,* N` at `(a, φ)` is the value at the identity index
of its component at `(cₙ(a), φ)` as a compatible family.** -/
theorem cechEval_eq (n : ℕ) (N : SheafOfModules.{u + 1} (cechRing.{u, w} hS n))
    {y : (base.{u, w} hS).val.val.obj}
    (a : CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n)
    (φ : (structureFunctor.{u, w} hS).obj ((cechProjection.{u, w} hS n).obj a) ⟶ y)
    (s : ((cechCompositeDirectImage.{u, w} hS n).obj N).val.presheaf.obj (op y)) :
    cechEval.{u, w} hS n N a φ s =
      ConcreteCategory.hom ((innerCounit N).app (op a))
        ((show compatibleSections (structureFunctor.{u, w} hS).op (innerPresheaf N) (op y)
          from s).val (op ((cechProjection.{u, w} hS n).obj a)) φ.op) :=
  (ConcreteCategory.comp_apply (cechOuterIso.{u, w} hS
      ((compositeInnerDirectImage C S hS (stack.{u, w} hS).val.val.p
        (stack.{u, w} hS).val.isFiberedInGroupoids (cechProjection.{u, w} hS n)
        (cechTopology.{u, w} hS n)).obj N) y).hom
    (Stacks.SheafOfModules.ranπ (structureFunctor.{u, w} hS).op (innerPresheaf N) (op y)
      (StructuredArrow.mk (Y := op ((cechProjection.{u, w} hS n).obj a)) φ.op) ≫
        (innerCounit N).app (op a)) s).trans
  ((ConcreteCategory.comp_apply _ _ _).trans
    (congrArg (ConcreteCategory.hom ((innerCounit N).app (op a)))
      (ranπ_cechOuterIso_hom_apply.{u, w} hS
        ((compositeInnerDirectImage C S hS (stack.{u, w} hS).val.val.p
          (stack.{u, w} hS).val.isFiberedInGroupoids (cechProjection.{u, w} hS n)
          (cechTopology.{u, w} hS n)).obj N) y
        (StructuredArrow.mk (Y := op ((cechProjection.{u, w} hS n).obj a)) φ.op) s)))

/-- The components of sections of `f_* cₙ,* N` are additive. -/
theorem cechEval_add (n : ℕ) (N : SheafOfModules.{u + 1} (cechRing.{u, w} hS n))
    {y : (base.{u, w} hS).val.val.obj}
    (a : CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n)
    (φ : (structureFunctor.{u, w} hS).obj ((cechProjection.{u, w} hS n).obj a) ⟶ y)
    (s s' : ((cechCompositeDirectImage.{u, w} hS n).obj N).val.presheaf.obj (op y)) :
    cechEval.{u, w} hS n N a φ (s + s') =
      cechEval.{u, w} hS n N a φ s + cechEval.{u, w} hS n N a φ s' :=
  map_add _ s s'

/-- The component morphism at `(a, φ)` of the sections of `f_* cₙ,* N` over `y`. -/
abbrev cechEvalHom (n : ℕ) (N : SheafOfModules.{u + 1} (cechRing.{u, w} hS n))
    {y : (base.{u, w} hS).val.val.obj}
    (a : CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n)
    (φ : (structureFunctor.{u, w} hS).obj ((cechProjection.{u, w} hS n).obj a) ⟶ y) :=
  compositeSectionsEvalHom C S hS (stack.{u, w} hS).val.val.p (base.{u, w} hS).val.val.p
    (stack.{u, w} hS).val.isFiberedInGroupoids (base.{u, w} hS).val.isFiberedInGroupoids
    (structureFunctor.{u, w} hS)
    (CatFiberedInGroupoids.homFunctor_comp_p (structureMap.{u, w} hS).hom)
    (cechProjection.{u, w} hS n) (cechTopology.{u, w} hS n) N a φ

/-- The reindexing `c_{m,*} c_m⁻¹ M ⟶ c_{n,*} c_n⁻¹ M` along `θ : [m] ⟶ [n]` of the relative Čech
cosimplicial module, between the inner direct images. -/
abbrev cechReindexMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (M : fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS)) :
    (compositeInnerDirectImage C S hS (stack.{u, w} hS).val.val.p
        (stack.{u, w} hS).val.isFiberedInGroupoids (cechProjection.{u, w} hS m)
        (cechTopology.{u, w} hS m)).obj ((cechInverseImage.{u, w} hS m).obj M) ⟶
      (compositeInnerDirectImage C S hS (stack.{u, w} hS).val.val.p
        (stack.{u, w} hS).val.isFiberedInGroupoids (cechProjection.{u, w} hS n)
        (cechTopology.{u, w} hS n)).obj ((cechInverseImage.{u, w} hS n).obj M) :=
  ((Stacks.RelativeCech.cechModuleEndofunctorCosimplicial.{u, u + 1, u + 1, u, u, u} C S hS
      (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.p
      (stack.{u, w} hS).val.val.p
      (classifyingAtlasFunctor.{u, w} _ (isSmooth_constantZModTwoGroup hS)) .fppf
      (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.isFiberedInGroupoids
      (stack.{u, w} hS).val.isFiberedInGroupoids
      (isFibredOneMorphism_classifyingAtlasFunctor.{u, w} _
        (isSmooth_constantZModTwoGroup hS))).map θ).app M

/-- **The components of a section are compatible with the reindexing of the Čech nerve**: the
component at `a` of the reindexed section is the component of the section at the reindexed
tuple. -/
theorem cechEvalHom_reindex {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (M : fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS))
    {y : (base.{u, w} hS).val.val.obj}
    (a : CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n)
    (φ : (structureFunctor.{u, w} hS).obj ((cechProjection.{u, w} hS n).obj a) ⟶ y) :
    (underlyingPresheafHom ((cechOuterDirectImage.{u, w} hS).map
        (cechReindexMap.{u, w} hS θ M)).val).app (op y) ≫
        cechEvalHom.{u, w} hS n ((cechInverseImage.{u, w} hS n).obj M) a φ =
      cechEvalHom.{u, w} hS m ((cechInverseImage.{u, w} hS m).obj M)
        ((Stacks.RelativeCech.Tuple.reindex _ _ θ.toOrderHom).obj a) φ := by
  rw [cechEvalHom, cechEvalHom, compositeSectionsEvalHom_eq, compositeSectionsEvalHom_eq,
    outerSectionsIso_naturality_left_assoc, Stacks.SheafOfModules.ranπ_map_functor_assoc]
  rfl

/-- The components of a section are compatible with the reindexing of the Čech nerve. -/
theorem cechEval_reindex {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (M : fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS))
    {y : (base.{u, w} hS).val.val.obj}
    (a : CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n)
    (φ : (structureFunctor.{u, w} hS).obj ((cechProjection.{u, w} hS n).obj a) ⟶ y)
    (s : ((cechCompositeDirectImage.{u, w} hS m).obj
      ((cechInverseImage.{u, w} hS m).obj M)).val.presheaf.obj (op y)) :
    cechEval.{u, w} hS n ((cechInverseImage.{u, w} hS n).obj M) a φ
        (ConcreteCategory.hom ((underlyingPresheafHom ((cechOuterDirectImage.{u, w} hS).map
          (cechReindexMap.{u, w} hS θ M)).val).app (op y)) s) =
      cechEval.{u, w} hS m ((cechInverseImage.{u, w} hS m).obj M)
        ((Stacks.RelativeCech.Tuple.reindex _ _ θ.toOrderHom).obj a) φ s :=
  (ConcreteCategory.comp_apply _ _ s).symm.trans
    (ConcreteCategory.congr_hom (cechEvalHom_reindex.{u, w} hS θ M a φ) s)

/-- **The sections formula for `f_* cₙ,*` at one module**: the component at the terminal arrow
identifies the sections over `y` with the sections over the canonical tuple of the universal
points on `y.left ×_S Gⁿ`. -/
def cechSectionsIsoApp (y : (base.{u, w} hS).val.val.obj) (n : ℕ)
    (N : SheafOfModules.{u + 1} (cechRing.{u, w} hS n)) :
    ((cechCompositeDirectImage.{u, w} hS n).obj N).val.presheaf.obj (op y) ≅
      N.val.presheaf.obj (op (cechTerminal.{u, w} hS y n).left) :=
  compositeSectionsIsoOfIsTerminalApp (B := C) (S := S) (hS := hS)
    (q := (stack.{u, w} hS).val.val.p) (r := (base.{u, w} hS).val.val.p)
    (hq := (stack.{u, w} hS).val.isFiberedInGroupoids)
    (hr := (base.{u, w} hS).val.isFiberedInGroupoids)
    (F := CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom)
    (hF := CatFiberedInGroupoids.homFunctor_comp_p (structureMap.{u, w} hS).hom)
    (c := cechProjection.{u, w} hS n) (J := cechTopology.{u, w} hS n) N
    (isTerminalCechTerminal.{u, w} hS y n)

/-- The forward map of `cechSectionsIsoApp` is the component at the terminal arrow. -/
theorem cechSectionsIsoApp_hom (y : (base.{u, w} hS).val.val.obj) (n : ℕ)
    (N : SheafOfModules.{u + 1} (cechRing.{u, w} hS n))
    (s : ((cechCompositeDirectImage.{u, w} hS n).obj N).val.presheaf.obj (op y)) :
    ConcreteCategory.hom (cechSectionsIsoApp.{u, w} hS y n N).hom s =
      cechEval.{u, w} hS n N (cechTerminal.{u, w} hS y n).left (cechTerminal.{u, w} hS y n).hom s :=
  rfl

/-- The composite `f_* cₙ,* cₙ⁻¹` written as a composite of three functors. -/
abbrev cechCompositeFunctor (n : ℕ) :
    fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS) ⥤
      fppfModulesUnivLE.{u, w, u + 1} C S hS (base.{u, w} hS) :=
  cechInverseImage.{u, w} hS n ⋙ cechDirectImageProjection.{u, w} hS n ⋙
    fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS)

/-- The morphisms of the degree `n` term of the relative Čech complex. -/
theorem cechComplex_map_f (n : ℕ) {M M' : fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS)}
    (ψ : M ⟶ M') :
    ((cechComplex.{u, w} hS).map ψ).f n =
      (cechDirectImageProjection.{u, w} hS n).map ((cechInverseImage.{u, w} hS n).map ψ) :=
  rfl

/-- The degree `n` term of the relative Čech complex is `cₙ,* cₙ⁻¹`. -/
def cechComplexEvalIso (n : ℕ) :
    cechComplex.{u, w} hS ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) n ≅
      cechInverseImage.{u, w} hS n ⋙ cechDirectImageProjection.{u, w} hS n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun ψ =>
    (Category.comp_id _).trans ((cechComplex_map_f.{u, w} hS n ψ).trans (Category.id_comp _).symm))

/-- `f_* cₙ,* cₙ⁻¹`, as the degree `n` term of the Čech complex followed by `f_*`, is the
composite of the three functors. -/
def cechDirectImageIso (n : ℕ) : cechDirectImage.{u, w} hS n ≅ cechCompositeFunctor.{u, w} hS n :=
  Functor.isoWhiskerRight (cechComplexEvalIso.{u, w} hS n)
    (fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS))

/-- `f_* cₙ,* cₙ⁻¹` on morphisms of sections is the composite `f_* cₙ,*` applied to `cₙ⁻¹`. -/
theorem cechCompositeFunctor_comp_sections_map (y : (base.{u, w} hS).val.val.obj) (n : ℕ)
    {M M' : fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS)} (ψ : M ⟶ M') :
    (cechCompositeFunctor.{u, w} hS n ⋙ SheafOfModules.toSheaf _ ⋙
        (sheafSections _ AddCommGrpCat.{u + 1}).obj (op y)).map ψ =
      (cechCompositeDirectImage.{u, w} hS n ⋙ SheafOfModules.toSheaf _ ⋙
        (sheafSections _ AddCommGrpCat.{u + 1}).obj (op y)).map
          ((cechInverseImage.{u, w} hS n).map ψ) :=
  rfl

/-- The sections over the trivial torsor of a morphism are the sections over the terminal
tuple of its inverse image. -/
theorem cechSectionsObj_sections_map (y : (base.{u, w} hS).val.val.obj) (n : ℕ)
    {M M' : fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS)} (ψ : M ⟶ M') :
    (SheafOfModules.toSheaf _ ⋙
        (sheafSections _ AddCommGrpCat.{u + 1}).obj (op (cechSectionsObj.{u, w} hS y n))).map ψ =
      (SheafOfModules.toSheaf _ ⋙ (sheafSections (cechTopology.{u, w} hS n)
        AddCommGrpCat.{u + 1}).obj (op (cechTerminal.{u, w} hS y n).left)).map
          ((cechInverseImage.{u, w} hS n).map ψ) :=
  rfl

/-- `cechSectionsIsoApp` is natural in the module, in the form of the composite `f_* cₙ,*`. -/
theorem cechSectionsIsoApp_naturality_aux (y : (base.{u, w} hS).val.val.obj) (n : ℕ)
    {M M' : fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS)} (ψ : M ⟶ M') :
    (cechCompositeDirectImage.{u, w} hS n ⋙ SheafOfModules.toSheaf _ ⋙
        (sheafSections _ AddCommGrpCat.{u + 1}).obj (op y)).map
          ((cechInverseImage.{u, w} hS n).map ψ) ≫
        (cechSectionsIsoApp.{u, w} hS y n ((cechInverseImage.{u, w} hS n).obj M')).hom =
      (cechSectionsIsoApp.{u, w} hS y n ((cechInverseImage.{u, w} hS n).obj M)).hom ≫
        (SheafOfModules.toSheaf _ ⋙ (sheafSections (cechTopology.{u, w} hS n)
          AddCommGrpCat.{u + 1}).obj (op (cechTerminal.{u, w} hS y n).left)).map
            ((cechInverseImage.{u, w} hS n).map ψ) :=
  compositeSectionsIsoOfIsTerminalApp_naturality (B := C) (S := S) (hS := hS)
    (q := (stack.{u, w} hS).val.val.p) (r := (base.{u, w} hS).val.val.p)
    (hq := (stack.{u, w} hS).val.isFiberedInGroupoids)
    (hr := (base.{u, w} hS).val.isFiberedInGroupoids)
    (F := CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom)
    (hF := CatFiberedInGroupoids.homFunctor_comp_p (structureMap.{u, w} hS).hom)
    (c := cechProjection.{u, w} hS n) (J := cechTopology.{u, w} hS n)
    (isTerminalCechTerminal.{u, w} hS y n) ((cechInverseImage.{u, w} hS n).map ψ)

/-- `cechSectionsIsoApp` is natural in the module. -/
theorem cechSectionsIsoApp_naturality (y : (base.{u, w} hS).val.val.obj) (n : ℕ)
    {M M' : fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS)} (ψ : M ⟶ M') :
    (cechCompositeFunctor.{u, w} hS n ⋙ SheafOfModules.toSheaf _ ⋙
        (sheafSections _ AddCommGrpCat.{u + 1}).obj (op y)).map ψ ≫
        (cechSectionsIsoApp.{u, w} hS y n ((cechInverseImage.{u, w} hS n).obj M')).hom =
      (cechSectionsIsoApp.{u, w} hS y n ((cechInverseImage.{u, w} hS n).obj M)).hom ≫
        (SheafOfModules.toSheaf _ ⋙
          (sheafSections _ AddCommGrpCat.{u + 1}).obj (op (cechSectionsObj.{u, w} hS y n))).map
            ψ := by
  rw [cechCompositeFunctor_comp_sections_map]
  exact (cechSectionsIsoApp_naturality_aux.{u, w} hS y n ψ).trans
    (congrArg (_ ≫ ·) (cechSectionsObj_sections_map.{u, w} hS y n ψ).symm)

/-- **The sections formula for `f_* cₙ,* cₙ⁻¹`**: its sections over `y` are the sections over the
trivial torsor on `y.left ×_S Gⁿ`, naturally in the module. -/
def cechCompositeSectionsIso (y : (base.{u, w} hS).val.val.obj) (n : ℕ) :
    cechCompositeFunctor.{u, w} hS n ⋙ SheafOfModules.toSheaf _ ⋙
        (sheafSections _ AddCommGrpCat.{u + 1}).obj (op y) ≅
      SheafOfModules.toSheaf _ ⋙
        (sheafSections _ AddCommGrpCat.{u + 1}).obj (op (cechSectionsObj.{u, w} hS y n)) :=
  NatIso.ofComponents
    (fun M => cechSectionsIsoApp.{u, w} hS y n ((cechInverseImage.{u, w} hS n).obj M))
    (fun ψ => cechSectionsIsoApp_naturality.{u, w} hS y n ψ)

/-- The object computing the sections over `y` lies over an affine scheme when `y` does. -/
theorem isAffineOver_cechSectionsObj (y : (base.{u, w} hS).val.val.obj) (n : ℕ)
    (hy : IsAffine (FibredSite.schemeOf C S hS (base.{u, w} hS).val.val.p y)) :
    IsAffineOver C S hS ((stack.{u, w} hS).val.val.p.obj (cechSectionsObj.{u, w} hS y n)) := by
  rw [stackProj_atlasFunctor_obj]
  exact isAffineOver_powerObj y.left n hy

/-- The inverse image along a projection of the Čech nerve preserves finite limits. -/
instance preservesFiniteLimits_cechInverseImage (n : ℕ) :
    PreservesFiniteLimits (cechInverseImage.{u, w} hS n) :=
  preservesFiniteLimits_of_natIso (SheafOfModules.pushforwardIdIsoPushforward₀ _ _ _ _)

/-- The direct image along a projection of the Čech nerve preserves finite limits, being a right
adjoint. -/
instance preservesFiniteLimits_cechDirectImageProjection (n : ℕ) :
    PreservesFiniteLimits (cechDirectImageProjection.{u, w} hS n) := by
  have : PreservesLimitsOfSize.{0, 0} (cechDirectImageProjection.{u, w} hS n) :=
    (SheafOfModules.pushforward₀DirectImageAdjunction _ _ _ _).rightAdjoint_preservesLimits
  infer_instance

/-- The direct image along the structure morphism preserves finite limits, being a right
adjoint. -/
instance preservesFiniteLimits_fppfModuleSheafPushforwardOfStacks_structureMap :
    PreservesFiniteLimits (fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS)) := by
  have : PreservesLimitsOfSize.{0, 0}
      (fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS)) :=
    (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} C S hS _ _ _ _ _ _ _
      _).rightAdjoint_preservesLimits
  infer_instance

/-- `f_* cₙ,* cₙ⁻¹` preserves finite limits. -/
instance preservesFiniteLimits_cechCompositeFunctor (n : ℕ) :
    PreservesFiniteLimits (cechCompositeFunctor.{u, w} hS n) := by
  have h₁ := preservesFiniteLimits_cechInverseImage.{u, w} hS n
  have h₂ := preservesFiniteLimits_cechDirectImageProjection.{u, w} hS n
  have h₃ := preservesFiniteLimits_fppfModuleSheafPushforwardOfStacks_structureMap.{u, w} hS
  have h₄ : PreservesFiniteLimits (cechDirectImageProjection.{u, w} hS n ⋙
      fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS)) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ (cechDirectImageProjection.{u, w} hS n)
      (fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS)) h₂ h₃
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ (cechInverseImage.{u, w} hS n)
    (cechDirectImageProjection.{u, w} hS n ⋙
      fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS)) h₁ h₄

/-- `f_* cₙ,* cₙ⁻¹`, as the degree `n` term of the Čech complex followed by `f_*`, preserves
finite limits. -/
instance preservesFiniteLimits_cechDirectImage (n : ℕ) :
    PreservesFiniteLimits (cechDirectImage.{u, w} hS n) :=
  preservesFiniteLimits_of_natIso (cechDirectImageIso.{u, w} hS n).symm

/-- `f_* cₙ,* cₙ⁻¹` is additive. -/
instance additive_cechCompositeFunctor (n : ℕ) : (cechCompositeFunctor.{u, w} hS n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `f_* cₙ,* cₙ⁻¹`, as the degree `n` term of the Čech complex followed by `f_*`, is
additive. -/
instance additive_cechDirectImage (n : ℕ) : (cechDirectImage.{u, w} hS n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The higher right derived functors of the composite `f_* cₙ,* cₙ⁻¹` vanish at the structure
sheaf of `B(ℤ/2)_S`. -/
theorem isZero_rightDerived_cechCompositeFunctor_uliftUnit (n q : ℕ) (hq : 0 < q) :
    letI := enoughInjectives_fppfModulesUnivLESucc C S hS (stack.{u, w} hS)
    IsZero (((cechCompositeFunctor.{u, w} hS n).rightDerived q).obj
      (Stacks.SheafOfModules.uliftUnit.{u + 1} _)) := by
  have := enoughInjectives_fppfModulesUnivLESucc C S hS (stack.{u, w} hS)
  exact SheafOfModules.isZero_rightDerived_of_sectionsFormula (cechCompositeFunctor.{u, w} hS n)
    (fun y => IsAffine (FibredSite.schemeOf C S hS (base.{u, w} hS).val.val.p y))
    (FibredSite.mem_of_forall_isAffine C S hS (base.{u, w} hS).val.val.p
      (base.{u, w} hS).val.isFiberedInGroupoids)
    (fun y _ => cechSectionsObj.{u, w} hS y n)
    (fun y _ => cechCompositeSectionsIso.{u, w} hS y n) _
    (fun y hy m hm => isZero_rightDerived_evaluation_uliftUnit_of_isAffineOver C S hS
      (stack.{u, w} hS) (isAffineOver_cechSectionsObj.{u, w} hS y n hy) m hm) q hq

/-- **The higher right derived functors of `f_* cₙ,* cₙ⁻¹` vanish at the structure sheaf** of
`B(ℤ/2)_S`, at module universe `u + 1`. -/
theorem isZero_rightDerived_cechDirectImage_uliftUnit (n q : ℕ) (hq : 0 < q) :
    letI := enoughInjectives_fppfModulesUnivLESucc C S hS (stack.{u, w} hS)
    IsZero (((cechDirectImage.{u, w} hS n).rightDerived q).obj
      (Stacks.SheafOfModules.uliftUnit.{u + 1} _)) := by
  have := enoughInjectives_fppfModulesUnivLESucc C S hS (stack.{u, w} hS)
  refine (isZero_rightDerived_cechCompositeFunctor_uliftUnit.{u, w} hS n q hq).of_iso
    { hom := (NatTrans.rightDerived (cechDirectImageIso.{u, w} hS n).hom q).app _
      inv := (NatTrans.rightDerived (cechDirectImageIso.{u, w} hS n).inv q).app _
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, Iso.hom_inv_id,
      NatTrans.rightDerived_id, NatTrans.id_app]
  · rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, Iso.inv_hom_id,
      NatTrans.rightDerived_id, NatTrans.id_app]

end AlgebraicGeometry.Stack.ClassifyingZModTwo

end
