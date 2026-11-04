module

public import
  StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekCovariance
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeTraceSection
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeDualizingModule
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel

/-!
# Covariance of compactly supported cohomology for flat quasi-finite morphisms

In Situation [Stacks, Tag 0F42] let

`U --h--> X --f--> Y`,  `g = f ∘ h`

be a commutative diagram of `FTS_S` with `h` flat and quasi-finite. [Stacks, Tag 0G58] says there
is a canonical transformation `Rg_! ∘ h^* ⟶ Rf_!`, constructed as in [Stacks, Tag 0G57] from a
transformation `h^* ⟶ h^!`, which in turn comes from:

* `h^! K = h^* K ⊗ ω_{U/X}` with `ω_{U/X} = h^! 𝒪_X` ([Stacks, Tag 0B6U], [Stacks, Tag 0BV7]);
* `ω_{U/X}` is the relative dualizing module of `h` ([Stacks, Tag 0BVG], [Stacks, Tag 0BUL]);
* the trace element `τ_{U/X} : 𝒪_U ⟶ ω_{U/X}` ([Stacks, Tag 0BVJ]).

The transformation `h^* K ⟶ h^! K` is

`h^* K ≅ h^* K ⊗ 𝒪_U --(1 ⊗ τ_{U/X})--> h^* K ⊗ h^! 𝒪_X ≅ h^! K`,

and the transformation `Rg_!(h^* K) ⟶ Rf_! K` is then the one of [Stacks, Tag 0G2X] attached to

`Hom(Rf_! K, L) = Hom_X(K, f^! L) ⟶ Hom_U(h^* K, h^* f^! L) ⟶ Hom_U(h^* K, h^! f^! L)
  = Hom_U(h^* K, g^! L) = Hom(Rg_!(h^* K), L)`,

using [Stacks, Tag 0G51] twice and `h^! ∘ f^! = g^!` ([Stacks, Tag 0ATX]).

## Main definitions

* `CategoryTheory.homMapNatTransOfHom`: the transformation `Hom(A, F₁ -) ⟶ Hom(H A, F₂ -)`
  induced by a functor `H` and a transformation `H ∘ F₁ ⟶ F₂`.
* `Stacks.Duality.upperShriekTraceMap`: `τ_{U/X} : 𝒪_U ⟶ h^! 𝒪_X` in `D_QCoh(𝒪_U)`.
* `Stacks.Duality.pullbackToUpperShriekOfFlatQuasiFinite`: `h^* ⟶ h^!` on `D^+_QCoh(𝒪_X)`.
* `AlgebraicGeometry.lowerShriekFlatQuasiFiniteMap`: **[Stacks, Tag 0G58]**.

## References

* [Stacks Project, Tag 0G58](https://stacks.math.columbia.edu/tag/0G58)
* [Stacks Project, Tag 0G57](https://stacks.math.columbia.edu/tag/0G57)
* [Stacks Project, Tag 0BVJ](https://stacks.math.columbia.edu/tag/0BVJ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

variable {𝒜 : Type u₁} [Category.{v} 𝒜] {𝒜' : Type u₂} [Category.{v} 𝒜']
  {𝒳 : Type u₃} [Category.{v} 𝒳] {𝒳' : Type u₄} [Category.{v} 𝒳'] {ℬ : Type u₅} [Category.{v} ℬ]

/-- The transformation `Hom(ι₁ A, F₁ B) ⟶ Hom(ι₂ (H A), F₂ B)`, `φ ↦ β⁻¹ ≫ Hs φ ≫ θ`, induced by a
functor `Hs`, an identification `β : ι₁ ⋙ Hs ≅ H ⋙ ι₂` and a transformation
`θ : F₁ ⋙ Hs ⟶ F₂`. For `θ` an isomorphism this is `CategoryTheory.homMapNatTrans`. -/
def homMapNatTransOfHom (ι₁ : 𝒜 ⥤ 𝒳) (ι₂ : 𝒜' ⥤ 𝒳') (H : 𝒜 ⥤ 𝒜') (Hs : 𝒳 ⥤ 𝒳')
    (β : ι₁ ⋙ Hs ≅ H ⋙ ι₂) (F₁ : ℬ ⥤ 𝒳) (F₂ : ℬ ⥤ 𝒳') (θ : F₁ ⋙ Hs ⟶ F₂) :
    ι₁.op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F₁ ⟶
      H.op ⋙ ι₂.op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F₂ where
  app A :=
    { app := fun B => ↾fun φ => β.inv.app A.unop ≫ Hs.map φ ≫ θ.app B
      naturality := fun {B B'} b => by
        ext φ
        change β.inv.app A.unop ≫ Hs.map (φ ≫ F₁.map b) ≫ θ.app B' =
          (β.inv.app A.unop ≫ Hs.map φ ≫ θ.app B) ≫ F₂.map b
        rw [Hs.map_comp, Category.assoc, Category.assoc, Category.assoc]
        exact congrArg (fun t => β.inv.app A.unop ≫ Hs.map φ ≫ t) (θ.naturality b) }
  naturality {A A'} a := by
    ext B φ
    change β.inv.app A'.unop ≫ Hs.map (ι₁.map a.unop ≫ φ) ≫ θ.app B =
      ι₂.map (H.map a.unop) ≫ β.inv.app A.unop ≫ Hs.map φ ≫ θ.app B
    have h := β.inv.naturality a.unop
    simp only [Functor.comp_map] at h
    rw [Hs.map_comp, ← Category.assoc, ← Category.assoc, ← h]
    simp only [Category.assoc]

/-- For an isomorphism `θ`, `CategoryTheory.homMapNatTransOfHom` is
`CategoryTheory.homMapNatTrans`. -/
theorem homMapNatTransOfHom_hom (ι₁ : 𝒜 ⥤ 𝒳) (ι₂ : 𝒜' ⥤ 𝒳') (H : 𝒜 ⥤ 𝒜') (Hs : 𝒳 ⥤ 𝒳')
    (β : ι₁ ⋙ Hs ≅ H ⋙ ι₂) (F₁ : ℬ ⥤ 𝒳) (F₂ : ℬ ⥤ 𝒳') (θ : F₁ ⋙ Hs ≅ F₂) :
    homMapNatTransOfHom ι₁ ι₂ H Hs β F₁ F₂ θ.hom = homMapNatTrans ι₁ ι₂ H Hs β F₁ F₂ θ :=
  rfl

end CategoryTheory

namespace Stacks.Duality

open DerivedPushforward Stacks.Discriminant

variable {S : Scheme.{u}} [IsNoetherian S] {U X : FTS S} (h : U ⟶ X) [Flat h.left]
  [LocallyQuasiFinite h.left] (ch : CompactificationOf (Over.mk h.left))

/-- For `h` flat and quasi-finite, `h^! 𝒪_X` is concentrated in degree `0` ([Stacks, Tag 0BV7]),
so in particular in degrees `≥ 0`. -/
instance isGE_relativeDualizingComplexObj_of_flat_of_locallyQuasiFinite :
    (relativeDualizingComplexObj h ch).IsGE 0 := by
  obtain ⟨ω, -, -, ⟨e⟩⟩ := exists_isCoherent_isFlatOver_iso_single h ch
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm 0

/-- **The trace element `τ_{U/X}`** ([Stacks, Tag 0BVJ]) of the flat quasi-finite morphism `h`,
as a global section of `ω_{U/X} = H⁰(h^! 𝒪_X)`, the relative dualizing module of `h`
([Stacks, Tag 0BVG], [Stacks, Tag 0BUL]). -/
abbrev upperShriekTraceElement : Γ(upperShriekStructureSheafZeroth h ch, ⊤) :=
  relativeTraceSection (upperShriekRelativeDualizingModuleData h ch)

/-- **The trace `τ_{U/X} : 𝒪_U ⟶ ω_{U/X} = h^! 𝒪_X`** in `D_QCoh(𝒪_U)`: the morphism of
`𝒪_U`-modules `𝒪_U ⟶ H⁰(h^! 𝒪_X)` sending `1` to the trace element
`Stacks.Duality.upperShriekTraceElement`, read as a morphism `𝒪_U[0] ⟶ h^! 𝒪_X` since `h^! 𝒪_X`
is concentrated in degrees `≥ 0` ([Stacks, Tag 0BV7]). -/
def upperShriekTraceMap :
    derivedStructureSheaf U.left ⟶ (upperShriek h ch).obj (derivedStructureSheaf X.left) :=
  ObjectProperty.homMk
    ((Equiv.ofBijective _ (DerivedCategory.bijective_homologyFromSingle_of_isGE
      (C := U.left.Modules) (SheafOfModules.unit U.left.ringCatSheaf)
      (relativeDualizingComplexObj h ch) 0)).symm
      ((SheafOfModules.unitHomEquiv _).symm
        ((Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal _
          isTerminalTop).symm (upperShriekTraceElement h ch))))

/-- `upperShriekTraceMap` is the morphism inducing `𝒪_U ⟶ H⁰(h^! 𝒪_X)`, `1 ↦ τ_{U/X}`, on
cohomology in degree `0`. -/
theorem homologyFromSingle_upperShriekTraceMap :
    DerivedCategory.homologyFromSingle (C := U.left.Modules)
        (SheafOfModules.unit U.left.ringCatSheaf)
        (relativeDualizingComplexObj h ch) 0 (upperShriekTraceMap h ch).hom =
      (SheafOfModules.unitHomEquiv _).symm
        ((Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal _
          isTerminalTop).symm (upperShriekTraceElement h ch)) :=
  Function.surjInv_eq (DerivedCategory.bijective_homologyFromSingle_of_isGE _ _ 0).2 _

/-- **The transformation `h^* ⟶ h^!`** on `D^+_QCoh(𝒪_X)` for `h` flat and quasi-finite, at the
compactification `ch` of `h`:

`h^* K ≅ h^* K ⊗ 𝒪_U --(1 ⊗ τ_{U/X})--> h^* K ⊗ h^! 𝒪_X ≅ h^! K`,

where `τ_{U/X}` is the trace `Stacks.Duality.upperShriekTraceMap` and the last isomorphism is
`h^! K = h^* K ⊗ ω_{U/X}` of [Stacks, Tag 0B6U] (`h` is flat of finite presentation, hence
perfect). -/
def pullbackToUpperShriekOfFlatQuasiFinite :
    (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel X.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' h.left ⟶
      (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel X.left ⥤ _) ⋙
        upperShriek h ch :=
  haveI := locallyOfFinitePresentation_left h
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft
      ((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel X.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' h.left)
      ((quasiCoherentDerivedTensorRightUnitor U.left).inv ≫
        (quasiCoherentDerivedTensor U.left).flip.map (upperShriekTraceMap h ch)) ≫
    (upperShriekCompareWithPullbackPlusIso h ch).hom

end Stacks.Duality

namespace Stacks.Duality.UpperShriekDuality

open TwistedInverseImageDuality

variable {S : Scheme.{u}} [IsNoetherian S] {U X Y : FTS S}

/-- **`h^* ∘ f^! ⟶ g^!` for `g = f ∘ h` and `h` flat and quasi-finite**: the transformation
`h^* ⟶ h^!` of `Stacks.Duality.pullbackToUpperShriekOfFlatQuasiFinite` applied to `f^!`, followed
by `h^! f^! = g^!` ([Stacks, Tag 0ATX]), for arbitrary compactifications, at the standard model
on `D^+_{Coh}`. -/
def upperShriekStdPullFlatQuasiFiniteHom (h : U ⟶ X) [Flat h.left] [LocallyQuasiFinite h.left]
    (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))
    (ch : CompactificationOf (Over.mk h.left))
    (cU : CompactificationOf (Over.mk (h ≫ f).left)) :
    upperShriekStd f c ⋙ pull h.left ⟶ upperShriekStd (h ≫ f) cU :=
  (upperShriekStdPullIso h f c).hom ≫
    (Functor.whiskerLeft (plusCohToQCohPlus Y.left ⋙ upperShriekPlus f c)
      (Functor.whiskerRight (pullbackToUpperShriekOfFlatQuasiFinite h ch)
        ((ObjectProperty.ι _ : quasiCoherentDerivedCategory U.left ⥤ _) ⋙
          (comparison U.left).inverse)) :
      plusCohToQCoh Y.left ⋙ upperShriek f c ⋙ quasiCoherentDerivedPullback' h.left ⋙
          (ObjectProperty.ι _ : quasiCoherentDerivedCategory U.left ⥤ _) ⋙
            (comparison U.left).inverse ⟶
        plusCohToQCohPlus Y.left ⋙ (upperShriekPlus f c ⋙ upperShriekPlus h ch) ⋙
          ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison U.left).inverse) ≫
    (Functor.isoWhiskerLeft (plusCohToQCohPlus Y.left)
      (Functor.isoWhiskerRight (upperShriekCompIso h f ch c cU).symm
        (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison U.left).inverse)) :
      plusCohToQCohPlus Y.left ⋙ (upperShriekPlus f c ⋙ upperShriekPlus h ch) ⋙
          ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison U.left).inverse ≅
        upperShriekStd (h ≫ f) cU).hom

end Stacks.Duality.UpperShriekDuality

namespace AlgebraicGeometry

open Stacks.Duality Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 10000] CategoryTheory.Functor.hasLeftKanExtension_of_type
  CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_type
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

variable {S : Scheme.{u}} [IsNoetherian S] {U X Y : FTS S}

/-- **Stacks Project, Tag 0G58.** In Situation [Stacks, Tag 0F42] let

`U --h--> X --f--> Y`,  `g = f ∘ h`

be a commutative diagram of `FTS_S` with `h` flat and quasi-finite. Then there is a canonical
transformation

`Rg_! ∘ h^* ⟶ Rf_!`

of functors on `D^b_{Coh}(𝒪_X)`, constructed as in [Stacks, Tag 0G57] from the transformation
`h^* ⟶ h^!` on `D^+_{Coh}(𝒪_X)` (`Stacks.Duality.pullbackToUpperShriekOfFlatQuasiFinite`) given by
`h^! K = h^* K ⊗ ω_{U/X}`, `ω_{U/X} = h^! 𝒪_X` the relative dualizing module of `h`
([Stacks, Tag 0B6U], [Stacks, Tag 0BV7], [Stacks, Tag 0BVG], [Stacks, Tag 0BUL]), and the trace
element `τ_{U/X} : 𝒪_U ⟶ ω_{U/X}` ([Stacks, Tag 0BVJ]): for `L` in `D^b_{Coh}(𝒪_Y)`,

`Hom(Rf_! K, L) = Hom_X(K, f^! L) ⟶ Hom_U(h^* K, h^* f^! L) ⟶ Hom_U(h^* K, h^! f^! L)
  = Hom_U(h^* K, g^! L) = Hom(Rg_!(h^* K), L)`,

by [Stacks, Tag 0G51] twice and `h^! ∘ f^! = g^!` ([Stacks, Tag 0ATX]); the functoriality in `L`
gives the morphism of pro-objects by [Stacks, Tag 0G2X] (`AlgebraicGeometry.lowerShriekMapOfHom`).
Quasi-finiteness is `LocallyQuasiFinite`, morphisms of `FTS_S` being quasi-compact. `Rf_!` and
`Rg_!` are computed at arbitrary compactifications `c` and `cU`, and `h^!` at the
compactification of `h` obtained from them
(`Stacks.Duality.CompCompactification.restrictCompactification`). -/
@[stacks 0G58]
def lowerShriekFlatQuasiFiniteMap (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))
    (h : U ⟶ X) [Flat h.left] [LocallyQuasiFinite h.left] (g : U ⟶ Y) (w : h ≫ f = g)
    (cU : CompactificationOf (Over.mk g.left)) :
    boundedCoherentPullback h.left ⋙ lowerShriek g cU ⟶ lowerShriek f c := by
  subst w
  exact lowerShriekMapOfHom f c (h ≫ f) cU (boundedCoherentPullback h.left)
    (homMapNatTransOfHom (boundedCoherentDerived X.left).ι (boundedCoherentDerived U.left).ι
      (boundedCoherentPullback h.left) (pull h.left) (boundedCoherentPullbackPullIso h.left)
      (upperShriekStd f c) (upperShriekStd (h ≫ f) cU)
      (upperShriekStdPullFlatQuasiFiniteHom h f c
        (CompCompactification.restrictCompactification h f c cU) cU))

end AlgebraicGeometry
