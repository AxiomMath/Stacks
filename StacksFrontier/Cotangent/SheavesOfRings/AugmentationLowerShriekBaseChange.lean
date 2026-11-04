module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.AugmentationDerivedBaseChangeFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.AugmentationMooreColumnRow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.DerivedProjectionMooreComplexModules
public import StacksFrontier.Cotangent.SheavesOfRings.MooreSplice
public import StacksFrontier.Cotangent.SheavesOfRings.SimplicialResolutionMooreQuasiIso

/-!
# The sheafification square for base change along an augmentation

Let `(C, J)` be a small site, let `A_•` be a simplicial sheaf of commutative rings on it and let
`ε : A_• ⟶ O` be an augmentation.  Write `K` for the topology of the simplicial site `Δ × C`,
`Lε^* = - ⊗^𝐋_{A_•} π^{-1}O : D(A_•) ⟶ D(π^{-1}O)` for the derived extension of scalars of
[Stacks, Tag 09D3] and `Lπ_! : D(π^{-1}O) ⟶ D(O)` for the derived lower shriek of
[Stacks, Tag 09CY].

Base change along `A_• ⟶ π^{-1}O` on the simplicial site has two spellings: the *presheaf*-level
change of rings `- ⊗_{A_•} π^{-1}O` of [Stacks, Tag 03CU], at which the column and row steps of
[Stacks, Tag 08RX] are stated, and the degreewise *sheaf*-level extension of scalars of
[Stacks, Tag 03CZ], at which `Stacks.SimplicialModules.augmentationBaseChangeFlatIso` computes
`Lε^*`. This file identifies the two after sheafification and shows that the identification
carries one base-change unit to the other, for the proof of [Stacks, Tag 09D2] with module
coefficients.

## Main definitions and results

* `Stacks.SimplicialModules.augmentationSheafifyExtendScalarsIso`: sheafification carries the
  presheaf-level change of rings to the sheaf-level extension of scalars, on complexes.
* `Stacks.SimplicialModules.augSheafifyComparison`: the comparison from the presheaf-level base
  change of a complex to the sheaf-level one, with
  `Stacks.SimplicialModules.isIso_augMooreTgtC_map_augSheafifyComparison`: **`s(-)` inverts it**,
  because its first leg is the unit of sheafification, which sheafification inverts, and `s(-)`
  inverts whatever sheafification inverts
  (`Stacks.SimplicialModules.isIso_mooreSheafCochain_map_of_W`).
* `Stacks.SimplicialModules.unit_comp_augSheafifyComparison` and
  `Stacks.SimplicialModules.unit_comp_augSheafifyComparison_comp_adjoint`: the comparison carries
  the presheaf-level base-change unit to the sheaf-level one.
* `Stacks.SimplicialModules.isFlat_augSrcSheafify_obj_of_isStdCover`: the sheafification of a
  standard cover is a flat sheaf of `A_•`-modules — [Stacks, Tag 03ES] followed by
  [Stacks, Tag 03ET].
* `Stacks.SimplicialModules.quasiIso_augSrcSheafifyAdjC_homEquiv_symm`: the transpose
  `L^•_♯ ⟶ ε_* X^•` of a quasi-isomorphism `L^• ⟶ (ε_* X^•)^{pre}` is a quasi-isomorphism.
* the boundedness instances for the functor images, and the additivity of the four left adjoints.

## Implementation notes

`- ⊗_{A_•} π^{-1}O` followed by degreewise sheafification and degreewise sheafification followed
by sheaf-level extension of scalars are both left adjoint to "forget the sheaf condition, then
restrict scalars along `A_• ⟶ π^{-1}O`", so uniqueness of left adjoints
(`CategoryTheory.Adjunction.leftAdjointUniq`) identifies them.  The compatibility with the
base-change units is the defining property of `leftAdjointUniq`
(`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`), as for
`Stacks.SheafOfModules.ChangeOfRings.unit_comp_restrictScalars_map_extendScalarsIsoTensor_hom_app`,
which crosses the two *sheaf*-level spellings of extension of scalars.

The derived counit `Lε^* ε_* ⟶ id` on `D(π^{-1}O)` is not an isomorphism.  `Lε^*` is computed on
the fibres, so `H^{-i}(Lε^*(ε_* N))` restricted to `{n} × C` is `Tor_i^{P_n}(N, O)`, and for the
standard resolution `Tor_1^{P_n}(O, O) = I_n/I_n²` is `Ω_{P_n/A} ⊗ O`, nonzero whenever the
cotangent complex is.  The underived counit `ε^* ε_* ≅ id` *is* invertible, because `ε` is
surjective in each degree.  The Tor terms cancel only under `L π_!`, under the hypothesis of
[Stacks, Tag 09D2], so the comparison is made on the simplicial site, before `L π_!`.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3)
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03ES](https://stacks.math.columbia.edu/tag/03ES)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.PresheafOfModules.ChangeOfRings (ringPresheaf changeOfRings restrictScalars
  changeOfRingsAdjunction unitMap)

namespace Stacks.SimplicialModules

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A : SimplicialObject (Sheaf J CommRingCat.{u})} {O : Sheaf J CommRingCat.{u}}
  (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O)

/-! ### The two sheaves of rings on `Δ × C` and the map between them

They are written as `Stacks.Sheaves.RingedToposModules` writes sheaves of rings — a presheaf of
commutative rings together with the sheaf condition on the underlying presheaf of rings — and are
definitionally `(Stacks.Cohomology.ringedTopos _ _).ringSheaf` and
`Stacks.SimplicialModules.projectionRingSheaf`. -/

/-- The sheaf condition on the presheaf of rings underlying `A_•` on `Δ × C`. -/
theorem augSrcIsSheaf : Presheaf.IsSheaf (projectionTopology C J)
    (ringPresheaf (simplicialCommRingSheaf J A).obj) :=
  ((sheafCompose (projectionTopology C J)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (simplicialCommRingSheaf J A)).property

/-- The sheaf condition on the presheaf of rings underlying `π^{-1}O` on `Δ × C`. -/
theorem augTgtIsSheaf : Presheaf.IsSheaf (projectionTopology C J)
    (ringPresheaf (projectionCommRing J O).obj) :=
  (projectionRingSheaf J O).property

/-- `A_•` read as a sheaf of rings on `Δ × C`. -/
abbrev augSrcRing : Sheaf (projectionTopology C J) RingCat.{u} :=
  Stacks.Sheaves.RingedToposModules.commRingSheaf (projectionTopology C J)
    (simplicialCommRingSheaf J A).obj (augSrcIsSheaf J (A := A))

/-- `π^{-1}O` read as a sheaf of rings on `Δ × C`. -/
abbrev augTgtRing : Sheaf (projectionTopology C J) RingCat.{u} :=
  projectionRingSheaf J O

/-- The presheaf of rings underlying `π^{-1}O` on `Δ × C`, in the `ringPresheaf` spelling.  It
is `(Stacks.SimplicialModules.augTgtRing J).obj`, but that projection does not reduce at instance
transparency. -/
abbrev augTgtRingPresheaf : (SimplexCategory × C)ᵒᵖ ⥤ RingCat.{u} :=
  ringPresheaf (projectionCommRing J O).obj

/-- The identity of the presheaf of rings underlying `π^{-1}O`, with its source in the
`ringPresheaf` spelling and its target in the spelling the sheaf of rings `π^{-1}O` carries. -/
def augTgtRingUnit : augTgtRingPresheaf J (O := O) ⟶ (augTgtRing J (O := O)).obj := 𝟙 _

/-- `Stacks.SimplicialModules.augTgtRingUnit` is locally injective. -/
instance augTgtRingUnit_isLocallyInjective :
    Presheaf.IsLocallyInjective (projectionTopology C J) (augTgtRingUnit J (O := O)) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h => h

/-- `Stacks.SimplicialModules.augTgtRingUnit` is locally surjective. -/
instance augTgtRingUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective (projectionTopology C J) (augTgtRingUnit J (O := O)) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ x => ⟨x, rfl⟩

/-- The homomorphism `A_• ⟶ π^{-1}O` of sheaves of rings on `Δ × C`. -/
abbrev augRingMap : augSrcRing J (A := A) ⟶ augTgtRing J (O := O) :=
  Stacks.Sheaves.RingedToposModules.commRingSheafMap (projectionTopology C J)
    (augmentationCommRingMap J ε).hom (augSrcIsSheaf J (A := A)) (augTgtIsSheaf J (O := O))

/-- **Extension of scalars along the augmentation, as the sheafified sectionwise tensor
product** of [Stacks, Tag 03CZ]. -/
abbrev augExtendScalars :
    SheafOfModules.{u} (augSrcRing J (A := A)) ⥤ SheafOfModules.{u} (augTgtRing J (O := O)) :=
  Stacks.Sheaves.RingedToposModules.extendScalars (projectionTopology C J)
    (augmentationCommRingMap J ε).hom (augSrcIsSheaf J (A := A)) (augTgtIsSheaf J (O := O))

/-- The adjunction between extension and restriction of scalars along the augmentation, of
[Stacks, Tag 03CZ]. -/
abbrev augExtendRestrictAdjunction :
    augExtendScalars J ε ⊣ SheafOfModules.restrictScalars (augRingMap J ε) :=
  Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction (projectionTopology C J)
    (augmentationCommRingMap J ε).hom (augSrcIsSheaf J (A := A)) (augTgtIsSheaf J (O := O))

/-- Sheafification of presheaves of `A_•`-modules on `Δ × C`. -/
abbrev augSrcSheafify :
    PresheafOfModules.{u} (augSrcRing J (A := A)).obj ⥤
      SheafOfModules.{u} (augSrcRing J (A := A)) :=
  PresheafOfModules.sheafification (R := augSrcRing J (A := A)) (𝟙 _)

/-- Sheafification of presheaves of `π^{-1}O`-modules on `Δ × C`. -/
abbrev augTgtSheafify :
    PresheafOfModules.{u} (augTgtRingPresheaf J (O := O)) ⥤
      SheafOfModules.{u} (augTgtRing J (O := O)) :=
  PresheafOfModules.sheafification (R := augTgtRing J (O := O)) (augTgtRingUnit J (O := O))

/-- `- ⊗_{A_•} π^{-1}O` on presheaves of modules on `Δ × C`. -/
abbrev augChangeOfRings :
    PresheafOfModules.{u} (augSrcRing J (A := A)).obj ⥤
      PresheafOfModules.{u} (augTgtRingPresheaf J (O := O)) :=
  changeOfRings (augmentationCommRingMap J ε).hom

/-- Restriction of scalars along the augmentation, on presheaves of modules on `Δ × C`. -/
abbrev augRestrictScalars :
    PresheafOfModules.{u} (augTgtRingPresheaf J (O := O)) ⥤
      PresheafOfModules.{u} (augSrcRing J (A := A)).obj :=
  restrictScalars (augmentationCommRingMap J ε).hom

/-- The presheaf-level change-of-rings adjunction along the augmentation, of
[Stacks, Tag 03CU]. -/
abbrev augChangeOfRingsAdjunction : augChangeOfRings J ε ⊣ augRestrictScalars J ε :=
  changeOfRingsAdjunction (augmentationCommRingMap J ε).hom

/-- The sheafification adjunction for presheaves of `A_•`-modules on `Δ × C`. -/
abbrev augSrcSheafifyAdjunction :
    augSrcSheafify J (A := A) ⊣
      SheafOfModules.forget (augSrcRing J (A := A)) ⋙
        PresheafOfModules.restrictScalars (𝟙 (augSrcRing J (A := A)).obj) :=
  PresheafOfModules.sheafificationAdjunction (R := augSrcRing J (A := A)) (𝟙 _)

/-- The sheafification adjunction for presheaves of `π^{-1}O`-modules on `Δ × C`. -/
abbrev augTgtSheafifyAdjunction :
    augTgtSheafify J (O := O) ⊣
      SheafOfModules.forget (augTgtRing J (O := O)) ⋙
        PresheafOfModules.restrictScalars (augTgtRingUnit J (O := O)) :=
  PresheafOfModules.sheafificationAdjunction (R := augTgtRing J (O := O))
    (augTgtRingUnit J (O := O))

/-! ### Additivity of the left adjoints -/

/-- Restriction of scalars along the augmentation is additive: it does not change the underlying
morphism of presheaves of abelian groups. -/
instance additive_sheafRestrictScalars_augRingMap :
    (SheafOfModules.restrictScalars (augRingMap J ε)).Additive where
  map_add := by intros; rfl


/-- The right adjoint of sheafification of presheaves of `A_•`-modules is additive: neither
forgetting the sheaf condition nor restricting scalars along the identity changes the underlying
morphism of presheaves of abelian groups. -/
instance additive_forget_comp_restrictScalars_src :
    (SheafOfModules.forget (augSrcRing J (A := A)) ⋙
      PresheafOfModules.restrictScalars (𝟙 (augSrcRing J (A := A)).obj)).Additive where
  map_add := by intros; rfl

/-- The same for presheaves of `π^{-1}O`-modules. -/
instance additive_forget_comp_restrictScalars_tgt :
    (SheafOfModules.forget (augTgtRing J (O := O)) ⋙
      PresheafOfModules.restrictScalars (augTgtRingUnit J (O := O))).Additive where
  map_add := by intros; rfl

/-- The common right adjoint of the sheafification square, in its first spelling, is
additive. -/
instance additive_presheafChangeThenSheafifyRight :
    ((SheafOfModules.forget (augTgtRing J (O := O)) ⋙
      PresheafOfModules.restrictScalars (augTgtRingUnit J (O := O))) ⋙
      augRestrictScalars J ε).Additive where
  map_add := by intros; rfl

/-- The common right adjoint of the sheafification square, in its second spelling, is
additive. -/
instance additive_sheafifyThenExtendScalarsRight :
    (SheafOfModules.restrictScalars (augRingMap J ε) ⋙
      (SheafOfModules.forget (augSrcRing J (A := A)) ⋙
        PresheafOfModules.restrictScalars (𝟙 (augSrcRing J (A := A)).obj))).Additive where
  map_add := by intros; rfl

/-- Change of rings is additive, being a left adjoint of the additive restriction of scalars. -/
instance additive_augChangeOfRings : (augChangeOfRings J ε).Additive :=
  Adjunction.left_adjoint_additive (augChangeOfRingsAdjunction J ε)

/-- Sheafification of presheaves of `A_•`-modules is additive, being a left adjoint. -/
instance additive_augSrcSheafify : (augSrcSheafify J (A := A)).Additive :=
  Adjunction.left_adjoint_additive (augSrcSheafifyAdjunction J (A := A))

/-- Sheafification of presheaves of `π^{-1}O`-modules is additive, being a left adjoint. -/
instance additive_augTgtSheafify : (augTgtSheafify J (O := O)).Additive :=
  Adjunction.left_adjoint_additive (augTgtSheafifyAdjunction J (O := O))

/-- Extension of scalars along the augmentation is additive, being a left adjoint. -/
instance additive_augExtendScalars : (augExtendScalars J ε).Additive :=
  Adjunction.left_adjoint_additive (augExtendRestrictAdjunction J ε)

/-- Extension of scalars along the augmentation preserves zero morphisms. -/
instance preservesZeroMorphisms_augExtendScalars :
    (augExtendScalars J ε).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The right adjoint of sheafification of presheaves of `A_•`-modules preserves zero
morphisms. -/
instance preservesZeroMorphisms_forget_comp_restrictScalars_src :
    (SheafOfModules.forget (augSrcRing J (A := A)) ⋙
      PresheafOfModules.restrictScalars
        (𝟙 (augSrcRing J (A := A)).obj)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The same for presheaves of `π^{-1}O`-modules. -/
instance preservesZeroMorphisms_forget_comp_restrictScalars_tgt :
    (SheafOfModules.forget (augTgtRing J (O := O)) ⋙
      PresheafOfModules.restrictScalars
        (𝟙 (augTgtRing J (O := O)).obj)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _


/-! ### The functors and adjunctions above, applied degreewise to cochain complexes -/

/-- `- ⊗_{A_•} π^{-1}O` on complexes of presheaves of modules. -/
abbrev augChangeOfRingsC :
    CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ ⥤
      CochainComplex (PresheafOfModules.{u} (augTgtRingPresheaf J (O := O))) ℤ :=
  (augChangeOfRings J ε).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction of scalars along the augmentation, on complexes of presheaves of modules. -/
abbrev augRestrictScalarsC :
    CochainComplex (PresheafOfModules.{u} (augTgtRingPresheaf J (O := O))) ℤ ⥤
      CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ :=
  (augRestrictScalars J ε).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Sheafification of complexes of presheaves of `A_•`-modules. -/
abbrev augSrcSheafifyC :
    CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (augSrcRing J (A := A))) ℤ :=
  (augSrcSheafify J (A := A)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Sheafification of complexes of presheaves of `π^{-1}O`-modules. -/
abbrev augTgtSheafifyC :
    CochainComplex (PresheafOfModules.{u} (augTgtRingPresheaf J (O := O))) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ :=
  (augTgtSheafify J (O := O)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The right adjoint of `Stacks.SimplicialModules.augSrcSheafifyC`. -/
abbrev augSrcForgetC :
    CochainComplex (SheafOfModules.{u} (augSrcRing J (A := A))) ℤ ⥤
      CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ :=
  (SheafOfModules.forget (augSrcRing J (A := A)) ⋙
    PresheafOfModules.restrictScalars
      (𝟙 (augSrcRing J (A := A)).obj)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The right adjoint of `Stacks.SimplicialModules.augTgtSheafifyC`. -/
abbrev augTgtForgetC :
    CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ ⥤
      CochainComplex (PresheafOfModules.{u} (augTgtRingPresheaf J (O := O))) ℤ :=
  (SheafOfModules.forget (augTgtRing J (O := O)) ⋙
    PresheafOfModules.restrictScalars
      (𝟙 (augTgtRing J (O := O)).obj)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Sheaf-level extension of scalars along the augmentation, on complexes. -/
abbrev augExtendScalarsC :
    CochainComplex (SheafOfModules.{u} (augSrcRing J (A := A))) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ :=
  (augExtendScalars J ε).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `ε_*` on complexes: restriction of scalars along the augmentation, degreewise. -/
abbrev augPushforwardC :
    CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (augSrcRing J (A := A))) ℤ :=
  (SheafOfModules.restrictScalars (augRingMap J ε)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `s(-)` of a complex of presheaves of `A_•`-modules: the Moore double complex. -/
abbrev augMooreSrcC :
    CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ ⥤
      HomologicalComplex₂ (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (mooreSheafCochain J (simplicialCommRingSheaf J A).obj).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- `s(-)` of a complex of presheaves of `π^{-1}O`-modules: the Moore double complex. -/
abbrev augMooreTgtC :
    CochainComplex (PresheafOfModules.{u} (augTgtRingPresheaf J (O := O))) ℤ ⥤
      HomologicalComplex₂ (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (mooreSheafCochain J (projectionCommRing J O).obj).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The presheaf-level change-of-rings adjunction on complexes. -/
abbrev augChangeOfRingsAdjC : augChangeOfRingsC J ε ⊣ augRestrictScalarsC J ε :=
  Adjunction.mapHomologicalComplexAdjunction (augChangeOfRingsAdjunction J ε)
    (ComplexShape.up ℤ)

/-- The sheafification adjunction for presheaves of `A_•`-modules, on complexes. -/
abbrev augSrcSheafifyAdjC : augSrcSheafifyC J (A := A) ⊣ augSrcForgetC J (A := A) :=
  Adjunction.mapHomologicalComplexAdjunction (augSrcSheafifyAdjunction J (A := A))
    (ComplexShape.up ℤ)

/-- The sheafification adjunction for presheaves of `π^{-1}O`-modules, on complexes. -/
abbrev augTgtSheafifyAdjC : augTgtSheafifyC J (O := O) ⊣ augTgtForgetC J (O := O) :=
  Adjunction.mapHomologicalComplexAdjunction (augTgtSheafifyAdjunction J (O := O))
    (ComplexShape.up ℤ)

/-- The adjunction between extension and restriction of scalars along the augmentation, of
[Stacks, Tag 03CZ], on complexes. -/
abbrev augExtendRestrictAdjC : augExtendScalarsC J ε ⊣ augPushforwardC J ε :=
  Adjunction.mapHomologicalComplexAdjunction (augExtendRestrictAdjunction J ε)
    (ComplexShape.up ℤ)

/-! ### The sheafification square -/

/-- The presheaf-level change of rings followed by sheafification, as a left adjoint on
complexes. -/
abbrev presheafChangeThenSheafifyAdjunction :
    ((augChangeOfRings J ε ⋙ augTgtSheafify J (O := O)).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⊣
      (((SheafOfModules.forget (augTgtRing J (O := O)) ⋙
        PresheafOfModules.restrictScalars (augTgtRingUnit J (O := O))) ⋙
        augRestrictScalars J ε).mapHomologicalComplex (ComplexShape.up ℤ)) :=
  Adjunction.mapHomologicalComplexAdjunction
    ((augChangeOfRingsAdjunction J ε).comp (augTgtSheafifyAdjunction J (O := O)))
    (ComplexShape.up ℤ)

/-- Sheafification followed by sheaf-level extension of scalars, as a left adjoint of the *same*
functor, on complexes. -/
abbrev sheafifyThenExtendScalarsAdjunction :
    ((augSrcSheafify J (A := A) ⋙ augExtendScalars J ε).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⊣
      ((SheafOfModules.restrictScalars (augRingMap J ε) ⋙
        (SheafOfModules.forget (augSrcRing J (A := A)) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (augSrcRing J (A := A)).obj))).mapHomologicalComplex (ComplexShape.up ℤ)) :=
  Adjunction.mapHomologicalComplexAdjunction
    ((augSrcSheafifyAdjunction J (A := A)).comp (augExtendRestrictAdjunction J ε))
    (ComplexShape.up ℤ)

/-- **Sheafification carries the presheaf-level change of rings to the sheaf-level extension of
scalars.**  Both `(- ⊗_{A_•} π^{-1}O)` followed by degreewise sheafification and degreewise
sheafification followed by `Stacks.SimplicialModules.augExtendScalars` are left adjoint to
"forget the sheaf condition, then restrict scalars along `A_• ⟶ π^{-1}O`", so uniqueness of left
adjoints identifies them.  It carries the column step of [Stacks, Tag 08RX], stated for the
presheaf-level change of rings, to the sheaf-level base change. -/
def augmentationSheafifyExtendScalarsIso :
    ((augChangeOfRings J ε ⋙ augTgtSheafify J (O := O)).mapHomologicalComplex
        (ComplexShape.up ℤ)) ≅
      ((augSrcSheafify J (A := A) ⋙ augExtendScalars J ε).mapHomologicalComplex
        (ComplexShape.up ℤ)) :=
  Adjunction.leftAdjointUniq (presheafChangeThenSheafifyAdjunction J ε)
    (sheafifyThenExtendScalarsAdjunction J ε)

/-- **The complex `s(-)` inverts the unit of sheafification of presheaves of modules.**  That
unit is `CategoryTheory.toSheafify` on the underlying abelian presheaf, and `s(-)` inverts
whatever sheafification inverts. -/
instance isIso_mooreSheafCochain_map_augTgtSheafifyAdjunction_unit_app
    (V : PresheafOfModules.{u} (augTgtRingPresheaf J (O := O))) :
    IsIso ((mooreSheafCochain J (projectionCommRing J O).obj).map
      ((augTgtSheafifyAdjunction J (O := O)).unit.app V)) :=
  isIso_mooreSheafCochain_map_of_W J _ ((projectionTopology C J).W_toSheafify _)

/-- **The comparison from the presheaf-level base change to the sheaf-level one**: the unit of
sheafification followed by the sheafification square. -/
def augSheafifyComparison
    (L : CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ) :
    (augChangeOfRingsC J ε).obj L ⟶
      (augTgtForgetC J (O := O)).obj ((augExtendScalarsC J ε).obj
        ((augSrcSheafifyC J (A := A)).obj L)) :=
  (augTgtSheafifyAdjC J (O := O)).unit.app ((augChangeOfRingsC J ε).obj L) ≫
    (augTgtForgetC J (O := O)).map ((augmentationSheafifyExtendScalarsIso J ε).hom.app L)

/-- **`s(-)` inverts the comparison.**  Its first leg is the unit of sheafification, which `s(-)`
inverts, and its second leg is invertible. -/
instance isIso_augMooreTgtC_map_augSheafifyComparison
    (L : CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ) :
    IsIso ((augMooreTgtC J (O := O)).map (augSheafifyComparison J ε L)) := by
  have : ∀ n : ℤ, IsIso (((augMooreTgtC J (O := O)).map
      ((augTgtSheafifyAdjC J (O := O)).unit.app ((augChangeOfRingsC J ε).obj L))).f n) :=
    fun n => isIso_mooreSheafCochain_map_augTgtSheafifyAdjunction_unit_app J _
  have : IsIso ((augMooreTgtC J (O := O)).map
      ((augTgtSheafifyAdjC J (O := O)).unit.app ((augChangeOfRingsC J ε).obj L))) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso ((augmentationSheafifyExtendScalarsIso J ε).hom.app L) :=
    NatIso.isIso_app_of_isIso _ _
  rw [augSheafifyComparison, Functor.map_comp]
  infer_instance

/-- **The sheafification square respects the base-change units.**  For a map `w` of complexes out
of the sheafified `L^•`, the presheaf-level base-change unit followed by the comparison and by
the sheaf-level adjoint of `w` is the sheafification unit followed by `w`. -/
lemma unit_comp_augSheafifyComparison
    (L : CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ)
    (Z : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ)
    (w : (augSrcSheafifyC J (A := A)).obj L ⟶ (augPushforwardC J ε).obj Z) :
    (augChangeOfRingsAdjC J ε).unit.app L ≫
        (augRestrictScalarsC J ε).map (augSheafifyComparison J ε L ≫
          (augTgtForgetC J (O := O)).map
            (((augExtendRestrictAdjC J ε).homEquiv _ Z).symm w)) =
      (augSrcSheafifyAdjC J (A := A)).unit.app L ≫ (augSrcForgetC J (A := A)).map w := by
  have hstep : (augChangeOfRingsAdjC J ε).unit.app L ≫
        (augRestrictScalarsC J ε).map (augSheafifyComparison J ε L) =
      (augSrcSheafifyAdjC J (A := A)).unit.app L ≫ (augSrcForgetC J (A := A)).map
        ((augExtendRestrictAdjC J ε).unit.app ((augSrcSheafifyC J (A := A)).obj L)) := by
    have h1 := Adjunction.unit_leftAdjointUniq_hom_app
      (presheafChangeThenSheafifyAdjunction J ε) (sheafifyThenExtendScalarsAdjunction J ε) L
    rw [augSheafifyComparison, Functor.map_comp, ← Category.assoc]
    refine Eq.trans (congrArg (· ≫ _) (HomologicalComplex.hom_ext _ _
      fun n => Adjunction.comp_unit_app _ _ _).symm) (h1.trans (HomologicalComplex.hom_ext _ _
      fun n => Adjunction.comp_unit_app _ _ _))
  rw [Functor.map_comp, ← Category.assoc, hstep]
  show ((augSrcSheafifyAdjC J (A := A)).unit.app L ≫ (augSrcForgetC J (A := A)).map
        ((augExtendRestrictAdjC J ε).unit.app ((augSrcSheafifyC J (A := A)).obj L))) ≫
      (augSrcForgetC J (A := A)).map ((augPushforwardC J ε).map
        (((augExtendRestrictAdjC J ε).homEquiv _ Z).symm w)) = _
  rw [Category.assoc, ← Functor.map_comp, ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-! ### Flatness of the sheafified resolution -/

/-- The identity of the presheaf of rings underlying `A_•`, with its target spelled by
`Stacks.SheafOfModules.Tensor.ringSheaf`, the spelling at which [Stacks, Tag 03ET] is stated. -/
def augSrcRingUnit :
    (simplicialCommRingSheaf J A).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (simplicialCommRingSheaf J A)).obj :=
  𝟙 _

/-- `Stacks.SimplicialModules.augSrcRingUnit` is locally injective. -/
instance augSrcRingUnit_isLocallyInjective :
    Presheaf.IsLocallyInjective (projectionTopology C J) (augSrcRingUnit J (A := A)) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h => h

/-- `Stacks.SimplicialModules.augSrcRingUnit` is locally surjective. -/
instance augSrcRingUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective (projectionTopology C J) (augSrcRingUnit J (A := A)) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ x => ⟨x, rfl⟩

/-- **The sheafification of a standard cover is a flat sheaf of `A_•`-modules.**  Its sections
are flat (`PresheafOfModules.flat_obj_of_isStdCover`), so it is a flat presheaf of modules
([Stacks, Tag 03ES]), and the sheaf associated to a flat presheaf of modules is flat
([Stacks, Tag 03ET]). -/
lemma isFlat_augSrcSheafify_obj_of_isStdCover
    {N : PresheafOfModules.{u} (augSrcRing J (A := A)).obj}
    (hN : PresheafOfModules.IsStdCover N) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := simplicialCommRingSheaf J A) ((augSrcSheafify J (A := A)).obj N) :=
  Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification
    (projectionTopology C J) (Osharp := simplicialCommRingSheaf J A) (augSrcRingUnit J (A := A)) N
    (AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat N
      (fun V => PresheafOfModules.flat_obj_of_isStdCover hN V))

/-! ### Boundedness of the functor images -/

/-- `ε_*` of a complex bounded above by `0` is bounded above by `0`. -/
instance isStrictlyLE_augPushforwardC_obj
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0] :
    CochainComplex.IsStrictlyLE ((augPushforwardC J ε).obj X) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (SheafOfModules.restrictScalars (augRingMap J ε))
    (CochainComplex.isZero_of_isStrictlyLE X 0 i hi)

/-- The underlying presheaf complex of a complex bounded above by `0` is bounded above by `0`. -/
instance isStrictlyLE_augSrcForgetC_obj
    (Y : CochainComplex (SheafOfModules.{u} (augSrcRing J (A := A))) ℤ) [Y.IsStrictlyLE 0] :
    CochainComplex.IsStrictlyLE ((augSrcForgetC J (A := A)).obj Y) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (SheafOfModules.forget (augSrcRing J (A := A)) ⋙
      PresheafOfModules.restrictScalars (𝟙 (augSrcRing J (A := A)).obj))
    (CochainComplex.isZero_of_isStrictlyLE Y 0 i hi)

/-- Sheafifying a complex bounded above by `0` keeps it bounded above by `0`. -/
instance isStrictlyLE_augSrcSheafifyC_obj
    (L : CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ)
    [L.IsStrictlyLE 0] :
    CochainComplex.IsStrictlyLE ((augSrcSheafifyC J (A := A)).obj L) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (augSrcSheafify J (A := A))
    (CochainComplex.isZero_of_isStrictlyLE L 0 i hi)

/-- Extending scalars keeps a complex bounded above by `0` bounded above by `0`. -/
instance isStrictlyLE_augExtendScalarsC_obj
    (M : CochainComplex (SheafOfModules.{u} (augSrcRing J (A := A))) ℤ) [M.IsStrictlyLE 0] :
    CochainComplex.IsStrictlyLE ((augExtendScalarsC J ε).obj M) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (augExtendScalars J ε)
    (CochainComplex.isZero_of_isStrictlyLE M 0 i hi)

/-- The underlying presheaf complex of a complex of sheaves of `π^{-1}O`-modules bounded above
by `0` is bounded above by `0`. -/
instance isStrictlyLE_augTgtForgetC_obj
    (Z : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [Z.IsStrictlyLE 0] :
    CochainComplex.IsStrictlyLE ((augTgtForgetC J (O := O)).obj Z) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (SheafOfModules.forget (augTgtRing J (O := O)) ⋙
      PresheafOfModules.restrictScalars (augTgtRingUnit J (O := O)))
    (CochainComplex.isZero_of_isStrictlyLE Z 0 i hi)

/-- Restricting scalars keeps a complex bounded above by `0` bounded above by `0`. -/
instance isStrictlyLE_augRestrictScalarsC_obj
    (V : CochainComplex (PresheafOfModules.{u} (augTgtRingPresheaf J (O := O))) ℤ)
    [V.IsStrictlyLE 0] :
    CochainComplex.IsStrictlyLE ((augRestrictScalarsC J ε).obj V) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (augRestrictScalars J ε)
    (CochainComplex.isZero_of_isStrictlyLE V 0 i hi)

/-- Sheafification of presheaves of `A_•`-modules preserves homology, being exact. -/
instance preservesHomology_augSrcSheafify :
    (augSrcSheafify J (A := A)).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-! ### The base-change triangle at the module level -/

/-- **The base-change triangle at the module level.**  The presheaf-level base-change unit,
followed by the comparison with the sheaf-level base change and by the sheaf-level adjoint of the
transpose of the resolution, is the resolution itself. -/
lemma unit_comp_augSheafifyComparison_comp_adjoint
    (L : CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ)
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ)
    (p : L ⟶ (augRestrictScalarsC J ε).obj ((augTgtForgetC J (O := O)).obj X)) :
    (augChangeOfRingsAdjC J ε).unit.app L ≫
      (augRestrictScalarsC J ε).map (augSheafifyComparison J ε L) ≫
      (augRestrictScalarsC J ε).map ((augTgtForgetC J (O := O)).map
        (((augExtendRestrictAdjC J ε).homEquiv ((augSrcSheafifyC J (A := A)).obj L) X).symm
          (((augSrcSheafifyAdjC J (A := A)).homEquiv L
            ((augPushforwardC J ε).obj X)).symm p))) = p := by
  have h := unit_comp_augSheafifyComparison J ε L X
    (((augSrcSheafifyAdjC J (A := A)).homEquiv L ((augPushforwardC J ε).obj X)).symm p)
  rw [Functor.map_comp] at h
  rw [h]
  exact (Adjunction.homEquiv_unit (augSrcSheafifyAdjC J (A := A)) L
    ((augPushforwardC J ε).obj X) _).symm.trans (Equiv.apply_symm_apply _ _)

/-! ### The transpose of the resolution -/

/-- **The transpose of a resolution of `ε_* X^•` is a quasi-isomorphism after sheafification.**
Sheafification of presheaves of modules is exact, and its counit at a complex of sheaves of
modules is invertible, so the adjoint `L^•_♯ ⟶ ε_* X^•` of a quasi-isomorphism
`L^• ⟶ (ε_* X^•)^{pre}` is again a quasi-isomorphism. -/
lemma quasiIso_augSrcSheafifyAdjC_homEquiv_symm
    (L : CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ)
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ)
    (p : L ⟶ (augSrcForgetC J (A := A)).obj ((augPushforwardC J ε).obj X)) (hp : QuasiIso p) :
    QuasiIso (((augSrcSheafifyAdjC J (A := A)).homEquiv L
      ((augPushforwardC J ε).obj X)).symm p) := by
  have : ∀ n : ℤ, IsIso (((augSrcSheafifyAdjC J (A := A)).counit.app
      ((augPushforwardC J ε).obj X)).f n) := fun n =>
    NatIso.isIso_app_of_isIso (augSrcSheafifyAdjunction J (A := A)).counit _
  have : IsIso ((augSrcSheafifyAdjC J (A := A)).counit.app ((augPushforwardC J ε).obj X)) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : QuasiIso ((augSrcSheafifyC J (A := A)).map p) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology p _
  rw [Adjunction.homEquiv_counit]
  exact quasiIso_comp _ _

end Stacks.SimplicialModules

end
