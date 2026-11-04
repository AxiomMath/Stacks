module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.StdCoverResolution
public import StacksFrontier.Cotangent.SheavesOfRings.AugmentationLowerShriekBaseChange
public import StacksFrontier.Cotangent.SheavesOfRings.MooreSplice

/-!
# `L π_!(L ε^*(ε_* X^•)) ≅ L π_!(X^•)` for a complex bounded above by `0`

Let `(C, J)` be a small site, let `A_•` be a simplicial sheaf of commutative rings on it and let
`ε : A_• ⟶ O` be an augmentation. Write `Δ × C` for the simplicial site of [Stacks, Tag 09D0],
`Lε^* = - ⊗^𝐋_{A_•} π^{-1}O : D(A_•) ⥤ D(π^{-1}O)` for the derived extension of scalars of
[Stacks, Tag 09D3] and `Lπ_! : D(π^{-1}O) ⥤ D(O)` for the derived lower shriek of
[Stacks, Tag 09CY].

This file proves the module-coefficient dévissage of [Stacks, Tag 09D2] at the augmentation, on a
cochain complex `X^•` of sheaves of `π^{-1}O`-modules **bounded above by `0`**: under the
hypothesis `hθ` that `s(A_•) ⟶ s(π^{-1}O)` be a quasi-isomorphism of complexes of abelian sheaves
on `C`, the derived base change along the augmentation may be dropped after `L π_!`. This is a
special case of Tag 09D2: the complex is bounded above by `0` and of the form `ε_* X^•`, and the
hypothesis is on `s(A_•) ⟶ s(π^{-1}O)` rather than on `L π_! A_• ⟶ L π_! B_•`.

The identification cannot be made before `L π_!`: `Lε^*` is computed on the fibres, so
`H^{-i}(Lε^*(ε_* N))` restricted to `{n} × C` is `Tor_i^{P_n}(N, O)`, and for the standard
resolution `Tor_1^{P_n}(O, O) = I_n/I_n²` is nonzero; these terms cancel under `L π_!`.

The proof resolves the underlying presheaf complex of `ε_* X^•` by standard covers
(`PresheafOfModules.exists_isStdCover_resolution_of_isLE`, the standard-cover form of
[Stacks, Tag 03EW]), sheafifies it to a complex of flat sheaves of `A_•`-modules on which `Lε^*` is
computed degreewise, compares the column and row filtrations of [Stacks, Tag 08RX], and computes
`L π_!` on both sides by Moore total complexes.

## Main definitions

* `Stacks.SimplicialModules.mooreSheafBicomplexSplitIso`: the two readings of the base-changed
  Moore double complex of a complex, and the fact that the comparison is the identity.
* `Stacks.SimplicialModules.augMooreAbDictionary`: the abelian-coefficient Moore double complex of
  a complex of sheaves of `π^{-1}O`-modules is `s(-)` of its underlying presheaf complex.
* `Stacks.SimplicialModules.augmentationBaseChangeComplexIso`: the abstract and the sectionwise
  extension of scalars along the augmentation agree on complexes.

## Main results

* `Stacks.SimplicialModules.quasiIso_total_map_of_column_row_presheafLevel`: **the column and row
  steps fed to each other, stated before `s(-)` is applied.**
* `Stacks.SimplicialModules.quasiIso_total_map_augMooreTgtC_adjoint`: that step at the
  augmentation, at the sheafified resolution.
* `Stacks.SimplicialModules.quasiIso_total_map_mooreModBicomplex_of_augMooreTgtC`: the same
  conclusion at module coefficients.
* `Stacks.SimplicialModules.nonempty_derivedProjectionLowerShriek_augmentationBaseChange_iso`:
  **`L π_!(L ε^*(ε_* X^•)) ≅ L π_!(X^•)`.**

## Implementation notes

The column/row step is proved in the `Generic` section, with the homomorphism of presheaves of
commutative rings left as a variable, where the comparison of the two readings of the base-changed
Moore double complex is the identity `Stacks.SimplicialModules.mooreSheafBicomplexSplitIso`; it is
then instantiated at the augmentation. The abelian- and module-coefficient Moore double complexes
are compared once, as the natural isomorphism `Stacks.SimplicialModules.augMooreAbDictionary`, and
morphisms are transported by its naturality. The two `local instance`s in the `Concrete` section
register additivity and preservation of zero morphisms of
`Stacks.Sheaves.RingedToposModules.extendScalars` at the spelling
`Stacks.SheafOfModules.ChangeOfRings.extendScalarsIsoTensor` is stated in.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3)
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the Atiyah triangle, whose
  outer-term identifications use this statement at a sheaf placed in degree `0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.PresheafOfModules.ChangeOfRings (ringPresheaf changeOfRings restrictScalars
  changeOfRingsAdjunction unitMap unitMap')

namespace Stacks.SimplicialModules

universe u

section Generic

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  {A₁ A₂ : (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u}} (θ : A₁ ⟶ A₂)

/-- Change of rings is additive, being a left adjoint. -/
local instance additive_changeOfRings : (changeOfRings θ :
    PresheafOfModules.{u} (ringPresheaf A₁) ⥤ PresheafOfModules.{u} (ringPresheaf A₂)).Additive :=
  Adjunction.left_adjoint_additive
    (show (changeOfRings θ : PresheafOfModules.{u} (ringPresheaf A₁) ⥤
        PresheafOfModules.{u} (ringPresheaf A₂)) ⊣ restrictScalars θ from
      changeOfRingsAdjunction θ)

/-- Restriction of scalars along `θ`, degreewise, keeps a complex bounded above by `0`. -/
instance isStrictlyLE_restrictScalarsComplex_obj
    (N : CochainComplex (PresheafOfModules.{u} (ringPresheaf A₂)) ℤ) [N.IsStrictlyLE 0] :
    CochainComplex.IsStrictlyLE
      (((restrictScalars θ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (restrictScalars θ) (CochainComplex.isZero_of_isStrictlyLE N 0 i hi)

/-- The two readings of the base-changed Moore double complex of a complex. -/
abbrev mooreSheafBicomplexSplitIso :
    changeOfRingsComplex θ ⋙
        (mooreSheafCochain J A₂).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (changeOfRings θ ⋙ mooreSheafCochain J A₂).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl (changeOfRings θ ⋙ mooreSheafCochain J A₂))
    (ComplexShape.up ℤ)

/-- The split comparison is the identity natural transformation. -/
lemma mooreSheafBicomplexSplitIso_inv : (mooreSheafBicomplexSplitIso J θ).inv = 𝟙 _ :=
  NatTrans.mapHomologicalComplex_id (ComplexShape.up ℤ) _

/-- **The split comparison is the identity**, with its target spelled as `s(-)` applied to the
degreewise base change. -/
lemma mooreSheafBicomplexSplitIso_inv_app
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf A₁)) ℤ) :
    (mooreSheafBicomplexSplitIso J θ).inv.app L =
      𝟙 (((mooreSheafCochain J A₂).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((changeOfRingsComplex θ).obj L)) := by
  rw [mooreSheafBicomplexSplitIso_inv]; rfl

/-- The base-change unit followed by the split comparison is the degreewise unit. -/
lemma mooreSheafBicomplexBaseChangeMap_comp_splitIso_inv_app
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf A₁)) ℤ) :
    mooreSheafBicomplexBaseChangeMap J θ L ≫ (mooreSheafBicomplexSplitIso J θ).inv.app L =
      ((mooreSheafCochain J A₁).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (changeOfRingsComplexUnit θ L) := by
  rw [← mooreSheafCochain_map_changeOfRingsComplexUnit, mooreSheafBicomplexSplitIso_inv_app]
  exact Category.comp_id _

/-- **The column and row steps fed to each other, before `s(-)` is applied.** -/
theorem quasiIso_total_map_of_column_row_presheafLevel
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf A₁)) ℤ) [L.IsStrictlyLE 0]
    (hP : ∀ q, PresheafOfModules.IsStdCover (L.X q))
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' θ)))
    {M N : CochainComplex (PresheafOfModules.{u} (ringPresheaf A₂)) ℤ}
    [M.IsStrictlyLE 0] [N.IsStrictlyLE 0]
    (c₁ : (changeOfRingsComplex θ).obj L ⟶ M)
    (hc₁ : IsIso (((mooreSheafCochain J A₂).mapHomologicalComplex (ComplexShape.up ℤ)).map c₁))
    (c₂ : M ⟶ N)
    (p : L ⟶ ((restrictScalars θ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
    (hp : QuasiIso p)
    (hcomm : changeOfRingsComplexUnit θ L ≫
        ((restrictScalars θ).mapHomologicalComplex (ComplexShape.up ℤ)).map c₁ ≫
        ((restrictScalars θ).mapHomologicalComplex (ComplexShape.up ℤ)).map c₂ = p) :
    QuasiIso (HomologicalComplex₂.total.map
      (((mooreSheafCochain J A₂).mapHomologicalComplex (ComplexShape.up ℤ)).map c₂)
      (ComplexShape.up ℤ)) := by
  have := hc₁
  have := hp
  have : IsIso ((mooreSheafBicomplexSplitIso J θ).inv.app L) := NatIso.isIso_app_of_isIso _ _
  refine quasiIso_total_map_of_column_row J θ L hP hθ
    ((mooreSheafBicomplexSplitIso J θ).inv.app L ≫
      ((mooreSheafCochain J A₂).mapHomologicalComplex (ComplexShape.up ℤ)).map c₁)
    (((mooreSheafCochain J A₂).mapHomologicalComplex (ComplexShape.up ℤ)).map c₂)
    (((mooreSheafCochain J A₁).mapHomologicalComplex (ComplexShape.up ℤ)).map p)
    (quasiIso_total_map_mooreSheafBicomplex J p) ?_
  simp only [Category.assoc]
  rw [← Category.assoc, mooreSheafBicomplexBaseChangeMap_comp_splitIso_inv_app]
  have h := congrArg
    ((mooreSheafCochain J A₁).mapHomologicalComplex (ComplexShape.up ℤ)).map hcomm
  rw [Functor.map_comp, Functor.map_comp, mooreSheafCochain_map_restrictScalars_map,
    mooreSheafCochain_map_restrictScalars_map] at h
  exact h

end Generic

section Concrete

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A : SimplicialObject (Sheaf J CommRingCat.{u})} {O : Sheaf J CommRingCat.{u}}
  (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O)

/-- **The column and row steps at the augmentation.** For a complex `L` of standard covers bounded
above by `0` and a quasi-isomorphism `p` from `L` to the underlying presheaf complex of `ε_* X`,
the adjoint of the sheafified transpose of `p` induces a quasi-isomorphism of the total complexes
of the Moore double complexes of the underlying presheaf complexes. -/
theorem quasiIso_total_map_augMooreTgtC_adjoint
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' (augmentationCommRingMap J ε).hom)))
    (L : CochainComplex (PresheafOfModules.{u} (augSrcRing J (A := A)).obj) ℤ)
    [L.IsStrictlyLE 0] (hP : ∀ q, PresheafOfModules.IsStdCover (L.X q))
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0]
    (p : L ⟶ (augSrcForgetC J (A := A)).obj ((augPushforwardC J ε).obj X))
    (hp : QuasiIso p) :
    QuasiIso (HomologicalComplex₂.total.map
      ((augMooreTgtC J (O := O)).map ((augTgtForgetC J (O := O)).map
        (((augExtendRestrictAdjC J ε).homEquiv ((augSrcSheafifyC J (A := A)).obj L) X).symm
          (((augSrcSheafifyAdjC J (A := A)).homEquiv L
            ((augPushforwardC J ε).obj X)).symm p))))
      (ComplexShape.up ℤ)) :=
  quasiIso_total_map_of_column_row_presheafLevel J (augmentationCommRingMap J ε).hom L hP hθ
    (augSheafifyComparison J ε L) inferInstance
    ((augTgtForgetC J (O := O)).map _)
    p hp (by
      rw [← Functor.map_comp]
      exact unit_comp_augSheafifyComparison_comp_adjoint J ε L X p)

/-- `π^{-1}O`'s base sheaf of rings, in the spelling `Lπ_!` takes it. -/
abbrev augBaseRing : Sheaf J RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf O

/-- **The abelian-coefficient Moore double complex of a complex of sheaves of `π^{-1}O`-modules is
`s(-)` of its underlying presheaf complex.** -/
def augMooreAbDictionary :
    mooreAbBicomplexFunctor C J (augBaseRing J (O := O)) ≅
      augTgtForgetC J (O := O) ⋙ augMooreTgtC J (O := O) :=
  NatIso.mapHomologicalComplex
      (eqToIso (show SheafOfModules.toSheaf.{u} (projectionRing C J (augBaseRing J (O := O))) ⋙
          sheafToPresheaf (projectionTopology C J) AddCommGrpCat.{u} ⋙ mooreAbSheafCochain J =
        (SheafOfModules.forget (augTgtRing J (O := O)) ⋙
            PresheafOfModules.restrictScalars (augTgtRingUnit J (O := O))) ⋙
          mooreSheafCochain J (projectionCommRing J O).obj from rfl))
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl
      ((SheafOfModules.forget (augTgtRing J (O := O)) ⋙
          PresheafOfModules.restrictScalars (augTgtRingUnit J (O := O))) ⋙
        mooreSheafCochain J (projectionCommRing J O).obj)) (ComplexShape.up ℤ)).symm

/-- **The abelian-coefficient conclusion of the column/row step, at module coefficients.** -/
theorem quasiIso_total_map_mooreModBicomplex_of_augMooreTgtC
    {M X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ}
    [M.IsStrictlyLE 0] [X.IsStrictlyLE 0] (u : M ⟶ X)
    (h : QuasiIso (HomologicalComplex₂.total.map
      ((augMooreTgtC J (O := O)).map ((augTgtForgetC J (O := O)).map u))
      (ComplexShape.up ℤ))) :
    QuasiIso (HomologicalComplex₂.total.map
      ((mooreModBicomplexFunctor C J (augBaseRing J (O := O))).map u)
      (ComplexShape.up ℤ)) := by
  rw [quasiIso_total_map_mooreModBicomplex_iff]
  refine (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    (HomologicalComplex₂.total.mapIso ((augMooreAbDictionary J (O := O)).app M)
      (ComplexShape.up ℤ))
    (HomologicalComplex₂.total.mapIso ((augMooreAbDictionary J (O := O)).app X)
      (ComplexShape.up ℤ)) ?_)).mpr h
  simp only [HomologicalComplex₂.total.mapIso_hom, Arrow.mk_hom,
    ← HomologicalComplex₂.total.map_comp]
  have hnat := (augMooreAbDictionary J (O := O)).hom.naturality u
  rw [Functor.comp_map] at hnat
  exact congrArg (fun t => HomologicalComplex₂.total.map t (ComplexShape.up ℤ)) hnat.symm

/-- Extension of scalars along the augmentation is additive, at the spelling
`Stacks.SheafOfModules.ChangeOfRings.extendScalarsIsoTensor` is stated in. -/
local instance additive_extendScalars_tensorSpelling :
    (Stacks.Sheaves.RingedToposModules.extendScalars (projectionTopology C J)
      (augmentationCommRingMap J ε).hom (augSrcIsSheaf J (A := A))
      (augTgtIsSheaf J (O := O))).Additive :=
  inferInstanceAs (augExtendScalars J ε).Additive

/-- The same for preservation of zero morphisms. -/
local instance preservesZeroMorphisms_extendScalars_tensorSpelling :
    (Stacks.Sheaves.RingedToposModules.extendScalars (projectionTopology C J)
      (augmentationCommRingMap J ε).hom (augSrcIsSheaf J (A := A))
      (augTgtIsSheaf J (O := O))).PreservesZeroMorphisms :=
  inferInstanceAs (augExtendScalars J ε).PreservesZeroMorphisms

/-- **The two degreewise extensions of scalars along the augmentation agree on complexes.** -/
def augmentationBaseChangeComplexIso :
    augmentationBaseChangeComplex J ε ≅ augExtendScalarsC J ε :=
  NatIso.mapHomologicalComplex
    (Stacks.SheafOfModules.ChangeOfRings.extendScalarsIsoTensor
      (augmentationCommRingMap J ε).hom (augSrcIsSheaf J (A := A)) (augTgtIsSheaf J (O := O)))
    (ComplexShape.up ℤ)

/-- **A flat resolution of `ε_* X`, with the column/row conclusion at module coefficients.** For a
complex `X` bounded above by `0` there are a complex `M` of flat sheaves of `A_•`-modules bounded
above by `0` and a quasi-isomorphism `w : M ⟶ ε_* X` whose adjoint induces a quasi-isomorphism of
the total complexes of the module-coefficient Moore double complexes. -/
theorem exists_augExtendScalars_quasiIso_total
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' (augmentationCommRingMap J ε).hom)))
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0] :
    ∃ (M : CochainComplex (SheafOfModules.{u} (augSrcRing J (A := A))) ℤ)
      (_ : M.IsStrictlyLE 0)
      (_ : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := simplicialCommRingSheaf J A) (M.X i))
      (w : M ⟶ (augPushforwardC J ε).obj X), QuasiIso w ∧
      QuasiIso (HomologicalComplex₂.total.map
        ((mooreModBicomplexFunctor C J (augBaseRing J (O := O))).map
          (((augExtendRestrictAdjC J ε).homEquiv M X).symm w)) (ComplexShape.up ℤ)) := by
  obtain ⟨L, p, hp, hP, hLE⟩ := PresheafOfModules.exists_isStdCover_resolution_of_isLE (0 : ℤ)
    ((augSrcForgetC J (A := A)).obj ((augPushforwardC J ε).obj X))
  have := hLE
  exact ⟨(augSrcSheafifyC J (A := A)).obj L, inferInstance,
    fun i => isFlat_augSrcSheafify_obj_of_isStdCover J (hP i),
    ((augSrcSheafifyAdjC J (A := A)).homEquiv L ((augPushforwardC J ε).obj X)).symm p,
    quasiIso_augSrcSheafifyAdjC_homEquiv_symm J ε L X p hp,
    quasiIso_total_map_mooreModBicomplex_of_augMooreTgtC J (O := O) _
      (quasiIso_total_map_augMooreTgtC_adjoint J ε hθ L hP X p hp)⟩

/-- **`Lπ_!(Lε^*(ε_* X)) ≅ Lπ_!(X)`** for a complex `X` of sheaves of `π^{-1}O`-modules bounded
above by `0`. -/
theorem nonempty_derivedProjectionLowerShriek_augmentationBaseChange_iso
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' (augmentationCommRingMap J ε).hom)))
    (X : CochainComplex (SheafOfModules.{u} (augTgtRing J (O := O))) ℤ) [X.IsStrictlyLE 0] :
    Nonempty
      ((derivedProjectionLowerShriek C J (augBaseRing J (O := O))).obj
          ((derivedBaseChangeToProjectionRing J ε).obj
            (DerivedCategory.Q.obj ((augPushforwardC J ε).obj X))) ≅
        (derivedProjectionLowerShriek C J (augBaseRing J (O := O))).obj
          (DerivedCategory.Q.obj X)) := by
  obtain ⟨M, hMLE, hflat, w, hw, hq⟩ := exists_augExtendScalars_quasiIso_total J ε hθ X
  have := hMLE
  refine ⟨(derivedProjectionLowerShriek C J (augBaseRing J (O := O))).mapIso
      ((derivedBaseChangeToProjectionRing J ε).mapIso
          (CochainComplex.derivedIsoOfQuasiIso w hw).symm ≪≫
        augmentationBaseChangeFlatIso J ε M 0 hMLE hflat ≪≫
        DerivedCategory.Q.mapIso ((augmentationBaseChangeComplexIso J ε).app M)) ≪≫ ?_⟩
  exact derivedProjectionLowerShriekIsoMooreBicomplexTotalModules C J
      (augBaseRing J (O := O)) ((augExtendScalarsC J ε).obj M) ≪≫
    CochainComplex.derivedIsoOfQuasiIso _ hq ≪≫
    (derivedProjectionLowerShriekIsoMooreBicomplexTotalModules C J
      (augBaseRing J (O := O)) X).symm

end Concrete

end Stacks.SimplicialModules

end
