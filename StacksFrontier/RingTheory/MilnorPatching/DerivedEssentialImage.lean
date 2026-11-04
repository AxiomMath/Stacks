module

public import StacksFrontier.RingTheory.MilnorPatching.DerivedGlueingMap
public import StacksFrontier.Homology.Perfect.HenselianLiftingSurjection
public import StacksFrontier.RingTheory.Henselian.Pair.Nilpotent

/-!
# Pseudo-coherent objects over a fibre product of rings along a henselian surjection

Let `B' = B ×_A A'` be a fibre product of rings in which `A' → A` is surjective with kernel `I`
and `(A', I)` is a henselian pair (for instance `I` locally nilpotent). Derived extension of
scalars defines a functor from `D(B')` to the 2-fibre product `D(B) ×_{D(A)} D(A')`, whose objects
are triples `(M, K', α)` with `α : M ⊗ᴸ_B A ≅ K' ⊗ᴸ_{A'} A`. This file proves that every triple
with `M` and `K'` pseudo-coherent is in its essential image. Derived categories are arbitrary
`HasDerivedCategory` models, and derived extension of scalars is any total left derived functor
of degreewise extension of scalars.

## Main definitions

* `MilnorPatching.fstDerivedExtensionCompIso` and `MilnorPatching.sndDerivedExtensionCompIso`: the
  canonical identifications `(- ⊗ᴸ_{B'} B) ⊗ᴸ_B A ≅ - ⊗ᴸ_{B'} A ≅ (- ⊗ᴸ_{B'} A') ⊗ᴸ_{A'} A`, the
  2-cell of the functor `D(B') ⥤ D(B) ×_{D(A)} D(A')`.

## Main results

* `MilnorPatching.patchedComplex_derivedExtensionIso_compatible`: the identifications
  `L ⊗ᴸ_{B'} B ≅ E` and `L ⊗ᴸ_{B'} A' ≅ P` for the patched complex `L` of `(E, P, φ)` are
  compatible with the isomorphism `E ⊗ᴸ_B A ≅ P ⊗ᴸ_{A'} A` represented by `φ`.
* `MilnorPatching.isIso_and_compatible_of_distinguished_glueingMap`: for pseudo-coherent `M`, `K'`
  and `α : M ⊗ᴸ_B A ≅ K' ⊗ᴸ_{A'} A`, and any distinguished triangle
  `M' → M ⊕ K' → K' ⊗ᴸ_{A'} A → M'[1]` whose second morphism is the glueing map of `(M, K', α)`,
  the maps `M' ⊗ᴸ_{B'} B ⟶ M` and `M' ⊗ᴸ_{B'} A' ⟶ K'` adjoint to the components of `M' ⟶ M ⊕ K'`
  are isomorphisms compatible with `α`.
* `MilnorPatching.exists_derivedExtension_iso_of_isPseudoCoherent`: for pseudo-coherent
  `M ∈ D(B)` and `K' ∈ D(A')` and `α : M ⊗ᴸ_B A ≅ K' ⊗ᴸ_{A'} A` there are `M' ∈ D(B')` and
  isomorphisms `M' ⊗ᴸ_{B'} B ≅ M` and `M' ⊗ᴸ_{B'} A' ≅ K'` compatible with `α`.
* `MilnorPatching.isIso_homEquiv_symm_of_distinguished_glueingMap`: the isomorphism statement for
  arbitrary adjunctions `Lj ⊣ Rj`, `Lf' ⊣ Rf'`, `Lf ⊣ Rf`, `Li ⊣ Ri` whose right adjoints are
  isomorphic to derived restriction of scalars.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 0BCE](https://stacks.math.columbia.edu/tag/0BCE)
* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ModuleGlueing StacksDraft.PseudoCoherence
  StacksDraft.DerivedExtensionScalarsModelComp
open scoped TensorProduct

universe w₁ w₂ w₃ w₄ u

namespace MilnorPatching

/-- Extension of scalars is additive. -/
local instance extendScalarsAdditiveDerivedEssentialImage {R T : Type u} [CommRing R]
    [CommRing T] (f : R →+* T) : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
  {toBase : B →+* A} {surjection : A' →+* A} (I : Ideal A')
  (s : RingFibreProduct.Situation toBase surjection I)

/-- The retargeting of degreewise extension of scalars along an equality of ring maps, read in the
derived category, is the localization of the retargeting of complexes. -/
theorem eqToHom_extensionOfScalarsComplexGeneral_app {R T : Type u} [CommRing R] [CommRing T]
    [HasDerivedCategory.{w₄} (ModuleCat.{u} T)] {k₁ k₂ : R →+* T} (e : k₁ = k₂)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (eqToHom (congrArg (fun k ↦
        CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral.{u, u, u, w₄} k)
          e)).app L =
      DerivedCategory.Q.map (eqToHom (congrArg (fun k ↦
        ((ModuleCat.extendScalars.{u, u, u} k).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
          e)) := by
  subst e
  simp only [eqToHom_refl, NatTrans.id_app]
  exact (DerivedCategory.Q.map_id _).symm

section Complex

variable (E : CochainComplex (ModuleCat.{u} B) ℤ) (P : CochainComplex (ModuleCat.{u} A') ℤ)
  (φ : ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅
    ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  (hE : ∀ n, Module.Finite B (E.X n) ∧ Module.Projective B (E.X n))
  (hP : ∀ n, Module.Finite A' (P.X n) ∧ Module.Projective A' (P.X n))

/-- **The patching isomorphisms are compatible with `φ`, on complexes.** Going from
`(L ⊗_{B'} B) ⊗_B A` to `(L ⊗_{B'} A') ⊗_{A'} A` through `L ⊗_{B'} A`, and then to `P ⊗_{A'} A`,
is going to `E ⊗_B A` and applying `φ`. -/
theorem patchedComplex_extendScalarsComp_compatible :
    (Functor.mapHomologicalComplexCompIso
        (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
          (fibreProductFst I s) toBase).symm
        (ComplexShape.up ℤ)).hom.app (patchedComplex I s E P φ hE hP) ≫
      eqToHom (congrArg (fun k ↦ ((ModuleCat.extendScalars.{u, u, u} k).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (patchedComplex I s E P φ hE hP))
          (toBase_comp_fibreProductFst I s)) ≫
      (Functor.mapHomologicalComplexCompIso
        (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
          (fibreProductSnd I s) surjection).symm
        (ComplexShape.up ℤ)).inv.app (patchedComplex I s E P φ hE hP) ≫
      ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom =
    ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom ≫ φ.hom := by
  ext n : 1
  have h := patchedComplexExtendScalarsIso_compatible I s E P φ hE hP n
  have hiso : ((fibreProductExtension I s).obj ((patchedComplex I s E P φ hE hP).X n)).iso.hom =
      (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
          (fibreProductFst I s) toBase).inv.app ((patchedComplex I s E P φ hE hP).X n) ≫
        eqToHom (congrArg (fun k ↦ (ModuleCat.extendScalars.{u, u, u} k).obj
          ((patchedComplex I s E P φ hE hP).X n)) (toBase_comp_fibreProductFst I s)) ≫
        (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
          (fibreProductSnd I s) surjection).hom.app ((patchedComplex I s E P φ hE hP).X n) := by
    show ((ModuleGlueing.extendScalarsComp.{u} (fibreProductFst I s) toBase).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars.{u, u, u} (toBase_comp_fibreProductFst I s)) ≪≫
      ModuleGlueing.extendScalarsComp.{u} (fibreProductSnd I s) surjection).hom.app _ = _
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
    rfl
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, HomologicalComplex.eqToHom_f,
    Functor.mapHomologicalComplex_map_f, Iso.symm_hom, Iso.symm_inv] at h ⊢
  rw [h, hiso]
  rfl

end Complex

variable [HasDerivedCategory.{w₁} (ModuleCat.{u} s.fibreProduct)]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} B)] [HasDerivedCategory.{w₃} (ModuleCat.{u} A')]
  [HasDerivedCategory.{w₄} (ModuleCat.{u} A)]
  (F₁ : DerivedCategory (ModuleCat.{u} s.fibreProduct) ⥤ DerivedCategory (ModuleCat.{u} B))
  (α₁ : DerivedCategory.Q ⋙ F₁ ⟶
    (ModuleCat.extendScalars.{u, u, u} (fibreProductFst I s)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F₁.IsLeftDerivedFunctor α₁
    (HomologicalComplex.quasiIso (ModuleCat.{u} s.fibreProduct) (ComplexShape.up ℤ))]
  (F₂ : DerivedCategory (ModuleCat.{u} s.fibreProduct) ⥤ DerivedCategory (ModuleCat.{u} A'))
  (α₂ : DerivedCategory.Q ⋙ F₂ ⟶
    (ModuleCat.extendScalars.{u, u, u} (fibreProductSnd I s)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F₂.IsLeftDerivedFunctor α₂
    (HomologicalComplex.quasiIso (ModuleCat.{u} s.fibreProduct) (ComplexShape.up ℤ))]
  (G₁ : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} A))
  (β₁ : DerivedCategory.Q ⋙ G₁ ⟶
    (ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G₁.IsLeftDerivedFunctor β₁ (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))]
  (G₂ : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} A))
  (β₂ : DerivedCategory.Q ⋙ G₂ ⟶
    (ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G₂.IsLeftDerivedFunctor β₂
    (HomologicalComplex.quasiIso (ModuleCat.{u} A') (ComplexShape.up ℤ))]

/-- The canonical identification `(- ⊗ᴸ_{B'} B) ⊗ᴸ_B A ≅ - ⊗ᴸ_{B'} A`, the target being the
chosen derived extension of scalars along `B' → A`. -/
abbrev fstDerivedExtensionCompIso :
    F₁ ⋙ G₁ ≅ (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (fibreProductToBase I s)).functor :=
  compModelIso.{u, u, u, u, w₁, w₂, w₄} (fibreProductFst I s) toBase F₁ α₁ G₁ β₁
    (fibreProductToBase I s) (toBase_comp_fibreProductFst I s) (hFld := ‹_›) (hGld := ‹_›)

/-- The canonical identification `(- ⊗ᴸ_{B'} A') ⊗ᴸ_{A'} A ≅ - ⊗ᴸ_{B'} A`, the target being the
chosen derived extension of scalars along `B' → A`. -/
abbrev sndDerivedExtensionCompIso :
    F₂ ⋙ G₂ ≅ (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (fibreProductToBase I s)).functor :=
  compModelIso.{u, u, u, u, w₁, w₃, w₄} (fibreProductSnd I s) surjection F₂ α₂ G₂ β₂
    (fibreProductToBase I s) rfl (hFld := ‹_›) (hGld := ‹_›)

section Compatible

variable (E : CochainComplex (ModuleCat.{u} B) ℤ) (P : CochainComplex (ModuleCat.{u} A') ℤ)
  (φ : ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅
    ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  (hE : ∀ n, Module.Finite B (E.X n) ∧ Module.Projective B (E.X n))
  (hP : ∀ n, Module.Finite A' (P.X n) ∧ Module.Projective A' (P.X n))

/-- If `i.hom ≫ κ = w ≫ g.hom` for isomorphisms `i` and `g`, then `i.inv ≫ w = κ ≫ g.inv`. -/
private theorem inv_comp_eq_of_hom_comp_eq {𝒞 : Type*} [Category* 𝒞] {X Y A B : 𝒞} (i : X ≅ Y)
    (g : A ≅ B) (w : X ⟶ A) (κ : Y ⟶ B) (h : i.hom ≫ κ = w ≫ g.hom) :
    i.inv ≫ w = κ ≫ g.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The patching isomorphisms are compatible with `φ`, in the derived categories.** For the
patched complex `L` of `(E, P, φ)`, going from `(L ⊗ᴸ_{B'} B) ⊗ᴸ_B A` to `E ⊗ᴸ_B A` and then to
`P ⊗ᴸ_{A'} A` by the isomorphism represented by `φ` is going to `(L ⊗ᴸ_{B'} A') ⊗ᴸ_{A'} A` through
`L ⊗ᴸ_{B'} A` and then to `P ⊗ᴸ_{A'} A`. -/
theorem patchedComplex_derivedExtensionIso_compatible (d : ℤ) [E.IsStrictlyLE d]
    [P.IsStrictlyLE d] [IsIso (β₁.app E)] [IsIso (β₂.app P)] :
    (fstDerivedExtensionCompIso I s F₁ α₁ G₁ β₁).inv.app
        (DerivedCategory.Q.obj (patchedComplex I s E P φ hE hP)) ≫
      G₁.map (patchedComplexDerivedExtensionFstIso I s E P φ hE hP F₁ α₁ d).hom ≫
        (complexDerivedExtensionIso E P φ G₁ β₁ G₂ β₂).hom =
    (sndDerivedExtensionCompIso I s F₂ α₂ G₂ β₂).inv.app
        (DerivedCategory.Q.obj (patchedComplex I s E P φ hE hP)) ≫
      G₂.map (patchedComplexDerivedExtensionSndIso I s E P φ hE hP F₂ α₂ d).hom := by
  rw [← cancel_mono (β₂.app P)]
  simp only [Category.assoc]
  rw [complexDerivedExtensionIso_hom_comp]
  let L := patchedComplex I s E P φ hE hP
  let D₁ : ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{u, u, u}
          (fibreProductFst I s)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≅
      ((ModuleCat.extendScalars.{u, u, u} (fibreProductToBase I s)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L :=
    (Functor.mapHomologicalComplexCompIso
        (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
          (fibreProductFst I s) toBase).symm (ComplexShape.up ℤ)).app L ≪≫
      eqToIso (congrArg (fun k ↦ ((ModuleCat.extendScalars.{u, u, u} k).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) (toBase_comp_fibreProductFst I s))
  let D₂ : ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{u, u, u}
          (fibreProductSnd I s)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≅
      ((ModuleCat.extendScalars.{u, u, u} (fibreProductToBase I s)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L :=
    (Functor.mapHomologicalComplexCompIso
        (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
          (fibreProductSnd I s) surjection).symm (ComplexShape.up ℤ)).app L
  have q₁ : DerivedCategory.Q.map D₁.hom =
      (extensionOfScalarsComplexCompIso.{u, u, u, u, w₄} (fibreProductFst I s) toBase).hom.app L ≫
        (eqToHom (congrArg (fun k ↦
          CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral.{u, u, u, w₄} k)
          (toBase_comp_fibreProductFst I s))).app L := by
    rw [eqToHom_extensionOfScalarsComplexGeneral_app (toBase_comp_fibreProductFst I s) L]
    exact DerivedCategory.Q.map_comp _ _
  have z₁ : (fstDerivedExtensionCompIso I s F₁ α₁ G₁ β₁).hom.app (DerivedCategory.Q.obj L) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (fibreProductToBase I s)).comparison.app L =
      G₁.map (α₁.app L) ≫ β₁.app _ ≫ DerivedCategory.Q.map D₁.hom := by
    refine (compModelIso_hom_app_comp_comparison _ _ _ _ _ _ _ _ (hFld := ‹_›) (hGld := ‹_›)
      L).trans ?_
    rw [q₁]
    simp only [compComparisonOfEq, NatTrans.comp_app]
    show (G₁.map (α₁.app L) ≫ β₁.app _ ≫
      (extensionOfScalarsComplexCompIso.{u, u, u, u, w₄} (fibreProductFst I s) toBase).hom.app L) ≫
        _ = _
    simp only [Category.assoc]
    congr 1
    exact Category.assoc _ _ _
  have z₂ : (sndDerivedExtensionCompIso I s F₂ α₂ G₂ β₂).hom.app (DerivedCategory.Q.obj L) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (fibreProductToBase I s)).comparison.app L =
      G₂.map (α₂.app L) ≫ β₂.app _ ≫ DerivedCategory.Q.map D₂.hom := by
    refine (compModelIso_hom_app_comp_comparison _ _ _ _ _ _ _ _ (hFld := ‹_›) (hGld := ‹_›)
      L).trans ?_
    simp only [compComparisonOfEq, eqToHom_refl, Category.comp_id]
    rfl
  let κ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (fibreProductToBase I s)).functor.obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u}
        (fibreProductToBase I s)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (fibreProductToBase I s)).comparison.app L
  have k₁ : (fstDerivedExtensionCompIso I s F₁ α₁ G₁ β₁).inv.app (DerivedCategory.Q.obj L) ≫
      G₁.map (α₁.app L) ≫ β₁.app _ =
      κ ≫ DerivedCategory.Q.map D₁.inv :=
    inv_comp_eq_of_hom_comp_eq
      ((fstDerivedExtensionCompIso I s F₁ α₁ G₁ β₁).app (DerivedCategory.Q.obj L))
      (DerivedCategory.Q.mapIso D₁) _ _
      (z₁.trans (Category.assoc _ _ _).symm)
  have k₂ : (sndDerivedExtensionCompIso I s F₂ α₂ G₂ β₂).inv.app (DerivedCategory.Q.obj L) ≫
      G₂.map (α₂.app L) ≫ β₂.app _ =
      κ ≫ DerivedCategory.Q.map D₂.inv :=
    inv_comp_eq_of_hom_comp_eq
      ((sndDerivedExtensionCompIso I s F₂ α₂ G₂ β₂).app (DerivedCategory.Q.obj L))
      (DerivedCategory.Q.mapIso D₂) _ _
      (z₂.trans (Category.assoc _ _ _).symm)
  have hK := patchedComplex_extendScalarsComp_compatible I s E P φ hE hP
  have hK' : D₁.inv ≫ ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom ≫
        φ.hom =
      D₂.inv ≫ ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom := by
    rw [Iso.inv_comp_eq]
    simp only [D₁, D₂, Iso.trans_hom, eqToIso.hom, Iso.app_hom, Iso.app_inv, Category.assoc]
    exact hK.symm
  have hQK : DerivedCategory.Q.map D₁.inv ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom) ≫
        DerivedCategory.Q.map φ.hom =
      DerivedCategory.Q.map D₂.inv ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom) := by
    simp only [← CategoryTheory.Functor.map_comp, hK']
  have c₁ : G₁.map (patchedComplexDerivedExtensionFstIso I s E P φ hE hP F₁ α₁ d).hom ≫
      β₁.app E = G₁.map (α₁.app L) ≫ β₁.app _ ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom) := by
    change G₁.map (α₁.app L ≫ _) ≫ _ = _
    rw [G₁.map_comp, Category.assoc]
    exact congrArg (G₁.map (α₁.app L) ≫ ·) (β₁.naturality _)
  have c₂ : G₂.map (patchedComplexDerivedExtensionSndIso I s E P φ hE hP F₂ α₂ d).hom ≫
      β₂.app P = G₂.map (α₂.app L) ≫ β₂.app _ ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom) := by
    change G₂.map (α₂.app L ≫ _) ≫ _ = _
    rw [G₂.map_comp, Category.assoc]
    exact congrArg (G₂.map (α₂.app L) ≫ ·) (β₂.naturality _)
  rw [reassoc_of% c₁, c₂, reassoc_of% k₁, reassoc_of% k₂, hQK]

end Compatible

/-- The transpose of `e ≫ Q(ψ♭) ≫ m` under the derived extension of scalars adjunction, where `ψ♭`
is the transpose of `ψ : K ⊗_R T ≅ X`, is `F e ≫ α_K ≫ Q ψ ≫ m`. -/
private theorem homEquiv_symm_comp_Q_map_comp {R T : Type u} [CommRing R] [CommRing T]
    [HasDerivedCategory.{w₁} (ModuleCat.{u} R)] [HasDerivedCategory.{w₂} (ModuleCat.{u} T)]
    (f : R →+* T) (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
    (α : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    {Z : DerivedCategory (ModuleCat.{u} R)} {K : CochainComplex (ModuleCat.{u} R) ℤ}
    {X : CochainComplex (ModuleCat.{u} T) ℤ} {Y : DerivedCategory (ModuleCat.{u} T)}
    (e : Z ⟶ DerivedCategory.Q.obj K)
    (ψ : ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ≅ X) (m : DerivedCategory.Q.obj X ⟶ Y) :
    ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
      f F α).homEquiv _ _).symm
        (e ≫ DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).homEquiv _ _ ψ.hom) ≫
          (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app X ≫
            (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map m) =
      F.map e ≫ (α.app K ≫ DerivedCategory.Q.map ψ.hom) ≫ m := by
  rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc (DerivedCategory.Q.map _),
    Adjunction.homEquiv_naturality_right_symm]
  exact congrArg (fun t ↦ F.map e ≫ t ≫ m)
    (derivedExtensionScalarsAdjunction_homEquiv_symm_Q_map f F α K X ψ)

open CochainComplex.DerivedExtensionScalars (derivedExtensionScalarsAdjunction) in
/-- Let `B' = B ×_A A'` be a fibre product of rings in which `A' → A` is surjective with kernel `I`
and `(A', I)` is a henselian pair. Let `M ∈ D(B)` and `K' ∈ D(A')` be pseudo-coherent and
`α : M ⊗ᴸ_B A ≅ K' ⊗ᴸ_{A'} A`, and let `M' → M ⊕ K' → (K' ⊗ᴸ_{A'} A) → M'[1]` be a distinguished
triangle in `D(B')` whose second morphism is the glueing map of `(M, K', α)`
(`MilnorPatching.glueingMap`, for derived restriction of scalars and the derived change-of-rings
adjunctions). Then the maps `a : M' ⊗ᴸ_{B'} B ⟶ M` and `b : M' ⊗ᴸ_{B'} A' ⟶ K'` adjoint to the two
components of `M' ⟶ M ⊕ K'` are isomorphisms, and `α ∘ (a ⊗ᴸ A)` and `b ⊗ᴸ A` agree through the
canonical identifications `(M' ⊗ᴸ_{B'} B) ⊗ᴸ_B A ≅ M' ⊗ᴸ_{B'} A ≅ (M' ⊗ᴸ_{B'} A') ⊗ᴸ_{A'} A`. -/
theorem isIso_and_compatible_of_distinguished_glueingMap (hI : HenselianPair A' I)
    (M : DerivedCategory (ModuleCat.{u} B)) (hM : IsPseudoCoherentIn M)
    (K' : DerivedCategory (ModuleCat.{u} A')) (hK' : IsPseudoCoherentIn K')
    (α : G₁.obj M ≅ G₂.obj K')
    (Tr : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} s.fibreProduct)))
    (hTr : Tr ∈ distTriang (DerivedCategory (ModuleCat.{u} s.fibreProduct)))
    (e₂ : Tr.obj₂ ≅ (derivedRestrictFst I s).obj M ⊞ (derivedRestrictSnd I s).obj K')
    (e₃ : Tr.obj₃ ≅ (derivedRestrictFst I s).obj
      ((ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory.obj (G₂.obj K')))
    (comm : Tr.mor₂ ≫ e₃.hom = e₂.hom ≫ glueingMap
      (derivedExtensionScalarsAdjunction.{u, u, u} toBase G₁ β₁)
      (derivedExtensionScalarsAdjunction.{u, u, u} surjection G₂ β₂)
      (derivedRestrictCompIso I s) M K' α.hom) :
    IsIso (((derivedExtensionScalarsAdjunction.{u, u, u} (fibreProductFst I s) F₁ α₁).homEquiv
        _ _).symm (Tr.mor₁ ≫ e₂.hom ≫ biprod.fst)) ∧
      IsIso (((derivedExtensionScalarsAdjunction.{u, u, u} (fibreProductSnd I s) F₂ α₂).homEquiv
        _ _).symm (Tr.mor₁ ≫ e₂.hom ≫ biprod.snd)) ∧
      (fstDerivedExtensionCompIso I s F₁ α₁ G₁ β₁).inv.app Tr.obj₁ ≫
          G₁.map (((derivedExtensionScalarsAdjunction.{u, u, u} (fibreProductFst I s) F₁
            α₁).homEquiv _ _).symm (Tr.mor₁ ≫ e₂.hom ≫ biprod.fst)) ≫ α.hom =
        (sndDerivedExtensionCompIso I s F₂ α₂ G₂ β₂).inv.app Tr.obj₁ ≫
          G₂.map (((derivedExtensionScalarsAdjunction.{u, u, u} (fibreProductSnd I s) F₂
            α₂).homEquiv _ _).symm (Tr.mor₁ ≫ e₂.hom ≫ biprod.snd)) := by
  classical
  obtain ⟨E, hE, ⟨m⟩⟩ := hM
  have hEterms : ∀ n, Module.Finite B (E.X n) ∧ Module.Projective B (E.X n) := fun n ↦ by
    have := (hE.finiteFree n).1
    have := (hE.finiteFree n).2
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨d₁, hd₁⟩ := hE.upperBound
  have hEflat : CochainComplex.KFlat.{u, u} E := by
    have : ∀ n, Module.Flat B (E.X n) := fun n ↦ by
      have := (hEterms n).2
      exact Module.Flat.of_projective
    exact CochainComplex.KFlat.kFlat_of_flat.{u, u} E d₁
  have hβE : IsIso (β₁.app E) :=
    CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{u, u, u} toBase G₁ β₁ E
      hEflat
  have hFbdd : ∃ b, CochainComplex.IsStrictlyLE (((ModuleCat.extendScalars.{u, u, u}
      toBase).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) b := ⟨d₁, inferInstance⟩
  have hFterms : ∀ n, Module.Finite A ((((ModuleCat.extendScalars.{u, u, u}
      toBase).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n) ∧
      Module.Projective A ((((ModuleCat.extendScalars.{u, u, u}
        toBase).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n) := fun n ↦ by
    have := (hEterms n).1
    have := (hEterms n).2
    let : Algebra B A := toBase.toAlgebra
    exact ⟨inferInstanceAs (Module.Finite A (A ⊗[B] E.X n)),
      inferInstanceAs (Module.Projective A (A ⊗[B] E.X n))⟩
  let eGiven : DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u}
      toBase).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅ G₂.obj K' :=
    (asIso (β₁.app E)).symm ≪≫ G₁.mapIso m ≪≫ α
  have hI' : HenselianPair A' (RingHom.ker surjection) := s.ker_surjection ▸ hI
  obtain ⟨P, hP, ⟨d₂, hd₂⟩, ψ, eK, hcompat⟩ :=
    StacksDraft.Perfect.exists_finiteProjective_lift_iso_of_surjective surjection
      s.surjective_surjection hI' G₂ β₂ K' hK' _ hFbdd hFterms eGiven
  have : E.IsStrictlyLE (max d₁ d₂) := E.isStrictlyLE_of_le d₁ _ (le_max_left _ _)
  have : P.IsStrictlyLE (max d₁ d₂) := P.isStrictlyLE_of_le d₂ _ (le_max_right _ _)
  have hPflat : CochainComplex.KFlat.{u, u} P := by
    have : ∀ n, Module.Flat A' (P.X n) := fun n ↦ by
      have := (hP n).2
      exact Module.Flat.of_projective
    exact CochainComplex.KFlat.kFlat_of_flat.{u, u} P d₂
  have hβP : IsIso (β₂.app P) :=
    CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{u, u, u} surjection G₂
      β₂ P hPflat
  let αφ := complexDerivedExtensionIso E P ψ.symm G₁ β₁ G₂ β₂
  have hrel : G₁.map m.hom ≫ α.hom = αφ.hom ≫ G₂.map eK.hom := by
    rw [← hcompat]
    simp [αφ, complexDerivedExtensionIso, eGiven]
  let adjF := derivedExtensionScalarsAdjunction.{u, u, u} toBase G₁ β₁
  let adjI := derivedExtensionScalarsAdjunction.{u, u, u} surjection G₂ β₂
  have hnat := biprod_map_comp_glueingMap adjF adjI (derivedRestrictCompIso I s) m.hom eK.hom
    αφ.hom α.hom hrel
  let bm := biprod.mapIso ((derivedRestrictFst I s).mapIso m) ((derivedRestrictSnd I s).mapIso eK)
  let X := (derivedRestrictFst I s).mapIso
    ((ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory.mapIso (G₂.mapIso eK))
  have hg : glueingMap adjF adjI (derivedRestrictCompIso I s) M K' α.hom ≫ X.inv =
      bm.inv ≫ glueingMap adjF adjI (derivedRestrictCompIso I s) (DerivedCategory.Q.obj E)
        (DerivedCategory.Q.obj P) αφ.hom := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hnat
  obtain ⟨e₁, h₁⟩ := exists_iso_patchedComplex_of_distinguished_glueingMap I s E P ψ.symm hEterms
    hP G₁ β₁ G₂ β₂ Tr hTr (e₂ ≪≫ bm.symm) (e₃ ≪≫ X.symm) (by
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [reassoc_of% comm, hg, Category.assoc])
  have key : ∀ {Z : DerivedCategory (ModuleCat.{u} s.fibreProduct)}
      (p : (derivedRestrictFst I s).obj M ⊞ (derivedRestrictSnd I s).obj K' ⟶ Z)
      (k : DerivedCategory.Q.obj (restrictedFst I s E ⊞ restrictedSnd I s P) ⟶ Z),
      bm.inv ≫ (glueingSourceIso I s E P).hom ≫ k = p →
        Tr.mor₁ ≫ e₂.hom ≫ p = e₁.hom ≫ DerivedCategory.Q.map (biprod.lift
          (patchedComplexToFst I s E P ψ.symm hEterms hP)
          (patchedComplexToSnd I s E P ψ.symm hEterms hP)) ≫ k := by
    rintro Z p k rfl
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc] at h₁
    rw [reassoc_of% h₁]
  have key₁ : Tr.mor₁ ≫ e₂.hom ≫ biprod.fst =
      e₁.hom ≫ DerivedCategory.Q.map (patchedComplexToFst I s E P ψ.symm hEterms hP) ≫
        (ModuleCat.restrictScalars.{u} (fibreProductFst I s)).mapDerivedCategoryFactors.inv.app
          E ≫ (derivedRestrictFst I s).map m.hom := by
    rw [key _ (DerivedCategory.Q.map biprod.fst ≫
        (ModuleCat.restrictScalars.{u} (fibreProductFst I s)).mapDerivedCategoryFactors.inv.app
          E ≫ (derivedRestrictFst I s).map m.hom) (by
        rw [glueingSourceIso_hom_fst_assoc, Iso.hom_inv_id_app_assoc]; simp [bm]),
      ← DerivedCategory.Q.map_comp_assoc, biprod.lift_fst]
  have key₂ : Tr.mor₁ ≫ e₂.hom ≫ biprod.snd =
      e₁.hom ≫ DerivedCategory.Q.map (patchedComplexToSnd I s E P ψ.symm hEterms hP) ≫
        (ModuleCat.restrictScalars.{u} (fibreProductSnd I s)).mapDerivedCategoryFactors.inv.app
          P ≫ (derivedRestrictSnd I s).map eK.hom := by
    rw [key _ (DerivedCategory.Q.map biprod.snd ≫
        (ModuleCat.restrictScalars.{u} (fibreProductSnd I s)).mapDerivedCategoryFactors.inv.app
          P ≫ (derivedRestrictSnd I s).map eK.hom) (by
        rw [glueingSourceIso_hom_snd_assoc, Iso.hom_inv_id_app_assoc]; simp [bm]),
      ← DerivedCategory.Q.map_comp_assoc, biprod.lift_snd]
  have ha : ((derivedExtensionScalarsAdjunction.{u, u, u} (fibreProductFst I s) F₁ α₁).homEquiv
      _ _).symm (Tr.mor₁ ≫ e₂.hom ≫ biprod.fst) = F₁.map e₁.hom ≫
        (patchedComplexDerivedExtensionFstIso I s E P ψ.symm hEterms hP F₁ α₁ (max d₁ d₂)).hom ≫
          m.hom := by
    rw [key₁]
    exact homEquiv_symm_comp_Q_map_comp (fibreProductFst I s) F₁ α₁ e₁.hom
      (patchedComplexExtendScalarsFstIso I s E P ψ.symm hEterms hP) m.hom
  have hb : ((derivedExtensionScalarsAdjunction.{u, u, u} (fibreProductSnd I s) F₂ α₂).homEquiv
      _ _).symm (Tr.mor₁ ≫ e₂.hom ≫ biprod.snd) = F₂.map e₁.hom ≫
        (patchedComplexDerivedExtensionSndIso I s E P ψ.symm hEterms hP F₂ α₂ (max d₁ d₂)).hom ≫
          eK.hom := by
    rw [key₂]
    exact homEquiv_symm_comp_Q_map_comp (fibreProductSnd I s) F₂ α₂ e₁.hom
      (patchedComplexExtendScalarsSndIso I s E P ψ.symm hEterms hP) eK.hom
  refine ⟨by rw [ha]; infer_instance, by rw [hb]; infer_instance, ?_⟩
  rw [ha, hb]
  have nat₁ : (fstDerivedExtensionCompIso I s F₁ α₁ G₁ β₁).inv.app Tr.obj₁ ≫
      G₁.map (F₁.map e₁.hom) =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (fibreProductToBase I s)).functor.map e₁.hom ≫
        (fstDerivedExtensionCompIso I s F₁ α₁ G₁ β₁).inv.app
          (DerivedCategory.Q.obj (patchedComplex I s E P ψ.symm hEterms hP)) :=
    ((fstDerivedExtensionCompIso I s F₁ α₁ G₁ β₁).inv.naturality e₁.hom).symm
  have nat₂ : (sndDerivedExtensionCompIso I s F₂ α₂ G₂ β₂).inv.app Tr.obj₁ ≫
      G₂.map (F₂.map e₁.hom) =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (fibreProductToBase I s)).functor.map e₁.hom ≫
        (sndDerivedExtensionCompIso I s F₂ α₂ G₂ β₂).inv.app
          (DerivedCategory.Q.obj (patchedComplex I s E P ψ.symm hEterms hP)) :=
    ((sndDerivedExtensionCompIso I s F₂ α₂ G₂ β₂).inv.naturality e₁.hom).symm
  have hX := patchedComplex_derivedExtensionIso_compatible I s F₁ α₁ F₂ α₂ G₁ β₁ G₂ β₂ E P
    ψ.symm hEterms hP (max d₁ d₂)
  simp only [Functor.map_comp, Category.assoc]
  rw [hrel, reassoc_of% nat₁, reassoc_of% hX, reassoc_of% nat₂]

open CochainComplex.DerivedExtensionScalars (derivedExtensionScalarsAdjunction) in
/-- Let `B' = B ×_A A'` be a fibre product of rings in which `A' → A` is surjective with kernel `I`
and `(A', I)` is a henselian pair. Let `M ∈ D(B)` and `K' ∈ D(A')` be pseudo-coherent and
`α : M ⊗ᴸ_B A ≅ K' ⊗ᴸ_{A'} A`. Then the triple `(M, K', α)` is in the essential image of derived
extension of scalars `D(B') ⥤ D(B) ×_{D(A)} D(A')`: there are `M' ∈ D(B')` and isomorphisms
`a : M' ⊗ᴸ_{B'} B ≅ M` and `b : M' ⊗ᴸ_{B'} A' ≅ K'` such that `α ∘ (a ⊗ᴸ A)` and `b ⊗ᴸ A` agree
through the canonical identifications
`(M' ⊗ᴸ_{B'} B) ⊗ᴸ_B A ≅ M' ⊗ᴸ_{B'} A ≅ (M' ⊗ᴸ_{B'} A') ⊗ᴸ_{A'} A`. -/
theorem exists_derivedExtension_iso_of_isPseudoCoherent (hI : HenselianPair A' I)
    (M : DerivedCategory (ModuleCat.{u} B)) (hM : IsPseudoCoherentIn M)
    (K' : DerivedCategory (ModuleCat.{u} A')) (hK' : IsPseudoCoherentIn K')
    (α : G₁.obj M ≅ G₂.obj K') :
    ∃ (M' : DerivedCategory (ModuleCat.{u} s.fibreProduct)) (a : F₁.obj M' ≅ M)
      (b : F₂.obj M' ≅ K'),
      (fstDerivedExtensionCompIso I s F₁ α₁ G₁ β₁).inv.app M' ≫ G₁.map a.hom ≫ α.hom =
        (sndDerivedExtensionCompIso I s F₂ α₂ G₂ β₂).inv.app M' ≫ G₂.map b.hom := by
  obtain ⟨M', u₁, w, hT⟩ := Pretriangulated.distinguished_cocone_triangle₁ (glueingMap
    (derivedExtensionScalarsAdjunction.{u, u, u} toBase G₁ β₁)
    (derivedExtensionScalarsAdjunction.{u, u, u} surjection G₂ β₂)
    (derivedRestrictCompIso I s) M K' α.hom)
  obtain ⟨ha, hb, hc⟩ := isIso_and_compatible_of_distinguished_glueingMap I s F₁ α₁ F₂ α₂ G₁ β₁
    G₂ β₂ hI M hM K' hK' α _ hT (Iso.refl _) (Iso.refl _) (by simp)
  exact ⟨M', asIso _, asIso _, hc⟩

/-- `MilnorPatching.exists_derivedExtension_iso_of_isPseudoCoherent` when the kernel `I` of
`A' → A` is contained in the nilradical of `A'`. -/
theorem exists_derivedExtension_iso_of_isPseudoCoherent_of_le_nilradical
    (hI : I ≤ nilradical A')
    (M : DerivedCategory (ModuleCat.{u} B)) (hM : IsPseudoCoherentIn M)
    (K' : DerivedCategory (ModuleCat.{u} A')) (hK' : IsPseudoCoherentIn K')
    (α : G₁.obj M ≅ G₂.obj K') :
    ∃ (M' : DerivedCategory (ModuleCat.{u} s.fibreProduct)) (a : F₁.obj M' ≅ M)
      (b : F₂.obj M' ≅ K'),
      (fstDerivedExtensionCompIso I s F₁ α₁ G₁ β₁).inv.app M' ≫ G₁.map a.hom ≫ α.hom =
        (sndDerivedExtensionCompIso I s F₂ α₂ G₂ β₂).inv.app M' ≫ G₂.map b.hom :=
  have := (etaleBaseChange_isEquivalence_and_henselianRing_of_le_nilradical I hI).2
  exists_derivedExtension_iso_of_isPseudoCoherent I s F₁ α₁ F₂ α₂ G₁ β₁ G₂ β₂
    (henselianPair_of_henselianRing A' I) M hM K' hK' α

section Transport

open CochainComplex.DerivedExtensionScalars (derivedExtensionScalarsAdjunction
  totalDerivedExtensionScalars)

/-- If the right adjoint of `adj` is isomorphic to that of `adj₀`, then transposing along `adj` is
an isomorphism as soon as transposing the composite with the isomorphism along `adj₀` is. -/
private theorem isIso_homEquiv_symm_of_ofNatIsoRight {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    {L L₀ : 𝒞 ⥤ 𝒟} {R R₀ : 𝒟 ⥤ 𝒞} (adj : L ⊣ R) (e : R ≅ R₀) (adj₀ : L₀ ⊣ R₀) {X : 𝒞} {Y : 𝒟}
    (x : X ⟶ R.obj Y) (h : IsIso ((adj₀.homEquiv _ _).symm (x ≫ e.hom.app Y))) :
    IsIso ((adj.homEquiv _ _).symm x) := by
  have : (adj.homEquiv _ _).symm x = ((adj.ofNatIsoRight e).leftAdjointUniq adj₀).hom.app X ≫
      (adj₀.homEquiv _ _).symm (x ≫ e.hom.app Y) := by
    rw [← homEquiv_symm_eq_leftAdjointUniq_hom_app_comp,
      Adjunction.homEquiv_ofNatIsoRight_symm_apply, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  rw [this]
  infer_instance

/-- Let `Lj ⊣ Rj`, `Lf' ⊣ Rf'`, `Lf ⊣ Rf` and `Li ⊣ Ri` be any adjunctions between the derived
categories of `B'`, `B`, `A'` and `A` (at any models) whose right adjoints are isomorphic to
derived restriction of scalars along `B' → B`, `B' → A'`, `B → A` and `A' → A`, and let
`c : Rf ⋙ Rj ≅ Ri ⋙ Rf'` correspond, under these isomorphisms, to the canonical identification
`MilnorPatching.derivedRestrictCompIso`. For pseudo-coherent `M ∈ D(B)` and `K' ∈ D(A')` and
`α : Lf M ≅ Li K'`, if `M' → Rj M ⊕ Rf' K' → Rj (Rf (Li K')) → M'[1]` is a distinguished triangle
whose second morphism is the glueing map of `(M, K', α)`, then the maps `Lj M' ⟶ M` and
`Lf' M' ⟶ K'` adjoint to the two components of `M' ⟶ Rj M ⊕ Rf' K'` are isomorphisms.

No compatibility of the units and counits of the four adjunctions with those of the
change-of-rings adjunctions is assumed. -/
theorem isIso_homEquiv_symm_of_distinguished_glueingMap (hI : HenselianPair A' I)
    {Lj : DerivedCategory (ModuleCat.{u} s.fibreProduct) ⥤ DerivedCategory (ModuleCat.{u} B)}
    {Rj : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} s.fibreProduct)}
    (adjJ : Lj ⊣ Rj) (eJ : Rj ≅ derivedRestrictFst I s)
    {Lf' : DerivedCategory (ModuleCat.{u} s.fibreProduct) ⥤ DerivedCategory (ModuleCat.{u} A')}
    {Rf' : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} s.fibreProduct)}
    (adjF' : Lf' ⊣ Rf') (eF' : Rf' ≅ derivedRestrictSnd I s)
    {Lf : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} A)}
    {Rf : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B)}
    (adjF : Lf ⊣ Rf) (eF : Rf ≅ (ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory)
    {Li : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} A)}
    {Ri : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A')}
    (adjI : Li ⊣ Ri) (eI : Ri ≅ (ModuleCat.restrictScalars.{u} surjection).mapDerivedCategory)
    (c : Rf ⋙ Rj ≅ Ri ⋙ Rf')
    (hc : ∀ X : DerivedCategory (ModuleCat.{u} A),
      c.hom.app X ≫ eF'.hom.app (Ri.obj X) ≫ (derivedRestrictSnd I s).map (eI.hom.app X) =
        eJ.hom.app (Rf.obj X) ≫ (derivedRestrictFst I s).map (eF.hom.app X) ≫
          (derivedRestrictCompIso I s).hom.app X)
    (M : DerivedCategory (ModuleCat.{u} B)) (hM : IsPseudoCoherentIn M)
    (K' : DerivedCategory (ModuleCat.{u} A')) (hK' : IsPseudoCoherentIn K')
    (α : Lf.obj M ≅ Li.obj K') {M' : DerivedCategory (ModuleCat.{u} s.fibreProduct)}
    (u : M' ⟶ Rj.obj M ⊞ Rf'.obj K') (w : Rj.obj (Rf.obj (Li.obj K')) ⟶ M'⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk u (glueingMap adjF adjI c M K' α.hom) w ∈
      distTriang (DerivedCategory (ModuleCat.{u} s.fibreProduct))) :
    IsIso ((adjJ.homEquiv _ _).symm (u ≫ biprod.fst)) ∧
      IsIso ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)) := by
  let D₁ := totalDerivedExtensionScalars.{u, u, u} (fibreProductFst I s)
  let D₂ := totalDerivedExtensionScalars.{u, u, u} (fibreProductSnd I s)
  let D₃ := totalDerivedExtensionScalars.{u, u, u} toBase
  let D₄ := totalDerivedExtensionScalars.{u, u, u} surjection
  let γ₁ : DerivedCategory.Q ⋙ D₁.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} (fibreProductFst I s)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D₁.comparison
  let γ₂ : DerivedCategory.Q ⋙ D₂.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} (fibreProductSnd I s)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D₂.comparison
  let γ₃ : DerivedCategory.Q ⋙ D₃.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D₃.comparison
  let γ₄ : DerivedCategory.Q ⋙ D₄.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D₄.comparison
  have : D₁.functor.IsLeftDerivedFunctor γ₁
      (HomologicalComplex.quasiIso (ModuleCat.{u} s.fibreProduct) (ComplexShape.up ℤ)) :=
    D₁.isLeftDerived
  have : D₂.functor.IsLeftDerivedFunctor γ₂
      (HomologicalComplex.quasiIso (ModuleCat.{u} s.fibreProduct) (ComplexShape.up ℤ)) :=
    D₂.isLeftDerived
  have : D₃.functor.IsLeftDerivedFunctor γ₃
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)) := D₃.isLeftDerived
  have : D₄.functor.IsLeftDerivedFunctor γ₄
      (HomologicalComplex.quasiIso (ModuleCat.{u} A') (ComplexShape.up ℤ)) := D₄.isLeftDerived
  let adj₁ := derivedExtensionScalarsAdjunction.{u, u, u} (fibreProductFst I s) D₁.functor γ₁
  let adj₂ := derivedExtensionScalarsAdjunction.{u, u, u} (fibreProductSnd I s) D₂.functor γ₂
  let adj₃ := derivedExtensionScalarsAdjunction.{u, u, u} toBase D₃.functor γ₃
  let adj₄ := derivedExtensionScalarsAdjunction.{u, u, u} surjection D₄.functor γ₄
  let θF := (adjF.ofNatIsoRight eF).leftAdjointUniq adj₃
  let θI := (adjI.ofNatIsoRight eI).leftAdjointUniq adj₄
  let α' : D₃.functor.obj M ≅ D₄.functor.obj K' := θF.symm.app M ≪≫ α ≪≫ θI.app K'
  have h₁ := glueingMap_comp_ofNatIsoRight adjF adjI c eJ eF' eF eI (derivedRestrictCompIso I s)
    hc M K' α.hom
  have h₂ := glueingMap_comp_leftAdjointUniq (adjF.ofNatIsoRight eF) (adjI.ofNatIsoRight eI)
    (derivedRestrictCompIso I s) adj₃ adj₄ M K' α.hom
  let e₂ : Rj.obj M ⊞ Rf'.obj K' ≅
      (derivedRestrictFst I s).obj M ⊞ (derivedRestrictSnd I s).obj K' :=
    biprod.mapIso (eJ.app M) (eF'.app K')
  let e₃ : Rj.obj (Rf.obj (Li.obj K')) ≅ (derivedRestrictFst I s).obj
      ((ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory.obj (D₄.functor.obj K')) :=
    eJ.app _ ≪≫ (derivedRestrictFst I s).mapIso (eF.app _) ≪≫
      (derivedRestrictFst I s).mapIso
        ((ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory.mapIso (θI.app K'))
  obtain ⟨ha, hb, -⟩ := isIso_and_compatible_of_distinguished_glueingMap I s D₁.functor γ₁
    D₂.functor γ₂ D₃.functor γ₃ D₄.functor γ₄ hI
    M hM K' hK' α' _ hT e₂ e₃ (by
      show glueingMap adjF adjI c M K' α.hom ≫ eJ.hom.app _ ≫
          (derivedRestrictFst I s).map (eF.hom.app _) ≫ (derivedRestrictFst I s).map
            ((ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory.map (θI.hom.app K')) = _
      rw [reassoc_of% h₁, h₂]
      rfl)
  have hfst : u ≫ e₂.hom ≫ biprod.fst = (u ≫ biprod.fst) ≫ eJ.hom.app M := by
    simp [e₂]
  have hsnd : u ≫ e₂.hom ≫ biprod.snd = (u ≫ biprod.snd) ≫ eF'.hom.app K' := by
    simp [e₂]
  exact ⟨isIso_homEquiv_symm_of_ofNatIsoRight adjJ eJ adj₁ _ (by rw [← hfst]; exact ha),
    isIso_homEquiv_symm_of_ofNatIsoRight adjF' eF' adj₂ _ (by rw [← hsnd]; exact hb)⟩

end Transport

end MilnorPatching
