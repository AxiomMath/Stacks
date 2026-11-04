module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDerivedLimit
public import StacksFrontier.Homology.DerivedComplete.MilnorEpiTower

/-!
# The derived global sections on `ℕ` through the Milnor model

Let `R` be a commutative ring, let `O` be the constant sheaf of rings with value `R` on the
natural numbers with the chaotic topology (`Stacks.LiftedNat`), and let `ℬ` be a sheaf of
differential graded `O`-algebras. For a right differential graded `ℬ`-module `M`, the complexes
of sections `M(n)` form a tower of complexes of `R`-modules, and its global sections
`Γ(M) = lim_n M(n)` map to the strict Milnor model of this tower, the mapping cocone of
`1 - shift` on `∏_n M(n)`.

We show that, after composing with the comparison map `Qh(Γ(M)) ⟶ RΓ(M)` of the derived global
sections, this map identifies `RΓ(M)` with the Milnor model: there is an isomorphism `ψ` from
`RΓ(M)` to the class of the Milnor model whose composite with the comparison map is the class of
the augmentation. For a graded injective K-injective module `I` both the comparison map and the
augmentation are invertible (the transitions of the tower of sections of `I` are surjective);
an arbitrary `M` is reduced to this case by a graded injective K-injective resolution, since on a
chaotic site taking sections over a stage preserves quasi-isomorphisms.

## Main definitions

* `Stacks.ChaoticSite.sectionsTowerMap`: the map of towers of complexes of sections induced by a
  map of complexes of sheaves of modules.
* `Stacks.ChaoticSite.milnorAug`: the augmentation `Γ(M) ⟶ Milnor(n ↦ M(n))`.
* `Stacks.ChaoticSite.derivedGlobalSectionsAuxIso`: the identification of the source
  `Qh(K(Γ)(M))` of the comparison map with `Q(Γ(M))`, a component of
  `DerivedCategory.quotientCompQhIso`.

## Main results

* `Stacks.ChaoticSite.quasiIso_sectionsTowerMap_app`: a quasi-isomorphism of complexes of sheaves
  of modules induces a quasi-isomorphism on the sections over every stage.
* `Stacks.ChaoticSite.quasiIso_milnorAug_of_isDGInjective`: for a graded injective K-injective
  module the augmentation is a quasi-isomorphism.
* `Stacks.ChaoticSite.exists_milnorIso`: **`RΓ(M)` is the Milnor model of the tower of sections
  of `M`**, compatibly with the comparison map and the augmentation.

## References

* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
* [Stacks Project, Tag 0GZK](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Tag 091D](https://stacks.math.columbia.edu/tag/091D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Stacks.PresheafOfModules CountableMilnorTower

universe u

namespace Stacks.ChaoticSite

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-! ### Functoriality of the tower of sections -/

/-- The map of towers of complexes of sections induced by a map of complexes of sheaves of
modules: over the stage `n` it is the map of complexes of sections over `n`. -/
def sectionsTowerMap
    {K L : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := LiftedNat.{u}) R)) ℤ}
    (φ : K ⟶ L) : sectionsTower R K ⟶ sectionsTower R L :=
  Functor.whiskerLeft LiftedNat.ofNat.op
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((sectionsFunctor R).mapHomologicalComplex _).map φ))

/-- The components of `sectionsTowerMap` are the maps of sections over the stages. -/
theorem sectionsTowerMap_app_f
    {K L : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := LiftedNat.{u}) R)) ℤ}
    (φ : K ⟶ L) (n : ℕ) (k : ℤ) :
    ((sectionsTowerMap R φ).app (op n)).f k =
      ((sectionsFunctor R).map (φ.f k)).app (op (LiftedNat.ofNat.obj n)) := rfl

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective in
/-- **A quasi-isomorphism of complexes of sheaves of modules induces a quasi-isomorphism on the
complexes of sections over every stage**: on the chaotic site, taking sections over a stage is
exact. -/
theorem quasiIso_sectionsTowerMap_app
    {K L : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := LiftedNat.{u}) R)) ℤ}
    (φ : K ⟶ L) [QuasiIso φ] (n : ℕ) : QuasiIso ((sectionsTowerMap R φ).app (op n)) := by
  let G := sectionsFunctor R ⋙ (evaluation _ (ModuleCat.{u} R)).obj (op (LiftedNat.ofNat.obj n))
  have : G.PreservesHomology := Functor.preservesHomologyOfExact G
  exact (inferInstance : QuasiIso ((G.mapHomologicalComplex _).map φ))

/-! ### The augmentation into the Milnor model -/

section Milnor

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

variable (ℬ : DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := LiftedNat.{u}) R))

/-- **The augmentation of the global sections into the Milnor model** of the tower of complexes
of sections: the map `Γ(M) ⟶ Milnor(n ↦ M(n))` given by the legs of the limit cone. -/
def milnorAug (M : DifferentialGradedModule.{u, u, u} ℬ) :
    (dgGlobalSections R ℬ).obj M ⟶ countableMilnorFunctor.obj (sectionsTower R M.complex) :=
  TowerAugmentation.augmentationMap (TowerAugmentation.ofCone (sectionsTowerCone R M.complex))

/-- The global sections of a homomorphism are compatible with the legs of the limit cones. -/
theorem dgGlobalSections_map_π {M N : DifferentialGradedModule.{u, u, u} ℬ} (f : M ⟶ N)
    (n : ℕ) :
    (dgGlobalSections R ℬ).map f ≫ (sectionsTowerCone R N.complex).π.app (op n) =
      (sectionsTowerCone R M.complex).π.app (op n) ≫
        (sectionsTowerMap R f.toHomologicalComplex).app (op n) := by
  ext k : 1
  exact limMap_π _ _

/-- **Naturality of the augmentation into the Milnor model.** -/
theorem milnorAug_naturality {M N : DifferentialGradedModule.{u, u, u} ℬ} (f : M ⟶ N) :
    (dgGlobalSections R ℬ).map f ≫ milnorAug R ℬ N =
      milnorAug R ℬ M ≫ countableMilnorFunctor.map (sectionsTowerMap R f.toHomologicalComplex) :=
  TowerAugmentation.augmentationMap_naturality
    (TowerAugmentation.ofCone (sectionsTowerCone R M.complex))
    (TowerAugmentation.ofCone (sectionsTowerCone R N.complex)) ((dgGlobalSections R ℬ).map f) _
    (dgGlobalSections_map_π R ℬ f)

/-- **For a graded injective K-injective module the augmentation into the Milnor model is a
quasi-isomorphism**: the transition maps of its tower of sections are surjective. -/
theorem quasiIso_milnorAug_of_isDGInjective {I : DifferentialGradedModule.{u, u, u} ℬ}
    (hI : IsDGInjective I) : QuasiIso (milnorAug R ℬ I) := by
  have := epi_sectionsTower_map R I.complex
    (fun k _ _ h => surjective_sections_map_of_isDGInjective hI k h)
  exact quasiIso_augmentationMap_ofCone _ (isLimitSectionsTowerCone R I.complex)

/-- The source `Qh(K(Γ)(M))` of the comparison map of the derived global sections at a module `M`
is the class `Q(Γ(M))` of the complex of global sections: the component of
`DerivedCategory.quotientCompQhIso` at `Γ(M)`. -/
def derivedGlobalSectionsAuxIso (M : DifferentialGradedModule.{u, u, u} ℬ) :
    (derivedGlobalSectionsAux R ℬ).obj
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj M) ≅
      DerivedCategory.Q.obj ((dgGlobalSections R ℬ).obj M) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app ((dgGlobalSections R ℬ).obj M)

/-- The identification `Qh(K(Γ)(M)) ≅ Q(Γ(M))` is the component of
`DerivedCategory.quotientCompQhIso`. -/
theorem derivedGlobalSectionsAuxIso_hom (M : DifferentialGradedModule.{u, u, u} ℬ) :
    (derivedGlobalSectionsAuxIso R ℬ M).hom =
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app
        ((dgGlobalSections R ℬ).obj M) := rfl

/-- Naturality of the identification `Qh(K(Γ)(M)) ≅ Q(Γ(M))`. -/
theorem derivedGlobalSectionsAuxIso_hom_naturality {M N : DifferentialGradedModule.{u, u, u} ℬ}
    (f : M ⟶ N) :
    (derivedGlobalSectionsAux R ℬ).map
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).map f) ≫
        (derivedGlobalSectionsAuxIso R ℬ N).hom =
      (derivedGlobalSectionsAuxIso R ℬ M).hom ≫
        DerivedCategory.Q.map ((dgGlobalSections R ℬ).map f) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality
    ((dgGlobalSections R ℬ).map f)

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective in
/-- **The derived global sections are the Milnor model of the tower of sections.** For every
right differential graded `ℬ`-module `M` there is an isomorphism `ψ` from `RΓ(M)` to the class
of the Milnor model of the tower `n ↦ M(n)` of complexes of sections, such that the comparison
map `Qh(Γ(M)) ⟶ RΓ(M)` followed by `ψ` is the class of the augmentation `milnorAug`. -/
theorem exists_milnorIso (M : DifferentialGradedModule.{u, u, u} ℬ) :
    ∃ ψ : (derivedGlobalSections R ℬ).obj ((toDerivedCategory.{u, u, u} ℬ).obj
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj M)) ≅
        DerivedCategory.Q.obj (countableMilnorFunctor.obj (sectionsTower R M.complex)),
      (derivedGlobalSectionsUnit R ℬ).app
          ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj M) ≫ ψ.hom =
        (derivedGlobalSectionsAuxIso R ℬ M).hom ≫ DerivedCategory.Q.map (milnorAug R ℬ M) := by
  obtain ⟨I, f, hf, hG, hK⟩ : ∃ (I : DifferentialGradedModule.{u, u, u} ℬ) (f : M ⟶ I),
      QuasiIso f.toHomologicalComplex ∧ GradedInjective I ∧ IsKInjective I :=
    hasKInjectiveResolutions_dg.{u, u, u} (X := constRingedSite LiftedNat.{u} R) ℬ M
  have hI : IsDGInjective I := ⟨hG, hK⟩
  let q := DifferentialGradedModule.HomotopyCategory.quotient ℬ
  let T := sectionsTowerMap R f.toHomologicalComplex
  have hTQ : IsIso (DerivedCategory.Q.map (countableMilnorFunctor.map T)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact map_quasiIso_and_milnor_triangle.1 T (fun n => quasiIso_sectionsTowerMap_app R _ n)
  have hA : IsIso (DerivedCategory.Q.map (milnorAug R ℬ I)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact quasiIso_milnorAug_of_isDGInjective R ℬ hI
  have hβ := isIso_derivedGlobalSectionsUnit_app R ℬ hI
  have hs : IsIso ((toDerivedCategory.{u, u, u} ℬ).map (q.map f)) :=
    Localization.inverts _ (quasiIsomorphisms.{u, u, u} ℬ) (q.map f)
      ((quasiIsomorphisms_quotient_map_iff f).2 hf)
  refine ⟨asIso ((derivedGlobalSections R ℬ).map ((toDerivedCategory.{u, u, u} ℬ).map (q.map f)))
    ≪≫ (asIso ((derivedGlobalSectionsUnit R ℬ).app (q.obj I))).symm
    ≪≫ derivedGlobalSectionsAuxIso R ℬ I
    ≪≫ asIso (DerivedCategory.Q.map (milnorAug R ℬ I))
    ≪≫ (asIso (DerivedCategory.Q.map (countableMilnorFunctor.map T))).symm, ?_⟩
  have h₄ : DerivedCategory.Q.map ((dgGlobalSections R ℬ).map f) ≫
      DerivedCategory.Q.map (milnorAug R ℬ I) ≫
        inv (DerivedCategory.Q.map (countableMilnorFunctor.map T)) =
      DerivedCategory.Q.map (milnorAug R ℬ M) := by
    rw [← Functor.map_comp_assoc, milnorAug_naturality R ℬ f, Functor.map_comp,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv]
  rw [reassoc_of% ((derivedGlobalSectionsUnit R ℬ).naturality (q.map f)).symm]
  simp only [IsIso.hom_inv_id_assoc]
  rw [reassoc_of% derivedGlobalSectionsAuxIso_hom_naturality R ℬ f, h₄]

end Milnor

end Stacks.ChaoticSite
