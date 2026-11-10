module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.RingTheory.Flat.CategoryTheory
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.Monoidal
public import StacksFrontier.CategoryTheory.Sites.MonoidalColimits
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.Exact

/-!
# Flat étale sheaves of `Λ`-modules

Let `Λ` be a commutative ring and `X` a scheme. A sheaf `F` of `Λ`-modules on the small étale site
of `X` is *flat* when tensoring with it over `Λ`, for the monoidal structure
`Stacks.EtaleCohomology.etaleModuleMonoidalCategory`, preserves monomorphisms. Since tensoring is
right exact, a flat sheaf is one for which tensoring with it is exact, on either side.

This file proves what the generic ladder construction of K-flat resolutions
(`CochainComplex.KFlatBifunctor.exists_kFlatResolution_of_flat`) asks of the class of flat
sheaves: it contains zero, is closed under isomorphisms, binary direct sums and sequential
colimits, every sheaf is a quotient of a flat one, and tensoring with a flat sheaf on either side
carries acyclic complexes to acyclic complexes.

## Main definitions

* `Stacks.EtaleCohomology.IsFlatEtaleModule`: flatness of an étale sheaf of `Λ`-modules.

## Main results

* `ModuleCat.mono_whiskerRight_of_flat`: tensoring with a flat module preserves monomorphisms.
* `Stacks.EtaleCohomology.isFlatEtaleModule_presheafToSheaf_obj`: the sheafification of a
  presheaf of flat modules is flat.
* `Stacks.EtaleCohomology.exists_epi_isFlatEtaleModule`: every étale sheaf of `Λ`-modules is a
  quotient of a flat one, the sheafification of the presheaf of free modules on its sections.
* `Stacks.EtaleCohomology.isFlatEtaleModule_biprod`, `isFlatEtaleModule_colimit`: binary direct
  sums and colimits along shapes with exact colimits of flat sheaves are flat.
* `Stacks.EtaleCohomology.IsFlatEtaleModule.acyclic_map_tensorRight`, `..._tensorLeft`:
  tensoring with a flat sheaf keeps acyclic complexes acyclic.

## Implementation notes

The generating flat sheaves are the sheafifications of the presheaves of free modules on the
sections, `Stacks.LargeModuleUniverse.freeLarge` (Mathlib's `ModuleCat.free` needs the module
universe to be that of `Λ`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w u r

namespace ModuleCat

/-- **Tensoring on the right with a flat module preserves monomorphisms**, for the tensor product
`ModuleCat.liftedModuleMonoidal` of modules in a universe above that of the ring. -/
theorem mono_whiskerRight_of_flat {R : Type r} [CommRing R] {A B : ModuleCat.{max w r} R}
    (f : A ⟶ B) [Mono f] (N : ModuleCat.{max w r} R) [Module.Flat R N] : Mono (f ▷ N) := by
  rw [ModuleCat.mono_iff_injective] at *
  exact Module.Flat.rTensor_preserves_injective_linearMap f.hom ‹_›

end ModuleCat

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

variable {Λ : Type r} [CommRing Λ] {X : Scheme.{u}}

variable (Λ X) in
/-- Sequential colimits of étale sheaves of `Λ`-modules exist. -/
instance etaleModules_hasColimitsOfShape_nat :
    HasColimitsOfShape ℕ (EtaleModules.{u, r} Λ X) :=
  (etaleModules_hasColimitsOfSize_zero.{u, r} Λ X).has_colimits_of_shape ℕ

/-- An étale sheaf of `Λ`-modules is **flat** when tensoring with it preserves monomorphisms.
Tensoring is right exact, so this is the exactness of `- ⊗_Λ F`
(`Stacks.EtaleCohomology.IsFlatEtaleModule.preservesFiniteLimits_tensorRight`); by the braiding it
is also the exactness of `F ⊗_Λ -`. -/
def IsFlatEtaleModule (F : EtaleModules.{u, r} Λ X) : Prop :=
  (tensorRight F).PreservesMonomorphisms

/-- Tensoring on the left with a flat étale sheaf of `Λ`-modules preserves monomorphisms: it is
tensoring on the right, up to the braiding. -/
theorem IsFlatEtaleModule.preservesMonomorphisms_tensorLeft {F : EtaleModules.{u, r} Λ X}
    (hF : IsFlatEtaleModule F) : (tensorLeft F).PreservesMonomorphisms :=
  have : (tensorRight F).PreservesMonomorphisms := hF
  Functor.PreservesMonomorphisms.of_iso (BraidedCategory.tensorLeftIsoTensorRight F).symm

/-- Flatness of étale sheaves of `Λ`-modules is invariant under isomorphism. -/
theorem IsFlatEtaleModule.of_iso {F G : EtaleModules.{u, r} Λ X} (e : F ≅ G)
    (hF : IsFlatEtaleModule F) : IsFlatEtaleModule G :=
  have : (tensorRight F).PreservesMonomorphisms := hF
  Functor.PreservesMonomorphisms.of_iso ((tensoringRight _).mapIso e)

/-- A zero étale sheaf of `Λ`-modules is flat: tensoring with it is zero. -/
theorem isFlatEtaleModule_of_isZero {F : EtaleModules.{u, r} Λ X} (hF : IsZero F) :
    IsFlatEtaleModule F := by
  constructor
  intro A B f _
  have hB : IsZero ((tensorRight F).obj A) := by
    rw [IsZero.iff_id_eq_zero]
    have h : (tensorLeft A).map (𝟙 F) = 0 := by rw [hF.eq_of_src (𝟙 F) 0, Functor.map_zero]
    simpa using h
  exact hB.mono _

/-- Tensoring a monomorphism on the right with a flat étale sheaf gives a monomorphism. -/
private theorem IsFlatEtaleModule.mono_whiskerRight {F : EtaleModules.{u, r} Λ X}
    (hF : IsFlatEtaleModule F) {M N : EtaleModules.{u, r} Λ X} (f : M ⟶ N) [Mono f] :
    Mono (f ▷ F) :=
  have : (tensorRight F).PreservesMonomorphisms := hF
  (tensorRight F).map_mono f

/-- **A direct sum of two flat étale sheaves of `Λ`-modules is flat.** -/
theorem isFlatEtaleModule_biprod {A B : EtaleModules.{u, r} Λ X} (hA : IsFlatEtaleModule A)
    (hB : IsFlatEtaleModule B) : IsFlatEtaleModule (A ⊞ B) := by
  constructor
  intro M N f _
  refine Preadditive.mono_of_cancel_zero _ fun {Z} h hh ↦ ?_
  have key {P : EtaleModules.{u, r} Λ X} (π : A ⊞ B ⟶ P) (_ : Mono (f ▷ P)) :
      h ≫ M ◁ π = 0 := by
    refine (cancel_mono (f ▷ P)).1 ?_
    rw [Category.assoc, whisker_exchange, ← Category.assoc]
    change (h ≫ (tensorRight (A ⊞ B)).map f) ≫ _ = _
    rw [hh, zero_comp, zero_comp]
  have : h = h ≫ M ◁ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) := by
    rw [biprod.total]
    simp
  rw [this, MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add,
    MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp, ← Category.assoc,
    ← Category.assoc, key biprod.fst (hA.mono_whiskerRight f),
    key biprod.snd (hB.mono_whiskerRight f), zero_comp, zero_comp, add_zero]

/-- Tensoring on the left by a fixed étale sheaf of `Λ`-modules preserves colimits. -/
instance preservesColimitsOfSize_etaleModule_tensorLeft (F : EtaleModules.{u, r} Λ X) :
    PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r} (tensorLeft F) := by
  let := isMonoidal_W_smallEtale_module.{u, r} Λ X
  have := preservesColimits_tensorLeft_etaleCoefficients.{u, r} Λ
  exact Sheaf.preservesColimitsOfSize_tensorLeft X.smallEtaleTopology F

/-- Tensoring on the right by a fixed étale sheaf of `Λ`-modules preserves colimits. -/
instance preservesColimitsOfSize_etaleModule_tensorRight (F : EtaleModules.{u, r} Λ X) :
    PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r} (tensorRight F) := by
  let := isMonoidal_W_smallEtale_module.{u, r} Λ X
  have := preservesColimits_tensorRight_etaleCoefficients.{u, r} Λ
  exact Sheaf.preservesColimitsOfSize_tensorRight X.smallEtaleTopology F

/-- Tensoring on the left by a fixed étale sheaf of `Λ`-modules preserves sequential colimits. -/
instance preservesColimitsOfShape_nat_etaleModule_tensorLeft (F : EtaleModules.{u, r} Λ X) :
    PreservesColimitsOfShape ℕ (tensorLeft F) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft F) :=
    preservesColimitsOfSize_shrink.{0, max (u + 1) r, 0, max (u + 1) r} _
  infer_instance

/-- Tensoring on the right by a fixed étale sheaf of `Λ`-modules preserves sequential
colimits. -/
instance preservesColimitsOfShape_nat_etaleModule_tensorRight (F : EtaleModules.{u, r} Λ X) :
    PreservesColimitsOfShape ℕ (tensorRight F) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
    preservesColimitsOfSize_shrink.{0, max (u + 1) r, 0, max (u + 1) r} _
  infer_instance

/-- Tensoring on the right by a fixed étale sheaf of `Λ`-modules preserves finite colimits. -/
instance preservesFiniteColimits_etaleModule_tensorRight (F : EtaleModules.{u, r} Λ X) :
    PreservesFiniteColimits (tensorRight F) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
    preservesColimitsOfSize_shrink.{0, max (u + 1) r, 0, max (u + 1) r} _
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- Tensoring on the left by a fixed étale sheaf of `Λ`-modules preserves finite colimits. -/
instance preservesFiniteColimits_etaleModule_tensorLeft (F : EtaleModules.{u, r} Λ X) :
    PreservesFiniteColimits (tensorLeft F) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft F) :=
    preservesColimitsOfSize_shrink.{0, max (u + 1) r, 0, max (u + 1) r} _
  exact PreservesColimitsOfSize.preservesFiniteColimits _

variable (Λ X) in
/-- **Sequential colimits of étale sheaves of `Λ`-modules are exact.** -/
instance etaleModules_hasExactColimitsOfShape_nat :
    HasExactColimitsOfShape ℕ (EtaleModules.{u, r} Λ X) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{max (u + 1) r} Λ) := AB5OfSize_shrink _
  have : HasExactColimitsOfShape ℕ (ModuleCat.{max (u + 1) r} Λ) := AB5OfSize.ofShape ℕ
  exact Sheaf.hasExactColimitsOfShape _

/-- **A colimit of flat étale sheaves of `Λ`-modules is flat**, along any shape in `Type` whose
colimits exist and are exact: `f ▷ colim D` is the colimit of the monomorphisms `f ▷ D j`. -/
theorem isFlatEtaleModule_colimit {J : Type} [SmallCategory J]
    [HasColimitsOfShape J (EtaleModules.{u, r} Λ X)]
    [HasExactColimitsOfShape J (EtaleModules.{u, r} Λ X)]
    (D : J ⥤ EtaleModules.{u, r} Λ X) (hD : ∀ j, IsFlatEtaleModule (D.obj j)) :
    IsFlatEtaleModule (colimit D) := by
  constructor
  intro M N f _
  have hl (P : EtaleModules.{u, r} Λ X) : PreservesColimitsOfShape J (tensorLeft P) := by
    have : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
      preservesColimitsOfSize_shrink.{0, max (u + 1) r, 0, max (u + 1) r} _
    infer_instance
  let α : D ⋙ tensorLeft M ⟶ D ⋙ tensorLeft N :=
    { app j := f ▷ D.obj j
      naturality _ _ g := by simp [whisker_exchange] }
  have : Mono α := by
    have (j : J) : Mono (α.app j) := (hD j).mono_whiskerRight f
    exact NatTrans.mono_of_mono_app _
  have h : f ▷ colimit D = (preservesColimitIso (tensorLeft M) D).hom ≫ colim.map α ≫
      (preservesColimitIso (tensorLeft N) D).inv := by
    refine (cancel_epi (preservesColimitIso (tensorLeft M) D).inv).1 ?_
    refine colimit.hom_ext fun j ↦ ?_
    simp only [Iso.inv_hom_id_assoc, ι_preservesColimitIso_inv_assoc, colim_map,
      ι_colimMap_assoc, ι_preservesColimitIso_inv]
    simpa [α] using whisker_exchange f (colimit.ι D j)
  change Mono (f ▷ colimit D)
  rw [h]
  infer_instance

/-- **A sequential colimit of flat étale sheaves of `Λ`-modules is flat.** -/
theorem isFlatEtaleModule_colimit_nat (D : ℕ ⥤ EtaleModules.{u, r} Λ X)
    (hD : ∀ j, IsFlatEtaleModule (D.obj j)) : IsFlatEtaleModule (colimit D) :=
  isFlatEtaleModule_colimit D hD

/-- **The sheafification of a presheaf of flat modules is flat**: tensoring with it is the
sheafification of the sectionwise tensor product, and sectionwise tensoring with a flat module
preserves monomorphisms, as does sheafification. -/
theorem isFlatEtaleModule_presheafToSheaf_obj (P : X.Etaleᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ)
    [∀ U, Module.Flat Λ (P.obj U)] :
    IsFlatEtaleModule
      ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj P) := by
  let := isMonoidal_W_smallEtale_module.{u, r} Λ X
  let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
  constructor
  intro A B f _
  -- sectionwise, `f ▷ P` is a monomorphism
  have hP : Mono (f.hom ▷ P) := by
    have (U : X.Etaleᵒᵖ) : Mono ((f.hom ▷ P).app U) := by
      have : Mono (f.hom.app U) := inferInstance
      exact ModuleCat.mono_whiskerRight_of_flat (f.hom.app U) (P.obj U)
    exact NatTrans.mono_of_mono_app _
  -- `L.map f.hom ▷ L P` is `L (f.hom ▷ P)` up to the tensorator of `L`
  have h₁ : Mono (L.map f.hom ▷ L.obj P) := by
    have : L.map f.hom ▷ L.obj P ≫ (Functor.Monoidal.commTensorRight L P).hom.app B.obj =
        (Functor.Monoidal.commTensorRight L P).hom.app A.obj ≫ L.map (f.hom ▷ P) :=
      (Functor.Monoidal.commTensorRight L P).hom.naturality f.hom
    have h : L.map f.hom ▷ L.obj P = (Functor.Monoidal.commTensorRight L P).hom.app A.obj ≫
        L.map (f.hom ▷ P) ≫ (Functor.Monoidal.commTensorRight L P).inv.app B.obj := by
      rw [← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id_app]
      simp
    rw [h]
    infer_instance
  -- and `f` is `L.map f.hom` up to the counit of sheafification
  have hc := (sheafificationAdjunction X.smallEtaleTopology
    (ModuleCat.{max (u + 1) r} Λ)).counit.naturality f
  have h₂ : f ▷ L.obj P = (inv ((sheafificationAdjunction X.smallEtaleTopology
        (ModuleCat.{max (u + 1) r} Λ)).counit.app A) ▷ L.obj P) ≫ (L.map f.hom ▷ L.obj P) ≫
      ((sheafificationAdjunction X.smallEtaleTopology
        (ModuleCat.{max (u + 1) r} Λ)).counit.app B ▷ L.obj P) := by
    rw [← comp_whiskerRight, ← comp_whiskerRight]
    congr 1
    simp only [Functor.comp_map, Functor.id_map] at hc
    rw [IsIso.eq_inv_comp]
    exact hc.symm
  change Mono (f ▷ L.obj P)
  rw [h₂]
  infer_instance

/-- **Every étale sheaf of `Λ`-modules is a quotient of a flat one**: of the sheafification of the
presheaf of free modules on its sections. -/
theorem exists_epi_isFlatEtaleModule (G : EtaleModules.{u, r} Λ X) :
    ∃ (F : EtaleModules.{u, r} Λ X) (p : F ⟶ G), IsFlatEtaleModule F ∧ Epi p := by
  let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
  let P : X.Etaleᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ :=
    G.obj ⋙ forget (ModuleCat.{max (u + 1) r} Λ) ⋙
      Stacks.LargeModuleUniverse.freeLarge.{max (u + 1) r} Λ
  let q : P ⟶ G.obj :=
    { app U := Stacks.LargeModuleUniverse.freeLargeDesc (fun x ↦ x)
      naturality U V g := by
        refine Stacks.LargeModuleUniverse.freeLarge_hom_ext fun x ↦ ?_
        change Stacks.LargeModuleUniverse.freeLargeDesc (M := G.obj.obj V) (fun y ↦ y)
            (Finsupp.mapDomain (G.obj.map g) (Finsupp.single x 1)) =
          G.obj.map g (Stacks.LargeModuleUniverse.freeLargeDesc (M := G.obj.obj U) (fun y ↦ y)
            (Stacks.LargeModuleUniverse.freeLargeMk x))
        rw [Finsupp.mapDomain_single]
        exact (Stacks.LargeModuleUniverse.freeLargeDesc_apply _ _).trans
          (congrArg (G.obj.map g)
            (Stacks.LargeModuleUniverse.freeLargeDesc_apply (M := G.obj.obj U) (fun y ↦ y)
              x).symm) }
  have : Epi q := by
    have (U : X.Etaleᵒᵖ) : Epi (q.app U) := by
      rw [ModuleCat.epi_iff_surjective]
      intro x
      exact ⟨Stacks.LargeModuleUniverse.freeLargeMk x,
        Stacks.LargeModuleUniverse.freeLargeDesc_apply _ x⟩
    exact NatTrans.epi_of_epi_app _
  have (U : X.Etaleᵒᵖ) : Module.Flat Λ (P.obj U) :=
    inferInstanceAs (Module.Flat Λ ((G.obj.obj U) →₀ Λ))
  exact ⟨L.obj P, L.map q ≫ (sheafificationAdjunction _ _).counit.app G,
    isFlatEtaleModule_presheafToSheaf_obj P, inferInstance⟩

/-! ### Exactness -/

/-- **Tensoring on the right with a flat étale sheaf of `Λ`-modules is exact.** -/
theorem IsFlatEtaleModule.preservesFiniteLimits_tensorRight {F : EtaleModules.{u, r} Λ X}
    (hF : IsFlatEtaleModule F) : PreservesFiniteLimits (tensorRight F) := by
  have : (tensorRight F).PreservesMonomorphisms := hF
  exact Stacks.Sites.AbelianLowerShriek.preservesFiniteLimits_of_preservesMonomorphisms _

/-- **Tensoring on the left with a flat étale sheaf of `Λ`-modules is exact.** -/
theorem IsFlatEtaleModule.preservesFiniteLimits_tensorLeft {F : EtaleModules.{u, r} Λ X}
    (hF : IsFlatEtaleModule F) : PreservesFiniteLimits (tensorLeft F) := by
  have : (tensorLeft F).PreservesMonomorphisms := hF.preservesMonomorphisms_tensorLeft
  exact Stacks.Sites.AbelianLowerShriek.preservesFiniteLimits_of_preservesMonomorphisms _

/-- **Tensoring an acyclic complex termwise on the right by a flat étale sheaf of `Λ`-modules
gives an acyclic complex.** -/
theorem IsFlatEtaleModule.acyclic_map_tensorRight {F : EtaleModules.{u, r} Λ X}
    (hF : IsFlatEtaleModule F) {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (EtaleModules.{u, r} Λ X) c} (hK : K.Acyclic) :
    (((tensorRight F).mapHomologicalComplex c).obj K).Acyclic :=
  have := hF.preservesFiniteLimits_tensorRight
  HomologicalComplex.Acyclic.map _ hK

/-- **Tensoring an acyclic complex termwise on the left by a flat étale sheaf of `Λ`-modules
gives an acyclic complex.** -/
theorem IsFlatEtaleModule.acyclic_map_tensorLeft {F : EtaleModules.{u, r} Λ X}
    (hF : IsFlatEtaleModule F) {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (EtaleModules.{u, r} Λ X) c} (hK : K.Acyclic) :
    (((tensorLeft F).mapHomologicalComplex c).obj K).Acyclic :=
  have := hF.preservesFiniteLimits_tensorLeft
  HomologicalComplex.Acyclic.map _ hK

end Stacks.EtaleCohomology

end
