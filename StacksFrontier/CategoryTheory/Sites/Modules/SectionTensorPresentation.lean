module

public import StacksFrontier.CategoryTheory.Sites.Modules.FreeTensorStructureSheaf

/-!
# The presentation of `M ⊗_A 𝒪` by free sheaves of modules, and its global sections

Let `(C, J)` be a site, let `O` be a sheaf of commutative rings on it, write `A = Γ(C, O)` for the
ring of global functions and `M ⊗_A 𝒪` for the sheaf of `O`-modules attached to an `A`-module `M`
by `Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor`.

An `A`-module `M` is the cokernel of the map `⨁_{K} A ⟶ ⨁_{M} A` carrying the free module on the
kernel `K` of the canonical surjection `⨁_M A ⟶ M` into the free module on the elements of `M`.
The functor `M ↦ M ⊗_A 𝒪` is a left adjoint, so it preserves that cokernel, and it carries a free
`A`-module to a free sheaf of `O`-modules by
`Stacks.Cohomology.SiteModules.sectionTensorFreeIso`.  Hence `M ⊗_A 𝒪` is the cokernel of a map of
free sheaves of `O`-modules; this is a global presentation, and `M ⊗_A 𝒪` is quasi-coherent for an
arbitrary `A`-module `M`.

The same presentation computes global sections: if the global-sections functor is right exact, and
if the canonical map `M ⟶ Γ(C, M ⊗_A 𝒪)` is invertible for free `A`-modules, then it is invertible
for every `A`-module.  Both rows of the resulting ladder are cokernels — the top because `M` is
presented, the bottom because `M ↦ M ⊗_A 𝒪` preserves all colimits and global sections preserve
this one — and a natural transformation out of the identity functor which is invertible on a
diagram is invertible on a colimit the target functor preserves.

## Main definitions

* `Stacks.Cohomology.SiteModules.freeGlobalModuleCover`: the canonical surjection `⨁_M A ⟶ M`
  from the free module on the elements of `M`, and
  `Stacks.Cohomology.SiteModules.freeGlobalModuleRelations` the free module on its kernel mapping
  into the source.
* `Stacks.Cohomology.SiteModules.sectionTensorPresentationMap`: the map of free sheaves of
  `O`-modules whose cokernel is `M ⊗_A 𝒪`, with
  `Stacks.Cohomology.SiteModules.sectionTensorCokernelIso` the identification of that cokernel.
* `Stacks.Cohomology.SiteModules.sectionTensorPresentation`: the resulting global presentation of
  `M ⊗_A 𝒪`.

## Main results

* `Stacks.Cohomology.SiteModules.isColimitFreeGlobalModuleCover`: an `A`-module is the cokernel of
  the map of free modules above.
* `Stacks.Cohomology.SiteModules.isQuasicoherentOnSite_sectionTensor`: `M ⊗_A 𝒪` is quasi-coherent
  on the site for every module `M` over the global functions.
* The global-sections statement `Γ(C, M ⊗_A 𝒪) = M` of Stacks 07UZ is not proved here; it is
  `AlgebraicGeometry.Space.CohomologyVanishingSituation.globalSectionsTensorLinearEquiv`, with the
  unit form `AlgebraicGeometry.Space.CohomologyVanishingSituation.isIso_unit_tensorSheaf`.

## Implementation notes

The universes follow `Stacks.Cohomology.SiteModules.FreeTensorStructureSheaf`: the sheaf of rings
lies in `CommRingCat.{max u r}` and the tensor functor is instantiated at free module universe
`u`, which is the universe in which `SheafOfModules.free` and `SheafOfModules.Presentation` live.
The index types of the two free modules are the carrier of `M` and the carrier of the kernel of
`freeGlobalModuleCover`, both of which lie in `Type (max u r)` as required.

The functor `M ↦ M ⊗_A 𝒪` is additive because global sections are, which is what
`CategoryTheory.Adjunction.left_adjoint_additive` needs; additivity is used only so that the
cokernel cofork of a map maps to a cokernel cofork, `G.map 0` being zero rather than only
isomorphic to it.

## References

* [Stacks Project, Tag 07UZ](https://stacks.math.columbia.edu/tag/07UZ)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ u v r

namespace Stacks.Cohomology.SiteModules

/-- A natural transformation out of the identity functor which is invertible on a diagram is
invertible at the point of a colimit cocone over that diagram, provided the target functor carries
the cocone to a colimit cocone. -/
private theorem isIso_natTransApp_of_isColimit {D : Type u₁} [Category.{v₁} D] {G : D ⥤ D}
    (η : 𝟭 D ⟶ G) {K : Type u₂} [Category.{v₂} K] {F : K ⥤ D} {c : Cocone F}
    (hc : IsColimit c) (hGc : IsColimit (G.mapCocone c))
    (h : ∀ k, IsIso (η.app (F.obj k))) : IsIso (η.app c.pt) := by
  have : ∀ k, IsIso (η.app (F.obj k)) := h
  let w : F ≅ F ⋙ G :=
    NatIso.ofComponents (fun k => asIso (η.app (F.obj k))) fun f => η.naturality (F.map f)
  have e : η.app c.pt = (hc.coconePointsIsoOfNatIso hGc w).hom := by
    refine hc.hom_ext fun k => ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact η.naturality (c.ι.app k)
  rw [e]
  infer_instance

/-- A natural transformation out of the identity functor which is invertible on the two terms of
a cokernel presentation is invertible on the object presented, provided the target functor carries
the presentation to a cokernel presentation. -/
private theorem isIso_natTransApp_of_isColimitCokernelCofork {D : Type u₁} [Category.{v₁} D]
    [HasZeroMorphisms D] {G : D ⥤ D} (η : 𝟭 D ⟶ G) {A B Z : D} {a : A ⟶ B} {p : B ⟶ Z}
    (hp : a ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hp))
    (hGc : IsColimit (G.mapCocone (CokernelCofork.ofπ p hp)))
    (hA : IsIso (η.app A)) (hB : IsIso (η.app B)) : IsIso (η.app Z) :=
  isIso_natTransApp_of_isColimit η hc hGc fun k => by
    cases k with
    | zero => exact hA
    | one => exact hB

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u r} RingCat.{max u r})]
  [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}]
  (O : Sheaf J CommRingCat.{max u r})

/-- The canonical surjection `⨁_M A ⟶ M` from the free module on the elements of a module over
the global functions, evaluating a finitely supported family of coefficients. -/
def freeGlobalModuleCover (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    freeGlobalModule O M ⟶ M :=
  ModuleCat.ofHom (Finsupp.linearCombination (GlobalFunctionRing O) (fun m : M => m))

omit [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}] in
/-- The canonical surjection carries the standard basis vector at `m` to `m`. -/
@[simp] theorem freeGlobalModuleCover_single (M : ModuleCat.{max u r} (GlobalFunctionRing O))
    (m : M) : (freeGlobalModuleCover O M).hom (Finsupp.single m 1) = m := by
  simp [freeGlobalModuleCover]

omit [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}] in
/-- The free module on the elements of a module covers it. -/
theorem epi_freeGlobalModuleCover (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    Epi (freeGlobalModuleCover O M) :=
  (ModuleCat.epi_iff_surjective _).2 fun m =>
    ⟨Finsupp.single m 1, freeGlobalModuleCover_single O M m⟩

/-- The free module on the kernel of `Stacks.Cohomology.SiteModules.freeGlobalModuleCover`,
mapping into the free module on the elements of `M` by the inclusion of that kernel. -/
def freeGlobalModuleRelations (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    freeGlobalModule O (LinearMap.ker (freeGlobalModuleCover O M).hom) ⟶ freeGlobalModule O M :=
  ModuleCat.ofHom (Finsupp.linearCombination (GlobalFunctionRing O)
    (fun k : LinearMap.ker (freeGlobalModuleCover O M).hom => k.1))

omit [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}] in
/-- The map on relations carries the standard basis vector at a relation to that relation. -/
@[simp] theorem freeGlobalModuleRelations_single
    (M : ModuleCat.{max u r} (GlobalFunctionRing O))
    (k : LinearMap.ker (freeGlobalModuleCover O M).hom) :
    (freeGlobalModuleRelations O M).hom (Finsupp.single k 1) = k.1 := by
  simp [freeGlobalModuleRelations]

omit [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}] in
/-- The relations of the free cover are killed by it. -/
theorem freeGlobalModuleRelations_comp_cover (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    freeGlobalModuleRelations O M ≫ freeGlobalModuleCover O M = 0 := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun k => LinearMap.ext fun a => ?_)
  have h : (freeGlobalModuleRelations O M).hom (Finsupp.single k a) = a • k.1 :=
    Finsupp.linearCombination_single _ _ _
  show (freeGlobalModuleCover O M).hom ((freeGlobalModuleRelations O M).hom
    (Finsupp.single k a)) = 0
  rw [h, map_smul, LinearMap.mem_ker.1 k.2, smul_zero]

omit [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}] in
/-- **A module over the global functions is the cokernel of a map of free modules**, namely of the
free module on the kernel of its free cover into the free module on its elements. -/
def isColimitFreeGlobalModuleCover (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    IsColimit (CokernelCofork.ofπ (freeGlobalModuleCover O M)
      (freeGlobalModuleRelations_comp_cover O M)) := by
  haveI := epi_freeGlobalModuleCover O M
  have hexact : (ShortComplex.mk (freeGlobalModuleRelations O M) (freeGlobalModuleCover O M)
      (freeGlobalModuleRelations_comp_cover O M)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨Finsupp.single ⟨x, hx⟩ 1, freeGlobalModuleRelations_single O M ⟨x, hx⟩⟩
  exact hexact.gIsCokernel

variable [HasSheafify J AddCommGrpCat.{max u r}]

/-- Sheaves of `O`-modules whose sections lie in the universe of the rings of `O` form an abelian
category.  The instance is named here rather than left to instance search, which commits to
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and its enlarged module universe. -/
private instance (priority := high) abelianSectionModuleSheaves :
    Abelian (_root_.SheafOfModules.{max u r} (ringSheafOfSite O)) :=
  _root_.SheafOfModules.instAbelian _

/-- The map of free sheaves of `O`-modules whose cokernel is `M ⊗_A 𝒪`: the map of free modules
presenting `M`, tensored with the structure sheaf and read through
`Stacks.Cohomology.SiteModules.sectionTensorFreeIso`. -/
def sectionTensorPresentationMap (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    SheafOfModules.free (R := ringSheafOfSite O)
        (LinearMap.ker (freeGlobalModuleCover O M).hom) ⟶
      SheafOfModules.free (R := ringSheafOfSite O) M :=
  (sectionTensorFreeIso O _).inv ≫
    (sectionTensorSheafFunctor.{u, v, max u r, u} O).map (freeGlobalModuleRelations O M) ≫
      (sectionTensorFreeIso O _).hom

section Presentation

attribute [-instance] moduleSheavesAbelian

/-- The surjection of the free sheaf of `O`-modules on the elements of `M` onto `M ⊗_A 𝒪`: the
free cover of `M`, tensored with the structure sheaf and read through
`Stacks.Cohomology.SiteModules.sectionTensorFreeIso`. -/
def sectionTensorPresentationπ (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    SheafOfModules.free (R := ringSheafOfSite O) M ⟶
      (sectionTensorSheafFunctor.{u, v, max u r, u} O).obj M :=
  (sectionTensorFreeIso O _).inv ≫
    (sectionTensorSheafFunctor.{u, v, max u r, u} O).map (freeGlobalModuleCover O M)

omit [HasSheafify J AddCommGrpCat.{max u r}] in
/-- The relations of the free presentation of `M ⊗_A 𝒪` are killed by its generators. -/
theorem sectionTensorPresentationMap_comp_π
    (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    sectionTensorPresentationMap O M ≫ sectionTensorPresentationπ O M = 0 := by
  have : (sectionTensorSheafFunctor.{u, v, max u r, u} O).Additive :=
    (sectionTensorSheafAdjunction.{u, v, max u r, u} O).left_adjoint_additive
  rw [sectionTensorPresentationMap, sectionTensorPresentationπ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    freeGlobalModuleRelations_comp_cover, Functor.map_zero, Limits.comp_zero]

/-- **`M ⊗_A 𝒪` is the cokernel of a map of free sheaves of `O`-modules.** The functor
`M ↦ M ⊗_A 𝒪` preserves the cokernel presenting `M`, being a left adjoint, and carries the two
free modules to free sheaves of modules. -/
def isColimitSectionTensorPresentation (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    IsColimit (CokernelCofork.ofπ (sectionTensorPresentationπ O M)
      (sectionTensorPresentationMap_comp_π O M)) := by
  haveI : (sectionTensorSheafFunctor.{u, v, max u r, u} O).Additive :=
    (sectionTensorSheafAdjunction.{u, v, max u r, u} O).left_adjoint_additive
  have hsize : PreservesColimitsOfSize.{0, 0} (sectionTensorSheafFunctor.{u, v, max u r, u} O) :=
    (sectionTensorSheafAdjunction.{u, v, max u r, u} O).leftAdjoint_preservesColimits
  haveI : PreservesColimit (parallelPair (freeGlobalModuleRelations O M) 0)
      (sectionTensorSheafFunctor.{u, v, max u r, u} O) :=
    PreservesColimitsOfShape.preservesColimit (self := hsize.preservesColimitsOfShape)
  refine Cofork.isColimitOfIsos _
    (isColimitCoforkMapOfIsColimit' (sectionTensorSheafFunctor.{u, v, max u r, u} O)
      (freeGlobalModuleRelations_comp_cover O M) (isColimitFreeGlobalModuleCover O M))
    _ (sectionTensorFreeIso O _) (sectionTensorFreeIso O _) (Iso.refl _) ?_ ?_ ?_
  · simp [sectionTensorPresentationMap]
  · simp
  · simp [sectionTensorPresentationπ]

/-- **A global presentation of `M ⊗_A 𝒪`**: the elements of `M` as generators and the kernel of
the free cover of `M` as relations. -/
def sectionTensorPresentation (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    ((sectionTensorSheafFunctor.{u, v, max u r, u} O).obj M).Presentation :=
  _root_.SheafOfModules.presentationOfIsCokernelFree (sectionTensorPresentationMap O M)
    (sectionTensorPresentationπ O M) (sectionTensorPresentationMap_comp_π O M)
    (isColimitSectionTensorPresentation O M)

/-- **`M ⊗_A 𝒪` is quasi-coherent on the site for every module `M` over the global functions.**
It is the cokernel of a map of free sheaves of `O`-modules, which is a global presentation. -/
@[stacks 07UZ "quasi-coherence of the module M ⊗_A 𝒪_X attached to a module over the global \
functions"]
theorem isQuasicoherentOnSite_sectionTensor (M : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    ((sectionTensorSheafFunctor.{u, v, max u r, u} O).obj M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentation (sectionTensorPresentation O M)

end Presentation

end Stacks.Cohomology.SiteModules

end
