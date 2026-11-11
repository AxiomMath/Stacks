module

public import StacksFrontier.CategoryTheory.Sites.Modules.SectionTensorPresentation

/-!
# The global sections of `M ⊗_A 𝒪`

Let `(C, J)` be a site, let `O` be a sheaf of commutative rings on it, write `A = Γ(C, O)` for the
ring of global functions and `M ⊗_A 𝒪` for the sheaf of `O`-modules attached to an `A`-module `M`
by `Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor`.

`Stacks.Cohomology.SiteModules.isIso_sectionTensorSheafUnit_of_free` reduces the equality
`Γ(C, M ⊗_A 𝒪) = M` for an arbitrary `A`-module `M` to the case of a free `A`-module, granted that
the global-sections functor is right exact.  This file discharges the free case, which is the
computation `Γ(C, ⨁_{i ∈ I} 𝒪) = ⨁_{i ∈ I} A` of the source.

The free sheaf of `O`-modules `𝒪^{(I)}` is the coproduct of `I` copies of `𝒪`, so a functor out of
sheaves of modules which preserves that coproduct carries the tautological cofan on `𝒪^{(I)}` to a
coproduct cofan.  The free module `⨁_I A = (I →₀ A)` carries a cofan of `I` copies of
`Γ(C, 𝒪) = A` which is a coproduct cofan because `Finsupp.lsum` is its universal property, and the
comparison map of the two cofans sends the standard basis vector at `i` to the tautological global
section of `𝒪^{(I)}` at `i`.  Hence that comparison is invertible as soon as global sections
commute with the coproduct of `I` copies of `𝒪`, which is the hypothesis carried by the results
below and is exactly the direct-sum computation the source cites.

The canonical map `M ⟶ Γ(C, M ⊗_A 𝒪)` at a free module factors as the comparison above through
`Γ` of a morphism `(⨁_I A) ⊗_A 𝒪 ⟶ 𝒪^{(I)}`, and that morphism is invertible because both of its
sides corepresent the functor `F ↦ (I → Γ(C, F))`: a morphism between two objects corepresenting
the same functor which matches the identity under the two bijections is an isomorphism.

## Main definitions

* `Stacks.Cohomology.SiteModules.globalSectionsUnitIso`: the identification `A = Γ(C, 𝒪)` of the
  global functions with the global sections of the structure sheaf read as a module over itself.
* `Stacks.Cohomology.SiteModules.freeGlobalModuleCofanLeg` and
  `isColimitFreeGlobalModuleCofan`: the free module `⨁_I A` is the coproduct of `I` copies of
  `Γ(C, 𝒪)`.
* `Stacks.Cohomology.SiteModules.freeSectionsHom`: the comparison `⨁_I A ⟶ Γ(C, 𝒪^{(I)})`,
  sending the standard basis vector at `i` to the tautological section at `i`.
* `Stacks.Cohomology.SiteModules.sectionTensorFreeHom`: the canonical morphism
  `(⨁_I A) ⊗_A 𝒪 ⟶ 𝒪^{(I)}`, namely the one corresponding to the tautological sections.

## Main results

* `Stacks.Cohomology.SiteModules.isIso_freeSectionsHom`: `Γ(C, ⨁_{i ∈ I} 𝒪) = ⨁_{i ∈ I} A` when
  global sections commute with that coproduct.
* `Stacks.Cohomology.SiteModules.isIso_sectionTensorSheafUnit_free`: the free-module case of
  `Γ(C, M ⊗_A 𝒪) = M`, under the hypothesis on global sections below.  Stacks 07UZ itself, in
  Situation 07UY, is
  `AlgebraicGeometry.Space.CohomologyVanishingSituation.isIso_unit_tensorSheaf` and
  `AlgebraicGeometry.Space.CohomologyVanishingSituation.globalSectionsTensorLinearEquiv`.

## Implementation notes

The universes follow `Stacks.Cohomology.SiteModules.SectionTensorPresentation`: the sheaf of rings
lies in `CommRingCat.{max u r}` and the tensor functor is instantiated at free module universe
`u`, which is the universe in which `SheafOfModules.free` lives.

The hypothesis on global sections is `PreservesColimit (Discrete.functor (fun _ : I => 𝒪))`, that
is, preservation of the single coproduct actually used, rather than preservation of all coproducts
of shape `I`.  This is the weakest form under which the free case goes through and it is the
direct-sum computation of the source, whose content is that the cohomology of the site vanishes
enough for global sections to commute with direct sums; nothing of it is proved here.

`globalSectionsUnitIso` is given by its two maps rather than by a `LinearEquiv`: the carrier of
`Γ(C, 𝒪)` is the compatible families of sections of the sheaf of rings, which is the carrier of
`A` itself, so both maps are the identity on the underlying families and all four laws are
`rfl`.

The morphism `sectionTensorFreeHom` is built from the corepresentation rather than taken to be
`Stacks.Cohomology.SiteModules.sectionTensorFreeIso`.  Its defining equation
`sectionTensorFreeHomEquiv_sectionTensorFreeHom` is then available by `Equiv.apply_symm_apply`,
whereas the value of the comparison isomorphism of two corepresenting objects under the
bijections is not part of the public interface of
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso`.

## References

* [Stacks Project, Tag 07UZ](https://stacks.math.columbia.edu/tag/07UZ)
* [Stacks Project, Tag 0718](https://stacks.math.columbia.edu/tag/0718)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u v r

namespace Stacks.Cohomology.SiteModules

/-- **A morphism between two objects corepresenting the same functor which matches the identity
under the two bijections is an isomorphism.**  Its inverse is the morphism matching the identity
the other way round, and the two composition laws follow from the naturality of the
bijections. -/
private theorem isIso_of_corepresentableBy {D : Type u₁} [Category.{v₁} D] {F : D ⥤ Type v₁}
    {X X' : D} (e : F.CorepresentableBy X) (e' : F.CorepresentableBy X') (φ : X ⟶ X')
    (hφ : e.homEquiv φ = e'.homEquiv (𝟙 X')) : IsIso φ := by
  refine ⟨e'.homEquiv.symm (e.homEquiv (𝟙 X)), ?_, ?_⟩
  · refine e.homEquiv.injective ?_
    rw [e.homEquiv_comp, hφ, ← e'.homEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]
  · refine e'.homEquiv.injective ?_
    rw [e'.homEquiv_comp, Equiv.apply_symm_apply, ← e.homEquiv_comp, Category.id_comp, hφ]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u r} RingCat.{max u r})]
  [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}]
  (O : Sheaf J CommRingCat.{max u r})

/-- A global function read as a global section of the structure sheaf viewed as a module over
itself: the same compatible family of sections. -/
def globalSectionsUnitHom :
    ModuleCat.of (GlobalFunctionRing O) (GlobalFunctionRing O) ⟶
      (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).obj
        (SheafOfModules.unit (ringSheafOfSite O)) :=
  ModuleCat.ofHom
    { toFun := fun a => (SheafOfModules.unit (ringSheafOfSite O)).val.sectionsMk
        (fun X => a.val X) (fun _ _ f => a.property f)
      map_add' := fun _ _ => by ext; rfl
      map_smul' := fun _ _ => by ext; rfl }

/-- A global section of the structure sheaf viewed as a module over itself, read as a global
function. -/
def globalSectionsUnitInv :
    (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).obj
        (SheafOfModules.unit (ringSheafOfSite O)) ⟶
      ModuleCat.of (GlobalFunctionRing O) (GlobalFunctionRing O) :=
  ModuleCat.ofHom
    { toFun := fun s => ⟨fun X => s.eval X, fun f => s.property f⟩
      map_add' := fun _ _ => by ext; rfl
      map_smul' := fun _ _ => by ext; rfl }

/-- **`Γ(C, 𝒪) = A`**: the global sections of the structure sheaf read as a module over itself are
the global functions. -/
def globalSectionsUnitIso :
    ModuleCat.of (GlobalFunctionRing O) (GlobalFunctionRing O) ≅
      (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).obj
        (SheafOfModules.unit (ringSheafOfSite O)) where
  hom := globalSectionsUnitHom O
  inv := globalSectionsUnitInv O
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

omit [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}] in
/-- The unit global function is the global section of `𝒪` attached to the identity. -/
theorem globalSectionsUnitHom_one :
    (globalSectionsUnitHom O).hom (1 : GlobalFunctionRing O) =
      (SheafOfModules.unit (ringSheafOfSite O)).unitHomEquiv
        (𝟙 (SheafOfModules.unit (ringSheafOfSite O))) := by
  apply Subtype.ext
  funext X
  rfl

/-- The `i`-th inclusion of `Γ(C, 𝒪)` into the free module `⨁_I A`: the global functions read as
the coefficient at `i`. -/
def freeGlobalModuleCofanLeg (I : Type (max u r)) (i : I) :
    (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).obj
        (SheafOfModules.unit (ringSheafOfSite O)) ⟶ freeGlobalModule O I :=
  (globalSectionsUnitIso O).inv ≫ ModuleCat.ofHom (Finsupp.lsingle i)

/-- **The free module `⨁_I A` is the coproduct of `I` copies of `Γ(C, 𝒪)`.**  An `A`-linear map
out of it is a family of elements of the target indexed by `I`, which is
`Stacks.Cohomology.SiteModules.freeGlobalModuleHomEquiv`, and an `A`-linear map out of
`Γ(C, 𝒪) = A` is a single element of the target. -/
def isColimitFreeGlobalModuleCofan (I : Type (max u r)) :
    IsColimit (Cofan.mk (freeGlobalModule O I) (freeGlobalModuleCofanLeg O I)) :=
  Cofan.IsColimit.mk _
    (fun t => (freeGlobalModuleHomEquiv O I t.pt).symm
      (fun i => ((globalSectionsUnitIso O).hom ≫ t.inj i).hom (1 : GlobalFunctionRing O)))
    (fun t i => by
      change freeGlobalModuleCofanLeg O I i ≫ _ = _
      rw [freeGlobalModuleCofanLeg, Category.assoc, Iso.inv_comp_eq]
      refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
      change ((freeGlobalModuleHomEquiv O I t.pt).symm _).hom (Finsupp.lsingle i (1 : _)) = _
      rw [Finsupp.lsingle_apply, freeGlobalModuleHomEquiv_symm_single])
    (fun t m hm => by
      refine (freeGlobalModuleHomEquiv O I t.pt).injective (funext fun i => ?_)
      rw [Equiv.apply_symm_apply]
      have h := congrArg
        (fun (f : (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).obj
            (SheafOfModules.unit (ringSheafOfSite O)) ⟶ t.pt) =>
          f.hom ((globalSectionsUnitHom O).hom (1 : GlobalFunctionRing O))) (hm i)
      change m.hom (Finsupp.single i (1 : GlobalFunctionRing O)) = _
      exact h)

/-- The comparison `⨁_I A ⟶ Γ(C, 𝒪^{(I)})`: the `A`-linear map carrying the standard basis vector
at `i` to the tautological global section of the free sheaf of modules at `i`. -/
def freeSectionsHom (I : Type (max u r)) :
    freeGlobalModule O I ⟶
      (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).obj
        (SheafOfModules.free (R := ringSheafOfSite O) I) :=
  (freeGlobalModuleHomEquiv O I
    ((globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).obj
      (SheafOfModules.free (R := ringSheafOfSite O) I))).symm
    (SheafOfModules.freeSection (R := ringSheafOfSite O) (I := I))

/-- The comparison carries the standard basis vector at `i` to the tautological section at `i`. -/
theorem freeSectionsHom_single (I : Type (max u r)) (i : I) :
    (freeSectionsHom O I).hom (Finsupp.single i (1 : GlobalFunctionRing O)) =
      SheafOfModules.freeSection (R := ringSheafOfSite O) i :=
  freeGlobalModuleHomEquiv_symm_single O I _ _ i

/-- The comparison `⨁_I A ⟶ Γ(C, 𝒪^{(I)})` is a morphism of cofans: it carries the `i`-th
inclusion of `Γ(C, 𝒪)` to the global sections of the `i`-th inclusion of `𝒪`. -/
theorem cofanLeg_comp_freeSectionsHom (I : Type (max u r)) (i : I) :
    freeGlobalModuleCofanLeg O I i ≫ freeSectionsHom O I =
      (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).map
        (SheafOfModules.ιFree (R := ringSheafOfSite O) i) := by
  rw [freeGlobalModuleCofanLeg, Category.assoc, Iso.inv_comp_eq]
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  have hR : ((globalSectionsUnitIso O).hom ≫ (globalSectionsFunctor.{u, v, max u r, max u r}
      (ringSheafOfSite O)).map (SheafOfModules.ιFree (R := ringSheafOfSite O) i)).hom
        (1 : GlobalFunctionRing O) =
      (SheafOfModules.free (R := ringSheafOfSite O) I).unitHomEquiv
        (SheafOfModules.ιFree i) := by
    change SheafOfModules.sectionsMap (SheafOfModules.ιFree (R := ringSheafOfSite O) i)
        ((globalSectionsUnitHom O).hom (1 : GlobalFunctionRing O)) = _
    rw [globalSectionsUnitHom_one, ← SheafOfModules.unitHomEquiv_comp_apply, Category.id_comp]
  have hL : SheafOfModules.freeSection (R := ringSheafOfSite O) (I := I) i =
      (SheafOfModules.free (R := ringSheafOfSite O) I).unitHomEquiv
        (SheafOfModules.ιFree i ≫ 𝟙 _) := rfl
  change (freeSectionsHom O I).hom (Finsupp.lsingle i (1 : GlobalFunctionRing O)) = _
  rw [Finsupp.lsingle_apply, freeSectionsHom_single, hR, hL, Category.comp_id]

/-- **`Γ(C, ⨁_{i ∈ I} 𝒪) = ⨁_{i ∈ I} A`**, granted that the global-sections functor commutes with
the coproduct of `I` copies of the structure sheaf.

Both sides are coproducts of `I` copies of `Γ(C, 𝒪) = A` and the comparison
`Stacks.Cohomology.SiteModules.freeSectionsHom` is a morphism of the two coproduct cofans. -/
theorem isIso_freeSectionsHom (I : Type (max u r))
    (hI : PreservesColimit
      (Discrete.functor (fun _ : I => SheafOfModules.unit (ringSheafOfSite O)))
      (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O))) :
    IsIso (freeSectionsHom O I) := by
  have _hI := hI
  have hmap : IsColimit (Cofan.mk
      ((globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).obj
        (SheafOfModules.free (R := ringSheafOfSite O) I))
      (fun i => (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).map
        (SheafOfModules.ιFree (R := ringSheafOfSite O) i)) :
      Cofan fun _ : I => (globalSectionsFunctor.{u, v, max u r, max u r}
        (ringSheafOfSite O)).obj (SheafOfModules.unit (ringSheafOfSite O))) :=
    isColimitCofanMkObjOfIsColimit _ _ _
      (SheafOfModules.isColimitFreeCofan (R := ringSheafOfSite O) I)
  let f : Cofan.mk _ (freeGlobalModuleCofanLeg O I) ⟶ Cofan.mk _ (fun i =>
      (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).map
        (SheafOfModules.ιFree (R := ringSheafOfSite O) i)) :=
    { hom := freeSectionsHom O I
      w := fun ⟨i⟩ => cofanLeg_comp_freeSectionsHom O I i }
  have := IsColimit.hom_isIso (isColimitFreeGlobalModuleCofan O I) hmap f
  exact (Cocone.forget _).map_isIso f

/-- The canonical morphism `(⨁_I A) ⊗_A 𝒪 ⟶ 𝒪^{(I)}`: the one corresponding, under the
corepresentation
`Stacks.Cohomology.SiteModules.corepresentableBySectionTensorFree`, to the tautological global
sections of the free sheaf of modules. -/
def sectionTensorFreeHom (I : Type (max u r)) :
    (sectionTensorSheafFunctor.{u, v, max u r, u} O).obj (freeGlobalModule O I) ⟶
      SheafOfModules.free (R := ringSheafOfSite O) I :=
  (sectionTensorFreeHomEquiv O I (SheafOfModules.free (R := ringSheafOfSite O) I)).symm
    (SheafOfModules.freeSection (R := ringSheafOfSite O) (I := I))

/-- `sectionTensorFreeHom` spelled out. -/
theorem sectionTensorFreeHom_def (I : Type (max u r)) :
    sectionTensorFreeHom O I =
      (sectionTensorFreeHomEquiv O I (SheafOfModules.free (R := ringSheafOfSite O) I)).symm
        (SheafOfModules.freeSection (R := ringSheafOfSite O) (I := I)) := rfl

/-- The canonical morphism `(⨁_I A) ⊗_A 𝒪 ⟶ 𝒪^{(I)}` corresponds to the tautological global
sections. -/
theorem sectionTensorFreeHomEquiv_sectionTensorFreeHom (I : Type (max u r)) :
    sectionTensorFreeHomEquiv O I (SheafOfModules.free (R := ringSheafOfSite O) I)
        (sectionTensorFreeHom O I) =
      SheafOfModules.freeSection (R := ringSheafOfSite O) (I := I) := by
  rw [sectionTensorFreeHom_def]
  exact Equiv.apply_symm_apply _ _

/-- The corepresentation of indexed global sections by `(⨁_I A) ⊗_A 𝒪` is
`sectionTensorFreeHomEquiv`. -/
theorem corepresentableBySectionTensorFree_homEquiv (I : Type (max u r))
    (F : SheafOfModules.{max u r} (ringSheafOfSite O))
    (f : (sectionTensorSheafFunctor.{u, v, max u r, u} O).obj (freeGlobalModule O I) ⟶ F) :
    (corepresentableBySectionTensorFree O I).homEquiv f = sectionTensorFreeHomEquiv O I F f := rfl

/-- The identity of `𝒪^{(I)}` corresponds to the tautological global sections. -/
theorem corepresentableByFree_homEquiv_id (I : Type (max u r)) :
    (corepresentableByFree O I).homEquiv (𝟙 (SheafOfModules.free (R := ringSheafOfSite O) I)) =
      SheafOfModules.freeSection (R := ringSheafOfSite O) (I := I) := rfl

/-- **The canonical morphism `(⨁_I A) ⊗_A 𝒪 ⟶ 𝒪^{(I)}` is an isomorphism.**  Both sides
corepresent the functor `F ↦ (I → Γ(C, F))` and this morphism matches the identity of `𝒪^{(I)}`
under the two bijections. -/
theorem isIso_sectionTensorFreeHom (I : Type (max u r)) :
    IsIso (sectionTensorFreeHom O I) := by
  apply isIso_of_corepresentableBy (corepresentableBySectionTensorFree O I)
    (corepresentableByFree O I)
  rw [corepresentableBySectionTensorFree_homEquiv, corepresentableByFree_homEquiv_id,
    sectionTensorFreeHomEquiv_sectionTensorFreeHom]

/-- The bijection `sectionTensorFreeHomEquiv` is the adjunction followed by evaluating at the
standard basis. -/
theorem freeGlobalModuleHomEquiv_homEquiv (I : Type (max u r))
    (F : SheafOfModules.{max u r} (ringSheafOfSite O))
    (f : (sectionTensorSheafFunctor.{u, v, max u r, u} O).obj (freeGlobalModule O I) ⟶ F) :
    freeGlobalModuleHomEquiv O I
        ((globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).obj F)
        ((sectionTensorSheafAdjunction.{u, v, max u r, u} O).homEquiv _ F f) =
      sectionTensorFreeHomEquiv O I F f := rfl

/-- The comparison `⨁_I A ⟶ Γ(C, 𝒪^{(I)})` corresponds to the tautological global sections. -/
theorem freeGlobalModuleHomEquiv_freeSectionsHom (I : Type (max u r)) :
    freeGlobalModuleHomEquiv O I
        ((globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).obj
          (SheafOfModules.free (R := ringSheafOfSite O) I)) (freeSectionsHom O I) =
      SheafOfModules.freeSection (R := ringSheafOfSite O) (I := I) :=
  (freeGlobalModuleHomEquiv O I ((globalSectionsFunctor.{u, v, max u r, max u r}
      (ringSheafOfSite O)).obj
    (SheafOfModules.free (R := ringSheafOfSite O) I))).apply_symm_apply
      (SheafOfModules.freeSection (R := ringSheafOfSite O) (I := I))

/-- The canonical map `⨁_I A ⟶ Γ(C, (⨁_I A) ⊗_A 𝒪)` followed by the global sections of
`sectionTensorFreeHom` is the comparison `⨁_I A ⟶ Γ(C, 𝒪^{(I)})`: both correspond to the
tautological global sections. -/
theorem sectionTensorSheafUnit_comp_map_sectionTensorFreeHom (I : Type (max u r)) :
    sectionTensorSheafUnit.{u, v, max u r, u} (freeGlobalModule O I) ≫
        (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).map
          (sectionTensorFreeHom O I) = freeSectionsHom O I := by
  have h := (sectionTensorSheafAdjunction.{u, v, max u r, u} O).homEquiv_unit
    (X := freeGlobalModule O I) (Y := SheafOfModules.free (R := ringSheafOfSite O) I)
    (f := sectionTensorFreeHom O I)
  rw [sectionTensorSheafAdjunction_unit_app] at h
  rw [← h]
  refine (freeGlobalModuleHomEquiv O I _).injective ?_
  rw [freeGlobalModuleHomEquiv_homEquiv, freeGlobalModuleHomEquiv_freeSectionsHom,
    sectionTensorFreeHomEquiv_sectionTensorFreeHom]

/-- **`Γ(C, (⨁_I A) ⊗_A 𝒪) = ⨁_I A`** on a general site, for an index set `I` such that the
global-sections functor commutes with the coproduct of `I` copies of the structure sheaf (the
hypothesis `hI`).  This is the free-module step of the source's proof of Stacks 07UZ; Stacks 07UZ
itself is proved in full, with no such hypothesis, and registered, as
`AlgebraicGeometry.Space.CohomologyVanishingSituation.isIso_unit_tensorSheaf` and
`AlgebraicGeometry.Space.CohomologyVanishingSituation.globalSectionsTensorLinearEquiv`.

The canonical map factors as the comparison `⨁_I A ⟶ Γ(C, 𝒪^{(I)})` through the global sections
of the isomorphism `(⨁_I A) ⊗_A 𝒪 ≅ 𝒪^{(I)}`, and that comparison is invertible because
`Γ(C, ⨁_{i ∈ I} 𝒪) = ⨁_{i ∈ I} A`. -/
theorem isIso_sectionTensorSheafUnit_free (I : Type (max u r))
    (hI : PreservesColimit
      (Discrete.functor (fun _ : I => SheafOfModules.unit (ringSheafOfSite O)))
      (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O))) :
    IsIso (sectionTensorSheafUnit.{u, v, max u r, u} (freeGlobalModule O I)) := by
  have h₁ : IsIso (sectionTensorFreeHom O I) := isIso_sectionTensorFreeHom O I
  have h₂ : IsIso ((globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).map
      (sectionTensorFreeHom O I)) :=
    Functor.map_isIso (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O))
      (sectionTensorFreeHom O I)
  have h₃ : IsIso (sectionTensorSheafUnit.{u, v, max u r, u} (freeGlobalModule O I) ≫
      (globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).map
        (sectionTensorFreeHom O I)) := by
    rw [sectionTensorSheafUnit_comp_map_sectionTensorFreeHom]
    exact isIso_freeSectionsHom O I hI
  exact IsIso.of_isIso_comp_right _
    ((globalSectionsFunctor.{u, v, max u r, max u r} (ringSheafOfSite O)).map
      (sectionTensorFreeHom O I))

end Stacks.Cohomology.SiteModules

end
