module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSectionsTensor

/-!
# A global presentation of `M ⊗_A 𝒪` on a site with a final object

Let `(C, J)` be a site with a final object `Z`, let `O` be a sheaf of commutative rings on it and
write `A = Γ(C, O)` for its ring of global functions.  For every `A`-module `M` the sheaf of
`O`-modules `M ⊗_A 𝒪` of `Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor` has a global
presentation in the sense of Stacks 03DL(6): it is the cokernel of a map between two coproducts of
copies of the structure sheaf.  In particular it is quasi-coherent on the site.

The point of this file is the universes.  The objects of the site, its morphisms and the rings of
sections of `O` lie in three independent universes `u`, `v` and `r`, and the module `M` and
`M ⊗_A 𝒪` have their sections at `max u v r`, which is where global presentations are taken.
`Stacks.Cohomology.SiteModules.isQuasicoherentOnSite_sectionTensor` asks instead that the rings of
`O` contain the universe of the objects of the site; that fails on the small étale site of an
algebraic space, whose objects lie one universe above its structure rings.  The price is a final
object: the copies of the structure sheaf in a global presentation are its universe lifts, and
morphisms out of such a lift are sections over a final object
(`SheafOfModules.uliftUnitHomEquiv`).  A slice site always has one.

## Main definitions

* `Stacks.Cohomology.SiteModules.freeSectionModule`: the free `A`-module `⨁_I A` on a type `I`.
* `Stacks.Cohomology.SiteModules.sectionTensorFreeTerminalEquiv`: morphisms
  `(⨁_I A) ⊗_A 𝒪 ⟶ N` are families, indexed by `I`, of sections of `N` over the final object.
* `Stacks.Cohomology.SiteModules.sectionTensorFreeCofanInj`: the resulting coprojections from the
  universe lift of the structure sheaf into `(⨁_I A) ⊗_A 𝒪`.

## Main results

* `Stacks.Cohomology.SiteModules.isColimitSectionTensorFreeCofan`: `(⨁_I A) ⊗_A 𝒪` is a
  coproduct of copies of the universe lift of the structure sheaf.
* `Stacks.Cohomology.SiteModules.hasGlobalPresentation_sectionTensor_of_isTerminal`: `M ⊗_A 𝒪`
  has a global presentation.
* `Stacks.Cohomology.SiteModules.isQuasicoherentOnSite_sectionTensor_of_isTerminal`: `M ⊗_A 𝒪`
  is quasi-coherent on the site.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07UZ](https://stacks.math.columbia.edu/tag/07UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  (O : Sheaf J CommRingCat.{r})

/-- The free module `⨁_I A` on a type `I` over the ring `A = Γ(C, O)` of global functions, with
its elements in the universe in which global presentations are taken. -/
abbrev freeSectionModule (I : Type (max u v r)) : ModuleCat.{max u r v} (GlobalFunctionRing O) :=
  ModuleCat.of _ (I →₀ GlobalFunctionRing O)

/-- **The universal property of `⨁_I A`**: an `A`-linear map out of it is a family of elements
of the target indexed by `I`, recovered by evaluating at the standard basis. -/
def freeSectionModuleHomEquiv (I : Type (max u v r))
    (N : ModuleCat.{max u r v} (GlobalFunctionRing O)) :
    (freeSectionModule O I ⟶ N) ≃ (I → N) where
  toFun f i := f.hom (Finsupp.single i 1)
  invFun s := ModuleCat.ofHom (Finsupp.lsum (GlobalFunctionRing O)
    (fun i => LinearMap.toSpanSingleton (GlobalFunctionRing O) N (s i)))
  left_inv f := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun i => LinearMap.ext fun a => ?_)
    change Finsupp.lsum (GlobalFunctionRing O) _ (Finsupp.single i a) = f.hom (Finsupp.single i a)
    rw [Finsupp.lsum_single]
    change a • f.hom (Finsupp.single i 1) = _
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  right_inv s := by
    funext i
    change Finsupp.lsum (GlobalFunctionRing O) _ (Finsupp.single i 1) = s i
    rw [Finsupp.lsum_single]
    exact LinearMap.toSpanSingleton_apply_one _ _ _

variable [HasWeakSheafify J AddCommGrpCat.{max u r v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r v}]
  {O} {Z : C} (hZ : IsTerminal Z)

/-- **Morphisms `(⨁_I A) ⊗_A 𝒪 ⟶ N` are families of sections of `N` over the final object**:
the adjunction between `M ↦ M ⊗_A 𝒪` and global sections, the universal property of `⨁_I A`, and
the identification of global sections with sections over a final object. -/
def sectionTensorFreeTerminalEquiv (I : Type (max u v r))
    (N : SheafOfModules.{max u r v} (ringSheafOfSite O)) :
    ((sectionTensorSheafFunctor.{u, v, r, v} O).obj (freeSectionModule O I) ⟶ N) ≃
      (I → N.val.obj (op Z)) :=
  ((sectionTensorSheafAdjunction.{u, v, r, v} O).homEquiv _ N).trans
    ((freeSectionModuleHomEquiv O I _).trans
      (Equiv.piCongrRight fun _ => N.val.sectionsEquivObjOfIsTerminal hZ))

/-- The family of sections attached to a composite is the image of the family attached to the
first factor. -/
theorem sectionTensorFreeTerminalEquiv_comp (I : Type (max u v r))
    {N N' : SheafOfModules.{max u r v} (ringSheafOfSite O)}
    (φ : (sectionTensorSheafFunctor.{u, v, r, v} O).obj (freeSectionModule O I) ⟶ N)
    (g : N ⟶ N') (i : I) :
    sectionTensorFreeTerminalEquiv hZ I N' (φ ≫ g) i =
      g.val.app (op Z) (sectionTensorFreeTerminalEquiv hZ I N φ i) := by
  change (((sectionTensorSheafAdjunction.{u, v, r, v} O).homEquiv _ N' (φ ≫ g)).hom
    (Finsupp.single i 1)).val (op Z) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The coprojection of the `i`-th copy of the universe lift of the structure sheaf into
`(⨁_I A) ⊗_A 𝒪`: the morphism attached to the image of the `i`-th basis vector. -/
def sectionTensorFreeCofanInj (I : Type (max u v r)) (i : I) :
    SheafOfModules.uliftForPresentation.{u, v, r, r, max u v r}
        (SheafOfModules.unit (ringSheafOfSite O)) ⟶
      (sectionTensorSheafFunctor.{u, v, r, v} O).obj (freeSectionModule O I) :=
  SheafOfModules.fromUliftUnit.{u, v, r, max u v r} hZ
    (sectionTensorFreeTerminalEquiv hZ I _ (𝟙 _) i)

/-- Composing a coprojection with a morphism out of `(⨁_I A) ⊗_A 𝒪` gives the morphism attached
to the corresponding section. -/
theorem sectionTensorFreeCofanInj_comp (I : Type (max u v r)) (i : I)
    {N : SheafOfModules.{max u r v} (ringSheafOfSite O)}
    (φ : (sectionTensorSheafFunctor.{u, v, r, v} O).obj (freeSectionModule O I) ⟶ N) :
    sectionTensorFreeCofanInj hZ I i ≫ φ =
      SheafOfModules.fromUliftUnit.{u, v, r, max u v r} hZ
        (sectionTensorFreeTerminalEquiv hZ I N φ i) := by
  apply (SheafOfModules.uliftUnitHomEquiv.{u, v, r, max u v r} hZ N).injective
  rw [SheafOfModules.uliftUnitHomEquiv_comp]
  refine ((congrArg (φ.val.app (op Z))
    ((SheafOfModules.uliftUnitHomEquiv.{u, v, r, max u v r} hZ _).apply_symm_apply _)).trans
      ?_).trans ((SheafOfModules.uliftUnitHomEquiv.{u, v, r, max u v r} hZ N).apply_symm_apply
        _).symm
  rw [← sectionTensorFreeTerminalEquiv_comp, Category.id_comp]

/-- **`(⨁_I A) ⊗_A 𝒪` is a coproduct of copies of the universe lift of the structure sheaf.** -/
def isColimitSectionTensorFreeCofan (I : Type (max u v r)) :
    IsColimit (Cofan.mk ((sectionTensorSheafFunctor.{u, v, r, v} O).obj (freeSectionModule O I))
      (sectionTensorFreeCofanInj hZ I)) :=
  Cofan.IsColimit.mk _
    (fun s => (sectionTensorFreeTerminalEquiv hZ I s.pt).symm
      fun i => SheafOfModules.uliftUnitHomEquiv.{u, v, r, max u v r} hZ s.pt (s.inj i))
    (fun s i => by
      change sectionTensorFreeCofanInj hZ I i ≫ _ = _
      rw [sectionTensorFreeCofanInj_comp, Equiv.apply_symm_apply]
      exact (SheafOfModules.uliftUnitHomEquiv.{u, v, r, max u v r} hZ s.pt).symm_apply_apply _)
    (fun s m hm => by
      apply (sectionTensorFreeTerminalEquiv hZ I s.pt).injective
      rw [Equiv.apply_symm_apply]
      funext i
      rw [← hm i]
      change _ = SheafOfModules.uliftUnitHomEquiv.{u, v, r, max u v r} hZ s.pt
        (sectionTensorFreeCofanInj hZ I i ≫ m)
      rw [sectionTensorFreeCofanInj_comp]
      exact ((SheafOfModules.uliftUnitHomEquiv.{u, v, r, max u v r} hZ s.pt).apply_symm_apply
        _).symm)

/-! ### The global presentation -/

/-- The canonical surjection `⨁_M A ⟶ M` from the free module on the elements of `M`. -/
def freeSectionModuleCover (M : ModuleCat.{max u r v} (GlobalFunctionRing O)) :
    freeSectionModule O (ULift.{max u v r} M) ⟶ M :=
  ModuleCat.ofHom (Finsupp.linearCombination (GlobalFunctionRing O) (fun m => m.down))

/-- The free module on the kernel of the canonical surjection, mapping into its source. -/
def freeSectionModuleRelations (M : ModuleCat.{max u r v} (GlobalFunctionRing O)) :
    freeSectionModule O (ULift.{max u v r} (LinearMap.ker (freeSectionModuleCover M).hom)) ⟶
      freeSectionModule O (ULift.{max u v r} M) :=
  ModuleCat.ofHom (Finsupp.linearCombination (GlobalFunctionRing O) (fun k => k.down.1))

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The relations map composed with the canonical surjection onto `M` is zero. -/
theorem freeSectionModuleRelations_comp_cover (M : ModuleCat.{max u r v} (GlobalFunctionRing O)) :
    freeSectionModuleRelations M ≫ freeSectionModuleCover M = 0 := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun k => LinearMap.ext fun a => ?_)
  have h : (freeSectionModuleRelations M).hom (Finsupp.single k a) = a • k.down.1 :=
    Finsupp.linearCombination_single _ _ _
  change (freeSectionModuleCover M).hom ((freeSectionModuleRelations M).hom
    (Finsupp.single k a)) = 0
  rw [h, map_smul, LinearMap.mem_ker.1 k.down.2, smul_zero]

/-- **A module over the global functions is the cokernel of a map of free modules.** -/
def isColimitFreeSectionModuleCover (M : ModuleCat.{max u r v} (GlobalFunctionRing O)) :
    IsColimit (CokernelCofork.ofπ (freeSectionModuleCover M)
      (freeSectionModuleRelations_comp_cover M)) := by
  have hepi : Epi (freeSectionModuleCover M) :=
    (ModuleCat.epi_iff_surjective _).2 fun m => ⟨Finsupp.single (ULift.up m) 1, by
      change Finsupp.linearCombination (GlobalFunctionRing O) _ (Finsupp.single _ 1) = m
      rw [Finsupp.linearCombination_single, one_smul]⟩
  have hexact : (ShortComplex.mk (freeSectionModuleRelations M) (freeSectionModuleCover M)
      (freeSectionModuleRelations_comp_cover M)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    refine ⟨Finsupp.single (ULift.up ⟨x, hx⟩) 1, ?_⟩
    change Finsupp.linearCombination (GlobalFunctionRing O) _ (Finsupp.single _ 1) = x
    rw [Finsupp.linearCombination_single, one_smul]
  exact hexact.gIsCokernel

include hZ in
/-- **`M ⊗_A 𝒪` has a global presentation**, on a site with a final object, with no condition on
the universes of the site and of the structure sheaf.  The functor `M ↦ M ⊗_A 𝒪` is a left
adjoint, so it carries the cokernel presenting `M` by free modules to a cokernel, and it carries
a free module to a coproduct of copies of the universe lift of the structure sheaf by
`Stacks.Cohomology.SiteModules.isColimitSectionTensorFreeCofan`. -/
theorem hasGlobalPresentation_sectionTensor_of_isTerminal
    (M : ModuleCat.{max u r v} (GlobalFunctionRing O)) :
    ((sectionTensorSheafFunctor.{u, v, r, v} O).obj M).HasGlobalPresentation := by
  let F := sectionTensorSheafFunctor.{u, v, r, v} O
  have hadd : F.Additive := (sectionTensorSheafAdjunction.{u, v, r, v} O).left_adjoint_additive
  have hsize : PreservesColimitsOfSize.{0, 0} F :=
    (sectionTensorSheafAdjunction.{u, v, r, v} O).leftAdjoint_preservesColimits
  have : PreservesColimit (parallelPair (freeSectionModuleRelations M) 0) F :=
    PreservesColimitsOfShape.preservesColimit (self := hsize.preservesColimitsOfShape)
  let e := Stacks.SheafOfModules.uliftForPresentationIsoSelf.{u, v, r, v} (F.obj M)
  have hc := isColimitCoforkMapOfIsColimit' F (freeSectionModuleRelations_comp_cover M)
    (isColimitFreeSectionModuleCover M)
  refine ⟨_, _, _, _, sectionTensorFreeCofanInj hZ _, sectionTensorFreeCofanInj hZ _,
    ⟨isColimitSectionTensorFreeCofan hZ _⟩, ⟨isColimitSectionTensorFreeCofan hZ _⟩,
    F.map (freeSectionModuleRelations M), F.map (freeSectionModuleCover M) ≫ e.hom, ?_, ?_⟩
  · rw [← Category.assoc, ← F.map_comp, freeSectionModuleRelations_comp_cover, F.map_zero,
      zero_comp]
  · refine ⟨Cofork.isColimitOfIsos _ hc _ (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_⟩
    · simp
    · simp
    · exact Category.id_comp _

include hZ in
/-- **`M ⊗_A 𝒪` is quasi-coherent** on a site with a final object, for every module `M` over the
global functions, with no condition on the universes of the site and of the structure sheaf. -/
theorem isQuasicoherentOnSite_sectionTensor_of_isTerminal
    (M : ModuleCat.{max u r v} (GlobalFunctionRing O)) :
    ((sectionTensorSheafFunctor.{u, v, r, v} O).obj M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_hasGlobalPresentation _
    (hasGlobalPresentation_sectionTensor_of_isTerminal hZ M)

end Stacks.Cohomology.SiteModules
