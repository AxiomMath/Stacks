module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSectionsTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The free module over the global functions tensored with the structure sheaf

Let `(C, J)` be a site, let `O` be a sheaf of commutative rings on it and write `A = Γ(C, O)` for
the ring of global functions.  For a type `I` the free `A`-module `⨁_I A` is carried by the
functor `M ↦ M ⊗_A 𝒪` of
`Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor` to the free sheaf of `O`-modules
`𝒪^{(I)}` on the same index set.  This file proves that identification and draws the
quasi-coherence of `(⨁_I A) ⊗_A 𝒪` from it.

Both sides corepresent the functor sending a sheaf of `O`-modules `F` to the families
`I → Γ(C, F)` of its global sections: for `𝒪^{(I)}` this is `SheafOfModules.freeHomEquiv`, and
for `(⨁_I A) ⊗_A 𝒪` it is the adjunction
`Stacks.Cohomology.SiteModules.sectionTensorSheafAdjunction` composed with the universal property
of a free module.  The isomorphism is the resulting comparison of corepresenting objects.

## Main definitions

* `Stacks.Cohomology.SiteModules.freeGlobalModule`: the free module `⨁_I A` on a type `I` over
  the global functions of `O`, with `freeGlobalModuleHomEquiv` its universal property.
* `Stacks.Cohomology.SiteModules.indexedSectionsFunctor`: the functor sending a sheaf of
  `O`-modules to the families of its global sections indexed by `I`.
* `Stacks.Cohomology.SiteModules.sectionTensorFreeHomEquiv`: the bijection between morphisms
  `(⨁_I A) ⊗_A 𝒪 ⟶ F` and families `I → Γ(C, F)`.
* `Stacks.Cohomology.SiteModules.corepresentableByFree` and
  `corepresentableBySectionTensorFree`: the two corepresentations of that functor.

## Main results

* `Stacks.Cohomology.SiteModules.sectionTensorFreeIso`: the isomorphism
  `(⨁_I A) ⊗_A 𝒪 ≅ 𝒪^{(I)}`.
* `Stacks.Cohomology.SiteModules.sectionTensorFreeHomEquiv_comp` and
  `sectionTensorFreeHomEquiv_naturality`: that bijection is natural in the sheaf of modules.
* `Stacks.Cohomology.SiteModules.isQuasicoherentOnSite_sectionTensorFree`:
  `(⨁_I A) ⊗_A 𝒪` is quasi-coherent on the site.

## Implementation notes

The ring of global functions `A` lies in the universe `max u r`, where `u` is the universe of the
objects of the site and `r` that of the rings of sections of `O`, and
`Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor` lands in sheaves of modules whose
sections lie in `max u r w` for a free module universe `w`.  `SheafOfModules.free`, by contrast,
exists only at module universe equal to the ring universe: `SheafOfModules.unit` is the sheaf of
rings read as a module over itself, so its sections lie in the universe of the rings, and the
coproduct of copies of it lies there too.  The same is true of `SheafOfModules.Presentation` and
of `Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentation`.  Everything here is therefore
stated for a sheaf of rings in `CommRingCat.{max u r}` and the tensor functor instantiated at
free module universe `u`, which puts the module sections at `max u r` as well.  This is an
instantiation of the general construction, not a restriction of it; it is the universe in which
the whole free-and-presented API of sheaves of modules lives.

`freeGlobalModule` is `I →₀ A` rather than a categorical coproduct of copies of `A` so that its
universal property is `Finsupp.lsum`, which places the index type, the ring and the target module
in unrelated universes; the coproduct would have to be formed in `ModuleCat.{max u r} A`, where a
copy of `A` is an object only because the module universe has been made equal to the ring
universe.

The comparison of the two corepresenting objects is `Functor.CorepresentableBy.uniqueUpToIso`,
which builds the isomorphism from the two bijections and their naturality.  The isomorphism is
therefore constructed, not extracted from an existence statement, and both of its inverse laws
come from the bijections.

## References

* [Stacks Project, Tag 07UX](https://stacks.math.columbia.edu/tag/07UX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u r} RingCat.{max u r})]
  [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}]
  (O : Sheaf J CommRingCat.{max u r})

/-- The free module `⨁_I A` on a type `I` over the ring `A = Γ(C, O)` of global functions of a
sheaf of commutative rings, carried by the finitely supported families `I →₀ A`. -/
abbrev freeGlobalModule (I : Type (max u r)) : ModuleCat.{max u r} (GlobalFunctionRing O) :=
  ModuleCat.of _ (I →₀ GlobalFunctionRing O)

/-- **The universal property of `⨁_I A`**: an `A`-linear map out of it is a family of elements
of the target indexed by `I`, recovered by evaluating at the standard basis. -/
def freeGlobalModuleHomEquiv (I : Type (max u r))
    (N : ModuleCat.{max u r} (GlobalFunctionRing O)) :
    (freeGlobalModule O I ⟶ N) ≃ (I → N) where
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

omit [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}] in
/-- The map `⨁_I A ⟶ N` attached to a family of elements, evaluated on a basis vector. -/
@[simp] theorem freeGlobalModuleHomEquiv_symm_single (I : Type (max u r))
    (N : ModuleCat.{max u r} (GlobalFunctionRing O)) (s : I → N) (i : I) :
    ((freeGlobalModuleHomEquiv O I N).symm s).hom (Finsupp.single i 1) = s i :=
  congrFun ((freeGlobalModuleHomEquiv O I N).right_inv s) i

/-- The functor sending a sheaf of `O`-modules to the families of its global sections indexed by
a fixed type `I`. -/
def indexedSectionsFunctor (I : Type (max u r)) :
    SheafOfModules.{max u r} (ringSheafOfSite O) ⥤ Type (max u r) where
  obj F := I → F.sections
  map f := ↾(fun s i => SheafOfModules.sectionsMap f (s i))
  map_id _ := rfl
  map_comp _ _ := rfl

omit [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}] in
/-- The functor of indexed global sections acts on a family by restricting each member. -/
@[simp] theorem indexedSectionsFunctor_map_apply (I : Type (max u r))
    {F G : SheafOfModules.{max u r} (ringSheafOfSite O)} (f : F ⟶ G)
    (s : (indexedSectionsFunctor O I).obj F) (i : I) :
    (indexedSectionsFunctor O I).map f s i = SheafOfModules.sectionsMap f (s i) := rfl

/-- **The free sheaf of `O`-modules on `I` corepresents families of global sections indexed by
`I`.** This is `SheafOfModules.freeHomEquiv` together with its naturality. -/
def corepresentableByFree (I : Type (max u r)) :
    (indexedSectionsFunctor O I).CorepresentableBy
      (SheafOfModules.free (R := ringSheafOfSite O) I) where
  homEquiv {F} := SheafOfModules.freeHomEquiv F
  homEquiv_comp g f := funext fun i => SheafOfModules.freeHomEquiv_comp_apply f g i

/-- The bijection between morphisms `(⨁_I A) ⊗_A 𝒪 ⟶ F` and families of global sections of `F`
indexed by `I`: the adjunction followed by the universal property of `⨁_I A`. -/
@[sga "4 IV 11.3.3" "special case"]
def sectionTensorFreeHomEquiv (I : Type (max u r))
    (F : SheafOfModules.{max u r} (ringSheafOfSite O)) :
    ((sectionTensorSheafFunctor.{u, v, max u r, u} O).obj (freeGlobalModule O I) ⟶ F) ≃
      (indexedSectionsFunctor O I).obj F :=
  ((sectionTensorSheafAdjunction.{u, v, max u r, u} O).homEquiv _ F).trans
    (freeGlobalModuleHomEquiv O I _)

omit [HasWeakSheafify J AddCommGrpCat.{max u r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r}] in
/-- Evaluating at the standard basis commutes with restricting a global section along a morphism
of sheaves of modules. -/
theorem freeGlobalModuleHomEquiv_comp_globalSectionsFunctor_map (I : Type (max u r))
    {F G : SheafOfModules.{max u r} (ringSheafOfSite O)} (g : F ⟶ G)
    (θ : freeGlobalModule O I ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F) (i : I) :
    freeGlobalModuleHomEquiv O I _ (θ ≫ (globalSectionsFunctor (ringSheafOfSite O)).map g) i =
      SheafOfModules.sectionsMap g (freeGlobalModuleHomEquiv O I _ θ i) := rfl

/-- Restricting a family of global sections along a morphism of sheaves of modules corresponds
to postcomposition, so `sectionTensorFreeHomEquiv` is natural. -/
theorem sectionTensorFreeHomEquiv_comp (I : Type (max u r))
    {F G : SheafOfModules.{max u r} (ringSheafOfSite O)} (g : F ⟶ G)
    (f : (sectionTensorSheafFunctor.{u, v, max u r, u} O).obj (freeGlobalModule O I) ⟶ F)
    (i : I) :
    sectionTensorFreeHomEquiv O I G (f ≫ g) i =
      SheafOfModules.sectionsMap g (sectionTensorFreeHomEquiv O I F f i) := by
  change (freeGlobalModuleHomEquiv O I _)
    ((sectionTensorSheafAdjunction.{u, v, max u r, u} O).homEquiv _ G (f ≫ g)) i = _
  rw [(sectionTensorSheafAdjunction.{u, v, max u r, u} O).homEquiv_naturality_right f g]
  exact freeGlobalModuleHomEquiv_comp_globalSectionsFunctor_map O I g _ i

/-- `sectionTensorFreeHomEquiv` is natural in the sheaf of modules, in the form required of a
corepresentation. -/
theorem sectionTensorFreeHomEquiv_naturality (I : Type (max u r))
    {F G : SheafOfModules.{max u r} (ringSheafOfSite O)} (g : F ⟶ G)
    (f : (sectionTensorSheafFunctor.{u, v, max u r, u} O).obj (freeGlobalModule O I) ⟶ F) :
    sectionTensorFreeHomEquiv O I G (f ≫ g) =
      (indexedSectionsFunctor O I).map g (sectionTensorFreeHomEquiv O I F f) := by
  funext i
  rw [indexedSectionsFunctor_map_apply]
  apply sectionTensorFreeHomEquiv_comp

/-- **`(⨁_I A) ⊗_A 𝒪` corepresents families of global sections indexed by `I`.** This is the
adjunction `Stacks.Cohomology.SiteModules.sectionTensorSheafAdjunction` composed with the
universal property of `⨁_I A`. -/
def corepresentableBySectionTensorFree (I : Type (max u r)) :
    (indexedSectionsFunctor O I).CorepresentableBy
      ((sectionTensorSheafFunctor.{u, v, max u r, u} O).obj (freeGlobalModule O I)) where
  homEquiv {F} := sectionTensorFreeHomEquiv O I F
  homEquiv_comp g f := by apply sectionTensorFreeHomEquiv_naturality

/-- **The tensor of a free module over the global functions with the structure sheaf is the free
sheaf of modules on the same index set**: `(⨁_I A) ⊗_A 𝒪 ≅ 𝒪^{(I)}`.

Both sides corepresent the functor `F ↦ (I → Γ(C, F))`, and the isomorphism compares the two
corepresenting objects.  It is a step towards Stacks 07UZ, which is proved in full, and
registered, as
`AlgebraicGeometry.Space.CohomologyVanishingSituation.isIso_unit_tensorSheaf` and
`AlgebraicGeometry.Space.CohomologyVanishingSituation.globalSectionsTensorLinearEquiv`. -/
def sectionTensorFreeIso (I : Type (max u r)) :
    (sectionTensorSheafFunctor.{u, v, max u r, u} O).obj (freeGlobalModule O I) ≅
      SheafOfModules.free (R := ringSheafOfSite O) I :=
  (corepresentableBySectionTensorFree O I).uniqueUpToIso (corepresentableByFree O I)

/-- **`(⨁_I A) ⊗_A 𝒪` is quasi-coherent on the site.** It is the free sheaf of modules on `I` by
`Stacks.Cohomology.SiteModules.sectionTensorFreeIso`, and a free sheaf of modules is presented by
its index type with no relations. -/
theorem isQuasicoherentOnSite_sectionTensorFree [HasSheafify J AddCommGrpCat.{max u r}]
    (I : Type (max u r)) :
    ((sectionTensorSheafFunctor.{u, v, max u r, u} O).obj
      (freeGlobalModule O I)).IsQuasicoherentOnSite :=
  _root_.SheafOfModules.IsQuasicoherentOnSite.of_iso (sectionTensorFreeIso O I).symm
    (Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentation
      (Stacks.SheafOfModules.presentationFree I))

end Stacks.Cohomology.SiteModules
