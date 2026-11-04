module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.RingTheory.MilnorPatching.Relative
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension
public import StacksFrontier.Topology.Maps.Proper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesAPI
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.ConstructibleDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.ProjectionFormulaBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ForgetEtaleModuleStructure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Complexes with constructible cohomology sheaves in the model `EtaleModules`

For a Noetherian ring `Λ` the objects of `D(X_étale, Λ)` with constructible cohomology sheaves
form the triangulated subcategory `D_c(X_étale, Λ)` of Tag 0GK2,
`Stacks.EtaleCohomology.IsConstructibleEtaleComplex`. This file proves stability properties of
it: closure under isomorphisms and under extensions in distinguished triangles, stability under
inverse image (Tag 095G), descent along a surjective morphism of quasi-compact quasi-separated
schemes (Tag 095Q), and the reduction of constructibility on a Noetherian scheme, by Noetherian
induction, to its generic form on every closed subscheme.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleComplex_of_iso`,
  `Stacks.EtaleCohomology.isConstructibleEtaleComplex_obj₂_of_distinguished`: closure properties.
* `Stacks.EtaleCohomology.isConstructibleEtaleComplex_singleFunctor_obj`: a constructible sheaf
  placed in degree zero lies in `D_c`.
* `Stacks.EtaleCohomology.isConstructibleEtaleComplex_etaleModuleDerivedInverseImage`: inverse
  image preserves `D_c`.
* `Stacks.EtaleCohomology.isConstructibleEtaleComplex_of_inverseImage_of_surjective`: `D_c`
  descends along a surjective morphism of quasi-compact quasi-separated schemes.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_forall_exists_opens`: on a Noetherian
  scheme a sheaf of `Λ`-modules is constructible as soon as its inverse image to every nonempty
  closed subscheme is constructible on some nonempty open; and the same for complexes,
  `Stacks.EtaleCohomology.isConstructibleEtaleComplex_of_forall_exists_opens`.

## Implementation notes

The Noetherian induction runs over closed subsets of the underlying space, the statement at a
closed subset `C` being that the inverse image of the sheaf along every closed immersion with
image `C` is constructible; the complement of a nonempty open in a closed subscheme is given the
reduced induced structure (`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`), and the two
pieces are glued by `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_isOpen_isClosed`.

## References

* [Stacks Project, Tag 0GK2](https://stacks.math.columbia.edu/tag/0GK2)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

section General

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- `D_c(X_étale, Λ)` is closed under isomorphisms. -/
theorem isConstructibleEtaleComplex_of_iso {X : Scheme.{u}}
    {K L : DerivedCategory (EtaleModules.{u, r} Λ X)} (e : K ≅ L)
    (hK : IsConstructibleEtaleComplex Λ K) : IsConstructibleEtaleComplex Λ L :=
  fun n ↦ (IsConstructibleEtaleModule Λ).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK n)

/-- **`D_c(X_étale, Λ)` is closed under extensions**: in a distinguished triangle whose first and
third objects have constructible cohomology sheaves, so does the second. -/
theorem isConstructibleEtaleComplex_obj₂_of_distinguished {X : Scheme.{u}}
    (T : Pretriangulated.Triangle (DerivedCategory (EtaleModules.{u, r} Λ X)))
    (hT : T ∈ distTriang _) (h₁ : IsConstructibleEtaleComplex Λ T.obj₁)
    (h₃ : IsConstructibleEtaleComplex Λ T.obj₃) : IsConstructibleEtaleComplex Λ T.obj₂ :=
  DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _
    (WeakSerre.isWeakSerre_of_isWeakSerreClass _) T hT h₁ h₃

/-- A constructible sheaf placed in degree zero has constructible cohomology sheaves. -/
theorem isConstructibleEtaleComplex_singleFunctor_obj {X : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X) (hF : IsConstructibleEtaleModule Λ F) :
    IsConstructibleEtaleComplex Λ
      ((DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F) := by
  intro n
  by_cases hn : n = 0
  · subst hn
    exact (IsConstructibleEtaleModule Λ).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · refine (IsConstructibleEtaleModule Λ).prop_of_isZero ?_
    exact IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology _ _ _ n hn)
      ((DerivedCategory.homologyFunctor _ n).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F) ≪≫
        (DerivedCategory.homologyFunctorFactors _ n).app _)

/-- The cohomology sheaves of an inverse image are the inverse images of the cohomology
sheaves. -/
def etaleModuleDerivedInverseImageHomologyIso {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℤ)
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    (DerivedCategory.homologyFunctor _ n).obj
        ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ g).obj K) ≅
      (etaleModuleInverseImage.{u, r} Λ g).obj ((DerivedCategory.homologyFunctor _ n).obj K) :=
  ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryHomologyIso n).app K

/-- **Inverse image preserves `D_c`** (Tag 095G applied to every cohomology sheaf). -/
@[sga "5 I 1.9" "more general"]
theorem isConstructibleEtaleComplex_etaleModuleDerivedInverseImage {X Y : Scheme.{u}}
    (g : X ⟶ Y) (K : DerivedCategory (EtaleModules.{u, r} Λ Y))
    (hK : IsConstructibleEtaleComplex Λ K) :
    IsConstructibleEtaleComplex Λ ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ g).obj K) :=
  fun n ↦ (IsConstructibleEtaleModule Λ).prop_of_iso
    (etaleModuleDerivedInverseImageHomologyIso Λ g n K).symm
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ g _ (hK n))

/-- Inverse image along a composite is the composite of the inverse images, on objects. -/
def etaleModuleInverseImageCompObjIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : EtaleModules.{u, r} Λ Z) :
    (etaleModuleInverseImage.{u, r} Λ (f ≫ g)).obj F ≅
      (etaleModuleInverseImage.{u, r} Λ f).obj ((etaleModuleInverseImage.{u, r} Λ g).obj F) :=
  (etaleModuleInverseImageCompIso'.{u, r} Λ f g (f ≫ g) rfl).app F

/-- Constructibility of the inverse image along a composite is constructibility of the iterated
inverse image. -/
theorem isConstructibleEtaleModule_inverseImage_comp_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (F : EtaleModules.{u, r} Λ Z) :
    IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ (f ≫ g)).obj F) ↔
      IsConstructibleEtaleModule Λ
        ((etaleModuleInverseImage.{u, r} Λ f).obj ((etaleModuleInverseImage.{u, r} Λ g).obj F)) :=
  (IsConstructibleEtaleModule Λ).prop_iff_of_iso (etaleModuleInverseImageCompObjIso Λ f g F)

/-- Membership in `D_c` of the inverse image along a composite is membership of the iterated
inverse image. -/
theorem isConstructibleEtaleComplex_inverseImage_comp_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (K : DerivedCategory (EtaleModules.{u, r} Λ Z)) :
    IsConstructibleEtaleComplex Λ
        ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ (f ≫ g)).obj K) ↔
      IsConstructibleEtaleComplex Λ ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ f).obj
        ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ g).obj K)) :=
  forall_congr' fun n ↦ (IsConstructibleEtaleModule Λ).prop_iff_of_iso
    (etaleModuleDerivedInverseImageHomologyIso Λ (f ≫ g) n K ≪≫
      etaleModuleInverseImageCompObjIso Λ f g _ ≪≫
      (etaleModuleInverseImage.{u, r} Λ f).mapIso
        (etaleModuleDerivedInverseImageHomologyIso Λ g n K).symm ≪≫
      (etaleModuleDerivedInverseImageHomologyIso Λ f n _).symm)

/-- **Noetherian induction for constructibility.** Let `S` be a Noetherian scheme and `ℱ` a
sheaf of `Λ`-modules on `S_étale`. If for every closed immersion `i : T ⟶ S` with `T` nonempty
there is a nonempty open `U ⊆ T` on which `i⁻¹ ℱ` is constructible, then `ℱ` is constructible. -/
theorem isConstructibleEtaleModule_of_forall_exists_opens {S : Scheme.{u}} [IsNoetherian S]
    (F : EtaleModules.{u, r} Λ S)
    (h : ∀ (T : Scheme.{u}) (i : T ⟶ S) [IsClosedImmersion i], Nonempty T →
      ∃ U : T.Opens, (U : Set T).Nonempty ∧
        IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ (U.ι ≫ i)).obj F)) :
    IsConstructibleEtaleModule Λ F := by
  suffices H : ∀ C : TopologicalSpace.Closeds S, ∀ (T : Scheme.{u}) (i : T ⟶ S)
      [IsClosedImmersion i], Set.range i.base = (C : Set S) →
      IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ i).obj F) from
    (IsConstructibleEtaleModule Λ).prop_of_iso ((etaleModuleInverseImageIdIso Λ S).app F)
      (H ⊤ S (𝟙 S) (by simp))
  intro C
  induction C using WellFoundedLT.induction with
  | ind C ih =>
  intro T i _ hC
  have : IsNoetherian T := isNoetherian_of_isClosedImmersion i
  rcases isEmpty_or_nonempty T with hT | hT
  · refine isConstructibleEtaleModule_of_constructible_immersion_cover Λ _ (I := PEmpty.{1})
      (fun _ ↦ T) (fun e ↦ e.elim) (fun e ↦ e.elim) ?_ (fun e ↦ e.elim)
    exact Set.eq_univ_of_forall fun x ↦ (hT.false x).elim
  obtain ⟨U, hU, hFU⟩ := h T i hT
  let Zc : TopologicalSpace.Closeds T := ⟨(U : Set T)ᶜ, U.isOpen.isClosed_compl⟩
  let Z := (Scheme.IdealSheafData.vanishingIdeal Zc).subscheme
  let ι : Z ⟶ T := (Scheme.IdealSheafData.vanishingIdeal Zc).subschemeι
  have hι : Set.range ι.base = (U : Set T)ᶜ :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  let C' : TopologicalSpace.Closeds S :=
    ⟨i.base '' (U : Set T)ᶜ, i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
  have hmem (y : T) : i.base y ∈ (C : Set S) := hC ▸ ⟨y, rfl⟩
  have hC' : C' < C := by
    refine lt_of_le_of_ne (fun x hx ↦ ?_) fun he ↦ ?_
    · obtain ⟨y, -, rfl⟩ := hx
      exact hmem y
    · obtain ⟨y, hy⟩ := hU
      rw [← he] at hmem
      obtain ⟨y', hy', hyy'⟩ := hmem y
      exact hy' (i.isClosedEmbedding.injective hyy' ▸ hy)
  have hZ := ih C' hC' Z (ι ≫ i) (by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hι]
    rfl)
  refine isConstructibleEtaleModule_of_isOpen_isClosed Λ _ U
    (TopologicalSpace.NoetherianSpace.isCompact _) ι hι ?_
    ((isConstructibleEtaleModule_inverseImage_comp_iff Λ ι i F).1 hZ)
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    (etaleModuleInverseImageCompObjIso Λ U.ι i F ≪≫
      (etaleModuleInverseImageRestrictionIso.{u, r} Λ U.ι).app _) hFU

/-- **Noetherian induction for `D_c`.** Let `S` be a Noetherian scheme and `K` an object of
`D(S_étale, Λ)`. If for every closed immersion `i : T ⟶ S` with `T` nonempty there is a
nonempty open `U ⊆ T` with `(i⁻¹ K)|_U` in `D_c`, then `K` lies in `D_c`. -/
theorem isConstructibleEtaleComplex_of_forall_exists_opens {S : Scheme.{u}} [IsNoetherian S]
    (K : DerivedCategory (EtaleModules.{u, r} Λ S))
    (h : ∀ (T : Scheme.{u}) (i : T ⟶ S) [IsClosedImmersion i], Nonempty T →
      ∃ U : T.Opens, (U : Set T).Nonempty ∧
        IsConstructibleEtaleComplex Λ
          ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ (U.ι ≫ i)).obj K)) :
    IsConstructibleEtaleComplex Λ K := fun n ↦
  isConstructibleEtaleModule_of_forall_exists_opens Λ _ fun T i _ hT ↦ by
    obtain ⟨U, hU, hK⟩ := h T i hT
    exact ⟨U, hU, (IsConstructibleEtaleModule Λ).prop_of_iso
      (etaleModuleDerivedInverseImageHomologyIso Λ (U.ι ≫ i) n K) (hK n)⟩

end General

section Descent

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **`D_c` descends along a surjective morphism of quasi-compact quasi-separated schemes**
(Tag 095Q applied to every cohomology sheaf). -/
theorem isConstructibleEtaleComplex_of_inverseImage_of_surjective {X Y : Scheme.{u}}
    (g : X ⟶ Y) [Surjective g] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (K : DerivedCategory (EtaleModules.{u, u + 1} Λ Y))
    (hK : IsConstructibleEtaleComplex Λ
      ((etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ g).obj K)) :
    IsConstructibleEtaleComplex Λ K := fun n ↦
  isConstructibleEtaleModule_of_inverseImage_of_surjective Λ g _
    ((IsConstructibleEtaleModule Λ).prop_of_iso
      (etaleModuleDerivedInverseImageHomologyIso Λ g n K) (hK n))

end Descent

end Stacks.EtaleCohomology

end
