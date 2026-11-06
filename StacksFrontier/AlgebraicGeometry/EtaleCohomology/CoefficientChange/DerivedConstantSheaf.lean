module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.DerivedTensor
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.KFlat.BifunctorCoproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.SubcategoryLocalization

/-!
# The derived constant sheaf functor on the small étale site

Let `Λ` be a commutative ring and `X` a scheme.  The constant sheaf functor
`c_X : Mod(Λ) ⥤ Sh(X_étale, Λ)` (the constant presheaf followed by sheafification) is exact, so
it acts on unbounded derived categories without being derived:
`c_X : D(Λ) ⥤ D(X_étale, Λ)`.  This is the functor `M ↦ M̲` through which the projection formula
behind the second diagram of [Stacks, Remark 0GL6] is a statement natural in `M ∈ D(Λ)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleConstantSheafFunctor`: the constant sheaf functor on modules.
* `Stacks.EtaleCohomology.etaleModuleDerivedConstantSheaf`: its action on unbounded derived
  categories, a triangulated functor.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedConstantSheaf_preservesCoproducts`: the derived
  constant sheaf functor commutes with direct sums.
* `Stacks.EtaleCohomology.isFlatEtaleModule_etaleModuleConstantSheaf_obj`: the constant sheaf on
  a flat module is flat.
* `Stacks.EtaleCohomology.kFlat_etaleModuleConstantSheaf_of_isStrictlyLE`: the constant sheaf
  complex on a bounded above complex of flat modules is K-flat.
* `Stacks.EtaleCohomology.exists_quasiIso_kFlat_etaleModuleConstantSheafFunctor`: every complex of
  modules is resolved by one whose constant sheaf complexes are K-flat in both variables, on the
  small étale site of every scheme.
* `Stacks.EtaleCohomology.etaleModuleDerivedTensor_obj_preservesCoproducts`: `K ⊗^L -` commutes
  with direct sums.
* `Stacks.EtaleCohomology.constantSheafKFlatObjects_isLocalization`,
  `Stacks.EtaleCohomology.constantSheafKFlatComplexes_isLocalization`: hence `D(Λ)` is the
  localization of those complexes at the quasi-isomorphisms, in `K(Λ)` and among complexes.

## Implementation notes

Exactness is that of `Functor.const` and of sheafification; the functor is moreover a left
adjoint (sheafification is), so it preserves all colimits of the coefficient size, and direct
sums pass to derived categories because the localization functors preserve them
(Stacks 07D9, `Stacks.Injectives.derivedCategoryQ_preservesCoproducts`) and are essentially
surjective.

## References

* [Stacks Project, Remark 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme CochainComplex.KFlatBifunctor

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- The constant sheaf functor `M ↦ M̲` from `Λ`-modules to étale sheaves of `Λ`-modules on `X`:
the constant presheaf followed by sheafification. -/
abbrev etaleModuleConstantSheafFunctor : ModuleCat.{max (u + 1) r} Λ ⥤ EtaleModules.{u, r} Λ X :=
  constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)

/-- The constant sheaf functor is left exact: so are the constant presheaf and sheafification. -/
instance etaleModuleConstantSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleConstantSheafFunctor.{u, r} Λ X) := by
  dsimp only [etaleModuleConstantSheafFunctor, constantSheaf]
  infer_instance

/-- The constant sheaf functor preserves colimits: so do the constant presheaf and
sheafification, a left adjoint. -/
instance etaleModuleConstantSheaf_preservesColimitsOfSize :
    PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r}
      (etaleModuleConstantSheafFunctor.{u, r} Λ X) := by
  dsimp only [etaleModuleConstantSheafFunctor, constantSheaf]
  infer_instance

/-- The constant sheaf functor is right exact. -/
instance etaleModuleConstantSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleConstantSheafFunctor.{u, r} Λ X) := by
  dsimp only [etaleModuleConstantSheafFunctor, constantSheaf]
  infer_instance

/-- The constant sheaf functor is additive, being left exact. -/
instance etaleModuleConstantSheaf_additive :
    (etaleModuleConstantSheafFunctor.{u, r} Λ X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The derived constant sheaf functor** `c_X : D(Λ) ⥤ D(X_étale, Λ)`: the constant sheaf
functor is exact, so it acts degreewise on complexes and descends to unbounded derived
categories. -/
abbrev etaleModuleDerivedConstantSheaf :
    DerivedCategory (ModuleCat.{max (u + 1) r} Λ) ⥤ DerivedCategory (EtaleModules.{u, r} Λ X) :=
  (etaleModuleConstantSheafFunctor.{u, r} Λ X).mapDerivedCategory

/-- **The derived constant sheaf functor commutes with direct sums.**  On complexes the constant
sheaf functor preserves them degreewise, and the localization functors preserve them (Stacks
07D9) and are essentially surjective. -/
instance etaleModuleDerivedConstantSheaf_preservesCoproducts (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) (etaleModuleDerivedConstantSheaf.{u, r} Λ X) := by
  have : PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ etaleModuleDerivedConstantSheaf.{u, r} Λ X) :=
    preservesColimitsOfShape_of_natIso
      (etaleModuleConstantSheafFunctor.{u, r} Λ X).mapDerivedCategoryFactors.symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q _ I

/-- The constant sheaf on a flat module is flat: it is the sheafification of a presheaf of flat
modules. -/
theorem isFlatEtaleModule_etaleModuleConstantSheaf_obj (M : ModuleCat.{max (u + 1) r} Λ)
    [Module.Flat Λ M] : IsFlatEtaleModule ((etaleModuleConstantSheafFunctor.{u, r} Λ X).obj M) :=
  have : ∀ U : X.Etaleᵒᵖ, Module.Flat Λ (((Functor.const X.Etaleᵒᵖ).obj M).obj U) :=
    fun _ ↦ inferInstanceAs (Module.Flat Λ M)
  isFlatEtaleModule_presheafToSheaf_obj _

/-- **The constant sheaf complex on a bounded above complex of flat modules is K-flat**
(Stacks 06YQ): its terms are flat étale sheaves. -/
theorem kFlat_etaleModuleConstantSheaf_of_isStrictlyLE
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) (b : ℤ) [N.IsStrictlyLE b]
    (hN : ∀ i, Module.Flat Λ (N.X i)) :
    KFlat (etaleModuleTensor.{u, r} Λ X)
      (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N) :=
  kFlat_etaleModule_of_isStrictlyLE Λ X _ b fun i ↦
    have := hN i
    isFlatEtaleModule_etaleModuleConstantSheaf_obj Λ X (N.X i)

/-- The constant sheaf complex on a bounded above complex of flat modules is K-flat in the left
variable (Stacks 06YQ): its terms are flat étale sheaves. -/
theorem kFlatLeft_etaleModuleConstantSheaf_of_isStrictlyLE
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) (b : ℤ) [N.IsStrictlyLE b]
    (hN : ∀ i, Module.Flat Λ (N.X i)) :
    KFlatLeft (etaleModuleTensor.{u, r} Λ X)
      (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N) :=
  kFlatLeft_etaleModule_of_isStrictlyLE Λ X _ b fun i ↦
    have := hN i
    isFlatEtaleModule_etaleModuleConstantSheaf_obj Λ X (N.X i)

/-- **The constant sheaf complex on a sequential colimit of bounded above complexes of flat
modules is K-flat in both variables**: the constant sheaf functor commutes with the colimit,
each term of the sequence goes to a K-flat complex, and K-flatness passes to sequential colimits
(Stacks 06YR). -/
theorem kFlat_etaleModuleConstantSheaf_colimit
    (D : ℕ ⥤ CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ)
    (hle : ∀ n : ℕ, (D.obj n).IsStrictlyLE n)
    (hflat : ∀ (n : ℕ) (i : ℤ), Module.Flat Λ ((D.obj n).X i)) :
    KFlat (etaleModuleTensor.{u, r} Λ X)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (colimit D)) ∧
      KFlatLeft (etaleModuleTensor.{u, r} Λ X)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (colimit D)) := by
  let Φ := (etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)
  have hc : IsColimit (Φ.mapCocone (colimit.cocone D)) :=
    isColimitOfPreserves Φ (colimit.isColimit D)
  have hex : ∀ (E : ℕ ⥤ CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (s : Cocone E),
      IsColimit s → (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic := acyclic_of_isColimit_nat
  have h1 : KFlat (etaleModuleTensor.{u, r} Λ X) (Φ.mapCocone (colimit.cocone D)).pt :=
    kFlat_of_isColimit (etaleModuleTensor.{u, r} Λ X) _ hc (fun _ ↦ inferInstance) hex fun n ↦
      have := hle n
      kFlat_etaleModuleConstantSheaf_of_isStrictlyLE Λ X (D.obj n) n (hflat n)
  have h2 : KFlat (etaleModuleTensor.{u, r} Λ X).flip (Φ.mapCocone (colimit.cocone D)).pt :=
    kFlat_of_isColimit (etaleModuleTensor.{u, r} Λ X).flip _ hc (fun _ ↦ inferInstance) hex
      fun n ↦
        have := hle n
        (kFlatLeft_iff_kFlat_flip _ _).1
          (kFlatLeft_etaleModuleConstantSheaf_of_isStrictlyLE Λ X (D.obj n) n (hflat n))
  exact ⟨h1, (kFlatLeft_iff_kFlat_flip _ _).2 h2⟩

/-- **Every complex of `Λ`-modules is resolved by one whose constant sheaf complexes are K-flat**:
there is a quasi-isomorphism `P ⟶ N` such that, on the small étale site of every scheme `X`, the
constant sheaf complex `P̲` is K-flat in both variables of the tensor product over `Λ`.  The
resolution is the colimit of the ladder of Stacks 06YS by bounded above complexes of projective
modules. -/
theorem exists_quasiIso_kFlat_etaleModuleConstantSheafFunctor
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) (p : P ⟶ N), QuasiIso p ∧
      ∀ X : Scheme.{u},
        KFlat (etaleModuleTensor.{u, r} Λ X)
            (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ∧
          KFlatLeft (etaleModuleTensor.{u, r} Λ X)
            (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) := by
  let : AB5OfSize.{0, 0, max (u + 1) r, max (u + 1) r + 1} AddCommGrpCat.{max (u + 1) r} :=
    AB5OfSize_of_univLE.{0, 0, max (u + 1) r, max (u + 1) r} AddCommGrpCat.{max (u + 1) r}
  let : HasExactColimitsOfShape ℕ (ModuleCat.{max (u + 1) r} Λ) :=
    HasExactColimitsOfShape.domain_of_functor ℕ
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})
  let Pr : ObjectProperty (ModuleCat.{max (u + 1) r} Λ) := fun M ↦ Projective M
  let : Pr.ContainsZero := ⟨⟨ModuleCat.of Λ (Fin 0 → ULift.{max (u + 1) r} Λ),
    ModuleCat.isZero_of_subsingleton _, (inferInstance : Projective _)⟩⟩
  let : Pr.IsClosedUnderIsomorphisms := ⟨fun e h ↦ @Projective.of_iso _ _ _ _ e h⟩
  obtain ⟨D, p, hle, hD, hp, -⟩ := exists_resolution_colimit_of_flat Pr
    (fun M M' hM hM' ↦ by
      change Projective M at hM
      change Projective M' at hM'
      show Projective (M ⊞ M')
      infer_instance)
    (fun M ↦ ⟨Projective.over M, (inferInstance : Projective _), Projective.π M, inferInstance⟩)
    N
  refine ⟨colimit D, p, hp, fun X ↦ kFlat_etaleModuleConstantSheaf_colimit Λ X D hle
    fun n i ↦ ?_⟩
  have : Projective ((D.obj n).X i) := hD n i
  infer_instance

/-- A bounded above complex of flat modules has constant sheaf complexes K-flat in both variables
on every scheme. -/
private theorem forall_kFlat_and_kFlatLeft_etaleModuleConstantSheaf_of_isStrictlyLE
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) (b : ℤ) [N.IsStrictlyLE b]
    (hN : ∀ i, Module.Flat Λ (N.X i)) (X : Scheme.{u}) :
    KFlat (etaleModuleTensor.{u, r} Λ X)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) ∧
      KFlatLeft (etaleModuleTensor.{u, r} Λ X)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) :=
  ⟨kFlat_etaleModuleConstantSheaf_of_isStrictlyLE Λ X N b hN,
    kFlatLeft_etaleModuleConstantSheaf_of_isStrictlyLE Λ X N b hN⟩

/-- The complexes of `Λ`-modules whose constant sheaf complexes are K-flat in both variables of
the tensor product over `Λ` on the small étale site of every scheme, as objects of the homotopy
category. -/
abbrev constantSheafKFlatObjects :
    ObjectProperty (HomotopyCategory (ModuleCat.{max (u + 1) r} Λ) (ComplexShape.up ℤ)) :=
  fun K ↦ ∀ X : Scheme.{u},
    KFlat (etaleModuleTensor.{u, r} Λ X)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.as) ∧
      KFlatLeft (etaleModuleTensor.{u, r} Λ X)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.as)

/-- A bounded above complex of flat modules has K-flat constant sheaf complexes on every scheme
(Stacks 06YQ), so it lies in `constantSheafKFlatObjects`. -/
theorem constantSheafKFlatObjects_of_isStrictlyLE
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) (b : ℤ) [N.IsStrictlyLE b]
    (hN : ∀ i, Module.Flat Λ (N.X i)) :
    constantSheafKFlatObjects.{u, r} Λ ((HomotopyCategory.quotient _ _).obj N) :=
  forall_kFlat_and_kFlatLeft_etaleModuleConstantSheaf_of_isStrictlyLE Λ N b hN

/-- The quasi-isomorphisms between objects of `constantSheafKFlatObjects`. -/
abbrev constantSheafKFlatQuasiIso :
    MorphismProperty (constantSheafKFlatObjects.{u, r} Λ).FullSubcategory :=
  (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).inverseImage
    (constantSheafKFlatObjects.{u, r} Λ).ι

/-- **`D(Λ)` is the localization of the complexes whose constant sheaf complexes are K-flat**:
they resolve every complex (`exists_quasiIso_kFlat_etaleModuleConstantSheafFunctor`), so a natural
transformation of functors on `D(Λ)` may be given on them. -/
instance constantSheafKFlatObjects_isLocalization :
    ((constantSheafKFlatObjects.{u, r} Λ).ι ⋙ DerivedCategory.Qh).IsLocalization
      (constantSheafKFlatQuasiIso.{u, r} Λ) := by
  have : (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (constantSheafKFlatObjects.{u, r} Λ)).HasLeftResolutions := fun K ↦ by
    obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨P, p, hp, hP⟩ := exists_quasiIso_kFlat_etaleModuleConstantSheafFunctor.{u, r} Λ N
    exact ⟨{ X₁ := ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩
             w := (HomotopyCategory.quotient _ _).map p
             hw := (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (constantSheafKFlatObjects.{u, r} Λ)
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (constantSheafKFlatObjects.{u, r} Λ))
    DerivedCategory.Qh

/-- Membership in `constantSheafKFlatObjects` is invariant under isomorphism in `K(Λ)`: the
constant sheaf functor carries it to an isomorphism in the homotopy category of sheaves, and
K-flatness on either side is an intersection of preimages of the acyclic objects. -/
instance constantSheafKFlatObjects_isClosedUnderIsomorphisms :
    (constantSheafKFlatObjects.{u, r} Λ).IsClosedUnderIsomorphisms where
  of_iso {K K'} e hK X := by
    let Φ := (etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomotopyCategory (ComplexShape.up ℤ)
    refine ⟨(kFlatObjects_iff (etaleModuleTensor.{u, r} Λ X) (Φ.obj K')).2 fun G hG ↦ ?_,
      (kFlatObjectsLeft_iff (etaleModuleTensor.{u, r} Λ X) (Φ.obj K')).2 fun G hG ↦ ?_⟩
    · exact (acyclicPreimage (etaleModuleTensor.{u, r} Λ X) G).prop_of_iso (Φ.mapIso e)
        ((kFlatObjects_iff (etaleModuleTensor.{u, r} Λ X) (Φ.obj K)).1 (hK X).1 G hG)
    · exact (acyclicPreimageLeft (etaleModuleTensor.{u, r} Λ X) G).prop_of_iso (Φ.mapIso e)
        ((kFlatObjectsLeft_iff (etaleModuleTensor.{u, r} Λ X) (Φ.obj K)).1 (hK X).2 G hG)

/-- The complexes of `Λ`-modules whose constant sheaf complexes are K-flat in both variables of
the tensor product over `Λ` on the small étale site of every scheme. -/
abbrev constantSheafKFlatComplexes :
    ObjectProperty (CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) :=
  fun N ↦ ∀ X : Scheme.{u},
    KFlat (etaleModuleTensor.{u, r} Λ X)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) ∧
      KFlatLeft (etaleModuleTensor.{u, r} Λ X)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)

/-- The quasi-isomorphisms between objects of `constantSheafKFlatComplexes`. -/
abbrev constantSheafKFlatComplexesQuasiIso :
    MorphismProperty (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory :=
  (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).inverseImage
    (constantSheafKFlatComplexes.{u, r} Λ).ι

/-- A bounded above complex of flat modules has K-flat constant sheaf complexes on every scheme
(Stacks 06YQ), so it lies in `constantSheafKFlatComplexes`. -/
theorem constantSheafKFlatComplexes_of_isStrictlyLE
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) (b : ℤ) [N.IsStrictlyLE b]
    (hN : ∀ i, Module.Flat Λ (N.X i)) :
    constantSheafKFlatComplexes.{u, r} Λ N :=
  forall_kFlat_and_kFlatLeft_etaleModuleConstantSheaf_of_isStrictlyLE Λ N b hN

/-- **`D(Λ)` is the localization of the complexes whose constant sheaf complexes are K-flat**,
at the quasi-isomorphisms between them: the classes of these complexes in `K(Λ)` localize onto
`D(Λ)` (`constantSheafKFlatObjects_isLocalization`), and the complexes localize at their
homotopy equivalences onto their classes. -/
instance constantSheafKFlatComplexes_isLocalization :
    ((constantSheafKFlatComplexes.{u, r} Λ).ι ⋙ DerivedCategory.Q).IsLocalization
      (constantSheafKFlatComplexesQuasiIso.{u, r} Λ) :=
  ObjectProperty.ι_comp_Q_isLocalization (constantSheafKFlatObjects.{u, r} Λ)

/-- **The derived tensor product of étale sheaves of `Λ`-modules commutes with direct sums in
its second variable**: `K ⊗^L -` preserves coproducts, the sheaf tensor product `G ⊗ -` being a
left adjoint and the localization functors preserving coproducts (Stacks 07D9). -/
instance etaleModuleDerivedTensor_obj_preservesCoproducts
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) ((etaleModuleDerivedTensor.{u, r} Λ X).obj K) :=
  letI : IsGrothendieckAbelian.{max (u + 1) r} (EtaleModules.{u, r} Λ X) :=
    etaleModules_isGrothendieckAbelian.{u, r} Λ X
  letI hcol : HasColimitsOfSize.{max (u + 1) r, max (u + 1) r} (EtaleModules.{u, r} Λ X) :=
    IsGrothendieckAbelian.hasColimits _
  letI : HasColimitsOfShape (Discrete I) (EtaleModules.{u, r} Λ X) :=
    hcol.has_colimits_of_shape _
  derivedBifunctor_obj_preservesColimitsOfShape_discrete _ I (fun _ ↦ inferInstance) K

end Stacks.EtaleCohomology

end
