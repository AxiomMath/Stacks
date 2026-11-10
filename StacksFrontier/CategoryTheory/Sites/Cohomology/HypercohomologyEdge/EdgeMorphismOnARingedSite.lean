module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksCore.Tactic.StacksAttribute

/-!
# The hypercohomology edge morphism on a ringed site

Let `K ∈ D(O)` be a complex of sheaves of modules on a ringed site and `U` an object of the site.
This file constructs the natural edge morphism `H^q(U, K) ⟶ H^0(U, H^q(K))` out of unbounded
derived sections, the morphism in terms of which Stacks 0BKZ is stated, together with the general
comparison machinery it is assembled from.

The construction is in three layers, each stated for an arbitrary left exact additive functor
`F : A ⥤ B` of abelian categories and only specialised to sections at the end.

* On complexes: `F` being left exact, `F` commutes with cycles, so there is a canonical
  comparison `H^q(F K) ⟶ F(H^q K)` (`homologyComparison`), natural in `K`.
* On the homotopy category: that comparison inverts homotopy equivalences, hence descends
  (`homologyComparisonOnHomotopy`).
* On the derived category: if every complex of `A` admits a quasi-isomorphism to a K-injective
  complex, then `RF ⋙ H^q` is again a right derived functor
  (`homologyPostcompose_isRightDerivedFunctor`), so its universal property produces a unique
  natural transformation `RF ⋙ H^q ⟶ H^q ⋙ F` extending the comparison
  (`derivedHomologyComparison`).

## Main definitions

* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparison`: the comparison
  `H^q(F K) ⟶ F(H^q K)` on complexes.
* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison`: the edge
  morphism `RF ⋙ H^q ⟶ H^q ⋙ F` of an
  unbounded right derived functor.
* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections` and
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections`: the functor whose
  unbounded right derived functor is `RΓ(U, -)`, and that derived functor.
* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.hypercohomologyEdge`: the edge morphism
  `H^q(U, K) ⟶ H^0(U, H^q(K))`.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.isIso_cyclesComparison`: the comparison
  on cycles is invertible.
* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison_fac_app`: the
  factorisation that characterises the
  edge morphism.
* `isIso_hypercohomologyEdge_app_of_isKInjective`: the edge morphism is
  invertible at a K-injective complex whose own sections-homology comparison is invertible.

## Implementation notes

Sections are taken as `SheafOfModules.evaluation`, whose additivity is established here by
unfolding it to the composite of the forgetful functor with evaluation of a presheaf of modules; it
does not synthesise through the name.

The site, morphism, ring-sheaf and module universes are independent, and so is the universe of the
Grothendieck abelian structure. `IsGrothendieckAbelian` is an explicit hypothesis, used only to
produce K-injective resolutions through `Stacks.Injectives.kInjectiveResolutionFunctor`.

Unlike the source, the existence of K-injective resolutions is carried as an explicit
hypothesis `hA` on the general lemmas rather than decided by cases inside the definition of the
edge morphism: the definition is then the canonical comparison unconditionally, instead of
agreeing with it only where resolutions happen to exist.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vA uA vB uB

namespace Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

section Complexes

/-- The comparison `Z^q(F K) ⟶ F(Z^q K)` on cycles. -/
public noncomputable def cyclesComparison (K : CochainComplex A ℤ) (q : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).cycles q ⟶
      F.obj (K.cycles q) :=
  (KernelFork.isLimitMapConeEquiv
      (KernelFork.ofι (K.iCycles q) (K.iCycles_d q (q + 1))) F
      (isLimitOfPreserves F (K.cyclesIsKernel q (q + 1) (by simp)))).lift
    (KernelFork.ofι (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles q)
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles_d q (q + 1)))

/-- `F` applied to the inclusion of cycles is a monomorphism. -/
public lemma mono_map_iCycles (K : CochainComplex A ℤ) (q : ℤ) :
    Mono (F.map (K.iCycles q)) :=
  Fork.IsLimit.mono
    (KernelFork.isLimitMapConeEquiv
      (KernelFork.ofι (K.iCycles q) (K.iCycles_d q (q + 1))) F
      (isLimitOfPreserves F (K.cyclesIsKernel q (q + 1) (by simp))))

/-- The cycles comparison followed by `F` applied to the inclusion of cycles is the inclusion of
the cycles of `F K`. -/
@[reassoc]
public lemma cyclesComparison_comp_map_iCycles (K : CochainComplex A ℤ) (q : ℤ) :
    cyclesComparison F K q ≫ F.map (K.iCycles q) =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles q :=
  (KernelFork.isLimitMapConeEquiv
      (KernelFork.ofι (K.iCycles q) (K.iCycles_d q (q + 1))) F
      (isLimitOfPreserves F (K.cyclesIsKernel q (q + 1) (by simp)))).fac
    (KernelFork.ofι (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles q)
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles_d q (q + 1)))
    WalkingParallelPair.zero

/-- The map `F(Z^q K) ⟶ Z^q(F K)` which an additive functor supplies with no exactness
hypothesis; it is inverse to `cyclesComparison`. -/
public noncomputable def cyclesComparisonInv (K : CochainComplex A ℤ) (q : ℤ) :
    F.obj (K.cycles q) ⟶ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).cycles q :=
  ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).liftCycles
    (F.map (K.iCycles q)) (q + 1) (by simp)
    (by rw [show ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).d q (q + 1) =
        F.map (K.d q (q + 1)) from rfl, ← F.map_comp, K.iCycles_d, F.map_zero])

/-- The cycles comparison is an isomorphism, `F` being left exact. -/
public instance isIso_cyclesComparison (K : CochainComplex A ℤ) (q : ℤ) :
    IsIso (cyclesComparison F K q) := by
  have := mono_map_iCycles F K q
  refine ⟨cyclesComparisonInv F K q, ?_, ?_⟩
  · apply (cancel_mono
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles q)).1
    rw [Category.assoc, cyclesComparisonInv, HomologicalComplex.liftCycles_i,
      cyclesComparison_comp_map_iCycles, Category.id_comp]
  · apply (cancel_mono (F.map (K.iCycles q))).1
    rw [Category.assoc, cyclesComparison_comp_map_iCycles, cyclesComparisonInv,
      HomologicalComplex.liftCycles_i, Category.id_comp]

/-- The cycles comparison is natural. -/
@[reassoc]
public lemma cyclesComparison_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :
    HomologicalComplex.cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) q ≫
        cyclesComparison F L q =
      cyclesComparison F K q ≫ F.map (HomologicalComplex.cyclesMap f q) := by
  have := mono_map_iCycles F L q
  apply (cancel_mono (F.map (L.iCycles q))).1
  rw [Category.assoc, cyclesComparison_comp_map_iCycles, HomologicalComplex.cyclesMap_i,
    Category.assoc, ← F.map_comp, HomologicalComplex.cyclesMap_i, F.map_comp,
    cyclesComparison_comp_map_iCycles_assoc]
  rfl

/-- The comparison `H^q(F K) ⟶ F(H^q K)`, together with its defining factorisation through
the projection from cycles. -/
public noncomputable def homologyComparisonData (K : CochainComplex A ℤ) (q : ℤ) :
    { e : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology q ⟶
        F.obj (K.homology q) //
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q ≫ e =
        cyclesComparison F K q ≫ F.map (K.homologyπ q) } := by
  have := mono_map_iCycles F K q
  have he : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).toCycles (q - 1) q ≫
      cyclesComparison F K q = F.map (K.toCycles (q - 1) q) := by
    apply (cancel_mono (F.map (K.iCycles q))).1
    rw [Category.assoc, cyclesComparison_comp_map_iCycles, ← F.map_comp, K.toCycles_i]
    exact ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).toCycles_i (q - 1) q
  refine CokernelCofork.IsColimit.desc'
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyIsCokernel (q - 1) q (by simp))
    (cyclesComparison F K q ≫ F.map (K.homologyπ q)) ?_
  rw [← Category.assoc, he, ← F.map_comp, K.toCycles_comp_homologyπ, F.map_zero]

/-- The comparison `H^q(F K) ⟶ F(H^q K)` for a left exact additive functor `F`. -/
public noncomputable def homologyComparison (K : CochainComplex A ℤ) (q : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology q ⟶
      F.obj (K.homology q) :=
  (homologyComparisonData F K q).1

/-- The projection from cycles followed by the homology comparison equals the cycles comparison
followed by `F` applied to the projection from cycles. -/
@[reassoc]
public lemma homologyπ_comp_homologyComparison (K : CochainComplex A ℤ) (q : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q ≫
        homologyComparison F K q =
      cyclesComparison F K q ≫ F.map (K.homologyπ q) :=
  (homologyComparisonData F K q).2

/-- The homology comparison is natural. -/
@[reassoc]
public lemma homologyComparison_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : ℤ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) q ≫
        homologyComparison F L q =
      homologyComparison F K q ≫ F.map (HomologicalComplex.homologyMap f q) := by
  apply (cancel_epi (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q)).1
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    homologyπ_comp_homologyComparison, ← Category.assoc, cyclesComparison_naturality,
    Category.assoc, ← F.map_comp, ← HomologicalComplex.homologyπ_naturality, F.map_comp,
    homologyπ_comp_homologyComparison_assoc]

/-! ### Naturality in the functor

`cyclesComparison_naturality` and `homologyComparison_naturality` are naturality in the
**complex**, with the functor fixed. The lemmas below are naturality in the **functor**, along a
natural transformation `α : F ⟶ G` of two left exact additive functors, with the complex fixed. -/

/-- **The cycles comparison is natural in the functor.** For left exact additive functors
`F, G : A ⥤ B`, a natural transformation `α : F ⟶ G`, a cochain complex `K` in `A` and a degree
`q`, the square

> `Z^q(F K) ⟶ F(Z^q K) ⟶ G(Z^q K)` versus `Z^q(F K) ⟶ Z^q(G K) ⟶ G(Z^q K)`

commutes, the vertical map being the one `α` induces on complexes. -/
@[reassoc]
public lemma cyclesComparison_naturality_natTrans {G : A ⥤ B} [G.Additive]
    [PreservesFiniteLimits G] (α : F ⟶ G) (K : CochainComplex A ℤ) (q : ℤ) :
    cyclesComparison F K q ≫ α.app (K.cycles q) =
      HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) q ≫
        cyclesComparison G K q := by
  have := mono_map_iCycles G K q
  apply (cancel_mono (G.map (K.iCycles q))).1
  rw [Category.assoc, Category.assoc, cyclesComparison_comp_map_iCycles, ← α.naturality,
    cyclesComparison_comp_map_iCycles_assoc, HomologicalComplex.cyclesMap_i]
  rfl

/-- **The homology comparison is natural in the functor.** For left exact additive functors
`F, G : A ⥤ B`, a natural transformation `α : F ⟶ G`, a cochain complex `K` in `A` and a degree
`q`, the square

> `H^q(F K) ⟶ F(H^q K) ⟶ G(H^q K)` versus `H^q(F K) ⟶ H^q(G K) ⟶ G(H^q K)`

commutes, the vertical map being the one `α` induces on complexes. -/
@[reassoc]
public lemma homologyComparison_naturality_natTrans {G : A ⥤ B} [G.Additive]
    [PreservesFiniteLimits G] (α : F ⟶ G) (K : CochainComplex A ℤ) (q : ℤ) :
    homologyComparison F K q ≫ α.app (K.homology q) =
      HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) q ≫
        homologyComparison G K q := by
  apply (cancel_epi (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q)).1
  rw [← Category.assoc, homologyπ_comp_homologyComparison, Category.assoc, α.naturality,
    ← Category.assoc, cyclesComparison_naturality_natTrans F α K q, Category.assoc,
    ← homologyπ_comp_homologyComparison, ← Category.assoc, Category.assoc,
    HomologicalComplex.homologyπ_naturality_assoc]

/-- The homology comparison as a natural transformation of functors on cochain complexes. -/
public noncomputable def homologyComparisonNatTrans (q : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q ⟶
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙ F where
  app K := homologyComparison F K q
  naturality _ _ f := homologyComparison_naturality F f q

/-- **`homologyComparisonNatTrans` is natural in the functor**, as an identity of natural
transformations of functors on cochain complexes. -/
public lemma homologyComparisonNatTrans_naturality_natTrans {G : A ⥤ B} [G.Additive]
    [PreservesFiniteLimits G] (α : F ⟶ G) (q : ℤ) :
    homologyComparisonNatTrans F q ≫
        Functor.whiskerLeft (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q) α =
      Functor.whiskerRight (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))
          (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q) ≫
        homologyComparisonNatTrans G q :=
  NatTrans.ext (funext fun K => homologyComparison_naturality_natTrans F α K q)

end Complexes

section Homotopy

/-- The homology comparison descends to the homotopy category. -/
public noncomputable def homologyComparisonOnHomotopy (q : ℤ) :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) q ⟶
      HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) q ⋙ F := by
  let c := ComplexShape.up ℤ
  let QA := HomotopyCategory.quotient A c
  let QB := HomotopyCategory.quotient B c
  let hB := HomotopyCategory.homologyFunctor B c q
  let Fcomp := F.mapHomologicalComplex c
  let Fhom := F.mapHomotopyCategory c
  let eL : QA ⋙ HomotopyCategory.homologyFunctor A c q ⋙ F ≅
      HomologicalComplex.homologyFunctor A c q ⋙ F :=
    Functor.isoWhiskerRight (HomotopyCategory.homologyFunctorFactors A c q) F
  let eR : QA ⋙ Fhom ⋙ hB ≅ Fcomp ⋙ HomologicalComplex.homologyFunctor B c q :=
    (Functor.associator QA Fhom hB).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomotopyCategoryFactors F c) hB ≪≫
      Functor.associator Fcomp QB hB ≪≫
      Functor.isoWhiskerLeft Fcomp (HomotopyCategory.homologyFunctorFactors B c q)
  exact Localization.liftNatTrans QA (HomologicalComplex.homotopyEquivalences A c)
    (QA ⋙ Fhom ⋙ hB) (QA ⋙ HomotopyCategory.homologyFunctor A c q ⋙ F)
    (Fhom ⋙ hB) (HomotopyCategory.homologyFunctor A c q ⋙ F)
    (eR.hom ≫ homologyComparisonNatTrans F q ≫ eL.inv)

/-- **The descended homology comparison is natural in the functor.** For left exact additive
functors `F, G : A ⥤ B`, a natural transformation `α : F ⟶ G` and a degree `q`, the comparison on
the homotopy category commutes with `α` and with the transformation `α` induces on the two
functors between homotopy categories. -/
@[reassoc]
public lemma homologyComparisonOnHomotopy_naturality_natTrans {G : A ⥤ B} [G.Additive]
    [PreservesFiniteLimits G] (α : F ⟶ G) (q : ℤ) :
    homologyComparisonOnHomotopy F q ≫
        Functor.whiskerLeft (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) q) α =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ))
          (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) q) ≫
        homologyComparisonOnHomotopy G q := by
  apply Localization.natTrans_ext (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
  intro K
  have hsq : (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K =
      (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) := by
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hnatalpha := α.naturality
    ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q).inv.app K)
  simp only [Functor.comp_obj] at hnatalpha
  have hdeg := congr_app (homologyComparisonNatTrans_naturality_natTrans F α q) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hdeg
  have hfac := ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) q).hom.naturality
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K)).symm
  simp only [Functor.comp_map] at hfac
  rw [homologyComparisonOnHomotopy, homologyComparisonOnHomotopy]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Localization.liftNatTrans_app, Localization.Lifting.compLeft, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id, Iso.trans_hom, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_inv, Category.assoc]
  rw [hnatalpha, ← Category.assoc ((homologyComparisonNatTrans F q).app K), hdeg]
  simp only [Category.assoc]
  rw [← Category.assoc ((HomotopyCategory.homologyFunctorFactors B
    (ComplexShape.up ℤ) q).hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)), hfac]
  simp only [Category.assoc]
  rw [← Category.assoc ((HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) q).map
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K)),
    ← Functor.map_comp, ← hsq, Functor.map_comp]
  simp only [Category.assoc]

/-- The descended comparison is invertible at (the image of) a cochain complex whose homology
comparison is invertible. -/
public lemma isIso_homologyComparisonOnHomotopy_app (K : CochainComplex A ℤ) (q : ℤ)
    [IsIso (homologyComparison F K q)] :
    IsIso ((homologyComparisonOnHomotopy F q).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
  have : IsIso ((homologyComparisonNatTrans F q).app K) :=
    inferInstanceAs (IsIso (homologyComparison F K q))
  rw [homologyComparisonOnHomotopy, Localization.liftNatTrans_app]
  simp only [NatTrans.comp_app]
  infer_instance

end Homotopy

section Derived

variable [HasDerivedCategory A] [HasDerivedCategory B]

/-- Postcomposing a right derived functor with a homology functor again gives a right derived
functor, provided every complex admits a quasi-isomorphism to a K-injective complex. -/
public theorem homologyPostcompose_isRightDerivedFunctor
    (G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory B)
    (R : DerivedCategory A ⥤ DerivedCategory B) (α : G ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (q : ℤ) :
    (R ⋙ DerivedCategory.homologyFunctor B q).IsRightDerivedFunctor
      (Functor.whiskerRight α (DerivedCategory.homologyFunctor B q) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  let c := ComplexShape.up ℤ
  let QA : HomotopyCategory A c ⥤ DerivedCategory A := DerivedCategory.Qh
  let Q := HomotopyCategory.quotient A c
  let W := HomotopyCategory.quasiIso A c
  let H := DerivedCategory.homologyFunctor B q
  let G' := G ⋙ H
  have hpt :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective G' hA
  have : G'.HasPointwiseRightDerivedFunctor W := hpt.1
  have : G'.HasRightDerivedFunctor W := inferInstance
  let R' := G'.totalRightDerived QA W
  let β := G'.totalRightDerivedUnit QA W
  let α' := Functor.whiskerRight α H ≫ (Functor.associator _ _ _).hom
  let τ := R'.rightDerivedDesc β W (R ⋙ H) α'
  have hτ : ∀ X, IsIso (τ.app X) := by
    intro X
    rw [← NatTrans.isIso_app_iff_of_iso τ (QA.objObjPreimageIso X)]
    obtain ⟨K, hK⟩ := HomotopyCategory.quotient_obj_surjective (QA.objPreimage X)
    rw [← hK]
    obtain ⟨I, f, hI, hf⟩ := hA K
    have hinv : IsIso (QA.map (Q.map f)) :=
      Localization.inverts QA W _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf)
    rw [NatTrans.isIso_app_iff_of_iso τ (asIso (QA.map (Q.map f)))]
    have hβ : IsIso (β.app (Q.obj I)) :=
      hpt.2 (D := DerivedCategory A) (L := QA) R' β I hI
    have hα : IsIso (α.app (Q.obj I)) :=
      (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
        G hA).2 (D := DerivedCategory A) (L := QA) R α I hI
    have hα' : IsIso (α'.app (Q.obj I)) := by
      dsimp [α']
      infer_instance
    have hfac : β.app (Q.obj I) ≫ τ.app (QA.obj (Q.obj I)) = α'.app (Q.obj I) := by
      simpa [τ] using R'.rightDerived_fac_app β W (R ⋙ H) α' (Q.obj I)
    exact IsIso.of_isIso_fac_left hfac
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (RF := R') (α := β) (W := W) (G := R ⋙ H) (β := α')).2 (NatIso.isIso_of_isIso_app τ)

/-- The homology comparison, transported to the source of the universal property of the
unbounded right derived functor. -/
public noncomputable def homotopyHomologyComparisonToDerived (q : ℤ) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        DerivedCategory.homologyFunctor B q ⟶
      DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor A q ⋙ F := by
  let c := ComplexShape.up ℤ
  let Fh := F.mapHomotopyCategory c
  let HA := DerivedCategory.homologyFunctor A q
  let HB := DerivedCategory.homologyFunctor B q
  let QA : HomotopyCategory A c ⥤ DerivedCategory A := DerivedCategory.Qh
  let QB : HomotopyCategory B c ⥤ DerivedCategory B := DerivedCategory.Qh
  let eSource : (Fh ⋙ QB) ⋙ HB ≅ Fh ⋙ HomotopyCategory.homologyFunctor B c q :=
    Functor.associator Fh QB HB ≪≫
      Functor.isoWhiskerLeft Fh (DerivedCategory.homologyFunctorFactorsh B q)
  let eTarget : (QA ⋙ HA) ⋙ F ≅ HomotopyCategory.homologyFunctor A c q ⋙ F :=
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactorsh A q) F
  exact eSource.hom ≫ homologyComparisonOnHomotopy F q ≫ eTarget.inv ≫
    (Functor.associator QA HA F).hom

/-- **The hypercohomology edge morphism** `H^q(RF K) ⟶ F(H^q K)` of an unbounded right derived
functor: the unique natural transformation out of `RF ⋙ H^q`, as a right derived functor of
`K ↦ H^q(F K)`, extending the homology comparison on the homotopy category. -/
public noncomputable def derivedHomologyComparison
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (q : ℤ) :
    R ⋙ DerivedCategory.homologyFunctor B q ⟶ DerivedCategory.homologyFunctor A q ⋙ F :=
  have := homologyPostcompose_isRightDerivedFunctor _ R α hA q
  (R ⋙ DerivedCategory.homologyFunctor B q).rightDerivedDesc
    (Functor.whiskerRight α (DerivedCategory.homologyFunctor B q) ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (DerivedCategory.homologyFunctor A q ⋙ F) (homotopyHomologyComparisonToDerived F q)

/-- The defining factorisation of `derivedHomologyComparison`. -/
public lemma derivedHomologyComparison_fac_app
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (q : ℤ)
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (DerivedCategory.homologyFunctor B q).map (α.app K) ≫
        (derivedHomologyComparison F R α hA q).app (DerivedCategory.Qh.obj K) =
      (homotopyHomologyComparisonToDerived F q).app K := by
  have := homologyPostcompose_isRightDerivedFunctor _ R α hA q
  simpa [derivedHomologyComparison] using
    (R ⋙ DerivedCategory.homologyFunctor B q).rightDerived_fac_app
      (Functor.whiskerRight α (DerivedCategory.homologyFunctor B q) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctor A q ⋙ F) (homotopyHomologyComparisonToDerived F q) K

/-! ### Naturality of the edge morphism in the functor

The lemmas below are naturality in the **functor**, along a natural transformation `α : F ⟶ G` of
two left exact additive functors, of `homotopyHomologyComparisonToDerived` and of the edge morphism
`derivedHomologyComparison`. -/

/-- **The comparison transported to the source of the derived functor's universal property is
natural in the functor.** -/
@[reassoc]
public lemma homotopyHomologyComparisonToDerived_naturality_natTrans {G : A ⥤ B} [G.Additive]
    [PreservesFiniteLimits G] (α : F ⟶ G) (q : ℤ) :
    homotopyHomologyComparisonToDerived F q ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerLeft (DerivedCategory.homologyFunctor A q) α) =
      Functor.whiskerRight (Functor.whiskerRight
          (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)) DerivedCategory.Qh)
          (DerivedCategory.homologyFunctor B q) ≫
        homotopyHomologyComparisonToDerived G q := by
  ext K
  have hnatalpha := α.naturality ((DerivedCategory.homologyFunctorFactorsh A q).inv.app K)
  simp only [Functor.comp_obj] at hnatalpha
  have hhom := congr_app (homologyComparisonOnHomotopy_naturality_natTrans F α q) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hhom
  have hfach := ((DerivedCategory.homologyFunctorFactorsh B q).hom.naturality
    ((NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app K)).symm
  simp only [Functor.comp_map] at hfach
  rw [homotopyHomologyComparisonToDerived, homotopyHomologyComparisonToDerived]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Category.id_comp, Category.comp_id, Category.assoc]
  rw [hnatalpha, ← Category.assoc ((homologyComparisonOnHomotopy F q).app K), hhom]
  simp only [Category.assoc]
  rw [← Category.assoc ((DerivedCategory.homologyFunctorFactorsh B q).hom.app
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)), hfach]
  simp only [Category.assoc]

/-- **The hypercohomology edge morphism is natural in the functor.** Let `F, G : A ⥤ B` be left
exact additive functors, `α : F ⟶ G` a natural transformation, `RF` and `RG` right derived
functors of `F` and `G` with units `uF` and `uG`, and `Rα : RF ⟶ RG` a transformation compatible
with `α` on the homotopy category, in the sense of `hRα`. Then the square

> `H^q(RF K) ⟶ F(H^q K) ⟶ G(H^q K)` versus `H^q(RF K) ⟶ H^q(RG K) ⟶ G(H^q K)`

commutes: the edge morphism of `RF` followed by `α` is `Rα` followed by the edge morphism of
`RG`. -/
public lemma derivedHomologyComparison_naturality_natTrans {G : A ⥤ B} [G.Additive]
    [PreservesFiniteLimits G] (α : F ⟶ G)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (uF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor uF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (uG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    [RG.IsRightDerivedFunctor uG (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (Rα : RF ⟶ RG)
    (hRα : Functor.whiskerRight (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ uG =
        uF ≫ Functor.whiskerLeft DerivedCategory.Qh Rα)
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (q : ℤ) :
    derivedHomologyComparison F RF uF hA q ≫
        Functor.whiskerLeft (DerivedCategory.homologyFunctor A q) α =
      Functor.whiskerRight Rα (DerivedCategory.homologyFunctor B q) ≫
        derivedHomologyComparison G RG uG hA q := by
  have hRD := homologyPostcompose_isRightDerivedFunctor _ RF uF hA q
  apply (RF ⋙ DerivedCategory.homologyFunctor B q).rightDerived_ext
    (Functor.whiskerRight uF (DerivedCategory.homologyFunctor B q) ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  ext K
  have facF := derivedHomologyComparison_fac_app F RF uF hA q K
  have facG := derivedHomologyComparison_fac_app G RG uG hA q K
  have hRaK := congr_app hRα K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hRaK
  have hD0 := congr_app (homotopyHomologyComparisonToDerived_naturality_natTrans F α q) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hD0
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Category.assoc]
  rw [← Category.assoc ((DerivedCategory.homologyFunctor B q).map (uF.app K)), facF, hD0,
    ← Category.assoc ((DerivedCategory.homologyFunctor B q).map (uF.app K)),
    ← Functor.map_comp, ← hRaK, Functor.map_comp, Category.assoc, facG]

/-- The comparison transported to the derived level is invertible at (the image of) a complex
whose own homology comparison is invertible. -/
public lemma isIso_homotopyHomologyComparisonToDerived_app (K : CochainComplex A ℤ) (q : ℤ)
    [IsIso (homologyComparison F K q)] :
    IsIso ((homotopyHomologyComparisonToDerived F q).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
  have := isIso_homologyComparisonOnHomotopy_app F K q
  rw [homotopyHomologyComparisonToDerived]
  simp only [NatTrans.comp_app]
  infer_instance

/-- **The edge morphism is invertible at a K-injective complex whose homology comparison is
invertible.** -/
public lemma isIso_derivedHomologyComparison_app_of_isKInjective
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (q : ℤ)
    (I : CochainComplex A ℤ) (hI : I.IsKInjective) [IsIso (homologyComparison F I q)] :
    IsIso ((derivedHomologyComparison F R α hA q).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) := by
  have hα : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hA).2
      (D := DerivedCategory A) (L := DerivedCategory.Qh) R α I hI
  have htarget := isIso_homotopyHomologyComparisonToDerived_app F I q
  have hfac := derivedHomologyComparison_fac_app F R α hA q
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)
  exact IsIso.of_isIso_fac_left hfac

end Derived

section SiteSections

open Opposite

universe u v wRing wModule g

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

attribute [local instance] HasDerivedCategory.standard

/-- Evaluation of a sheaf of modules at an object of the site is additive. -/
public instance evaluation_additive (O : Sheaf J RingCat.{wRing}) (X : Cᵒᵖ) :
    (SheafOfModules.evaluation.{wModule} O X).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- Every complex of sheaves of modules over a Grothendieck abelian category of modules admits
a quasi-isomorphism to a K-injective complex. -/
public lemma exists_quasiIso_isKInjective_sheafOfModules (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]
    (K : CochainComplex (SheafOfModules.{wModule} O) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{wModule} O) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{wModule} O)).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{wModule} O)).app K,
    inferInstance, inferInstance⟩

/-- The homotopy-category functor whose unbounded right derived functor is derived sections
over an object of the site. -/
public noncomputable abbrev homotopySections (O : Sheaf J RingCat.{wRing}) (U : C)
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}] :
    HomotopyCategory (SheafOfModules.{wModule} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{wModule} (O.obj.obj (op U))) :=
  (SheafOfModules.evaluation O (op U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- **Unbounded derived sections over an object of a ringed site**, `RΓ(U, -)`. -/
public noncomputable abbrev derivedSections (O : Sheaf J RingCat.{wRing}) (U : C)
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [(homotopySections O U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))] :
    DerivedCategory (SheafOfModules.{wModule} O) ⥤
      DerivedCategory (ModuleCat.{wModule} (O.obj.obj (op U))) :=
  (homotopySections O U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))

/-- **The hypercohomology edge morphism** `H^q(U, K) ⟶ H^0(U, H^q(K))` on a ringed site: the
unique natural transformation out of `RΓ(U, -) ⋙ H^q`, as a right derived functor of
`K ↦ H^q(Γ(U, K))`, which extends the comparison `H^q(Γ(U, K)) ⟶ Γ(U, H^q(K))` on the
homotopy category. -/
public noncomputable def hypercohomologyEdge (O : Sheaf J RingCat.{wRing}) (U : C)
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]
    [(homotopySections O U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))]
    (q : ℤ) :
    derivedSections O U ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{wModule} (O.obj.obj (op U))) q ⟶
      DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q ⋙
        SheafOfModules.evaluation O (op U) :=
  derivedHomologyComparison (SheafOfModules.evaluation O (op U)) (derivedSections O U)
    ((homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
    (exists_quasiIso_isKInjective_sheafOfModules O) q

/-- **The hypercohomology edge morphism is invertible at a K-injective complex of sheaves of
modules whose sections-homology comparison is invertible.** -/
public lemma isIso_hypercohomologyEdge_app_of_isKInjective (O : Sheaf J RingCat.{wRing}) (U : C)
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]
    [(homotopySections O U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))]
    (q : ℤ) (I : CochainComplex (SheafOfModules.{wModule} O) ℤ) (hI : I.IsKInjective)
    [IsIso (homologyComparison (SheafOfModules.evaluation O (op U)) I q)] :
    IsIso ((hypercohomologyEdge O U q).app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)).obj I))) :=
  isIso_derivedHomologyComparison_app_of_isKInjective
    (SheafOfModules.evaluation O (op U)) (derivedSections O U)
    ((homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
    (exists_quasiIso_isKInjective_sheafOfModules O) q I hI

end SiteSections

end Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

end
