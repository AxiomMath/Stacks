module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence

/-!
# Tag 08JA at an arbitrary representative pair

Let `(C, O)` be a ringed site. The degree-zero identification
`H^0(C, RSheafHom(L, M)) = Hom_{D(O)}(L, M)` of Tag 08JA for arbitrary objects of `D(O)`,
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`, is built from the *chosen*
K-flat and K-injective models of `L` and `M`. This file identifies it, at the class of a K-flat
complex `A` and the class of a K-injective complex `I`, with the identification
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat` at the pair `(A, I)`
itself, with no transport at all.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat`: **Tag 08JA at
  arbitrary objects, read at `(Q A, Q I)` for a K-flat `A` and a K-injective `I`, is Tag 08JA at
  the pair `(A, I)`.**

## Implementation notes

This is the model-independence of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence` for a
pair of representatives one of which is the chosen pair: the two are compared through a common
K-flat refinement of the contravariant variable
(`AlgebraicGeometry.RingedSite.exists_kFlat_common_refinement`), where Tag 0A96 restores the
K-injectivity of the internal Hom complex, and the covariant variable moves by a morphism of
complexes because the given representative is itself K-injective
(`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective`). It does not follow from the
naturality proved there, which compares the chosen models of two *different* pairs of objects and
says nothing about a representative the construction did not choose.

What it is for: the degree-zero reading of the canonical map
`Hom^•(F, G) ⟶ RHom_O(F, G)` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomLocalization` is proved
at a K-flat `F` and a K-injective `G` against
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat`, whereas the degree-`n`
reading of the global derived hom that the central clause of Tag 0CS6 consumes is stated against
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`; this is what bridges the two.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe v u

/-- **Solving for a conjugate across a refinement, with one side untransported.** The formal end
of the comparison below: `g` and `g'` are compared through a refinement `R` by an invertible
`qu`, and the conjugate of `g` by the two representing isomorphisms is `g'`. -/
private theorem conj_of_refinement_id {C : Type u} [Category.{v} C] {A₀ A I₀ I R : C}
    (eA : A₀ ≅ A) (eI : I₀ ≅ I) (qu : R ⟶ A₀) [IsIso qu] (qv : R ⟶ A) (qm : I₀ ⟶ I) (qn : I ⟶ I)
    (hn : qn = 𝟙 I) (hm : qm = eI.hom) (hu : qu ≫ eA.hom = qv)
    (g : A₀ ⟶ I₀) (g' : A ⟶ I) (hcomb : qu ≫ g ≫ qm = qv ≫ g' ≫ qn) :
    (eA.inv ≫ g) ≫ eI.hom = g' := by
  rw [hn, Category.comp_id, ← hu, hm, Category.assoc] at hcomb
  rw [Category.assoc, Iso.inv_comp_eq]
  exact (cancel_epi qu).mp hcomb

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]

/-- **Tag 08JA at arbitrary objects, read at a representative pair, is Tag 08JA at that pair.**
For a K-flat complex `A` and a K-injective complex `I`, the degree-zero identification
`H^0(C, RSheafHom(Q A, Q I)) = Hom_{D(O)}(Q A, Q I)` built from the chosen models is the
identification built at `(A, I)` itself.

The chosen models and `(A, I)` are compared through a common K-flat refinement of the
contravariant variable, exactly as in the model-independence argument; see the implementation
notes. -/
theorem derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective]
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) ξ =
      derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA ξ := by
  have hAI : ((sheafHomComplex X A I).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X A I hA
  have hA₀ : ((sheafHomComplex X (kFlatModel X (DerivedCategory.Q.obj A))
      (kInjectiveModel X (DerivedCategory.Q.obj I))).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X _ _
      (isKFlat_kFlatModel X (DerivedCategory.Q.obj A))
  obtain ⟨m, hm⟩ := exists_Q_map_eq_of_isKInjective X
    (kInjectiveModelIso X (DerivedCategory.Q.obj I)).hom
  obtain ⟨R, hR, u, v, hu, huv⟩ := exists_kFlat_common_refinement X
    (kFlatModelIso X (DerivedCategory.Q.obj A)).hom
  have hRI : ((sheafHomComplex X R I).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X R I hR
  have : IsIso (DerivedCategory.Q.map u) := hu
  -- The two transports of `ξ` agree.
  have hmorph : (derivedSheafHomObjectsModelIso X
          (kFlatModelIso X (DerivedCategory.Q.obj A))
          (kInjectiveModelIso X (DerivedCategory.Q.obj I))).hom ≫
        (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map u).op).app
            (DerivedCategory.Q.obj (kInjectiveModel X (DerivedCategory.Q.obj I))) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map
            (DerivedCategory.Q.map m)) =
      ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map v).op).app
          (DerivedCategory.Q.obj I) ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map
          (DerivedCategory.Q.map (𝟙 I)) := by
    have hI : (kInjectiveModelIso X (DerivedCategory.Q.obj I)).inv ≫
        DerivedCategory.Q.map m = DerivedCategory.Q.map (𝟙 I) := by
      exact (congrArg ((kInjectiveModelIso X (DerivedCategory.Q.obj I)).inv ≫ ·) hm).trans
        ((kInjectiveModelIso X (DerivedCategory.Q.obj I)).inv_hom_id.trans
          (CategoryTheory.Functor.map_id DerivedCategory.Q I).symm)
    refine (congrArg (· ≫ _) (derivedSheafHomObjectsModelIso_hom X
      (kFlatModelIso X (DerivedCategory.Q.obj A))
      (kInjectiveModelIso X (DerivedCategory.Q.obj I)))).trans ?_
    exact (derivedSheafHomBifunctor_map_comp X
      (kFlatModelIso X (DerivedCategory.Q.obj A)).hom
      (kInjectiveModelIso X (DerivedCategory.Q.obj I)).inv
      (DerivedCategory.Q.map u) (DerivedCategory.Q.map m)).trans
        (congrArg₂ (fun source target =>
          ((derivedSheafHomBifunctor X).map source.op).app (DerivedCategory.Q.obj I) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map target)
          huv hI)
  have harg := (homologyGlobalSections_map_comp_apply X
      (derivedSheafHomObjectsModelIso X (kFlatModelIso X (DerivedCategory.Q.obj A))
        (kInjectiveModelIso X (DerivedCategory.Q.obj I))).hom
      (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map u).op).app
          (DerivedCategory.Q.obj (kInjectiveModel X (DerivedCategory.Q.obj I))) ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map
          (DerivedCategory.Q.map m)) ξ).trans
    (congrArg (fun f => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map f) ξ) hmorph)
  -- Tag 08JA at a representative pair is natural for morphisms of complexes, twice.
  have h1 := derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality X u m
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map
        (derivedSheafHomObjectsModelIso X (kFlatModelIso X (DerivedCategory.Q.obj A))
          (kInjectiveModelIso X (DerivedCategory.Q.obj I))).hom) ξ)
  have h2 := derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality X v (𝟙 I) ξ
  refine (derivedSheafHomGlobalSectionsEquiv_apply X (DerivedCategory.Q.obj A)
    (DerivedCategory.Q.obj I) ξ).trans ?_
  refine (congrArg (fun identification : _ ≃+ _ =>
    ((kFlatModelIso X (DerivedCategory.Q.obj A)).inv ≫ identification
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X (DerivedCategory.Q.obj A))
            (kInjectiveModelIso X (DerivedCategory.Q.obj I))).hom) ξ)) ≫
      (kInjectiveModelIso X (DerivedCategory.Q.obj I)).hom)
    (derivedSheafHomGlobalSectionsEquivOfKFlat_eq X _ _
      (isKFlat_kFlatModel X (DerivedCategory.Q.obj A)))).trans ?_
  refine Eq.trans ?_ (congrArg (fun identification : _ ≃+ _ => identification ξ)
    (derivedSheafHomGlobalSectionsEquivOfKFlat_eq X A I hA)).symm
  exact conj_of_refinement_id (kFlatModelIso X (DerivedCategory.Q.obj A))
    (kInjectiveModelIso X (DerivedCategory.Q.obj I)) (DerivedCategory.Q.map u)
    (DerivedCategory.Q.map v) (DerivedCategory.Q.map m) (DerivedCategory.Q.map (𝟙 I))
    (CategoryTheory.Functor.map_id _ _) hm huv _ _
    (h1.symm.trans ((congrArg (fun z => derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X R I z)
      harg).trans h2))

end AlgebraicGeometry.RingedSite

end
