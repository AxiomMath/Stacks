module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompSingleDelta
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleInverseLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDualTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleTensorCohomologyDualExt
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedBaseRingTensor
public import StacksFrontier.Deformation.Artin.Obstruction.DerivedCohomologyShiftedHom
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareLocalization
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# `H^i(Spec A, K ⊗^L M~) = H^i(K_A ⊗^L_A M)` for a perfect `K` on `(Spec A)_étale`

Let `A` be a ring and `Y = Spec A`, as an algebraic space over `S`, and let `M ↦ M~` be the
module `𝒪_Y ⊗_A M` of Stacks 0D3F. For a perfect object `K` of `D(𝒪_Y)` (on the small étale
site of `Y`) there is a perfect complex `K_A` of `A`-modules and isomorphisms

`H^i(Y, K ⊗^L M~) ≅ H^i(K_A ⊗^L_A M)`,

natural in the `A`-module `M` and compatible with the boundary maps of short exact sequences
`0 → M₁ → M₂ → M₃ → 0`. This is the identification of `H^i(Spec A, K ⊗^L -)` with the
cohomology of a perfect complex of `A`-modules used, after Stacks 08JR, in the proof of Stacks
08WA and in Remark 0D1P.

## Main results

* `exists_isPerfect_smallEtaleTensorCohomology_addEquiv_derivedCohomology_of_iso`:
  the statement above for any functor `H` from `A`-modules to `𝒪_Y`-modules presented with an
  isomorphism identifying it with the associated module `M ↦ M~` read over `Γ(Spec A)`.

## The proof

Both sides are groups of morphisms out of a perfect object, compatibly with the boundary maps:

* `H^i(Y, K ⊗^L ℱ) ≅ Hom(K^∨, ℱ[i])`
  (`AlgebraicGeometry.Space.smallEtaleTensorCohomologyDualExtAddEquiv`);
* `H^i(K_A ⊗^L_A M) ≅ Hom_{D(A)}(L, M[i])` for `K_A` the derived dual of a perfect `L`
  (`Deformation.Artin.exists_isPerfect_derivedCohomology_addEquiv_shiftedHom`, from 07VI).

The functor `Φ : D(A) ⥤ D(𝒪_Y)` induced by the exact functor `M ↦ M~` is fully faithful, and
`K^∨ ≅ Φ(L)` for a perfect `L`: by
`AlgebraicGeometry.Space.baseRingTensorModuleIsoRepresentedAffineAssociated`
the functor `M ↦ M~` is the associated module functor of `D_QCoh(𝒪_Y) ≃ D(Γ(Y, 𝒪_Y))`
(`AlgebraicGeometry.Space.representedAffineDerivedAdjunction`), read through the ring isomorphism
`A ≅ Γ(Spec A, 𝒪)`. So `Hom(K^∨, M~[i]) ≅ Hom(Φ L, (Φ M)[i]) ≅ Hom_{D(A)}(L, M[i])`, and the
boundary morphism of `0 → M₁~ → M₂~ → M₃~ → 0` is the image under `Φ` of that of
`0 → M₁ → M₂ → M₃ → 0` (`CategoryTheory.ShortComplex.ShortExact.mapShiftedHom_singleδ`).

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
-- One standard-model line, scoped to this file: the base declarations
-- `Deformation.Artin.derivedCohomology`, `Deformation.Artin.boundaryMap`,
-- `AlgebraicGeometry.Space.smallEtaleTensorCohomology` and
-- `AlgebraicGeometry.Space.representedAffineDerivedAdjunction` are stated in the model
-- `HasDerivedCategory.standard`.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] pointTopology
attribute [local instance 5000] SheafOfModules.instAbelian
-- The universe-`u` sheafification of the small étale site, ahead of universe-polymorphic
-- candidates whose universe constraints are left stuck.
attribute [local instance 100000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-- The scheme underlying `Spec A`, as an object of the site, is affine. -/
instance isAffine_toScheme_algebraOver :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (Deformation.Artin.algebraOver A B S hS toS hA)) :=
  inferInstanceAs (IsAffine (Spec (.of A)))

/-- `M ↦ M~ = 𝒪_{Spec A} ⊗_A M` on the small étale site of `Spec A`, for the base-ring datum
`A ≅ Γ(Spec A) → Γ(𝒪_{Spec A})` of the identity of `Spec A`. -/
local notation "tildeA" => baseRingTensorModule B S hS
  (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))
  (RingHom.comp (baseRingHomOfMap (𝟙 (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))
    (CommRingCat.Hom.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of A)))))

/-- `Γ(Spec A) ≅ A`, with its source spelled as the ring of global functions of the object
`Spec A` of the site, which is the ring of
`AlgebraicGeometry.Space.representedAffineAssociated`. -/
def algebraOverGlobalSectionsIso :
    Γ((BigFppfOver.toScheme B S hS).obj (Deformation.Artin.algebraOver A B S hS toS hA), ⊤) ≅
      CommRingCat.of A :=
  Scheme.ΓSpecIso (CommRingCat.of A)

/-- **`M ↦ M~` is the associated module of `M` read over `Γ(Spec A)`**: restriction of scalars
along `Γ(Spec A) ≅ A` followed by the associated-module functor of the affine represented space
is the base-ring tensor product `𝒪 ⊗_A -`, by
`AlgebraicGeometry.Space.baseRingTensorModuleIsoRepresentedAffineAssociated`. -/
def restrictScalarsRepresentedAffineAssociatedIso :
    ModuleCat.restrictScalars.{u, u, u} (algebraOverGlobalSectionsIso A B S hS toS hA).hom.hom ⋙
        representedAffineAssociated B S hS (Deformation.Artin.algebraOver A B S hS toS hA) ≅
      tildeA :=
  Functor.isoWhiskerLeft _
      (baseRingTensorModuleIsoRepresentedAffineAssociated B S hS
        (Deformation.Artin.algebraOver A B S hS toS hA)).symm ≪≫
    Functor.isoWhiskerRight
      (StacksDraft.DerivedRingIso.extendScalarsRestrictIso
        (algebraOverGlobalSectionsIso A B S hS toS hA).inv.hom
        (algebraOverGlobalSectionsIso A B S hS toS hA).hom.hom (fun x => by simp) (fun y => by simp)
        (baseRingHomOfMap (𝟙 (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))))
      (Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor.{u, u, u, u} _ ⋙
        (smallEtaleModelModulesEquiv B S hS
          (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))).inverse)

/-- The associated module functor of the affine represented space `Spec A`
(`AlgebraicGeometry.Space.representedAffineAssociated`), with its target spelled as the modules
over the structure sheaf of the small étale ringed topos of `Spec A`, the spelling of
`AlgebraicGeometry.Space.smallEtaleTensorCohomology`. -/
def representedAffineAssociatedRingedTopos :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj
        (Deformation.Artin.algebraOver A B S hS toS hA), ⊤) ⥤
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))) :=
  representedAffineAssociated B S hS (Deformation.Artin.algebraOver A B S hS toS hA)

/-- The associated module functor of `Spec A` is additive. -/
instance additive_representedAffineAssociatedRingedTopos :
    (representedAffineAssociatedRingedTopos A B S hS toS hA).Additive :=
  additive_representedAffineAssociated B S hS (Deformation.Artin.algebraOver A B S hS toS hA)

/-- The associated module functor of `Spec A` preserves finite limits. -/
instance preservesFiniteLimits_representedAffineAssociatedRingedTopos :
    PreservesFiniteLimits (representedAffineAssociatedRingedTopos A B S hS toS hA) :=
  preservesFiniteLimits_representedAffineAssociated B S hS
    (Deformation.Artin.algebraOver A B S hS toS hA)

/-- The associated module functor of `Spec A` preserves finite colimits. -/
instance preservesFiniteColimits_representedAffineAssociatedRingedTopos :
    PreservesFiniteColimits (representedAffineAssociatedRingedTopos A B S hS toS hA) :=
  preservesFiniteColimits_representedAffineAssociated B S hS
    (Deformation.Artin.algebraOver A B S hS toS hA)

/-- **The functor `Φ : D(A) ⥤ D(𝒪_{Spec A})`**: restriction of scalars along `Γ(Spec A) ≅ A`
followed by the derived associated-module functor of the affine represented space `Spec A`. -/
abbrev algebraOverDerivedAssociated :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))) :=
  (ModuleCat.restrictScalars.{u, u, u}
    (algebraOverGlobalSectionsIso A B S hS toS hA).hom.hom).mapDerivedCategory ⋙
    (representedAffineAssociatedRingedTopos A B S hS toS hA).mapDerivedCategory

/-- **`Φ` is fully faithful**: restriction of scalars along a ring isomorphism induces an
equivalence of derived categories, and the derived associated-module functor of an affine
represented space is fully faithful
(`AlgebraicGeometry.Space.representedAffineDerivedAssociatedFullyFaithful`). -/
def algebraOverDerivedAssociatedFullyFaithful :
    (algebraOverDerivedAssociated A B S hS toS hA).FullyFaithful :=
  haveI := StacksDraft.DerivedRingIso.isEquivalence_mapDerivedCategory_restrictScalars
    (algebraOverGlobalSectionsIso A B S hS toS hA).inv.hom
    (algebraOverGlobalSectionsIso A B S hS toS hA).hom.hom (fun x => by simp) (fun y => by simp)
  haveI : (representedAffineAssociatedRingedTopos A B S hS toS hA).mapDerivedCategory.Full :=
    (representedAffineDerivedAssociatedFullyFaithful B S hS
      (Deformation.Artin.algebraOver A B S hS toS hA)).full
  haveI : (representedAffineAssociatedRingedTopos A B S hS toS hA).mapDerivedCategory.Faithful :=
    (representedAffineDerivedAssociatedFullyFaithful B S hS
      (Deformation.Artin.algebraOver A B S hS toS hA)).faithful
  (Functor.FullyFaithful.ofFullyFaithful
    (ModuleCat.restrictScalars.{u, u, u}
      (algebraOverGlobalSectionsIso A B S hS toS hA).hom.hom).mapDerivedCategory).comp
    (Functor.FullyFaithful.ofFullyFaithful
      (representedAffineAssociatedRingedTopos A B S hS toS hA).mapDerivedCategory)

/-- **A perfect object on `(Spec A)_étale` comes from a perfect complex of `A`-modules**: it lies
in `D_QCoh`, so it is the associated object of its derived sections, which are perfect over
`Γ(Spec A) ≅ A`. -/
theorem exists_isPerfect_iso_algebraOverDerivedAssociated_obj
    (E : smallEtaleModulesDerived B S hS
      (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))
    (hE : SmallEtaleIsPerfect B S hS E) :
    ∃ (L : DerivedCategory (ModuleCat.{u} A)) (_ : StacksDraft.Perfect.IsPerfect L),
      Nonempty (E ≅ (algebraOverDerivedAssociated A B S hS toS hA).obj L) := by
  let U := Deformation.Artin.algebraOver A B S hS toS hA
  let ε := (algebraOverGlobalSectionsIso A B S hS toS hA).inv.hom
  let ε' := (algebraOverGlobalSectionsIso A B S hS toS hA).hom.hom
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E
    (qcohDerived_of_isPerfect B S hS (schemeSpace U) E hE)
  let L₀ := (representedAffineDerivedSections B S hS U).obj E
  let ρ : A ≃+* Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
    (algebraOverGlobalSectionsIso A B S hS toS hA).symm.commRingCatIsoToRingEquiv
  refine ⟨(ModuleCat.restrictScalars.{u, u, u} ρ.toRingHom).mapDerivedCategory.obj L₀,
    StacksDraft.Perfect.isPerfect_restrictScalars_ringEquiv ρ L₀
      (isPerfect_representedAffineDerivedSections_obj B S hS U E hE), ⟨?_⟩⟩
  let r : L₀ ≅ (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.obj
      ((ModuleCat.restrictScalars.{u, u, u} ε).mapDerivedCategory.obj L₀) :=
    ((RingTheory.TorIndependence.mapDerivedCategoryCompNatIso _ _ _
      (StacksDraft.DerivedRingIso.restrictScalarsCounitOfInv ε ε' (fun y => by simp [ε, ε']))).app
        L₀ ≪≫ Stacks.Homology.mapDerivedCategoryIdIso.app L₀).symm
  exact (asIso ((representedAffineDerivedAdjunction B S hS U).counit.app E)).symm ≪≫
    (representedAffineDerivedAssociated B S hS U).mapIso r

section Transport

variable {A B S hS toS hA}

variable (H : ModuleCat.{u} A ⥤
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))))
  (e : (ModuleCat.restrictScalars.{u, u, u}
      (algebraOverGlobalSectionsIso A B S hS toS hA).hom.hom) ⋙
    representedAffineAssociatedRingedTopos A B S hS toS hA ≅ H)

/-- **`Φ(M[0]) ≅ H(M)[0]`**, naturally in the `A`-module `M`, for a functor `H` identified with
the associated module `M ↦ M~` read over `Γ(Spec A)`. -/
def algebraOverDerivedAssociatedSingleIso :
    DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        algebraOverDerivedAssociated A B S hS toS hA ≅
      H ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))) 0 :=
  Functor.mapDerivedCategoryCompSingleIsoOfIso
    (ModuleCat.restrictScalars.{u, u, u} (algebraOverGlobalSectionsIso A B S hS toS hA).hom.hom)
    (representedAffineAssociatedRingedTopos A B S hS toS hA) H e

/-- **`Φ` carries the boundary morphism of `0 → M₁ → M₂ → M₃ → 0` to that of
`0 → H M₁ → H M₂ → H M₃ → 0`**, through `Φ(M[0]) ≅ H(M)[0]`. -/
theorem algebraOverDerivedAssociated_map_singleδ [H.PreservesZeroMorphisms]
    {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact) (hT : (Sq.map H).ShortExact) :
    ((algebraOverDerivedAssociated A B S hS toS hA).map hSq.singleδ ≫
        ((algebraOverDerivedAssociated A B S hS toS hA).commShiftIso (1 : ℤ)).hom.app _) ≫
        ((algebraOverDerivedAssociatedSingleIso H e).hom.app Sq.X₁)⟦(1 : ℤ)⟧' =
      (algebraOverDerivedAssociatedSingleIso H e).hom.app Sq.X₃ ≫ hT.singleδ :=
  Functor.mapDerivedCategoryCompSingleIsoOfIso_singleδ
    (ModuleCat.restrictScalars.{u, u, u} (algebraOverGlobalSectionsIso A B S hS toS hA).hom.hom)
    (representedAffineAssociatedRingedTopos A B S hS toS hA) H e hSq hT

variable {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
    (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))}
  {L : DerivedCategory (ModuleCat.{u} A)}
  (ε : E ≅ (algebraOverDerivedAssociated A B S hS toS hA).obj L)

/-- **`Hom_{D(A)}(L, M[0][i]) ≃+ Hom(E, H(M)[0][i])` for `E ≅ Φ(L)`**: `Φ` is fully faithful, and
`Φ(M[0][i]) ≅ Φ(M[0])[i] ≅ H(M)[0][i]`. -/
def algebraOverDerivedAssociatedShiftedHomAddEquiv (M : ModuleCat.{u} A) (i : ℤ) :
    (L ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)⟦i⟧) ≃+
      (E ⟶ ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))
        0).obj (H.obj M))⟦i⟧) :=
  (AddEquiv.ofBijective (algebraOverDerivedAssociated A B S hS toS hA).mapAddHom
    ((algebraOverDerivedAssociatedFullyFaithful A B S hS toS hA).map_bijective _ _)).trans
    (Stacks.Injectives.homCongrAddEquiv ε.symm
      (((algebraOverDerivedAssociated A B S hS toS hA).commShiftIso i).app _ ≪≫
        (shiftFunctor _ i).mapIso ((algebraOverDerivedAssociatedSingleIso H e).app M)))

/-- `AlgebraicGeometry.Space.algebraOverDerivedAssociatedShiftedHomAddEquiv` applies `Φ` to a
morphism and composes with `ε` and the isomorphism `Φ(M[0][i]) ≅ H(M)[0][i]`. -/
theorem algebraOverDerivedAssociatedShiftedHomAddEquiv_apply (M : ModuleCat.{u} A) (i : ℤ)
    (f : L ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)⟦i⟧) :
    algebraOverDerivedAssociatedShiftedHomAddEquiv H e ε M i f =
      ε.hom ≫ (algebraOverDerivedAssociated A B S hS toS hA).map f ≫
        ((algebraOverDerivedAssociated A B S hS toS hA).commShiftIso i).hom.app _ ≫
          ((algebraOverDerivedAssociatedSingleIso H e).hom.app M)⟦i⟧' :=
  rfl

/-- `AlgebraicGeometry.Space.algebraOverDerivedAssociatedShiftedHomAddEquiv` is natural in the
module. -/
theorem algebraOverDerivedAssociatedShiftedHomAddEquiv_naturality {M N : ModuleCat.{u} A}
    (g : M ⟶ N) (i : ℤ) (f : L ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)⟦i⟧) :
    algebraOverDerivedAssociatedShiftedHomAddEquiv H e ε N i
        (f ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)⟦i⟧') =
      algebraOverDerivedAssociatedShiftedHomAddEquiv H e ε M i f ≫
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))
          0).map (H.map g))⟦i⟧' := by
  have hτ : (algebraOverDerivedAssociated A B S hS toS hA).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g) ≫
        (algebraOverDerivedAssociatedSingleIso H e).hom.app N =
      (algebraOverDerivedAssociatedSingleIso H e).hom.app M ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))
          0).map (H.map g) :=
    (algebraOverDerivedAssociatedSingleIso H e).hom.naturality g
  rw [algebraOverDerivedAssociatedShiftedHomAddEquiv_apply,
    algebraOverDerivedAssociatedShiftedHomAddEquiv_apply]
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, hτ, Functor.map_comp]

/-- `AlgebraicGeometry.Space.algebraOverDerivedAssociatedShiftedHomAddEquiv` carries composition
with the boundary morphism of `0 → M₁ → M₂ → M₃ → 0` to composition with that of
`0 → H M₁ → H M₂ → H M₃ → 0`. -/
theorem algebraOverDerivedAssociatedShiftedHomAddEquiv_singleδ [H.PreservesZeroMorphisms]
    {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact) (hT : (Sq.map H).ShortExact)
    (f : L ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₃)⟦(1 : ℤ)⟧) :
    algebraOverDerivedAssociatedShiftedHomAddEquiv H e ε Sq.X₁ 2
        (f ≫ hSq.singleδ⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ) 1 2 (by norm_num)).inv.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁)) =
      algebraOverDerivedAssociatedShiftedHomAddEquiv H e ε Sq.X₃ 1 f ≫
        hT.singleδ⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
              (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))))
            (1 : ℤ) 1 2 (by norm_num)).inv.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
                (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))
              0).obj (H.obj Sq.X₁)) := by
  have hδ := algebraOverDerivedAssociated_map_singleδ H e hSq hT
  have hk := Functor.map_comp_shiftFunctorAdd'_inv_commShiftIso
    (algebraOverDerivedAssociated A B S hS toS hA) hSq.singleδ 1 2 (by norm_num)
  have hk' : ∀ {Z : DerivedCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))} (k : _ ⟶ Z),
      (algebraOverDerivedAssociated A B S hS toS hA).map (hSq.singleδ⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ) 1 2 (by norm_num)).inv.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁)) ≫
        ((algebraOverDerivedAssociated A B S hS toS hA).commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁) ≫ k =
      ((algebraOverDerivedAssociated A B S hS toS hA).commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₃) ≫
        ((algebraOverDerivedAssociated A B S hS toS hA).map hSq.singleδ ≫
          ((algebraOverDerivedAssociated A B S hS toS hA).commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))))
          (1 : ℤ) 1 2 (by norm_num)).inv.app
          ((algebraOverDerivedAssociated A B S hS toS hA).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁)) ≫ k := fun k => by
    simpa only [Category.assoc] using hk =≫ k
  have hn : (((algebraOverDerivedAssociatedSingleIso H e).hom.app Sq.X₁)⟦(1 : ℤ)⟧')⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))))
          (1 : ℤ) 1 2 (by norm_num)).inv.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
              (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))
            0).obj (H.obj Sq.X₁)) =
      (shiftFunctorAdd' (DerivedCategory
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))))
        (1 : ℤ) 1 2 (by norm_num)).inv.app
          ((algebraOverDerivedAssociated A B S hS toS hA).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁)) ≫
        ((algebraOverDerivedAssociatedSingleIso H e).hom.app Sq.X₁)⟦(2 : ℤ)⟧' :=
    (shiftFunctorAdd' (DerivedCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))))
      (1 : ℤ) 1 2 (by norm_num)).inv.naturality _
  rw [algebraOverDerivedAssociatedShiftedHomAddEquiv_apply,
    algebraOverDerivedAssociatedShiftedHomAddEquiv_apply, Functor.map_comp, Category.assoc, hk',
    ← hn, ← Functor.map_comp_assoc, hδ, Functor.map_comp_assoc]
  simp only [Category.assoc]

end Transport

section Assembly

variable {A B S hS toS hA}

/-- **`H^i(Spec A, K ⊗^L H(M)) ≅ H^i(K_A ⊗^L_A M)` for a perfect `K`**, for any functor `H`
identified with the associated module `M ↦ M~` read over `Γ(Spec A)`: there is a perfect complex
`K_A` of `A`-modules and isomorphisms natural in `M` and compatible with the boundary maps of short
exact sequences. -/
theorem exists_isPerfect_smallEtaleTensorCohomology_addEquiv_derivedCohomology_of_iso
    (H : ModuleCat.{u} A ⥤
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))))
    [H.PreservesZeroMorphisms]
    (e : (ModuleCat.restrictScalars.{u, u, u}
        (algebraOverGlobalSectionsIso A B S hS toS hA).hom.hom) ⋙
      representedAffineAssociatedRingedTopos A B S hS toS hA ≅ H)
    (K : smallEtaleModulesDerived B S hS
      (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))
    (hK : SmallEtaleIsPerfect B S hS K) :
    ∃ (K_A : DerivedCategory (ModuleCat.{u} A)) (_ : StacksDraft.Perfect.IsPerfect K_A)
      (γ : ∀ (M : ModuleCat.{u} A) (i : ℤ),
        smallEtaleTensorCohomology B S hS K (H.obj M) i ≃+
          (Deformation.Artin.derivedCohomology A K_A i).obj M),
      (∀ {M N : ModuleCat.{u} A} (g : M ⟶ N) (i : ℤ) (y),
        γ N i ((smallEtaleTensorCohomologyMap B S hS K (H.map g) i) y) =
          (Deformation.Artin.derivedCohomology A K_A i).map g (γ M i y)) ∧
      (∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact)
        (hT : (Sq.map H).ShortExact) (y),
        γ Sq.X₁ 2 ((smallEtaleTensorCohomologyDelta B S hS K (Sq.map H) hT 1 2 rfl) y) =
          Deformation.Artin.boundaryMap A K_A hSq (γ Sq.X₃ 1 y)) := by
  obtain ⟨L, hL, ⟨ε⟩⟩ := exists_isPerfect_iso_algebraOverDerivedAssociated_obj A B S hS toS hA
    (smallEtaleDerivedDual B S hS (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)) K)
    (isPerfect_smallEtaleDerivedDual B S hS
      (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)) K hK)
  obtain ⟨KA, hKA, eA, heAnat, heAδ⟩ :=
    Deformation.Artin.exists_isPerfect_derivedCohomology_addEquiv_shiftedHom A L hL
  obtain ⟨E₁, hE₁nat, hE₁δ⟩ := exists_smallEtaleTensorCohomology_addEquiv_dualExt B S hS K hK
  refine ⟨KA, hKA, fun M i => (E₁ (H.obj M) i).trans
      ((algebraOverDerivedAssociatedShiftedHomAddEquiv H e ε M i).symm.trans (eA M i).symm),
    ?_, ?_⟩
  · intro M N g i y
    have h1 : ∀ z, (algebraOverDerivedAssociatedShiftedHomAddEquiv H e ε N i).symm
        (z ≫ ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))
          0).map (H.map g))⟦i⟧') =
        (algebraOverDerivedAssociatedShiftedHomAddEquiv H e ε M i).symm z ≫
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)⟦i⟧' := fun z => by
      rw [AddEquiv.symm_apply_eq, algebraOverDerivedAssociatedShiftedHomAddEquiv_naturality,
        AddEquiv.apply_symm_apply]
    have h2 : ∀ w, (eA N i).symm
        (w ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)⟦i⟧') =
        (Deformation.Artin.derivedCohomology A KA i).map g ((eA M i).symm w) := fun w => by
      rw [AddEquiv.symm_apply_eq, heAnat, AddEquiv.apply_symm_apply]
    simp only [AddEquiv.trans_apply]
    rw [hE₁nat, h1, h2]
  · intro Sq hSq hT y
    have h1 : ∀ z, (algebraOverDerivedAssociatedShiftedHomAddEquiv H e ε Sq.X₁ 2).symm
        (z ≫ hT.singleδ⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
              (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))))
            (1 : ℤ) 1 2 (by norm_num)).inv.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
                (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))
              0).obj (Sq.map H).X₁)) =
        (algebraOverDerivedAssociatedShiftedHomAddEquiv H e ε Sq.X₃ 1).symm z ≫
          hSq.singleδ⟦(1 : ℤ)⟧' ≫
            (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ) 1 2 (by norm_num)).inv.app
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁) := fun z => by
      rw [AddEquiv.symm_apply_eq,
        algebraOverDerivedAssociatedShiftedHomAddEquiv_singleδ H e ε hSq hT,
        AddEquiv.apply_symm_apply]
      rfl
    have h2 : ∀ w, (eA Sq.X₁ 2).symm (w ≫ hSq.singleδ⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ) 1 2 (by norm_num)).inv.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₁)) =
        Deformation.Artin.boundaryMap A KA hSq ((eA Sq.X₃ 1).symm w) := fun w => by
      rw [AddEquiv.symm_apply_eq, heAδ, AddEquiv.apply_symm_apply]
    simp only [AddEquiv.trans_apply]
    have k1 : E₁ (H.obj Sq.X₁) 2
        (smallEtaleTensorCohomologyDelta B S hS K (Sq.map H) hT 1 2 rfl y) =
        E₁ (Sq.map H).X₃ 1 y ≫ hT.singleδ⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
              (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))))
            (1 : ℤ) 1 2 (by norm_num)).inv.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
                (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))))
              0).obj (Sq.map H).X₁) :=
      hE₁δ hT y
    rw [k1, h1, h2]
    rfl

end Assembly

end AlgebraicGeometry.Space

end
