module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.ProjectiveDimension.Criteria
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompat
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyFactorsh
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunctionUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorExtendHomology
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent

/-!
# The top cohomology of a derived base change

Let `f : R ⟶ A` be a homomorphism of commutative rings and `N` an object of `D(R)` with no
cohomology above degree `t`. Then the top cohomology of the derived base change is the base change
of the top cohomology:

`Hᵗ(N ⊗_R^𝐋 A) ≅ A ⊗_R Hᵗ(N)`,

through the canonical map, the transpose of the map induced on `Hᵗ` by the unit
`N ⟶ (N ⊗_R^𝐋 A)|_R` of the derived extension–restriction adjunction. This is right exactness of
`A ⊗_R -` read in the derived category: on a complex of projectives vanishing above `t`, which
computes the derived base change termwise, the top cohomology is a cokernel and extension of
scalars preserves cokernels.

## Main definitions

* `StacksDraft.TopDegreeExtendScalars.homologyComparison`: for a left adjoint `F` with exact
  right adjoint, the comparison `F(Hᵗ(K)) ⟶ Hᵗ(F(K))` of a cochain complex.
* `StacksDraft.TopDegreeExtendScalars.topDegreeComparison`: the comparison
  `A ⊗_R Hᵗ(N) ⟶ Hᵗ(N ⊗_R^𝐋 A)` in the derived category.

## Main results

* `StacksDraft.TopDegreeExtendScalars.isIso_homologyComparison`: the comparison is an
  isomorphism on a complex with nothing in degree `t + 1`.
* `StacksDraft.TopDegreeExtendScalars.topDegreeComparison_comp`: the comparison against the
  cohomology of a derived base-change map
  `StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison`.
* `StacksDraft.TopDegreeExtendScalars.isIso_topDegreeComparison`: **the top cohomology of a
  derived base change**, for `N` with no cohomology above `t`.

## Implementation notes

The derived extension of scalars is
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral`, with the adjunction
`StacksDraft.TopDegreeExtendScalars.extAdj` through which
`StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison` is defined. Both are available at
the standard model of the derived categories only, so the declarations of the second section are
stated at that model, scoped to each declaration.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.TopDegreeExtendScalars

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]

variable {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] [G.PreservesHomology] (adj : F ⊣ G)

/-- The comparison `F(Hᵗ(K)) ⟶ Hᵗ(F(K))` for a left adjoint `F` with exact right adjoint `G`:
the transpose of the map `Hᵗ(K) ⟶ Hᵗ(G F K) ≅ G(Hᵗ(F K))` induced by the unit. -/
def homologyComparison (K : CochainComplex C ℤ) (t : ℤ) :
    F.obj (K.homology t) ⟶ ((F.mapHomologicalComplex _).obj K).homology t :=
  (adj.homEquiv _ _).symm
    (HomologicalComplex.homologyMap ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K) t ≫
      (Stacks.DerivedIndexing.mapExactHomologyIso G ((F.mapHomologicalComplex _).obj K) t).hom)

/-- The inclusion of the cycles is an isomorphism in degree `t` when `K` has nothing in
degree `t + 1`. -/
private theorem isIso_iCycles_of_isZero (K : CochainComplex C ℤ) (t : ℤ)
    (hK : IsZero (K.X (t + 1))) : IsIso (K.iCycles t) :=
  K.isIso_iCycles t (t + 1) (by simp) (hK.eq_of_tgt _ _)

/-- The cokernel description of the top homology: for a complex with nothing in degree `t + 1`,
the composite `Kᵗ ≅ Zᵗ(K) ⟶ Hᵗ(K)` is a cokernel of the differential into degree `t`. -/
def topHomologyπ (K : CochainComplex C ℤ) (t : ℤ) (hK : IsZero (K.X (t + 1))) :
    K.X t ⟶ K.homology t :=
  haveI := K.isIso_iCycles t (t + 1) (by simp) (hK.eq_of_tgt _ _)
  inv (K.iCycles t) ≫ K.homologyπ t

/-- `topHomologyπ` after the inclusion of the cycles is the projection to homology. -/
theorem topHomologyπ_eq (K : CochainComplex C ℤ) (t : ℤ) (hK : IsZero (K.X (t + 1))) :
    K.iCycles t ≫ topHomologyπ K t hK = K.homologyπ t := by
  have := isIso_iCycles_of_isZero K t hK
  simp [topHomologyπ]

/-- `topHomologyπ` kills the differential into degree `t`. -/
theorem d_comp_topHomologyπ (K : CochainComplex C ℤ) (t : ℤ) (hK : IsZero (K.X (t + 1))) :
    K.d (t - 1) t ≫ topHomologyπ K t hK = 0 := by
  have := isIso_iCycles_of_isZero K t hK
  rw [topHomologyπ, ← K.toCycles_i (t - 1) t, Category.assoc, IsIso.hom_inv_id_assoc,
    K.toCycles_comp_homologyπ]

/-- `topHomologyπ` is a cokernel of the differential into degree `t`. -/
def isColimitTopHomologyπ (K : CochainComplex C ℤ) (t : ℤ) (hK : IsZero (K.X (t + 1))) :
    IsColimit (CokernelCofork.ofπ (f := K.d (t - 1) t) (topHomologyπ K t hK)
      (d_comp_topHomologyπ K t hK)) := by
  haveI := K.isIso_iCycles t (t + 1) (by simp) (hK.eq_of_tgt _ _)
  have hc := K.homologyIsCokernel (t - 1) t (by simp)
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun g hg => hc.desc (CokernelCofork.ofπ (K.iCycles t ≫ g) (by
      rw [K.toCycles_i_assoc, hg])))
    (fun g hg => ?_) (fun g hg m hm => ?_)
  · have := hc.fac (CokernelCofork.ofπ (K.iCycles t ≫ g) (by rw [K.toCycles_i_assoc, hg]))
      WalkingParallelPair.one
    simp only [Cofork.ofπ_ι_app] at this
    rw [topHomologyπ, Category.assoc, this, IsIso.inv_hom_id_assoc]
  · apply Cofork.IsColimit.hom_ext hc
    have := hc.fac (CokernelCofork.ofπ (K.iCycles t ≫ g) (by rw [K.toCycles_i_assoc, hg]))
      WalkingParallelPair.one
    simp only [Cofork.ofπ_ι_app, Cofork.π_ofπ] at this ⊢
    rw [this, ← hm, ← Category.assoc, topHomologyπ_eq]

/-- The comparison `F(Hᵗ(K)) ⟶ Hᵗ(F(K))` against the cokernel descriptions of the two top
homologies: it is the map they induce. -/
theorem map_topHomologyπ_comp_homologyComparison (K : CochainComplex C ℤ) (t : ℤ)
    (hK : IsZero (K.X (t + 1))) (hFK : IsZero (((F.mapHomologicalComplex _).obj K).X (t + 1))) :
    F.map (topHomologyπ K t hK) ≫ homologyComparison adj K t =
      topHomologyπ ((F.mapHomologicalComplex _).obj K) t hFK := by
  set L := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  set u := (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K
  have := isIso_iCycles_of_isZero K t hK
  have := isIso_iCycles_of_isZero L t hFK
  have := isIso_iCycles_of_isZero ((G.mapHomologicalComplex _).obj L) t (G.map_isZero hFK)
  rw [homologyComparison, ← Adjunction.homEquiv_naturality_left_symm,
    ← (adj.homEquiv _ _).symm_apply_apply (topHomologyπ L t hFK)]
  congr 1
  rw [Adjunction.homEquiv_unit]
  have hu : u.f t = adj.unit.app (K.X t) := rfl
  have key : inv (K.iCycles t) ≫ HomologicalComplex.cyclesMap u t ≫
      (Stacks.DerivedIndexing.mapExactCyclesIso G L t).hom =
        adj.unit.app (K.X t) ≫ G.map (inv (L.iCycles t)) := by
    rw [← cancel_epi (K.iCycles t), ← cancel_mono (G.map (L.iCycles t))]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← G.map_comp, IsIso.inv_hom_id, G.map_id,
      Stacks.DerivedIndexing.mapExactCyclesIso_hom_iCycles]
    exact (HomologicalComplex.cyclesMap_i u t).trans (by rw [hu]; simp)
  have hnat : HomologicalComplex.homologyπ K t ≫ HomologicalComplex.homologyMap u t =
      HomologicalComplex.cyclesMap u t ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homologyπ t :=
    HomologicalComplex.homologyπ_naturality u t
  calc topHomologyπ K t hK ≫ HomologicalComplex.homologyMap u t ≫
        (Stacks.DerivedIndexing.mapExactHomologyIso G L t).hom
      = inv (K.iCycles t) ≫ (HomologicalComplex.homologyπ K t ≫
          HomologicalComplex.homologyMap u t) ≫
          (Stacks.DerivedIndexing.mapExactHomologyIso G L t).hom := by
        simp only [topHomologyπ, Category.assoc]
    _ = inv (K.iCycles t) ≫ HomologicalComplex.cyclesMap u t ≫
          (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homologyπ t ≫
          (Stacks.DerivedIndexing.mapExactHomologyIso G L t).hom) := by
        rw [hnat]; simp only [Category.assoc]
    _ = (inv (K.iCycles t) ≫ HomologicalComplex.cyclesMap u t ≫
          (Stacks.DerivedIndexing.mapExactCyclesIso G L t).hom) ≫ G.map (L.homologyπ t) := by
        rw [Stacks.DerivedIndexing.homologyπ_mapExactHomologyIso_hom]; simp only [Category.assoc]
    _ = adj.unit.app (K.X t) ≫ G.map (topHomologyπ L t hFK) := by
        rw [key, topHomologyπ, G.map_comp, Category.assoc]

/-- **The top homology commutes with a right exact functor.** For a left adjoint `F` with exact
right adjoint and a complex `K` with nothing in degree `t + 1`, the comparison
`F(Hᵗ(K)) ⟶ Hᵗ(F(K))` is an isomorphism: both sides are cokernels of the differential into
degree `t`, the first because `F` preserves cokernels. -/
theorem isIso_homologyComparison (K : CochainComplex C ℤ) (t : ℤ) (hK : IsZero (K.X (t + 1))) :
    IsIso (homologyComparison adj K t) := by
  have hFK : IsZero (((F.mapHomologicalComplex _).obj K).X (t + 1)) := F.map_isZero hK
  have h1 := isColimitTopHomologyπ K t hK
  have h2 := isColimitTopHomologyπ ((F.mapHomologicalComplex _).obj K) t hFK
  have : Epi (topHomologyπ K t hK) := Cofork.IsColimit.epi h1
  have : Epi (topHomologyπ ((F.mapHomologicalComplex _).obj K) t hFK) := Cofork.IsColimit.epi h2
  have : F.IsLeftAdjoint := adj.isLeftAdjoint
  have : F.PreservesEpimorphisms := inferInstance
  have hfac := map_topHomologyπ_comp_homologyComparison adj K t hK hFK
  let ψ := h2.desc (CokernelCofork.ofπ (F.map (topHomologyπ K t hK)) (by
    change F.map (K.d (t - 1) t) ≫ _ = 0
    rw [← F.map_comp, d_comp_topHomologyπ, F.map_zero]))
  have hψ : topHomologyπ ((F.mapHomologicalComplex _).obj K) t hFK ≫ ψ =
      F.map (topHomologyπ K t hK) :=
    h2.fac _ WalkingParallelPair.one
  refine ⟨ψ, ?_, ?_⟩
  · rw [← cancel_epi (F.map (topHomologyπ K t hK)), reassoc_of% hfac, hψ, Category.comp_id]
  · rw [← cancel_epi (topHomologyπ ((F.mapHomologicalComplex _).obj K) t hFK),
      reassoc_of% hψ, hfac, Category.comp_id]

section Derived

universe u

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The derived extension–restriction adjunction through which
`StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison` is defined. -/
def extAdj :=
  @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u} R A _ _ f _ _
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u} f).functor
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u} f).comparison
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
        f).isLeftDerived

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison` is the transpose under
`StacksDraft.TopDegreeExtendScalars.extAdj`. -/
theorem derivedBaseChangeComparison_eq {X : DerivedCategory (ModuleCat.{u} R)}
    {Y : DerivedCategory (ModuleCat.{u} A)}
    (g : X ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj Y) :
    StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison f g =
      ((extAdj f).homEquiv X Y).symm g :=
  rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The top-degree comparison** `A ⊗_R Hᵗ(N) ⟶ Hᵗ(N ⊗_R^𝐋 A)` for derived extension of scalars:
the transpose of the map induced on `Hᵗ` by the unit `N ⟶ (N ⊗_R^𝐋 A)|_R`. -/
def topDegreeComparison (N : DerivedCategory (ModuleCat.{u} R)) (t : ℤ) :
    (ModuleCat.extendScalars f).obj ((DerivedCategory.homologyFunctor _ t).obj N) ⟶
      (DerivedCategory.homologyFunctor _ t).obj
        ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
          f).functor.obj N) :=
  ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm
    ((DerivedCategory.homologyFunctor _ t).map ((extAdj f).unit.app N) ≫
      ((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso t).hom.app _)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The top-degree comparison against the cohomology of a derived base-change map. -/
theorem topDegreeComparison_comp {N : DerivedCategory (ModuleCat.{u} R)}
    {E : DerivedCategory (ModuleCat.{u} A)}
    (g : N ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj E) (t : ℤ) :
    topDegreeComparison f N t ≫ (DerivedCategory.homologyFunctor _ t).map
        (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison f g) =
      ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm
        ((DerivedCategory.homologyFunctor _ t).map g ≫
          ((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso t).hom.app E) := by
  rw [derivedBaseChangeComparison_eq, topDegreeComparison,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  conv_rhs => rw [← ((extAdj f).homEquiv N E).apply_symm_apply g, Adjunction.homEquiv_unit]
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact (((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso t).hom.naturality _).symm

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The top-degree comparison is natural in the derived object. -/
theorem topDegreeComparison_naturality {N N' : DerivedCategory (ModuleCat.{u} R)} (φ : N ⟶ N')
    (t : ℤ) :
    topDegreeComparison f N t ≫ (DerivedCategory.homologyFunctor _ t).map
        ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
          f).functor.map φ) =
      (ModuleCat.extendScalars f).map ((DerivedCategory.homologyFunctor _ t).map φ) ≫
        topDegreeComparison f N' t := by
  have h : (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
      f).functor.map φ = StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison f
        (φ ≫ (extAdj f).unit.app N') := by
    rw [derivedBaseChangeComparison_eq, ← (extAdj f).unit_naturality,
      ← Adjunction.homEquiv_unit, Equiv.symm_apply_apply]
  rw [h, topDegreeComparison_comp, topDegreeComparison,
    ← Adjunction.homEquiv_naturality_left_symm, Functor.map_comp, Category.assoc]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The top-degree comparison is an isomorphism at a bounded-above complex of projectives.** -/
theorem isIso_topDegreeComparison_Q (P : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] (t : ℤ) [P.IsStrictlyLE t] :
    IsIso (topDegreeComparison f (DerivedCategory.Q.obj P) t) := by
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u} f
  let G := ModuleCat.restrictScalars.{u} f
  let F := ModuleCat.extendScalars.{u, u, u} f
  let adjM := ModuleCat.extendRestrictScalarsAdj.{u, u, u} f
  have hc : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P t
  let hD : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := D.isLeftDerived
  have hunit := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app
    R A _ _ f _ _ D.functor D.comparison hD P
  have hP : IsZero (P.X (t + 1)) := P.isZero_of_isStrictlyLE t (t + 1) (by omega)
  have key : topDegreeComparison f (DerivedCategory.Q.obj P) t ≫
      (DerivedCategory.homologyFunctor _ t).map (D.comparison.app P) =
      F.map ((DerivedCategory.homologyFunctorFactors _ t).hom.app P) ≫
        homologyComparison adjM P t ≫
          (DerivedCategory.homologyFunctorFactors _ t).inv.app ((F.mapHomologicalComplex _).obj P)
              := by
    have hcomp : D.comparison.app P = StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison f
        ((extAdj f).unit.app _ ≫ (ModuleCat.restrictScalars f).mapDerivedCategory.map
          (D.comparison.app P)) := by
      rw [derivedBaseChangeComparison_eq]
      exact (Equiv.eq_symm_apply _).mpr ((extAdj f).homEquiv_unit _ _ _)
    rw [hcomp, topDegreeComparison_comp]
    have hunit' : (extAdj f).unit.app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars f).mapDerivedCategory.map (D.comparison.app P) =
      DerivedCategory.Q.map ((adjM.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex _).obj P) := hunit
    rw [hunit']
    have hQ := G.mapDerivedCategoryHomologyIso_hom_app_Q t
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    have hnat := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) t).hom.naturality
      ((adjM.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P)
    simp only [Functor.comp_map] at hnat
    let u := (adjM.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P
    let FP := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) t
    let a := H.map (DerivedCategory.Q.map u)
    let b := H.map (G.mapDerivedCategoryFactors.inv.app FP)
    let c' := H.map (G.mapDerivedCategoryFactors.hom.app FP)
    let r := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) t).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj FP) ≫
        (G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) t).hom.app FP ≫
          G.map ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) t).inv.app FP)
    have e2 : b ≫ c' = 𝟙 _ := by
      simp only [b, c', H, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj]
      exact H.map_id _
    have key2 : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) t).map
          (DerivedCategory.Q.map u ≫ G.mapDerivedCategoryFactors.inv.app FP) ≫
          (G.mapDerivedCategoryHomologyIso t).hom.app (DerivedCategory.Q.obj FP) =
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) t).hom.app P ≫
          (HomologicalComplex.homologyMap u t ≫
            (Stacks.DerivedIndexing.mapExactHomologyIso G FP t).hom) ≫
          G.map ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) t).inv.app FP) := by
      calc _ = (a ≫ b) ≫ (c' ≫ r) :=
            congrArg₂ (· ≫ ·) (H.map_comp _ _) hQ
        _ = a ≫ (b ≫ c') ≫ r := by simp only [Category.assoc]
        _ = a ≫ r := congrArg (a ≫ ·) ((congrArg (· ≫ r) e2).trans (Category.id_comp r))
        _ = (a ≫ (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) t).hom.app
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj FP)) ≫
            (G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) t).hom.app FP ≫
              G.map ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) t).inv.app FP) :=
            (Category.assoc _ _ _).symm
        _ = ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) t).hom.app P ≫
              HomologicalComplex.homologyMap u t) ≫
            (G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) t).hom.app FP ≫
              G.map ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) t).inv.app FP) :=
            congrArg (· ≫ _) hnat
        _ = _ := (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)
    refine (congrArg (fun w => (adjM.homEquiv _ _).symm w) key2).trans ?_
    exact (Adjunction.homEquiv_naturality_left_symm _ _ _).trans
      (congrArg _ (Adjunction.homEquiv_naturality_right_symm _ _ _))
  have : IsIso (topDegreeComparison f (DerivedCategory.Q.obj P) t ≫
      (DerivedCategory.homologyFunctor _ t).map (D.comparison.app P)) := by
    rw [key]
    have h1 : IsIso (F.map ((DerivedCategory.homologyFunctorFactors _ t).hom.app P)) :=
      Functor.map_isIso _ _
    have h2 := isIso_homologyComparison adjM P t hP
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1
      (@IsIso.comp_isIso _ _ _ _ _ _ _ h2 (Iso.isIso_hom ((DerivedCategory.homologyFunctorFactors _
          t).app _).symm))
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor _ t).map (D.comparison.app P))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The top-degree comparison is an isomorphism.** For `N ∈ D(R)` with no cohomology above
degree `t`, `A ⊗_R Hᵗ(N) ≅ Hᵗ(N ⊗_R^𝐋 A)` through the canonical map: compute `N` by a complex
of projectives vanishing above `t`, on which derived extension of scalars is termwise and the top
cohomology is a cokernel, which extension of scalars preserves. -/
theorem isIso_topDegreeComparison (N : DerivedCategory (ModuleCat.{u} R)) (t : ℤ) [N.IsLE t] :
    IsIso (topDegreeComparison f N t) := by
  obtain ⟨P, ⟨e⟩, hproj, hP⟩ :=
    StacksDraft.ProjectiveDimension.exists_projective_representative_boundedAbove N t
  have : ∀ i, Projective (P.X i) := fun i => inferInstance
  have := isIso_topDegreeComparison_Q f P t
  have h := topDegreeComparison_naturality f e.hom t
  have : IsIso ((ModuleCat.extendScalars f).map
      ((DerivedCategory.homologyFunctor _ t).map e.hom) ≫ topDegreeComparison f N t) := by
    rw [← h]; infer_instance
  exact IsIso.of_isIso_comp_left ((ModuleCat.extendScalars f).map
    ((DerivedCategory.homologyFunctor _ t).map e.hom)) _

end Derived

end StacksDraft.TopDegreeExtendScalars

end
