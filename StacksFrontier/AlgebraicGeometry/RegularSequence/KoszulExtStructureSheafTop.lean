module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtStructureSheaf
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulHomComplexExact
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtFromStrictlyPerfectResolutionNaturality

/-!
# The Ext sheaves of a Koszul quotient into the structure sheaf: vanishing and the top degree

Let `O♯` be a sheaf of commutative rings on a space and let `f₁, …, f_r` be global sections whose
Koszul complex resolves `O♯/I`. Then

* `𝓔xtⁿ(O♯/I, O♯) = 0` for every `n ≠ r`, and
* the quotient map `O♯ ⟶ O♯/I` induces an isomorphism `𝓔xtʳ(O♯/I, O♯) ≅ 𝓔xtʳ(O♯/I, O♯/I)`.

These are the two local statements in the proof of [Stacks, Tag 0BQZ]. Both are also read off
arbitrary models: for complexes `A`, `J`, `Q` presenting `O♯/I`, `O♯` and `O♯/I` in `D(O♯)` with
`J` and `Q` K-injective, the cohomology sheaves of `𝓗om^•(A, J)` vanish off degree `r`, and a map
`J ⟶ Q` lying over the quotient map induces an isomorphism on the degree-`r` cohomology sheaves
of `𝓗om^•(A, -)`.

## Main results

* `Stacks.RegularSequence.KoszulChainData.isZero_derivedSheafExt_unit_of_ne_of_quasiIso`
* `Stacks.RegularSequence.KoszulChainData.isIso_derivedSheafExtMap_quotientπ`
* `Stacks.RegularSequence.KoszulChainData.isZero_homology_sheafHomComplex_of_ne`
* `Stacks.RegularSequence.KoszulChainData.isIso_homologyMap_homMap_of_comp`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex

universe u

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.SheafOfModules Stacks.ChainComplex

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ)
  (f : Fin r → ↑(Rc.obj.obj (op (⊤ : Opens ↥X))))
  (hφ : ∀ k : Fin r,
    ((SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)).freeHomEquiv φ
      (ULift.up k)).val (op (⊤ : Opens ↥X)) = f k)

/-- The quotient `O♯/I`, placed in degree zero, as an object of `D(O♯)`. -/
abbrev quotientDerived : DerivedCategory (StructureSheafModules Rc) :=
  DerivedCategory.Q.obj
    ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj (quotient Rc (φ := φ)))

/-- The structure sheaf `O♯`, placed in degree zero, as an object of `D(O♯)`. -/
abbrev unitDerived : DerivedCategory (StructureSheafModules Rc) :=
  DerivedCategory.Q.obj (unitSingleComplex Rc)

/-- The quotient map `O♯ ⟶ O♯/I`, in `D(O♯)`. -/
abbrev quotientDerivedπ : unitDerived Rc ⟶ quotientDerived Rc (φ := φ) :=
  DerivedCategory.Q.map
    ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map (koszulQuotientπ φ))

include hφ in
/-- **The Ext sheaves of the quotient into the structure sheaf vanish outside the length**:
`𝓔xtⁿ(O♯/I, O♯) = 0` for `n ≠ r`. Below `0` and above `r` the Hom complex out of the Koszul
complex has no terms; in the degrees `0, …, r - 1` it is exact. -/
theorem isZero_derivedSheafExt_unit_of_ne_of_quasiIso [QuasiIso K.augmentation] {n : ℤ}
    (hn : n ≠ r) :
    IsZero (derivedSheafExt Rc (quotientDerived Rc (φ := φ)) (unitDerived Rc) n) := by
  rcases lt_or_gt_of_ne hn with h | h
  · rcases lt_or_ge n 0 with h0 | h0
    · exact isZero_derivedSheafExt_unit_of_notMem_Icc Rc K (Or.inl h0)
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
      exact ((exactAt_homComplex_unit Rc K f hφ (n := m) (by omega)).isZero_homology).of_iso
        (structureSheafExtIsoHomologyCochain Rc K (m : ℤ))
  · exact isZero_derivedSheafExt_unit_of_notMem_Icc Rc K (Or.inr h)

/-- With no generators the quotient map is an isomorphism: it is the cokernel of a morphism out
of a zero object. -/
theorem isIso_koszulQuotientπ_of_eq_zero (hr : r = 0) : IsIso (koszulQuotientπ φ) := by
  subst hr
  have hz : IsZero (koszulFreeSheaf Rc 0) := SheafOfModules.isZero_free_of_isEmpty _
  obtain rfl : φ = 0 := hz.eq_of_src _ _
  infer_instance

/-- Precomposing in the source with an isomorphism `e` does not change whether the map of Ext
sheaves induced by `π` in the target is an isomorphism. -/
private theorem isIso_derivedSheafExtMap_id_of_iso (n : ℤ)
    {K K' L L' : DerivedCategory (StructureSheafModules Rc)} (e : K' ⟶ K) [IsIso e] (π : L ⟶ L')
    (h : IsIso (derivedSheafExtMap Rc n (𝟙 K) π)) : IsIso (derivedSheafExtMap Rc n (𝟙 K') π) := by
  have e1 := derivedSheafExtMap_comp Rc n e (𝟙 L) (𝟙 K') π
  have e2 := derivedSheafExtMap_comp Rc n (𝟙 K) π e (𝟙 L')
  simp only [Category.id_comp, Category.comp_id] at e1 e2
  have := isIso_derivedSheafExtMap Rc n e (𝟙 L)
  have := isIso_derivedSheafExtMap Rc n e (𝟙 L')
  exact IsIso.of_isIso_fac_left (e1.trans e2.symm)

include hφ in
/-- **In the top degree the quotient map induces an isomorphism of Ext sheaves**,
`𝓔xtʳ(O♯/I, O♯) ≅ 𝓔xtʳ(O♯/I, O♯/I)`. -/
theorem isIso_derivedSheafExtMap_quotientπ [QuasiIso K.augmentation] :
    IsIso (derivedSheafExtMap Rc (r : ℤ) (𝟙 (quotientDerived Rc (φ := φ)))
      (quotientDerivedπ Rc (φ := φ))) := by
  by_cases hr0 : r = 0
  · have hπ : IsIso (koszulQuotientπ φ) := isIso_koszulQuotientπ_of_eq_zero Rc hr0
    have h1 : IsIso ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map
      (koszulQuotientπ φ)) := Functor.map_isIso _ (koszulQuotientπ φ)
    have h2 : IsIso (quotientDerivedπ Rc (φ := φ)) := Functor.map_isIso DerivedCategory.Q _
    exact isIso_derivedSheafExtMap Rc (r : ℤ) _ _
  obtain ⟨b, hr⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  subst hr
  have hq := quasiIsoAt_homComplexQuotientMap Rc φ f hφ K rfl
  rw [quasiIsoAt_iff_isIso_homologyMap] at hq
  have key := derivedSheafExtIsoHomologyOfResolution_naturality_target Rc (cochain Rc K)
    (unitSingleComplex Rc) ((b + 1 : ℕ) : ℤ) (finite_not_isZero_cochain_X Rc K)
    (isFiniteFreeSummand_cochain_X Rc K) (cochainAugmentation Rc K)
    ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map (koszulQuotientπ φ))
  have h1 : IsIso (derivedSheafExtMap Rc ((b + 1 : ℕ) : ℤ)
      (𝟙 (DerivedCategory.Q.obj (asCochain ((single (StructureSheafModules Rc)
        (ComplexShape.down ℤ) 0).obj (quotient Rc (φ := φ))))))
      (quotientDerivedπ Rc (φ := φ))) :=
    IsIso.of_isIso_fac_right key
  exact isIso_derivedSheafExtMap_id_of_iso Rc _ (DerivedCategory.Q.mapIso
    (quotientSingleIso Rc (φ := φ))).inv _ h1

/-! ### Reading the two statements off arbitrary models -/

variable {Am J Q : CochainComplex (StructureSheafModules Rc) ℤ} [J.IsKInjective] [Q.IsKInjective]
  (eA : DerivedCategory.Q.obj Am ≅ quotientDerived Rc (φ := φ))
  (eJ : DerivedCategory.Q.obj J ≅ unitDerived Rc)
  (eQ : DerivedCategory.Q.obj Q ≅ quotientDerived Rc (φ := φ))

/-- The cohomology sheaves of `𝓗om^•(A, J)` for `J` K-injective are the Ext sheaves. -/
def homologySheafHomComplexIsoDerivedSheafExt (n : ℤ) :
    (RingedSite.sheafHomComplex (ringedSite Rc) Am J).obj.homology n ≅
      derivedSheafExt Rc (DerivedCategory.Q.obj Am) (DerivedCategory.Q.obj J) n :=
  ((DerivedCategory.homologyFunctor _ n).mapIso (derivedSheafHomComparison Rc Am J) ≪≫
    (DerivedCategory.homologyFunctorFactors _ n).app _).symm

include hφ eA eJ in
/-- **The cohomology sheaves of `𝓗om^•(A, J)` vanish off degree `r`**, for `A` presenting the
quotient and `J` a K-injective complex presenting the structure sheaf. -/
theorem isZero_homology_sheafHomComplex_of_ne [QuasiIso K.augmentation] {n : ℤ} (hn : n ≠ r) :
    IsZero ((RingedSite.sheafHomComplex (ringedSite Rc) Am J).obj.homology n) :=
  ((isZero_derivedSheafExt_unit_of_ne_of_quasiIso Rc K f hφ hn).of_iso
    (derivedSheafExtMapIso Rc n eA.symm eJ)).of_iso
    (homologySheafHomComplexIsoDerivedSheafExt Rc n)

include hφ eA in
/-- **A map of K-injective models lying over the quotient map induces an isomorphism on the
degree-`r` cohomology sheaves of `𝓗om^•(A, -)`.** -/
theorem isIso_homologyMap_homMap_of_comp [QuasiIso K.augmentation] (g : J ⟶ Q)
    (hg : eJ.inv ≫ DerivedCategory.Q.map g ≫ eQ.hom = quotientDerivedπ Rc (φ := φ)) :
    IsIso (homologyMap (RingedSite.homMap (ringedSite Rc) (𝟙 Am) g) (r : ℤ)) := by
  have hnat := RingedSite.derivedSheafHomComparison_naturality (ringedSite Rc) (𝟙 Am) g
  rw [DerivedCategory.Q.map_id, ← Category.assoc] at hnat
  have hfac := DerivedCategory.homologyFunctorFactors_hom_naturality
    (C := StructureSheafModules Rc) (RingedSite.homMap (ringedSite Rc) (𝟙 Am) g) (r : ℤ)
  have hQg : DerivedCategory.Q.map g = eJ.hom ≫ quotientDerivedπ Rc (φ := φ) ≫ eQ.inv := by
    rw [← hg]; simp
  have hE : IsIso (derivedSheafExtMap Rc (r : ℤ) (𝟙 (DerivedCategory.Q.obj Am))
      (DerivedCategory.Q.map g)) := by
    have := isIso_derivedSheafExtMap_id_of_iso Rc (r : ℤ) eA.hom (quotientDerivedπ Rc (φ := φ))
      (isIso_derivedSheafExtMap_quotientπ Rc K f hφ)
    have eq : derivedSheafExtMap Rc (r : ℤ) (𝟙 (DerivedCategory.Q.obj Am))
        (eJ.hom ≫ quotientDerivedπ Rc (φ := φ) ≫ eQ.inv) =
        derivedSheafExtMap Rc (r : ℤ) (𝟙 (DerivedCategory.Q.obj Am)) eJ.hom ≫
          derivedSheafExtMap Rc (r : ℤ) (𝟙 (DerivedCategory.Q.obj Am))
            (quotientDerivedπ Rc (φ := φ)) ≫
          derivedSheafExtMap Rc (r : ℤ) (𝟙 (DerivedCategory.Q.obj Am)) eQ.inv := by
      rw [derivedSheafExtMap_comp, derivedSheafExtMap_comp]
      simp only [Category.comp_id]
    rw [hQg, eq]
    have := isIso_derivedSheafExtMap Rc (r : ℤ) (𝟙 (DerivedCategory.Q.obj Am)) eJ.hom
    have := isIso_derivedSheafExtMap Rc (r : ℤ) (𝟙 (DerivedCategory.Q.obj Am)) eQ.inv
    infer_instance
  have hE' : IsIso ((DerivedCategory.homologyFunctor _ (r : ℤ)).map
      ((((derivedSheafHom Rc).map (𝟙 (DerivedCategory.Q.obj Am)).op).app
        (DerivedCategory.Q.obj J)) ≫
        ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj Am))).map
          (DerivedCategory.Q.map g))) := hE
  have h1 : IsIso ((DerivedCategory.homologyFunctor _ (r : ℤ)).map
      (DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 Am) g))) := by
    have h2 : IsIso ((DerivedCategory.homologyFunctor _ (r : ℤ)).map
        ((RingedSite.derivedSheafHomComparison (ringedSite Rc) Am J).hom ≫
          DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc) (𝟙 Am) g))) := by
      have e := congrArg (fun φ => (DerivedCategory.homologyFunctor _ (r : ℤ)).map φ) hnat
      dsimp only at e
      rw [← e, Functor.map_comp]
      exact IsIso.comp_isIso' hE' inferInstance
    rw [Functor.map_comp] at h2
    exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor _ (r : ℤ)).map
      (RingedSite.derivedSheafHomComparison (ringedSite Rc) Am J).hom) _
  have h3 : IsIso ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc)
      (r : ℤ)).hom.app ((RingedSite.sheafHomComplex (ringedSite Rc) Am J).obj)) :=
    ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (r : ℤ)).app _).isIso_hom
  have h4 : IsIso ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc)
      (r : ℤ)).hom.app ((RingedSite.sheafHomComplex (ringedSite Rc) Am Q).obj)) :=
    ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (r : ℤ)).app _).isIso_hom
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ h3 (IsIso.comp_isIso' h1 h4) hfac.symm

end Stacks.RegularSequence.KoszulChainData
