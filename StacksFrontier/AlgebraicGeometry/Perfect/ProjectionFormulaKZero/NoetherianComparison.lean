module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectionFormulaKZero.PerfectTensor
public import StacksFrontier.AlgebraicGeometry.Perfect.CoherentKGroupModule

/-!
# The product on `K'₀` of a Noetherian scheme, through `K₀(D^b_Coh)`

Let `X` be a Noetherian scheme. Under the identification `K'₀(X) = K₀(D^b_Coh(𝒪_X))` of
[Stacks, Tag 0FDF] the parity Euler class of an object of `D^b_Coh(𝒪_X)` is its class, and the
product `perfectCoherentSMul` is the module structure of [Stacks, Tag 0FDK] given by the derived
tensor product `D_perf(𝒪_X) × D^b_Coh(𝒪_X) ⟶ D^b_Coh(𝒪_X)`
(`AlgebraicGeometry.exists_module_coherentKZero`).

## Main results

* `AlgebraicGeometry.ParityEulerClass.parityEulerClass_single`: `χ(ℱ[0]) = [ℱ]`.
* `AlgebraicGeometry.ParityEulerClass.addEquiv_parityEulerClass_eq_cls`: under the
  identification of [Stacks, Tag 0FDF], `χ(K) = [K]` for `K ∈ D^b_Coh(𝒪_X)`.
* `AlgebraicGeometry.ParityEulerClass.perfectCoherentSMul_eq_smul` and
  `AlgebraicGeometry.ParityEulerClass.exists_module_perfectCoherentSMul_eq_smul`:
  `perfectCoherentSMul` is the scalar multiplication of the module structure of
  `AlgebraicGeometry.exists_module_coherentKZero`.

## References

* [Stacks Project, Tag 0FDF](https://stacks.math.columbia.edu/tag/0FDF)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.ParityEulerClass

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **The parity Euler class of a coherent module placed in degree `0` is its class.** -/
theorem parityEulerClass_single (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    parityEulerClass ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj) = KZero.mk _ F := by
  have hK := isLocallyBoundedCoherent_single F.obj
    (CoherentAbelian.isCoherent_of_stacksIsCoherent F.property)
  rw [parityEulerClass_eq hK]
  have hz₁ : IsZero (paritySum ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj) 1) :=
    isZero_sigma _ fun i =>
      ProperPushforwardKZero.isZero_homologyFunctor_obj_singleFunctor_obj F.obj _ (by omega)
  have hz₀ : ∀ i : ℤ, i ∉ ({0} : Set ℤ) → IsZero ((DerivedCategory.homologyFunctor X.Modules
      (2 * i + 0)).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj)) := fun i hi =>
    ProperPushforwardKZero.isZero_homologyFunctor_obj_singleFunctor_obj F.obj _ (by
      simp only [Set.mem_singleton_iff] at hi
      omega)
  have e₀ : paritySum ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj) 0 ≅ F.obj :=
    (sigmaSubtypeIsoOfIsZero _ ({0} : Set ℤ) hz₀).symm ≪≫ coproductUniqueIso _ ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app F.obj
  rw [KZero.mk_eq_zero_of_isZero (X := parityObject _ hK 1)
      (IsZero.of_full_of_faithful_of_isZero
        (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι _ hz₁), sub_zero]
  exact KZero.mk_eq_of_iso (ObjectProperty.isoMk _ e₀)

/-- An object of `D^b_Coh(𝒪_X)` has locally bounded coherent cohomology. -/
theorem isLocallyBoundedCoherent_of_boundedCoherent (K : DerivedCategory X.Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf) K) :
    IsLocallyBoundedCoherent K := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  refine ⟨fun n => CoherentAbelian.isCoherent_of_stacksIsCoherent (hc n), fun x =>
    ⟨Set.univ, Filter.univ_mem, (Set.finite_Icc a b).subset fun n hn => ?_⟩⟩
  by_contra hnot
  simp only [Set.mem_Icc, not_and_or, not_le] at hnot
  obtain ⟨y, hy, -⟩ := hn
  exact (supp_eq_empty_of_isZero (hnot.elim (ha n) (hb n))).le hy

/-- **The parity Euler class inverts the identification `K'₀(X) = K₀(D^b_Coh(𝒪_X))`.** For any
isomorphism `e` sending the class of a coherent module to the class of that module placed in
degree `0` — the identification of [Stacks, Tag 0FDF] — and every `K ∈ D^b_Coh(𝒪_X)`,
`e (χ K) = [K]`. -/
theorem addEquiv_parityEulerClass_eq_cls [IsLocallyNoetherian X]
    (e : CoherentKZero X ≃+ K0 (boundedCoherentAtScheme X).FullSubcategory)
    (hexists : ∀ G : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
      ∃ D : (boundedCoherentAtScheme X).FullSubcategory,
        Nonempty (D.obj ≅ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} X.ringCatSheaf) 0).obj G.obj))
    (hchar : ∀ (G : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
      (D : (boundedCoherentAtScheme X).FullSubcategory),
        (D.obj ≅ (DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj G.obj) →
          e (KZero.mk _ G) = K0.cls D)
    (K : (boundedCoherentAtScheme X).FullSubcategory) :
    e (parityEulerClass K.obj) = K0.cls K := by
  let ψ : K0 (boundedCoherentAtScheme X).FullSubcategory →+ CoherentKZero X :=
    QuotientAddGroup.lift _ (FreeAbelianGroup.lift fun D => parityEulerClass D.obj) fun a ha => by
      refine (AddSubgroup.closure_le (K := (FreeAbelianGroup.lift fun D :
        (boundedCoherentAtScheme X).FullSubcategory => parityEulerClass D.obj).ker)).2 ?_ ha
      rintro _ ⟨T, hT, rfl⟩
      have h₂ : parityEulerClass T.obj₂.obj =
          parityEulerClass T.obj₁.obj + parityEulerClass T.obj₃.obj :=
        parityEulerClass_obj₂ _ ((ObjectProperty.ι _).map_distinguished T hT)
          (isLocallyBoundedCoherent_of_boundedCoherent _ T.obj₁.property)
          (isLocallyBoundedCoherent_of_boundedCoherent _ T.obj₂.property)
          (isLocallyBoundedCoherent_of_boundedCoherent _ T.obj₃.property)
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of, h₂]
      abel
  have hψ : ∀ D : (boundedCoherentAtScheme X).FullSubcategory,
      ψ (K0.cls D) = parityEulerClass D.obj := fun D => by
    simp only [ψ, K0.cls]
    rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]
  have hcomp : ψ.comp e.toAddMonoidHom = AddMonoidHom.id _ := by
    refine KZero.hom_ext fun G => ?_
    obtain ⟨D, ⟨i⟩⟩ := hexists G
    change ψ (e (KZero.mk _ G)) = KZero.mk _ G
    rw [hchar G D i, hψ D, parityEulerClass_congr i]
    exact parityEulerClass_single G
  obtain ⟨y, hy⟩ := e.surjective (K0.cls K)
  have h : ψ (e y) = y := DFunLike.congr_fun hcomp y
  rw [hy, hψ K] at h
  rw [h, hy]

/-- **On a Noetherian scheme, `perfectCoherentSMul` is the module structure of
[Stacks, Tag 0FDK].** For every module structure `m` of `K'₀(X)` over `K₀(X)` and identification
`e : K'₀(X) ≅ K₀(D^b_Coh(𝒪_X))` with the properties of
`AlgebraicGeometry.exists_module_coherentKZero` — `e` sends the class of a coherent module to the
class of that module in degree `0`, and `e([P] • [ℱ]) = [P ⊗^𝐋 ℱ]` — the scalar multiplication of
`m` on classes is `perfectCoherentSMul`. -/
theorem perfectCoherentSMul_eq_smul [IsNoetherian X] :
    letI := (perfectTensorStructureScheme X).commRing
    ∀ (m : Module (K0 (perfectAtScheme X).FullSubcategory) (CoherentKZero X))
      (e : CoherentKZero X ≃+ K0 (boundedCoherentAtScheme X).FullSubcategory),
      (∀ G : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
        ∃ D : (boundedCoherentAtScheme X).FullSubcategory,
          Nonempty (D.obj ≅ (DerivedCategory.singleFunctor
            (SheafOfModules.{u} X.ringCatSheaf) 0).obj G.obj)) →
      (∀ (G : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
        (D : (boundedCoherentAtScheme X).FullSubcategory),
          (D.obj ≅ (DerivedCategory.singleFunctor
            (SheafOfModules.{u} X.ringCatSheaf) 0).obj G.obj) →
            e (KZero.mk _ G) = K0.cls D) →
      (∀ (K : (perfectAtScheme X).FullSubcategory)
        (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
        (L : (boundedCoherentAtScheme X).FullSubcategory)
        (_ : L.obj ≅ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} X.ringCatSheaf) 0).obj F.obj)
        (h : boundedCoherentAtScheme X (((TorFormula.derivedTensor X).obj K.obj).obj L.obj)),
          letI := m
          e (K0.cls K • KZero.mk _ F) =
            K0.cls (⟨((TorFormula.derivedTensor X).obj K.obj).obj L.obj, h⟩ :
              (boundedCoherentAtScheme X).FullSubcategory)) →
      ∀ (P : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X)
        (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf),
        letI := m
        perfectCoherentSMul X (K0.cls P) (KZero.mk _ F) =
          K0.cls (⟨P.obj, P.property⟩ : (perfectAtScheme X).FullSubcategory) •
            KZero.mk _ F := by
  intro m e hexists hchar hsmul P F
  obtain ⟨L, ⟨i⟩⟩ := hexists F
  have h : boundedCoherentAtScheme X (((TorFormula.derivedTensor X).obj P.obj).obj L.obj) :=
    derivedCategoryBBounded_coherentModules_derivedTensor_of_isPerfect X _ _ P.property L.property
  apply e.injective
  rw [hsmul ⟨P.obj, P.property⟩ F L i h, perfectCoherentSMul_cls_mk]
  exact (congrArg e (parityEulerClass_congr
    (((TorFormula.derivedTensor X).obj P.obj).mapIso i)).symm).trans
      (addEquiv_parityEulerClass_eq_cls e hexists hchar ⟨_, h⟩)

/-- **On a Noetherian scheme the product `perfectCoherentSMul` is the scalar multiplication of a
module structure of `K'₀(X)` over the Grothendieck ring `K₀(X)` of [Stacks, Tag 0FDK]**, namely the
one of `AlgebraicGeometry.exists_module_coherentKZero`. -/
theorem exists_module_perfectCoherentSMul_eq_smul [IsNoetherian X] :
    letI := (perfectTensorStructureScheme X).commRing
    ∃ m : Module (K0 (perfectAtScheme X).FullSubcategory) (CoherentKZero X),
      ∀ (P : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X)
        (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf),
        letI := m
        perfectCoherentSMul X (K0.cls P) (KZero.mk _ F) =
          K0.cls (⟨P.obj, P.property⟩ : (perfectAtScheme X).FullSubcategory) •
            KZero.mk _ F := by
  obtain ⟨m, e, h₁, h₂, h₃⟩ := exists_module_coherentKZero X
  exact ⟨m, perfectCoherentSMul_eq_smul m e h₁ h₂ h₃⟩

end AlgebraicGeometry.ParityEulerClass
