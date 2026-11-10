module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Basic
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedTensorSingle

/-!
# The top cohomology sheaf of a derived tensor product with a sheaf

Let `(C, J)` be a site, `Λ` a commutative ring and `K` an object of the derived category
`D(C, Λ)` of sheaves of `Λ`-modules lying in degrees `≤ b`. For a sheaf `N` of `Λ`-modules,
`K ⊗_Λ^L N[0]` lies in degrees `≤ b` (`Stacks.ModuleSheaf.isLE_tensor`) and its top cohomology
sheaf is `H^b(K ⊗_Λ^L N[0]) ≅ H^b(K) ⊗_Λ N`, naturally in `N`. More generally, for a complex `K`
vanishing above `b` and a bifunctor `T` right exact in its first variable,
`H^b(p ↦ T(K^p, M)) ≅ T(coker(K^{b-1} → K^b), M)`, naturally in `M`.

## Main definitions

* `CochainComplex.KFlatBifunctor.rowHomologyToOpcycles`: for a complex `K` vanishing above `b`
  and a bifunctor `T`, the comparison map `H^b(p ↦ T(K^p, M)) ⟶ T(coker(K^{b-1} → K^b), M)`.
* `CochainComplex.KFlatBifunctor.rowHomologyIsoOpcycles`: it is an isomorphism of functors of
  `M` when `T` is right exact in its first variable.

## Main results

* `Stacks.ModuleSheaf.nonempty_homology_tensor_single_natIso_of_isLE`: the functors
  `N ↦ H^b(K ⊗_Λ^L N[0])` and `N ↦ H^b(K) ⊗_Λ N` are isomorphic.
* `Stacks.ModuleSheaf.nonempty_homology_tensor_single_iso_of_isLE`: its value at one sheaf.
* `Stacks.ModuleSheaf.exists_distTriang_whiskerRight`: `- ⊗_Λ^L N` preserves distinguished
  triangles.
* `Stacks.ModuleSheaf.nonempty_singleFunctor_tensor_iso_shift`,
  `Stacks.ModuleSheaf.nonempty_homology_singleFunctor_tensor_iso`: a sheaf placed in degree `a`,
  tensored with an object, is the shift by `-a` of the same sheaf placed in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe t w v u

namespace CochainComplex.KFlatBifunctor

section TopDegree

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (T : A ⥤ B ⥤ D) [T.Additive] [∀ X, (T.obj X).Additive]
  (K : CochainComplex A ℤ) (b : ℤ)

omit [Abelian B] [∀ X, (T.obj X).Additive] in
/-- The image under `T(-, M)` of the projection `K^b ⟶ coker(K^{b-1} → K^b)` vanishes on the
image of the differential of the termwise complex `p ↦ T(K^p, M)`. -/
theorem rowComplex_d_comp_map_pOpcycles (M : B) :
    (rowComplex T K M).d (b - 1) b ≫ (T.map (K.pOpcycles b)).app M = 0 := by
  change (T.map (K.d (b - 1) b)).app M ≫ _ = 0
  rw [← NatTrans.comp_app, ← T.map_comp, K.d_pOpcycles, T.map_zero, NatTrans.app_zero]

/-- The map `coker(T(K^{b-1}, M) → T(K^b, M)) ⟶ T(coker(K^{b-1} → K^b), M)` induced by the
projection `K^b ⟶ coker(K^{b-1} → K^b)`. -/
def rowOpcyclesToOpcycles (M : B) :
    (rowComplex T K M).opcycles b ⟶ (T.obj (K.opcycles b)).obj M :=
  (rowComplex T K M).descOpcycles ((T.map (K.pOpcycles b)).app M) (b - 1) (by simp)
    (rowComplex_d_comp_map_pOpcycles T K b M)

omit [Abelian B] [∀ X, (T.obj X).Additive] in
/-- `rowOpcyclesToOpcycles` is induced by `T(K^b ⟶ coker(K^{b-1} → K^b), M)`. -/
@[reassoc (attr := simp)]
theorem p_rowOpcyclesToOpcycles (M : B) :
    (rowComplex T K M).pOpcycles b ≫ rowOpcyclesToOpcycles T K b M =
      (T.map (K.pOpcycles b)).app M :=
  HomologicalComplex.p_descOpcycles _ _ _ _ _

/-- The comparison map `H^b(p ↦ T(K^p, M)) ⟶ T(coker(K^{b-1} → K^b), M)`. -/
def rowHomologyToOpcycles (M : B) :
    (rowComplex T K M).homology b ⟶ (T.obj (K.opcycles b)).obj M :=
  (rowComplex T K M).homologyι b ≫ rowOpcyclesToOpcycles T K b M

/-- The comparison map `rowHomologyToOpcycles` as a natural transformation of functors of the
coefficients. -/
def rowHomologyToOpcyclesNatTrans :
    rowFunctor T K ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) b ⟶
      T.obj (K.opcycles b) where
  app M := rowHomologyToOpcycles T K b M
  naturality {M M'} g := by
    have h₁ := HomologicalComplex.homologyι_naturality (K := rowComplex T K M)
      (L := rowComplex T K M') (rowComplexMapRight T K g) b
    have h₂ : HomologicalComplex.opcyclesMap (rowComplexMapRight T K g) b ≫
        rowOpcyclesToOpcycles T K b M' =
          rowOpcyclesToOpcycles T K b M ≫ (T.obj (K.opcycles b)).map g := by
      rw [← cancel_epi ((rowComplex T K M).pOpcycles b), HomologicalComplex.p_opcyclesMap_assoc,
        p_rowOpcyclesToOpcycles, p_rowOpcyclesToOpcycles_assoc]
      exact (T.map (K.pOpcycles b)).naturality g
    change HomologicalComplex.homologyMap (rowComplexMapRight T K g) b ≫
        (rowComplex T K M').homologyι b ≫ rowOpcyclesToOpcycles T K b M' =
      ((rowComplex T K M).homologyι b ≫ rowOpcyclesToOpcycles T K b M) ≫ _
    rw [reassoc_of% h₁, h₂, Category.assoc]

variable [K.IsStrictlyLE b] [∀ M, PreservesFiniteColimits (T.flip.obj M)]

/-- The cokernel of `T(K^{b-1}, M) → T(K^b, M)` is `T(coker(K^{b-1} → K^b), M)` when `T` is
right exact in its first variable. -/
instance isIso_rowOpcyclesToOpcycles (M : B) : IsIso (rowOpcyclesToOpcycles T K b M) := by
  let hc := CokernelCofork.mapIsColimit _
    (K.opcyclesIsCokernel (b - 1) b (by simp)) (T.flip.obj M)
  obtain ⟨inv, hinv⟩ := CokernelCofork.IsColimit.desc' hc ((rowComplex T K M).pOpcycles b)
    ((rowComplex T K M).d_pOpcycles (b - 1) b)
  refine ⟨inv, ?_, Cofork.IsColimit.hom_ext hc ?_⟩
  · rw [← cancel_epi ((rowComplex T K M).pOpcycles b), p_rowOpcyclesToOpcycles_assoc,
      Category.comp_id]
    exact hinv
  · change (T.map (K.pOpcycles b)).app M ≫ _ = (T.map (K.pOpcycles b)).app M ≫ _
    rw [Category.comp_id, ← Category.assoc]
    exact (congrArg (· ≫ rowOpcyclesToOpcycles T K b M) hinv).trans
      (p_rowOpcyclesToOpcycles T K b M)

/-- In the top degree of a complex vanishing above `b`, the comparison map is invertible when
`T` is right exact in its first variable. -/
instance isIso_rowHomologyToOpcycles (M : B) : IsIso (rowHomologyToOpcycles T K b M) := by
  have : IsIso ((rowComplex T K M).homologyι b) :=
    (rowComplex T K M).isIso_homologyι b (b + 1) (by simp)
      (((T.flip.obj M).map_isZero (K.isZero_of_isStrictlyLE b (b + 1) (by lia))).eq_of_tgt _ _)
  dsimp only [rowHomologyToOpcycles]
  infer_instance

/-- The comparison `rowHomologyToOpcyclesNatTrans` is an isomorphism of functors. -/
instance isIso_rowHomologyToOpcyclesNatTrans : IsIso (rowHomologyToOpcyclesNatTrans T K b) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    (fun M => isIso_rowHomologyToOpcycles T K b M)

/-- **The top cohomology of a termwise complex.** For a complex `K` vanishing above `b` and a
bifunctor `T` which is right exact in its first variable, `H^b(p ↦ T(K^p, M))` is
`T(coker(K^{b-1} → K^b), M)`, naturally in `M`. -/
def rowHomologyIsoOpcycles :
    rowFunctor T K ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) b ≅
      T.obj (K.opcycles b) :=
  asIso (rowHomologyToOpcyclesNatTrans T K b)

end TopDegree

end CochainComplex.KFlatBifunctor

namespace Stacks.ModuleSheaf

open CochainComplex.KFlatBifunctor

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type w} [CommRing Λ] [UnivLE.{max u v, w}]
  [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]

/-- Tensoring with a fixed sheaf of `Λ`-modules on the right is right exact. -/
instance preservesFiniteColimits_curriedTensor_flip_obj (N : Sheaf J (ModuleCat.{w} Λ)) :
    PreservesFiniteColimits ((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).flip.obj N) :=
  inferInstanceAs (PreservesFiniteColimits (tensorRight N))

/-- **The top cohomology of a derived tensor product with a sheaf**, as functors of the sheaf:
if `K` lies in degrees `≤ b`, then `N ↦ H^b(K ⊗_Λ^L N[0])` is isomorphic to
`N ↦ H^b(K) ⊗_Λ N`. -/
theorem nonempty_homology_tensor_single_natIso_of_isLE
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (b : ℤ) [K.IsLE b] :
    Nonempty (DerivedCategory.singleFunctor _ 0 ⋙ tensorLeft K ⋙
        DerivedCategory.homologyFunctor _ b ≅
      tensorLeft ((DerivedCategory.homologyFunctor _ b).obj K)) := by
  obtain ⟨F, hF, hFLE, ⟨eF⟩⟩ := exists_kFlat_isStrictlyLE_representative K b
  have hP := CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ (kFlat_of_isStrictlyLE F b hF)
  let T := curriedTensor (Sheaf J (ModuleCat.{w} Λ))
  exact ⟨Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
      (Functor.isoWhiskerRight ((curriedTensor _).mapIso eF.symm)
        (DerivedCategory.homologyFunctor _ b)) ≪≫
    Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ _ 0)
      (tensorLeft (DerivedCategory.Q.obj F) ⋙ DerivedCategory.homologyFunctor _ b) ≪≫
    Functor.isoWhiskerRight (derivedTensorSingleIso hP) (DerivedCategory.homologyFunctor _ b) ≪≫
    Functor.isoWhiskerLeft (rowFunctor T F) (DerivedCategory.homologyFunctorFactors _ b) ≪≫
    rowHomologyIsoOpcycles T F b ≪≫
    T.mapIso ((F.isoHomologyι b (b + 1) (by simp)
        ((F.isZero_of_isStrictlyLE b (b + 1) (by lia)).eq_of_tgt _ _)).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors _ b).app F).symm ≪≫
      (DerivedCategory.homologyFunctor _ b).mapIso eF)⟩

/-- **The top cohomology of a derived tensor product with a sheaf**: if `K` lies in degrees
`≤ b`, then `H^b(K ⊗_Λ^L N[0]) ≅ H^b(K) ⊗_Λ N`. -/
theorem nonempty_homology_tensor_single_iso_of_isLE
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (b : ℤ) [K.IsLE b]
    (N : Sheaf J (ModuleCat.{w} Λ)) :
    Nonempty ((DerivedCategory.homologyFunctor _ b).obj
        (K ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
      (DerivedCategory.homologyFunctor _ b).obj K ⊗ N) := by
  obtain ⟨e⟩ := nonempty_homology_tensor_single_natIso_of_isLE K b
  exact ⟨e.app N⟩

/-- **Tensoring a distinguished triangle on the right** with an object of `D(C, Λ)` gives a
distinguished triangle. -/
theorem exists_distTriang_whiskerRight
    (T : Pretriangulated.Triangle (DerivedCategory (Sheaf J (ModuleCat.{w} Λ))))
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (N : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    ∃ δ : T.obj₃ ⊗ N ⟶ (T.obj₁ ⊗ N)⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk (T.mor₁ ▷ N) (T.mor₂ ▷ N) δ ∈
        Pretriangulated.distinguishedTriangles := by
  obtain ⟨s, hs⟩ := exists_commShift_isTriangulated_tensorRight J Λ N
  exact ⟨_, (tensorRight N).map_distinguished T hT⟩

/-- **A sheaf placed in degree `a`, tensored with an object**: `F[-a] ⊗_Λ^L M` is
`(F[0] ⊗_Λ^L M)[-a]`. -/
theorem nonempty_singleFunctor_tensor_iso_shift (F : Sheaf J (ModuleCat.{w} Λ))
    (M : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (a : ℤ) :
    Nonempty ((DerivedCategory.singleFunctor _ a).obj F ⊗ M ≅
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗ M)⟦-a⟧) := by
  obtain ⟨s, -⟩ := exists_commShift_isTriangulated_tensorRight J Λ M
  exact ⟨whiskerRightIso
      (((DerivedCategory.singleFunctors _).shiftIso (-a) a 0 (by lia)).app F).symm M ≪≫
    ((tensorRight M).commShiftIso (-a)).app _⟩

/-- **The cohomology of a sheaf placed in degree `a`, tensored with an object**:
`Hⁿ(F[-a] ⊗_Λ^L M) ≅ H^{n-a}(F[0] ⊗_Λ^L M)`. -/
theorem nonempty_homology_singleFunctor_tensor_iso (F : Sheaf J (ModuleCat.{w} Λ))
    (M : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (a n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ a).obj F ⊗ M) ≅
      (DerivedCategory.homologyFunctor _ (n - a)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗ M)) := by
  obtain ⟨e⟩ := nonempty_singleFunctor_tensor_iso_shift F M a
  exact ⟨(DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
    ((DerivedCategory.homologyFunctor _ 0).shiftIso (-a) n (n - a) (by lia)).app _⟩

end Stacks.ModuleSheaf

end
