module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.MatrixActionDerived
public import StacksFrontier.Algebra.Homology.MatrixActionTensor
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution
public import StacksFrontier.Homology.Perfect.DerivedTensorFibre
public import StacksFrontier.Homology.PseudoCoherent.Coherent

/-!
# The derived fibre of a pseudo-coherent complex, from tensoring with finite free complexes

Let `A` be a commutative ring, `p` a prime of `A` whose residue field `κ(p)` is a pseudo-coherent
`A`-module (for instance any prime of a Noetherian ring), and `M` a pseudo-coherent object of
`D(A)`.  Let `R → κ(p)` be a resolution by a bounded above complex of finite free `A`-modules
with chosen bases, that is a complex of `Mat_ (SingleObj A)`.  The degree-`i` cohomology of the
derived fibre `M ⊗^L_A κ(p)` vanishes as soon as the degree-`i` cohomology of `M ⊗_A σ^{≥k}R`
does, for `k` small enough compared to `i`, where `σ^{≥k}R` is the stupid truncation and
`- ⊗_A σ^{≥k}R` is `CategoryTheory.MatrixAction.derivedTot`.

## Main definitions

* `CategoryTheory.MatrixAction.realizeModule`: the finite free `A`-module `A^ι` on a basis `ι`.
* `CategoryTheory.MatrixAction.liftComplex`: a complex whose terms are in the essential image of
  a fully faithful functor, lifted along it.

## Main results

* `CategoryTheory.MatrixAction.exists_realizeModule_iso`: a complex of finite free modules is
  the realization of a complex of matrices.
* `CategoryTheory.MatrixAction.fibreCohomologyVanishes_of_resolution`: for a resolution `R` of
  `κ(p)` by finite free modules and `M` represented by a complex strictly bounded above by `b`,
  `H^i(M ⊗_A σ^{≥k}R) = 0` with `b + k < i` gives
  `StacksDraft.Perfect.FibreCohomologyVanishes p M i`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace CategoryTheory.MatrixAction

section Lift

variable {B C : Type*} [Category B] [Category C] [Preadditive B] [Preadditive C]
  (F : B ⥤ C) [F.Additive] (hF : F.FullyFaithful)

/-- A cochain complex of `C` whose terms are, up to chosen isomorphisms, images of objects of `B`
under a fully faithful additive functor, lifted to a cochain complex of `B`. -/
def liftComplex (E : CochainComplex C ℤ) (X : ℤ → B) (e : ∀ n, F.obj (X n) ≅ E.X n) :
    CochainComplex B ℤ where
  X := X
  d n m := hF.preimage ((e n).hom ≫ E.d n m ≫ (e m).inv)
  shape n m h := hF.map_injective (by rw [E.shape n m h]; simp)
  d_comp_d' n m l _ _ := hF.map_injective (by simp)

/-- The image of the lifted complex is the original complex. -/
def liftComplexIso (E : CochainComplex C ℤ) (X : ℤ → B) (e : ∀ n, F.obj (X n) ≅ E.X n) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (liftComplex F hF E X e) ≅ E :=
  HomologicalComplex.Hom.isoOfComponents e fun n m _ => by
    simp [liftComplex]

end Lift

variable (A : Type u) [CommRing A]

/-- The finite free `A`-module `A^ι` on the basis `ι`, as a functor out of
`Mat_ (SingleObj A)`. -/
abbrev realizeModule : Mat_ (SingleObj A) ⥤ ModuleCat.{u} A :=
  realize A (𝟙_ (ModuleCat.{u} A))

/-- The morphism of `Mat_ (SingleObj A)` with given entries. -/
def ofEntries {M N : Mat_ (SingleObj A)} (c : M.ι → N.ι → A) : M ⟶ N := c

/-- The entries of `ofEntries A c` are given by `c`. -/
@[simp]
lemma entry_ofEntries {M N : Mat_ (SingleObj A)} (c : M.ι → N.ι → A) (i : M.ι) (j : N.ι) :
    entry A (ofEntries A c) i j = c i j := rfl

/-- An endomorphism of `A` as an `A`-module is multiplication by its value at `1`. -/
lemma moduleCat_unit_hom_eq_smul (f : 𝟙_ (ModuleCat.{u} A) ⟶ 𝟙_ (ModuleCat.{u} A)) :
    f = (show A from f.hom (1 : A)) • 𝟙 _ := by
  ext
  change f.hom (1 : A) = (f.hom (1 : A)) • (1 : A)
  rw [smul_eq_mul, mul_one]

/-- The functor `realizeModule A` is faithful. -/
instance : (realizeModule A).Faithful where
  map_injective {M N f g} h := by
    refine Mat_.hom_ext _ _ fun i j => ?_
    have h' := congrArg (fun φ => biproduct.ι _ i ≫ φ ≫ biproduct.π _ j) h
    simp only [ι_realizeMap_π] at h'
    have := congrArg (fun φ : 𝟙_ (ModuleCat.{u} A) ⟶ 𝟙_ _ => φ.hom (1 : A)) h'
    simpa using this

/-- The functor `realizeModule A` is full. -/
instance : (realizeModule A).Full where
  map_surjective {M N} φ := by
    refine ⟨ofEntries A fun i j =>
      (biproduct.ι (fun _ : M.ι => 𝟙_ (ModuleCat.{u} A)) i ≫ φ ≫
        biproduct.π (fun _ : N.ι => 𝟙_ (ModuleCat.{u} A)) j).hom (1 : A), ?_⟩
    refine realize_hom_ext A fun i j => ?_
    change biproduct.ι _ i ≫ realizeMap A _ _ ≫ biproduct.π _ j = _
    rw [ι_realizeMap_π, entry_ofEntries]
    exact (moduleCat_unit_hom_eq_smul A _).symm

/-- `A^ι` as a fully faithful functor out of `Mat_ (SingleObj A)`. -/
def realizeModuleFullyFaithful : (realizeModule A).FullyFaithful :=
  .ofFullyFaithful _

/-- A finite free module is isomorphic to `A^ι` for some finite `ι`. -/
lemma exists_realizeModule_obj_iso (P : ModuleCat.{u} A) [Module.Finite A P] [Module.Free A P] :
    ∃ M : Mat_ (SingleObj A), Nonempty ((realizeModule A).obj M ≅ P) := by
  classical
  let b := (Module.Free.chooseBasis A P).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex A P))
  exact ⟨⟨Fin (Fintype.card (Module.Free.ChooseBasisIndex A P)), fun _ => ⟨⟩⟩,
    ⟨ModuleCat.biproductIsoPi _ ≪≫ LinearEquiv.toModuleIso b.equivFun.symm⟩⟩

/-- **A complex of finite free modules is the realization of a complex of matrices.** -/
theorem exists_realizeModule_iso (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (hE : ∀ n, Module.Finite A (E.X n) ∧ Module.Free A (E.X n)) :
    ∃ Q : CochainComplex (Mat_ (SingleObj A)) ℤ,
      Nonempty (((realizeModule A).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ≅ E) := by
  choose X e using fun n => @exists_realizeModule_obj_iso A _ (E.X n) (hE n).1 (hE n).2
  exact ⟨liftComplex _ (realizeModuleFullyFaithful A) E X fun n => (e n).some,
    ⟨liftComplexIso _ _ _ _ _⟩⟩

section Fibre

open StacksDraft.PseudoCoherence

/-- The stupid truncation `σ^{≥k}R` of a complex strictly bounded above by `c` is strictly
bounded above by `c`. -/
instance isStrictlyLE_stupidTrunc {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    (R : CochainComplex C ℤ) (c k : ℤ) [R.IsStrictlyLE c] :
    CochainComplex.IsStrictlyLE (R.stupidTrunc (ComplexShape.embeddingUpIntGE k)) c := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  by_cases hk : k ≤ n
  · exact (R.isZero_of_isStrictlyLE c n hn).of_iso
      (R.stupidTruncXIso (ComplexShape.embeddingUpIntGE k) (i := (n - k).toNat)
        (by change k + ((n - k).toNat : ℤ) = n; omega))
  · exact R.isZero_stupidTrunc_X _ n
      ((ComplexShape.notMem_range_embeddingUpIntGE_iff k n).2 (by omega))

/-- Tensoring a complex `P` strictly bounded above by `b` with the inclusion `σ^{≥k}R ⟶ R` is an
isomorphism in every total degree `≥ b + k`. -/
lemma isIso_mapBifunctorMap_ιStupidTrunc_f (P : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] (R : CochainComplex (Mat_ (SingleObj A)) ℤ) (k n : ℤ) (hn : b + k ≤ n) :
    IsIso ((HomologicalComplex.mapBifunctorMap (𝟙 P)
      (R.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (matrixAction A)
        (ComplexShape.up ℤ)).f n) := by
  refine StacksDraft.TotalComplexQuasiIso.isIso_total_map_f _ n fun p q hpq => ?_
  by_cases hq : k ≤ q
  · have := HomologicalComplex.isIso_ιStupidTrunc_f R (ComplexShape.embeddingUpIntGE k)
      (i := (q - k).toNat) (by change k + ((q - k).toNat : ℤ) = q; omega)
    change IsIso (((matrixAction A).map (𝟙 (P.X p))).app _ ≫
      ((matrixAction A).obj (P.X p)).map ((R.ιStupidTrunc _).f q))
    rw [Functor.map_id, NatTrans.id_app, Category.id_comp]
    exact Functor.map_isIso _ _
  · exact StacksDraft.TotalComplexQuasiIso.isIso_of_isZero_of_isZero _
      (((matrixAction A).flip.obj _).map_isZero (P.isZero_of_isStrictlyLE b p (by omega)))
      (((matrixAction A).flip.obj _).map_isZero (P.isZero_of_isStrictlyLE b p (by omega)))

attribute [local instance] HasDerivedCategory.standard

/-- A complex whose class in `D(A)` is a module placed in degree `0` has no cohomology off
degree `0`. -/
lemma isZero_homology_of_iso_single (E : CochainComplex (ModuleCat.{u} A) ℤ) (N : ModuleCat.{u} A)
    (e : DerivedCategory.Q.obj E ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)
    (j : ℤ) (hj : j ≠ 0) : IsZero (E.homology j) := by
  have h0 : IsZero ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj N
      |>.homology j) :=
    HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 N j hj
  have e' : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj N) :=
    e ≪≫ (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app N
  exact h0.of_iso ((DerivedCategory.homologyFunctorFactors _ j).symm.app E ≪≫
    (DerivedCategory.homologyFunctor _ j).mapIso e' ≪≫
    (DerivedCategory.homologyFunctorFactors _ j).app _)

/-- A bounded above complex of finite free modules is K-flat. -/
private theorem kFlat_of_isBoundedAboveFiniteFree {X : CochainComplex (ModuleCat.{u} A) ℤ}
    (hX : IsBoundedAboveFiniteFree X) : X.KFlat := by
  obtain ⟨d, _⟩ := hX.upperBound
  have : ∀ n : ℤ, Module.Flat A (X.X n) := fun n => by
    have := (hX.finiteFree n).2
    exact Module.Flat.of_free
  exact CochainComplex.KFlat.kFlat_of_flat.{u, u} X d

/-- **The derived fibre from tensoring with truncated free resolutions.**  Let `p` be a prime of
`A`, and `R` a bounded above complex of finite free `A`-modules with chosen bases, strictly
bounded above by `c`, whose realization resolves the residue field `κ(p)`.  Let `M ∈ D(A)` be
represented by a bounded above complex `P` of finite free modules strictly bounded above by `b`.
If `b + k < i` and `H^i(M ⊗_A σ^{≥k}R) = 0`, then the derived fibre `M ⊗^L_A κ(p)` has no
cohomology in degree `i`. -/
theorem fibreCohomologyVanishes_of_resolution (p : Ideal A) [p.IsPrime]
    (R : CochainComplex (Mat_ (SingleObj A)) ℤ) (c : ℤ) [R.IsStrictlyLE c]
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : IsBoundedAboveFiniteFree E)
    (eR : ((realizeModule A).mapHomologicalComplex (ComplexShape.up ℤ)).obj R ≅ E)
    (eE : DerivedCategory.Q.obj E ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A p.ResidueField))
    (M : DerivedCategory (ModuleCat.{u} A)) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : IsBoundedAboveFiniteFree P) (eP : DerivedCategory.Q.obj P ≅ M) (b : ℤ)
    [P.IsStrictlyLE b] (i k : ℤ) (hik : b + k < i)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((derivedTot A (R.stupidTrunc (ComplexShape.embeddingUpIntGE k)) k c).obj M))) :
    StacksDraft.Perfect.FibreCohomologyVanishes.{u, u} p M i := by
  refine
    StacksDraft.Perfect.fibreCohomologyVanishes_of_isZero_homology_derivedTensor_single_residueField
      p M ⟨P, hP, ⟨eP⟩⟩ i ?_
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let Qk := R.stupidTrunc (ComplexShape.embeddingUpIntGE k)
  have hT : ∀ (X : ModuleCat.{u} A) (a : A),
      ((curriedTensor (ModuleCat.{u} A)).obj X).map (a • 𝟙 (𝟙_ (ModuleCat.{u} A))) =
        a • 𝟙 _ := fun X a => by
    change X ◁ (a • 𝟙 _) = _
    rw [MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id]
    rfl
  have hiso : IsIso (HomologicalComplex.homologyMap (HomologicalComplex.mapBifunctorMap (𝟙 P)
      (R.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (matrixAction A)
        (ComplexShape.up ℤ)) i) :=
    StacksDraft.StupidTruncation.isIso_homologyMap_of_isIso_f_prev_next _ i
      (isIso_mapBifunctorMap_ιStupidTrunc_f A P b R k _ (by simp; omega))
      (isIso_mapBifunctorMap_ιStupidTrunc_f A P b R k _ (by omega))
      (isIso_mapBifunctorMap_ιStupidTrunc_f A P b R k _ (by simp; omega))
  have h₁ : IsZero (((tot A Qk).obj P).homology i) :=
    h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (derivedTotObjIso A Qk k c eP) ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app _).symm
  have h₂ : IsZero (((tot A R).obj P).homology i) :=
    h₁.of_iso (@asIso _ _ _ _ _ hiso).symm
  have h₃ : IsZero ((P ⊗ E).homology i) :=
    h₂.of_iso (HomologicalComplex.homologyMapIso
      ((MonoidalCategory.whiskerLeftIso P eR.symm) ≪≫
        mapBifunctorTensorRealizeIso A (curriedTensor (ModuleCat.{u} A)) (𝟙_ _)
          (rightUnitorNatIso _) hT P R) i)
  refine h₃.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    ((T.tensor.mapIso eP.symm).app _ ≪≫ (T.tensor.obj _).mapIso eE.symm ≪≫
      T.comparison P E (kFlat_of_isBoundedAboveFiniteFree A hP)
        (kFlat_of_isBoundedAboveFiniteFree A hE)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _)

end Fibre

end CategoryTheory.MatrixAction

end
