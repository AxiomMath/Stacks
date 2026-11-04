module

public import StacksFrontier.CategoryTheory.Functor.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex

/-!
# The degree-zero cohomology of a derived tensor product of two modules

Let `(C, O)` be a ringed site and let `A` and `B` be sheaves of `O`-modules. The canonical map

`A[0] ⊗^𝐋_O B[0] ⟶ Tot(A[0] ⊗_O B[0])`

of [Stacks, Tag 06YU] from the derived to the ordinary total tensor product induces an isomorphism
on cohomology in degree zero: `H⁰(A ⊗^𝐋 B) = A ⊗_O B`. This is the degree-zero case of the
identification of `H^{-i}(A ⊗^𝐋 B)` with `Tor_i(A, B)`, and it holds because the tensor product
is right exact.

## Main results

* `HomologicalComplex.isIso_homologyMap_mapHomologicalComplex_zero`: a right exact functor
  applied degreewise to a morphism of complexes vanishing in positive degrees preserves the
  property of inducing an isomorphism on cohomology in degree zero.
* `Stacks.DerivedTensor.RingedSite.isIso_homologyMap_toTensor_single`: the canonical map
  `A[0] ⊗^𝐋 B[0] ⟶ Tot(A[0] ⊗ B[0])` is an isomorphism on cohomology in degree zero.

## Implementation notes

Resolve `A[0]` by a complex `F` of flat modules vanishing in positive degrees, by
[Stacks, Tag 05T7]; it is K-flat by [Stacks, Tag 06YQ], so the canonical map at `F` is
invertible, and by naturality the canonical map at `A[0]` is invertible on `H⁰` exactly when
`Tot(F ⊗ B[0]) ⟶ Tot(A[0] ⊗ B[0])` is. That map is `- ⊗ B` applied degreewise to the resolution
`F ⟶ A[0]`, and on complexes vanishing in positive degrees the cohomology in degree zero is a
cokernel, which the right exact `- ⊗ B` preserves.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace HomologicalComplex

variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B] (G : A ⥤ B)
  [G.Additive] [PreservesFiniteColimits G]

/-- **A right exact functor preserves the cohomology in degree zero of a complex vanishing in
positive degrees**, compatibly with morphisms: if `f : K ⟶ L` induces an isomorphism on `H⁰`,
so does `G` applied degreewise to `f`. In degree zero such a complex has zero outgoing
differential, so its cohomology is the cokernel of the incoming one, which `G` preserves. -/
lemma isIso_homologyMap_mapHomologicalComplex_zero {K L : CochainComplex A ℤ} (f : K ⟶ L)
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] [IsIso (homologyMap f 0)] :
    IsIso (homologyMap ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) 0) := by
  have key (M : CochainComplex A ℤ) [M.IsStrictlyLE 0] : G.PreservesLeftHomologyOf (M.sc 0) :=
    G.preservesLeftHomology_of_zero_g (M.sc 0)
      ((M.isZero_of_isStrictlyLE 0 _ (by simp)).eq_of_tgt _ _)
  have := key K
  have := key L
  have e : homologyMap ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) 0 ≫
      ((L.sc 0).mapHomologyIso G).hom = ((K.sc 0).mapHomologyIso G).hom ≫
        G.map (homologyMap f 0) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor A (ComplexShape.up ℤ) 0).map f) G
  have : IsIso (homologyMap ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) 0 ≫
      ((L.sc 0).mapHomologyIso G).hom) := by
    rw [e]
    have h2 : IsIso (G.map (homologyMap f 0)) := inferInstance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) (by convert h2 using 0; exact Iff.rfl)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom _) this

end HomologicalComplex

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Modules R)]

/-- **`H⁰(A[0] ⊗^𝐋 B[0]) = A ⊗ B`**: the canonical map from the derived tensor product of two
modules placed in degree zero to their total tensor complex is an isomorphism on cohomology in
degree zero. -/
theorem isIso_homologyMap_toTensor_single (T : DerivedTensorProduct R) (A B : Modules R) :
    IsIso ((DerivedCategory.homologyFunctor (Modules R) 0).map
      (T.toTensor ((CochainComplex.singleFunctor (Modules R) 0).obj A)
        ((CochainComplex.singleFunctor (Modules R) 0).obj B))) := by
  let H0 := DerivedCategory.homologyFunctor (Modules R) 0
  let sA := (CochainComplex.singleFunctor (Modules R) 0).obj A
  let sB := (CochainComplex.singleFunctor (Modules R) 0).obj B
  let G := (Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj B
  obtain ⟨L, s, hs, hLflat, hLE⟩ := (CochainComplex.exists_quasiIso_prop (flatModules R)
    (fun M => by
      obtain ⟨N, π, hflat, hepi⟩ :=
        Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat R M
      exact ⟨N, hflat, π, hepi⟩) 0).2 sA
  have hL : Stacks.SheafOfModules.KFlat.KFlat R L :=
    Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat R L ⟨0, hLE⟩ hLflat
  have nat := T.toTensor_naturality s (𝟙 sB)
  have hQs : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  -- the map of total complexes is `- ⊗ B` applied to `s`, up to isomorphism
  let m := HomologicalComplex.mapBifunctorMap s (𝟙 sB)
    (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)
  have hm : m = (HomologicalComplex.mapBifunctorSingleRightIso _ L B).hom ≫
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map s ≫
        (HomologicalComplex.mapBifunctorSingleRightIso _ sA B).inv := by
    rw [← HomologicalComplex.mapBifunctorSingleRightIso_hom_naturality_assoc, Iso.hom_inv_id,
      Category.comp_id]
  have : IsIso (HomologicalComplex.homologyMap s 0) := inferInstance
  have hG : IsIso (HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map s) 0) :=
    HomologicalComplex.isIso_homologyMap_mapHomologicalComplex_zero G s
  have hH0m : IsIso (H0.map (DerivedCategory.Q.map m)) := by
    have : IsIso (HomologicalComplex.homologyMap m 0) := by
      rw [hm, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
      infer_instance
    exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors (Modules R) 0) m).2 this
  have hrhs : IsIso (H0.map (T.toTensor L sB ≫ DerivedCategory.Q.map m)) := by
    rw [Functor.map_comp, T.toTensor_eq_comparisonLeft L sB hL]
    exact IsIso.comp_isIso' inferInstance hH0m
  have hlhs : IsIso (H0.map
      ((T.tensor.map (DerivedCategory.Q.map s)).app (DerivedCategory.Q.obj sB) ≫
      (T.tensor.obj (DerivedCategory.Q.obj sA)).map (DerivedCategory.Q.map (𝟙 sB)) ≫
        T.toTensor sA sB)) := by
    rwa [nat]
  rw [Functor.map_comp, Functor.map_comp] at hlhs
  have : IsIso (H0.map ((T.tensor.obj (DerivedCategory.Q.obj sA)).map
      (DerivedCategory.Q.map (𝟙 sB)))) := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    infer_instance
  have h1 := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance hlhs
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ this h1

section NatTrans

attribute [local instance] CategoryTheory.Functor.flip_obj_additive

variable (T : DerivedTensorProduct R) (B : Modules R)

/-- The canonical map from the derived tensor product to the total tensor complex, read at the
complexes concentrated in degree zero, as a natural transformation in the first module. -/
def toTensorSingleNatTrans :
    (CochainComplex.singleFunctor (Modules R) 0 ⋙ DerivedCategory.Q) ⋙
        T.tensor.flip.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj B)) ⟶
      CochainComplex.singleFunctor (Modules R) 0 ⋙
        (Stacks.SheafOfModules.Tensor.tensorComplex R).flip.obj
          ((CochainComplex.singleFunctor (Modules R) 0).obj B) ⋙ DerivedCategory.Q where
  app A := T.toTensor ((CochainComplex.singleFunctor (Modules R) 0).obj A)
    ((CochainComplex.singleFunctor (Modules R) 0).obj B)
  naturality {A A'} φ := by
    have h := T.toTensor_naturality ((CochainComplex.singleFunctor (Modules R) 0).map φ)
      (𝟙 ((CochainComplex.singleFunctor (Modules R) 0).obj B))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h

/-- `Tot(A[0] ⊗ B[0])` is `(A ⊗ B)[0]`, naturally in `A`. -/
def totSingleIso :
    CochainComplex.singleFunctor (Modules R) 0 ⋙
        (Stacks.SheafOfModules.Tensor.tensorComplex R).flip.obj
          ((CochainComplex.singleFunctor (Modules R) 0).obj B) ⋙ DerivedCategory.Q ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj B ⋙
        DerivedCategory.singleFunctor (Modules R) 0 :=
  NatIso.ofComponents (G := CochainComplex.singleFunctor (Modules R) 0 ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj B).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (fun A => DerivedCategory.Q.mapIso (HomologicalComplex.mapBifunctorSingleRightIso
        (Stacks.SheafOfModules.Tensor.sheafTensor R)
        ((CochainComplex.singleFunctor (Modules R) 0).obj A) B))
      (fun {A A'} φ => by
        have h := HomologicalComplex.mapBifunctorSingleRightIso_hom_naturality
          (Stacks.SheafOfModules.Tensor.sheafTensor R)
          ((CochainComplex.singleFunctor (Modules R) 0).obj A) B
          ((CochainComplex.singleFunctor (Modules R) 0).map φ)
        exact (DerivedCategory.Q.map_comp _ _).symm.trans
          ((congrArg DerivedCategory.Q.map h).trans (DerivedCategory.Q.map_comp _ _))) ≪≫
    Functor.isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj B) (ComplexShape.up ℤ) 0)
        DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj B)
      (DerivedCategory.singleFunctorIsoCompQ _ 0).symm

/-- **The canonical map `A[0] ⊗^𝐋 B[0] ⟶ (A ⊗ B)[0]`**, natural in `A`: the canonical map of
[Stacks, Tag 06YU] from the derived to the total tensor product, followed by the identification
of the total tensor product of two complexes concentrated in degree zero. -/
def tensorSingleNatTrans :
    DerivedCategory.singleFunctor (Modules R) 0 ⋙
        T.tensor.flip.obj ((DerivedCategory.singleFunctor (Modules R) 0).obj B) ⟶
      (Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj B ⋙
        DerivedCategory.singleFunctor (Modules R) 0 :=
  (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ _ 0) _ ≪≫
      Functor.isoWhiskerLeft _ (T.tensor.flip.mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app B))).hom ≫
    toTensorSingleNatTrans R T B ≫ (totSingleIso R B).hom

/-- **The canonical map `A[0] ⊗^𝐋 B[0] ⟶ (A ⊗ B)[0]` is an isomorphism on `H⁰`.** -/
theorem isIso_homologyMap_tensorSingleNatTrans_app (A : Modules R) :
    IsIso ((DerivedCategory.homologyFunctor (Modules R) 0).map
      ((tensorSingleNatTrans R T B).app A)) := by
  have := isIso_homologyMap_toTensor_single R T A B
  simp only [tensorSingleNatTrans, NatTrans.comp_app, Functor.map_comp]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this inferInstance)

end NatTrans

end Stacks.DerivedTensor.RingedSite

end
