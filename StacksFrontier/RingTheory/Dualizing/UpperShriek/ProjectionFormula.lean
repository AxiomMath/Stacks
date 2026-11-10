module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# The projection formula for a ring homomorphism, in the derived category

Let `φ : A →+* B` be a homomorphism of commutative rings, write `i_*` for derived restriction of
scalars `D(B) ⥤ D(A)` and `- ⊗_A^L B` for derived extension of scalars.  For `N` in `D(A)` and
`F` in `D(B)` there is a canonical isomorphism

`i_*(F ⊗_B^L (N ⊗_A^L B)) ≅ i_*F ⊗_A^L N`,

natural in `F` **and** in `N`.  This file proves it, for the derived tensor products of the
canonical tensor--Hom adjunction `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` of
[Stacks, Tag 0A63] and for an arbitrary total left derived model of extension of scalars.

## Main definitions

* `Dualizing.ProjectionFormula.chainProjNatIso` — the chain-level projection formula
  `L ⊗_B (P ⊗_A B) ≅ L ⊗_A P` of [Stacks, Tag 06Y6], as a natural isomorphism in the complex `L`
  of `B`-modules.
* `Dualizing.ProjectionFormula.derivedTensorRightNatIso` — K-flat representatives compute the
  derived tensor product with a fixed K-flat complex, naturally in the other variable.
* `Dualizing.ProjectionFormula.derivedProjKFlat` — the projection formula at a K-flat
  representative of `N`, and `derivedProjKFlatChain_naturality` its naturality in that
  representative.
* `Dualizing.ProjectionFormula.derivedProjBifunctorNatIso` — the projection formula as an
  isomorphism of bifunctors `D(A) ⥤ (D(B) ⥤ D(A))`, for an arbitrary left adjoint of
  `RHom_A(B, -)`.
* `Dualizing.ProjectionFormula.derivedProjNatIso` — its value at an object `N` of `D(A)`.

## Implementation notes: naturality in `N`

Naturality in `N` is what makes [Stacks, Tag 0E9L] functorial, and it cannot be read off a
resolution chosen separately for each `N`.  Both chain-level halves are available: the
comparison `CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso` is natural in the
complex of `A`-modules and `chainProjNatIso` is natural in the complex of `B`-modules.  The
derived tensor comparison is made natural in both representatives by
`derivedTensor_comparison_naturality`, which upgrades the former `..._naturality_left`; the
five legs are then pasted into `derivedProjKFlatChain_naturality`, naturality of the projection
formula at K-flat representatives in the `A`-complex.  The descent to all of `D(A)` is
`ModuleSystemRlimTensor.natIsoOfResolutions`, applied with the K-flat complexes as resolving
class and the functor category `D(B) ⥤ D(A)` as target: a family of isomorphisms on the
resolving class, natural in chain maps between its members, determines an isomorphism of
functors on `D(A)`, so nothing is chosen object by object.

## Implementation notes

The chain-level comparison is
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso`, which the library already proves
natural in the complex of `A`-modules; the missing half, naturality in the complex of
`B`-modules, is `Dualizing.ProjectionFormula.baseChange_tensor_isoX_naturality_left`, checked on
each antidiagonal summand of the total complex against
`CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso_natural_left`.

Passing to the derived category needs the K-flat comparison of
`CochainComplex.DerivedTensor.derivedTensor_comparison` to be natural in its first
representative; that is `derivedTensor_comparison_naturality_left`, obtained by pasting the
naturality of the scalar transport, of the transported tensor comparison over the lifted ring,
and of the tensor comparison of `StacksDraft.DerivedHom.DerivedHomData` itself.

The descent from complexes to `D(B)` is `Localization.liftNatIso`: all five comparisons making
up the projection formula are natural in the complex of `B`-modules with no K-flatness
hypothesis on it, so the composite is an isomorphism of functors on cochain complexes and
descends. Only `N` has to be resolved, and
`TotalDerivedExtensionScalars.comparison_isIso_of_kFlat` computes its derived base change on
that resolution.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace Dualizing.ProjectionFormula

open CochainComplex CochainComplex.DerivedTensor CochainComplex.KFlat.ScalarBaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Pasting five commuting squares along a ladder: the top row composed after the left-hand
vertical equals the bottom row composed before the right-hand vertical.  The projection formula
is a composite of five comparisons, so each of its naturality statements is this pasting. -/
private theorem comp_ladder_five {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ B₂ B₃ B₄ B₅ : C}
    (t : A₀ ⟶ B₀)
    (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄) (a₅ : A₄ ⟶ A₅)
    (b₁ : B₀ ⟶ B₁) (b₂ : B₁ ⟶ B₂) (b₃ : B₂ ⟶ B₃) (b₄ : B₃ ⟶ B₄) (b₅ : B₄ ⟶ B₅)
    (v₁ : A₁ ⟶ B₁) (v₂ : A₂ ⟶ B₂) (v₃ : A₃ ⟶ B₃) (v₄ : A₄ ⟶ B₄) (v₅ : A₅ ⟶ B₅)
    (s₁ : t ≫ b₁ = a₁ ≫ v₁) (s₂ : v₁ ≫ b₂ = a₂ ≫ v₂) (s₃ : v₂ ≫ b₃ = a₃ ≫ v₃)
    (s₄ : v₃ ≫ b₄ = a₄ ≫ v₄) (s₅ : v₄ ≫ b₅ = a₅ ≫ v₅) :
    t ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ b₅ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅) ≫ v₅ := by
  simp only [Category.assoc]
  rw [reassoc_of% s₁, reassoc_of% s₂, reassoc_of% s₃, reassoc_of% s₄, s₅]

/-- Pasting four commuting squares along a ladder. -/
private theorem comp_ladder_four {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : C}
    (t : A₀ ⟶ B₀)
    (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄)
    (b₁ : B₀ ⟶ B₁) (b₂ : B₁ ⟶ B₂) (b₃ : B₂ ⟶ B₃) (b₄ : B₃ ⟶ B₄)
    (v₁ : A₁ ⟶ B₁) (v₂ : A₂ ⟶ B₂) (v₃ : A₃ ⟶ B₃) (v₄ : A₄ ⟶ B₄)
    (s₁ : t ≫ b₁ = a₁ ≫ v₁) (s₂ : v₁ ≫ b₂ = a₂ ≫ v₂) (s₃ : v₂ ≫ b₃ = a₃ ≫ v₃)
    (s₄ : v₃ ≫ b₄ = a₄ ≫ v₄) :
    t ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ v₄ := by
  simp only [Category.assoc]
  rw [reassoc_of% s₁, reassoc_of% s₂, reassoc_of% s₃, s₄]

/-- Right tensoring by a fixed complex acts on the antidiagonal summand `K^i ⊗ N^j` by the
given map on `K^i` and the identity on `N^j`. -/
lemma ι_trightCochain_map
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
    [∀ K L : CochainComplex C ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)]
    [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]
    (N : CochainComplex C ℤ) {K L : CochainComplex C ℤ} (g : K ⟶ L)
    (i j n : ℤ) (h : i + j = n) :
    GradedObject.Monoidal.ιTensorObj K.X N.X i j n h ≫ ((TrightCochain N).map g).f n =
      (g.f i ▷ N.X j) ≫ GradedObject.Monoidal.ιTensorObj L.X N.X i j n h := by
  have h0 : HomologicalComplex.ιTensorObj K N i j n h ≫ ((TrightCochain N).map g).f n =
      (g.f i ▷ N.X j) ≫ HomologicalComplex.ιTensorObj L N i j n h := by
    change HomologicalComplex.ιMapBifunctor K N (curriedTensor C) (.up ℤ) i j n h ≫
      (HomologicalComplex.mapBifunctorMap g (𝟙 N) (curriedTensor C) (.up ℤ)).f n = _
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp
  exact h0

/-- The chain-level projection formula, degreewise, is natural in the complex of `B`-modules:
the comparison on one antidiagonal summand. -/
lemma baseChange_tensor_isoX_naturality_left (φ : A →+* B)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    {L L' : CochainComplex (ModuleCat.{max u v} B) ℤ} (g : L ⟶ L') (n i j : ℤ)
    (h : i + j = n) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, v}
    letI : MonoidalCategory (ModuleCat.{max u v} A) :=
      ModuleCat.liftedModuleMonoidal.{u, v}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} B) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, v}
    letI : MonoidalCategory (ModuleCat.{max u v} B) :=
      ModuleCat.liftedModuleMonoidal.{u, v}
    (ModuleCat.restrictScalars.{max u v} φ).map
          (GradedObject.Monoidal.ιTensorObj L.X
            ((extendScalarsLarge.{v, u, u} φ).obj P).X i j n h) ≫
        ((ModuleCat.restrictScalars.{max u v} φ).map
            (((TrightCochain ((extendScalarsLarge.{v, u, u} φ).obj P)).map g).f n) ≫
          (baseChange_tensor_isoX.{u, u, v} φ P L' n).hom) =
      (ModuleCat.restrictScalars.{max u v} φ).map
          (GradedObject.Monoidal.ιTensorObj L.X
            ((extendScalarsLarge.{v, u, u} φ).obj P).X i j n h) ≫
        ((baseChange_tensor_isoX.{u, u, v} φ P L n).hom ≫
          ((TrightCochain P).map ((restrictScalarsLarge.{v, u, u} φ).map g)).f n) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v} A) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, v}
  let : MonoidalCategory (ModuleCat.{max u v} A) :=
    ModuleCat.liftedModuleMonoidal.{u, v}
  let : MonoidalCategoryStruct (ModuleCat.{max u v} B) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, v}
  let : MonoidalCategory (ModuleCat.{max u v} B) :=
    ModuleCat.liftedModuleMonoidal.{u, v}
  have hι : GradedObject.Monoidal.ιTensorObj L.X
          ((extendScalarsLarge.{v, u, u} φ).obj P).X i j n h ≫
        ((TrightCochain ((extendScalarsLarge.{v, u, u} φ).obj P)).map g).f n =
      (g.f i ▷ ((extendScalarsLarge.{v, u, u} φ).obj P).X j) ≫
        GradedObject.Monoidal.ιTensorObj L'.X
          ((extendScalarsLarge.{v, u, u} φ).obj P).X i j n h :=
    ι_trightCochain_map _ g i j n h
  have hι2 : GradedObject.Monoidal.ιTensorObj
          ((restrictScalarsLarge.{v, u, u} φ).obj L).X P.X i j n h ≫
        ((TrightCochain P).map ((restrictScalarsLarge.{v, u, u} φ).map g)).f n =
      ((ModuleCat.restrictScalars.{max u v} φ).map (g.f i) ▷ P.X j) ≫
        GradedObject.Monoidal.ιTensorObj
          ((restrictScalarsLarge.{v, u, u} φ).obj L').X P.X i j n h :=
    ι_trightCochain_map P _ i j n h
  have hXL : (ModuleCat.restrictScalars.{max u v} φ).map
          (GradedObject.Monoidal.ιTensorObj L.X
            ((extendScalarsLarge.{v, u, u} φ).obj P).X i j n h) ≫
        (baseChange_tensor_isoX.{u, u, v} φ P L n).hom =
      (projectionFormulaIso.{u, u, v} φ (L.X i) (P.X j)).hom ≫
        GradedObject.Monoidal.ιTensorObj
          ((restrictScalarsLarge.{v, u, u} φ).obj L).X P.X i j n h :=
    baseChange_tensor_isoX_hom_ι.{u, u, v} φ P L n i j h
  have hXL' : (ModuleCat.restrictScalars.{max u v} φ).map
          (GradedObject.Monoidal.ιTensorObj L'.X
            ((extendScalarsLarge.{v, u, u} φ).obj P).X i j n h) ≫
        (baseChange_tensor_isoX.{u, u, v} φ P L' n).hom =
      (projectionFormulaIso.{u, u, v} φ (L'.X i) (P.X j)).hom ≫
        GradedObject.Monoidal.ιTensorObj
          ((restrictScalarsLarge.{v, u, u} φ).obj L').X P.X i j n h :=
    baseChange_tensor_isoX_hom_ι.{u, u, v} φ P L' n i j h
  have hnat : (ModuleCat.restrictScalars.{max u v} φ).map
          (g.f i ▷ ((extendScalarsLarge.{v, u, u} φ).obj P).X j) ≫
        (projectionFormulaIso.{u, u, v} φ (L'.X i) (P.X j)).hom =
      (projectionFormulaIso.{u, u, v} φ (L.X i) (P.X j)).hom ≫
        ((ModuleCat.restrictScalars.{max u v} φ).map (g.f i) ▷ P.X j) :=
    projectionFormulaIso_natural_left.{u, u, v} φ (P.X j) (g.f i)
  erw [← Category.assoc, ← Functor.map_comp, hι, Functor.map_comp, Category.assoc, hXL',
    reassoc_of% hnat, Category.assoc, ← hι2, reassoc_of% hXL, Category.assoc]
  rfl

/-- **The chain-level projection formula, as a natural isomorphism of functors.** For a ring
homomorphism `φ : A →+* B` and a complex `P` of `A`-modules, the underlying complex of
`A`-modules of `L ⊗_B (P ⊗_A B)` is `L ⊗_A P`, naturally in the complex `L` of `B`-modules. -/
noncomputable def chainProjNatIso (φ : A →+* B)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    tensorRightLarge.{u, v} ((extendScalarsLarge.{v, u, u} φ).obj P) ⋙
        restrictScalarsLarge.{v, u, u} φ ≅
      restrictScalarsLarge.{v, u, u} φ ⋙ tensorRightLarge.{u, v} P :=
  NatIso.ofComponents (fun L => baseChange_tensor_iso.{u, u, v} φ P L) (by
    intro L L' g
    ext n : 1
    let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
    let Z := ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{max u v} B)) ℤ ℤ).obj
      L.X).obj ((extendScalarsLarge.{v, u, u} φ).obj P).X
    apply (isColimitOfPreserves (ModuleCat.restrictScalars.{max u v} φ)
      (Z.isColimitCofanMapObj p n)).hom_ext
    rintro ⟨⟨i, j⟩, (h : i + j = n)⟩
    exact baseChange_tensor_isoX_naturality_left.{u, v} φ P g n i j h)

attribute [local instance] HasDerivedCategory.standard

/-- Degreewise restriction of scalars along `ULift.ringEquiv.symm`, on cochain complexes. -/
noncomputable abbrev uliftComplexes (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{max u v} R) ℤ ⥤
      CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ :=
  (StacksDraft.DerivedHom.uliftModuleEquivalence.{u, max u v, v} R).inverse.mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- **Naturality in both representatives of the K-flat comparison** for the derived tensor
product of the canonical tensor--Hom adjunction.  Both K-flat factors may move: this is what
makes the projection formula descend to `D(A)` without choosing a resolution. -/
lemma derivedTensor_comparison_naturality (R : Type u) [CommRing R]
    {K K' : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : K ⟶ K')
    {N N' : CochainComplex (ModuleCat.{max u v} R) ℤ} (g : N ⟶ N')
    (hN : IsKFlat.{u, v} N) (hN' : IsKFlat.{u, v} N') :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} R).tensor.map
          (X := (DerivedCategory.Q.obj K, DerivedCategory.Q.obj N))
          (Y := (DerivedCategory.Q.obj K', DerivedCategory.Q.obj N'))
          (DerivedCategory.Q.map f, DerivedCategory.Q.map g) ≫
        (derivedTensor_comparison.{u, v} R K' N' hN').hom =
      (derivedTensor_comparison.{u, v} R K N hN).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f g
          (moduleTensor.{u, v} R) (ComplexShape.up ℤ)) := by
  let D := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} R
  let EF := (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} R).functor
  let DU := StacksDraft.DerivedHom.derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)
  let UI := StacksDraft.DerivedHom.derivedTensorULiftIso.{u, v, max u v + 1} R
  let EC := uliftComplexes.{u, v} R
  let K₀ := EC.obj K
  let K₀' := EC.obj K'
  let N₀ := EC.obj N
  let N₀' := EC.obj N'
  let f₀ : DerivedCategory.Q.obj K₀ ⟶ DerivedCategory.Q.obj K₀' :=
    DerivedCategory.Q.map (EC.map f)
  let g₀ : DerivedCategory.Q.obj N₀ ⟶ DerivedCategory.Q.obj N₀' :=
    DerivedCategory.Q.map (EC.map g)
  have hN₀ : CochainComplex.KFlat N₀ :=
    isKFlat_restrictScalars_of_ringEquiv (ULift.ringEquiv.{u, v} (R := R)) N hN
  have hN₀' : CochainComplex.KFlat N₀' :=
    isKFlat_restrictScalars_of_ringEquiv (ULift.ringEquiv.{u, v} (R := R)) N' hN'
  -- The three legs of the comparison: the scalar transport of the two representatives, the
  -- transported tensor comparison over the lifted ring, and the scalar transport of the total
  -- tensor product.
  have hdef : ∀ (X Y : CochainComplex (ModuleCat.{max u v} R) ℤ) (hY : IsKFlat.{u, v} Y)
      (hY₀ : CochainComplex.KFlat (EC.obj Y)),
      (derivedTensor_comparison.{u, v} R X Y hY).hom =
        D.tensor.map ((scalarEquivalenceQObjIso.{u, v} R X).inv,
            (scalarEquivalenceQObjIso.{u, v} R Y).inv) ≫
          ((UI.hom.app (DerivedCategory.Q.obj (EC.obj X), DerivedCategory.Q.obj (EC.obj Y)) ≫
              EF.map (DU.tensorIso (EC.obj X) (EC.obj Y) hY₀).hom) ≫
            (scalarEquivalenceTensorComplexIso.{u, v} R X Y).hom) := fun _ _ _ _ => rfl
  have hS1 : D.tensor.map
          (X := (DerivedCategory.Q.obj K, DerivedCategory.Q.obj N))
          (Y := (DerivedCategory.Q.obj K', DerivedCategory.Q.obj N'))
          (DerivedCategory.Q.map f, DerivedCategory.Q.map g) ≫
        D.tensor.map ((scalarEquivalenceQObjIso.{u, v} R K').inv,
          (scalarEquivalenceQObjIso.{u, v} R N').inv) =
      D.tensor.map ((scalarEquivalenceQObjIso.{u, v} R K).inv,
          (scalarEquivalenceQObjIso.{u, v} R N).inv) ≫
        D.tensor.map
          (X := (EF.obj (DerivedCategory.Q.obj K₀), EF.obj (DerivedCategory.Q.obj N₀)))
          (Y := (EF.obj (DerivedCategory.Q.obj K₀'), EF.obj (DerivedCategory.Q.obj N₀')))
          (EF.map f₀, EF.map g₀) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg D.tensor.map (Prod.ext ?_ ?_)
    · exact scalarEquivalenceQObjIso_inv_naturality.{u, v} R f
    · exact scalarEquivalenceQObjIso_inv_naturality.{u, v} R g
  have hS2 : D.tensor.map
          (X := (EF.obj (DerivedCategory.Q.obj K₀), EF.obj (DerivedCategory.Q.obj N₀)))
          (Y := (EF.obj (DerivedCategory.Q.obj K₀'), EF.obj (DerivedCategory.Q.obj N₀')))
          (EF.map f₀, EF.map g₀) ≫
        UI.hom.app (DerivedCategory.Q.obj K₀', DerivedCategory.Q.obj N₀') =
      UI.hom.app (DerivedCategory.Q.obj K₀, DerivedCategory.Q.obj N₀) ≫
        EF.map (DU.tensor.map
          (X := (DerivedCategory.Q.obj K₀, DerivedCategory.Q.obj N₀))
          (Y := (DerivedCategory.Q.obj K₀', DerivedCategory.Q.obj N₀'))
          (f₀, g₀)) := by
    have h := UI.hom.naturality
      (show (DerivedCategory.Q.obj K₀, DerivedCategory.Q.obj N₀) ⟶
          (DerivedCategory.Q.obj K₀', DerivedCategory.Q.obj N₀') from (f₀, g₀))
    simpa using h
  have hS3 : EF.map (DU.tensor.map
            (X := (DerivedCategory.Q.obj K₀, DerivedCategory.Q.obj N₀))
            (Y := (DerivedCategory.Q.obj K₀', DerivedCategory.Q.obj N₀'))
            (f₀, g₀)) ≫
        EF.map (DU.tensorIso K₀' N₀' hN₀').hom =
      EF.map (DU.tensorIso K₀ N₀ hN₀).hom ≫
        EF.map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (EC.map f)
          (EC.map g) (moduleTensor.{max u v, 0} (ULift.{v} R)) (ComplexShape.up ℤ))) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg EF.map (DU.tensorIso_naturality (EC.map f) (EC.map g) hN₀ hN₀')
  have hS4 : EF.map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (EC.map f)
            (EC.map g) (moduleTensor.{max u v, 0} (ULift.{v} R)) (ComplexShape.up ℤ))) ≫
        (scalarEquivalenceTensorComplexIso.{u, v} R K' N').hom =
      (scalarEquivalenceTensorComplexIso.{u, v} R K N).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f g
          (moduleTensor.{u, v} R) (ComplexShape.up ℤ)) :=
    scalarEquivalenceTensorComplexIso_naturality.{u, v} R f g
  rw [hdef K N hN hN₀, hdef K' N' hN' hN₀']
  exact (Category.assoc _ _ _).symm.trans
    ((CategoryTheory.eq_whisker hS1 _).trans
      ((Category.assoc _ _ _).trans
        ((CategoryTheory.whisker_eq _
            ((Category.assoc _ _ _).symm.trans
              ((CategoryTheory.eq_whisker (Category.assoc _ _ _).symm _).trans
                ((CategoryTheory.eq_whisker (CategoryTheory.eq_whisker hS2 _) _).trans
                  ((CategoryTheory.eq_whisker (Category.assoc _ _ _) _).trans
                    ((CategoryTheory.eq_whisker (CategoryTheory.whisker_eq _ hS3) _).trans
                      ((CategoryTheory.eq_whisker (Category.assoc _ _ _).symm _).trans
                        ((Category.assoc _ _ _).trans
                          ((CategoryTheory.whisker_eq _ hS4).trans
                            (Category.assoc _ _ _).symm))))))))).trans
          (Category.assoc _ _ _).symm)))

/-- Naturality in the first representative of the K-flat comparison for the derived tensor
product of the canonical tensor--Hom adjunction. -/
lemma derivedTensor_comparison_naturality_left (R : Type u) [CommRing R]
    {K K' : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : K ⟶ K')
    (N : CochainComplex (ModuleCat.{max u v} R) ℤ) (hN : CochainComplex.KFlat.{u, v} N) :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} R).tensor.map
          (X := (DerivedCategory.Q.obj K, DerivedCategory.Q.obj N))
          (Y := (DerivedCategory.Q.obj K', DerivedCategory.Q.obj N))
          (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj N)) ≫
        (derivedTensor_comparison.{u, v} R K' N hN).hom =
      (derivedTensor_comparison.{u, v} R K N hN).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f (𝟙 N)
          (moduleTensor.{u, v} R) (ComplexShape.up ℤ)) := by
  have h := derivedTensor_comparison_naturality.{u, v} R f (𝟙 N) hN hN
  rwa [CategoryTheory.Functor.map_id] at h

/-- Tensoring on the right with a fixed object of the derived category, for the canonical
tensor--Hom adjunction of [Stacks, Tag 0A63]. -/
noncomputable abbrev tensorRightDerived (R : Type u) [CommRing R]
    (M : DerivedCategory (ModuleCat.{max u v} R)) :
    DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R) :=
  (Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
    max u v + 1} R).tensor).flip.obj M

/-- **K-flat representatives compute the derived tensor product, naturally.** Tensoring with a
fixed K-flat complex on the right, read on the derived category, agrees with the total tensor
product of complexes. -/
noncomputable def derivedTensorRightNatIso (R : Type u) [CommRing R]
    (N : CochainComplex (ModuleCat.{max u v} R) ℤ) (hN : CochainComplex.KFlat.{u, v} N) :
    DerivedCategory.Q ⋙ tensorRightDerived.{u, v} R (DerivedCategory.Q.obj N) ≅
      tensorRightLarge.{u, v} N ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun X => derivedTensor_comparison.{u, v} R X N hN)
    (fun f => derivedTensor_comparison_naturality_left.{u, v} R f N hN)

/-- Extension of scalars preserves K-flatness, in the universe-independent form; this is
[Stacks, Tag 06Y1]. -/
lemma isKFlat_extendScalarsLarge (φ : A →+* B)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P) :
    IsKFlat.{u, v} ((extendScalarsLarge.{v, u, u} φ).obj P) :=
  CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, v} φ P hP

/-- **The projection formula on complexes of `B`-modules, at a K-flat `P`.** The five
comparisons composing the projection formula, read on cochain complexes of `B`-modules, where
each of them is natural with no K-flatness hypothesis on that variable. -/
noncomputable def derivedProjKFlatChain (φ : A →+* B)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P) :
    DerivedCategory.Q ⋙ (tensorRightDerived.{u, v} B
          (DerivedCategory.Q.obj ((extendScalarsLarge.{v, u, u} φ).obj P)) ⋙
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory) ≅
      DerivedCategory.Q ⋙ ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⋙
        tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
        (derivedTensorRightNatIso.{u, v} B _ (isKFlat_extendScalarsLarge.{u, v} φ P hP))
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (chainProjNatIso.{u, v} φ P) DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedTensorRightNatIso.{u, v} A P hP).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.symm _ ≪≫
    Functor.associator _ _ _

/-- The five legs of `Dualizing.ProjectionFormula.derivedProjKFlatChain`, read at a complex
`L` of `B`-modules. -/
lemma derivedProjKFlatChain_hom_app (φ : A →+* B)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P)
    (L : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    (derivedProjKFlatChain.{u, v} φ P hP).hom.app L =
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          (derivedTensor_comparison.{u, v} B L ((extendScalarsLarge.{v, u, u} φ).obj P)
            (isKFlat_extendScalarsLarge.{u, v} φ P hP)).hom ≫
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app
            ((tensorRightLarge.{u, v} ((extendScalarsLarge.{v, u, u} φ).obj P)).obj L) ≫
          DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, v} φ P L).hom ≫
            (derivedTensor_comparison.{u, v} A
              ((restrictScalarsLarge.{v, u, u} φ).obj L) P hP).inv ≫
              (tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P)).map
                ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.inv.app L) := by
  have h : (derivedProjKFlatChain.{u, v} φ P hP).hom.app L =
      𝟙 _ ≫ (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          (derivedTensor_comparison.{u, v} B L ((extendScalarsLarge.{v, u, u} φ).obj P)
            (isKFlat_extendScalarsLarge.{u, v} φ P hP)).hom ≫
        𝟙 _ ≫ (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app
            ((tensorRightLarge.{u, v} ((extendScalarsLarge.{v, u, u} φ).obj P)).obj L) ≫
          𝟙 _ ≫ DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, v} φ P L).hom ≫
            𝟙 _ ≫ (derivedTensor_comparison.{u, v} A
              ((restrictScalarsLarge.{v, u, u} φ).obj L) P hP).inv ≫
              𝟙 _ ≫ (tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P)).map
                ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.inv.app L) ≫
                𝟙 _ := rfl
  rw [h]
  simp only [Category.id_comp, Category.comp_id]

/-- **The chain-level projection formula is natural in the complex over `A` as well.** For a
chain map `f : P ⟶ P'` between K-flat complexes of `A`-modules the two sides of the projection
formula are exchanged compatibly with `f`, at every complex `L` of `B`-modules.  This is the
half the library was missing, and the reason the descent below needs no choice of resolution. -/
lemma derivedProjKFlatChain_naturality (φ : A →+* B)
    {P P' : CochainComplex (ModuleCat.{max u v} A) ℤ} (f : P ⟶ P')
    (hP : IsKFlat.{u, v} P) (hP' : IsKFlat.{u, v} P')
    (L : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.map
            (X := (DerivedCategory.Q.obj L,
              DerivedCategory.Q.obj ((extendScalarsLarge.{v, u, u} φ).obj P)))
            (Y := (DerivedCategory.Q.obj L,
              DerivedCategory.Q.obj ((extendScalarsLarge.{v, u, u} φ).obj P')))
            (𝟙 (DerivedCategory.Q.obj L),
              DerivedCategory.Q.map ((extendScalarsLarge.{v, u, u} φ).map f))) ≫
        (derivedProjKFlatChain.{u, v} φ P' hP').hom.app L =
      (derivedProjKFlatChain.{u, v} φ P hP).hom.app L ≫
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            (DerivedCategory.Q.obj L), DerivedCategory.Q.obj P))
          (Y := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            (DerivedCategory.Q.obj L), DerivedCategory.Q.obj P'))
          (𝟙 ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            (DerivedCategory.Q.obj L)), DerivedCategory.Q.map f) := by
  rw [derivedProjKFlatChain_hom_app, derivedProjKFlatChain_hom_app]
  have h1 : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.map
            (X := (DerivedCategory.Q.obj L,
              DerivedCategory.Q.obj ((extendScalarsLarge.{v, u, u} φ).obj P)))
            (Y := (DerivedCategory.Q.obj L,
              DerivedCategory.Q.obj ((extendScalarsLarge.{v, u, u} φ).obj P')))
            (𝟙 (DerivedCategory.Q.obj L),
              DerivedCategory.Q.map ((extendScalarsLarge.{v, u, u} φ).map f))) ≫
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          (derivedTensor_comparison.{u, v} B L ((extendScalarsLarge.{v, u, u} φ).obj P')
            (isKFlat_extendScalarsLarge.{u, v} φ P' hP')).hom =
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          (derivedTensor_comparison.{u, v} B L ((extendScalarsLarge.{v, u, u} φ).obj P)
            (isKFlat_extendScalarsLarge.{u, v} φ P hP)).hom ≫
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 L)
            ((extendScalarsLarge.{v, u, u} φ).map f) (moduleTensor.{u, v} B)
            (ComplexShape.up ℤ))) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map ?_
    have h := derivedTensor_comparison_naturality.{u, v} B (𝟙 L)
      ((extendScalarsLarge.{v, u, u} φ).map f)
      (isKFlat_extendScalarsLarge.{u, v} φ P hP)
      (isKFlat_extendScalarsLarge.{u, v} φ P' hP')
    simpa using h
  have h2 : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 L)
            ((extendScalarsLarge.{v, u, u} φ).map f) (moduleTensor.{u, v} B)
            (ComplexShape.up ℤ))) ≫
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app
          ((tensorRightLarge.{u, v} ((extendScalarsLarge.{v, u, u} φ).obj P')).obj L) =
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app
          ((tensorRightLarge.{u, v} ((extendScalarsLarge.{v, u, u} φ).obj P)).obj L) ≫
        DerivedCategory.Q.map ((restrictScalarsLarge.{v, u, u} φ).map
          (HomologicalComplex.mapBifunctorMap (𝟙 L)
            ((extendScalarsLarge.{v, u, u} φ).map f) (moduleTensor.{u, v} B)
            (ComplexShape.up ℤ))) :=
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.naturality
      (HomologicalComplex.mapBifunctorMap (𝟙 L)
        ((extendScalarsLarge.{v, u, u} φ).map f) (moduleTensor.{u, v} B) (ComplexShape.up ℤ))
  have h3 : DerivedCategory.Q.map ((restrictScalarsLarge.{v, u, u} φ).map
          (HomologicalComplex.mapBifunctorMap (𝟙 L)
            ((extendScalarsLarge.{v, u, u} φ).map f) (moduleTensor.{u, v} B)
            (ComplexShape.up ℤ))) ≫
        DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, v} φ P' L).hom =
      DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, v} φ P L).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          (𝟙 ((restrictScalarsLarge.{v, u, u} φ).obj L)) f (moduleTensor.{u, v} A)
          (ComplexShape.up ℤ)) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map
        (baseChange_tensor_iso_naturality.{u, u, v} φ f L)).trans
          (DerivedCategory.Q.map_comp _ _))
  have h4 : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          (𝟙 ((restrictScalarsLarge.{v, u, u} φ).obj L)) f (moduleTensor.{u, v} A)
          (ComplexShape.up ℤ)) ≫
        (derivedTensor_comparison.{u, v} A
          ((restrictScalarsLarge.{v, u, u} φ).obj L) P' hP').inv =
      (derivedTensor_comparison.{u, v} A
          ((restrictScalarsLarge.{v, u, u} φ).obj L) P hP).inv ≫
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (X := (DerivedCategory.Q.obj ((restrictScalarsLarge.{v, u, u} φ).obj L),
            DerivedCategory.Q.obj P))
          (Y := (DerivedCategory.Q.obj ((restrictScalarsLarge.{v, u, u} φ).obj L),
            DerivedCategory.Q.obj P'))
          (𝟙 (DerivedCategory.Q.obj ((restrictScalarsLarge.{v, u, u} φ).obj L)),
            DerivedCategory.Q.map f) := by
    have h := derivedTensor_comparison_naturality.{u, v} A
      (𝟙 ((restrictScalarsLarge.{v, u, u} φ).obj L)) f hP hP'
    rw [CategoryTheory.Functor.map_id] at h
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  have h5 := (((Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
      max u v + 1} A).tensor).flip.map (DerivedCategory.Q.map f)).naturality
      ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.inv.app L)).symm
  exact comp_ladder_five _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5

/-- **The projection formula in the derived category, at a K-flat representative.** For a ring
homomorphism `φ : A →+* B` and a K-flat complex `P` of `A`-modules, derived restriction of
scalars carries `- ⊗_B^L (P ⊗_A B)` to `- ⊗_A^L P`. -/
noncomputable def derivedProjKFlat (φ : A →+* B)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P) :
    tensorRightDerived.{u, v} B
          (DerivedCategory.Q.obj ((extendScalarsLarge.{v, u, u} φ).obj P)) ⋙
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⋙
        tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} B) (ComplexShape.up ℤ)) _ _ _ _
    (derivedProjKFlatChain.{u, v} φ P hP)

/-- The projection formula at a K-flat representative is the descent of its chain-level form:
at a localized complex the two agree. -/
lemma derivedProjKFlat_hom_app_Q (φ : A →+* B)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P)
    (L : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    (derivedProjKFlat.{u, v} φ P hP).hom.app (DerivedCategory.Q.obj L) =
      (derivedProjKFlatChain.{u, v} φ P hP).hom.app L := by
  simp [derivedProjKFlat, Localization.liftNatIso, Localization.liftNatTrans_app]

/-- The naturality of `Dualizing.ProjectionFormula.derivedProjKFlat` in the K-flat complex `P`,
on all of `D(B)`: by uniqueness of transformations descending along the localization functor it
follows from the chain-level statement `derivedProjKFlatChain_naturality`. -/
lemma derivedProjKFlat_naturality (φ : A →+* B)
    {P P' : CochainComplex (ModuleCat.{max u v} A) ℤ} (f : P ⟶ P')
    (hP : IsKFlat.{u, v} P) (hP' : IsKFlat.{u, v} P') :
    Functor.whiskerRight
          ((Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
              max u v + 1} B).tensor).flip.map
            (DerivedCategory.Q.map ((extendScalarsLarge.{v, u, u} φ).map f)))
          (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ≫
        (derivedProjKFlat.{u, v} φ P' hP').hom =
      (derivedProjKFlat.{u, v} φ P hP).hom ≫
        Functor.whiskerLeft (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory
          ((Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
            max u v + 1} A).tensor).flip.map (DerivedCategory.Q.map f)) := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} B) (ComplexShape.up ℤ)) (fun L => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    derivedProjKFlat_hom_app_Q]
  exact derivedProjKFlatChain_naturality.{u, v} φ f hP hP' L

/-- Any left adjoint of derived coextension of scalars is derived restriction of scalars: the
comparison provided by [Stacks, Tag 0A70] and uniqueness of adjoints. -/
noncomputable def leftAdjointIsoRestrictScalarsDerived (φ : A →+* B)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) :
    iStar ≅ (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory :=
  adj.leftAdjointUniq (Dualizing.restrictScalarsDerived_adj_derivedHom.{u, v, u} φ).some

/-- The left-hand side of the projection formula as a functor of `N`, valued in functors of
`F`: `N ↦ (F ↦ i_*(F ⊗_B^L (N ⊗_A^L B)))`. -/
noncomputable def projLeftBifunctor (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A)) :
    DerivedCategory (ModuleCat.{max u v} A) ⥤
      (DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A)) :=
  E.functor ⋙
    (Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
      max u v + 1} B).tensor).flip ⋙
    (Functor.whiskeringRight _ _ _).obj iStar

/-- The right-hand side of the projection formula as a functor of `N`, valued in functors of
`F`: `N ↦ (F ↦ i_*F ⊗_A^L N)`. -/
noncomputable def projRightBifunctor
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A)) :
    DerivedCategory (ModuleCat.{max u v} A) ⥤
      (DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A)) :=
  (Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
      max u v + 1} A).tensor).flip ⋙
    (Functor.whiskeringLeft _ _ _).obj iStar

/-- The projection formula at the localization of a K-flat complex, with **no choice of
resolution**: the derived base change of `Q(P)` is computed by the comparison of the model `E`
at `P`, which is invertible because `P` is K-flat. -/
noncomputable def derivedProjKFlatRep (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P) :
    (projLeftBifunctor.{u, v} φ E iStar).obj (DerivedCategory.Q.obj P) ≅
      (projRightBifunctor.{u, v} iStar).obj (DerivedCategory.Q.obj P) :=
  Functor.isoWhiskerRight
      ((Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} B).tensor).flip.mapIso
        (@asIso _ _ _ _ (E.comparison.app P)
          (E.comparison_isIso_of_kFlat P ((isKFlat_iff_kFlat P).mp hP)))) iStar ≪≫
    Functor.isoWhiskerLeft _ (leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj) ≪≫
    derivedProjKFlat.{u, v} φ P hP ≪≫
    Functor.isoWhiskerRight (leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj).symm
      (tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P))

/-- The family `Dualizing.ProjectionFormula.derivedProjKFlatRep` is natural in chain maps
between K-flat complexes of `A`-modules: the comparison of the model `E` is a natural
transformation, the identification of `iStar` with restriction of scalars does not depend on
`P`, and the projection formula at a K-flat representative is natural in `P` by
`derivedProjKFlat_naturality`. -/
lemma derivedProjKFlatRep_naturality (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (P P' : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hP : IsKFlat.{u, v} P) (hP' : IsKFlat.{u, v} P') (f : P ⟶ P') :
    (projLeftBifunctor.{u, v} φ E iStar).map (DerivedCategory.Q.map f) ≫
        (derivedProjKFlatRep.{u, v} φ E iStar adj P' hP').hom =
      (derivedProjKFlatRep.{u, v} φ E iStar adj P hP).hom ≫
        (projRightBifunctor.{u, v} iStar).map (DerivedCategory.Q.map f) := by
  refine NatTrans.ext (funext fun X => ?_)
  simp only [NatTrans.comp_app]
  let CX := (Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
    max u v + 1} B).tensor).obj X
  let u := leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj
  have s₁ : iStar.map (CX.map (E.functor.map (DerivedCategory.Q.map f))) ≫
        iStar.map (CX.map (E.comparison.app P')) =
      iStar.map (CX.map (E.comparison.app P)) ≫
        iStar.map (CX.map (DerivedCategory.Q.map ((extendScalarsLarge.{v, u, u} φ).map f))) :=
    (iStar.map_comp _ _).symm.trans
      ((congrArg iStar.map (CX.map_comp _ _).symm).trans
        ((congrArg (fun g => iStar.map (CX.map g)) (E.comparison.naturality f)).trans
          ((congrArg iStar.map (CX.map_comp _ _)).trans (iStar.map_comp _ _))))
  have s₂ := u.hom.naturality
    (CX.map (DerivedCategory.Q.map ((extendScalarsLarge.{v, u, u} φ).map f)))
  have s₃ := NatTrans.congr_app (derivedProjKFlat_naturality.{u, v} φ f hP hP') X
  have s₄ := (((Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
    max u v + 1} A).tensor).flip.map (DerivedCategory.Q.map f)).naturality (u.inv.app X)).symm
  exact comp_ladder_four _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂ s₃ s₄

/-- **The projection formula in the derived category, as an isomorphism of bifunctors.** Let
`φ : A →+* B` be a homomorphism of commutative rings, let `E` be any total left derived model of
extension of scalars along `φ` and let `iStar` be any left adjoint of derived coextension of
scalars `RHom_A(B, -)` — derived restriction of scalars is one, by [Stacks, Tag 0A70].  Then

`i_*(F ⊗_B^L (N ⊗_A^L B)) ≅ i_*F ⊗_A^L N`

naturally in `F` **and** in `N`.  The `F`-naturality is already present at chain level, where
all five comparisons making up the formula are natural with no K-flatness hypothesis on the
complex of `B`-modules; the `N`-naturality is `derivedProjKFlatRep_naturality`, and the two
variables are kept apart by reading the formula as an isomorphism of functors
`D(A) ⥤ (D(B) ⥤ D(A))`.  No resolution is chosen object by object: the K-flat complexes resolve
every complex of `A`-modules, so a family of isomorphisms on them which is natural in chain maps
between them determines an isomorphism of functors on all of `D(A)`
(`ModuleSystemRlimTensor.natIsoOfResolutions`). -/
noncomputable def derivedProjBifunctorNatIso (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) :
    projLeftBifunctor.{u, v} φ E iStar ≅ projRightBifunctor.{u, v} iStar :=
  ModuleSystemRlimTensor.natIsoOfResolutions
    (B := ModuleCat.{max u v} A) (fun P => IsKFlat.{u, v} P)
    (fun K => by
      obtain ⟨P, s, hP, -, hs, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, v} K
      exact ⟨P, s, (isKFlat_iff_kFlat P).mpr hP, hs⟩)
    _ _ (fun P hP => derivedProjKFlatRep.{u, v} φ E iStar adj P hP)
    (fun P P' hP hP' f => derivedProjKFlatRep_naturality.{u, v} φ E iStar adj P P' hP hP' f)

/-- **The projection formula in the derived category.** Let `φ : A →+* B` be a homomorphism of
commutative rings, let `E` be any total left derived model of extension of scalars along `φ`,
let `iStar` be any left adjoint of derived coextension of scalars `RHom_A(B, -)` — derived
restriction of scalars is one, by [Stacks, Tag 0A70] — and let `N` be an object of `D(A)`.
Then

`i_*(F ⊗_B^L (N ⊗_A^L B)) ≅ i_*F ⊗_A^L N`

naturally in `F`.  This is the value at `N` of the bifunctorial form
`Dualizing.ProjectionFormula.derivedProjBifunctorNatIso`, so it is natural in `N` as well. -/
noncomputable def derivedProjNatIso (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    tensorRightDerived.{u, v} B (E.functor.obj N) ⋙ iStar ≅
      iStar ⋙ tensorRightDerived.{u, v} A N :=
  (derivedProjBifunctorNatIso.{u, v} φ E iStar adj).app N

/-- The transpose of the relative tensor--Hom diagonal: derived restriction of scalars applied to
`RHom_A(B, -) ⊗ᴸ_B (Y ⊗ᴸ_A B)` is `i_*RHom_A(B, -) ⊗ᴸ_A Y` by the projection formula, and the
counit of [Stacks, Tag 0A70] then lands it in `- ⊗ᴸ_A Y`. -/
noncomputable def derivedProjDiagonalTranspose (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (Y : DerivedCategory (ModuleCat.{max u v} A)) :
    (Dualizing.derivedHom.{u, v, u} φ ⋙ tensorRightDerived.{u, v} B (E.functor.obj Y)) ⋙
        iStar ⟶
      tensorRightDerived.{u, v} A Y :=
  (Functor.isoWhiskerLeft (Dualizing.derivedHom.{u, v, u} φ)
      (derivedProjNatIso.{u, v} φ E iStar adj Y)).hom ≫
    Functor.whiskerRight adj.counit (tensorRightDerived.{u, v} A Y)

/-- **The `B`-linear tensor--Hom diagonal along a ring homomorphism.**  For `φ : A →+* B`, a
total left derived model `E` of extension of scalars, a left adjoint `iStar` of derived
coextension of scalars `RHom_A(B, -)` and a fixed `Y` in `D(A)`, the canonical morphism

`Y ⊗ᴸ_A RHom_A(B, -) ⟶ RHom_A(B, Y ⊗ᴸ_A -)`

of functors `D(A) ⥤ D(B)`.  The source tensors a *fixed* object of `D(A)` with a *varying*
object of `D(B)` over `A`; no such bifunctor `D(A) × D(B) ⥤ D(B)` exists here, so it is read
through the projection formula as `- ⊗ᴸ_B (Y ⊗ᴸ_A B)`, that is
`tensorRightDerived B (E.functor.obj Y)`.  The morphism is then the transpose across `adj` of
`Dualizing.ProjectionFormula.derivedProjDiagonalTranspose`, so it needs no comparison beyond
`derivedProjNatIso` itself; `homEquiv_derivedProjDiagonalTranspose` records that
characterisation, which determines it uniquely. -/
noncomputable def derivedTensorHomDiagonalAlongRingHom (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (Y : DerivedCategory (ModuleCat.{max u v} A)) :
    Dualizing.derivedHom.{u, v, u} φ ⋙ tensorRightDerived.{u, v} B (E.functor.obj Y) ⟶
      tensorRightDerived.{u, v} A Y ⋙ Dualizing.derivedHom.{u, v, u} φ :=
  Functor.whiskerLeft
      (Dualizing.derivedHom.{u, v, u} φ ⋙ tensorRightDerived.{u, v} B (E.functor.obj Y))
      adj.unit ≫
    Functor.whiskerRight (derivedProjDiagonalTranspose.{u, v} φ E iStar adj Y)
      (Dualizing.derivedHom.{u, v, u} φ)

/-- The diagonal, objectwise. -/
theorem derivedTensorHomDiagonalAlongRingHom_app (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (Y X : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X =
      adj.unit.app ((Dualizing.derivedHom.{u, v, u} φ ⋙
          tensorRightDerived.{u, v} B (E.functor.obj Y)).obj X) ≫
        (Dualizing.derivedHom.{u, v, u} φ).map
          ((derivedProjDiagonalTranspose.{u, v} φ E iStar adj Y).app X) :=
  rfl

/-- **The diagonal is characterised by its transpose.** -/
theorem homEquiv_derivedProjDiagonalTranspose (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (Y X : DerivedCategory (ModuleCat.{max u v} A)) :
    adj.homEquiv _ _ ((derivedProjDiagonalTranspose.{u, v} φ E iStar adj Y).app X) =
      (derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X := by
  simp [derivedTensorHomDiagonalAlongRingHom, Adjunction.homEquiv_unit]

/-- The diagonal at the chosen extension-of-scalars model and derived restriction of scalars. -/
noncomputable def derivedTensorHomDiagonalRestrictScalars (φ : A →+* B)
    (Y : DerivedCategory (ModuleCat.{max u v} A)) :
    Dualizing.derivedHom.{u, v, u} φ ⋙ tensorRightDerived.{u, v} B
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v,
          max u v + 1, max u v + 1} φ).functor.obj Y) ⟶
      tensorRightDerived.{u, v} A Y ⋙ Dualizing.derivedHom.{u, v, u} φ :=
  derivedTensorHomDiagonalAlongRingHom.{u, v} φ
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v,
      max u v + 1, max u v + 1} φ)
    _ (Dualizing.restrictScalarsDerived_adj_derivedHom.{u, v, u} φ).some Y

end Dualizing.ProjectionFormula


end
