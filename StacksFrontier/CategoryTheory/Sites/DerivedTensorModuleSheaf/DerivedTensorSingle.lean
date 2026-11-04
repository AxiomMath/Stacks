module

public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedChangeOfRings
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedLeft

/-!
# Derived tensor products with a sheaf placed in degree zero

Let `(C, J)` be a site, `Λ` a commutative ring and `P` a complex of sheaves of `Λ`-modules which
is K-flat. For a sheaf `M` of `Λ`-modules placed in degree zero, the derived tensor product
`P ⊗_Λ^L M[0]` is computed by the termwise complex `p ↦ P^p ⊗_Λ M`, naturally in `M`. For a
ring map `Λ → S`, the projection formula `(S ⊗_Λ F) ⊗_S N ≅ F ⊗_Λ N` holds for sheaves, naturally
in both variables.

## Main definitions

* `CochainComplex.KFlatBifunctor.rowFunctor`: the termwise complex `p ↦ F(K^p, M)` as a functor
  of `M`.
* `CochainComplex.KFlatBifunctor.mapRowComplexIso`: a natural isomorphism
  `G(F(a, b)) ≅ F'(G₁ a, G₂ b)` applied termwise to the termwise complexes.
* `Stacks.ModuleSheaf.derivedTensorSingleIso`: for a left K-flat complex `P`, the functor
  `M ↦ P ⊗^L M[0]` is `M ↦ Q(p ↦ P^p ⊗ M)`.
* `Stacks.ModuleSheaf.extendScalarsTensorRestrictScalarsIso`: the projection formula for
  sheaves, `(S ⊗_Λ F) ⊗_S N ≅ F ⊗_Λ N` over `Λ`, as an isomorphism of curried bifunctors.

## Main results

* `CochainComplex.KFlatBifunctor.mapRowComplexIso_hom_naturality`: the termwise comparison is
  natural in the module of coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe t w v u

namespace CochainComplex.KFlatBifunctor

section Row

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]

/-- The termwise complex `p ↦ F(K^p, M)` as a functor of `M`. -/
@[simps]
def rowFunctor (K : CochainComplex A ℤ) : B ⥤ CochainComplex D ℤ where
  obj M := rowComplex F K M
  map g := rowComplexMapRight F K g
  map_id M := by
    ext p
    simp [rowComplexMapRight, rowComplex]
  map_comp g g' := by
    ext p
    simp [rowComplexMapRight, rowComplex]

variable {A' B' D' : Type*} [Category A'] [Category B'] [Category D']
  [Abelian A'] [Abelian B'] [Abelian D']
  (F' : A' ⥤ B' ⥤ D') [F'.Additive] [∀ X, (F'.obj X).Additive]
  {G₁ : A ⥤ A'} {G₂ : B ⥤ B'} {G : D ⥤ D'} [G₁.Additive] [G.Additive]

/-- A natural isomorphism `G(F(a, b)) ≅ F'(G₁ a, G₂ b)`, applied termwise, identifies `G` of the
termwise complex `p ↦ F(K^p, M)` with the termwise complex `p ↦ F'(G₁ K^p, G₂ M)`. -/
def mapRowComplexIso
    (e : F ⋙ (Functor.whiskeringRight _ _ _).obj G ≅
      G₁ ⋙ F' ⋙ (Functor.whiskeringLeft _ _ _).obj G₂)
    (K : CochainComplex A ℤ) (M : B) :
    (G.mapHomologicalComplex _).obj (rowComplex F K M) ≅
      rowComplex F' ((G₁.mapHomologicalComplex _).obj K) (G₂.obj M) :=
  HomologicalComplex.Hom.isoOfComponents (fun p => (e.app (K.X p)).app M) fun p q _ => by
    simpa [rowComplex] using (NatTrans.congr_app (e.hom.naturality (K.d p q)) M).symm

omit [Abelian B] [Abelian B'] [∀ X, (F.obj X).Additive] [∀ X, (F'.obj X).Additive] in
/-- **The termwise comparison is natural in the coefficients.** -/
theorem mapRowComplexIso_hom_naturality
    (e : F ⋙ (Functor.whiskeringRight _ _ _).obj G ≅
      G₁ ⋙ F' ⋙ (Functor.whiskeringLeft _ _ _).obj G₂)
    (K : CochainComplex A ℤ) {M M' : B} (g : M ⟶ M') :
    (G.mapHomologicalComplex _).map (rowComplexMapRight F K g) ≫
        (mapRowComplexIso F F' e K M').hom =
      (mapRowComplexIso F F' e K M).hom ≫
        rowComplexMapRight F' ((G₁.mapHomologicalComplex _).obj K) (G₂.map g) := by
  ext p
  simp only [mapRowComplexIso, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    rowComplexMapRight]
  exact (e.hom.app (K.X p)).naturality g

/-- `mapRowComplexIso` as an isomorphism of functors of the coefficients. -/
def mapRowFunctorIso
    (e : F ⋙ (Functor.whiskeringRight _ _ _).obj G ≅
      G₁ ⋙ F' ⋙ (Functor.whiskeringLeft _ _ _).obj G₂)
    (K : CochainComplex A ℤ) :
    rowFunctor F K ⋙ G.mapHomologicalComplex _ ≅
      G₂ ⋙ rowFunctor F' ((G₁.mapHomologicalComplex _).obj K) :=
  NatIso.ofComponents (mapRowComplexIso F F' e K) (mapRowComplexIso_hom_naturality F F' e K)

end Row

end CochainComplex.KFlatBifunctor

namespace Stacks.ModuleSheaf

open CochainComplex.KFlatBifunctor

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type w} [CommRing Λ] [UnivLE.{max u v, w}]

/-- `CochainComplex.KFlatBifunctor.totalSingleIso` for sheaves of modules, with its source
spelled as the total complex `Tot(P ⊗ M[0])`. -/
def totalComplexSingleIso (P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (M : Sheaf J (ModuleCat.{w} Λ)) :
    totalComplex (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) ≅
      (rowFunctor (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P).obj M :=
  totalSingleIso (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P M

/-- The isomorphism `totalComplexSingleIso P M` is natural in the sheaf `M`. -/
theorem totalComplexSingleIso_hom_naturality (P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    {M M' : Sheaf J (ModuleCat.{w} Λ)} (g : M ⟶ M') :
    (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂HomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).map
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g) ≫
        (totalComplexSingleIso P M').hom =
      (totalComplexSingleIso P M).hom ≫
        (rowFunctor (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P).map g := by
  rw [Functor.map₂HomologicalComplex_obj_map]
  exact totalSingleIso_hom_naturality_right (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P g

section Derived

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]

/-- **A left K-flat complex tensored with a sheaf in degree zero.** For a left K-flat complex
`P` of sheaves of `Λ`-modules, the derived tensor product `P ⊗_Λ^L M[0]` is the termwise
complex `p ↦ P^p ⊗_Λ M`, naturally in the sheaf `M`. -/
def derivedTensorSingleIso {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P) :
    HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
        tensorLeft (DerivedCategory.Q.obj P) ≅
      rowFunctor (curriedTensor _) P ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun M => ((curriedTensorIsoDerivedBifunctor J Λ).app _).app _ ≪≫
      comparisonLeft _ P _ hP ≪≫ DerivedCategory.Q.mapIso (totalComplexSingleIso P M))
    (fun {M M'} g => by
      have h₁ := ((curriedTensorIsoDerivedBifunctor J Λ).hom.app
        (DerivedCategory.Q.obj P)).naturality
          (DerivedCategory.Q.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g))
      have h₂ := comparisonLeft_naturality_right (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g) hP
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
        Functor.comp_map]
      rw [← Functor.map_comp, ← totalComplexSingleIso_hom_naturality P g, Functor.map_comp,
        ← reassoc_of% h₂, ← reassoc_of% h₁])

end Derived

section ProjectionFormula

variable {S : Type w} [CommRing S] (f : Λ →+* S)

/-- The projection formula for sheaves at a fixed sheaf `X` of `Λ`-modules:
`(S ⊗_Λ X) ⊗_S N ≅ X ⊗_Λ N` over `Λ`, naturally in the sheaf `N` of `S`-modules. -/
def extendScalarsTensorRestrictScalarsIsoApp (X : Sheaf J (ModuleCat.{w} Λ)) :
    (curriedTensor (Sheaf J (ModuleCat.{w} S))).obj ((extendScalars J f).obj X) ⋙
        restrictScalars J f ≅
      restrictScalars J f ⋙ (curriedTensor (Sheaf J (ModuleCat.{w} Λ))).obj X :=
  NatIso.ofComponents (fun (N : Sheaf J (ModuleCat.{w} S)) =>
      (restrictScalars J f).mapIso (β_ _ _) ≪≫
        (restrictScalarsTensorExtendScalarsIso J f).app (N, X) ≪≫ β_ _ _)
    (fun {N N'} g => by
      have h' : (restrictScalars J f).map (g ▷ (extendScalars J f).obj X) ≫
          (restrictScalarsTensorExtendScalarsIso J f).hom.app (N', X) =
        (restrictScalarsTensorExtendScalarsIso J f).hom.app (N, X) ≫
          ((restrictScalars J f).map g ▷ X) := by
        rw [← tensorHom_id, ← tensorHom_id, ← (extendScalars J f).map_id]
        exact (restrictScalarsTensorExtendScalarsIso J f).hom.naturality
          ((g, 𝟙 X) : ((N, X) : Sheaf J (ModuleCat.{w} S) × Sheaf J (ModuleCat.{w} Λ)) ⟶ (N', X))
      dsimp
      simp only [Category.assoc, ← Functor.map_comp_assoc,
        BraidedCategory.braiding_naturality_right (C := Sheaf J (ModuleCat.{w} S))]
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% h']
      simp [BraidedCategory.braiding_naturality_left (C := Sheaf J (ModuleCat.{w} Λ))])

/-- **The projection formula for sheaves, as curried bifunctors**: for a sheaf `F` of
`Λ`-modules and a sheaf `N` of `S`-modules, `(S ⊗_Λ F) ⊗_S N`, read over `Λ`, is `F ⊗_Λ N`,
naturally in both. -/
def extendScalarsTensorRestrictScalarsIso :
    (extendScalars J f ⋙ curriedTensor (Sheaf J (ModuleCat.{w} S))) ⋙
        (Functor.whiskeringRight _ _ _).obj (restrictScalars J f) ≅
      𝟭 (Sheaf J (ModuleCat.{w} Λ)) ⋙ curriedTensor (Sheaf J (ModuleCat.{w} Λ)) ⋙
        (Functor.whiskeringLeft _ _ _).obj (restrictScalars J f) :=
  NatIso.ofComponents (fun X => extendScalarsTensorRestrictScalarsIsoApp f X)
    (fun {X X'} g => by
      refine NatTrans.ext (funext fun N => ?_)
      have h' : (restrictScalars J f).map (N ◁ (extendScalars J f).map g) ≫
          (restrictScalarsTensorExtendScalarsIso J f).hom.app (N, X') =
        (restrictScalarsTensorExtendScalarsIso J f).hom.app (N, X) ≫
          ((restrictScalars J f).obj N ◁ g) := by
        rw [← id_tensorHom, ← id_tensorHom, ← (restrictScalars J f).map_id]
        exact (restrictScalarsTensorExtendScalarsIso J f).hom.naturality
          ((𝟙 N, g) : ((N, X) : Sheaf J (ModuleCat.{w} S) × Sheaf J (ModuleCat.{w} Λ)) ⟶ (N, X'))
      dsimp [extendScalarsTensorRestrictScalarsIsoApp]
      simp only [Category.assoc, ← Functor.map_comp_assoc,
        BraidedCategory.braiding_naturality_left (C := Sheaf J (ModuleCat.{w} S))]
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% h']
      simp [BraidedCategory.braiding_naturality_right (C := Sheaf J (ModuleCat.{w} Λ))])

/-- Tensoring with the extension of scalars of a fixed sheaf is additive: the components of the
source of `Stacks.ModuleSheaf.extendScalarsTensorRestrictScalarsIso` are additive functors. -/
instance (X : Sheaf J (ModuleCat.{w} Λ)) :
    ((extendScalars J f ⋙ curriedTensor (Sheaf J (ModuleCat.{w} S))).obj X).Additive :=
  inferInstanceAs ((curriedTensor (Sheaf J (ModuleCat.{w} S))).obj
    ((extendScalars J f).obj X)).Additive

end ProjectionFormula

end Stacks.ModuleSheaf

end
