module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CohomologyAboveADegree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatHomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators

/-!
# The degree-zero cohomology of a derived tensor product of two modules

Let `(C, J, O)` be a ringed site and let `A`, `G` be sheaves of `O`-modules. Then

`H^0(A[0] ⊗_O^{L} G[0]) ≅ A ⊗_O G`,

**with no flatness and no K-flatness hypothesis on either factor.** The isomorphism is `H^0` of
the canonical map `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.toTensor` to the total
tensor complex, read through the identification of that complex with `A ⊗_O G` placed in degree
zero, so it is compatible with `toTensor` by construction, and it is natural in both `A` and
`G`.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.degreeZeroTensorMap`: the canonical map
  `H^0(A[0] ⊗^L_O G[0]) ⟶ A ⊗_O G`.
* `Stacks.DerivedTensor.RingedSite.degreeZeroTensorIso`: that map, as an isomorphism.
* `Stacks.DegreeZeroTensor.isIso_of_cokernel_comparison`: the abelian-category step the proof
  turns on.
* `CochainComplex.KFlatBifunctor.rowComplexMapSecond`: the action of the termwise complex
  `p ↦ F(K^p, M)` on a morphism of `M`.

## Main results

* `Stacks.DerivedTensor.RingedSite.isIso_degreeZeroTensorMap`: **the comparison is an
  isomorphism**, unconditionally.
* `Stacks.DerivedTensor.RingedSite.degreeZeroTensorMap_naturality` and
  `Stacks.DerivedTensor.RingedSite.degreeZeroTensorMap_naturality_second`: naturality in each
  of the two modules.
* `Stacks.DerivedTensor.RingedSite.epi_degreeZeroTensorMap`: the comparison is surjective, which
  is the half of the statement that needs only one flat module.
* `Stacks.DerivedTensor.RingedSite.exists_epi_isFlat`: enough flats on a ringed site.
* `CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_second`: the identification
  `Tot(F(K, M[0])) ≅ (p ↦ F(K^p, M))` is natural in `M`.

## Implementation notes

**Why this is not a corollary of the K-flat comparisons.** The comparisons of a derived tensor
product with the ordinary one *as complexes* are conditional: the fields `comparisonLeft` and
`comparisonRight` of `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` need K-flatness of
one factor, and `Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingleIso` and
`Stacks.DerivedTensor.RingedSite.homologyTensorFlatIso` inherit it. That is not an artifact:
`A[0] ⊗^L_O G[0]` is *not* `(A ⊗_O G)[0]` without a flatness hypothesis — its cohomology below
degree zero is the Tor sheaves, which do not vanish in general. What is unconditional is the
statement in degree zero alone, and that is what is proved here.

That degree-zero statement is also available on `toTensor` itself, for an arbitrary
`DerivedTensorProduct`, as
`Stacks.DerivedTensor.RingedSite.isIso_homologyMap_toTensor_single` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/DegreeZero.lean`, proved there by a
flat resolution of the left factor. This module is not about that map but about
`degreeZeroTensorMap`, which reads it through the identification of the total tensor complex
with `A ⊗_O G` in degree zero and is what the consumers below and in `./ShiftedDegreeZero.lean`
take as the comparison; do not restate the `toTensor` form here.

**The proof.** Choose a surjection `π : P ⟶ A` from a flat module (`exists_epi_isFlat`, which
reads off `SheafOfModules.exists_epi_from_coproduct_extensionByZero` of [Stacks, Tag 03EW] and
the flatness of a direct sum of extensions by zero of structure sheaves), and let
`ι : N ⟶ P` be its kernel. Then

* the comparison at `P` is an isomorphism, because a flat module placed in degree zero is
  K-flat ([Stacks, Tag 06YQ]) and `toTensor` is then `comparisonLeft`;
* the comparison at `N` is surjective, by the same argument applied to a flat module
  surjecting onto `N` together with right exactness of `- ⊗_O G` ([Stacks, Tag 05NB]) — this is
  `epi_degreeZeroTensorMap`;
* derived tensoring with `G[0]` keeps `π` surjective on `H^0`, which is [Stacks, Tag 0DIV] (2),
  `epi_homologyMap_derivedTensorSingle`;
* `- ⊗_O G` carries `N ⟶ P ⟶ A` to an exact pair, again by right exactness.

Those four facts and the naturality of the comparison are exactly the hypotheses of
`Stacks.DegreeZeroTensor.isIso_of_cokernel_comparison`, which needs only the *lower* row to be
exact: the upper row enters through `a ≫ u = 0` and the surjectivity of `u`, so the long exact
sequence of the derived tensor product never has to be written down. That is what keeps the
proof free of the triangle of a short exact sequence of complexes and of any truncation.

**Why the comparison is named rather than inlined.** Its two faces are needed separately: as
`H^0(toTensor)` it is manifestly compatible with the canonical datum, and as a map into
`A ⊗_O G` it is what the cokernel comparison and right exactness see. `degreeZeroTensorMap_eq`
and `totSingleHomologyIso_hom` are the `rfl` lemmas that let the two be exchanged without
rewriting with a definitional equation lemma.

**The chases are helpers at a variable category.** `Stacks.DegreeZeroTensor` collects the
reassociations, the transport of a square along a functor, and the cokernel comparison, each
stated for an arbitrary category with the morphisms explicit. Rewriting with `Category.assoc`
or `Functor.map_comp` directly in `D(Mod(O))` does not typecheck here.

**Naturality.** Both naturalities are `toTensor_naturality` pasted onto the naturality of the
identification of the total tensor complex with `A ⊗_O G` placed in degree zero. In the first
variable the latter is
`CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality` of
`StacksFrontier/Algebra/Homology/TotalSingleRowNaturality.lean`; in the second it is
`totalSingleIso_hom_naturality_second`, proved here because that file has only the first.  Both
end in the naturality of `HomologicalComplex.singleMapHomologicalComplex`, in its object for
one variable and in its functor for the other
(`StacksDraft.TotalSingleRow.singleMapHomologicalComplex_naturality`).

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0DIV](https://stacks.math.columbia.edu/tag/0DIV)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u d


/-! ### The total-complex identification in the second variable

`CochainComplex.KFlatBifunctor.totalSingleIso` is proved natural in the first complex in
`StacksFrontier/Algebra/Homology/TotalSingleRowNaturality.lean`. These two statements are its
naturality in the object placed in degree zero; they belong in that file and are placed here
because the degree-zero comparison below is the only consumer so far. -/

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]

/-- **The action of the termwise complex `p ↦ F(K^p, M)` on a morphism of `M`**: in each degree
the image of that morphism under `F(K^p, -)`. -/
def rowComplexMapSecond (K : CochainComplex A ℤ) {M M' : B} (g : M ⟶ M') :
    rowComplex F K M ⟶ rowComplex F K M' where
  f p := (F.obj (K.X p)).map g
  comm' p p' _ := (F.map (K.d p p')).naturality g

/-- **The single-row identification of the double complex is natural in the object placed in
the degree `q`.** In each first degree it is the naturality of
`HomologicalComplex.singleMapHomologicalComplex` for the functor `F(K^p, -)` in its object. -/
lemma mapBifunctorSingleIso_naturality_second (K : CochainComplex A ℤ) {M M' : B} (g : M ⟶ M')
    (q : ℤ) :
    ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map
          ((HomologicalComplex.single B (ComplexShape.up ℤ) q).map g) ≫
        (mapBifunctorSingleIso F K M' q).hom =
      (mapBifunctorSingleIso F K M q).hom ≫
        ((HomologicalComplex.single D (ComplexShape.up ℤ) q).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (rowComplexMapSecond F K g) := by
  refine HomologicalComplex.hom_ext _ _ (fun p => ?_)
  exact (HomologicalComplex.singleMapHomologicalComplex (F.obj (K.X p))
    (ComplexShape.up ℤ) q).hom.naturality g

variable [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **The termwise identification of the total complex is natural in the object placed in
degree zero.** The proof is that of
`CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality` with the single-row
identification's naturality taken in the other variable. -/
lemma totalSingleIso_hom_naturality_second (K : CochainComplex A ℤ) {M M' : B} (g : M ⟶ M') :
    HomologicalComplex.mapBifunctorMap (𝟙 K)
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map g) F (ComplexShape.up ℤ) ≫
        (totalSingleIso F K M').hom =
      (totalSingleIso F K M).hom ≫ rowComplexMapSecond F K g := by
  let _hT : (StacksDraft.TotalSingleRow.singleRow (rowComplex F K M) 0).HasTotal
      (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K M 0) _
  let _hT' : (StacksDraft.TotalSingleRow.singleRow (rowComplex F K M') 0).HasTotal
      (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K M' 0) _
  have : IsIso (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M) 0) :=
    StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit _ _
  have : IsIso (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M') 0) :=
    StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit _ _
  have hM : (totalSingleIso F K M).hom =
      HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M 0).hom (ComplexShape.up ℤ) ≫
        CategoryTheory.inv
            (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M) 0) ≫
          (CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ) neg_zero).hom.app
            (rowComplex F K M) := rfl
  have hM' : (totalSingleIso F K M').hom =
      HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M' 0).hom (ComplexShape.up ℤ) ≫
        CategoryTheory.inv
            (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M') 0) ≫
          (CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ) neg_zero).hom.app
            (rowComplex F K M') := rfl
  have hid : ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map (𝟙 K)).app
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) ≫
        ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K).map
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map g) =
      ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map g) := by
    rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  have h0 : HomologicalComplex.mapBifunctorMap (𝟙 K)
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map g) F (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map
        (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K).map
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map g))
        (ComplexShape.up ℤ) :=
    congrArg (fun m ↦ HomologicalComplex₂.total.map m (ComplexShape.up ℤ)) hid
  have h1 : HomologicalComplex₂.total.map
          (((HomologicalComplex.single D (ComplexShape.up ℤ) 0).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (rowComplexMapSecond F K g)) (ComplexShape.up ℤ) ≫
        CategoryTheory.inv
          (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M') 0) =
      CategoryTheory.inv
          (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M) 0) ≫
        (CategoryTheory.shiftFunctor (CochainComplex D ℤ) (-0 : ℤ)).map
          (rowComplexMapSecond F K g) := by
    rw [IsIso.comp_inv_eq, Category.assoc,
      StacksDraft.TotalSingleRow.totalSingleRowUnit_naturality (rowComplexMapSecond F K g) 0,
      IsIso.inv_hom_id_assoc]
  have h2 := (CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ)
    neg_zero).hom.naturality (rowComplexMapSecond F K g)
  rw [h0, hM, hM', ← Category.assoc, ← HomologicalComplex₂.total.map_comp,
    mapBifunctorSingleIso_naturality_second F K g 0, HomologicalComplex₂.total.map_comp,
    Category.assoc, reassoc_of% h1, h2, Category.assoc, Category.assoc]
  exact rfl

end CochainComplex.KFlatBifunctor

namespace Stacks.DegreeZeroTensor

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D]

/-- Transporting a commuting square along a functor. Stated at a variable category and with
the morphisms explicit, which is the only shape in which `Functor.map_comp` rewrites here. -/
theorem map_sq {E : Type u₂} [Category.{v₂} E] (H : D ⥤ E) {X Y Z W : D}
    (a : X ⟶ Y) (b : Y ⟶ W) (c : X ⟶ Z) (e : Z ⟶ W) (h : a ≫ b = c ≫ e) :
    H.map a ≫ H.map b = H.map c ≫ H.map e := by
  rw [← H.map_comp, ← H.map_comp, h]

/-- Pasting two commuting squares. -/
theorem two_sq {X Y Z X' Y' Z' : D} (a : X ⟶ Y) (b : Y ⟶ Z) (a' : X' ⟶ Y') (b' : Y' ⟶ Z')
    (u : X ⟶ X') (v : Y ⟶ Y') (w : Z ⟶ Z') (h₁ : u ≫ a' = a ≫ v) (h₂ : v ≫ b' = b ≫ w) :
    u ≫ a' ≫ b' = (a ≫ b) ≫ w := by
  have e1 : u ≫ a' ≫ b' = (u ≫ a') ≫ b' := (Category.assoc u a' b').symm
  have e2 : (a ≫ v) ≫ b' = a ≫ v ≫ b' := Category.assoc a v b'
  have e3 : a ≫ b ≫ w = (a ≫ b) ≫ w := (Category.assoc a b w).symm
  rw [e1, h₁, e2, h₂, e3]

/-- Pasting three commuting squares. -/
theorem three_sq {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : D}
    (t : X₀ ⟶ X₁) (r : X₁ ⟶ X₂) (e : X₂ ⟶ X₃)
    (t' : Y₀ ⟶ Y₁) (r' : Y₁ ⟶ Y₂) (e' : Y₂ ⟶ Y₃)
    (p : X₀ ⟶ Y₀) (q : X₁ ⟶ Y₁) (s : X₂ ⟶ Y₂) (g : X₃ ⟶ Y₃)
    (h₁ : p ≫ t' = t ≫ q) (h₂ : q ≫ r' = r ≫ s) (h₃ : s ≫ e' = e ≫ g) :
    p ≫ t' ≫ r' ≫ e' = (t ≫ r ≫ e) ≫ g := by
  have e1 : p ≫ t' ≫ r' ≫ e' = (p ≫ t') ≫ r' ≫ e' := (Category.assoc p t' _).symm
  have e2 : (t ≫ q) ≫ r' ≫ e' = t ≫ (q ≫ r') ≫ e' := by simp only [Category.assoc]
  have e3 : t ≫ (r ≫ s) ≫ e' = t ≫ r ≫ s ≫ e' := by simp only [Category.assoc]
  have e4 : t ≫ r ≫ e ≫ g = (t ≫ r ≫ e) ≫ g := by simp only [Category.assoc]
  rw [e1, h₁, e2, h₂, e3, h₃, e4]

/-- An epimorphism read off a square two of whose sides are isomorphisms. -/
theorem epi_of_sq {X Y Z W : D} (a : X ⟶ Z) (i : X ⟶ Y) (f : Y ⟶ W) (i' : Z ⟶ W)
    [IsIso i] [IsIso i'] [Epi f] (h : a ≫ i' = i ≫ f) : Epi a := by
  have ha : a = (i ≫ f) ≫ inv i' := by
    rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [ha]
  infer_instance

/-- A composite that an additive functor sends to zero. -/
theorem comp_map_eq_zero {E : Type u₂} [Category.{v₂} E] [Preadditive D] [Preadditive E]
    (H : D ⥤ E) [H.Additive] {X Y Z : D} (x : X ⟶ Y) (y : Y ⟶ Z) (h : x ≫ y = 0) :
    H.map x ≫ H.map y = 0 := by
  rw [← H.map_comp, h, H.map_zero]

/-- **The cokernel comparison.** Let `a ≫ u = 0` with `u` an epimorphism, let
`b ⟶ v` be an exact pair with `v` an epimorphism, and let a ladder `(φ₁, φ₂, φ₃)` connect
them. If `φ₁` is an epimorphism and `φ₂` is an isomorphism then so is `φ₃`: the exactness of
the lower row lets `v` factor the composite `φ₂⁻¹ ≫ u`, and the factor is a two-sided inverse
of `φ₃` because `u` and `v` are epimorphisms.

Only the lower row has to be exact. The upper row is used through `a ≫ u = 0` and the
surjectivity of `u` alone, which is what makes this applicable where the upper row is a piece
of a long exact sequence that has not been written down. -/
theorem isIso_of_cokernel_comparison [Abelian D] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : D}
    (a : X₁ ⟶ X₂) (u : X₂ ⟶ X₃) (b : Y₁ ⟶ Y₂) (v : Y₂ ⟶ Y₃)
    (φ₁ : X₁ ⟶ Y₁) (φ₂ : X₂ ⟶ Y₂) (φ₃ : X₃ ⟶ Y₃)
    (hbv : b ≫ v = 0) (hex : (ShortComplex.mk b v hbv).Exact) (hau : a ≫ u = 0)
    (hu : Epi u) (hv : Epi v) (hφ₁ : Epi φ₁) (hφ₂ : IsIso φ₂)
    (sq₁ : a ≫ φ₂ = φ₁ ≫ b) (sq₂ : u ≫ φ₃ = φ₂ ≫ v) : IsIso φ₃ := by
  have hb0 : b ≫ (inv φ₂ ≫ u) = 0 := by
    rw [← cancel_epi φ₁, comp_zero, ← Category.assoc φ₁ b, ← sq₁]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact hau
  have hd : v ≫ hex.desc (inv φ₂ ≫ u) hb0 = inv φ₂ ≫ u := hex.g_desc _ _
  refine ⟨hex.desc (inv φ₂ ≫ u) hb0, ?_, ?_⟩
  · rw [← cancel_epi u, Category.comp_id, ← Category.assoc u φ₃, sq₂, Category.assoc, hd]
    simp
  · rw [← cancel_epi v, Category.comp_id, ← Category.assoc v _ φ₃, hd, Category.assoc, sq₂]
    simp

end Stacks.DegreeZeroTensor

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Modules R)]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [HasDerivedCategory.{d} (Modules R)]
  [∀ (K L : CochainComplex (Modules R) ℤ),
      HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (ComplexShape.up ℤ)] in
/-- Enough flats on a ringed site. -/
theorem exists_epi_isFlat (M : Modules R) :
    ∃ P : Modules R, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) P ∧
      ∃ π : P ⟶ M, Epi π := by
  obtain ⟨ι, U, π, hπ⟩ :=
    SheafOfModules.exists_epi_from_coproduct_extensionByZero
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) M
  exact ⟨_, Stacks.SheafOfModules.KFlatResolution.isFlat_of_isSumOfExtensionByZeroStructureSheaves
    R _ ⟨ι, U, ⟨Iso.refl _⟩⟩, π, hπ⟩

/-- Abbreviation for a module placed in degree zero. -/
abbrev sg (A : Modules R) : CochainComplex (Modules R) ℤ :=
  (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj A

/-- The total tensor complex of two modules in degree zero is their tensor product in degree
zero. -/
def totSingleIsoSingle (G A : Modules R) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj (sg R A)).obj (sg R G) ≅
      sg R (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj G) :=
  CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (sg R A) G ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj G) (ComplexShape.up ℤ) 0).app A

/-- `H^0` of the total tensor complex of two modules in degree zero. -/
def totSingleHomologyIso (G A : Modules R) :
    (DerivedCategory.homologyFunctor (Modules R) 0).obj
        (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj (sg R A)).obj (sg R G))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj G :=
  (DerivedCategory.homologyFunctor (Modules R) 0).mapIso
      (DerivedCategory.Q.mapIso (totSingleIsoSingle R G A)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R) 0).app _

/-- The canonical map `H^0(A[0] ⊗^L_O G[0]) ⟶ A ⊗_O G`. -/
def degreeZeroTensorMap (G A : Modules R) :
    (DerivedCategory.homologyFunctor (Modules R) 0).obj
        (((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).obj
          (DerivedCategory.Q.obj (sg R G))) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj G :=
  (DerivedCategory.homologyFunctor (Modules R) 0).map
      ((canonicalDerivedTensorProduct R).toTensor (sg R A) (sg R G)) ≫
    (totSingleHomologyIso R G A).hom

/-- The forward map of `totSingleHomologyIso` is `H^0` of `totSingleIsoSingle` followed by the
identification of `H^0` of a complex concentrated in degree zero with its degree-zero term. -/
theorem totSingleHomologyIso_hom (G A : Modules R) :
    (totSingleHomologyIso R G A).hom =
      (DerivedCategory.homologyFunctor (Modules R) 0).map
          (DerivedCategory.Q.map (totSingleIsoSingle R G A).hom) ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R) 0).app
          (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj G)).hom :=
  rfl

/-- `degreeZeroTensorMap` is `H^0` of `DerivedTensorProduct.toTensor` followed by
`totSingleHomologyIso`. -/
theorem degreeZeroTensorMap_eq (G A : Modules R) :
    degreeZeroTensorMap R G A =
      (DerivedCategory.homologyFunctor (Modules R) 0).map
          ((canonicalDerivedTensorProduct R).toTensor (sg R A) (sg R G)) ≫
        (totSingleHomologyIso R G A).hom :=
  rfl

/-- For a flat left factor the canonical map is an isomorphism. -/
theorem isIso_degreeZeroTensorMap_of_isFlat (G A : Modules R)
    (hA : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) A) :
    IsIso (degreeZeroTensorMap R G A) := by
  have hK := Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R A hA 0
  have h : IsIso ((DerivedCategory.homologyFunctor (Modules R) 0).map
      ((canonicalDerivedTensorProduct R).toTensor (sg R A) (sg R G))) := by
    rw [(canonicalDerivedTensorProduct R).toTensor_eq_comparisonLeft (sg R A) (sg R G) hK]
    exact ((DerivedCategory.homologyFunctor (Modules R) 0).mapIso
      ((canonicalDerivedTensorProduct R).comparisonLeft (sg R A) (sg R G) hK)).isIso_hom
  rw [degreeZeroTensorMap_eq]
  exact IsIso.comp_isIso

/-- Naturality of `degreeZeroTensorMap`, from the naturality of `toTensor` and of the
identification `totSingleIsoSingle`. -/
private theorem degreeZeroTensorMap_naturality_of {G G' A A' : Modules R}
    (m : ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj G ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A').obj G')
    (e : ((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).obj
        (DerivedCategory.Q.obj (sg R G)) ⟶
      ((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A'))).obj
        (DerivedCategory.Q.obj (sg R G')))
    (w : ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj (sg R A)).obj (sg R G) ⟶
      ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj (sg R A')).obj (sg R G'))
    (h1 : e ≫ (canonicalDerivedTensorProduct R).toTensor (sg R A') (sg R G') =
      (canonicalDerivedTensorProduct R).toTensor (sg R A) (sg R G) ≫ DerivedCategory.Q.map w)
    (hn : w ≫ (totSingleIsoSingle R G' A').hom = (totSingleIsoSingle R G A).hom ≫
      (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map m) :
    (DerivedCategory.homologyFunctor (Modules R) 0).map e ≫ degreeZeroTensorMap R G' A' =
      degreeZeroTensorMap R G A ≫ m := by
  have h2 := Stacks.DegreeZeroTensor.map_sq (DerivedCategory.homologyFunctor (Modules R) 0) _ _ _ _
    (Stacks.DegreeZeroTensor.map_sq (DerivedCategory.Q (C := Modules R)) _ _ _ _ hn)
  have h3 := (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R) 0).hom.naturality m
  rw [degreeZeroTensorMap_eq, degreeZeroTensorMap_eq, totSingleHomologyIso_hom,
    totSingleHomologyIso_hom]
  exact Stacks.DegreeZeroTensor.three_sq _ _ _ _ _ _ _ _ _ _
    (Stacks.DegreeZeroTensor.map_sq _ _ _ _ _ h1) h2 h3

omit [HasDerivedCategory.{d} (Modules R)] in
/-- The total-complex identification is natural in the first module. -/
theorem totSingleIsoSingle_hom_naturality (G : Modules R) {A A' : Modules R} (f : A ⟶ A') :
    HomologicalComplex.mapBifunctorMap
          ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map f) (𝟙 (sg R G))
          (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) ≫
        (totSingleIsoSingle R G A').hom =
      (totSingleIsoSingle R G A).hom ≫
        (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor R).map f).app G) :=
  Stacks.DegreeZeroTensor.two_sq _ _ _ _ _ _ _
    (CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality
      (Stacks.SheafOfModules.Tensor.sheafTensor R)
      ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map f) G)
    ((HomologicalComplex.singleMapHomologicalComplex
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj G)
      (ComplexShape.up ℤ) 0).hom.naturality f)

/-- **The canonical map `H^0(A[0] ⊗^L_O G[0]) ⟶ A ⊗_O G` is natural in `A`.** -/
theorem degreeZeroTensorMap_naturality (G : Modules R) {A A' : Modules R} (f : A ⟶ A') :
    (DerivedCategory.homologyFunctor (Modules R) 0).map
          (((derivedTensorProductFunctor R).map
            (DerivedCategory.Q.map
              ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map f))).app
            (DerivedCategory.Q.obj (sg R G))) ≫
        degreeZeroTensorMap R G A' =
      degreeZeroTensorMap R G A ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor R).map f).app G := by
  have h1 := (canonicalDerivedTensorProduct R).toTensor_naturality
    ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map f) (𝟙 (sg R G))
  rw [(DerivedCategory.Q (C := Modules R)).map_id (sg R G),
    ((canonicalDerivedTensorProduct R).tensor.obj
      (DerivedCategory.Q.obj (sg R A'))).map_id (DerivedCategory.Q.obj (sg R G)),
    Category.id_comp] at h1
  exact degreeZeroTensorMap_naturality_of R _ _ _ h1
    (totSingleIsoSingle_hom_naturality R G f)



omit [HasDerivedCategory.{d} (Modules R)] in
/-- The total-complex identification is natural in the second module. -/
theorem totSingleIsoSingle_hom_naturality_second (A : Modules R) {G G' : Modules R} (g : G ⟶ G') :
    HomologicalComplex.mapBifunctorMap (𝟙 (sg R A))
          ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map g)
          (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) ≫
        (totSingleIsoSingle R G' A).hom =
      (totSingleIsoSingle R G A).hom ≫
        (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).map g) :=
  Stacks.DegreeZeroTensor.two_sq _ _ _ _ _ _ _
    (CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_second
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (sg R A) g)
    (StacksDraft.TotalSingleRow.singleMapHomologicalComplex_naturality
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.map g) 0 A).symm

/-- **The canonical map `H^0(A[0] ⊗^L_O G[0]) ⟶ A ⊗_O G` is natural in `G`.** -/
theorem degreeZeroTensorMap_naturality_second (A : Modules R) {G G' : Modules R} (g : G ⟶ G') :
    (DerivedCategory.homologyFunctor (Modules R) 0).map
          (((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).map
            (DerivedCategory.Q.map
              ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map g))) ≫
        degreeZeroTensorMap R G' A =
      degreeZeroTensorMap R G A ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).map g := by
  have h1 := (canonicalDerivedTensorProduct R).toTensor_naturality (𝟙 (sg R A))
    ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map g)
  rw [(DerivedCategory.Q (C := Modules R)).map_id (sg R A),
    (canonicalDerivedTensorProduct R).tensor.map_id (DerivedCategory.Q.obj (sg R A)),
    NatTrans.id_app, Category.id_comp] at h1
  exact degreeZeroTensorMap_naturality_of R _ _ _ h1
    (totSingleIsoSingle_hom_naturality_second R A g)

/-! ### Enough flats and right exactness -/

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [HasDerivedCategory.{d} (Modules R)]
  [∀ (K L : CochainComplex (Modules R) ℤ),
      HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (ComplexShape.up ℤ)] in
/-- **Right exactness of `- ⊗_O G`.** -/
theorem preservesFiniteColimits_sheafTensorFlip (G : Modules R) :
    PreservesFiniteColimits ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj G) :=
  let := Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj R G
  PreservesColimitsOfSize.preservesFiniteColimits _

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
      HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (ComplexShape.up ℤ)] in
/-- Away from degree zero a module placed in degree zero has no cohomology, so any map between
two such is an isomorphism there. -/
theorem isIso_homologyMap_Q_single_map {A A' : Modules R} (f : A ⟶ A') (i : ℤ) (hi : 0 < i) :
    IsIso ((DerivedCategory.homologyFunctor (Modules R) i).map
      (DerivedCategory.Q.map
        ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map f))) :=
  (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj (sg R A)) 0 i hi).isIso
    (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj (sg R A')) 0 i hi) _

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
      HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (ComplexShape.up ℤ)] in
/-- In degree zero `H^0` of a module placed in degree zero is the module, so a surjection of
modules stays one. -/
theorem epi_homologyMap_Q_single_map {A A' : Modules R} (f : A ⟶ A') [Epi f] :
    Epi ((DerivedCategory.homologyFunctor (Modules R) 0).map
      (DerivedCategory.Q.map
        ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map f))) :=
  Stacks.DegreeZeroTensor.epi_of_sq _ _ _ _
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R) 0).hom.naturality f)

/-- Derived tensoring with `G[0]` and taking `H^0` kills a composite of two maps of modules
whose composite is zero. -/
theorem comp_homologyMap_tensor_single_eq_zero (G : Modules R) {N P A : Modules R}
    (ι : N ⟶ P) (π : P ⟶ A) (h : ι ≫ π = 0) :
    (DerivedCategory.homologyFunctor (Modules R) 0).map
          (((derivedTensorProductFunctor R).map (DerivedCategory.Q.map
            ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map ι))).app
            (DerivedCategory.Q.obj (sg R G))) ≫
        (DerivedCategory.homologyFunctor (Modules R) 0).map
          (((derivedTensorProductFunctor R).map (DerivedCategory.Q.map
            ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map π))).app
            (DerivedCategory.Q.obj (sg R G))) = 0 :=
  Stacks.DegreeZeroTensor.comp_map_eq_zero
    (DerivedCategory.homologyFunctor (Modules R) 0) _ _
    (Stacks.DegreeZeroTensor.comp_map_eq_zero (derivedTensorSingle R G) _ _
      (Stacks.DegreeZeroTensor.comp_map_eq_zero (DerivedCategory.Q (C := Modules R)) _ _
        (Stacks.DegreeZeroTensor.comp_map_eq_zero
          (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0) ι π h)))

/-- `H^0` of derived tensoring with `G[0]` carries a surjection of modules in degree zero to a
surjection. This is [Stacks, Tag 0DIV] (2) in degree zero. -/
theorem epi_homologyMap_tensor_single {P A : Modules R} (π : P ⟶ A) [Epi π] (G : Modules R) :
    Epi ((DerivedCategory.homologyFunctor (Modules R) 0).map
      (((derivedTensorProductFunctor R).map (DerivedCategory.Q.map
        ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map π))).app
        (DerivedCategory.Q.obj (sg R G)))) :=
  epi_homologyMap_derivedTensorSingle R
    (DerivedCategory.Q.map
      ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map π)) G 0
    (fun i hi => isIso_homologyMap_Q_single_map R π i hi) (epi_homologyMap_Q_single_map R π)

/-! ### The comparison is surjective, then bijective -/

/-- **The canonical map `H^0(A[0] ⊗^L_O G[0]) ⟶ A ⊗_O G` is surjective.** Choose a flat module
surjecting onto `A`. The comparison is an isomorphism there, derived tensoring keeps the
surjection by [Stacks, Tag 0DIV] (2), and `- ⊗_O G` keeps it by right exactness. -/
theorem epi_degreeZeroTensorMap (G A : Modules R) : Epi (degreeZeroTensorMap R G A) := by
  obtain ⟨P, hP, π, hπ⟩ := exists_epi_isFlat R A
  have := hπ
  let := preservesFiniteColimits_sheafTensorFlip R G
  have : IsIso (degreeZeroTensorMap R G P) := isIso_degreeZeroTensorMap_of_isFlat R G P hP
  have hv : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor R).map π).app G) :=
    (inferInstance : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj G).map π))
  have : Epi (degreeZeroTensorMap R G P ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).map π).app G) := inferInstance
  exact epi_of_epi_fac (degreeZeroTensorMap_naturality R G π)

/-- **The canonical map `H^0(A[0] ⊗^L_O G[0]) ⟶ A ⊗_O G` is an isomorphism.** No flatness and
no K-flatness is assumed of either factor.

Choose a surjection `π : P ⟶ A` from a flat module and let `ι : N ⟶ P` be its kernel. The
comparison is an isomorphism at `P` because `P` is flat and surjective at `N` by
`epi_degreeZeroTensorMap`; derived tensoring with `G[0]` keeps `π` surjective on `H^0` by
[Stacks, Tag 0DIV] (2); and `- ⊗_O G` carries `N ⟶ P ⟶ A` to an exact pair by right exactness.
That is exactly the data of `Stacks.DegreeZeroTensor.isIso_of_cokernel_comparison`. -/
theorem isIso_degreeZeroTensorMap (G A : Modules R) : IsIso (degreeZeroTensorMap R G A) := by
  obtain ⟨P, hP, π, hπ⟩ := exists_epi_isFlat R A
  have := hπ
  let := preservesFiniteColimits_sheafTensorFlip R G
  have hS : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)
  have hSmap := hS.map_of_epi_of_preservesCokernel
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj G) hπ inferInstance
  exact Stacks.DegreeZeroTensor.isIso_of_cokernel_comparison _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor R).map (kernel.ι π)).app G)
    (((Stacks.SheafOfModules.Tensor.sheafTensor R).map π).app G)
    (degreeZeroTensorMap R G (kernel π)) (degreeZeroTensorMap R G P)
    (degreeZeroTensorMap R G A) _ hSmap
    (comp_homologyMap_tensor_single_eq_zero R G (kernel.ι π) π (kernel.condition π))
    (epi_homologyMap_tensor_single R π G)
    (inferInstance : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj G).map π))
    (epi_degreeZeroTensorMap R G (kernel π))
    (isIso_degreeZeroTensorMap_of_isFlat R G P hP)
    (degreeZeroTensorMap_naturality R G (kernel.ι π))
    (degreeZeroTensorMap_naturality R G π)

/-! ### The unconditional degree-zero comparison -/

/-- **`H^0` of the derived tensor product of two modules placed in degree zero is their
ordinary tensor product.** No flatness and no K-flatness is assumed of either factor.

The map is `degreeZeroTensorMap`, that is `H^0` of the canonical map
`DerivedTensorProduct.toTensor` to the total tensor complex, read through the identification of
that complex with `A ⊗_O G` placed in degree zero. So the identification is compatible with
`toTensor` by construction, and it is natural in `A` by
`degreeZeroTensorMap_naturality`. -/
def degreeZeroTensorIso (G A : Modules R) :
    (DerivedCategory.homologyFunctor (Modules R) 0).obj
        (((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).obj
          (DerivedCategory.Q.obj (sg R G))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj G :=
  letI := isIso_degreeZeroTensorMap R G A
  asIso (degreeZeroTensorMap R G A)

/-- The forward map of the isomorphism `degreeZeroTensorIso` is `degreeZeroTensorMap`. -/
theorem degreeZeroTensorIso_hom (G A : Modules R) :
    (degreeZeroTensorIso R G A).hom = degreeZeroTensorMap R G A :=
  rfl

end Stacks.DerivedTensor.RingedSite

end
