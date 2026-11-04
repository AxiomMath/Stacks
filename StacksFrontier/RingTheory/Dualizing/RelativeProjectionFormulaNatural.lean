module

public import Mathlib.CategoryTheory.Functor.Currying
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
public import StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormula

/-!
# The projection formula at the diagonal, naturally in the tensor factor

Let `R → A` be flat, put `B = A ⊗[R] A`, write `p₁ : A → B` for the left coprojection and
`Δ : B → A` for the multiplication map.  The module
`StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormula` proves the projection formula at the
diagonal,

> `Δ_*M ≅ A_B ⊗ᴸ_B p₁^*M`   in `D(B)`,

**pointwise**: as a `Nonempty`, each component read off a separately chosen K-flat representative
of `M`.  The duality route to [stacks 0E2D] of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` needs more than that.  Its one
remaining obligation is the *enriched* form of the adjunction `Δ_* ⊣ Δ^!` of [stacks 0A70], and
the Yoneda reduction of that statement needs the projection formula

> `Δ_*(M ⊗ᴸ_A Z) ≅ Δ_*M ⊗ᴸ_B p₁^*Z`   **naturally in `Z`**.

This file proves that, as `Dualizing.diagonalProjectionNatIso`: an isomorphism of *functors*
`D(A) ⥤ D(B)`, for an arbitrary object `M` of `D(A)`.

## The shape of the proof

Nothing is special about the diagonal: everything below is proved for a ring map `φ : A →+* B`
with a retraction `ψ : B →+* A`, as `Dualizing.singleTargetTensorExtendScalarsIso` is.

*At chain level.*  The projection formula of [stacks 06Y1], `baseChangeTensorIso`, is natural in
the base-changed complex (`Dualizing.baseChangeTensorIso_inv_naturality`), which is proved
degreewise from naturality of the module-level projection formula; and extension of scalars along
`φ` followed by extension along `ψ` is the identity *naturally*
(`Dualizing.extendScalarsRetractionNatIso`, the functorial upgrade of
`Dualizing.extendScalarsRetractionComplexIso`).  Composing the two gives

`ψ_*(P ⊗_A Z) ≅ ψ_*P ⊗_B φ^*Z`,   naturally in `Z`,

as `Dualizing.retractionProjectionNatIso`.

*Descent.*  On a K-flat `Z` both derived tensor products are computed by the chain-level one
(`DerivedHomData.tensorIso`), derived restriction along `Δ` by chain-level restriction
(`Functor.mapDerivedCategoryFactors`), and derived base change along `p₁` by chain-level base
change (`Dualizing.diagonalExtensionKFlatIso`, using that `p₁^*` of a K-flat complex is K-flat by
[stacks 06Y1]).  That identifies the two functors at every K-flat complex, compatibly with chain
maps between K-flat complexes — `Dualizing.diagonalProjectionComponent_naturality` — and
`ModuleSystemRlimTensor.natIsoOfResolutions` descends such a family to all of `D(A)`, every
complex having a K-flat resolution by [stacks 06Y4].  An arbitrary object of `D(A)` in the tensor
slot is reached by conjugating with a representative.

## Main definitions

* `Dualizing.extendScalarsRetractionNatIso` — extension along a map and then along a retraction
  of it is the identity, as an isomorphism of functors on complexes.
* `Dualizing.retractionProjectionNatIso` — **the chain-level projection formula at a retraction,
  natural in the tensor factor.**
* `Dualizing.diagonalProjectionComponent` — its value in `D(B)` at a chain-level pair.
* `Dualizing.diagonalProjectionNatIso` — **the projection formula at the diagonal, naturally in
  the tensor factor**: `Δ_*(M ⊗ᴸ_A -) ≅ Δ_*M ⊗ᴸ_B p₁^*(-)` as functors `D(A) ⥤ D(B)`.

## Main results

* `Dualizing.projectionFormulaIso_inv_natural_right`,
  `Dualizing.baseChangeTensorIso_inv_naturality`,
  `Dualizing.baseChangeTensorIso_hom_naturality` — **the projection formula of [stacks 06Y1] is
  natural in the base-changed complex**, degreewise and then on total complexes.  No naturality
  lemma for `baseChangeTensorIso` existed.
* `Dualizing.diagonalProjectionComponent_naturality` — the chain-level identification is natural
  in chain maps between K-flat complexes, which is what the descent consumes.

## Implementation notes

The degreewise naturality is proved by term-level pasting (`Category.assoc`, `eq_whisker`,
`whisker_eq`) rather than by rewriting: the composite
`projectionFormulaIso.inv ≫ ψ_*(ιTensorObj ...)` is type-correct only after unfolding
`CochainComplex.extendScalars`, so once one side of the degreewise goal has been rewritten the
goal is no longer type-correct at `implicit` transparency and no further rewrite fires.  Writing
each side's normal form as a `have` with an ascribed statement, and composing the two with
`Eq.trans`, keeps every defeq check local.

## References

* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
-/
@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

section ChainLevel

variable {A B : Type u} [CommRing A] [CommRing B]

/-- A naturality square read on the inverses of its two vertical isomorphisms. -/
private lemma inv_square {C : Type*} [Category* C] {X X' Y Y' : C} {e : X ≅ Y} {e' : X' ≅ Y'}
    {a : X ⟶ X'} {b : Y ⟶ Y'} (h : a ≫ e'.hom = e.hom ≫ b) : b ≫ e'.inv = e.inv ≫ a := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- The degreewise projection formula of [stacks 06Y1] is natural in the base-changed module
variable, read on the inverses. -/
theorem projectionFormulaIso_inv_natural_right (φ : A →+* B) (V : ModuleCat.{u} B)
    {W W' : ModuleCat.{u} A} (g : W ⟶ W') :
    ((ModuleCat.restrictScalars φ).obj V ◁ g) ≫ (projectionFormulaIso φ V W').inv =
      (projectionFormulaIso φ V W).inv ≫
        (ModuleCat.restrictScalars φ).map (V ◁ (ModuleCat.extendScalars φ).map g) := by
  exact inv_square (projectionFormulaIso_natural_right φ V g)

/-- Restriction of scalars on complexes acts degreewise. -/
theorem restrictScalars_map_f (φ : A →+* B) {X Y : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (n : ℤ) :
    ((CochainComplex.restrictScalars φ).map f).f n = (ModuleCat.restrictScalars φ).map (f.f n) :=
  rfl

/-- Extension of scalars on complexes acts degreewise. -/
theorem extendScalars_map_f (φ : A →+* B) {X Y : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : X ⟶ Y) (n : ℤ) :
    ((CochainComplex.extendScalars φ).map f).f n = (ModuleCat.extendScalars φ).map (f.f n) :=
  rfl

/-- The inverse of the comparison of total complexes is degreewise the inverse of the degreewise
comparison. -/
theorem baseChangeTensorIso_inv_f (φ : A →+* B) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    (baseChangeTensorIso φ K L).inv.f n = (baseChangeTensorIsoX φ K L n).inv := rfl

/-- The comparison of total complexes is degreewise the degreewise comparison. -/
theorem baseChangeTensorIso_hom_f (φ : A →+* B) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    (baseChangeTensorIso φ K L).hom.f n = (baseChangeTensorIsoX φ K L n).hom := rfl

/-- Left whiskering by a complex acts on the antidiagonal summands of a total complex by the
identity on the left factor. -/
theorem ι_whiskerLeft {R : Type u} [CommRing R] (X : CochainComplex (ModuleCat.{u} R) ℤ)
    {Y Y' : CochainComplex (ModuleCat.{u} R) ℤ} (f : Y ⟶ Y') (q pp n : ℤ) (h : q + pp = n) :
    HomologicalComplex.ιTensorObj X Y q pp n h ≫ (X ◁ f).f n =
      (X.X q ◁ f.f pp) ≫ HomologicalComplex.ιTensorObj X Y' q pp n h := by
  have key := HomologicalComplex.ι_mapBifunctorMap (𝟙 X) f (curriedTensor (ModuleCat.{u} R))
    (ComplexShape.up ℤ) q pp n h
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, curriedTensor_obj_map] at key
  exact key

/-- **The chain-level projection formula is natural in the base-changed complex.**  For a ring
map `φ : A →+* B`, a complex `L` of `B`-modules and a chain map `g : K ⟶ K'` of complexes of
`A`-modules, the comparison `baseChangeTensorIso` of [stacks 06Y1] commutes with `g`.  This is
the naturality the pointwise projection formula at the diagonal was missing. -/
theorem baseChangeTensorIso_inv_naturality (φ : A →+* B)
    {K K' : CochainComplex (ModuleCat.{u} A) ℤ} (g : K ⟶ K')
    (L : CochainComplex (ModuleCat.{u} B) ℤ) :
    ((CochainComplex.restrictScalars φ).obj L ◁ g) ≫ (baseChangeTensorIso φ K' L).inv =
      (baseChangeTensorIso φ K L).inv ≫
        (CochainComplex.restrictScalars φ).map (L ◁ (CochainComplex.extendScalars φ).map g) := by
  ext n : 1
  refine GradedObject.Monoidal.tensorObj_ext _ _ (fun q pp h => ?_)
  have hL : HomologicalComplex.ιTensorObj ((CochainComplex.restrictScalars φ).obj L) K q pp n h ≫
        (((CochainComplex.restrictScalars φ).obj L ◁ g).f n ≫
          (baseChangeTensorIsoX φ K' L n).inv) =
      (projectionFormulaIso φ (L.X q) (K.X pp)).inv ≫
        (ModuleCat.restrictScalars φ).map (L.X q ◁ (ModuleCat.extendScalars φ).map (g.f pp)) ≫
          (ModuleCat.restrictScalars φ).map
            (HomologicalComplex.ιTensorObj L ((CochainComplex.extendScalars φ).obj K')
              q pp n h) :=
    ((Category.assoc _ _ _).symm.trans
      ((ι_whiskerLeft ((CochainComplex.restrictScalars φ).obj L) g q pp n h =≫ _).trans
        ((Category.assoc _ _ _).trans
          (_ ≫= baseChangeTensorIsoX_inv_ι φ K' L n q pp h)))).trans
      ((reassoc_of% projectionFormulaIso_inv_natural_right φ (L.X q) (g.f pp)) _)
  have hR : HomologicalComplex.ιTensorObj ((CochainComplex.restrictScalars φ).obj L) K q pp n h ≫
        ((baseChangeTensorIsoX φ K L n).inv ≫
          (ModuleCat.restrictScalars φ).map
            ((L ◁ (CochainComplex.extendScalars φ).map g).f n)) =
      (projectionFormulaIso φ (L.X q) (K.X pp)).inv ≫
        (ModuleCat.restrictScalars φ).map (L.X q ◁ (ModuleCat.extendScalars φ).map (g.f pp)) ≫
          (ModuleCat.restrictScalars φ).map
            (HomologicalComplex.ιTensorObj L ((CochainComplex.extendScalars φ).obj K')
              q pp n h) :=
    ((reassoc_of% baseChangeTensorIsoX_inv_ι φ K L n q pp h) _).trans
      (_ ≫= (((ModuleCat.restrictScalars φ).map_comp _ _).symm.trans
        ((congrArg (fun t => (ModuleCat.restrictScalars φ).map t)
            (ι_whiskerLeft L ((CochainComplex.extendScalars φ).map g) q pp n h)).trans
          ((ModuleCat.restrictScalars φ).map_comp _ _))))
  exact hL.trans hR.symm

/-- The projection formula of [stacks 06Y1] is natural in the base-changed complex, read on the
forward maps. -/
theorem baseChangeTensorIso_hom_naturality (φ : A →+* B)
    {K K' : CochainComplex (ModuleCat.{u} A) ℤ} (g : K ⟶ K')
    (L : CochainComplex (ModuleCat.{u} B) ℤ) :
    (CochainComplex.restrictScalars φ).map (L ◁ (CochainComplex.extendScalars φ).map g) ≫
        (baseChangeTensorIso φ K' L).hom =
      (baseChangeTensorIso φ K L).hom ≫
        ((CochainComplex.restrictScalars φ).obj L ◁ g) := by
  exact inv_square (e := (baseChangeTensorIso φ K L).symm) (e' := (baseChangeTensorIso φ K' L).symm)
    (baseChangeTensorIso_inv_naturality φ g L)

/-- **Extension of scalars along a map and then along a retraction of it is the identity**, as an
isomorphism of functors on complexes.  `Dualizing.extendScalarsRetractionComplexIso` is its
value at a complex; what is added here is that the identification is natural, which is what the
projection formula at the diagonal needs in order to be natural in its tensor factor. -/
def extendScalarsRetractionNatIso (φ : A →+* B) (ψ : B →+* A) (h : ψ.comp φ = RingHom.id A) :
    CochainComplex.extendScalars φ ⋙ CochainComplex.extendScalars ψ ≅
      𝟭 (CochainComplex (ModuleCat.{u} A) ℤ) := by
  have e := NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} φ ψ)
    (ComplexShape.up ℤ)
  rw [h] at e
  exact e.symm ≪≫ NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId.{u, u} A)
      (ComplexShape.up ℤ) ≪≫
    CategoryTheory.Functor.mapHomologicalComplexIdIso _ _

/-- **The chain-level projection formula at a retraction, as an isomorphism of functors.**  Let
`φ : A →+* B` have the retraction `ψ : B →+* A` and fix a complex `P` of `A`-modules.  Then

`ψ_*(P ⊗_A Z) ≅ ψ_*P ⊗_B φ^*Z`,   naturally in `Z`.

On a fixed `Z` this is the projection formula of [stacks 06Y1] read along the retraction, which
is how `Dualizing.singleTargetTensorExtendScalarsIso` uses it at `P` the tensor unit; the content
here is that the identification is natural in `Z`, by
`Dualizing.baseChangeTensorIso_hom_naturality` and the naturality of
`Dualizing.extendScalarsRetractionNatIso`. -/
def retractionProjectionNatIso (φ : A →+* B) (ψ : B →+* A) (h : ψ.comp φ = RingHom.id A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    MonoidalCategory.tensorLeft P ⋙ CochainComplex.restrictScalars ψ ≅
      CochainComplex.extendScalars φ ⋙
        MonoidalCategory.tensorLeft ((CochainComplex.restrictScalars ψ).obj P) :=
  NatIso.ofComponents
    (fun Z =>
      (CochainComplex.restrictScalars ψ).mapIso
          ((MonoidalCategory.tensorLeft P).mapIso
            ((extendScalarsRetractionNatIso φ ψ h).app Z).symm) ≪≫
        baseChangeTensorIso ψ ((CochainComplex.extendScalars φ).obj Z) P)
    (fun {Z Z'} f => by
      have hnat : f ≫ ((extendScalarsRetractionNatIso φ ψ h).app Z').inv =
          ((extendScalarsRetractionNatIso φ ψ h).app Z).inv ≫
            (CochainComplex.extendScalars ψ).map ((CochainComplex.extendScalars φ).map f) :=
        (extendScalarsRetractionNatIso φ ψ h).inv.naturality f
      dsimp only [CategoryTheory.Functor.comp_map, Iso.trans_hom,
        CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, curriedTensor_obj_map]
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
        ← MonoidalCategory.whiskerLeft_comp, hnat, MonoidalCategory.whiskerLeft_comp,
        CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc,
        baseChangeTensorIso_hom_naturality ψ ((CochainComplex.extendScalars φ).map f) P])

end ChainLevel

section Pasting

variable {C : Type*} [Category* C]

/-- Two naturality squares side by side paste into one. -/
private lemma paste {X X' Y Y' W W' : C} {u : X ⟶ X'} {a : X ⟶ Y} {a' : X' ⟶ Y'} {v : Y ⟶ Y'}
    {b : Y ⟶ W} {b' : Y' ⟶ W'} {w : W ⟶ W'} (h1 : u ≫ a' = a ≫ v) (h2 : v ≫ b' = b ≫ w) :
    u ≫ a' ≫ b' = (a ≫ b) ≫ w := by
  rw [← Category.assoc, h1, Category.assoc, h2, Category.assoc]

/-- A functor carries a commuting square to a commuting square. -/
private lemma map_square {D : Type*} [Category* D] (F : C ⥤ D) {X Y W T : C} {a : X ⟶ Y}
    {b : Y ⟶ T} {c : X ⟶ W} {d : W ⟶ T} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

end Pasting

section Descent

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]

/-- K-flatness as a predicate on cochain complexes, spelled so that the descent lemmas of
`ModuleSystemRlimTensor` can consume it. -/
abbrev kFlatProp : CochainComplex (ModuleCat.{u} A) ℤ → Prop := fun L => L.KFlat

/-- Every cochain complex of `A`-modules has a K-flat resolution, [stacks 06Y4]. -/
lemma exists_kFlat (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ (L : CochainComplex (ModuleCat.{u} A) ℤ) (s : L ⟶ M), kFlatProp A L ∧ QuasiIso s := by
  obtain ⟨K, f, hK, -, hf, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} M
  exact ⟨K, f, hK, hf⟩

/-- The source of the projection formula at the diagonal, as a functor of the tensor factor:
`Z ↦ Δ_*(M ⊗ᴸ_A Z)`. -/
noncomputable def diagonalTensorRestrictFunctor (M : DerivedCategory (ModuleCat.{u} A)) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} (A ⊗[R] A)) :=
  (CategoryTheory.Functor.curry.obj
      (StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor A)).obj M ⋙
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory

/-- The target of the projection formula at the diagonal, as a functor of the tensor factor:
`Z ↦ Δ_*M ⊗ᴸ_B p₁^*Z`. -/
noncomputable def diagonalRestrictTensorFunctor (M : DerivedCategory (ModuleCat.{u} A)) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} (A ⊗[R] A)) :=
  diagonalDerivedExtension R A ⋙
    (CategoryTheory.Functor.curry.obj
        (StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A))).obj
      ((ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj M)

/-- On a K-flat complex, the derived base change along the left coprojection is computed by the
chain-level base change. -/
noncomputable def diagonalExtensionKFlatIso (Z : CochainComplex (ModuleCat.{u} A) ℤ)
    (hZ : Z.KFlat) :
    (diagonalDerivedExtension R A).obj (DerivedCategory.Q.obj Z) ≅
      DerivedCategory.Q.obj
        ((CochainComplex.extendScalars
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj Z) :=
  ((diagonalDerivedExtensionIsoTotalDerived R A).app (DerivedCategory.Q.obj Z)).symm ≪≫
    @asIso _ _ _ _ ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).comparison.app Z)
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* A ⊗[R] A)).comparison_isIso_of_kFlat Z hZ)

/-- The chain-level computation of the derived base change along the left coprojection is natural
in chain maps between K-flat complexes. -/
private lemma diagonalExtensionKFlatIso_naturality (Z Z' : CochainComplex (ModuleCat.{u} A) ℤ)
    (hZ : Z.KFlat) (hZ' : Z'.KFlat) (g : Z ⟶ Z') :
    (diagonalDerivedExtension R A).map (DerivedCategory.Q.map g) ≫
        (diagonalExtensionKFlatIso R A Z' hZ').hom =
      (diagonalExtensionKFlatIso R A Z hZ).hom ≫
        DerivedCategory.Q.map
          ((CochainComplex.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).map g) := by
  have hcomp : (totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).functor.map
          (DerivedCategory.Q.map g) ≫
        (@asIso _ _ _ _ ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).comparison.app Z')
          ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeLeftRingHom :
              A →+* A ⊗[R] A)).comparison_isIso_of_kFlat Z' hZ')).hom =
      (@asIso _ _ _ _ ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).comparison.app Z)
          ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeLeftRingHom :
              A →+* A ⊗[R] A)).comparison_isIso_of_kFlat Z hZ)).hom ≫
        DerivedCategory.Q.map
          ((CochainComplex.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).map g) :=
    (totalDerivedExtensionScalars.{u, u, u}
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).comparison.naturality g
  have hdiag : (diagonalDerivedExtension R A).map (DerivedCategory.Q.map g) ≫
        ((diagonalDerivedExtensionIsoTotalDerived R A).app (DerivedCategory.Q.obj Z')).inv =
      ((diagonalDerivedExtensionIsoTotalDerived R A).app (DerivedCategory.Q.obj Z)).inv ≫
        (totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).functor.map
          (DerivedCategory.Q.map g) :=
    (diagonalDerivedExtensionIsoTotalDerived R A).inv.naturality (DerivedCategory.Q.map g)
  dsimp only [diagonalExtensionKFlatIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hdiag, Category.assoc]
  exact (_ ≫= hcomp).trans (Category.assoc _ _ _).symm

/-- The inverse of `Dualizing.diagonalExtensionKFlatIso` is natural as well. -/
private lemma diagonalExtensionKFlatIso_inv_naturality
    (Z Z' : CochainComplex (ModuleCat.{u} A) ℤ) (hZ : Z.KFlat) (hZ' : Z'.KFlat) (g : Z ⟶ Z') :
    DerivedCategory.Q.map
          ((CochainComplex.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).map g) ≫
        (diagonalExtensionKFlatIso R A Z' hZ').inv =
      (diagonalExtensionKFlatIso R A Z hZ).inv ≫
        (diagonalDerivedExtension R A).map (DerivedCategory.Q.map g) := by
  exact inv_square (diagonalExtensionKFlatIso_naturality R A Z Z' hZ hZ' g)

/-- The comparison of the tensor product of `P` with a K-flat complex is natural in the K-flat
factor. -/
private lemma tensorIso_naturality_whiskerLeft {S : Type u} [CommRing S]
    (d : StacksDraft.DerivedHom.DerivedHomData S) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    {Z Z' : CochainComplex (ModuleCat.{u} S) ℤ} (hZ : Z.KFlat) (hZ' : Z'.KFlat) (g : Z ⟶ Z') :
    d.tensor.map (show ((DerivedCategory.Q.obj P, DerivedCategory.Q.obj Z) :
          DerivedCategory (ModuleCat.{u} S) × DerivedCategory (ModuleCat.{u} S)) ⟶
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Z') from
        (𝟙 _, DerivedCategory.Q.map g)) ≫ (d.tensorIso P Z' hZ').hom =
      (d.tensorIso P Z hZ).hom ≫ DerivedCategory.Q.map (P ◁ g) := by
  have h := d.tensorIso_naturality (𝟙 P) g hZ hZ'
  rw [CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom] at h
  exact h

/-- **The projection formula at the diagonal on a pair of chain-level data.**  For a complex `P`
of `A`-modules and a K-flat complex `Z`,

`Δ_*(P ⊗ᴸ_A Z) ≅ Δ_*P ⊗ᴸ_B p₁^*Z`,

every derived functor in sight being computed by its chain-level model. -/
noncomputable def diagonalProjectionComponent (P Z : CochainComplex (ModuleCat.{u} A) ℤ)
    (hZ : Z.KFlat) :
    (diagonalTensorRestrictFunctor R A (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj Z) ≅
      (diagonalRestrictTensorFunctor R A (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj Z) :=
  (show (diagonalTensorRestrictFunctor R A (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj Z) ≅
      (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R :
            A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (P ⊗ Z)) from
    (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.lmul' R :
          A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.mapIso
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction A).tensorIso P Z hZ)) ≪≫
  (show (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R :
            A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (P ⊗ Z)) ≅
      DerivedCategory.Q.obj
        ((CochainComplex.restrictScalars
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj (P ⊗ Z)) from
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R :
        A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategoryFactors.app (P ⊗ Z)) ≪≫
  DerivedCategory.Q.mapIso
    ((retractionProjectionNatIso
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
      (lmul'_comp_includeLeftRingHom R A) P).app Z) ≪≫
  ((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction (A ⊗[R] A)).tensorIso
    ((CochainComplex.restrictScalars
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj P)
    ((CochainComplex.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj Z)
    (kFlat_baseChange _ Z hZ)).symm ≪≫
  (show (StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
        (DerivedCategory.Q.obj
          ((CochainComplex.restrictScalars
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj P),
          DerivedCategory.Q.obj
            ((CochainComplex.extendScalars
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj Z)) ≅
      (diagonalRestrictTensorFunctor R A (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj Z) from
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).mapIso
      ((show DerivedCategory.Q.obj
            ((CochainComplex.restrictScalars
              (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj P) ≅
          (ModuleCat.restrictScalars.{u}
              (Algebra.TensorProduct.lmul' R :
                A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj
            (DerivedCategory.Q.obj P) from
        ((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R :
            A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategoryFactors.app P).symm).prod
        (diagonalExtensionKFlatIso R A Z hZ).symm))

/-- The chain-level projection formula at the diagonal is natural in chain maps between K-flat
complexes. -/
lemma diagonalProjectionComponent_naturality (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z Z' : CochainComplex (ModuleCat.{u} A) ℤ) (hZ : kFlatProp A Z) (hZ' : kFlatProp A Z')
    (g : Z ⟶ Z') :
    (diagonalTensorRestrictFunctor R A (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map g) ≫
        (diagonalProjectionComponent R A P Z' hZ').hom =
      (diagonalProjectionComponent R A P Z hZ).hom ≫
        (diagonalRestrictTensorFunctor R A (DerivedCategory.Q.obj P)).map
          (DerivedCategory.Q.map g) := by
  have h1 := tensorIso_naturality_whiskerLeft
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction A) P hZ hZ' g
  have h3 : (CochainComplex.restrictScalars
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).map (P ◁ g) ≫
        ((retractionProjectionNatIso
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
          (lmul'_comp_includeLeftRingHom R A) P).app Z').hom =
      ((retractionProjectionNatIso
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
          (lmul'_comp_includeLeftRingHom R A) P).app Z).hom ≫
        ((CochainComplex.restrictScalars
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj P ◁
          (CochainComplex.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).map g) :=
    (retractionProjectionNatIso
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
      (lmul'_comp_includeLeftRingHom R A) P).hom.naturality g
  have h4 := tensorIso_naturality_whiskerLeft
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction (A ⊗[R] A))
    ((CochainComplex.restrictScalars
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj P)
    (kFlat_baseChange _ Z hZ) (kFlat_baseChange _ Z' hZ')
    ((CochainComplex.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).map g)
  have h5 : (show ((DerivedCategory.Q.obj
            ((CochainComplex.restrictScalars
              (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj P),
          DerivedCategory.Q.obj
            ((CochainComplex.extendScalars
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj Z)) :
          DerivedCategory (ModuleCat.{u} (A ⊗[R] A)) ×
            DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) ⟶
        (DerivedCategory.Q.obj
          ((CochainComplex.restrictScalars
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj P),
          DerivedCategory.Q.obj
            ((CochainComplex.extendScalars
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj Z')) from
        (𝟙 _, DerivedCategory.Q.map
          ((CochainComplex.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).map g))) ≫
        ((((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R :
            A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategoryFactors.app P).symm.prod
          (diagonalExtensionKFlatIso R A Z' hZ').symm).hom) =
      ((((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R :
            A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategoryFactors.app P).symm.prod
          (diagonalExtensionKFlatIso R A Z hZ).symm).hom) ≫
        (show ((ModuleCat.restrictScalars.{u}
              (Algebra.TensorProduct.lmul' R :
                A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj (DerivedCategory.Q.obj P),
            (diagonalDerivedExtension R A).obj (DerivedCategory.Q.obj Z)) ⟶
          ((ModuleCat.restrictScalars.{u}
              (Algebra.TensorProduct.lmul' R :
                A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj (DerivedCategory.Q.obj P),
            (diagonalDerivedExtension R A).obj (DerivedCategory.Q.obj Z')) from
          (𝟙 _, (diagonalDerivedExtension R A).map (DerivedCategory.Q.map g))) := by
    refine Prod.ext ?_ ?_
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact diagonalExtensionKFlatIso_inv_naturality R A Z Z' hZ hZ' g
  exact paste (map_square _ h1)
    (paste ((ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R :
        A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategoryFactors.hom.naturality (P ◁ g))
      (paste (map_square DerivedCategory.Q h3)
        (paste (inv_square h4) (map_square _ h5))))

/-- **The projection formula at the diagonal, naturally in the tensor factor, on a chain-level
tensor factor.**  For a complex `P` of `A`-modules,

`Δ_*(P ⊗ᴸ_A -) ≅ Δ_*P ⊗ᴸ_B p₁^*(-)`   as functors `D(A) ⥤ D(B)`.

The two sides are computed on K-flat complexes by `Dualizing.diagonalProjectionComponent`, and
that family is natural in chain maps between K-flat complexes, so it descends to all of `D(A)` by
[stacks 06Y4]. -/
noncomputable def diagonalProjectionNatIsoOfComplex
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    diagonalTensorRestrictFunctor R A (DerivedCategory.Q.obj P) ≅
      diagonalRestrictTensorFunctor R A (DerivedCategory.Q.obj P) :=
  ModuleSystemRlimTensor.natIsoOfResolutions (kFlatProp A) (exists_kFlat A)
    (diagonalTensorRestrictFunctor R A (DerivedCategory.Q.obj P))
    (diagonalRestrictTensorFunctor R A (DerivedCategory.Q.obj P))
    (fun Z hZ => diagonalProjectionComponent R A P Z hZ)
    (fun Z Z' hZ hZ' g => diagonalProjectionComponent_naturality R A P Z Z' hZ hZ' g)

/-- **The projection formula at the diagonal, naturally in the tensor factor.**  Let `R → A` be
flat, put `B = A ⊗[R] A`, write `p₁ : A → B` for the left coprojection and `Δ : B → A` for the
multiplication map.  For every object `M` of `D(A)`,

`Δ_*(M ⊗ᴸ_A Z) ≅ Δ_*M ⊗ᴸ_B p₁^*Z`,   naturally in `Z`.

`Dualizing.nonempty_tensor_diagonalObject_iso_restrictScalars_lmul` is the case `M = A[0]` of
this read pointwise; what is added is both the second variable and, above all, the **naturality
in `Z`**, which is what the Yoneda reduction of the enriched adjunction `Δ_* ⊣ Δ^!` needs and
which the pointwise statement, each of whose components is read off a separately chosen K-flat
representative, cannot supply. -/
noncomputable def diagonalProjectionNatIso (M : DerivedCategory (ModuleCat.{u} A)) :
    diagonalTensorRestrictFunctor R A M ≅ diagonalRestrictTensorFunctor R A M :=
  letI e : DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage M) ≅ M :=
    DerivedCategory.Q.objObjPreimageIso M
  CategoryTheory.Functor.isoWhiskerRight
      ((CategoryTheory.Functor.curry.obj
        (StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor A)).mapIso e.symm)
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory ≪≫
    diagonalProjectionNatIsoOfComplex R A (DerivedCategory.Q.objPreimage M) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (diagonalDerivedExtension R A)
      ((CategoryTheory.Functor.curry.obj
        (StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A))).mapIso
        ((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R :
            A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.mapIso e))

end Descent

end

end Dualizing

end
