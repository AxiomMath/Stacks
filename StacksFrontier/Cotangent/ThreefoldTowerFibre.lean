module

public import StacksFrontier.Cotangent.ThreefoldPolynomialOnTop
public import StacksFrontier.Cotangent.StandardResolutionIsResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionCofinality
public import StacksFrontier.AlgebraicTopology.SimplicialObject.HomotopyEquivalenceProjectivity
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomotopy

/-!
# The fibres of `u₃ : C_{C/B/A} ⥤ C_{C/B}`

Let `A → B → C` be ring maps and let `u₃ : C_{C/B/A} ⥤ C_{C/B}` be the functor
`(P → B, Q → C) ↦ (Q ⊗_P B → C)` of Tag 08QT. Lower shriek along `u₃` is the left Kan extension
along `u₃`, computed at an object `(Q̄ → C)` of `C_{C/B}` by the colimit over the category of
costructured arrows of `u₃` over it: the towers `(P → B, Q → C)` together with a map
`Q ⊗_P B → Q̄` over `C`. The proof of Tag 08QW identifies that category with the site
`C_{Q̄/B/A}` of towers over `Q̄` ("again beware of reversal of arrows"), and this file does so:
a tower `(P → B, Q → Q̄)` over `Q̄` goes to the tower `(P → B, Q → Q̄ → C)` over `C` with the
map `Q ⊗_P B → Q̄` induced by `Q → Q̄`.

Since `Q̄` is a polynomial algebra over `B`, Tag 08QV supplies a cosimplicial object of
`C_{Q̄/B/A}`, the towers `(P_n → B, P_n[E] → Q̄)` of the standard resolution `P_• → B` of `B`
over `A`, from which every simplicial set of morphisms into a tower over `Q̄` is homotopy
equivalent to a singleton, and whose image under `u₃` is constant with value `(Q̄ → Q̄)`. This
file draws the consequence for the counit of lower shriek along `u₃`.

## Main definitions

* `CommAlgCat.fibreAlgebra`: the polynomial `B`-algebra `Q̄` of an object `(Q̄ → C)` of
  `C_{C/B}`, with `A` acting through `B`.
* `CommAlgCat.fibreTowerFunctor`: towers over `Q̄` are towers over `C`.
* `CommAlgCat.fibreTowerCostructured`: the functor from towers over `Q̄` to the costructured
  arrows of `u₃` over `(Q̄ → C)`.
* `CommAlgCat.fibreTowerCosimplicial` and `CommAlgCat.fibreSmallCosimplicial`: the cosimplicial
  object of Tag 08QV for `A → B → Q̄`, in `C_{Q̄/B/A}` and in its small model.

## Main results

* `CommAlgCat.fibreTowerCostructured` is an equivalence of categories: **the fibre of `u₃` over
  `(Q̄ → C)` is `C_{Q̄/B/A}`**, as the proof of Tag 08QW states.
* `CommAlgCat.isPointResolution_fibreSmallCosimplicial`: the cosimplicial object of the fibre is
  a point resolution in the sense of Tag 08Q9.
* `CommAlgCat.final_costructuredToOver`: the comparison of the fibre of `u₃` over `(Q̄ → C)` with
  the costructured arrows of the identity over `(Q̄ → C)` is final.
* `CommAlgCat.isIso_lanAdjunction_counit_app`: hence **the counit of `Lan_{u₃} ⊣ u₃^*` is
  invertible**, which is the degree-zero part of `Lg_{3,!} ∘ g₃⁻¹ = id`.

## References

* [Stacks Project, Tag 08QW](https://stacks.math.columbia.edu/tag/08QW)
* [Stacks Project, Tag 08QV](https://stacks.math.columbia.edu/tag/08QV)
* [Stacks Project, Tag 08QT](https://stacks.math.columbia.edu/tag/08QT)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  (U : PolynomialAugmentation B (towerRelativeAlgebra B C))

/-- The polynomial `B`-algebra `Q̄` of an object `(Q̄ → C)` of `C_{C/B}`, on which `A` acts
through `B`. The ring `A` is recorded in the name so that the action of `A` can be an
instance. -/
def fibreAlgebra (A : Type u) {B : Type u} [CommRing B] {C : Type u} [CommRing C] [Algebra B C]
    (U : PolynomialAugmentation B (towerRelativeAlgebra B C)) : Type u :=
  U.obj.left

/-- The ring structure of `Q̄`. -/
instance : CommRing (fibreAlgebra A U) := inferInstanceAs (CommRing U.obj.left)

/-- The `B`-algebra structure of `Q̄`. -/
instance : Algebra B (fibreAlgebra A U) := inferInstanceAs (Algebra B U.obj.left)

/-- `A` acts on `Q̄` through `B`. -/
instance : Algebra A (fibreAlgebra A U) :=
  ((algebraMap B (fibreAlgebra A U)).comp (algebraMap A B)).toAlgebra

/-- The actions of `A` and `B` on `Q̄` form a scalar tower. -/
instance : IsScalarTower A B (fibreAlgebra A U) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The augmentation `Q̄ → C`, as a map of `B`-algebras. -/
abbrev fibreAugmentationHom : fibreAlgebra A U →ₐ[B] C := CommAlgCat.Hom.hom U.obj.hom

/-- The augmentation `Q̄ → C`, as a map of `A`-algebras. -/
abbrev fibreAugmentation : towerTotalAlgebra A (fibreAlgebra A U) ⟶ towerTotalAlgebra A C :=
  CommAlgCat.ofHom ((fibreAugmentationHom U).restrictScalars A)

/-- A tower `(P → B, Q → Q̄)` over `Q̄`, read as a tower over `C` through `Q̄ → C`. -/
def fibreTowerComma (T : TowerComma A B (fibreAlgebra A U)) : TowerComma A B C where
  left := T.left
  right := Over.mk (T.right.hom ≫ fibreAugmentation U)
  hom := T.hom

/-- A polynomial tower over `Q̄`, read as a tower over `C`, is a polynomial tower. -/
lemma isPolynomialTower_fibreTowerComma (T : PolynomialTower A B (fibreAlgebra A U)) :
    IsPolynomialTower A B C (fibreTowerComma U T.obj) := by
  refine ⟨T.property.1, ?_⟩
  change T.obj.hom ≫ T.obj.right.hom ≫ fibreAugmentation U = _
  rw [← Category.assoc, T.property.2, Category.assoc]
  apply CommAlgCat.hom_ext
  refine AlgHom.ext fun p => ?_
  exact (fibreAugmentationHom U).commutes _


/-- A morphism of towers over `Q̄`, read as a morphism of towers over `C`. -/
def fibreTowerCommaMap {T T' : TowerComma A B (fibreAlgebra A U)} (g : T ⟶ T') :
    fibreTowerComma U T ⟶ fibreTowerComma U T' where
  left := g.left
  right := Over.homMk g.right.left (by
    change g.right.left ≫ T'.right.hom ≫ fibreAugmentation U = T.right.hom ≫ fibreAugmentation U
    rw [← Category.assoc, Over.w g.right])
  w := g.w

variable (A B C) in
/-- Towers over `Q̄` are towers over `C`, through `Q̄ → C`. -/
def fibreTowerFunctor : PolynomialTower A B (fibreAlgebra A U) ⥤ PolynomialTower A B C where
  obj T := ⟨fibreTowerComma U T.obj, isPolynomialTower_fibreTowerComma U T⟩
  map g := ObjectProperty.homMk (fibreTowerCommaMap U g.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The map `Q ⊗_P B → Q̄` of a tower over `Q̄`, which `u₃` of the tower over `C` it defines
carries to `Q̄`: the augmentation of the base-changed tower of Tag 08QT. -/
def fibreTowerBaseChange (T : PolynomialTower A B (fibreAlgebra A U)) :
    (polynomialTowerThirdAugmentations A B C).obj ((fibreTowerFunctor A B C U).obj T) ⟶ U :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom (towerBaseChangeAugmentation T)) (by
    apply CommAlgCat.hom_ext
    apply Algebra.TensorProduct.ext'
    intro b q
    have h1 := towerBaseChangeAugmentation_tmul T b q
    have h2 := towerBaseChangeAugmentation_tmul ((fibreTowerFunctor A B C U).obj T) b q
    change fibreAugmentationHom U (towerBaseChangeAugmentation T (b ⊗ₜ q)) =
      towerBaseChangeAugmentation ((fibreTowerFunctor A B C U).obj T) (b ⊗ₜ q)
    refine (congrArg (fibreAugmentationHom U) h1).trans (Eq.trans ?_ h2.symm)
    rw [map_mul, AlgHom.commutes]
    rfl))


/-- `u₃` of a morphism of towers over `Q̄` is compatible with the maps `Q ⊗_P B → Q̄`. -/
lemma fibreTowerBaseChange_naturality {T T' : PolynomialTower A B (fibreAlgebra A U)}
    (g : T ⟶ T') :
    (polynomialTowerThirdAugmentations A B C).map ((fibreTowerFunctor A B C U).map g) ≫
      fibreTowerBaseChange U T' = fibreTowerBaseChange U T := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply CommAlgCat.hom_ext
  refine AlgHom.ext fun z => ?_
  change towerBaseChangeAugmentation T' (towerBaseChangeMap (fibreTowerCommaMap U g.hom) z) =
    towerBaseChangeAugmentation T z
  induction z using TensorProduct.induction_on with
  | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
  | tmul b q =>
    have h1 := towerBaseChangeMap_tmul (fibreTowerCommaMap U g.hom) b q
    have h2 := towerBaseChangeAugmentation_tmul T' b (CommAlgCat.Hom.hom g.hom.right.left q)
    have h3 := towerBaseChangeAugmentation_tmul T b q
    have h4 := towerRightAugmentation_hom_apply g.hom q
    exact (congrArg _ h1).trans (h2.trans ((congrArg _ h4).trans h3.symm))
  | add x y hx hy => exact (congrArg _ (map_add _ _ _)).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm))

variable (A B C) in
/-- **The fibre of `u₃` over `(Q̄ → C)` is the site of towers over `Q̄`**, as a functor: a tower
`(P → B, Q → Q̄)` over `Q̄` goes to the tower `(P → B, Q → Q̄ → C)` over `C` together with the
map `Q ⊗_P B → Q̄`, an object of the category of costructured arrows of `u₃` over `(Q̄ → C)` in
which the left Kan extension along `u₃` is computed. -/
def fibreTowerCostructured :
    PolynomialTower A B (fibreAlgebra A U) ⥤
      CostructuredArrow (polynomialTowerThird A B C).op (op (op U)) where
  obj T := CostructuredArrow.mk (Y := op (op ((fibreTowerFunctor A B C U).obj T)))
    (fibreTowerBaseChange U T).op.op
  map g := CostructuredArrow.homMk ((fibreTowerFunctor A B C U).map g).op.op
    (congrArg (fun k => k.op.op) (fibreTowerBaseChange_naturality U g))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor from towers over `Q̄` to the fibre of `u₃` over `(Q̄ → C)` is faithful. -/
instance : (fibreTowerCostructured A B C U).Faithful where
  map_injective {T T'} g₁ g₂ h := by
    have h' := congrArg (fun k => k.left.unop.unop) h
    apply ObjectProperty.hom_ext
    apply CommaMorphism.ext
    · exact congrArg (fun k => k.hom.left) h'
    · apply Over.OverMorphism.ext
      exact congrArg (fun k => k.hom.right.left) h'

/-- A morphism of towers over `C` between towers over `Q̄`, compatible with the maps
`Q ⊗_P B → Q̄`, is a morphism of towers over `Q̄`: that compatibility, read on `1 ⊗ q`, says that
`Q → Q'` lies over `Q̄`. -/
lemma fibreTower_right_comp {T T' : PolynomialTower A B (fibreAlgebra A U)}
    (g : (fibreTowerFunctor A B C U).obj T ⟶ (fibreTowerFunctor A B C U).obj T')
    (hw : (polynomialTowerThirdAugmentations A B C).map g ≫ fibreTowerBaseChange U T' =
      fibreTowerBaseChange U T) :
    g.hom.right.left ≫ T'.obj.right.hom = T.obj.right.hom := by
  apply CommAlgCat.hom_ext
  refine AlgHom.ext fun q => ?_
  have h := congrArg (fun m => (CommAlgCat.Hom.hom m.hom.left)
    ((1 : B) ⊗ₜ[↑(towerLeftAlgebra ((fibreTowerFunctor A B C U).obj T).obj)] q)) hw
  have h1 := towerBaseChangeMap_tmul g.hom (1 : B) q
  have h2 := towerBaseChangeAugmentation_tmul T' (1 : B) ((CommAlgCat.Hom.hom g.hom.right.left) q)
  have h3 := towerBaseChangeAugmentation_tmul T (1 : B) q
  simp only [map_one, one_mul] at h2 h3
  exact h2.symm.trans ((congrArg (towerBaseChangeAugmentation T') h1).symm.trans (h.trans h3))

/-- The functor from towers over `Q̄` to the fibre of `u₃` over `(Q̄ → C)` is full. -/
instance : (fibreTowerCostructured A B C U).Full where
  map_surjective {T T'} f := by
    refine ⟨ObjectProperty.homMk
      { left := f.left.unop.unop.hom.left
        right := Over.homMk f.left.unop.unop.hom.right.left
          (fibreTower_right_comp U f.left.unop.unop
            (congrArg (fun k => k.unop.unop) (CostructuredArrow.w f)))
        w := f.left.unop.unop.hom.w }, ?_⟩
    apply CostructuredArrow.hom_ext
    rfl


section EssSurj

variable {U} (W : PolynomialTower A B C)
  (ψ : (polynomialTowerThirdAugmentations A B C).obj W ⟶ U)

/-- The map `Q ⊗_P B → Q̄` of an object `(W, ψ)` of the fibre of `u₃` over `(Q̄ → C)`, as a map
of `B`-algebras out of the tensor product. -/
def fibreBaseChangeHom :
    (B ⊗[↑(towerLeftAlgebra W.obj)] ↑(towerRightAlgebra W.obj)) →ₐ[B] fibreAlgebra A U :=
  CommAlgCat.Hom.hom ψ.hom.left

/-- `1 ⊗ (p · 1) = p ⊗ 1` in `B ⊗_P Q`, and the map `Q ⊗_P B → Q̄` sends it to the image of `p`
in `Q̄`. -/
lemma fibreBaseChange_one_tmul_algebraMap (p : ↑(towerLeftAlgebra W.obj)) :
    fibreBaseChangeHom W ψ ((1 : B) ⊗ₜ[↑(towerLeftAlgebra W.obj)]
      algebraMap ↑(towerLeftAlgebra W.obj) ↑(towerRightAlgebra W.obj) p) =
    algebraMap B (fibreAlgebra A U) (algebraMap ↑(towerLeftAlgebra W.obj) B p) := by
  rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  exact (fibreBaseChangeHom W ψ).commutes (algebraMap ↑(towerLeftAlgebra W.obj) B p)

/-- The map `Q → Q ⊗_P B → Q̄` attached to an object `(W, ψ)` of the fibre of `u₃` over
`(Q̄ → C)`, as a map of `A`-algebras. -/
def fibreTowerRightAug :
    towerRightAlgebra W.obj ⟶ towerTotalAlgebra A (fibreAlgebra A U) :=
  CommAlgCat.ofHom
    { toFun q := fibreBaseChangeHom W ψ ((1 : B) ⊗ₜ[↑(towerLeftAlgebra W.obj)] q)
      map_one' := by
        rw [← Algebra.TensorProduct.one_def]
        exact map_one _
      map_mul' x y := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      map_zero' := by rw [TensorProduct.tmul_zero, map_zero]
      map_add' x y := by rw [TensorProduct.tmul_add, map_add]
      commutes' a := by
        change fibreBaseChangeHom W ψ ((1 : B) ⊗ₜ[↑(towerLeftAlgebra W.obj)]
          algebraMap A ↑(towerRightAlgebra W.obj) a) = _
        rw [IsScalarTower.algebraMap_apply A ↑(towerLeftAlgebra W.obj)
          ↑(towerRightAlgebra W.obj), fibreBaseChange_one_tmul_algebraMap,
          ← IsScalarTower.algebraMap_apply A ↑(towerLeftAlgebra W.obj) B]
        rfl }

/-- The map `Q → Q̄` attached to `(W, ψ)` sends `q` to the image of `1 ⊗ q` under `ψ`. -/
lemma fibreTowerRightAug_apply (q : ↑(towerRightAlgebra W.obj)) :
    CommAlgCat.Hom.hom (fibreTowerRightAug W ψ) q =
      fibreBaseChangeHom W ψ ((1 : B) ⊗ₜ[↑(towerLeftAlgebra W.obj)] q) := rfl

/-- The tower over `Q̄` attached to an object `(W, ψ)` of the fibre of `u₃` over `(Q̄ → C)`:
`(P → B, Q → Q ⊗_P B → Q̄)`. -/
def fibreTowerOfCostructuredComma : TowerComma A B (fibreAlgebra A U) where
  left := W.obj.left
  right := Over.mk (fibreTowerRightAug W ψ)
  hom := W.obj.hom

/-- The tower over `Q̄` attached to an object `(W, ψ)` of the fibre of `u₃` is a polynomial tower.
-/
lemma isPolynomialTower_fibreTowerOfCostructuredComma :
    IsPolynomialTower A B (fibreAlgebra A U) (fibreTowerOfCostructuredComma W ψ) := by
  refine ⟨W.property.1, ?_⟩
  apply CommAlgCat.hom_ext
  refine AlgHom.ext fun p => ?_
  exact fibreBaseChange_one_tmul_algebraMap W ψ p

/-- The tower over `Q̄` attached to an object `(W, ψ)` of the fibre of `u₃` over `(Q̄ → C)`. -/
def fibreTowerOfCostructured : PolynomialTower A B (fibreAlgebra A U) :=
  ⟨fibreTowerOfCostructuredComma W ψ, isPolynomialTower_fibreTowerOfCostructuredComma W ψ⟩

/-- The tower over `C` defined by the tower over `Q̄` attached to `(W, ψ)` is `W` again. -/
def fibreTowerFunctorObjIso :
    (fibreTowerFunctor A B C U).obj (fibreTowerOfCostructured W ψ) ≅ W :=
  ObjectProperty.isoMk _ (Comma.isoMk (Iso.refl _) (Over.isoMk (Iso.refl _) (by
    apply CommAlgCat.hom_ext
    refine AlgHom.ext fun (q : ↑(towerRightAlgebra W.obj)) => ?_
    have h := congrArg (fun m => (CommAlgCat.Hom.hom m) ((1 : B) ⊗ₜ[↑(towerLeftAlgebra W.obj)] q))
      (Over.w ψ.hom)
    have h2 := towerBaseChangeAugmentation_tmul W (1 : B) q
    simp only [map_one, one_mul] at h2
    exact (h.trans h2).symm)) (by
    change W.obj.hom ≫ 𝟙 _ = 𝟙 _ ≫ W.obj.hom
    rw [Category.comp_id, Category.id_comp]))

/-- Under that identification, the map `Q ⊗_P B → Q̄` of the tower over `Q̄` is `ψ`. -/
lemma fibreTowerFunctorObjIso_hom_comp :
    (polynomialTowerThirdAugmentations A B C).map (fibreTowerFunctorObjIso W ψ).hom ≫ ψ =
      fibreTowerBaseChange U (fibreTowerOfCostructured W ψ) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply CommAlgCat.hom_ext
  refine AlgHom.ext fun (z : B ⊗[↑(towerLeftAlgebra W.obj)] ↑(towerRightAlgebra W.obj)) => ?_
  change fibreBaseChangeHom W ψ (towerBaseChangeMap (fibreTowerFunctorObjIso W ψ).hom.hom z) =
    towerBaseChangeAugmentation (fibreTowerOfCostructured W ψ) z
  induction z using TensorProduct.induction_on with
  | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
  | tmul b q =>
    have h1 := towerBaseChangeMap_tmul (fibreTowerFunctorObjIso W ψ).hom.hom b q
    have h2 := towerBaseChangeAugmentation_tmul (fibreTowerOfCostructured W ψ) b q
    refine (congrArg _ h1).trans (Eq.trans ?_ h2.symm)
    change fibreBaseChangeHom W ψ (b ⊗ₜ q) =
      algebraMap B (fibreAlgebra A U) b * fibreBaseChangeHom W ψ ((1 : B) ⊗ₜ q)
    rw [← (fibreBaseChangeHom W ψ).commutes b, ← map_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  | add x y hx hy => exact (congrArg _ (map_add _ _ _)).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm))

end EssSurj

/-- Every object of the fibre of `u₃` over `(Q̄ → C)` is isomorphic to the image of a tower over
`Q̄`. -/
instance : (fibreTowerCostructured A B C U).EssSurj where
  mem_essImage j := by
    refine ⟨fibreTowerOfCostructured j.left.unop.unop j.hom.unop.unop,
      ⟨CostructuredArrow.isoMk (fibreTowerFunctorObjIso _ _).op.op
        (congrArg (fun k => k.op.op)
          (fibreTowerFunctorObjIso_hom_comp j.left.unop.unop j.hom.unop.unop))⟩⟩


/-! ### The cosimplicial object of the fibre -/

section Resolution

variable (A)

/-- The set of variables of a chosen presentation `Q̄ = B[E]`. -/
def fibreVars : Type u := U.property.choose

/-- A chosen presentation `Q̄ = B[E]` of the polynomial `B`-algebra `Q̄`. -/
def fibrePresentation : MvPolynomial (fibreVars U) B ≃ₐ[B] fibreAlgebra A U :=
  U.property.choose_spec.some

/-- The towers `(P_n → B, P_n[E] → Q̄)` of the standard resolution `P_• → B` of `B` over `A`, as a
cosimplicial object of the site of towers over `Q̄`: the cosimplicial object of Tag 08QV for the
ring maps `A → B → Q̄`. -/
def fibreTowerCosimplicial :
    CosimplicialObject (polynomialTowerSite A B (fibreAlgebra A U)) :=
  towerCosimplicialObject (standardResolution.{u, u} A (towerBaseAlgebra A B)).hom
    (fibrePresentation A U)
    (standardResolution_isResolution.{u, u} A (towerBaseAlgebra A B)).isPolynomialAlgebra

omit [Algebra A C] [IsScalarTower A B C] in
/-- **Tag 08QV, the hypothesis of Tag 08Q9 for the fibre**: every simplicial set of morphisms
from the towers of the standard resolution into a tower over `Q̄` is homotopy equivalent to a
singleton. -/
lemma exists_homotopyEquivalences_fibreTowerCosimplicial
    (W : polynomialTowerSite A B (fibreAlgebra A U)) :
    ∃ f : (fibreTowerCosimplicial A U).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      SimplicialObject.homotopyEquivalences (Type u) f :=
  exists_homotopyEquivalences_towerMor _ _ _
    (standardResolution_isResolution.{u, u} A (towerBaseAlgebra A B)).trivialKanFibration W

/-- The small model of the site of towers over `Q̄`: the same category with its morphisms lifted
to the universe of its objects. -/
abbrev FibreSite (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {C : Type u}
    [CommRing C] [Algebra B C] (U : PolynomialAugmentation B (towerRelativeAlgebra B C)) :
    Type (u + 1) :=
  AsSmall.{u + 1} (polynomialTowerSite A B (fibreAlgebra A U))

/-- The cosimplicial object of the fibre, in the small model. -/
def fibreSmallCosimplicial : CosimplicialObject (FibreSite A U) :=
  fibreTowerCosimplicial A U ⋙ AsSmall.up

omit [Algebra A C] [IsScalarTower A B C] in
/-- **The cosimplicial object of the fibre is a point resolution of the small model.** -/
theorem isPointResolution_fibreSmallCosimplicial :
    Stacks.ChaoticSite.IsPointResolution (fibreSmallCosimplicial A U) := fun W => by
  obtain ⟨f, hf⟩ := exists_homotopyEquivalences_fibreTowerCosimplicial A U (ULift.down W)
  have h := SimplicialObject.homotopyEquivalences_whiskerRight
    _root_.CategoryTheory.uliftFunctor.{u + 1} hf
  let e : (fibreSmallCosimplicial A U).op ⋙ yoneda.obj W ≅
      (fibreTowerCosimplicial A U).op ⋙ yoneda.obj (ULift.down W) ⋙
        _root_.CategoryTheory.uliftFunctor.{u + 1} :=
    Iso.refl _
  let e' : (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1} ⋙
      _root_.CategoryTheory.uliftFunctor.{u + 1} ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 2} :=
    NatIso.ofComponents (fun _ => Equiv.toIso (Equiv.ulift.trans Equiv.punitEquivPUnit)) (by
      intros; rfl)
  exact ⟨e.hom ≫ Functor.whiskerRight f _root_.CategoryTheory.uliftFunctor.{u + 1} ≫ e'.hom,
    SimplicialObject.homotopyEquivalences_iso_comp_iso e _ e' h⟩

/-- The towers of the standard resolution, as a simplicial object of the category of towers
over `Q̄`. -/
abbrev fibreTowerSimplicial : SimplicialObject (PolynomialTower A B (fibreAlgebra A U)) :=
  towerSimplicialOfResolution (standardResolution.{u, u} A (towerBaseAlgebra A B)).hom
    (fibrePresentation A U)
    (standardResolution_isResolution.{u, u} A (towerBaseAlgebra A B)).isPolynomialAlgebra

/-- **`u₃` of each tower `(P_n → B, P_n[E] → Q̄)` is `Q̄` itself**: the map
`B ⊗_{P_n} P_n[E] → Q̄` is invertible, being `B ⊗_{P_n} P_n[E] = B[E] = Q̄`. -/
instance isIso_fibreTowerBaseChange_simplicial (m : SimplexCategoryᵒᵖ) :
    IsIso (fibreTowerBaseChange U ((fibreTowerSimplicial A U).obj m)) := by
  have hbij : Function.Bijective
      (towerBaseChangeAugmentation ((fibreTowerSimplicial A U).obj m)) := by
    have heq := towerBaseChangeAugmentation_eq_algEquiv
      (standardResolution.{u, u} A (towerBaseAlgebra A B)).hom (fibrePresentation A U)
      (standardResolution_isResolution.{u, u} A (towerBaseAlgebra A B)).isPolynomialAlgebra m
    let e := towerBaseChangeAlgEquiv
      (standardResolution.{u, u} A (towerBaseAlgebra A B)).hom (fibrePresentation A U)
      (standardResolution_isResolution.{u, u} A (towerBaseAlgebra A B)).isPolynomialAlgebra m
    refine ⟨fun x y hxy => e.injective ((heq x).symm.trans (hxy.trans (heq y))),
      fun z => ?_⟩
    obtain ⟨x, hx⟩ := e.surjective z
    exact ⟨x, (heq x).trans hx⟩
  let Fg := (IsPolynomialAlgebraOver B (towerRelativeAlgebra B C)).ι ⋙
    Over.forget (towerRelativeAlgebra B C) ⋙ forget (CommAlgCat.{u} B)
  have : IsIso (Fg.map (fibreTowerBaseChange U ((fibreTowerSimplicial A U).obj m))) :=
    (isIso_iff_bijective _).2 hbij
  exact isIso_of_reflects_iso _ Fg

end Resolution


end CommAlgCat

namespace Stacks.ChaoticSite

universe vD uD

/-- **A functor out of `Δᵒᵖ` all of whose values are terminal objects is final**: every
coyoneda colimit is the colimit of the constant singleton over the connected category `Δᵒᵖ`. -/
lemma final_of_forall_isTerminal {D : Type uD} [Category.{vD} D] (F : SimplexCategoryᵒᵖ ⥤ D)
    (h : ∀ n, IsTerminal (F.obj n)) : F.Final := by
  have : IsConnected SimplexCategoryᵒᵖ := isConnected_of_hasInitial _
  refine final_of_colimit_comp_coyoneda_isoPUnit F fun X => ?_
  let e : F ⋙ coyoneda.obj (op X) ≅ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vD + 1} :=
    NatIso.ofComponents (fun n => Equiv.toIso
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => (h n).from X
        left_inv := fun f => (h n).hom_ext _ _
        right_inv := fun _ => rfl }) (by intros; rfl)
  exact HasColimit.isoOfNatIso e ≪≫ Types.colimitConstPUnitIsoPUnit.{vD} SimplexCategoryᵒᵖ

end Stacks.ChaoticSite

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  (U : PolynomialAugmentation B (towerRelativeAlgebra B C))

/-- **The fibre of `u₃` over `(Q̄ → C)` is equivalent to the site of towers over `Q̄`.** -/
instance : (fibreTowerCostructured A B C U).IsEquivalence where

section Counit

variable (A) in
omit [Algebra A C] [IsScalarTower A B C] in
/-- **The towers of the standard resolution form a final functor `Δᵒᵖ ⥤ C_{Q̄/B/A}ᵒᵖ`**: every
colimit over `Δᵒᵖ` of a simplicial set of morphisms out of them is a singleton. -/
lemma final_fibreTowerCosimplicial_op : (fibreTowerCosimplicial A U).op.Final := by
  have : IsConnected SimplexCategoryᵒᵖ := isConnected_of_hasInitial _
  refine Stacks.ChaoticSite.final_of_colimit_comp_coyoneda_isoPUnit _ fun W => ?_
  have hf := (exists_homotopyEquivalences_fibreTowerCosimplicial A U W.unop).choose_spec
  have := Stacks.ChaoticSite.isIso_colim_map_of_homotopyEquivalences _ hf
  exact HasColimit.isoOfNatIso (Functor.isoWhiskerLeft _ (Coyoneda.objOpOp W.unop)) ≪≫
    asIso ((colim : SimplicialObject (Type u) ⥤ Type u).map
      (exists_homotopyEquivalences_fibreTowerCosimplicial A U W.unop).choose) ≪≫
    Types.colimitConstPUnitIsoPUnit.{u} SimplexCategoryᵒᵖ

variable (A B C) in
/-- The comparison of the costructured arrows of `u₃` with those of the identity, which have a
final object. -/
def costructuredToOver (y : (polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ) :
    CostructuredArrow (polynomialTowerThird A B C).op y ⥤
      CostructuredArrow (𝟭 (polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ) y where
  obj j := CostructuredArrow.mk (Y := (polynomialTowerThird A B C).op.obj j.left) j.hom
  map g := CostructuredArrow.homMk ((polynomialTowerThird A B C).op.map g.left)
    (CostructuredArrow.w g)

variable (A) in
/-- The towers of the standard resolution, read in the costructured arrows of `u₃` over
`(Q̄ → C)`. -/
abbrev fibreResolutionCostructured :
    SimplexCategoryᵒᵖ ⥤ CostructuredArrow (polynomialTowerThird A B C).op (op (op U)) :=
  (fibreTowerCosimplicial A U).op ⋙ (opOpEquivalence _).functor ⋙ fibreTowerCostructured A B C U

/-- **The fibre of `u₃` over `(Q̄ → C)` computes colimits of presheaves pulled back from
`C_{C/B}`**: the comparison with the costructured arrows of the identity is final. -/
lemma final_costructuredToOver :
    (costructuredToOver A B C (op (op U))).Final := by
  have := final_fibreTowerCosimplicial_op A U
  have : (fibreResolutionCostructured A U).Final := Functor.final_comp_equivalence _ _
  have : (fibreResolutionCostructured A U ⋙ costructuredToOver A B C (op (op U))).Final := by
    refine Stacks.ChaoticSite.final_of_forall_isTerminal _ fun n => ?_
    have h₁ := isIso_fibreTowerBaseChange_simplicial A U (op n.unop)
    have h₂ : IsIso (fibreTowerBaseChange U ((fibreTowerSimplicial A U).obj (op n.unop))).op :=
      inferInstance
    have h₃ := isIso_op (fibreTowerBaseChange U ((fibreTowerSimplicial A U).obj (op n.unop))).op
    exact IsTerminal.ofIso CostructuredArrow.mkIdTerminal (CostructuredArrow.isoMk
      (@asIso _ _ _ _
        (fibreTowerBaseChange U ((fibreTowerSimplicial A U).obj (op n.unop))).op.op h₃)
      (Category.comp_id _)).symm
  exact Functor.final_of_final_comp (fibreResolutionCostructured A U) _

end Counit

variable (A B C) in
/-- **The counit of `Lan_{u₃} ⊣ u₃^*` is invertible**: every abelian presheaf `ℳ` on `C_{C/B}` is
the left Kan extension of its restriction to `C_{C/B/A}`. At `(Q̄ → C)` the colimit over the
fibre of `u₃` of `ℳ ∘ u₃` is the colimit over the costructured arrows of the identity, which have
a final object, because the comparison is final. -/
theorem isIso_lanAdjunction_counit_app
    (M : (polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso (((polynomialTowerThird A B C).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app M) := by
  rw [Functor.isIso_lanAdjunction_counit_app_iff]
  refine Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension
    (E := Functor.LeftExtension.mk M (𝟙 ((polynomialTowerThird A B C).op ⋙ M))) fun y => ?_
  have : (costructuredToOver A B C y).Final := final_costructuredToOver y.unop.unop
  let hT : IsTerminal (CostructuredArrow.mk (𝟙 y) :
      CostructuredArrow (𝟭 (polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ) y) :=
    CostructuredArrow.mkIdTerminal
  have h₀ := colimitOfDiagramTerminal hT (CostructuredArrow.proj _ y ⋙ M)
  have h₁ := (Functor.Final.isColimitWhiskerEquiv (costructuredToOver A B C y) _).symm h₀
  refine IsColimit.ofIsoColimit h₁ (Cocone.ext (Iso.refl _) fun j => ?_)
  change M.map (hT.from ((costructuredToOver A B C y).obj j)).left ≫ 𝟙 _ = 𝟙 _ ≫ M.map j.hom
  rw [Category.comp_id, Category.id_comp]
  congr 1
  have h := CostructuredArrow.w (hT.from ((costructuredToOver A B C y).obj j))
  simp only [Functor.id_map, CostructuredArrow.mk_hom_eq_self] at h
  exact h

end CommAlgCat

end
