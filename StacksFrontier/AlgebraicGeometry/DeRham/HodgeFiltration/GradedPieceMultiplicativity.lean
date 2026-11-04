module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Multiplicativity
import StacksCore.Tactic.StacksAttribute

/-!
# The bottom graded piece of the Hodge filtration is multiplicative on complexes

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space and let
`Ω^•_{𝒪_X/A}` be the relative de Rham complex. Stacks Section 50.7 filters it by the brutal
truncations `σ^{≥k}Ω^•_{𝒪_X/A}`, whose bottom graded piece is the single complex
`Ω^k_{𝒪_X/A}[-k]`, and asserts that the projections

`σ^{≥k}Ω^•_{𝒪_X/A} ⟶ Ω^k_{𝒪_X/A}[-k]`

are multiplicative for the multiplication `AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge`
of that section and the wedge product `Ω^p ⊗_A Ω^q ⟶ Ω^{p + q}` on the graded pieces.

The reason it holds is a degree count. Both `Tot(Ω^p[-p] ⊗_A Ω^q[-q])` and the target
`Ω^{p + q}[-(p + q)]` are concentrated in degree `p + q`, so the square is one equation between
maps out of the degree-`(p + q)` term of `Tot(σ^{≥p}Ω^• ⊗_A σ^{≥q}Ω^•)`; and of the summands of
that term, indexed by the pairs `(a, b)` with `a + b = p + q`, every one but `(p, q)` has `a < p`
or `b < q` and so vanishes. On the surviving summand both routes are the wedge multiplication
`Ω^p ⊗_A Ω^q ⟶ Ω^{p + q}` of Tag 0FM2, the projections being isomorphisms in degree `p` and `q`.

## Main definitions

* `CochainComplex.brutalGradedPiece` and `CochainComplex.brutalπ`: the bottom graded piece
  `L^k[-k]` of a brutal truncation of an `ℕ`-indexed complex, and **the projection
  `σ^{≥k}L^• ⟶ L^k[-k]` onto it.**
* `AlgebraicGeometry.SheafOfModules.deRhamGradedPiece` and
  `AlgebraicGeometry.SheafOfModules.deRhamBrutalπ`: the same for the de Rham complex, so the
  graded piece is `Ω^k_{𝒪_X/A}[-k]`.
* `AlgebraicGeometry.SheafOfModules.gradedPieceTensorSquare`:
  `Tot(Ω^p_{𝒪_X/A}[-p] ⊗_A Ω^q_{𝒪_X/A}[-q])`.
* `AlgebraicGeometry.SheafOfModules.gradedPieceWedge`: **the multiplication
  `Tot(Ω^p[-p] ⊗_A Ω^q[-q]) ⟶ Ω^{p + q}[-(p + q)]` of the graded pieces**, induced by the wedge
  multiplication `AlgebraicGeometry.SheafOfModules.exteriorProductComponent` of Tag 0FM2.

## Main results

* `AlgebraicGeometry.SheafOfModules.isZero_gradedPieceTensorSquare_X`:
  `Tot(Ω^p[-p] ⊗_A Ω^q[-q])` vanishes in every degree other than `p + q`.
* `AlgebraicGeometry.SheafOfModules.gradedPieceWedge_comm`: **the projections onto the bottom
  graded pieces are multiplicative**, which is the complex-level form of the second commutative
  diagram of Section 50.7.

## References

* [Stacks Project, Section 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open HomologicalComplex
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.Tensor (sheafTensor)
-- The additivity of `⊗_A` in each variable at the open-cover site of a space.
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The bottom graded piece `L^k[-k]` of the brutal truncation `σ^{≥k}L^•`** of an `ℕ`-indexed
cochain complex: the degree-`k` term of `L^•` placed in cohomological degree `k`. -/
abbrev brutalGradedPiece (L : CochainComplex C ℕ) (k : ℕ) : CochainComplex C ℕ :=
  (HomologicalComplex.single C (ComplexShape.up ℕ) k).obj (L.X k)

/-- **The projection `σ^{≥k}L^• ⟶ L^k[-k]` of a brutal truncation onto its bottom graded piece.**
In degree `k` it is the inclusion `(σ^{≥k}L^•)^k ⟶ L^k`, which is an isomorphism there. -/
def brutalπ (L : CochainComplex C ℕ) (k : ℕ) : brutal L k ⟶ brutalGradedPiece L k :=
  mkHomToSingle ((ιBrutal L k).f k) fun i hi =>
    (isZero_brutal_X (k := k) (n := i) L (by change i + 1 = k at hi; omega)).eq_of_src _ _

/-- The degree-`k` component of the projection onto the bottom graded piece is the inclusion
`(σ^{≥k}L^•)^k ⟶ L^k`. -/
@[simp]
lemma brutalπ_f (L : CochainComplex C ℕ) (k : ℕ) :
    (brutalπ L k).f k =
      (ιBrutal L k).f k ≫ (singleObjXSelf (ComplexShape.up ℕ) k (L.X k)).inv :=
  mkHomToSingle_f _ _

/-- **The projection onto the bottom graded piece, read back in `L^k`**, is the inclusion
`(σ^{≥k}L^•)^k ⟶ L^k`. -/
@[simp]
lemma brutalπ_f_comp_singleObjXSelf (L : CochainComplex C ℕ) (k : ℕ) :
    (brutalπ L k).f k ≫ (singleObjXSelf (ComplexShape.up ℕ) k (L.X k)).hom =
      (ιBrutal L k).f k := by
  rw [brutalπ_f, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **A morphism into `σ^{≥k}L^•` followed by the projection onto the bottom graded piece** is,
in degree `k`, that morphism composed with the inclusion `σ^{≥k}L^• ⟶ L^•`. -/
lemma comp_brutalπ_f {N : CochainComplex C ℕ} (L : CochainComplex C ℕ) (k : ℕ)
    (g : N ⟶ brutal L k) :
    (g ≫ brutalπ L k).f k =
      (g ≫ ιBrutal L k).f k ≫ (singleObjXSelf (ComplexShape.up ℕ) k (L.X k)).inv := by
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, brutalπ_f, Category.assoc]

end CochainComplex

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

/-! ### The bottom graded piece of a step of the Hodge filtration -/

/-- **`Ω^k_{𝒪_X/A}[-k]`, the bottom graded piece of the brutal truncation `σ^{≥k}Ω^•_{𝒪_X/A}`**:
the sheaf of relative `k`-forms placed in cohomological degree `k`. -/
abbrev deRhamGradedPiece (k : ℕ) :
    CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ :=
  CochainComplex.brutalGradedPiece (deRhamComplex B D) k

/-- **The projection `σ^{≥k}Ω^•_{𝒪_X/A} ⟶ Ω^k_{𝒪_X/A}[-k]`** of a step of the Hodge filtration
onto its bottom graded piece. -/
abbrev deRhamBrutalπ (k : ℕ) : deRhamBrutal B D k ⟶ deRhamGradedPiece B D k :=
  CochainComplex.brutalπ (deRhamComplex B D) k

/-- **`Tot(Ω^p_{𝒪_X/A}[-p] ⊗_A Ω^q_{𝒪_X/A}[-q])`**, the total complex of the tensor product over
`A` of two bottom graded pieces of the Hodge filtration. -/
abbrev gradedPieceTensorSquare (p q : ℕ) :=
  ((tensorBifunctorNat (A := A)).obj (deRhamGradedPiece B D p)).obj (deRhamGradedPiece B D q)

/-- **`Tot(Ω^p[-p] ⊗_A Ω^q[-q])` vanishes in every degree other than `p + q`.** -/
lemma isZero_gradedPieceTensorSquare_X (p q n : ℕ) (hn : n ≠ p + q) :
    IsZero ((gradedPieceTensorSquare B D p q).X n) := by
  show IsZero ((HomologicalComplex.mapBifunctor (deRhamGradedPiece B D p)
    (deRhamGradedPiece B D q) (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ)).X n)
  refine HomologicalComplex₂.isZero_total_X_of_isZero _ _ n fun a b hab => ?_
  have hab' : a + b = n := hab
  show IsZero (((sheafTensor.{u, u, u, u, u} A).obj ((deRhamGradedPiece B D p).X a)).obj
    ((deRhamGradedPiece B D q).X b))
  by_cases ha : a = p
  · exact isZero_tensorFunctor_obj_obj_of_right _
      (isZero_single_obj_X (ComplexShape.up ℕ) q _ b (by omega))
  · exact isZero_tensorFunctor_obj_obj_of_left
      (isZero_single_obj_X (ComplexShape.up ℕ) p _ a ha) _

/-! ### The multiplication of the graded pieces -/

/-- **Two bifunctor squares in succession.** Restricting the second tensor factor along `g` and
then the first along `f`, and then doing the same for `g'` and `f'`, is restricting the second
factor along `g ≫ g'` and the first along `f ≫ f'`. -/
@[reassoc]
private lemma tensorBifunctorSquare_comp
    {M M' M'' N N' N'' :
      _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    ((sheafTensor.{u, u, u, u, u} A).obj M).map g ≫
        ((sheafTensor.{u, u, u, u, u} A).map f).app N' ≫
        (((sheafTensor.{u, u, u, u, u} A).obj M').map g' ≫
          ((sheafTensor.{u, u, u, u, u} A).map f').app N'') =
      ((sheafTensor.{u, u, u, u, u} A).obj M).map (g ≫ g') ≫
        ((sheafTensor.{u, u, u, u, u} A).map (f ≫ f')).app N'' := by
  have h := ((sheafTensor.{u, u, u, u, u} A).map f).naturality g'
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% h]

/-- The component of the multiplication of the graded pieces on the `(a, b)` summand of
`Tot(Ω^p[-p] ⊗_A Ω^q[-q])` in total degree `p + q`: wedge multiplication of a `p`-form by a
`q`-form on the only summand that does not vanish, namely `(p, q)`, and zero on the others. -/
def gradedPieceWedgeSummand (p q a b : ℕ) (hab : a + b = p + q) :
    ((sheafTensor.{u, u, u, u, u} A).obj ((deRhamGradedPiece B D p).X a)).obj
        ((deRhamGradedPiece B D q).X b) ⟶
      (deRhamComplex B D).X (p + q) :=
  if ha : a = p then
    ((sheafTensor.{u, u, u, u, u} A).obj ((deRhamGradedPiece B D p).X a)).map
          (singleObjXIsoOfEq (ComplexShape.up ℕ) q ((deRhamComplex B D).X q) b
            (by omega)).hom ≫
      ((sheafTensor.{u, u, u, u, u} A).map
            (singleObjXIsoOfEq (ComplexShape.up ℕ) p ((deRhamComplex B D).X p) a ha).hom).app
          ((deRhamComplex B D).X q) ≫
        exteriorProductComponent B p q
  else 0

/-- On the `(p, q)` summand the component of the multiplication of the graded pieces is wedge
multiplication of a `p`-form by a `q`-form. -/
lemma gradedPieceWedgeSummand_self (p q : ℕ) (hab : p + q = p + q) :
    gradedPieceWedgeSummand B D p q p q hab =
      ((sheafTensor.{u, u, u, u, u} A).obj ((deRhamGradedPiece B D p).X p)).map
            (singleObjXSelf (ComplexShape.up ℕ) q ((deRhamComplex B D).X q)).hom ≫
        ((sheafTensor.{u, u, u, u, u} A).map
              (singleObjXSelf (ComplexShape.up ℕ) p ((deRhamComplex B D).X p)).hom).app
            ((deRhamComplex B D).X q) ≫
          exteriorProductComponent B p q := by
  rw [gradedPieceWedgeSummand, dif_pos rfl]
  rfl

/-- The degree-`(p + q)` component of the multiplication of the graded pieces: the descent of
`AlgebraicGeometry.SheafOfModules.gradedPieceWedgeSummand` along the coproduct decomposition. -/
def gradedPieceWedgeDesc (p q : ℕ) :
    (gradedPieceTensorSquare B D p q).X (p + q) ⟶ (deRhamComplex B D).X (p + q) :=
  HomologicalComplex.mapBifunctorDesc fun a b h => gradedPieceWedgeSummand B D p q a b h

/-- The degree-`(p + q)` component of the multiplication of the graded pieces, restricted to the
`(a, b)` summand. -/
@[reassoc (attr := simp)]
lemma ι_gradedPieceWedgeDesc (p q a b : ℕ) (h : a + b = p + q) :
    HomologicalComplex.ιMapBifunctor (deRhamGradedPiece B D p) (deRhamGradedPiece B D q)
        (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) a b (p + q) h ≫
          gradedPieceWedgeDesc B D p q =
      gradedPieceWedgeSummand B D p q a b h :=
  HomologicalComplex.ι_mapBifunctorDesc _ a b h

/-- Reassociating a fourfold composite. -/
private lemma comp_assoc₃ {W₁ W₂ W₃ W₄ W₅ :
      _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (c : W₁ ⟶ W₂) (d : W₂ ⟶ W₃) (e : W₃ ⟶ W₄) (g : W₄ ⟶ W₅) :
    (c ≫ d ≫ e) ≫ g = c ≫ d ≫ e ≫ g := by
  simp only [Category.assoc]

/-- The degree-`(p + q)` component of the multiplication of the graded pieces, restricted to the
`(p, q)` summand and followed by a further morphism: wedge multiplication of a `p`-form by a
`q`-form. -/
private lemma ι_gradedPieceWedgeDesc_self_comp (p q : ℕ) (h : p + q = p + q)
    {Z : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (g : (deRhamComplex B D).X (p + q) ⟶ Z) :
    HomologicalComplex.ιMapBifunctor (deRhamGradedPiece B D p) (deRhamGradedPiece B D q)
          (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) p q (p + q) h ≫
        gradedPieceWedgeDesc B D p q ≫ g =
      ((sheafTensor.{u, u, u, u, u} A).obj ((deRhamGradedPiece B D p).X p)).map
            (singleObjXSelf (ComplexShape.up ℕ) q ((deRhamComplex B D).X q)).hom ≫
        ((sheafTensor.{u, u, u, u, u} A).map
              (singleObjXSelf (ComplexShape.up ℕ) p ((deRhamComplex B D).X p)).hom).app
            ((deRhamComplex B D).X q) ≫
          exteriorProductComponent B p q ≫ g :=
  ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g) (ι_gradedPieceWedgeDesc B D p q p q h))).trans
    ((congrArg (· ≫ g) (gradedPieceWedgeSummand_self B D p q h)).trans
      (comp_assoc₃ _ _ _ g))

/-- **The multiplication of the bottom graded pieces of the Hodge filtration**

`Tot(Ω^p_{𝒪_X/A}[-p] ⊗_A Ω^q_{𝒪_X/A}[-q]) ⟶ Ω^{p + q}_{𝒪_X/A}[-(p + q)]`,

induced by the wedge multiplication `Ω^p ⊗_A Ω^q ⟶ Ω^{p + q}` of Tag 0FM2. -/
def gradedPieceWedge (p q : ℕ) :
    gradedPieceTensorSquare B D p q ⟶ deRhamGradedPiece B D (p + q) :=
  mkHomToSingle (gradedPieceWedgeDesc B D p q) fun i hi =>
    (isZero_gradedPieceTensorSquare_X B D p q i
      (by change i + 1 = p + q at hi; omega)).eq_of_src _ _

/-- The degree-`(p + q)` component of the multiplication of the graded pieces. -/
@[simp]
lemma gradedPieceWedge_f (p q : ℕ) :
    (gradedPieceWedge B D p q).f (p + q) =
      gradedPieceWedgeDesc B D p q ≫
        (singleObjXSelf (ComplexShape.up ℕ) (p + q) ((deRhamComplex B D).X (p + q))).inv :=
  mkHomToSingle_f _ _

/-- **The right-hand route of the second square of Section 50.7 on the surviving summand.** On
the `(p, q)` summand the two projections onto the bottom graded pieces, followed by the
multiplication of the graded pieces, are the wedge multiplication
`AlgebraicGeometry.SheafOfModules.exteriorProductComponent` of Tag 0FM2 preceded by the two
inclusions of the truncations. -/
private lemma ι_gradedPieceWedgeDesc_brutalπ (p q : ℕ)
    (hab : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) =
      p + q) :
    ((sheafTensor.{u, u, u, u, u} A).obj ((deRhamBrutal B D p).X p)).map
          ((CochainComplex.brutalπ (deRhamComplex B D) q).f q) ≫
        HomologicalComplex.ιMapBifunctor (deRhamBrutal B D p) (deRhamGradedPiece B D q)
            (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) p q (p + q) hab ≫
          (HomologicalComplex.mapBifunctorMap (deRhamBrutalπ B D p)
                (𝟙 (deRhamGradedPiece B D q)) (sheafTensor.{u, u, u, u, u} A)
                (ComplexShape.up ℕ)).f (p + q) ≫
            gradedPieceWedgeDesc B D p q ≫
              (singleObjXSelf (ComplexShape.up ℕ) (p + q)
                ((deRhamComplex B D).X (p + q))).inv =
      ((sheafTensor.{u, u, u, u, u} A).obj ((deRhamBrutal B D p).X p)).map
          ((CochainComplex.ιBrutal (deRhamComplex B D) q).f q) ≫
        ((sheafTensor.{u, u, u, u, u} A).map
            ((CochainComplex.ιBrutal (deRhamComplex B D) p).f p)).app
            ((deRhamComplex B D).X q) ≫
          exteriorProductComponent B p q ≫
            (singleObjXSelf (ComplexShape.up ℕ) (p + q)
              ((deRhamComplex B D).X (p + q))).inv := by
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp]
  show ((sheafTensor.{u, u, u, u, u} A).obj ((deRhamBrutal B D p).X p)).map
        ((CochainComplex.brutalπ (deRhamComplex B D) q).f q) ≫
      ((sheafTensor.{u, u, u, u, u} A).map ((CochainComplex.brutalπ (deRhamComplex B D) p).f p)).app
          ((deRhamGradedPiece B D q).X q) ≫
        HomologicalComplex.ιMapBifunctor (deRhamGradedPiece B D p) (deRhamGradedPiece B D q)
            (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) p q (p + q) hab ≫
          gradedPieceWedgeDesc B D p q ≫
            (singleObjXSelf (ComplexShape.up ℕ) (p + q)
              ((deRhamComplex B D).X (p + q))).inv = _
  rw [ι_gradedPieceWedgeDesc_self_comp, tensorBifunctorSquare_comp_assoc,
    CochainComplex.brutalπ_f_comp_singleObjXSelf, CochainComplex.brutalπ_f_comp_singleObjXSelf]

/-- **The projections onto the bottom graded pieces are multiplicative.** This is the
complex-level form of the second commutative diagram of Stacks Section 50.7: the multiplication
`AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge` of the Hodge filtration followed by the
projection `σ^{≥(p + q)}Ω^• ⟶ Ω^{p + q}[-(p + q)]` agrees with the two projections tensored,
followed by the multiplication `AlgebraicGeometry.SheafOfModules.gradedPieceWedge` of the graded
pieces. -/
theorem gradedPieceWedge_comm (p q : ℕ) :
    hodgeFiltrationWedge B D p q ≫ deRhamBrutalπ B D (p + q) =
      ((tensorBifunctorNat (A := A)).obj (deRhamBrutal B D p)).map (deRhamBrutalπ B D q) ≫
        ((tensorBifunctorNat (A := A)).map (deRhamBrutalπ B D p)).app
            (deRhamGradedPiece B D q) ≫
          gradedPieceWedge B D p q := by
  show hodgeFiltrationWedge B D p q ≫ deRhamBrutalπ B D (p + q) =
      HomologicalComplex.mapBifunctorMap (𝟙 (deRhamBrutal B D p)) (deRhamBrutalπ B D q)
            (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) ≫
        HomologicalComplex.mapBifunctorMap (deRhamBrutalπ B D p)
              (𝟙 (deRhamGradedPiece B D q)) (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) ≫
          gradedPieceWedge B D p q
  apply to_single_hom_ext
  refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
  have hab' : a + b = p + q := hab
  by_cases ha : a < p
  · exact (isZero_tensorFunctor_obj_obj_of_left
      (CochainComplex.isZero_brutal_X (k := p) (n := a) (deRhamComplex B D)
        (by omega)) _).eq_of_src _ _
  by_cases hb : b < q
  · exact (isZero_tensorFunctor_obj_obj_of_right _
      (CochainComplex.isZero_brutal_X (k := q) (n := b) (deRhamComplex B D)
        (by omega))).eq_of_src _ _
  obtain rfl : p = a := by omega
  obtain rfl : q = b := by omega
  have hw : (hodgeFiltrationWedge B D p q ≫
        CochainComplex.brutalπ (deRhamComplex B D) (p + q)).f (p + q) =
      (truncatedWedge B D p q).f (p + q) ≫
        (singleObjXSelf (ComplexShape.up ℕ) (p + q) ((deRhamComplex B D).X (p + q))).inv := by
    rw [CochainComplex.comp_brutalπ_f, hodgeFiltrationWedge_ιBrutal]
  show HomologicalComplex.ιMapBifunctor (deRhamBrutal B D p) (deRhamBrutal B D q)
        (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) p q (p + q) hab ≫
      (hodgeFiltrationWedge B D p q ≫
        CochainComplex.brutalπ (deRhamComplex B D) (p + q)).f (p + q) =
    HomologicalComplex.ιMapBifunctor (deRhamBrutal B D p) (deRhamBrutal B D q)
        (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) p q (p + q) hab ≫
      ((HomologicalComplex.mapBifunctorMap (𝟙 (deRhamBrutal B D p)) (deRhamBrutalπ B D q)
            (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ)).f (p + q) ≫
        (HomologicalComplex.mapBifunctorMap (deRhamBrutalπ B D p)
              (𝟙 (deRhamGradedPiece B D q)) (sheafTensor.{u, u, u, u, u} A)
              (ComplexShape.up ℕ)).f (p + q) ≫
          (gradedPieceWedge B D p q).f (p + q))
  rw [hw]
  show HomologicalComplex.ιMapBifunctor (deRhamBrutal B D p) (deRhamBrutal B D q)
        (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) p q (p + q) hab ≫
      (((HomologicalComplex.mapBifunctorMap (𝟙 (deRhamBrutal B D p))
              (CochainComplex.ιBrutal (deRhamComplex B D) q) (sheafTensor.{u, u, u, u, u} A)
              (ComplexShape.up ℕ)).f (p + q) ≫
          (HomologicalComplex.mapBifunctorMap (CochainComplex.ιBrutal (deRhamComplex B D) p)
                (𝟙 (deRhamComplex B D)) (sheafTensor.{u, u, u, u, u} A)
                (ComplexShape.up ℕ)).f (p + q) ≫
            wedgeProductDesc B D (p + q)) ≫
        (singleObjXSelf (ComplexShape.up ℕ) (p + q) ((deRhamComplex B D).X (p + q))).inv) = _
  rw [gradedPieceWedge_f]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    ι_wedgeProductDesc_assoc, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  exact (ι_gradedPieceWedgeDesc_brutalπ B D p q hab).symm

end AlgebraicGeometry.SheafOfModules

end
