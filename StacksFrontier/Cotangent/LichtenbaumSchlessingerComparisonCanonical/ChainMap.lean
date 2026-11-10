module

public import StacksFrontier.Algebra.Homology.ModuleCatQuasiIsoAtElements
public import StacksFrontier.Cotangent.ConormalLowDegree
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparison
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonMap
public import StacksFrontier.Cotangent.NaiveComparisonIsIso
import all StacksFrontier.Cotangent.StandardResolutionFrobeniusHomotopy

/-!
# The canonical comparison of the cotangent complex with the Lichtenbaum–Schlessinger complex

Let `P → B` be a polynomial presentation of an `A`-algebra `B` with chosen generators `f_t` of
its defining ideal, and let `L` be the three-term complex `Rel/TrivRel → F ⊗_P B → Ω_{P/A} ⊗_P B`
attached to these data. This file constructs the canonical map `L_{B/A} → L` of the source and
proves that it identifies `L` with the truncation `τ_{≥ -2} L_{B/A}` ([Stacks, Tag 09CG]).

## Main definitions

* `Algebra.Presentation.lsChainMap`: the map of complexes `L_{B/A} → L` of the source, which is
  `dψ ⊗ 1`, `λ̄` and `q` in degrees `0`, `-1` and `-2`.
* `Algebra.Presentation.LichtenbaumSchlessingerComparison.canonical`: the chain-level comparison
  given by `lsChainMap`.
* `Algebra.Presentation.canonicalCotangentToLichtenbaumSchlessinger`: the canonical map
  `L_{B/A} → L` in `D(B)`.
* `Algebra.Presentation.canonicalTruncGECotangentIsoLichtenbaumSchlessinger`: the isomorphism
  `τ_{≥ -2} L_{B/A} ≅ L` it induces.

## Main results

* `Algebra.Presentation.isIso_homologyMap_lsChainMap_zero`,
  `Algebra.Presentation.isIso_homologyMap_lsChainMap_negOne`,
  `Algebra.Presentation.isIso_homologyMap_lsChainMap_negTwo`: `lsChainMap` is an isomorphism on
  `H⁰`, `H^{-1}` and `H^{-2}`.
* `Algebra.Presentation.isIso_descTruncGE_canonicalCotangentToLichtenbaumSchlessinger` and
  `Algebra.Presentation.canonicalTruncGECotangentIsoLichtenbaumSchlessinger_fac`: the canonical
  map induces an isomorphism `τ_{≥ -2} L_{B/A} ≅ L`.

## Implementation notes

The comparison is constructed on the standard resolution `P_•` of `B` over `A`, from an
`A`-algebra lift `ψ : P_0 → P` of the augmentation and an `A`-linear lift `λ` of the
biderivation on `P_1` with prescribed values on the variables; in degree `-2` it sends `dg` to
the class of `λ(d_0 g - d_1 g + d_2 g)`. Its isomorphisms on cohomology are proved as in the
source:

* on `H⁰` and `H^{-1}` by Remark 08UP and Lemma 08RB: the explicit map `L_{B/A} → NL(P₀ → B)` is
  an isomorphism there (`Stacks.Cotangent.isIso_homologyMap_explicitNaiveComparison`), and the
  comparison followed by the surjection `F ⊗ B → I/I²` is the map induced by `ψ` on naive
  cotangent complexes;
* on `H^{-2}` by Remarks 09D5 and 09D6: every `2`-cycle of `L_{B/A}` is cohomologous to `1 ⊗ dg`
  with `g ∈ J₂` and `d₀ g - d₁ g + d₂ g ∈ J₁²`
  (`Stacks.Cotangent.isIso_homologyMap_conormalToCotangentMoore`); on such a `g` the comparison is
  `λ(d₀ g - d₁ g + d₂ g)`, which `λ` turns into the value of the identification
  `μ : Ker(I ⊗ I → I²) → (Rel ∩ I F)/TrivRel` of 09D6 (`Algebra.Presentation.kerTensorRelation`),
  and both sides are homotopy invariant.

The passage from a chain-level comparison to the isomorphism `τ_{≥ -2} L_{B/A} ≅ L` is
`Algebra.Presentation.isIso_descTruncGE_cotangentToLichtenbaumSchlessinger` of
`StacksFrontier.Cotangent.LichtenbaumSchlessingerComparison`.

## References

* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
* [Stacks Project, Tag 08UP](https://stacks.math.columbia.edu/tag/08UP)
* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
* [Stacks Project, Tag 09D5](https://stacks.math.columbia.edu/tag/09D5)
* [Stacks Project, Tag 09D6](https://stacks.math.columbia.edu/tag/09D6)
-/

/-! ## The comparison map of complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TensorProduct KaehlerDifferential

universe u v w

namespace Algebra.Presentation

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B] [Algebra A B]
variable {X T : Type w} (P : Algebra.Presentation A B X T)

/-! ### The differentials of the cotangent complex -/

omit P in
/-- The differential of `L_{B/A}` out of simplicial degree three is `d₀ - d₁ + d₂ - d₃`. -/
theorem objD_two_eq :
    AlgebraicTopology.AlternatingFaceMapComplex.objD
        (CommAlgCat.cotangentSimplicialModule A (CommAlgCat.of A B)).object 2 =
      CommAlgCat.faceAsTermMap A (CommAlgCat.of A B) 2 0 -
        CommAlgCat.faceAsTermMap A (CommAlgCat.of A B) 2 1 +
        CommAlgCat.faceAsTermMap A (CommAlgCat.of A B) 2 2 -
        CommAlgCat.faceAsTermMap A (CommAlgCat.of A B) 2 3 := by
  rw [CommAlgCat.faceAsTermMap_eq, CommAlgCat.faceAsTermMap_eq, CommAlgCat.faceAsTermMap_eq,
    CommAlgCat.faceAsTermMap_eq]
  change ∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • _ = _
  rw [Fin.sum_univ_four]
  simp [SimplicialObject.δ, CommAlgCat.cotangentSimplicialModule, sub_eq_add_neg]
  abel

omit P in
/-- The differential of `L_{B/A}` from degree `-3` to degree `-2` is `d₀ - d₁ + d₂ - d₃` under
the identifications of its terms with those of the Moore complex. -/
theorem cotangentComplex_d_negThree_negTwo :
    (CommAlgCat.cotangentComplex A (CommAlgCat.of A B)).d (-3) (-2) =
      (CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 3).hom ≫
        (CommAlgCat.faceAsTermMap A (CommAlgCat.of A B) 2 0 -
          CommAlgCat.faceAsTermMap A (CommAlgCat.of A B) 2 1 +
          CommAlgCat.faceAsTermMap A (CommAlgCat.of A B) 2 2 -
          CommAlgCat.faceAsTermMap A (CommAlgCat.of A B) 2 3) ≫
        (CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 2).inv := by
  refine (CommAlgCat.cotangentComplex_d A (CommAlgCat.of A B) 2).trans ?_
  rw [objD_two_eq]
  rfl

/-! ### The components -/

local notation "𝕂" => (CommAlgCat.cotangentComplex A (CommAlgCat.of A B))
local notation "𝓔" n => (CommAlgCat.standardResolutionExtension A (CommAlgCat.of A B) n)

omit P in
/-- The term of `L_{B/A}` in degree `0`, the cotangent space of `P₀ → B`. -/
def cotangentDegreeIsoZero : (𝕂).X 0 ≅ ModuleCat.of B (𝓔 0).CotangentSpace :=
  CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 0 ≪≫
    eqToIso (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 0)

omit P in
/-- The term of `L_{B/A}` in degree `-1`, the cotangent space of `P₁ → B`. -/
def cotangentDegreeIsoOne : (𝕂).X (-1) ≅ ModuleCat.of B (𝓔 1).CotangentSpace :=
  CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 1 ≪≫
    eqToIso (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 1)

omit P in
/-- The term of `L_{B/A}` in degree `-2`, the cotangent space of `P₂ → B`. -/
def cotangentDegreeIsoTwo : (𝕂).X (-2) ≅ ModuleCat.of B (𝓔 2).CotangentSpace :=
  CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 2 ≪≫
    eqToIso (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 2)

omit P in
/-- The term of `L_{B/A}` in degree `-3`, the cotangent space of `P₃ → B`. -/
def cotangentDegreeIsoThree : (𝕂).X (-3) ≅ ModuleCat.of B (𝓔 3).CotangentSpace :=
  CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 3 ≪≫
    eqToIso (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 3)

omit P in
/-- The face map `d_i` on the terms of `L_{B/A}` is the map of cotangent spaces induced by the
face map of extensions `P_{n+1} → P_n`. -/
theorem faceAsTermMap_eq_eqToHom (n : ℕ) (i : Fin (n + 2)) :
    CommAlgCat.faceAsTermMap A (CommAlgCat.of A B) n i =
      eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) (n + 1)) ≫
        ModuleCat.ofHom (Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) n i)) ≫
        eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) n).symm := by
  rw [← Category.assoc, ← CommAlgCat.faceAsTermMap_comp_eqToHom, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

omit P in
/-- The differential of `L_{B/A}` from degree `-1` to degree `0` is `d₀ - d₁` on cotangent
spaces. -/
theorem cotangentComplex_d_negOne_zero' :
    (𝕂).d (-1) 0 = (cotangentDegreeIsoOne (A := A) (B := B)).hom ≫ ModuleCat.ofHom
      (Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 0 0) -
        Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 0 1)) ≫
      (cotangentDegreeIsoZero (A := A) (B := B)).inv := by
  rw [CommAlgCat.cotangentComplex_d_negOne_zero, cotangentDegreeIsoOne, cotangentDegreeIsoZero,
    faceAsTermMap_eq_eqToHom, faceAsTermMap_eq_eqToHom, ← Preadditive.comp_sub,
    ← Preadditive.sub_comp]
  simp only [Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Category.assoc]
  rfl

omit P in
/-- The differential of `L_{B/A}` from degree `-2` to degree `-1` is `d₀ - d₁ + d₂` on cotangent
spaces. -/
theorem cotangentComplex_d_negTwo_negOne' :
    (𝕂).d (-2) (-1) = (cotangentDegreeIsoTwo (A := A) (B := B)).hom ≫ ModuleCat.ofHom
      (Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 1 0) -
        Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 1 1) +
        Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 1 2)) ≫
      (cotangentDegreeIsoOne (A := A) (B := B)).inv := by
  rw [CommAlgCat.cotangentComplex_d_negTwo_negOne, cotangentDegreeIsoOne, cotangentDegreeIsoTwo,
    faceAsTermMap_eq_eqToHom, faceAsTermMap_eq_eqToHom, faceAsTermMap_eq_eqToHom,
    ← Preadditive.comp_sub, ← Preadditive.sub_comp, ← Preadditive.comp_add,
    ← Preadditive.add_comp]
  simp only [Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Category.assoc]
  rfl

omit P in
/-- The differential of `L_{B/A}` from degree `-3` to degree `-2` is `d₀ - d₁ + d₂ - d₃` on
cotangent spaces. -/
theorem cotangentComplex_d_negThree_negTwo' :
    (𝕂).d (-3) (-2) = (cotangentDegreeIsoThree (A := A) (B := B)).hom ≫ ModuleCat.ofHom
      (Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 0) -
        Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 1) +
        Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 2) -
        Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 3)) ≫
      (cotangentDegreeIsoTwo (A := A) (B := B)).inv := by
  rw [cotangentComplex_d_negThree_negTwo, cotangentDegreeIsoTwo, cotangentDegreeIsoThree,
    faceAsTermMap_eq_eqToHom, faceAsTermMap_eq_eqToHom, faceAsTermMap_eq_eqToHom,
    faceAsTermMap_eq_eqToHom, ← Preadditive.comp_sub, ← Preadditive.sub_comp,
    ← Preadditive.comp_add, ← Preadditive.add_comp, ← Preadditive.comp_sub,
    ← Preadditive.sub_comp]
  simp only [Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Category.assoc]
  rfl

omit P in
/-- `ULift.down` on the terms of the lifted cotangent complex. -/
def uliftDown (i : ℤ) : (cotangentComplexULift.{u, v, w} A B).X i →ₗ[B] (𝕂).X i :=
  ULift.moduleEquiv.toLinearMap

omit P in
/-- `ULift.up` on the terms of the lifted cotangent complex. -/
def uliftUp (i : ℤ) : (𝕂).X i →ₗ[B] (cotangentComplexULift.{u, v, w} A B).X i :=
  ULift.moduleEquiv.symm.toLinearMap

omit P in
/-- `ULift.down` undoes `uliftUp`. -/
@[simp]
theorem uliftUp_down (i : ℤ) (z : (𝕂).X i) :
    (uliftUp (A := A) (B := B) i z).down = z := rfl

omit P in
/-- `uliftUp` is injective. -/
theorem uliftUp_injective (i : ℤ) : Function.Injective (uliftUp.{u, v, w} (A := A) (B := B) i) :=
  fun z z' h => by simpa using congrArg ULift.down h

omit P in
/-- `uliftDown` is `ULift.down`. -/
@[simp]
theorem uliftDown_apply (i : ℤ) (z : (cotangentComplexULift.{u, v, w} A B).X i) :
    uliftDown (A := A) (B := B) i z = z.down := rfl

/-- The component of the comparison in degree `0`. -/
def lsChainZero : (cotangentComplexULift.{u, v, w} A B).X (0) ⟶
    (lichtenbaumSchlessingerComplex P).complex.X (0) :=
  (ConcreteCategory.ofHom (C := ModuleCat B) (X := (cotangentComplexULift.{u, v, w} A B).X (0))
    (P.lsComponentZero ∘ₗ ((cotangentDegreeIsoZero (A := A) (B := B)).hom.hom ∘ₗ
      uliftDown (A := A) (B := B) (0)))) ≫
    (lichtenbaumSchlessingerComplex P).differentialIso.inv

/-- In degree `0`, the comparison is `lsComponentZero` on the cotangent space of `P₀ → B`. -/
theorem lsChainZero_apply (z : (cotangentComplexULift.{u, v, w} A B).X (0)) :
    (lichtenbaumSchlessingerComplex P).differentialIso.hom (P.lsChainZero z) =
      P.lsComponentZero ((cotangentDegreeIsoZero (A := A) (B := B)).hom z.down) := by
  rw [lsChainZero, ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- The component of the comparison in degree `-1`. -/
def lsChainOne : (cotangentComplexULift.{u, v, w} A B).X (-1) ⟶
    (lichtenbaumSchlessingerComplex P).complex.X (-1) :=
  (ConcreteCategory.ofHom (C := ModuleCat B) (X := (cotangentComplexULift.{u, v, w} A B).X (-1))
    (P.lsComponentOne ∘ₗ ((cotangentDegreeIsoOne (A := A) (B := B)).hom.hom ∘ₗ
      uliftDown (A := A) (B := B) (-1)))) ≫
    (lichtenbaumSchlessingerComplex P).freeIso.inv

/-- In degree `-1`, the comparison is `lsComponentOne` on the cotangent space of `P₁ → B`. -/
theorem lsChainOne_apply (z : (cotangentComplexULift.{u, v, w} A B).X (-1)) :
    (lichtenbaumSchlessingerComplex P).freeIso.hom (P.lsChainOne z) =
      P.lsComponentOne ((cotangentDegreeIsoOne (A := A) (B := B)).hom z.down) := by
  rw [lsChainOne, ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- The component of the comparison in degree `-2`. -/
def lsChainTwo : (cotangentComplexULift.{u, v, w} A B).X (-2) ⟶
    (lichtenbaumSchlessingerComplex P).complex.X (-2) :=
  (ConcreteCategory.ofHom (C := ModuleCat B) (X := (cotangentComplexULift.{u, v, w} A B).X (-2))
    (P.lsComponentTwo ∘ₗ ((cotangentDegreeIsoTwo (A := A) (B := B)).hom.hom ∘ₗ
      uliftDown (A := A) (B := B) (-2)))) ≫
    (lichtenbaumSchlessingerComplex P).relationIso.inv

/-- In degree `-2`, the comparison is `lsComponentTwo` on the cotangent space of `P₂ → B`. -/
theorem lsChainTwo_apply (z : (cotangentComplexULift.{u, v, w} A B).X (-2)) :
    (lichtenbaumSchlessingerComplex P).relationIso.hom (P.lsChainTwo z) =
      P.lsComponentTwo ((cotangentDegreeIsoTwo (A := A) (B := B)).hom z.down) := by
  rw [lsChainTwo, ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

omit P in
/-- The differential of the lifted cotangent complex is the differential of `L_{B/A}` on
`ULift.down`. -/
theorem cotangentComplexULift_d_apply (i j : ℤ)
    (z : (cotangentComplexULift.{u, v, w} A B).X i) :
    ((cotangentComplexULift.{u, v, w} A B).d i j z).down = (𝕂).d i j z.down := rfl

/-- Two maps of `B`-modules agree if they agree after an isomorphism on the target. -/
private theorem hom_eq_of_iso_hom_apply_eq {R : Type*} [CommRing R] {X Y Z : ModuleCat R}
    (e : Y ≅ Z) (f g : X ⟶ Y)
    (h : ∀ z, e.hom (f z) = e.hom (g z)) : f = g := by
  rw [← cancel_mono e.hom]
  exact ModuleCat.hom_ext (LinearMap.ext h)

/-- The components of the comparison in degrees `-1` and `0` commute with the differentials. -/
theorem lsChain_square_zero :
    P.lsChainOne ≫ (lichtenbaumSchlessingerComplex P).complex.d (-1) 0 =
      (cotangentComplexULift.{u, v, w} A B).d (-1) 0 ≫ P.lsChainZero := by
  refine hom_eq_of_iso_hom_apply_eq (lichtenbaumSchlessingerComplex P).differentialIso _ _
    fun z => ?_
  have h := LinearMap.congr_fun P.lsComponent_square_zero
    ((cotangentDegreeIsoOne (A := A) (B := B)).hom z.down)
  rw [LinearMap.comp_apply] at h
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  rw [lsChainZero_apply, cotangentComplexULift_d_apply, cotangentComplex_d_negOne_zero',
    ← (lichtenbaumSchlessingerComplex P).freeIso.hom_inv_id_apply (P.lsChainOne z),
    lsChainOne_apply, lsComplex_d_negOne_inv_apply, h]
  simp

/-- The components of the comparison in degrees `-2` and `-1` commute with the differentials. -/
theorem lsChain_square_one :
    P.lsChainTwo ≫ (lichtenbaumSchlessingerComplex P).complex.d (-2) (-1) =
      (cotangentComplexULift.{u, v, w} A B).d (-2) (-1) ≫ P.lsChainOne := by
  let _ := relationModule P
  refine hom_eq_of_iso_hom_apply_eq (lichtenbaumSchlessingerComplex P).freeIso _ _ fun z => ?_
  have h := LinearMap.congr_fun P.lsComponent_square_one
    ((cotangentDegreeIsoTwo (A := A) (B := B)).hom z.down)
  rw [LinearMap.comp_apply] at h
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  rw [lsChainOne_apply, cotangentComplexULift_d_apply, cotangentComplex_d_negTwo_negOne',
    ← (lichtenbaumSchlessingerComplex P).relationIso.hom_inv_id_apply (P.lsChainTwo z),
    lsChainTwo_apply, lsComplex_d_negTwo_inv_apply, h]
  simp

/-- The component of the comparison in degree `-2` kills the boundaries from degree `-3`. -/
theorem lsChain_square_two :
    (cotangentComplexULift.{u, v, w} A B).d (-3) (-2) ≫ P.lsChainTwo = 0 := by
  refine hom_eq_of_iso_hom_apply_eq (lichtenbaumSchlessingerComplex P).relationIso _ _
    fun z => ?_
  have h := LinearMap.congr_fun P.lsComponent_square_two
    ((cotangentDegreeIsoThree (A := A) (B := B)).hom z.down)
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [ModuleCat.comp_apply]
  rw [lsChainTwo_apply, cotangentComplexULift_d_apply, cotangentComplex_d_negThree_negTwo']
  simpa using h

/-! ### The map of complexes -/

/-- The component of the comparison in degree `i`: the three components above in degrees `0`,
`-1`, `-2`, and zero elsewhere. -/
def lsChainComponent (i : ℤ) : (cotangentComplexULift.{u, v, w} A B).X i ⟶
    (lichtenbaumSchlessingerComplex P).complex.X i :=
  if h0 : i = 0 then eqToHom (by rw [h0]) ≫ P.lsChainZero ≫ eqToHom (by rw [h0])
  else if h1 : i = -1 then eqToHom (by rw [h1]) ≫ P.lsChainOne ≫ eqToHom (by rw [h1])
  else if h2 : i = -2 then eqToHom (by rw [h2]) ≫ P.lsChainTwo ≫ eqToHom (by rw [h2])
  else 0

/-- The component of the comparison in degree `0` is `lsChainZero`. -/
theorem lsChainComponent_zero : P.lsChainComponent 0 = P.lsChainZero := by
  rw [lsChainComponent, dite_eq_left rfl, eqToHom_refl, eqToHom_refl, Category.id_comp,
    Category.comp_id]

/-- The component of the comparison in degree `-1` is `lsChainOne`. -/
theorem lsChainComponent_negOne : P.lsChainComponent (-1) = P.lsChainOne := by
  rw [lsChainComponent, dite_eq_right (by decide), dite_eq_left rfl, eqToHom_refl,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The component of the comparison in degree `-2` is `lsChainTwo`. -/
theorem lsChainComponent_negTwo : P.lsChainComponent (-2) = P.lsChainTwo := by
  rw [lsChainComponent, dite_eq_right (by decide), dite_eq_right (by decide), dite_eq_left rfl,
    eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The component of the comparison vanishes outside degrees `0`, `-1` and `-2`. -/
theorem lsChainComponent_eq_zero (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ -1) (h2 : i ≠ -2) :
    P.lsChainComponent i = 0 := by
  rw [lsChainComponent, dite_eq_right h0, dite_eq_right h1, dite_eq_right h2]

/-- **The comparison map `L_{B/A} → L` of [Stacks, Tag 09CG]**, as a map of complexes: in
degrees `0`, `-1`, `-2` it is `dψ ⊗ 1`, `λ̄` and `q`, built from the choices `ψ : P₀ → P` and
the biderivation `λ : P₁ → F/TrivRel`. -/
def lsChainMap :
    cotangentComplexULift.{u, v, w} A B ⟶ (lichtenbaumSchlessingerComplex P).complex where
  f := P.lsChainComponent
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases e1 : i = -1
    · subst e1
      obtain rfl : j = 0 := by omega
      rw [lsChainComponent_negOne, lsChainComponent_zero, lsChain_square_zero]
    by_cases e2 : i = -2
    · subst e2
      obtain rfl : j = -1 := by omega
      rw [lsChainComponent_negTwo, lsChainComponent_negOne, lsChain_square_one]
    by_cases e3 : i = -3
    · subst e3
      obtain rfl : j = -2 := by omega
      rw [lsChainComponent_negTwo, lsChain_square_two,
        lsChainComponent_eq_zero P (-3) (by decide) (by decide) (by decide), Limits.zero_comp]
    by_cases e0 : i = 0
    · subst e0
      obtain rfl : j = 1 := by omega
      exact ((lichtenbaumSchlessingerComplex P).isZero_X 1 (by decide) (by decide)
        (by decide)).eq_of_tgt _ _
    rw [lsChainComponent_eq_zero P i e0 e1 e2,
      lsChainComponent_eq_zero P j (by omega) (by omega) (by omega), Limits.zero_comp,
      Limits.comp_zero]

/-- The component of `lsChainMap` in degree `i` is `lsChainComponent i`. -/
theorem lsChainMap_f (i : ℤ) : (P.lsChainMap).f i = P.lsChainComponent i := rfl

end Algebra.Presentation

end
