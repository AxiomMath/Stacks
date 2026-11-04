module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.CobarExact
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# The cobar resolution of a monad, as a functor of the coefficient object

Let `L ⊣ R` be an adjunction between abelian categories with `L` additive and let `T = L ⋙ R` be
the induced monad on `A`. `StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.CobarExact`
produces, for each object `X : A`, differentials making
`0 ⟶ X ⟶ T X ⟶ T² X ⟶ T³ X ⟶ ⋯`
an exact complex; but it produces them existentially, and an existential statement carries no
naturality in `X`. This file builds the same resolution as a *functor*
`A ⥤ CochainComplex A ℤ`
with a *natural* augmentation out of `X` placed in degree zero, and shows that the augmentation is
a quasi-isomorphism at every `X`.

Nothing is lost by asking for naturality, because the cobar construction involves no choices: its
degree-`n` term is the iterate `T^{n+1}`, an endofunctor of `A`, and its cofaces are the
whiskerings of the unit `η : 𝟭 A ⟶ T` into the `n + 2` available slots, which are transformations
of endofunctors. The differentials are therefore transformations `T^{n+1} ⟶ T^{n+2}` before any
object is plugged in.

## Implementation notes

The construction is the direct one. `Stacks.Cobar.cobarDiff` is the alternating sum of the Godement
cofaces `CategoryTheory.Godement.face (Stacks.Cobar.cod adj)`, read in `A ⥤ A` rather than in
`Aᵒᵖ ⥤ Aᵒᵖ` by `CategoryTheory.NatTrans.unop`; it is a transformation of endofunctors of `A`, so
`CochainComplex.of` assembles the terms into a cochain complex *of endofunctors*,
`Stacks.Cobar.cobarFunctorComplex`. `HomologicalComplex.asFunctor` turns a complex of functors into
a functor to complexes, and `ComplexShape.embeddingUpNat.extendFunctor` re-indexes from `ℕ` to `ℤ`
by zero in the negative degrees; the composite is `Stacks.Cobar.cobarComplexFunctor`. Both steps
are functors, so the degreewise identification with `T^{n+1}` and the augmentation are natural on
the nose rather than object by object.

Two facts about the differentials have to be imported from the construction in `Aᵒᵖ`: that
consecutive differentials compose to zero, and that the first one kills the unit. Both are read off
the alternating face map complex of the cobar resolution of a *single* object, because a
transformation of functors vanishes as soon as all its components do; this is what
`Stacks.Cobar.op_cobarDiff_app_eq` is for, and it is also the comparison that lets the exactness
statement of `Stacks.Cobar.exists_exact_cobar` be re-proved for these differentials rather than for
the ones that statement chose.

The quasi-isomorphism is checked at the `ℕ`-indexing and transported by
`HomologicalComplex.quasiIso_extendMap_iff`, the route of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FiniteDescent/ResolutionSpectralSequence.lean`: in
the positive degrees it is exactness of `Tⁿ ⟶ Tⁿ⁺¹ ⟶ Tⁿ⁺²` at `X`, and in degree zero it is the
statement that the unit exhibits `X` as the kernel of the first differential.

## Main definitions

* `Stacks.Cobar.cobarDiff`: the differentials `T^{n+1} ⟶ T^{n+2}` of the cobar complex, as
  transformations of endofunctors of `A`.
* `Stacks.Cobar.cobarFunctorComplex`: the cobar complex as a cochain complex of endofunctors.
* `Stacks.Cobar.cobarComplexFunctor`: **the augmented cobar complex as a functor**
  `A ⥤ CochainComplex A ℤ`, concentrated in the nonnegative degrees.
* `Stacks.Cobar.cobarComplexFunctorXIso`: the degreewise identification of degree `n ≥ 0` of that
  complex with `T^{n+1}`, as an isomorphism of functors.
* `Stacks.Cobar.cobarAugmentation`: **the augmentation**, a transformation from `X ↦ X[0]` to
  `Stacks.Cobar.cobarComplexFunctor` whose component at `X` is determined by `η_X`.

## Main results

* `Stacks.Cobar.exact_cobarDiff_app`: the cobar complex of `X` built from these differentials is
  exact, under the two hypotheses of `Stacks.Cobar.exists_exact_cobar`.
* `Stacks.Cobar.quasiIso_cobarAugmentation`: **the augmentation is a quasi-isomorphism** at every
  object, under the same two hypotheses.

## References

* [Stacks Project, Tag 0G5M](https://stacks.math.columbia.edu/tag/0G5M)
* [Stacks Project, Tag 0G5P](https://stacks.math.columbia.edu/tag/0G5P)
* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

universe v₁ v₂ u₁ u₂

namespace Stacks.Cobar

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
  {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)

/-! ### The differentials of the cobar complex -/

/-- The alternating sum `∑ (-1)^i d^{n+1}_i` of the Godement cofaces, as a transformation of
endofunctors of `Aᵒᵖ`. The cofaces whisker the counit `cod adj = η.op` of the comonad `T.op` into
the `n + 2` available slots, so this is the usual differential of a cosimplicial object, read in
the opposite category. -/
public def opDiff (n : ℕ) : (mnd L R).op.iterate (n + 2) ⟶ (mnd L R).op.iterate (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Godement.face (cod adj) (n + 1) i

/-- **The differentials of the augmented cobar complex.** `cobarDiff adj n : T^{n+1} ⟶ T^{n+2}` is
the alternating sum of the cofaces, which insert the unit `η : 𝟭 A ⟶ T` of the adjunction into each
of the `n + 2` slots of `T^{n+2}`. It is a transformation of endofunctors of `A`: the cobar
construction makes no choices, so the differential exists before any object is plugged in. -/
public def cobarDiff (n : ℕ) : (mnd L R).iterate (n + 1) ⟶ (mnd L R).iterate (n + 2) :=
  NatTrans.unop (eqToHom (op_iterate (mnd L R) (n + 2)).symm ≫ opDiff adj n ≫
    eqToHom (op_iterate (mnd L R) (n + 1)))

omit [Abelian B] in
/-- `cobarDiff` read back in `Aᵒᵖ ⥤ Aᵒᵖ` is the alternating sum of the Godement cofaces, pinned by
the identification `T.op^n = (T^n).op` of `Stacks.Cobar.op_iterate`. -/
public theorem op_cobarDiff (n : ℕ) :
    NatTrans.op (cobarDiff adj n) = eqToHom (op_iterate (mnd L R) (n + 2)).symm ≫
      opDiff adj n ≫ eqToHom (op_iterate (mnd L R) (n + 1)) :=
  rfl

omit [Abelian B] in
/-- The component of `cobarDiff` at an object, read in `Aᵒᵖ`. -/
public theorem op_cobarDiff_app (n : ℕ) (X : A) :
    ((cobarDiff adj n).app X).op
      = eqToHom (Functor.congr_obj (op_iterate (mnd L R) (n + 2)).symm (op X)) ≫
        (opDiff adj n).app (op X) ≫
          eqToHom (Functor.congr_obj (op_iterate (mnd L R) (n + 1)) (op X)) := by
  have h := NatTrans.congr_app (op_cobarDiff adj n) (op X)
  rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app, eqToHom_app] at h
  exact h

omit [Abelian B] in
/-- The differential of the alternating face map complex of a simplicial object of `Aᵒᵖ` whose
faces are the components of the Godement faces at `op X`: it is the component at `op X` of the
alternating sum `Stacks.Cobar.opDiff`. -/
public theorem alternatingFaceMapComplex_d_app_eq (X : A) (S : SimplicialObject Aᵒᵖ)
    (h : ∀ n : ℕ, S.obj (op ⦋n⦌) = ((mnd L R).op.iterate (n + 1)).obj (op X))
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)),
      S.δ j = eqToHom (h (n + 1)) ≫ (Godement.face (cod adj) (n + 1) j).app (op X) ≫
        eqToHom (h n).symm)
    (n : ℕ) :
    (AlternatingFaceMapComplex.obj S).d (n + 1) n
      = eqToHom (h (n + 1)) ≫ (opDiff adj n).app (op X) ≫ eqToHom (h n).symm := by
  rw [AlternatingFaceMapComplex.obj_d_eq, opDiff]
  simp only [NatTrans.app_sum, NatTrans.app_zsmul, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  exact Finset.sum_congr rfl fun i _ => by rw [hδ n i]

omit [Abelian B] in
/-- **The comparison.** The component of `cobarDiff adj n` at `X`, read in `Aᵒᵖ`, is the
differential of the alternating face map complex of *any* cobar resolution of `X` in the shape
`Stacks.Cobar.exists_augmented_cobar` produces, pinned by the identification of its degree-`n`
term with `op (T^{n+1} X)`. This is what lets the facts proved in `Aᵒᵖ` about the Godement
resolution be read as facts about these differentials. -/
public theorem op_cobarDiff_app_eq (X : A) (Z : SimplicialObject.Augmented Aᵒᵖ)
    (h : ∀ n : ℕ, Z.left.obj (op ⦋n⦌) = ((mnd L R).op.iterate (n + 1)).obj (op X))
    (hobj : ∀ n : ℕ, Z.left.obj (op ⦋n⦌) = op (((mnd L R).iterate (n + 1)).obj X))
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)),
      Z.left.δ j = eqToHom (h (n + 1)) ≫ (Godement.face (cod adj) (n + 1) j).app (op X) ≫
        eqToHom (h n).symm)
    (n : ℕ) :
    ((cobarDiff adj n).app X).op = eqToHom (hobj (n + 1)).symm ≫
      (AlternatingFaceMapComplex.obj Z.left).d (n + 1) n ≫ eqToHom (hobj n) := by
  rw [alternatingFaceMapComplex_d_app_eq adj X Z.left h hδ n, op_cobarDiff_app]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- A composite of morphisms of `A` vanishes if the composite of their opposites does. -/
private theorem comp_eq_zero_of_op_comp_eq_zero {C : Type u₁} [Category.{v₁} C]
    [Limits.HasZeroMorphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : g.op ≫ f.op = 0) : f ≫ g = 0 :=
  Quiver.Hom.op_inj (by simpa using h)

/-- The unit, read in `Aᵒᵖ` and precomposed with the identification of degree `0`, is the
augmentation of the cobar resolution `Z` of `X`. -/
private theorem eqToHom_comp_unit_op_eq {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C)
    (Z : SimplicialObject.Augmented Cᵒᵖ)
    (h : ∀ n : ℕ, Z.left.obj (op ⦋n⦌) = ((mnd F G).op.iterate (n + 1)).obj (op X))
    (hZ : Z.right = op X)
    (hobj : ∀ n : ℕ, Z.left.obj (op ⦋n⦌) = op (((mnd F G).iterate (n + 1)).obj X))
    (hhom : Z.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ (cod adj).app (op X) ≫ eqToHom hZ.symm) :
    eqToHom (hobj 0) ≫ (adj.unit.app X).op = Z.hom.app (op ⦋0⦌) ≫ eqToHom hZ := by
  rw [hhom]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

omit [Abelian B] in
/-- Consecutive differentials of the cobar complex compose to zero, at every object. -/
public theorem cobarDiff_app_comp_cobarDiff_app (n : ℕ) (X : A) :
    (cobarDiff adj n).app X ≫ (cobarDiff adj (n + 1)).app X = 0 := by
  obtain ⟨Z, h, _, hobj, hδ, _, _⟩ := exists_augmented_cobar adj X
  have hz : ∀ (i j k : ℕ) {W : Aᵒᵖ} (u : (AlternatingFaceMapComplex.obj Z.left).X k ⟶ W),
      (AlternatingFaceMapComplex.obj Z.left).d i j ≫
        (AlternatingFaceMapComplex.obj Z.left).d j k ≫ u = 0 := by
    intro i j k W u
    rw [← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]
  have hDD : ((cobarDiff adj (n + 1)).app X).op ≫ ((cobarDiff adj n).app X).op = 0 := by
    rw [op_cobarDiff_app_eq adj X Z h hobj hδ (n + 1), op_cobarDiff_app_eq adj X Z h hobj hδ n]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hz, comp_zero]
  exact comp_eq_zero_of_op_comp_eq_zero _ _ hDD

omit [Abelian B] in
/-- Consecutive differentials of the cobar complex compose to zero, as transformations of
endofunctors. -/
public theorem cobarDiff_comp_cobarDiff (n : ℕ) :
    cobarDiff adj n ≫ cobarDiff adj (n + 1) = 0 := by
  ext X
  simpa using cobarDiff_app_comp_cobarDiff_app adj n X

omit [Abelian B] in
/-- The first differential of the cobar complex kills the unit: this is the coaugmentation
condition `η_X ≫ d⁰ = 0`. -/
public theorem unit_app_comp_cobarDiff_app (X : A) :
    adj.unit.app X ≫ (cobarDiff adj 0).app X = 0 := by
  obtain ⟨Z, h, hZ, hobj, hδ, _, hhom⟩ := exists_augmented_cobar adj X
  have hunit := eqToHom_comp_unit_op_eq adj X Z h hZ hobj hhom
  have hzero : (AlternatingFaceMapComplex.obj Z.left).d (0 + 1) 0 ≫
      Z.hom.app (op ⦋0⦌) ≫ eqToHom hZ = 0 := by
    rw [← Category.assoc, (show (AlternatingFaceMapComplex.obj Z.left).d (0 + 1) 0 ≫
      Z.hom.app (op ⦋0⦌) = 0 from d_one_zero_comp_hom_app_zero Z), zero_comp]
  have hD0 : ((cobarDiff adj 0).app X).op ≫ (adj.unit.app X).op = 0 := by
    rw [op_cobarDiff_app_eq adj X Z h hobj hδ 0, Category.assoc, Category.assoc, hunit, hzero,
      comp_zero]
  exact comp_eq_zero_of_op_comp_eq_zero _ _ hD0

/-! ### The cobar complex as a functor -/

/-- **The cobar complex as a cochain complex of endofunctors of `A`**: degree `n` is the iterate
`T^{n+1}` and the differentials are `Stacks.Cobar.cobarDiff`. -/
public def cobarFunctorComplex : CochainComplex (A ⥤ A) ℕ :=
  CochainComplex.of (fun n => (mnd L R).iterate (n + 1)) (cobarDiff adj)
    (cobarDiff_comp_cobarDiff adj)

omit [Abelian B] in
/-- The differential of the cobar complex of endofunctors is `cobarDiff`. -/
public theorem cobarFunctorComplex_d (n : ℕ) :
    (cobarFunctorComplex adj).d n (n + 1) = cobarDiff adj n :=
  CochainComplex.of_d (fun k => (mnd L R).iterate (k + 1)) (cobarDiff adj) n

omit [Abelian B] in
/-- The differential of the `ℕ`-indexed cobar complex at an object is `cobarDiff`. -/
public theorem cobarFunctorComplex_asFunctor_d (X : A) (n : ℕ) :
    ((cobarFunctorComplex adj).asFunctor.obj X).d n (n + 1) = (cobarDiff adj n).app X :=
  NatTrans.congr_app (cobarFunctorComplex_d adj n) X

/-- **The augmented cobar complex as a functor** `A ⥤ CochainComplex A ℤ`. On the object `X` it is
the complex which is `T^{n+1} X` in degree `n ≥ 0` and zero in the negative degrees, with
differentials the alternating sums of the cofaces; on a morphism it is `T^{n+1}` applied to it in
each degree. -/
public def cobarComplexFunctor : A ⥤ CochainComplex A ℤ :=
  (cobarFunctorComplex adj).asFunctor ⋙ ComplexShape.embeddingUpNat.extendFunctor A

/-- The cobar complex of an object is concentrated in the nonnegative degrees. -/
public instance isStrictlyGE_cobarComplexFunctor_obj (X : A) :
    CochainComplex.IsStrictlyGE ((cobarComplexFunctor adj).obj X) 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    (((cobarFunctorComplex adj).asFunctor.obj X).extend ComplexShape.embeddingUpNat) 0)

/-- **The degreewise identification**: degree `n ≥ 0` of the cobar complex is the iterate
`T^{n+1}`, naturally in the coefficient object. Evaluating at `X` gives
`((cobarComplexFunctor adj).obj X).X n ≅ (T^{n+1}).obj X`. -/
public def cobarComplexFunctorXIso (n : ℕ) :
    cobarComplexFunctor adj ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) (n : ℤ)
      ≅ (mnd L R).iterate (n + 1) :=
  Functor.isoWhiskerLeft (cobarFunctorComplex adj).asFunctor
    (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso A (i := n) (i' := (n : ℤ)) rfl)

/-! ### The augmentation -/

/-- The unit `η_X : X ⟶ T X` of the adjunction, read as a morphism into degree `0` of the cobar
complex of `X`. Spelling the target this way, rather than as `T X`, is what keeps the morphisms
below type-correct without unfolding the complex. -/
public def cobarUnit (X : A) : X ⟶ ((cobarFunctorComplex adj).asFunctor.obj X).X 0 :=
  adj.unit.app X

omit [Abelian B] in
/-- The unit is killed by the first differential of the cobar complex of `X`. -/
public theorem cobarUnit_comp_d (X : A) :
    cobarUnit adj X ≫ ((cobarFunctorComplex adj).asFunctor.obj X).d 0 1 = 0 := by
  rw [cobarFunctorComplex_asFunctor_d]
  exact unit_app_comp_cobarDiff_app adj X

omit [Abelian B] in
/-- Naturality of the unit, read in degree `0` of the cobar complex. -/
public theorem cobarUnit_naturality {X Y : A} (f : X ⟶ Y) :
    f ≫ cobarUnit adj Y = cobarUnit adj X ≫ ((cobarFunctorComplex adj).asFunctor.map f).f 0 :=
  adj.unit.naturality f

/-- The component at `X` of the augmentation of the `ℕ`-indexed cobar complex: the morphism out of
`X` placed in degree zero determined by the unit `η_X : X ⟶ T X`. -/
public def cobarNatAug (X : A) :
    (HomologicalComplex.single A (ComplexShape.up ℕ) 0).obj X ⟶
      (cobarFunctorComplex adj).asFunctor.obj X :=
  HomologicalComplex.mkHomFromSingle (cobarUnit adj X) (fun k hk => by
    obtain rfl : k = 1 := by simpa [ComplexShape.up] using hk.symm
    exact cobarUnit_comp_d adj X)

omit [Abelian B] in
omit [Abelian B] in
/-- In degree zero the augmentation of the `ℕ`-indexed cobar complex is the unit. -/
public theorem cobarNatAug_f_zero (X : A) :
    (cobarNatAug adj X).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X).hom ≫ cobarUnit adj X :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The augmentation of the `ℕ`-indexed cobar complex, as a transformation of functors: naturality
in the coefficient object is naturality of the unit of the adjunction. -/
public def cobarNatAugmentation :
    HomologicalComplex.single A (ComplexShape.up ℕ) 0 ⟶ (cobarFunctorComplex adj).asFunctor where
  app := cobarNatAug adj
  naturality X Y f := by
    refine HomologicalComplex.from_single_hom_ext (j := 0) ?_
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex.single_map_f_self, cobarNatAug_f_zero, cobarNatAug_f_zero,
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc,
      cobarUnit_naturality]

/-- A single complex in degree `0` over `ℤ` is the extension by zero of the single complex over
`ℕ`, naturally in the object. -/
public def singleCompExtendFunctorIso :
    HomologicalComplex.single A (ComplexShape.up ℤ) 0 ≅
      HomologicalComplex.single A (ComplexShape.up ℕ) 0 ⋙
        ComplexShape.embeddingUpNat.extendFunctor A :=
  NatIso.ofComponents
    (fun X => (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 rfl).symm)
    (fun {X Y} f => by
      refine HomologicalComplex.from_single_hom_ext (j := (0 : ℤ)) ?_
      change ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).map f).f 0 ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat Y 0 0 rfl).inv.f 0
          = (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 rfl).inv.f 0 ≫
            (HomologicalComplex.extendMap
              ((HomologicalComplex.single A (ComplexShape.up ℕ) 0).map f)
              ComplexShape.embeddingUpNat).f 0
      rw [HomologicalComplex.extendSingleIso_inv_f ComplexShape.embeddingUpNat X 0 (0 : ℤ) rfl,
        HomologicalComplex.extendSingleIso_inv_f ComplexShape.embeddingUpNat Y 0 (0 : ℤ) rfl,
        HomologicalComplex.extendMap_f
          ((HomologicalComplex.single A (ComplexShape.up ℕ) 0).map f)
          ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl,
        HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
      all_goals simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- **The augmentation of the cobar complex**, as a transformation from the functor sending `X` to
`X` placed in degree zero to `Stacks.Cobar.cobarComplexFunctor`: its component at `X` is the
augmentation determined by the unit `η_X : X ⟶ T X` of the adjunction. -/
public def cobarAugmentation :
    HomologicalComplex.single A (ComplexShape.up ℤ) 0 ⟶ cobarComplexFunctor adj :=
  (singleCompExtendFunctorIso).hom ≫ Functor.whiskerRight (cobarNatAugmentation adj)
    (ComplexShape.embeddingUpNat.extendFunctor A)

/-! ### Exactness and the quasi-isomorphism -/

/-- Exactness of a short complex depends only on its two morphisms, not on the proof that they
compose to zero, so it may be transported along equalities of those morphisms. -/
private lemma exact_congr_mk {X Z W : A} {f f' : X ⟶ Z} {g g' : Z ⟶ W} (hf : f = f')
    (hg : g = g') (w : f ≫ g = 0) (w' : f' ≫ g' = 0) (h : (ShortComplex.mk f g w).Exact) :
    (ShortComplex.mk f' g' w').Exact := by
  subst hf
  subst hg
  exact h

/-- The left-homology criterion used at the bottom degree of an augmented resolution. Let
`φ : S₁ ⟶ S₂` be a morphism of short complexes with `S₁` having both maps zero and `S₂` having its
first map zero. If `α : P ⟶ S₂.X₂` is a kernel of `S₂.g` and `φ.τ₂` factors through `α` by an
isomorphism, then `φ` is a quasi-isomorphism: both sides compute the kernel of the second map. -/
private lemma shortComplex_quasiIso_of_isLimit {S₁ S₂ : ShortComplex A} (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) {P : A} (α : P ⟶ S₂.X₂)
    (hα : α ≫ S₂.g = 0) (hlim : IsLimit (KernelFork.ofι α hα)) (β : S₁.X₂ ⟶ P)
    (hβ : β ≫ α = φ.τ₂) (hβiso : IsIso β) :
    ShortComplex.QuasiIso φ := by
  have := hβiso
  exact (ShortComplex.LeftHomologyMapData.ofIsLimitKernelFork φ hf₁ _
    (KernelFork.IsLimit.ofId S₁.g hg₁) hf₂ (KernelFork.ofι α hα) hlim β
    ((Category.id_comp φ.τ₂).trans hβ.symm)).quasiIso_iff.2
    (by exact inferInstanceAs (IsIso β))

section Exact

variable [L.Additive] (hrefl : ∀ S : ShortComplex A, (S.map L).Exact → S.Exact)
  (hmono : ∀ {P Q : A} (φ : P ⟶ Q), Mono (L.map φ) → Mono φ)

omit [Abelian A] [Abelian B] [L.Additive] in
include hmono in
/-- The unit of the adjunction is a monomorphism when `L` reflects monomorphisms: the triangle
identity makes its `L`-image a split monomorphism. -/
public theorem mono_unit_app (X : A) : Mono (adj.unit.app X) := by
  have : IsSplitMono (L.map (adj.unit.app X)) :=
    ⟨⟨⟨adj.counit.app (L.obj X), adj.left_triangle_components X⟩⟩⟩
  exact hmono (adj.unit.app X) inferInstance

include hrefl in
/-- **The cobar complex built from `Stacks.Cobar.cobarDiff` is exact.** This is
`Stacks.Cobar.exists_exact_cobar` re-proved for these differentials rather than for the ones that
statement chose: the contraction of the `L`-image of the cobar resolution is reused through
`Stacks.Cobar.exists_homotopyEquiv_hom_f_zero`, and the comparison
`Stacks.Cobar.op_cobarDiff_app_eq` identifies its differentials with these. -/
public theorem exact_cobarDiff_app (X : A) :
    (ShortComplex.mk (adj.unit.app X) ((cobarDiff adj 0).app X)
        (unit_app_comp_cobarDiff_app adj X)).Exact ∧
      ∀ n : ℕ, (ShortComplex.mk ((cobarDiff adj n).app X) ((cobarDiff adj (n + 1)).app X)
        (cobarDiff_app_comp_cobarDiff_app adj n X)).Exact := by
  obtain ⟨Z, h, hZ, hobj, hδ, hσ, hhom⟩ := exists_augmented_cobar adj X
  obtain ⟨he, hε⟩ := exists_homotopyEquiv_hom_f_zero adj X Z h hZ hδ hσ hhom
  have hD := op_cobarDiff_app_eq adj X Z h hobj hδ
  have hd : ∀ n : ℕ,
      (AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj
        ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z))).d (n + 1) n
        = L.op.map ((AlternatingFaceMapComplex.obj Z.left).d (n + 1) n) :=
    map_alternatingFaceMapComplex_d L.op Z.left
  have hS : ∀ n : ℕ, IsZero (((ChainComplex.single₀ Bᵒᵖ).obj
      (SimplicialObject.Augmented.point.obj
        ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z))).X (n + 1)) :=
    fun n => HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero n)
  have hunit := eqToHom_comp_unit_op_eq adj X Z h hZ hobj hhom
  have hf : ∀ n : ℕ, L.op.map (eqToHom (hobj (n + 1))) ≫ L.op.map (((cobarDiff adj n).app X).op)
      = (AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj
          ((SimplicialObject.Augmented.whiskeringObj Aᵒᵖ Bᵒᵖ L.op).obj Z))).d (n + 1) n
        ≫ L.op.map (eqToHom (hobj n)) := by
    intro n
    rw [← Functor.map_comp, hD n]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [Functor.map_comp, ← hd n]
    rfl
  have hg0 : L.op.map (eqToHom (hobj 0)) ≫ L.op.map ((adj.unit.app X).op)
      = he.hom.f 0 ≫ L.op.map (eqToHom hZ) := by
    rw [← Functor.map_comp, hunit, Functor.map_comp, hε]
    rfl
  refine ⟨?_, fun n => ?_⟩
  · exact hrefl _ ((ShortComplex.exact_op_iff _).mp (exact_of_iso_conj
      (L.op.mapIso (eqToIso (hobj 1))) (L.op.mapIso (eqToIso (hobj 0)))
      (L.op.mapIso (eqToIso hZ)) (hf 0) hg0 (exact_zero_of_homotopyEquiv he hS)))
  · exact hrefl _ ((ShortComplex.exact_op_iff _).mp (exact_of_iso_conj
      (L.op.mapIso (eqToIso (hobj (n + 1 + 1)))) (L.op.mapIso (eqToIso (hobj (n + 1))))
      (L.op.mapIso (eqToIso (hobj n))) (hf (n + 1)) (hf n)
      (exact_of_homotopyEquiv_succ he hS n)))

include hrefl hmono in
/-- **The augmentation of the `ℕ`-indexed cobar complex is a quasi-isomorphism.** In degree zero
this is the statement that the unit exhibits `X` as the kernel of the first differential, and in
the positive degrees it is exactness of `Tⁿ X ⟶ Tⁿ⁺¹ X ⟶ Tⁿ⁺² X`. -/
public theorem quasiIso_cobarNatAugmentation (X : A) :
    QuasiIso ((cobarNatAugmentation adj).app X) := by
  obtain ⟨hex0, hex⟩ := exact_cobarDiff_app adj hrefl X
  have := mono_unit_app adj hmono X
  rw [quasiIso_iff]
  rintro (_ | n)
  · rw [CochainComplex.quasiIsoAt₀_iff]
    have w : adj.unit.app X ≫ ((cobarFunctorComplex adj).asFunctor.obj X).d 0 1 = 0 :=
      cobarUnit_comp_d adj X
    have hex0' : (ShortComplex.mk (adj.unit.app X)
        (((cobarFunctorComplex adj).asFunctor.obj X).d 0 1) w).Exact :=
      exact_congr_mk rfl (cobarFunctorComplex_asFunctor_d adj X 0).symm _ w hex0
    exact shortComplex_quasiIso_of_isLimit _
      (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 X 0 0)
      (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 X 0 1)
      (((cobarFunctorComplex adj).asFunctor.obj X).shape 0 0 (by simp)) (adj.unit.app X) w
      hex0'.fIsKernel (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X).hom
      (cobarNatAug_f_zero adj X).symm (Iso.isIso_hom _)
  · rw [quasiIsoAt_iff_exactAt _ (n + 1)
      (HomologicalComplex.ExactAt.of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 X (n + 1) (by omega))),
      HomologicalComplex.exactAt_iff'
        (K := (cobarFunctorComplex adj).asFunctor.obj X) (i := n) (j := n + 1) (k := n + 2)
        (CochainComplex.prev_nat_succ n) ((ComplexShape.up ℕ).next_eq' rfl)]
    exact exact_congr_mk (cobarFunctorComplex_asFunctor_d adj X n).symm
      (cobarFunctorComplex_asFunctor_d adj X (n + 1)).symm _ _ (hex n)

include hrefl hmono in
/-- **The augmentation of the cobar complex is a quasi-isomorphism**, for an adjunction `L ⊣ R`
between abelian categories with `L` additive, reflecting exactness of short complexes and
reflecting monomorphisms. Together with
`Stacks.Cobar.cobarComplexFunctor` this says that the cobar resolution computes `X` in the derived
category, functorially in `X`. -/
public theorem quasiIso_cobarAugmentation (X : A) :
    QuasiIso ((cobarAugmentation adj).app X) := by
  have : IsIso ((singleCompExtendFunctorIso (A := A)).hom.app X) :=
    (Iso.app (singleCompExtendFunctorIso (A := A)) X).isIso_hom
  have h1 : QuasiIso (HomologicalComplex.extendMap (cobarNatAug adj X)
      ComplexShape.embeddingUpNat) := by
    rw [HomologicalComplex.quasiIso_extendMap_iff]
    exact quasiIso_cobarNatAugmentation adj hrefl hmono X
  show QuasiIso ((singleCompExtendFunctorIso (A := A)).hom.app X ≫
    HomologicalComplex.extendMap (cobarNatAug adj X) ComplexShape.embeddingUpNat)
  rw [quasiIso_iff_comp_left ((singleCompExtendFunctorIso (A := A)).hom.app X)
      (HomologicalComplex.extendMap (cobarNatAug adj X) ComplexShape.embeddingUpNat)]
  exact h1

end Exact

end Stacks.Cobar

end
