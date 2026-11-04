module

public import StacksFrontier.Cotangent.Complex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksCore.Tactic.StacksAttribute

/-!
# Degree-zero homology of the cotangent complex (Stacks 08QF)

For a homomorphism of commutative rings `A → B`, the zeroth homology of the cotangent complex
`L_{B/A}` is the module of Kähler differentials `Ω[B⁄A]`.

## Main definitions

* `CommAlgCat.cotangentTermAug`: the augmentation `B ⊗[Pₙ] Ω[Pₙ⁄A] → Ω[B⁄A]` of the cotangent
  simplicial module to the constant simplicial module on `Ω[B⁄A]`.
* `CommAlgCat.cotangentProj`: the projection onto the degree-zero opcycles of the Moore complex.
* `CommAlgCat.cotangentClass`: the class of the generator `1 ⊗ d [b]` in those opcycles.
* `CommAlgCat.cotangentOpcyclesIso`: those opcycles are `Ω[B⁄A]`.
* `CommAlgCat.cotangentComplex_homologyZeroIso`: **Stacks 08QF**.

## Main results

* `CommAlgCat.pOpcycles_cotangentTermDifferential_eq`: modulo the image of the first
  differential, the class of `1 ⊗ d p` depends only on the image of `p` in `B`. This is the
  single relation the whole computation rests on; it comes from the degree-one generator
  `[p] ∈ P₁ = A[A[B]]`, whose two faces are `p` and `[ε p]`.
* `CommAlgCat.cotangentClass_add`, `CommAlgCat.cotangentClass_mul` and
  `CommAlgCat.cotangentClass_algebraMap`: `b ↦ [1 ⊗ d [b]]` is an `A`-derivation of `B`.

## Implementation notes

The Stacks proof of 08QF goes through the identification `L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗ B)` of Lemma
08PU and computes `π_!` as a colimit over the category of polynomial algebras over `B`. None of
that machinery is available here, so the argument is carried out directly on the standard
resolution, which by Lemma 08PT computes the same thing.

Since the cotangent complex vanishes in positive cohomological degrees, its degree-zero homology
is the cokernel of `δ₀ - δ₁ : B ⊗[P₁] Ω[P₁⁄A] → B ⊗[P₀] Ω[P₀⁄A]`, i.e. the degree-zero opcycles
of the Moore complex. The relation `pOpcycles_cotangentTermDifferential_eq` then says exactly that
`b ↦ [1 ⊗ d [b]]` is a well-defined derivation on that cokernel and is inverse to the
augmentation: the three defining relations of a derivation are the images of the degree-one
generators `[a]`, `[b] + [c]` and `[b]·[c]`.

`cotangentProj` repeats `HomologicalComplex.pOpcycles` with its domain spelled as
`cotangentTerm A B (op ⦋0⦌)`. The two are definitionally equal, but only at default
transparency — `alternatingFaceMapComplex` and `cotangentSimplicialModule` both have to be
unfolded — and `rw` type-checks its motive at a lower transparency, so an element of
`cotangentTerm` fed to `pOpcycles` directly produces goals no rewrite can touch.

## References

* [Stacks Project, Tag 08QF](https://stacks.math.columbia.edu/tag/08QF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped TensorProduct ChangeOfRings

universe u v

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### The augmentation to the Kähler differentials of `B` -/

/-- The `Pₙ`-linear map `Ω[Pₙ⁄A] → Ω[B⁄A]` induced by the augmentation, adjoint to
`cotangentTermAug`. -/
public noncomputable def cotangentTermAugAdjoint (n : SimplexCategoryᵒᵖ) :
    ModuleCat.of ((standardResolution A B).left.obj n)
      (KaehlerDifferential A ((standardResolution A B).left.obj n)) ⟶
    (ModuleCat.restrictScalars (standardResolutionAugmentationHom A B n)).obj
      (ModuleCat.of B (KaehlerDifferential A B)) := by
  let : Algebra ((standardResolution A B).left.obj n) B :=
    (standardResolutionAugmentationHom A B n).toAlgebra
  have : IsScalarTower A ((standardResolution A B).left.obj n) B :=
    IsScalarTower.of_algebraMap_eq
      (fun a => (((standardResolution A B).hom.app n).hom.commutes a).symm)
  exact ModuleCat.ofHom
    (X := ModuleCat.of ((standardResolution A B).left.obj n)
      (KaehlerDifferential A ((standardResolution A B).left.obj n)))
    (Y := (ModuleCat.restrictScalars (standardResolutionAugmentationHom A B n)).obj
      (ModuleCat.of B (KaehlerDifferential A B)))
    { toFun := fun ω => KaehlerDifferential.map A A ((standardResolution A B).left.obj n) B ω
      map_add' := fun x y =>
        (KaehlerDifferential.map A A ((standardResolution A B).left.obj n) B).map_add x y
      map_smul' := fun p x =>
        (KaehlerDifferential.map A A ((standardResolution A B).left.obj n) B).map_smul p x }

/-- The augmentation `B ⊗[Pₙ] Ω[Pₙ⁄A] → Ω[B⁄A]` of the cotangent simplicial module. -/
public noncomputable def cotangentTermAug (n : SimplexCategoryᵒᵖ) :
    cotangentTerm A B n ⟶ ModuleCat.of B (KaehlerDifferential A B) :=
  (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (standardResolutionAugmentationHom A B n)).symm
    (cotangentTermAugAdjoint A B n)

/-- The augmentation sends the generator `1 ⊗ d p` to `d (ε p)`. -/
@[simp]
public theorem cotangentTermAug_D (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution A B).left.obj n) :
    cotangentTermAug A B n (cotangentTermDifferential A B n p) =
      KaehlerDifferential.D A B ((standardResolution A B).hom.app n p) := by
  have h := (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
    (standardResolutionAugmentationHom A B n)).apply_symm_apply (cotangentTermAugAdjoint A B n)
  have h2 := congrArg
    (fun k : ModuleCat.of ((standardResolution A B).left.obj n)
        (KaehlerDifferential A ((standardResolution A B).left.obj n)) ⟶
      (ModuleCat.restrictScalars (standardResolutionAugmentationHom A B n)).obj
        (ModuleCat.of B (KaehlerDifferential A B)) =>
      k (KaehlerDifferential.D A _ p)) h
  refine h2.trans ?_
  let _ : Algebra ((standardResolution A B).left.obj n) B :=
    (standardResolutionAugmentationHom A B n).toAlgebra
  have : IsScalarTower A ((standardResolution A B).left.obj n) B :=
    IsScalarTower.of_algebraMap_eq
      (fun a => (((standardResolution A B).hom.app n).hom.commutes a).symm)
  change KaehlerDifferential.map A A ((standardResolution A B).left.obj n) B
      (KaehlerDifferential.D A _ p) = _
  rw [KaehlerDifferential.map_D]
  rfl

/-- The augmentation is a morphism to the constant simplicial module: it is compatible with every
simplicial operator. -/
public theorem cotangentMap_comp_cotangentTermAug {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    cotangentMap A B f ≫ cotangentTermAug A B j = cotangentTermAug A B i := by
  refine cotangentTerm_hom_ext A B _ _ _ fun p => ?_
  rw [ModuleCat.comp_apply, cotangentMap_D, cotangentTermAug_D, cotangentTermAug_D]
  exact congrArg _ (RingHom.congr_fun (standardResolutionAugmentationHom_naturality A B f) p)

/-! ### The Moore complex and its degree-zero opcycles -/

/-- The alternating-face-map (Moore) complex of the cotangent simplicial module. The cotangent
complex is its reindexing into cohomological degrees `≤ 0`. -/
public noncomputable abbrev cotangentMooreComplex : ChainComplex (ModuleCat.{max u v} B) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
    (cotangentSimplicialModule A B).object

/-- The first differential of the Moore complex is the alternating sum of the two faces. -/
public theorem cotangentMooreComplex_d_one_zero_δ :
    (cotangentMooreComplex A B).d 1 0 =
      (cotangentSimplicialModule A B).object.δ 0 - (cotangentSimplicialModule A B).object.δ 1 := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg]
  simp

/-- The first differential of the Moore complex, with the faces spelled as `cotangentMap`, so
that `cotangentMap_D` applies to it. -/
public theorem cotangentMooreComplex_d_one_zero :
    (cotangentMooreComplex A B).d 1 0 =
      (cotangentMap A B (SimplexCategory.δ (0 : Fin 2)).op -
        cotangentMap A B (SimplexCategory.δ (1 : Fin 2)).op :
      cotangentTerm A B (op ⦋0 + 1⦌) ⟶ cotangentTerm A B (op ⦋0⦌)) :=
  cotangentMooreComplex_d_one_zero_δ A B

/-- The projection onto the degree-zero opcycles of the Moore complex, with its domain spelled as
`cotangentTerm A B (op ⦋0⦌)`. -/
public noncomputable def cotangentProj :
    cotangentTerm A B (op ⦋0⦌) ⟶ (cotangentMooreComplex A B).opcycles 0 :=
  (cotangentMooreComplex A B).pOpcycles 0

/-- The projection onto the opcycles is epi, with the domain spelled as `cotangentTerm`. -/
public theorem epi_cotangentProj : Epi (cotangentProj A B) :=
  (inferInstance : Epi ((cotangentMooreComplex A B).pOpcycles 0))

/-- The alternating sum of the two faces is killed by the projection to the opcycles. -/
public theorem cotangentMap_sub_comp_cotangentProj :
    ((cotangentMap A B (SimplexCategory.δ (0 : Fin 2)).op -
        cotangentMap A B (SimplexCategory.δ (1 : Fin 2)).op :
      cotangentTerm A B (op ⦋0 + 1⦌) ⟶ cotangentTerm A B (op ⦋0⦌))) ≫
        cotangentProj A B = 0 :=
  (congrArg (fun k : cotangentTerm A B (op ⦋0 + 1⦌) ⟶ cotangentTerm A B (op ⦋0⦌) =>
      k ≫ cotangentProj A B) (cotangentMooreComplex_d_one_zero A B).symm).trans
    ((cotangentMooreComplex A B).d_pOpcycles 1 0)

/-- **The key relation.** Modulo the image of the first differential, the class of the generator
`1 ⊗ d p` depends only on the image of `p` under the augmentation. It is witnessed by the
degree-one generator `1 ⊗ d [p]`, whose zeroth face is `1 ⊗ d p` and whose first face is
`1 ⊗ d [ε p]`. -/
public theorem pOpcycles_cotangentTermDifferential_eq
    (p : (standardResolution A B).left.obj (op ⦋0⦌)) :
    cotangentProj A B (cotangentTermDifferential A B (op ⦋0⦌) p) =
      cotangentProj A B (cotangentTermDifferential A B (op ⦋0⦌)
        (standardResolutionVarZero A B ((standardResolution A B).hom.app (op ⦋0⦌) p))) := by
  have h : cotangentProj A B
      ((cotangentMap A B (SimplexCategory.δ (0 : Fin 2)).op :
          cotangentTerm A B (op ⦋0 + 1⦌) ⟶ cotangentTerm A B (op ⦋0⦌))
        (cotangentTermDifferential A B (op ⦋0 + 1⦌) (standardResolutionVarOne A B p)) -
      (cotangentMap A B (SimplexCategory.δ (1 : Fin 2)).op :
          cotangentTerm A B (op ⦋0 + 1⦌) ⟶ cotangentTerm A B (op ⦋0⦌))
        (cotangentTermDifferential A B (op ⦋0 + 1⦌) (standardResolutionVarOne A B p))) = 0 :=
    congrArg (fun k : cotangentTerm A B (op ⦋0 + 1⦌) ⟶ (cotangentMooreComplex A B).opcycles 0 =>
      k (cotangentTermDifferential A B (op ⦋0 + 1⦌) (standardResolutionVarOne A B p)))
      (cotangentMap_sub_comp_cotangentProj A B)
  have e₀ : (cotangentMap A B (SimplexCategory.δ (0 : Fin 2)).op :
        cotangentTerm A B (op ⦋0 + 1⦌) ⟶ cotangentTerm A B (op ⦋0⦌))
      (cotangentTermDifferential A B (op ⦋0 + 1⦌) (standardResolutionVarOne A B p)) =
      cotangentTermDifferential A B (op ⦋0⦌) p := by
    rw [cotangentMap_D]
    exact congrArg _ (standardResolution_δ_zero_varOne A B p)
  have e₁ : (cotangentMap A B (SimplexCategory.δ (1 : Fin 2)).op :
        cotangentTerm A B (op ⦋0 + 1⦌) ⟶ cotangentTerm A B (op ⦋0⦌))
      (cotangentTermDifferential A B (op ⦋0 + 1⦌) (standardResolutionVarOne A B p)) =
      cotangentTermDifferential A B (op ⦋0⦌)
        (standardResolutionVarZero A B ((standardResolution A B).hom.app (op ⦋0⦌) p)) := by
    rw [cotangentMap_D]
    exact congrArg _ (standardResolution_δ_one_varOne A B p)
  rw [e₀, e₁, map_sub, sub_eq_zero] at h
  exact h

/-! ### The degree-zero opcycles are the Kähler differentials -/

/-- The class of the generator `1 ⊗ d [b]` in the degree-zero opcycles. -/
public noncomputable def cotangentClass (b : B) : (cotangentMooreComplex A B).opcycles 0 :=
  cotangentProj A B (cotangentTermDifferential A B (op ⦋0⦌) (standardResolutionVarZero A B b))

/-- The class of `1 ⊗ d p` is `cotangentClass b` whenever `p` maps to `b`. -/
private theorem cotangentProj_D_eq_cotangentClass (p : (standardResolution A B).left.obj (op ⦋0⦌))
    (b : B) (hp : (standardResolution A B).hom.app (op ⦋0⦌) p = b) :
    cotangentProj A B (cotangentTermDifferential A B (op ⦋0⦌) p) = cotangentClass A B b :=
  hp ▸ pOpcycles_cotangentTermDifferential_eq A B p

/-- `b ↦ [1 ⊗ d [b]]` is additive. -/
public theorem cotangentClass_add (b c : B) :
    cotangentClass A B (b + c) = cotangentClass A B b + cotangentClass A B c := by
  rw [← cotangentProj_D_eq_cotangentClass A B
    (standardResolutionVarZero A B b + standardResolutionVarZero A B c) _
    (by rw [map_add, standardResolution_augmentation_varZero,
      standardResolution_augmentation_varZero]),
    cotangentTermDifferential_add, map_add]
  rfl

/-- `b ↦ [1 ⊗ d [b]]` satisfies the Leibniz rule. -/
public theorem cotangentClass_mul (b c : B) :
    cotangentClass A B (b * c) = b • cotangentClass A B c + c • cotangentClass A B b := by
  rw [← cotangentProj_D_eq_cotangentClass A B
    (standardResolutionVarZero A B b * standardResolutionVarZero A B c) _
    (by rw [map_mul, standardResolution_augmentation_varZero,
      standardResolution_augmentation_varZero]),
    cotangentTermDifferential_mul, map_add, map_smul, map_smul,
    show standardResolutionAugmentationHom A B (op ⦋0⦌) (standardResolutionVarZero A B b) = b from
      standardResolution_augmentation_varZero A B b,
    show standardResolutionAugmentationHom A B (op ⦋0⦌) (standardResolutionVarZero A B c) = c from
      standardResolution_augmentation_varZero A B c]
  rfl

/-- `b ↦ [1 ⊗ d [b]]` kills the image of `A`. -/
public theorem cotangentClass_algebraMap (a : A) :
    cotangentClass A B (algebraMap A B a) = 0 := by
  rw [← cotangentProj_D_eq_cotangentClass A B
    (algebraMap A ((standardResolution A B).left.obj (op ⦋0⦌)) a) (algebraMap A B a)
    (((standardResolution A B).hom.app (op ⦋0⦌)).hom.commutes a),
    cotangentTermDifferential_algebraMap, map_zero]

/-- `b ↦ [1 ⊗ d [b]]` is `A`-linear. -/
public theorem cotangentClass_smul (a : A) (b : B) :
    cotangentClass A B (a • b) = algebraMap A B a • cotangentClass A B b := by
  rw [Algebra.smul_def, cotangentClass_mul, cotangentClass_algebraMap, smul_zero, add_zero]

/-- The relations defining `Ω[B⁄A]` as a quotient of the free module on `B` are satisfied by
`b ↦ [1 ⊗ d [b]]`. -/
public theorem kerTotal_le_ker_cotangentClass :
    KaehlerDifferential.kerTotal A B ≤
      LinearMap.ker (Finsupp.linearCombination B (cotangentClass A B)) := by
  rw [KaehlerDifferential.kerTotal, Submodule.span_le]
  rintro _ ((⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨a, rfl⟩) <;>
    simp [LinearMap.mem_ker, cotangentClass_add, cotangentClass_mul, cotangentClass_algebraMap,
      add_comm]

/-- The canonical map `Ω[B⁄A] → H⁰(L_{B/A})`, into the degree-zero opcycles of the Moore complex,
induced by the derivation `b ↦ [1 ⊗ d [b]]`. -/
public noncomputable def kaehlerToCotangentOpcycles :
    ModuleCat.of B (KaehlerDifferential A B) ⟶ (cotangentMooreComplex A B).opcycles 0 :=
  ModuleCat.ofHom
    (((KaehlerDifferential.kerTotal A B).liftQ
        (Finsupp.linearCombination B (cotangentClass A B))
        (kerTotal_le_ker_cotangentClass A B)).comp
      (KaehlerDifferential.quotKerTotalEquiv A B).symm.toLinearMap)

/-- The canonical map sends `d b` to the class of `1 ⊗ d [b]`. -/
@[simp]
public theorem kaehlerToCotangentOpcycles_D (b : B) :
    kaehlerToCotangentOpcycles A B (KaehlerDifferential.D A B b) = cotangentClass A B b := by
  have h : (KaehlerDifferential.quotKerTotalEquiv A B).symm (KaehlerDifferential.D A B b) =
      (KaehlerDifferential.kerTotal A B).mkQ (Finsupp.single b 1) :=
    Derivation.congr_fun (KaehlerDifferential.quotKerTotalEquiv_symm_comp_D A B) b
  change ((KaehlerDifferential.kerTotal A B).liftQ
      (Finsupp.linearCombination B (cotangentClass A B))
      (kerTotal_le_ker_cotangentClass A B))
    ((KaehlerDifferential.quotKerTotalEquiv A B).symm (KaehlerDifferential.D A B b)) = _
  rw [h, Submodule.mkQ_apply, Submodule.liftQ_apply, Finsupp.linearCombination_single,
    one_smul]

/-- The augmentation descends to the degree-zero opcycles. -/
public noncomputable def cotangentOpcyclesToKaehler :
    (cotangentMooreComplex A B).opcycles 0 ⟶ ModuleCat.of B (KaehlerDifferential A B) :=
  (cotangentMooreComplex A B).descOpcycles (cotangentTermAug A B (op ⦋0⦌)) 1 (by simp) (by
    refine Eq.trans (congrArg (fun k : cotangentTerm A B (op ⦋0 + 1⦌) ⟶
        cotangentTerm A B (op ⦋0⦌) => k ≫ cotangentTermAug A B (op ⦋0⦌))
      (cotangentMooreComplex_d_one_zero A B)) ?_
    rw [Preadditive.sub_comp, cotangentMap_comp_cotangentTermAug,
      cotangentMap_comp_cotangentTermAug, sub_self]
    rfl)

/-- The projection followed by the descended augmentation is the augmentation. -/
public theorem cotangentProj_comp_cotangentOpcyclesToKaehler :
    cotangentProj A B ≫ cotangentOpcyclesToKaehler A B = cotangentTermAug A B (op ⦋0⦌) :=
  (cotangentMooreComplex A B).p_descOpcycles _ _ _ _

/-- The augmentation followed by the canonical map back is the projection: this is the key
relation, read as an identity of morphisms. -/
public theorem cotangentTermAug_comp_kaehlerToCotangentOpcycles :
    cotangentTermAug A B (op ⦋0⦌) ≫ kaehlerToCotangentOpcycles A B = cotangentProj A B := by
  refine cotangentTerm_hom_ext A B _ _ _ fun p => ?_
  rw [ModuleCat.comp_apply, cotangentTermAug_D, kaehlerToCotangentOpcycles_D, cotangentClass]
  exact (pOpcycles_cotangentTermDifferential_eq A B p).symm

/-- The degree-zero opcycles of the Moore complex are the Kähler differentials of `B` over `A`. -/
public noncomputable def cotangentOpcyclesIso :
    (cotangentMooreComplex A B).opcycles 0 ≅ ModuleCat.of B (KaehlerDifferential A B) where
  hom := cotangentOpcyclesToKaehler A B
  inv := kaehlerToCotangentOpcycles A B
  hom_inv_id := by
    have := epi_cotangentProj A B
    rw [← cancel_epi (cotangentProj A B), Category.comp_id, ← Category.assoc,
      cotangentProj_comp_cotangentOpcyclesToKaehler,
      cotangentTermAug_comp_kaehlerToCotangentOpcycles]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B) ?_
    rintro _ ⟨b, rfl⟩
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    change cotangentOpcyclesToKaehler A B (kaehlerToCotangentOpcycles A B
      (KaehlerDifferential.D A B b)) = _
    rw [kaehlerToCotangentOpcycles_D, cotangentClass, ← ModuleCat.comp_apply,
      cotangentProj_comp_cotangentOpcyclesToKaehler, cotangentTermAug_D,
      standardResolution_augmentation_varZero]
    rfl

/-! ### The theorem -/

/-- **Stacks Project, Tag 08QF.** The degree-zero homology of the cotangent complex `L_{B/A}` is
the module of Kähler differentials `Ω[B⁄A]`. -/
@[stacks 08QF]
public noncomputable def cotangentComplex_homologyZeroIso :
    (cotangentComplex A B).homology 0 ≅ ModuleCat.of B (KaehlerDifferential A B) :=
  (HomologicalComplex.extendHomologyIso (cotangentMooreComplex A B)
      (ComplexShape.embeddingUpIntLE 0) (j := 0) (j' := 0) (by simp)) ≪≫
    (cotangentMooreComplex A B).isoHomologyι₀ ≪≫ cotangentOpcyclesIso A B

end CommAlgCat

end
