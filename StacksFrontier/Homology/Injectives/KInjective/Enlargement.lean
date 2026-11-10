module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.CategoryTheory.Preadditive.Injective.GrothendieckFunctorial
import StacksCore.Tactic.StacksAttribute

/-!
# Functorial injective enlargement of complexes

Let `C` be a Grothendieck abelian category. Tag 079N produces a functor
`N : CochainComplex C ℤ ⥤ CochainComplex C ℤ` together with a natural transformation `j : 𝟭 ⟶ N`
which is a termwise monomorphism and a quasi-isomorphism, and such that in every degree `n` the map
`M ^ n ⟶ N (M) ^ n` factors through an injective subobject of `N (M) ^ n`.

A Grothendieck abelian category factors every morphism functorially as a monomorphism followed by a
morphism having the right lifting property with respect to all monomorphisms; applying this to
`X ⟶ 0` gives a functorial injective embedding `X ⟶ I (X)`. Out of it one builds the complex
`J (M)` with terms `J (M) ^ n = I (M ^ n) ⊕ I (M ^ (n + 1))` and the differential which is the
identity from the second summand in degree `n` to the first summand in degree `n + 1`; its terms
are injective and the map `u : M ⟶ J (M)` whose components are `i ≫ (i ∘ d)` is a termwise
monomorphism. With `Q (M) = J (M) / M` and `v : J (M) ⟶ Q (M)` the quotient map, the enlargement is
the mapping cocone `N (M) = C (v) [-1]`, and `j` is the lift of `u` along `v`. There is a short
exact sequence `0 ⟶ M ⟶ N (M) ⟶ W (M) ⟶ 0` whose third term is the mapping cocone `W (M)` of the
identity of `Q (M)`.

## Main definitions

* `Stacks.Injectives.injectiveEmbedding`: the functorial injective embedding `X ⟶ I (X)`.
* `Stacks.Injectives.injectiveEnvelope`: the functor `M ↦ J (M)`, with terms injective.
* `Stacks.Injectives.injectiveEnlargement`: the functor `M ↦ N (M)` of the source.
* `Stacks.Injectives.FunctorialInjectiveResolution`: the data asserted by Tag 079N.

## Main results

* `Stacks.Injectives.exists_functorialInjectiveResolution`: a Grothendieck abelian category admits
  a functorial injective enlargement of cochain complexes.
* `Stacks.Injectives.quasiIso_of_shortExact_of_acyclic_X₃`: a short exact sequence of cochain
  complexes with acyclic third term has a quasi-isomorphism as its first map.
* `Stacks.Injectives.acyclic_mappingCocone_id`: the mapping cocone of an identity is acyclic.

## Implementation notes

Mathlib's mapping cocone is used rather than a hand-rolled complex with a shifted summand: its
components are indexed by explicit degrees together with proofs relating them, which keeps all the
index bookkeeping of the construction out of the definitions. Two extensionality lemmas for mapping
cocones (`mappingCocone_hom_ext` for morphisms of complexes and `mappingCocone_X_hom_ext`,
`mappingCocone_X_hom_ext'` in a single degree) are proved from `CochainComplex.mappingCocone.id_X`;
they are what replaces the degreewise matrix calculus.

## References

* [Stacks Project, Tag 079N](https://stacks.math.columbia.edu/tag/079N)
-/

@[expose] public noncomputable section

open CategoryTheory Limits ZeroObject CochainComplex

universe w v u

namespace Stacks.Injectives

section General

variable {A : Type u} [Category.{v} A] [Abelian A]


/-- If the third term of a short exact sequence of cochain complexes is acyclic, the first map
of the sequence is a quasi-isomorphism. -/
lemma quasiIso_of_shortExact_of_acyclic_X₃ {S : ShortComplex (CochainComplex A ℤ)}
    (hS : S.ShortExact) (hX₃ : S.X₃.Acyclic) : QuasiIso S.f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap S.f n) :=
    (hS.homology_exact₁ (n - 1) n (by simp)).mono_g ((hX₃ (n - 1)).isZero_homology.eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap S.f n) :=
    (hS.homology_exact₂ n).epi_f ((hX₃ n).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- A cochain complex which becomes a zero object in the homotopy category is acyclic. -/
lemma acyclic_of_isZero_quotient_obj (K : CochainComplex A ℤ)
    (hK : IsZero ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) : K.Acyclic := by
  have h : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (𝟙 K) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map 0 := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact hK.eq_of_src _ _
  have ho := HomotopyCategory.homotopyOfEq _ _ h
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero,
    ← HomologicalComplex.homologyMap_id, ho.homologyMap_eq n]
  simp

variable {K L : CochainComplex A ℤ} (φ : K ⟶ L)

/-- Two morphisms into a mapping cocone which have the same two components are equal. -/
lemma mappingCocone_hom_ext {M : CochainComplex A ℤ} (a b : M ⟶ mappingCocone φ)
    (hfst : ∀ n, a.f n ≫ (mappingCocone.fst φ).f n = b.f n ≫ (mappingCocone.fst φ).f n)
    (hsnd : ∀ n, a.f n ≫ (mappingCocone.snd φ).v n (n - 1) (by omega) =
      b.f n ≫ (mappingCocone.snd φ).v n (n - 1) (by omega)) :
    a = b := by
  ext n
  have hid := mappingCocone.id_X φ n (n - 1) (by omega)
  rw [← Category.comp_id (a.f n), ← hid, ← Category.comp_id (b.f n), ← hid]
  simp only [Preadditive.comp_add, ← Category.assoc, hfst n, hsnd n]

/-- Two morphisms into a term of a mapping cocone which have the same two components are equal. -/
lemma mappingCocone_X_hom_ext {K L : CochainComplex A ℤ} (φ : K ⟶ L) {T : A} (n : ℤ)
    (a b : T ⟶ (mappingCocone φ).X n)
    (hfst : a ≫ (mappingCocone.fst φ).f n = b ≫ (mappingCocone.fst φ).f n)
    (hsnd : a ≫ (mappingCocone.snd φ).v n (n - 1) (by omega) =
      b ≫ (mappingCocone.snd φ).v n (n - 1) (by omega)) :
    a = b := by
  have hid := mappingCocone.id_X φ n (n - 1) (by omega)
  rw [← Category.comp_id a, ← hid, ← Category.comp_id b, ← hid]
  simp only [Preadditive.comp_add, ← Category.assoc, hfst, hsnd]

/-- Two morphisms out of a term of a mapping cocone which agree on both inclusions are equal. -/
lemma mappingCocone_X_hom_ext' {K L : CochainComplex A ℤ} (φ : K ⟶ L) {T : A} (n : ℤ)
    (a b : (mappingCocone φ).X n ⟶ T)
    (hinl : (mappingCocone.inl φ).v n n (add_zero n) ≫ a =
      (mappingCocone.inl φ).v n n (add_zero n) ≫ b)
    (hinr : ((mappingCocone.inr φ).1).v (n - 1) n (by omega) ≫ a =
      ((mappingCocone.inr φ).1).v (n - 1) n (by omega) ≫ b) :
    a = b := by
  have hid := mappingCocone.id_X φ n (n - 1) (by omega)
  rw [← Category.id_comp a, ← hid, ← Category.id_comp b, ← hid]
  simp only [Preadditive.add_comp, Category.assoc, hinl, hinr]

/-- The mapping cocone of an identity is acyclic. -/
lemma acyclic_mappingCocone_id (Q : CochainComplex A ℤ) : (mappingCocone (𝟙 Q)).Acyclic := by
  have h1 : IsZero ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
      (mappingCone (𝟙 Q))) := by
    rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id,
      HomotopyCategory.eq_of_homotopy _ _ (mappingCone.homotopyToZeroOfId Q),
      CategoryTheory.Functor.map_zero]
  refine acyclic_of_isZero_quotient_obj _ (IsZero.of_iso ?_
    (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso (-1 : ℤ)).app
      (mappingCone (𝟙 Q))))
  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (mappingCone (𝟙 Q)))⟦(-1 : ℤ)⟧)
      = (CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ))
          (-1 : ℤ)).map (𝟙 _) := by rw [CategoryTheory.Functor.map_id]
    _ = (CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ))
          (-1 : ℤ)).map 0 := by rw [h1.eq_of_src (𝟙 _) 0]
    _ = 0 := CategoryTheory.Functor.map_zero _ _ _

end General

section General2

variable {A : Type u} [Category.{v} A] [Abelian A]
  {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}


/-- The first component of the mapping cone of a square. -/
lemma mappingConeMap_f_fst (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) (n : ℤ) :
    (mappingCone.map φ₁ φ₂ a b comm).f n ≫
        (mappingCone.fst φ₂).1.v n (n + 1) (by omega) =
      (mappingCone.fst φ₁).1.v n (n + 1) (by omega) ≫ a.f (n + 1) := by
  simp [mappingCone.map, mappingCone.desc_f, Category.assoc]

/-- The second component of the mapping cone of a square. -/
lemma mappingConeMap_f_snd (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) (n : ℤ) :
    (mappingCone.map φ₁ φ₂ a b comm).f n ≫
        (mappingCone.snd φ₂).v n n (by omega) =
      (mappingCone.snd φ₁).v n n (by omega) ≫ b.f n := by
  simp [mappingCone.map, mappingCone.desc_f, Category.assoc]

variable {K L : CochainComplex A ℤ}

/-- `mappingCocone.fst` in terms of `mappingCone.fst`. -/
lemma mappingCocone_fst_f (φ : K ⟶ L) (n : ℤ) :
    (mappingCocone.fst φ).f n =
      ((mappingCone φ).shiftFunctorObjXIso (-1) n (n - 1) (by omega)).hom ≫
        (mappingCone.fst φ).1.v (n - 1) n (by omega) := by
  dsimp [mappingCocone.fst]
  rw [HomComplex.Cocycle.homOf_f, HomComplex.Cocycle.leftShift_coe,
    (mappingCone.fst φ).1.leftShift_v (-1) 0 (by omega) n n (by omega) (n - 1) (by omega)]
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  all_goals rfl

/-- `mappingCocone.snd` in terms of `mappingCone.snd`. -/
lemma mappingCocone_snd_v (φ : K ⟶ L) (n : ℤ) :
    (mappingCocone.snd φ).v n (n - 1) (by omega) =
      ((mappingCone φ).shiftFunctorObjXIso (-1) n (n - 1) (by omega)).hom ≫
        (mappingCone.snd φ).v (n - 1) (n - 1) (by omega) := by
  dsimp [mappingCocone.snd]
  change ((mappingCone.snd φ).leftShift (-1) (-1) (by omega)).v n (n - 1) (by omega) = _
  rw [(mappingCone.snd φ).leftShift_v (-1) (-1) (by omega) n (n - 1) (by omega) (n - 1) (by omega)]
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Int.negOnePow_even 2 ⟨1, rfl⟩]

/-- The shift by `-1` of a morphism, composed with the identifications of the shifted terms. -/
private lemma shift_map_f_comp_shiftFunctorObjXIso {X Y : CochainComplex A ℤ} (g : X ⟶ Y) (n : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map g).f n ≫
        (Y.shiftFunctorObjXIso (-1) n (n - 1) (by omega)).hom =
      (X.shiftFunctorObjXIso (-1) n (n - 1) (by omega)).hom ≫ g.f (n - 1) :=
  by
  rw [shiftFunctorObjXIso, shiftFunctorObjXIso, CochainComplex.shiftFunctor_map_f']
  exact (HomologicalComplex.XIsoOfEq_hom_naturality g (show n + -1 = n - 1 by omega))

/-- The shift by `-1` of the mapping cone of a square, composed with `mappingCocone.fst`. -/
lemma shiftedConeMap_f_fst (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) (n : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
          (mappingCone.map φ₁ φ₂ a b comm)).f n ≫ (mappingCocone.fst φ₂).f n =
      (mappingCocone.fst φ₁).f n ≫ a.f n := by
  have h : (mappingCone.map φ₁ φ₂ a b comm).f (n - 1) ≫
        (mappingCone.fst φ₂).1.v (n - 1) n (by omega) =
      (mappingCone.fst φ₁).1.v (n - 1) n (by omega) ≫ a.f n := by
    convert mappingConeMap_f_fst φ₁ φ₂ a b comm (n - 1) <;> omega
  rw [mappingCocone_fst_f, mappingCocone_fst_f, ← Category.assoc,
    shift_map_f_comp_shiftFunctorObjXIso, Category.assoc, h]
  exact (Category.assoc _ _ _).symm

/-- The shift by `-1` of the mapping cone of a square, composed with `mappingCocone.snd`. -/
lemma shiftedConeMap_f_snd (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) (n : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
          (mappingCone.map φ₁ φ₂ a b comm)).f n ≫
        (mappingCocone.snd φ₂).v n (n - 1) (by omega) =
      (mappingCocone.snd φ₁).v n (n - 1) (by omega) ≫ b.f (n - 1) := by
  rw [mappingCocone_snd_v, mappingCocone_snd_v, ← Category.assoc,
    shift_map_f_comp_shiftFunctorObjXIso, Category.assoc, mappingConeMap_f_snd]
  exact (Category.assoc _ _ _).symm


end General2

section Construction


variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- A functorial injective embedding in a Grothendieck abelian category. -/
def injectiveEmbedding : C ⥤ C := FunctorialEmbedding.embedding C

/-- The natural monomorphism from an object into its functorial injective embedding. -/
def injectiveEmbeddingι : 𝟭 C ⟶ injectiveEmbedding C := FunctorialEmbedding.unit C

/-- The map from an object to its functorial injective embedding is a monomorphism. -/
instance (X : C) : Mono ((injectiveEmbeddingι C).app X) :=
  FunctorialEmbedding.mono_unit_app C X

/-- The functorial injective embedding of an object is injective. -/
instance (X : C) : Injective ((injectiveEmbedding C).obj X) :=
  FunctorialEmbedding.injective_embedding_obj C X

/-! ### The termwise injective acyclic complex `J` -/

/-- The differential of `injectiveEnvelopeObj`. -/
def envelopeD (M : CochainComplex C ℤ) (i j : ℤ) :=
  if h : i + 1 = j then by
    subst j
    exact biprod.desc
      (0 : (injectiveEmbedding C).obj (M.X i) ⟶
        (injectiveEmbedding C).obj (M.X (i + 1)) ⊞
          (injectiveEmbedding C).obj (M.X (i + 1 + 1)))
      (biprod.inl : (injectiveEmbedding C).obj (M.X (i + 1)) ⟶
        (injectiveEmbedding C).obj (M.X (i + 1)) ⊞
          (injectiveEmbedding C).obj (M.X (i + 1 + 1)))
    else (0 : (injectiveEmbedding C).obj (M.X i) ⊞ (injectiveEmbedding C).obj (M.X (i + 1)) ⟶
      (injectiveEmbedding C).obj (M.X j) ⊞ (injectiveEmbedding C).obj (M.X (j + 1)))

/-- The complex with terms `I(M ^ n) ⊕ I(M ^ (n + 1))` and the shift differential. -/
def injectiveEnvelopeObj (M : CochainComplex C ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.mk
    (fun n => (injectiveEmbedding C).obj (M.X n) ⊞ (injectiveEmbedding C).obj (M.X (n + 1)))
    (envelopeD C M)
    (by intro i j hij; simp only [ComplexShape.up_Rel] at hij; simp [envelopeD, hij])
    (by
      intro i j k hij hjk
      simp only [ComplexShape.up_Rel] at hij hjk
      subst j
      subst k
      apply biprod.hom_ext' <;> simp [envelopeD])

/-- The functoriality of `injectiveEnvelopeObj`. -/
def envelopeMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    injectiveEnvelopeObj C M ⟶ injectiveEnvelopeObj C N where
  f n := biprod.map ((injectiveEmbedding C).map (f.f n))
    ((injectiveEmbedding C).map (f.f (n + 1)))
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst j
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp [injectiveEnvelopeObj, envelopeD]
    · simp [injectiveEnvelopeObj, envelopeD]

/-- The functor `M ↦ J(M)`, with values termwise injective acyclic complexes. -/
def injectiveEnvelope : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := injectiveEnvelopeObj C
  map := envelopeMap C
  map_id M := by
    ext n
    dsimp [envelopeMap, injectiveEnvelopeObj]
    apply biprod.hom_ext'
    · simp [biprod.inl_map]
    · simp [biprod.inr_map]
  map_comp f g := by
    ext n
    dsimp [envelopeMap, injectiveEnvelopeObj]
    apply biprod.hom_ext'
    · simp [biprod.inl_map_assoc, Functor.map_comp]
    · simp [biprod.inr_map_assoc, Functor.map_comp]

/-- The canonical termwise monomorphism `M ⟶ J(M)`. -/
def envelopeι (M : CochainComplex C ℤ) : M ⟶ injectiveEnvelopeObj C M where
  f n := biprod.lift ((injectiveEmbeddingι C).app (M.X n))
      (M.d n (n + 1) ≫ (injectiveEmbeddingι C).app (M.X (n + 1)))
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst j
    apply biprod.hom_ext
    · simp [injectiveEnvelopeObj, envelopeD, Category.assoc]
    · simp [injectiveEnvelopeObj, envelopeD, Category.assoc]

/-- The natural termwise monomorphism `𝟭 ⟶ J`. -/
def injectiveEnvelopeι : 𝟭 (CochainComplex C ℤ) ⟶ injectiveEnvelope C where
  app M := envelopeι C M
  naturality M N f := by
    ext n
    dsimp [envelopeι, envelopeMap, injectiveEnvelope, Functor.id_map]
    apply biprod.hom_ext
    · calc
        (f.f n ≫ biprod.lift ((injectiveEmbeddingι C).app (N.X n))
          (N.d n (n + 1) ≫ (injectiveEmbeddingι C).app (N.X (n + 1)))) ≫ biprod.fst =
            f.f n ≫ (injectiveEmbeddingι C).app (N.X n) := by simp
        _ = (injectiveEmbeddingι C).app (M.X n) ≫ (injectiveEmbedding C).map (f.f n) :=
          (injectiveEmbeddingι C).naturality (f.f n)
        _ = (biprod.lift ((injectiveEmbeddingι C).app (M.X n))
          (M.d n (n + 1) ≫ (injectiveEmbeddingι C).app (M.X (n + 1))) ≫
            biprod.map ((injectiveEmbedding C).map (f.f n))
              ((injectiveEmbedding C).map (f.f (n + 1)))) ≫ biprod.fst := by simp
    · calc
        (f.f n ≫ biprod.lift ((injectiveEmbeddingι C).app (N.X n))
          (N.d n (n + 1) ≫ (injectiveEmbeddingι C).app (N.X (n + 1)))) ≫ biprod.snd =
            f.f n ≫ N.d n (n + 1) ≫ (injectiveEmbeddingι C).app (N.X (n + 1)) := by
              simp [Category.assoc]
        _ = M.d n (n + 1) ≫ f.f (n + 1) ≫ (injectiveEmbeddingι C).app (N.X (n + 1)) := by
          simp
        _ = M.d n (n + 1) ≫ ((injectiveEmbeddingι C).app (M.X (n + 1)) ≫
            (injectiveEmbedding C).map (f.f (n + 1))) := by
          simpa only [Functor.id_map] using congrArg
            (fun z => M.d n (n + 1) ≫ z) ((injectiveEmbeddingι C).naturality (f.f (n + 1)))
        _ = (biprod.lift ((injectiveEmbeddingι C).app (M.X n))
          (M.d n (n + 1) ≫ (injectiveEmbeddingι C).app (M.X (n + 1))) ≫
            biprod.map ((injectiveEmbedding C).map (f.f n))
              ((injectiveEmbedding C).map (f.f (n + 1)))) ≫ biprod.snd := by
          simp [Category.assoc]

/-- Every term of `J(M)` is injective. -/
instance (M : CochainComplex C ℤ) (n : ℤ) :
    Injective (((injectiveEnvelope C).obj M).X n) := by
  change Injective ((injectiveEmbedding C).obj (M.X n) ⊞
    (injectiveEmbedding C).obj (M.X (n + 1)))
  infer_instance

/-- The map `M ⟶ J(M)` is a monomorphism in every degree. -/
instance (M : CochainComplex C ℤ) (n : ℤ) :
    Mono (((injectiveEnvelopeι C).app M).f n) := by
  have h : ((injectiveEnvelopeι C).app M).f n ≫
      (biprod.fst : (injectiveEmbedding C).obj (M.X n) ⊞
        (injectiveEmbedding C).obj (M.X (n + 1)) ⟶ _) =
      (injectiveEmbeddingι C).app (M.X n) := biprod.lift_fst _ _
  exact mono_of_mono_fac h



/-! ### The quotient `Q(M) = J(M)/M` -/

/-- The functoriality of the quotient `Q(M) = J(M)/M`. -/
def envelopeQuotientMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    cokernel ((injectiveEnvelopeι C).app M) ⟶ cokernel ((injectiveEnvelopeι C).app N) :=
  cokernel.map ((injectiveEnvelopeι C).app M) ((injectiveEnvelopeι C).app N) f
    ((injectiveEnvelope C).map f) ((injectiveEnvelopeι C).naturality f).symm

/-- The functor `M ↦ Q(M) = J(M)/M`. -/
def injectiveEnvelopeQuotient : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj M := cokernel ((injectiveEnvelopeι C).app M)
  map := envelopeQuotientMap C
  map_id M := by simp [envelopeQuotientMap, cokernel.map_id]
  map_comp f g := by
    rw [← cancel_epi (cokernel.π ((injectiveEnvelopeι C).app _))]
    simp [envelopeQuotientMap, Category.assoc]

/-- The natural epimorphism `J ⟶ Q`. -/
def injectiveEnvelopeπ : injectiveEnvelope C ⟶ injectiveEnvelopeQuotient C where
  app M := cokernel.π ((injectiveEnvelopeι C).app M)
  naturality M N f := by simp [injectiveEnvelopeQuotient, envelopeQuotientMap]

/-- The composite `M ⟶ J(M) ⟶ Q(M)` is zero. -/
lemma injectiveEnvelopeι_comp_π (M : CochainComplex C ℤ) :
    (injectiveEnvelopeι C).app M ≫ (injectiveEnvelopeπ C).app M = 0 :=
  cokernel.condition _

/-- The short exact sequence `0 ⟶ M ⟶ J(M) ⟶ Q(M) ⟶ 0`. -/
def envelopeShortComplex (M : CochainComplex C ℤ) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk ((injectiveEnvelopeι C).app M) ((injectiveEnvelopeπ C).app M)
    (injectiveEnvelopeι_comp_π C M)

/-- The sequence `0 ⟶ M ⟶ J(M) ⟶ Q(M) ⟶ 0` is short exact. -/
lemma envelopeShortComplex_shortExact (M : CochainComplex C ℤ) :
    (envelopeShortComplex C M).ShortExact where
  mono_f := HomologicalComplex.mono_of_mono_f _
    (fun n => show Mono (((injectiveEnvelopeι C).app M).f n) from inferInstance)
  epi_g := show Epi (cokernel.π ((injectiveEnvelopeι C).app M)) from inferInstance
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/-- In every degree `n`, the sequence `0 ⟶ M ^ n ⟶ J(M) ^ n ⟶ Q(M) ^ n ⟶ 0` is short exact. -/
lemma envelopeShortComplex_shortExact_eval (M : CochainComplex C ℤ) (n : ℤ) :
    ((envelopeShortComplex C M).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (envelopeShortComplex_shortExact C M) n

/-- The map `J(M) ⟶ Q(M)` is an epimorphism in every degree. -/
instance (M : CochainComplex C ℤ) (n : ℤ) : Epi (((injectiveEnvelopeπ C).app M).f n) :=
  (envelopeShortComplex_shortExact_eval C M n).epi_g

/-! ### The enlargement `N(M) = cocone(J(M) ⟶ Q(M))` -/

/-- The functoriality of the enlargement. -/
def enlargementMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    mappingCocone ((injectiveEnvelopeπ C).app M) ⟶
      mappingCocone ((injectiveEnvelopeπ C).app N) :=
  (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map
    (mappingCone.map ((injectiveEnvelopeπ C).app M) ((injectiveEnvelopeπ C).app N)
      ((injectiveEnvelope C).map f) ((injectiveEnvelopeQuotient C).map f)
      ((injectiveEnvelopeπ C).naturality f).symm)

/-- The functor `M ↦ N(M)`, the mapping cocone of `J(M) ⟶ Q(M)`. -/
def injectiveEnlargement : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj M := mappingCocone ((injectiveEnvelopeπ C).app M)
  map := enlargementMap C
  map_id M := by
    simp [enlargementMap, mappingCocone, mappingCone.map_id]
  map_comp f g := by
    simp only [enlargementMap, mappingCocone, Functor.map_comp]
    exact congrArg ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map)
      (mappingCone.map_comp ((injectiveEnvelopeπ C).app _) ((injectiveEnvelopeπ C).app _)
        ((injectiveEnvelopeπ C).app _)
        ((injectiveEnvelope C).map f) ((injectiveEnvelopeQuotient C).map f)
        ((injectiveEnvelopeπ C).naturality f).symm
        ((injectiveEnvelope C).map g) ((injectiveEnvelopeQuotient C).map g)
        ((injectiveEnvelopeπ C).naturality g).symm)

/-- The first component of `enlargementMap C f` is the map `J(f)`. -/
@[reassoc]
lemma enlargementMap_f_fst {M N : CochainComplex C ℤ} (f : M ⟶ N) (n : ℤ) :
    (enlargementMap C f).f n ≫ (mappingCocone.fst ((injectiveEnvelopeπ C).app N)).f n =
      (mappingCocone.fst ((injectiveEnvelopeπ C).app M)).f n ≫
        ((injectiveEnvelope C).map f).f n :=
  shiftedConeMap_f_fst _ _ _ _ _ n

/-- The second component of `enlargementMap C f` is the map `Q(f)`. -/
@[reassoc]
lemma enlargementMap_f_snd {M N : CochainComplex C ℤ} (f : M ⟶ N) (n : ℤ) :
    (enlargementMap C f).f n ≫
        (mappingCocone.snd ((injectiveEnvelopeπ C).app N)).v n (n - 1) (by omega) =
      (mappingCocone.snd ((injectiveEnvelopeπ C).app M)).v n (n - 1) (by omega) ≫
        ((injectiveEnvelopeQuotient C).map f).f (n - 1) :=
  shiftedConeMap_f_snd _ _ _ _ _ n

/-- The canonical morphism `M ⟶ N(M)`. -/
def enlargementι (M : CochainComplex C ℤ) :
    M ⟶ mappingCocone ((injectiveEnvelopeπ C).app M) :=
  mappingCocone.lift ((injectiveEnvelopeπ C).app M) ((injectiveEnvelopeι C).app M) 0 (by
    simp only [HomComplex.δ_zero, zero_add]
    rw [injectiveEnvelopeι_comp_π]
    simp)

/-- The first component of `M ⟶ N(M)` is the map `M ⟶ J(M)`. -/
@[reassoc]
lemma enlargementι_f_fst (M : CochainComplex C ℤ) (n : ℤ) :
    (enlargementι C M).f n ≫ (mappingCocone.fst ((injectiveEnvelopeπ C).app M)).f n =
      ((injectiveEnvelopeι C).app M).f n :=
  mappingCocone.lift_f_fst_f _ _ _ _ n

/-- The second component of `M ⟶ N(M)` is zero. -/
@[reassoc]
lemma enlargementι_f_snd (M : CochainComplex C ℤ) (n : ℤ) :
    (enlargementι C M).f n ≫
      (mappingCocone.snd ((injectiveEnvelopeπ C).app M)).v n (n - 1) (by omega) = 0 :=
  (mappingCocone.lift_f_snd_v _ _ _ _ n (n - 1) (by omega)).trans (by simp)

/-- The natural transformation `𝟭 ⟶ N`. -/
def injectiveEnlargementι : 𝟭 (CochainComplex C ℤ) ⟶ injectiveEnlargement C where
  app M := enlargementι C M
  naturality M N f := by
    refine mappingCocone_hom_ext _ _ _ (fun n => ?_) (fun n => ?_)
    · dsimp only [injectiveEnlargement]
      simpa only [HomologicalComplex.comp_f, Category.assoc, Functor.id_map,
        enlargementι_f_fst, enlargementMap_f_fst, enlargementι_f_fst_assoc] using
        congrArg (fun z : M ⟶ (injectiveEnvelope C).obj N => z.f n)
          ((injectiveEnvelopeι C).naturality f)
    · dsimp only [injectiveEnlargement]
      simp only [HomologicalComplex.comp_f, Category.assoc, Functor.id_map,
        enlargementι_f_snd, enlargementMap_f_snd, enlargementι_f_snd_assoc,
        Limits.zero_comp, Limits.comp_zero]


/-! ### The cokernel of the enlargement and the short exact sequence -/

/-- The projection from the enlargement onto the mapping cocone of the identity of `Q(M)`. -/
def enlargementπ (M : CochainComplex C ℤ) :
    mappingCocone ((injectiveEnvelopeπ C).app M) ⟶
      mappingCocone (𝟙 ((injectiveEnvelopeQuotient C).obj M)) :=
  (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map
    (mappingCone.map ((injectiveEnvelopeπ C).app M)
      (𝟙 ((injectiveEnvelopeQuotient C).obj M)) ((injectiveEnvelopeπ C).app M)
      (𝟙 ((injectiveEnvelopeQuotient C).obj M)) (by simp))

/-- The first component of `enlargementπ C M` is the first component of `N(M)` followed by the
map `J(M) ⟶ Q(M)`. -/
@[reassoc]
lemma enlargementπ_f_fst (M : CochainComplex C ℤ) (n : ℤ) :
    (enlargementπ C M).f n ≫
        (mappingCocone.fst (𝟙 ((injectiveEnvelopeQuotient C).obj M))).f n =
      (mappingCocone.fst ((injectiveEnvelopeπ C).app M)).f n ≫
        ((injectiveEnvelopeπ C).app M).f n :=
  shiftedConeMap_f_fst _ _ _ _ _ n

/-- The second component of `enlargementπ C M` is the second component of `N(M)`. -/
@[reassoc]
lemma enlargementπ_f_snd (M : CochainComplex C ℤ) (n : ℤ) :
    (enlargementπ C M).f n ≫
        (mappingCocone.snd (𝟙 ((injectiveEnvelopeQuotient C).obj M))).v n (n - 1) (by omega) =
      (mappingCocone.snd ((injectiveEnvelopeπ C).app M)).v n (n - 1) (by omega) := by
  have h := shiftedConeMap_f_snd ((injectiveEnvelopeπ C).app M)
    (𝟙 ((injectiveEnvelopeQuotient C).obj M)) ((injectiveEnvelopeπ C).app M)
    (𝟙 ((injectiveEnvelopeQuotient C).obj M)) (by simp) n
  simp only [HomologicalComplex.id_f, Category.comp_id] at h
  exact h

/-- On the first summand, `enlargementπ C M` is `J(M) ^ n ⟶ Q(M) ^ n` followed by the first
inclusion of the mapping cocone of the identity of `Q(M)`. -/
lemma inl_comp_enlargementπ (M : CochainComplex C ℤ) (n : ℤ) :
    (mappingCocone.inl ((injectiveEnvelopeπ C).app M)).v n n (add_zero n) ≫
        (enlargementπ C M).f n =
      ((injectiveEnvelopeπ C).app M).f n ≫
        (mappingCocone.inl (𝟙 ((injectiveEnvelopeQuotient C).obj M))).v n n (add_zero n) := by
  refine mappingCocone_X_hom_ext _ n _ _ ?_ ?_
  · simp [enlargementπ_f_fst]
  · simp [enlargementπ_f_snd]

/-- On the second summand, `enlargementπ C M` is the second inclusion of the mapping cocone of the
identity of `Q(M)`. -/
lemma inr_comp_enlargementπ (M : CochainComplex C ℤ) (n : ℤ) :
    ((mappingCocone.inr ((injectiveEnvelopeπ C).app M)).1).v (n - 1) n (by omega) ≫
        (enlargementπ C M).f n =
      ((mappingCocone.inr (𝟙 ((injectiveEnvelopeQuotient C).obj M))).1).v (n - 1) n (by omega) := by
  refine mappingCocone_X_hom_ext _ n _ _ ?_ ?_
  · simp [enlargementπ_f_fst]
  · simp [enlargementπ_f_snd]

/-- In degree `n`, the map `M ⟶ N(M)` is `M ^ n ⟶ J(M) ^ n` followed by the first inclusion of the
mapping cocone. -/
lemma enlargementι_f_eq (M : CochainComplex C ℤ) (n : ℤ) :
    (enlargementι C M).f n = ((injectiveEnvelopeι C).app M).f n ≫
      (mappingCocone.inl ((injectiveEnvelopeπ C).app M)).v n n (add_zero n) := by
  refine mappingCocone_X_hom_ext _ n _ _ ?_ ?_
  · simp [enlargementι_f_fst]
  · simp [enlargementι_f_snd]

/-- The composite `M ⟶ N(M) ⟶ W(M)` is zero. -/
lemma enlargementι_comp_π (M : CochainComplex C ℤ) :
    enlargementι C M ≫ enlargementπ C M = 0 := by
  refine mappingCocone_hom_ext _ _ _ (fun n => ?_) (fun n => ?_)
  · simp only [HomologicalComplex.comp_f, Category.assoc, enlargementπ_f_fst,
      enlargementι_f_fst_assoc, HomologicalComplex.zero_f, Limits.zero_comp]
    rw [← HomologicalComplex.comp_f, injectiveEnvelopeι_comp_π, HomologicalComplex.zero_f]
  · simp only [HomologicalComplex.comp_f, Category.assoc, enlargementπ_f_snd,
      enlargementι_f_snd, HomologicalComplex.zero_f, Limits.zero_comp]

/-- The short complex `M ⟶ N(M) ⟶ W(M)`, where `W(M)` is the mapping cocone of the identity of
`Q(M)`. -/
def enlargementShortComplex (M : CochainComplex C ℤ) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (enlargementι C M) (enlargementπ C M) (enlargementι_comp_π C M)

/-- In every degree `n`, the sequence `0 ⟶ M ^ n ⟶ N(M) ^ n ⟶ W(M) ^ n ⟶ 0` is short exact. -/
lemma enlargementShortComplex_shortExact_eval (M : CochainComplex C ℤ) (n : ℤ) :
    ((enlargementShortComplex C M).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).ShortExact := by
  have hSES := envelopeShortComplex_shortExact_eval C M n
  have := hSES.epi_g
  have hmono : Mono ((enlargementι C M).f n) := mono_of_mono_fac (enlargementι_f_fst C M n)
  have hepi : Epi ((enlargementπ C M).f n) := by
    refine ⟨fun s t ht => mappingCocone_X_hom_ext' _ n s t ?_ ?_⟩
    · refine (cancel_epi (((injectiveEnvelopeπ C).app M).f n)).1 ?_
      rw [← Category.assoc, ← Category.assoc, ← inl_comp_enlargementπ, Category.assoc,
        Category.assoc, ht]
    · rw [← inr_comp_enlargementπ, Category.assoc, Category.assoc, ht]
  have hexact : ∀ {T : C} (k : (mappingCocone ((injectiveEnvelopeπ C).app M)).X n ⟶ T),
      (enlargementι C M).f n ≫ k = 0 → { l // (enlargementπ C M).f n ≫ l = k } := by
    intro T k hk
    have hk1 : ((injectiveEnvelopeι C).app M).f n ≫
        ((mappingCocone.inl ((injectiveEnvelopeπ C).app M)).v n n (add_zero n) ≫ k) = 0 := by
      rw [← Category.assoc, ← enlargementι_f_eq, hk]
    have hgd : ((injectiveEnvelopeπ C).app M).f n ≫ hSES.exact.desc _ hk1 =
        (mappingCocone.inl ((injectiveEnvelopeπ C).app M)).v n n (add_zero n) ≫ k :=
      hSES.exact.g_desc _ hk1
    set d : ((injectiveEnvelopeQuotient C).obj M).X n ⟶ T := hSES.exact.desc
      ((mappingCocone.inl ((injectiveEnvelopeπ C).app M)).v n n (add_zero n) ≫ k) hk1 with hd
    set l := (mappingCocone.fst (𝟙 ((injectiveEnvelopeQuotient C).obj M))).f n ≫ d +
      (mappingCocone.snd (𝟙 ((injectiveEnvelopeQuotient C).obj M))).v n (n - 1) (by omega) ≫
        (((mappingCocone.inr ((injectiveEnvelopeπ C).app M)).1).v (n - 1) n (by omega) ≫ k)
      with hl
    have e1 : (mappingCocone.inl
        (𝟙 ((injectiveEnvelopeQuotient C).obj M))).v n n (add_zero n) ≫ l = d := by
      have h1 := mappingCocone.inl_v_fst_f (𝟙 ((injectiveEnvelopeQuotient C).obj M)) n
      have h2 := mappingCocone.inl_v_snd_v
        (𝟙 ((injectiveEnvelopeQuotient C).obj M)) n (n - 1) (by omega)
      rw [hl, Preadditive.comp_add, ← Category.assoc _ _ d, h1, Category.id_comp,
        ← Category.assoc, ← Category.assoc, h2, Limits.zero_comp, Limits.zero_comp, add_zero]
    have e2 : ((mappingCocone.inr
          (𝟙 ((injectiveEnvelopeQuotient C).obj M))).1).v (n - 1) n (by omega) ≫ l =
        ((mappingCocone.inr ((injectiveEnvelopeπ C).app M)).1).v (n - 1) n (by omega) ≫ k := by
      have h1 := mappingCocone.inr_v_fst_f
        (𝟙 ((injectiveEnvelopeQuotient C).obj M)) (n - 1) n (by omega)
      have h2 := mappingCocone.inr_v_snd_v
        (𝟙 ((injectiveEnvelopeQuotient C).obj M)) (n - 1) n (by omega)
      rw [hl, Preadditive.comp_add, ← Category.assoc _ _ d, h1, Limits.zero_comp, zero_add,
        ← Category.assoc, h2, Category.id_comp]
    refine ⟨l, mappingCocone_X_hom_ext' _ n _ _ ?_ ?_⟩
    · rw [← Category.assoc, inl_comp_enlargementπ, Category.assoc, e1]
      exact hgd
    · rw [← Category.assoc, inr_comp_enlargementπ, e2]
  have : Epi ((enlargementShortComplex C M).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).g := hepi
  exact { exact := ShortComplex.exact_of_g_is_cokernel _
            (CokernelCofork.IsColimit.ofπ' _ _ (fun k hk => hexact k hk))
          mono_f := hmono
          epi_g := hepi }

/-- The sequence `0 ⟶ M ⟶ N(M) ⟶ W(M) ⟶ 0` is short exact. -/
lemma enlargementShortComplex_shortExact (M : CochainComplex C ℤ) :
    (enlargementShortComplex C M).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (enlargementShortComplex_shortExact_eval C M)

end Construction

/-! ### The statement of Stacks 079N -/

section Statement

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The data and properties of a functorial injective enlargement of cochain complexes. -/
structure FunctorialInjectiveResolution where
  /-- The functorial enlargement of a complex. -/
  functor : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  /-- The natural map from a complex to its enlargement. -/
  inclusion : Functor.id (CochainComplex C ℤ) ⟶ functor
  /-- The inclusion is a monomorphism in every degree. -/
  mono_f : ∀ (M : CochainComplex C ℤ) (n : ℤ), Mono ((inclusion.app M).f n)
  /-- The inclusion is a quasi-isomorphism. -/
  quasiIso : ∀ M : CochainComplex C ℤ, QuasiIso (inclusion.app M)
  /-- In each degree the inclusion factors through an injective subobject of the
  corresponding term of the enlargement. -/
  factors_through_injective_subobject :
    ∀ (M : CochainComplex C ℤ) (n : ℤ),
      ∃ (I : C), Injective I ∧
        ∃ (toI : M.X n ⟶ I) (into : I ⟶ (functor.obj M).X n),
          Mono into ∧ toI ≫ into = (inclusion.app M).f n

/-- A Grothendieck abelian category admits a functorial termwise monomorphic quasi-isomorphism
from every cochain complex to one whose map in each degree factors through an injective
subobject. -/
@[stacks 079N]
theorem exists_functorialInjectiveResolution [IsGrothendieckAbelian.{w} C] :
    Nonempty (FunctorialInjectiveResolution C) :=
  ⟨{ functor := injectiveEnlargement C
     inclusion := injectiveEnlargementι C
     mono_f := fun M n => mono_of_mono_fac (enlargementι_f_fst C M n)
     quasiIso := fun M => quasiIso_of_shortExact_of_acyclic_X₃
       (enlargementShortComplex_shortExact C M) (acyclic_mappingCocone_id _)
     factors_through_injective_subobject := fun M n =>
       ⟨((injectiveEnvelope C).obj M).X n, inferInstance,
         ((injectiveEnvelopeι C).app M).f n,
         (mappingCocone.inl ((injectiveEnvelopeπ C).app M)).v n n (add_zero n),
         mono_of_mono_fac (mappingCocone.inl_v_fst_f ((injectiveEnvelopeπ C).app M) n),
         (enlargementι_f_eq C M n).symm⟩ }⟩

end Statement

end Stacks.Injectives
