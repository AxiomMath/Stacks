module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Preadditive.Injective.GrothendieckFunctorial
public import StacksFrontier.Homology.Injectives.Spaltenstein.FunctorialResolution

open Stacks.Injectives.KInjectiveResolution

/-!
# Functorial injective enlargement of unbounded complexes

In a Grothendieck abelian category every unbounded cochain complex admits, functorially, a
termwise monomorphic quasi-isomorphism into a complex whose map in each degree factors
through an injective subobject ([Stacks, Tag 079N]).

## Main results

* `Stacks.Injectives.FunctorialEnlargement.exists_functorialInjectiveResolution` is [Stacks, Tag
  079N]: a
  `Stacks.Injectives.KInjectiveResolution.FunctorialInjectiveResolution C` exists.
* `Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective` is [Stacks, Tag
  079P] with no
  hypotheses left standing: functorial K-injective resolutions exist.

## Implementation notes

The construction is the one the source uses.  Write `J` for the functorial injective
embedding of objects supplied by [Stacks, Tag 0139]
  (`Stacks.Injectives.FunctorialEmbedding.embedding`, with its
natural monomorphism `Stacks.Injectives.FunctorialEmbedding.unit`).

* `injComplex` is the degreewise injective enlargement of a complex `M`, with terms
  `J (Mⁿ) ⊞ J (Mⁿ⁺¹)` and differential `(a, b) ↦ (b, 0)`.  The inclusion of `M` has
  components `biprod.lift ηₘ (d ≫ η)`, which is a chain map and a degreewise
  monomorphism.  Note that no additivity of `J` is needed: the differential does not
  involve `J` on morphisms, so `J` need not even preserve zero morphisms.  This is why the
  bounded-below normalisation of [Stacks, Tag 0141] (replacing `J A` by `Ker (J A ⟶ J 0)`)
  is not repeated here.
* `injQuotientFunctor` is the cokernel of that inclusion, taken in `CochainComplex C ℤ`,
  and `injResolutionFunctor M` is the mapping cocone of the quotient projection
  `injComplex M ⟶ injQuotient M`, i.e. `Cone(J(M) → Q(M))⟦-1⟧`.

The three properties of the inclusion `M ⟶ injResolutionFunctor M` are read off the
mapping cocone's splitting data:

* it is a degreewise monomorphism because the first projection of the cocone splits it
  back onto the degreewise injective enlargement, whose own inclusion is monic;
* in each degree it factors through `(injComplex M)ⁿ`, an injective object (a biproduct of
  two values of `J`), included by the cocone's first inclusion, which is a split
  monomorphism — this is the factorization [Stacks, Tag 079N] asks for, and it is *weaker*
  than termwise injectivity of the enlargement, which is false here;
* it is a quasi-isomorphism because it sits in a short exact sequence whose third term is
  `mappingCocone (𝟙 (Q M))`, the mapping cocone of an identity, hence contractible and so
  acyclic.  Short exactness is checked degreewise: the first projection identifies the
  kernel with the degreewise kernel of the quotient projection, which is the complex
  itself, and epiness holds because the quotient projection is degreewise epi.

Unlike the bounded-below construction of [Stacks, Tag 0141], nothing here totalizes a
double complex, so no convergence hypothesis arises and the result holds for unbounded
complexes.

## References

* [Stacks Project, Tag 079N](https://stacks.math.columbia.edu/tag/079N)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0139](https://stacks.math.columbia.edu/tag/0139)
-/
@[expose] public section

open CategoryTheory Limits ZeroObject

universe w v u

namespace Stacks.Injectives.FunctorialEnlargement

variable (C : Type u) [Category.{v} C] [Abelian C]

section

variable [IsGrothendieckAbelian.{w} C]

omit [IsGrothendieckAbelian.{w} C] in
private lemma quasiIso_of_shortExact_of_acyclic_cokernel
    {A : Type u} [Category.{v} A] [Abelian A]
    {S : ShortComplex (CochainComplex A ℤ)} (hS : S.ShortExact)
    (hX₃ : S.X₃.Acyclic) : QuasiIso S.f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap S.f n) :=
    (hS.homology_exact₁ (n - 1) n (by simp)).mono_g
      ((hX₃ (n - 1)).isZero_homology.eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap S.f n) :=
    (hS.homology_exact₂ n).epi_f ((hX₃ n).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _


private noncomputable def injComplexD (M : CochainComplex C ℤ) (i j : ℤ) :=
  if h : i + 1 = j then by
    subst j
    exact biprod.desc
      (0 : (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X i) ⟶
        (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X (i + 1)) ⊞
          (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X (i + 1 + 1)))
      (biprod.inl : (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X (i + 1)) ⟶
        (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X (i + 1)) ⊞
          (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X (i + 1 + 1)))
    else (0 : (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X i) ⊞
      (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X (i + 1)) ⟶
      (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X j) ⊞
        (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X (j + 1)))

private noncomputable def injComplex (M : CochainComplex C ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.mk
    (fun n => (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X n) ⊞
      (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X (n + 1)))
    (injComplexD C M)
    (by intro i j hij; simp only [ComplexShape.up_Rel] at hij; simp [injComplexD, hij])
    (by
      intro i j k hij hjk
      simp only [ComplexShape.up_Rel] at hij hjk
      subst j
      subst k
      apply biprod.hom_ext' <;> simp [injComplexD])

private noncomputable def injComplexMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    injComplex C M ⟶ injComplex C N where
  f n := biprod.map ((Stacks.Injectives.FunctorialEmbedding.embedding C).map (f.f n))
    ((Stacks.Injectives.FunctorialEmbedding.embedding C).map (f.f (n + 1)))
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst j
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp [injComplex, injComplexD]
    · simp [injComplex, injComplexD]

private noncomputable def injComplexFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := injComplex C
  map := injComplexMap C
  map_id M := by
    ext n
    dsimp [injComplexMap, injComplex]
    apply biprod.hom_ext'
    · simp [biprod.inl_map]
    · simp [biprod.inr_map]
  map_comp f g := by
    ext n
    dsimp [injComplexMap, injComplex]
    apply biprod.hom_ext'
    · simp [biprod.inl_map_assoc, Functor.map_comp]
    · simp [biprod.inr_map_assoc, Functor.map_comp]

private noncomputable def injComplexInclusion (M : CochainComplex C ℤ) :
    M ⟶ injComplex C M where
  f n := by
    change M.X n ⟶ (injComplex C M).X n
    exact biprod.lift ((Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X n))
      (M.d n (n + 1) ≫ (Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X (n + 1)))
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst j
    apply biprod.hom_ext
    · simp [injComplex, injComplexD, Category.assoc]
    · simp [injComplex, injComplexD, Category.assoc]

private noncomputable def injComplexUnit :
    𝟭 (CochainComplex C ℤ) ⟶ injComplexFunctor C where
  app M := injComplexInclusion C M
  naturality M N f := by
    ext n
    dsimp [injComplexInclusion, injComplexMap, injComplexFunctor, Functor.id_map]
    apply biprod.hom_ext
    · calc
        (f.f n ≫ biprod.lift ((Stacks.Injectives.FunctorialEmbedding.unit C).app (N.X n))
          (N.d n (n + 1) ≫ (Stacks.Injectives.FunctorialEmbedding.unit C).app (N.X (n + 1)))) ≫
            biprod.fst =
            f.f n ≫ (Stacks.Injectives.FunctorialEmbedding.unit C).app (N.X n) := by simp
        _ = (Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X n) ≫
          (Stacks.Injectives.FunctorialEmbedding.embedding C).map (f.f n) :=
          (Stacks.Injectives.FunctorialEmbedding.unit C).naturality (f.f n)
        _ = (biprod.lift ((Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X n))
          (M.d n (n + 1) ≫ (Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X (n + 1))) ≫
            biprod.map ((Stacks.Injectives.FunctorialEmbedding.embedding C).map (f.f n))
              ((Stacks.Injectives.FunctorialEmbedding.embedding C).map (f.f (n + 1)))) ≫
              biprod.fst := by simp
    · calc
        (f.f n ≫ biprod.lift ((Stacks.Injectives.FunctorialEmbedding.unit C).app (N.X n))
          (N.d n (n + 1) ≫ (Stacks.Injectives.FunctorialEmbedding.unit C).app (N.X (n + 1)))) ≫
            biprod.snd =
            f.f n ≫ N.d n (n + 1) ≫ (Stacks.Injectives.FunctorialEmbedding.unit C).app (N.X (n + 1))
              := by
              simp [Category.assoc]
        _ = M.d n (n + 1) ≫ f.f (n + 1) ≫ (Stacks.Injectives.FunctorialEmbedding.unit C).app (N.X (n
          + 1)) := by
          rw [← Category.assoc, HomologicalComplex.Hom.comm f n (n + 1), Category.assoc]
        _ = M.d n (n + 1) ≫ ((Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X (n + 1)) ≫
            (Stacks.Injectives.FunctorialEmbedding.embedding C).map (f.f (n + 1))) := by
          simpa only [Functor.id_map] using congrArg
            (fun z => M.d n (n + 1) ≫ z) ((Stacks.Injectives.FunctorialEmbedding.unit C).naturality
              (f.f (n + 1)))
        _ = (biprod.lift ((Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X n))
          (M.d n (n + 1) ≫ (Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X (n + 1))) ≫
            biprod.map ((Stacks.Injectives.FunctorialEmbedding.embedding C).map (f.f n))
              ((Stacks.Injectives.FunctorialEmbedding.embedding C).map (f.f (n + 1)))) ≫
              biprod.snd := by simp [Category.assoc]

private noncomputable def injQuotientMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    cokernel ((injComplexUnit C).app M) ⟶ cokernel ((injComplexUnit C).app N) :=
  cokernel.map ((injComplexUnit C).app M) ((injComplexUnit C).app N) f
    ((injComplexFunctor C).map f) ((injComplexUnit C).naturality f).symm

private noncomputable def injQuotientFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj M := cokernel ((injComplexUnit C).app M)
  map := injQuotientMap C
  map_id M := by
    simp [injQuotientMap, cokernel.map_id]
  map_comp f g := by
    rw [← cancel_epi (cokernel.π ((injComplexUnit C).app _))]
    simp [injQuotientMap, Category.assoc]

private noncomputable def injQuotientProjection : injComplexFunctor C ⟶ injQuotientFunctor C where
  app M := cokernel.π ((injComplexUnit C).app M)
  naturality M N f := by
    simp [injQuotientFunctor, injQuotientMap]

private lemma injComplexUnit_quotient_zero (M : CochainComplex C ℤ) :
    (injComplexUnit C).app M ≫ (injQuotientProjection C).app M = 0 := by
  change (injComplexUnit C).app M ≫ cokernel.π ((injComplexUnit C).app M) = 0
  exact cokernel.condition _

omit [IsGrothendieckAbelian.{w} C] in
private lemma injMappingConeMap_fst
    {J₁ Q₁ J₂ Q₂ : CochainComplex C ℤ} (p₁ : J₁ ⟶ Q₁) (p₂ : J₂ ⟶ Q₂)
    (a : J₁ ⟶ J₂) (b : Q₁ ⟶ Q₂) (comm : p₁ ≫ b = a ≫ p₂) (n m : ℤ) (hnm : n + 1 = m) :
    (CochainComplex.mappingCone.map p₁ p₂ a b comm).f n ≫
        (CochainComplex.mappingCone.fst p₂).1.v n m hnm =
      (CochainComplex.mappingCone.fst p₁).1.v n m hnm ≫ a.f m := by
  subst hnm
  simp [CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc_f,
    Category.assoc]

omit [IsGrothendieckAbelian.{w} C] in
private lemma injMappingConeMap_snd
    {J₁ Q₁ J₂ Q₂ : CochainComplex C ℤ} (p₁ : J₁ ⟶ Q₁) (p₂ : J₂ ⟶ Q₂)
    (a : J₁ ⟶ J₂) (b : Q₁ ⟶ Q₂) (comm : p₁ ≫ b = a ≫ p₂) (n : ℤ) :
    (CochainComplex.mappingCone.map p₁ p₂ a b comm).f n ≫
        (CochainComplex.mappingCone.snd p₂).v n n (by omega) =
      (CochainComplex.mappingCone.snd p₁).v n n (by omega) ≫ b.f n := by
  simp [CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc_f,
    Category.assoc]

/-- The mapping cocone of a commutative square, as a map of mapping cocones: the shift by
`-1` of the induced map of mapping cones. -/
private noncomputable def mappingCoconeMap {J₁ Q₁ J₂ Q₂ : CochainComplex C ℤ}
    (p₁ : J₁ ⟶ Q₁) (p₂ : J₂ ⟶ Q₂) (a : J₁ ⟶ J₂) (b : Q₁ ⟶ Q₂)
    (comm : p₁ ≫ b = a ≫ p₂) :
    CochainComplex.mappingCocone p₁ ⟶ CochainComplex.mappingCocone p₂ :=
  (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1)).map
    (CochainComplex.mappingCone.map p₁ p₂ a b comm)

private noncomputable def injResolutionMap {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    CochainComplex.mappingCocone ((injQuotientProjection C).app M) ⟶
      CochainComplex.mappingCocone ((injQuotientProjection C).app N) :=
  mappingCoconeMap C _ _ ((injComplexFunctor C).map f) ((injQuotientFunctor C).map f)
    ((injQuotientProjection C).naturality f).symm

private noncomputable def injResolutionFunctor :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj M := CochainComplex.mappingCocone ((injQuotientProjection C).app M)
  map := injResolutionMap C
  map_id M := by
    simp [injResolutionMap, mappingCoconeMap, CochainComplex.mappingCocone,
      CochainComplex.mappingCone.map_id]
  map_comp f g := by
    simp only [injResolutionMap, mappingCoconeMap, CochainComplex.mappingCocone,
      Functor.map_comp]
    exact congrArg ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1)).map)
      (CochainComplex.mappingCone.map_comp
        ((injQuotientProjection C).app _) ((injQuotientProjection C).app _)
        ((injQuotientProjection C).app _)
        ((injComplexFunctor C).map f) ((injQuotientFunctor C).map f)
        ((injQuotientProjection C).naturality f).symm
        ((injComplexFunctor C).map g) ((injQuotientFunctor C).map g)
        ((injQuotientProjection C).naturality g).symm)

private noncomputable def injResolutionInclusion (M : CochainComplex C ℤ) :
  M ⟶ CochainComplex.mappingCocone ((injQuotientProjection C).app M) :=
  CochainComplex.mappingCocone.lift ((injQuotientProjection C).app M)
    ((injComplexUnit C).app M) 0 (by
      simp only [CochainComplex.HomComplex.δ_zero, zero_add]
      change CochainComplex.HomComplex.Cochain.ofHom
        ((injComplexUnit C).app M ≫ (injQuotientProjection C).app M) = 0
      rw [injComplexUnit_quotient_zero]
      simp)

omit [IsGrothendieckAbelian.{w} C] in
private lemma injMappingCoconeFstShift {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber φ] (n : ℤ) :
    (CochainComplex.mappingCocone.fst φ).f n =
      ((CochainComplex.mappingCone φ).shiftFunctorObjXIso
        (-1) n (n - 1) (by omega)).hom ≫
        (CochainComplex.mappingCone.fst φ).1.v (n - 1) n (by omega) := by
  dsimp [CochainComplex.mappingCocone.fst]
  rw [CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cocycle.leftShift_coe,
    (CochainComplex.mappingCone.fst φ).1.leftShift_v
      (-1) 0 (by omega) n n (by omega) (n - 1) (by omega)]
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  all_goals rfl

omit [IsGrothendieckAbelian.{w} C] in
private lemma injMappingCoconeSndShift {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber φ] (n : ℤ) :
    (CochainComplex.mappingCocone.snd φ).v n (n - 1) (by omega) =
      ((CochainComplex.mappingCone φ).shiftFunctorObjXIso
        (-1) n (n - 1) (by omega)).hom ≫
        (CochainComplex.mappingCone.snd φ).v (n - 1) (n - 1) (by omega) := by
  dsimp [CochainComplex.mappingCocone.snd]
  change ((CochainComplex.mappingCone.snd φ).leftShift (-1) (-1) (by omega)).v
    n (n - 1) (by omega) = _
  rw [(CochainComplex.mappingCone.snd φ).leftShift_v
      (-1) (-1) (by omega) n (n - 1) (by omega) (n - 1) (by omega)]
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Int.negOnePow_even 2 ⟨1, rfl⟩]

private lemma injResolutionInclusion_fst (M : CochainComplex C ℤ) (n : ℤ) :
    (injResolutionInclusion C M).f n ≫
        (CochainComplex.mappingCocone.fst ((injQuotientProjection C).app M)).f n =
      ((injComplexUnit C).app M).f n := by
  change (CochainComplex.mappingCocone.lift
      ((injQuotientProjection C).app M) ((injComplexUnit C).app M) 0 _).f n ≫
      (CochainComplex.mappingCocone.fst ((injQuotientProjection C).app M)).f n =
    ((injComplexUnit C).app M).f n
  exact CochainComplex.mappingCocone.lift_f_fst_f _ _ _ _ n

private lemma injResolutionInclusion_snd (M : CochainComplex C ℤ) (n : ℤ) :
    (injResolutionInclusion C M).f n ≫
        (CochainComplex.mappingCocone.snd ((injQuotientProjection C).app M)).v
          n (n - 1) (by omega) = 0 := by
  change (CochainComplex.mappingCocone.lift
      ((injQuotientProjection C).app M) ((injComplexUnit C).app M) 0 _).f n ≫
      (CochainComplex.mappingCocone.snd ((injQuotientProjection C).app M)).v
        n (n - 1) (by omega) = 0
  rw [CochainComplex.mappingCocone.lift_f_snd_v]
  simp

omit [IsGrothendieckAbelian.{w} C] in
/-- The shifted mapping-cone map commutes with the identifications of the shifted terms. -/
private lemma mappingCoconeMap_f_comp_shiftFunctorObjXIso {J₁ Q₁ J₂ Q₂ : CochainComplex C ℤ}
    (p₁ : J₁ ⟶ Q₁) (p₂ : J₂ ⟶ Q₂) (a : J₁ ⟶ J₂) (b : Q₁ ⟶ Q₂)
    (comm : p₁ ≫ b = a ≫ p₂) (n : ℤ) {W : C} (z : (CochainComplex.mappingCone p₂).X (n - 1) ⟶ W) :
    (mappingCoconeMap C p₁ p₂ a b comm).f n ≫
        ((CochainComplex.mappingCone p₂).shiftFunctorObjXIso (-1) n (n - 1) (by omega)).hom ≫ z =
      ((CochainComplex.mappingCone p₁).shiftFunctorObjXIso (-1) n (n - 1) (by omega)).hom ≫
        (CochainComplex.mappingCone.map p₁ p₂ a b comm).f (n - 1) ≫ z := by
  have hn : n + (-1) = n - 1 := by omega
  change ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1)).map
      (CochainComplex.mappingCone.map p₁ p₂ a b comm)).f n ≫
    ((CochainComplex.mappingCone p₂).XIsoOfEq hn).hom ≫ z = _
  rw [CochainComplex.shiftFunctor_map_f', ← Category.assoc,
    HomologicalComplex.XIsoOfEq_hom_naturality, Category.assoc]
  rfl

omit [IsGrothendieckAbelian.{w} C] in
private lemma mappingCoconeMapShift_fst {J₁ Q₁ J₂ Q₂ : CochainComplex C ℤ}
    (p₁ : J₁ ⟶ Q₁) (p₂ : J₂ ⟶ Q₂) (a : J₁ ⟶ J₂) (b : Q₁ ⟶ Q₂)
    (comm : p₁ ≫ b = a ≫ p₂) (n : ℤ) :
    (mappingCoconeMap C p₁ p₂ a b comm).f n ≫
        (CochainComplex.mappingCocone.fst p₂).f n =
    (CochainComplex.mappingCocone.fst p₁).f n ≫
        a.f n := by
  rw [injMappingCoconeFstShift, injMappingCoconeFstShift]
  exact (mappingCoconeMap_f_comp_shiftFunctorObjXIso C p₁ p₂ a b comm n _).trans
    ((congrArg (_ ≫ ·) (injMappingConeMap_fst C p₁ p₂ a b comm (n - 1) n (by omega))).trans
      (Category.assoc _ _ _).symm)

omit [IsGrothendieckAbelian.{w} C] in
private lemma mappingCoconeMapShift_snd {J₁ Q₁ J₂ Q₂ : CochainComplex C ℤ}
    (p₁ : J₁ ⟶ Q₁) (p₂ : J₂ ⟶ Q₂) (a : J₁ ⟶ J₂) (b : Q₁ ⟶ Q₂)
    (comm : p₁ ≫ b = a ≫ p₂) (n : ℤ) :
    (mappingCoconeMap C p₁ p₂ a b comm).f n ≫
        (CochainComplex.mappingCocone.snd p₂).v
          n (n - 1) (by omega) =
      (CochainComplex.mappingCocone.snd p₁).v
          n (n - 1) (by omega) ≫ b.f (n - 1) := by
  rw [injMappingCoconeSndShift, injMappingCoconeSndShift]
  exact (mappingCoconeMap_f_comp_shiftFunctorObjXIso C p₁ p₂ a b comm n _).trans
    ((congrArg (_ ≫ ·) (injMappingConeMap_snd C p₁ p₂ a b comm (n - 1))).trans
      (Category.assoc _ _ _).symm)


/-- The first component of the shifted mapping-cone map, for the naturality square of the
quotient projection. -/
private lemma injResolutionMap_fst_cocone {M N : CochainComplex C ℤ}
    (f : M ⟶ N) (n : ℤ) :
    (injResolutionMap C f).f n ≫
        (CochainComplex.mappingCocone.fst ((injQuotientProjection C).app N)).f n =
    (CochainComplex.mappingCocone.fst ((injQuotientProjection C).app M)).f n ≫
        ((injComplexFunctor C).map f).f n :=
  mappingCoconeMapShift_fst C _ _ _ _ ((injQuotientProjection C).naturality f).symm n

/-- The second component of the shifted mapping-cone map, for the naturality square of the
quotient projection. -/
private lemma injResolutionMap_snd_cocone {M N : CochainComplex C ℤ}
    (f : M ⟶ N) (n : ℤ) :
    (injResolutionMap C f).f n ≫
        (CochainComplex.mappingCocone.snd ((injQuotientProjection C).app N)).v
          n (n - 1) (by omega) =
      (CochainComplex.mappingCocone.snd ((injQuotientProjection C).app M)).v
          n (n - 1) (by omega) ≫ ((injQuotientFunctor C).map f).f (n - 1) :=
  mappingCoconeMapShift_snd C _ _ _ _ ((injQuotientProjection C).naturality f).symm n

omit [IsGrothendieckAbelian.{w} C] in
/-- The two projections of a mapping cocone are jointly monic in each degree. -/
private lemma mappingCocone_hom_ext {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber φ] {Z : C} (n : ℤ)
    (x y : Z ⟶ (CochainComplex.mappingCocone φ).X n)
    (h₁ : x ≫ (CochainComplex.mappingCocone.fst φ).f n =
      y ≫ (CochainComplex.mappingCocone.fst φ).f n)
    (h₂ : x ≫ (CochainComplex.mappingCocone.snd φ).v n (n - 1) (by omega) =
      y ≫ (CochainComplex.mappingCocone.snd φ).v n (n - 1) (by omega)) : x = y := by
  have hid := CochainComplex.mappingCocone.id_X φ n (n - 1) (by omega)
  have key : x ≫ 𝟙 _ = y ≫ 𝟙 _ := by
    rw [← hid, Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
      ← Category.assoc, ← Category.assoc, h₁, h₂]
  simpa using key

private noncomputable def injResolutionUnit :
    𝟭 (CochainComplex C ℤ) ⟶ injResolutionFunctor C where
  app M := injResolutionInclusion C M
  naturality M N f := by
    ext n
    refine mappingCocone_hom_ext C ((injQuotientProjection C).app N) n
      ((f ≫ injResolutionInclusion C N).f n)
      ((injResolutionInclusion C M ≫ injResolutionMap C f).f n) ?_ ?_
    · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
        injResolutionInclusion_fst, injResolutionMap_fst_cocone, ← Category.assoc,
        injResolutionInclusion_fst]
      exact congrArg (fun z : M ⟶ (injComplexFunctor C).obj N => z.f n)
        ((injComplexUnit C).naturality f)
    · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
        injResolutionInclusion_snd, injResolutionMap_snd_cocone, ← Category.assoc,
        injResolutionInclusion_snd]
      simp

/-- The components of the degreewise injective enlargement's inclusion. -/
private lemma injComplexUnit_app_f (M : CochainComplex C ℤ) (n : ℤ) :
    ((injComplexUnit C).app M).f n =
      biprod.lift ((Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X n))
        (M.d n (n + 1) ≫ (Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X (n + 1))) := rfl

/-- The inclusion into the degreewise injective enlargement is monic in each degree. -/
private lemma mono_injComplexUnit_app_f (M : CochainComplex C ℤ) (n : ℤ) :
    Mono (((injComplexUnit C).app M).f n) := by
  have : Mono ((Stacks.Injectives.FunctorialEmbedding.unit C).app (M.X n)) :=
    Stacks.Injectives.FunctorialEmbedding.mono_unit_app C _
  rw [injComplexUnit_app_f]
  exact mono_of_mono_fac (biprod.lift_fst _ _)

/-- Every term of the degreewise injective enlargement is an injective object. -/
private lemma injective_injComplex_X (M : CochainComplex C ℤ) (n : ℤ) :
    Injective ((injComplex C M).X n) := by
  have : Injective ((Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X n)) :=
    Stacks.Injectives.FunctorialEmbedding.injective_embedding_obj C _
  have : Injective ((Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X (n + 1))) :=
    Stacks.Injectives.FunctorialEmbedding.injective_embedding_obj C _
  change Injective ((Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X n) ⊞
    (Stacks.Injectives.FunctorialEmbedding.embedding C).obj (M.X (n + 1)))
  infer_instance

/-- The left inclusion of the enlargement into the mapping cocone is monic. -/
private lemma mono_injResolutionInl (M : CochainComplex C ℤ) (n : ℤ) :
    Mono ((CochainComplex.mappingCocone.inl ((injQuotientProjection C).app M)).v n n
      (add_zero n)) :=
  mono_of_mono_fac (CochainComplex.mappingCocone.inl_v_fst_f _ n)

/-- The inclusion into the mapping cocone is monic in each degree: it is split by the
first projection onto the degreewise injective enlargement, which is itself monic. -/
private lemma mono_injResolutionInclusion_f (M : CochainComplex C ℤ) (n : ℤ) :
    Mono ((injResolutionInclusion C M).f n) := by
  have := mono_injComplexUnit_app_f C M n
  exact mono_of_mono_fac (injResolutionInclusion_fst C M n)

/-- In each degree the inclusion into the mapping cocone factors through the term of the
degreewise injective enlargement, which is an injective object included by a split
monomorphism.  This is the degreewise factorization asked for by Tag 079N. -/
private lemma injResolutionInclusion_factors (M : CochainComplex C ℤ) (n : ℤ) :
    ((injComplexUnit C).app M).f n ≫
        (CochainComplex.mappingCocone.inl ((injQuotientProjection C).app M)).v n n
          (add_zero n) =
      (injResolutionInclusion C M).f n := by
  refine mappingCocone_hom_ext C ((injQuotientProjection C).app M) n _ _ ?_ ?_
  · rw [Category.assoc, CochainComplex.mappingCocone.inl_v_fst_f, injResolutionInclusion_fst]
    simp
  · rw [Category.assoc, CochainComplex.mappingCocone.inl_v_snd_v _ n (n - 1) (by omega),
      injResolutionInclusion_snd]
    simp


omit [IsGrothendieckAbelian.{w} C] in
/-- A shift of an acyclic complex is acyclic. -/
private theorem acyclic_shift {K : CochainComplex C ℤ} (hK : K.Acyclic) (a : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) a).obj K).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact IsZero.of_iso
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hK (a + i)))
    ((CochainComplex.ShiftSequence.shiftIso C a i (a + i) rfl).app K)

omit [IsGrothendieckAbelian.{w} C] in
/-- The two inclusions of a mapping cocone are jointly epic in each degree. -/
private lemma mappingCocone_hom_ext_from {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber φ] {Z : C} (n : ℤ)
    (u v : (CochainComplex.mappingCocone φ).X n ⟶ Z)
    (h₁ : (CochainComplex.mappingCocone.inl φ).v n n (add_zero n) ≫ u =
      (CochainComplex.mappingCocone.inl φ).v n n (add_zero n) ≫ v)
    (h₂ : ((CochainComplex.mappingCocone.inr φ).1).v (n - 1) n (by omega) ≫ u =
      ((CochainComplex.mappingCocone.inr φ).1).v (n - 1) n (by omega) ≫ v) : u = v := by
  have hid := CochainComplex.mappingCocone.id_X φ n (n - 1) (by omega)
  have key : 𝟙 _ ≫ u = 𝟙 _ ≫ v := by
    rw [← hid, Preadditive.add_comp, Preadditive.add_comp, Category.assoc, Category.assoc,
      Category.assoc, Category.assoc, h₁, h₂]
  simpa using key

variable (M : CochainComplex C ℤ)

/-- The canonical short exact sequence of a complex, its degreewise injective enlargement
and the quotient. -/
private lemma shortExact_injComplex :
    (ShortComplex.mk ((injComplexUnit C).app M) ((injQuotientProjection C).app M)
      (injComplexUnit_quotient_zero C M)).ShortExact := by
  have : Mono ((injComplexUnit C).app M) :=
    HomologicalComplex.mono_of_mono_f _ (mono_injComplexUnit_app_f C M)
  exact
    { mono_f := inferInstance
      epi_g := by
        change Epi (cokernel.π ((injComplexUnit C).app M))
        infer_instance
      exact := ShortComplex.exact_cokernel _ }

/-- The same short exact sequence read off in a single degree. -/
private lemma shortExact_injComplex_X (n : ℤ) :
    (ShortComplex.mk (((injComplexUnit C).app M).f n) (((injQuotientProjection C).app M).f n)
      (by rw [← HomologicalComplex.comp_f, injComplexUnit_quotient_zero]; simp)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 (shortExact_injComplex C M) n

/-- The third term of the short exact sequence computing the mapping cocone: the mapping
cocone of the identity of the quotient, which is contractible. -/
private noncomputable abbrev injResolutionCoker : CochainComplex C ℤ :=
  CochainComplex.mappingCocone (𝟙 ((injQuotientFunctor C).obj M))

/-- The projection of the mapping cocone onto the contractible third term, induced by the
square comparing the quotient projection with the identity of the quotient. -/
private noncomputable def injResolutionProj :
    CochainComplex.mappingCocone ((injQuotientProjection C).app M) ⟶ injResolutionCoker C M :=
  mappingCoconeMap C ((injQuotientProjection C).app M) (𝟙 _)
    ((injQuotientProjection C).app M) (𝟙 _) (by simp)

private lemma injResolutionProj_fst (n : ℤ) :
    (injResolutionProj C M).f n ≫
        (CochainComplex.mappingCocone.fst (𝟙 ((injQuotientFunctor C).obj M))).f n =
      (CochainComplex.mappingCocone.fst ((injQuotientProjection C).app M)).f n ≫
        ((injQuotientProjection C).app M).f n :=
  mappingCoconeMapShift_fst C _ _ _ _ _ n

private lemma injResolutionProj_snd (n : ℤ) :
    (injResolutionProj C M).f n ≫
        (CochainComplex.mappingCocone.snd (𝟙 ((injQuotientFunctor C).obj M))).v n (n - 1)
          (by omega) =
      (CochainComplex.mappingCocone.snd ((injQuotientProjection C).app M)).v n (n - 1)
        (by omega) := by
  have h := mappingCoconeMapShift_snd C ((injQuotientProjection C).app M) (𝟙 _)
    ((injQuotientProjection C).app M) (𝟙 _) (by simp) n
  simp only [HomologicalComplex.id_f, Category.comp_id] at h
  exact h

/-- The projection onto the contractible third term carries the first inclusion of the
mapping cocone to the quotient projection. -/
private lemma injResolutionProj_inl (n : ℤ) :
    (CochainComplex.mappingCocone.inl ((injQuotientProjection C).app M)).v n n (add_zero n) ≫
        (injResolutionProj C M).f n =
      ((injQuotientProjection C).app M).f n ≫
        (CochainComplex.mappingCocone.inl (𝟙 ((injQuotientFunctor C).obj M))).v n n
          (add_zero n) := by
  refine mappingCocone_hom_ext C (𝟙 ((injQuotientFunctor C).obj M)) n _ _ ?_ ?_
  · simp [injResolutionProj_fst]
  · simp [injResolutionProj_snd]

/-- The projection onto the contractible third term is the identity on the second
inclusion of the mapping cocone. -/
private lemma injResolutionProj_inr (n : ℤ) :
    ((CochainComplex.mappingCocone.inr ((injQuotientProjection C).app M)).1).v (n - 1) n
          (by omega) ≫ (injResolutionProj C M).f n =
      ((CochainComplex.mappingCocone.inr (𝟙 ((injQuotientFunctor C).obj M))).1).v (n - 1) n
        (by omega) := by
  refine mappingCocone_hom_ext C (𝟙 ((injQuotientFunctor C).obj M)) n _ _ ?_ ?_
  · simp [injResolutionProj_fst]
  · simp [injResolutionProj_snd]

/-- The inclusion of the complex into its mapping cocone is killed by the projection onto
the contractible third term. -/
private lemma injResolutionInclusion_comp_proj :
    injResolutionInclusion C M ≫ injResolutionProj C M = 0 := by
  ext n
  refine mappingCocone_hom_ext C (𝟙 ((injQuotientFunctor C).obj M)) n _ _ ?_ ?_
  · rw [HomologicalComplex.comp_f, Category.assoc, injResolutionProj_fst,
      ← Category.assoc, injResolutionInclusion_fst, ← HomologicalComplex.comp_f,
      injComplexUnit_quotient_zero]
    simp
  · rw [HomologicalComplex.comp_f, Category.assoc, injResolutionProj_snd,
      injResolutionInclusion_snd]
    simp

/-- The projection onto the contractible third term is epi in each degree: a map out of it
is killed on the first inclusion because the quotient projection is degreewise epi, and on
the second inclusion because the projection is the identity there. -/
private lemma epi_injResolutionProj_f (n : ℤ) : Epi ((injResolutionProj C M).f n) := by
  have hg : Epi (((injQuotientProjection C).app M).f n) :=
    (shortExact_injComplex_X C M n).epi_g
  rw [Preadditive.epi_iff_cancel_zero]
  intro Z u hu
  refine mappingCocone_hom_ext_from C (𝟙 ((injQuotientFunctor C).obj M)) n u 0 ?_ ?_
  · rw [comp_zero, ← cancel_epi (((injQuotientProjection C).app M).f n), comp_zero,
      ← Category.assoc, ← injResolutionProj_inl, Category.assoc, hu, comp_zero]
  · rw [comp_zero, ← injResolutionProj_inr, Category.assoc, hu, comp_zero]

/-- The inclusion into the mapping cocone is a kernel of the projection onto the
contractible third term, in each degree. -/
private noncomputable def isLimitInjResolutionKernel (n : ℤ) :
    IsLimit (KernelFork.ofι ((injResolutionInclusion C M).f n)
      (show (injResolutionInclusion C M).f n ≫ (injResolutionProj C M).f n = 0 by
        rw [← HomologicalComplex.comp_f, injResolutionInclusion_comp_proj]; simp)) := by
  have := mono_injResolutionInclusion_f C M n
  have : Mono (((injComplexUnit C).app M).f n) := mono_injComplexUnit_app_f C M n
  refine KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => ?_)
  -- the second component of `k` vanishes, and the first lands in the kernel of the
  -- degreewise quotient projection, which is the complex itself
  have hsnd : k ≫ (CochainComplex.mappingCocone.snd
      ((injQuotientProjection C).app M)).v n (n - 1) (by omega) = 0 := by
    rw [← injResolutionProj_snd, ← Category.assoc, hk, zero_comp]
  have hfst : (k ≫ (CochainComplex.mappingCocone.fst
      ((injQuotientProjection C).app M)).f n) ≫
      ((injQuotientProjection C).app M).f n = 0 := by
    rw [Category.assoc, ← injResolutionProj_fst, ← Category.assoc, hk, zero_comp]
  refine ⟨(shortExact_injComplex_X C M n).exact.lift _ hfst, ?_⟩
  refine mappingCocone_hom_ext C ((injQuotientProjection C).app M) n _ _ ?_ ?_
  · rw [Category.assoc, injResolutionInclusion_fst]
    exact (shortExact_injComplex_X C M n).exact.lift_f _ hfst
  · rw [Category.assoc, injResolutionInclusion_snd, comp_zero, hsnd]

/-- The short exact sequence exhibiting the mapping cocone as an extension of the complex
by the contractible third term. -/
private lemma shortExact_injResolution :
    (ShortComplex.mk (injResolutionInclusion C M) (injResolutionProj C M)
      (injResolutionInclusion_comp_proj C M)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  exact
    { mono_f := mono_injResolutionInclusion_f C M n
      epi_g := epi_injResolutionProj_f C M n
      exact := ShortComplex.exact_of_f_is_kernel _ (isLimitInjResolutionKernel C M n) }

/-- The contractible third term is acyclic. -/
private lemma acyclic_injResolutionCoker : (injResolutionCoker C M).Acyclic :=
  acyclic_shift C (Stacks.Injectives.acyclic_of_homotopy_id_zero C _
    (CochainComplex.mappingCone.homotopyToZeroOfId ((injQuotientFunctor C).obj M))) (-1)

/-- **The inclusion of a complex into its functorial injective enlargement is a
quasi-isomorphism.**  It sits in a short exact sequence whose third term is the mapping
cocone of an identity, hence contractible. -/
private lemma quasiIso_injResolutionInclusion : QuasiIso (injResolutionInclusion C M) :=
  quasiIso_of_shortExact_of_acyclic_cokernel (shortExact_injResolution C M)
    (acyclic_injResolutionCoker C M)

/-- **Stacks Project, Tag 079N.**  A Grothendieck abelian category admits a functorial
injective enlargement of unbounded cochain complexes: a functor on `CochainComplex C ℤ`
together with a natural inclusion which is a monomorphism in every degree, a
quasi-isomorphism, and which in each degree factors through an injective subobject of the
corresponding term of the enlargement.

This discharges the hypothesis of [Stacks, Tag 079P], which the tree states relative to
exactly this datum. -/
@[stacks 079N]
theorem exists_functorialInjectiveResolution :
    Nonempty (Stacks.Injectives.KInjectiveResolution.FunctorialInjectiveResolution C) :=
  ⟨{ functor := injResolutionFunctor C
     inclusion := injResolutionUnit C
     mono_f := mono_injResolutionInclusion_f C
     quasiIso := quasiIso_injResolutionInclusion C
     factors_through_injective_subobject := fun M n =>
       ⟨(injComplex C M).X n, injective_injComplex_X C M n,
        ((injComplexUnit C).app M).f n,
        (CochainComplex.mappingCocone.inl ((injQuotientProjection C).app M)).v n n
          (add_zero n),
        mono_injResolutionInl C M n, injResolutionInclusion_factors C M n⟩ }⟩

/-- **Stacks Project, Tag 079P**, unconditionally.  Functorial K-injective resolutions
exist in a Grothendieck abelian category: every complex `M` admits, functorially in `M`, a
termwise monomorphic quasi-isomorphism into a K-injective complex with injective terms.

The tree proves this relative to the Tag 079N datum
(`exists_functorial_quasiIso_isKInjective_of_functorialInjectiveResolution`);
`exists_functorialInjectiveResolution` supplies the datum. -/
@[stacks 079P "existence and functoriality", sga "2 VIII 1.4" "more general"]
theorem exists_functorial_quasiIso_isKInjective :
    Nonempty (Stacks.Injectives.KInjectiveResolution.FunctorialKInjectiveResolution C) :=
  exists_functorial_quasiIso_isKInjective_of_functorialInjectiveResolution C
    (exists_functorialInjectiveResolution C).some

end

end Stacks.Injectives.FunctorialEnlargement
