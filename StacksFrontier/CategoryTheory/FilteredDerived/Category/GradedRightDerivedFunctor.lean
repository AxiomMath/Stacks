module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.RightDerivedFunctor

/-!
# Graded pieces of the filtered right derived functor

Let `T : A ⥤ B` be an additive functor between abelian categories and suppose `A` has enough
injectives. Taking the `p`-th graded piece of the filtered right derived functor of `T` agrees
with the ordinary right derived functor of the `p`-th graded piece: there is a natural
isomorphism of functors `DF⁺(A) ⥤ D⁺(B)` between
`RT ⋙ gr^p` and `gr^p ⋙ RT`. Likewise forgetting the filtration commutes with it: there is a
natural isomorphism `RT ⋙ forget F ≅ forget F ⋙ RT`.

The comparison is built on a complex of filtered injective objects. There the filtration steps
of `T` applied termwise are split monomorphisms, so the image filtration of `T` agrees with the
pointwise image, and `T` preserves the cokernels computing the graded pieces. These two facts
identify the graded piece of the image filtration with `T` of the graded piece, compatibly with
morphisms, hence degreewise on complexes and then in the homotopy category. For `forget F` no
such identification is needed — the underlying object of the image filtration of `T(X)` is
`T(X)` itself — and what is used is that the underlying complex of a complex of filtered
injectives is a complex of injectives, on which the unit of `RT` is invertible.

## Main definitions

* `CategoryTheory.FilteredDerived.imageMapOfMonoIso` and
  `CategoryTheory.FilteredDerived.gradedImageIso`: the identification of the image filtration
  with the pointwise image, and the resulting identification on graded pieces.
* `CategoryTheory.FilteredDerived.gradedImageComplexIso`,
  `CategoryTheory.FilteredDerived.gradedImageHomotopyIso`: the same identification on complexes
  and in the homotopy category of complexes of filtered injectives.

## Main results

* `CategoryTheory.FilteredDerived.filteredRightDerivedFunctorGrPIso`: the natural isomorphism
  expressing commutativity of the square of bounded-below derived categories.
* `CategoryTheory.FilteredDerived.filteredRightDerivedFunctorForgetIso`: the natural isomorphism
  `RT ⋙ forget F ≅ forget F ⋙ RT` of [Stacks, Tag 015V].

## Implementation notes

The graded-piece functor on bounded-below filtered derived categories is
`CochainComplex.FilteredDerivedCategory.liftDFPlus` applied to `FiniteFilteredObject.grP`. The
equation of the source is realised as a natural isomorphism of functors, and the isomorphism
itself is produced rather than merely asserted to exist.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredDerived

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]

/-- On a filtered object whose filtration steps are carried by `G` to monomorphisms, the image
filtration `mapFilteredObject G X` agrees with the filtration `X.mapOfMono G h` cut out by
those monomorphisms themselves. -/
noncomputable def imageMapOfMonoIso (G : A ⥤ B) (X : FilteredObject A ℤᵒᵖ)
    (h : ∀ i, Mono (G.map (X.filtration.ι.app i))) :
    mapFilteredObject G X ≅ X.mapOfMono G h := by
  refine FilteredObject.isoMk (Iso.refl _) (fun i => ?_) (fun i => ?_)
  · cases i with
    | op p =>
      let f := G.map (X.filtration.ι.app (op p))
      letI : Mono f := h (op p)
      have he : imageSubobject f = Subobject.mk f := imageSubobject_mono f
      exact @Subobject.isoOfEqMk B _ _ _ (imageSubobject f) f (h (op p)) he
  · cases i with
    | op p =>
      let f := G.map (X.filtration.ι.app (op p))
      let _ : Mono f := h (op p)
      rw [FilteredObject.mapOfMono_filtration_ι_app]
      dsimp [FilteredObject.mapOfMono, mapFilteredObject]
      simp only [Subobject.isoOfEqMk_hom, Subobject.ofLEMk_comp]
      simp

/-- The functoriality of `FilteredObject.mapOfMono`: a morphism of filtered objects induces a
morphism of the filtrations cut out by the images of the filtration steps. -/
noncomputable def mapOfMonoMap {X Y : FilteredObject A ℤᵒᵖ} (G : A ⥤ B) (f : X ⟶ Y)
    (hX : ∀ i, Mono (G.map (X.filtration.ι.app i)))
    (hY : ∀ i, Mono (G.map (Y.filtration.ι.app i))) :
    X.mapOfMono G hX ⟶ Y.mapOfMono G hY :=
  FilteredObject.homMk (G.map f.hom) (fun i => G.map (f.natTrans.app i)) (by
    intro i
    dsimp [FilteredObject.mapOfMono]
    change G.map (f.natTrans.app i) ≫ G.map (Y.filtration.ι.app i) =
      G.map (X.filtration.ι.app i) ≫ G.map f.hom
    rw [← G.map_comp, ← G.map_comp, f.comm i])

omit [Abelian A] in
/-- `imageMapOfMonoIso` is natural in the filtered object. -/
lemma imageMapOfMonoIso_naturality {X Y : FiniteFilteredObject A} (G : A ⥤ B) (f : X ⟶ Y)
    (hX : ∀ i, Mono (G.map (X.obj.filtration.ι.app i)))
    (hY : ∀ i, Mono (G.map (Y.obj.filtration.ι.app i))) :
    mapFilteredObjectMap G f.hom ≫ (imageMapOfMonoIso G Y.obj hY).hom =
      (imageMapOfMonoIso G X.obj hX).hom ≫ mapOfMonoMap G f.hom hX hY := by
  apply FilteredObject.hom_ext
  · dsimp [imageMapOfMonoIso, mapOfMonoMap, mapFilteredObjectMap]
    change G.map f.hom.hom ≫ 𝟙 _ = 𝟙 _ ≫ G.map f.hom.hom
    simp

/-- An additive functor preserves the cokernel of a monomorphism out of an injective object:
such a monomorphism is split, and a split short exact sequence stays split exact. -/
lemma preservesCokernel_of_injective (T : A ⥤ B) [T.Additive] {X Y : A} (f : X ⟶ Y) [Mono f]
    [Injective X] : PreservesColimit (parallelPair f 0) T := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have hT := (hS.splittingOfInjective.map T).shortExact
  have := hT.epi_g
  exact preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    ((isColimitMapCoconeCoforkEquiv' T (cokernel.condition f)).symm hT.exact.gIsCokernel)

omit [Abelian A] [Abelian B] in
/-- The inclusion of a filtration step with injective source is split, so any functor carries
it to a monomorphism. -/
lemma mono_map_inclusion (T : A ⥤ B) (X : FilteredObject A ℤᵒᵖ)
    (hX : ∀ i, Injective (X.filtration.obj i)) (i : ℤᵒᵖ) :
    Mono (T.map (X.filtration.ι.app i)) := by
  have := hX i
  have : IsSplitMono (X.filtration.ι.app i) :=
    IsSplitMono.mk' ⟨Injective.factorThru (𝟙 _) _, Injective.comp_factorThru _ _⟩
  infer_instance

/-- For a finite filtered object with injective filtration terms, the `p`-th graded piece of
the image filtration of `T` is `T` of the `p`-th graded piece. -/
noncomputable def gradedImageIso (T : A ⥤ B) [T.Additive] (X : FiniteFilteredObject A)
    (hX : ∀ i, Injective (X.obj.filtration.obj i)) (p : ℤ) :
    (FiniteFilteredObject.grP p).obj ((mapFiniteFiltered T).obj X) ≅
      T.obj ((FiniteFilteredObject.grP p).obj X) := by
  have := hX (op (p + 1))
  letI : PreservesColimit
      (parallelPair (X.obj.filtration.step (FilteredObject.succHom p)) 0) T :=
    preservesCokernel_of_injective T _
  let e := (PreservesCokernel.iso T
    (X.obj.filtration.step (FilteredObject.succHom p))).symm
  exact (FilteredObject.gr p).mapIso
      (imageMapOfMonoIso T X.obj (mono_map_inclusion T X.obj hX)) ≪≫ e

/-- For a finite filtered object with injective filtration terms, `T` preserves the cokernel
computing the `p`-th graded piece. -/
private lemma preservesColimit_step_of_injective (T : A ⥤ B) [T.Additive]
    {X : FiniteFilteredObject A} (hX : ∀ i, Injective (X.obj.filtration.obj i)) (p : ℤ) :
    PreservesColimit (parallelPair (X.obj.filtration.step (FilteredObject.succHom p)) 0) T :=
  have := hX (op (p + 1))
  preservesCokernel_of_injective T _

/-- `gradedImageIso` is natural in the finite filtered object. -/
lemma gradedImageIso_naturality (T : A ⥤ B) [T.Additive] {X Y : FiniteFilteredObject A}
    (hX : ∀ i, Injective (X.obj.filtration.obj i))
    (hY : ∀ i, Injective (Y.obj.filtration.obj i)) (p : ℤ) (f : X ⟶ Y) :
    (FiniteFilteredObject.grP p).map ((mapFiniteFiltered T).map f) ≫
        (gradedImageIso T Y hY p).hom =
      (gradedImageIso T X hX p).hom ≫ T.map ((FiniteFilteredObject.grP p).map f) := by
  have := preservesColimit_step_of_injective T hX p
  have := preservesColimit_step_of_injective T hY p
  have hXm : ∀ i, Mono (T.map (X.obj.filtration.ι.app i)) := mono_map_inclusion T X.obj hX
  have hYm : ∀ i, Mono (T.map (Y.obj.filtration.ι.app i)) := mono_map_inclusion T Y.obj hY
  -- The image filtration is naturally the filtration cut out by the mapped inclusions.
  have key : (FilteredObject.gr p).map (mapFilteredObjectMap T f.hom) ≫
        (FilteredObject.gr p).map (imageMapOfMonoIso T Y.obj hYm).hom =
      (FilteredObject.gr p).map (imageMapOfMonoIso T X.obj hXm).hom ≫
        (FilteredObject.gr p).map (mapOfMonoMap T f.hom hXm hYm) := by
    rw [← Functor.map_comp, ← Functor.map_comp, imageMapOfMonoIso_naturality T f hXm hYm]
  -- On that filtration the graded piece is a cokernel of a mapped step, so the comparison
  -- morphisms of `T` are natural.
  have key' : (FilteredObject.gr p).map (mapOfMonoMap T f.hom hXm hYm) ≫
        cokernelComparison (Y.obj.filtration.step (FilteredObject.succHom p)) T =
      cokernelComparison (X.obj.filtration.step (FilteredObject.succHom p)) T ≫
        T.map ((FilteredObject.gr p).map f.hom) :=
    cokernel_map_comp_cokernelComparison
      (X.obj.filtration.step (FilteredObject.succHom p)) T
      (Y.obj.filtration.step (FilteredObject.succHom p))
      (f.hom.natTrans.app (op (p + 1))) (f.hom.natTrans.app (op p))
      (FilteredObject.step_natTrans_app f.hom (FilteredObject.succHom p))
  change (FilteredObject.gr p).map (mapFilteredObjectMap T f.hom) ≫
      ((FilteredObject.gr p).map (imageMapOfMonoIso T Y.obj hYm).hom ≫
        (PreservesCokernel.iso T
          (Y.obj.filtration.step (FilteredObject.succHom p))).inv) =
    ((FilteredObject.gr p).map (imageMapOfMonoIso T X.obj hXm).hom ≫
        (PreservesCokernel.iso T
          (X.obj.filtration.step (FilteredObject.succHom p))).inv) ≫
      T.map ((FilteredObject.gr p).map f.hom)
  rw [PreservesCokernel.iso_inv, PreservesCokernel.iso_inv]
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) key).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) key').trans (Category.assoc _ _ _).symm

/-- Every filtration term of every degree of a bounded-below complex of filtered injective
objects is injective. -/
lemma injective_filtration_term (K : CochainComplex (FiniteFilteredObject A) ℤ)
    (hK : CochainComplex.FilteredDerivedCategory.filteredInjectivePlusC A K) (n : ℤ) (i : ℤᵒᵖ) :
    Injective ((K.X n).obj.filtration.obj i) := by
  let I := (CochainComplex.toFilf.obj K).obj
  have hI : ∀ n, (CochainComplex.evalFil I n).IsFilteredInjective := fun n =>
    (CochainComplex.isFilteredInjective_evalFil_iff I n).2
      ⟨(CochainComplex.toFilf.obj K).property n, fun q =>
        Injective.of_iso
          (HomologicalComplex.Hom.isoApp ((CochainComplex.grIso q).app K) n).symm
          (hK.2 n q)⟩
  exact CochainComplex.injective_filtration_obj_X_of_isFilteredInjective I hI i n

/-- Degreewise, `gradedImageIso` identifies the `p`-th graded piece of the image filtration of
a complex of filtered injectives with `T` of its `p`-th graded piece. -/
noncomputable def gradedImageComplexIso (T : A ⥤ B) [T.Additive]
    (K : CochainComplex (FiniteFilteredObject A) ℤ)
    (hK : CochainComplex.FilteredDerivedCategory.filteredInjectivePlusC A K) (p : ℤ) :
    ((FiniteFilteredObject.grP p).mapHomologicalComplex (.up ℤ)).obj
        (((mapFiniteFiltered T).mapHomologicalComplex (.up ℤ)).obj K) ≅
      (T.mapHomologicalComplex (.up ℤ)).obj
        (((FiniteFilteredObject.grP p).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => gradedImageIso T (K.X n) (injective_filtration_term K hK n) p)
    (fun n m _ => (gradedImageIso_naturality T
      (injective_filtration_term K hK n) (injective_filtration_term K hK m) p (K.d n m)).symm)

/-- `gradedImageComplexIso` is natural in the complex. -/
lemma gradedImageComplexIso_naturality (T : A ⥤ B) [T.Additive]
    {K L : CochainComplex (FiniteFilteredObject A) ℤ}
    (hK : CochainComplex.FilteredDerivedCategory.filteredInjectivePlusC A K)
    (hL : CochainComplex.FilteredDerivedCategory.filteredInjectivePlusC A L) (p : ℤ) (f : K ⟶ L) :
    ((FiniteFilteredObject.grP p).mapHomologicalComplex (.up ℤ)).map
        (((mapFiniteFiltered T).mapHomologicalComplex (.up ℤ)).map f) ≫
        (gradedImageComplexIso T L hL p).hom =
      (gradedImageComplexIso T K hK p).hom ≫ (T.mapHomologicalComplex (.up ℤ)).map
        (((FiniteFilteredObject.grP p).mapHomologicalComplex (.up ℤ)).map f) := by
  ext n
  exact gradedImageIso_naturality T
    (injective_filtration_term K hK n) (injective_filtration_term L hL n) p (f.f n)

/-- An object of `K⁺(Iᶠ)` is represented by a bounded-below complex of filtered injective
objects. -/
lemma filteredInjectivePlus_as
    (X : (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).FullSubcategory) :
    CochainComplex.FilteredDerivedCategory.filteredInjectivePlusC A X.obj.as := by
  obtain ⟨K, hK, he⟩ := (ObjectProperty.strictMap_iff _ _ _).1 X.property
  exact (congrArg (fun Z => Z.as) he) ▸ hK

/-- `gradedImageComplexIso` in the homotopy category: on `K⁺(Iᶠ)`, taking the `p`-th graded
piece of the image filtration of `T` agrees with applying `T` to the `p`-th graded piece. -/
noncomputable def gradedImageHomotopyIso (T : A ⥤ B) [T.Additive] (p : ℤ) :
    (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).ι ⋙
        (mapFiniteFiltered T).mapHomotopyCategory (.up ℤ) ⋙
          (FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ) ≅
      (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).ι ⋙
        (FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ) ⋙
          T.mapHomotopyCategory (.up ℤ) :=
  NatIso.ofComponents
    (fun X => (HomotopyCategory.quotient B (.up ℤ)).mapIso
      (gradedImageComplexIso T X.obj.as (filteredInjectivePlus_as X) p)) (by
      intro X Y f
      obtain ⟨g, hg⟩ := (HomotopyCategory.quotient _ _).map_surjective f.hom
      change _ ≫ (HomotopyCategory.quotient B (.up ℤ)).map _ =
        (HomotopyCategory.quotient B (.up ℤ)).map _ ≫ _
      change ((FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ)).map
          (((mapFiniteFiltered T).mapHomotopyCategory (.up ℤ)).map f.hom) ≫ _ =
        _ ≫ (T.mapHomotopyCategory (.up ℤ)).map
          (((FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ)).map f.hom)
      rw [← hg]
      change (HomotopyCategory.quotient B (.up ℤ)).map _ ≫ _ =
        _ ≫ (HomotopyCategory.quotient B (.up ℤ)).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact (HomotopyCategory.quotient B (.up ℤ)).congr_map
        (gradedImageComplexIso_naturality T _ _ p g))

/-- The functor `Fil^f(A) ⥤ Fil^f(B)` induced by `T` lies over `T`: forgetting the image
filtration of `T(X)` gives back `T` applied to the underlying object of `X`. -/
noncomputable def mapFiniteFilteredCompForgetIso (T : A ⥤ B) [T.Additive] :
    mapFiniteFiltered T ⋙ FiniteFilteredObject.forget ≅ FiniteFilteredObject.forget ⋙ T :=
  Iso.refl _

/-- On the homotopy category, forgetting the image filtration of `T` applied termwise to a
complex of finite filtered objects is `T` applied termwise to the underlying complex. -/
noncomputable def mapHomotopyCategoryForgetIso (T : A ⥤ B) [T.Additive] :
    (mapFiniteFiltered T).mapHomotopyCategory (.up ℤ) ⋙
        FiniteFilteredObject.forget.mapHomotopyCategory (.up ℤ) ≅
      FiniteFilteredObject.forget.mapHomotopyCategory (.up ℤ) ⋙
        T.mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (mapFiniteFilteredCompForgetIso T) (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (FiniteFilteredObject.forget ⋙ T))
      (.up ℤ)).symm

/-- The underlying complex of a bounded-below complex of filtered injective objects has
injective terms: each term is a finite filtered object whose filtration steps are injective,
and its top step is the whole object. -/
lemma injective_forget_X (K : CochainComplex (FiniteFilteredObject A) ℤ)
    (hK : CochainComplex.FilteredDerivedCategory.filteredInjectivePlusC A K) (n : ℤ) :
    Injective (FiniteFilteredObject.forget.obj (K.X n)) := by
  obtain ⟨p, hp⟩ := (K.X n).property.exists_isIso_ι
  exact Injective.of_iso (asIso ((K.X n).obj.filtration.ι.app (op p)))
    (injective_filtration_term K hK n (op p))

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- Taking the `p`-th graded piece commutes with the filtered right derived functor: for an
additive functor `T : A ⥤ B` out of an abelian category with enough injectives, there is a
natural isomorphism `RT ⋙ gr^p ≅ gr^p ⋙ RT` of functors `DF⁺(A) ⥤ D⁺(B)`, i.e.
`gr^p ∘ RT ≅ RT ∘ gr^p`, where the `RT` on the left is the filtered right derived functor and
the one on the right is the right derived functor `D⁺(A) ⥤ D⁺(B)`.

This is the isomorphism of [Stacks, Tag 015U]. There the filtered right derived functor is
`RT = T_ext ∘ j'` ([Stacks, Tag 05U2]), with `j'` a quasi-inverse of the equivalence
`K⁺(Iᶠ) ⥤ DF⁺(A)` of [Stacks, Tag 015Q] and `T_ext` the functor of [Stacks, Tag 05U0],
`T_ext(I) = ⨁ T(I_q)` with `F^p T_ext(I) = ⨁_{q ≥ p} T(I_q)` for a splitting
`I ≅ ⨁ I_q`, `F^p I = ⨁_{q ≥ p} I_q`, of a filtered injective object ([Stacks, Tag 015T]).
Here `filteredRightDerivedFunctor T` is `(toPlus A).inv ⋙ filteredInjectivePlusMapToDerivedPlus T`:
`j'` is `(toPlus A).inv`, and on `K⁺(Iᶠ)` the functor `T` is applied termwise with the
filtration `F^p T(I) = T(F^p I) ⊆ T(I)`. On a filtered injective object each `F^p I ⟶ I` is a
split monomorphism, so `T(F^p I) ⟶ T(I)` is a monomorphism and the image filtration is
`T(F^p I)` itself (`imageMapOfMonoIso`); under a splitting `I ≅ ⨁ I_q` it is
`⨁_{q ≥ p} T(I_q)`, which is `T_ext(I)`. The identity
`gr^p(T_ext(I)) ≅ T(gr^p I)` used by the source is `gradedImageIso`.

See [Stacks Project, Tag 03TE](https://stacks.math.columbia.edu/tag/03TE) and
[Stacks Project, Tag 015U](https://stacks.math.columbia.edu/tag/015U). -/
@[stacks 03TE, stacks 015U "the isomorphism `gr^p ∘ RT ≅ RT ∘ gr^p` of functors \
  `DF⁺(A) ⥤ D⁺(B)`, for `T` additive and `A` with enough injectives, with `RT = T_ext ∘ j'`: \
  `j'` is `(toPlus A).inv` and `T_ext` is `T` applied termwise on `K⁺(Iᶠ)`, \
  `F^p T(I) = T(F^p I)` (`imageMapOfMonoIso`)"]
noncomputable def filteredRightDerivedFunctorGrPIso (T : A ⥤ B) [T.Additive]
    [EnoughInjectives A] (p : ℤ) :
    filteredRightDerivedFunctor T ⋙
        CochainComplex.FilteredDerivedCategory.liftDFPlus (FiniteFilteredObject.grP p)
          (CochainComplex.FilteredDerivedCategory.grP_inverts p) ≅
      CochainComplex.FilteredDerivedCategory.liftDFPlus (FiniteFilteredObject.grP p)
          (CochainComplex.FilteredDerivedCategory.grP_inverts p) ⋙
        T.rightDerivedFunctorPlus := by
  let E := CochainComplex.FilteredDerivedCategory.toPlus A
  let grA := CochainComplex.FilteredDerivedCategory.liftDFPlus
    (FiniteFilteredObject.grP (𝒜 := A) p)
    (CochainComplex.FilteredDerivedCategory.grP_inverts p)
  let grB := CochainComplex.FilteredDerivedCategory.liftDFPlus
    (FiniteFilteredObject.grP (𝒜 := B) p)
    (CochainComplex.FilteredDerivedCategory.grP_inverts p)
  let H : (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).FullSubcategory ⥤
      HomotopyCategory.Plus A :=
    (HomotopyCategory.plus A).lift
      ((CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).ι ⋙
        (FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ))
      (fun X => CochainComplex.FilteredDerivedCategory.plus_mapHomotopyCategory_obj _
        (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus_le_plus _ X.property))
  let eA : E ⋙ grA ≅ H ⋙ DerivedCategory.Plus.Qh :=
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft
        (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).ι
        (Localization.fac _ (CochainComplex.FilteredDerivedCategory.grP_inverts p)
          CochainComplex.FilteredDerivedCategory.Qh))
  let eB : filteredInjectivePlusMapToDerivedPlus T ⋙ grB ≅
      H ⋙ T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft
        ((CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).ι ⋙
          (mapFiniteFiltered T).mapHomotopyCategory (.up ℤ))
        (Localization.fac _ (CochainComplex.FilteredDerivedCategory.grP_inverts p)
          CochainComplex.FilteredDerivedCategory.Qh) ≪≫
        Functor.isoWhiskerRight (gradedImageHomotopyIso T p) DerivedCategory.Qh)
  have hH (X) (n : ℤ) : Injective ((H.obj X).obj.as.X n) :=
    (filteredInjectivePlus_as X).2 n p
  let eT : H ⋙ T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      H ⋙ DerivedCategory.Plus.Qh ⋙ T.rightDerivedFunctorPlus :=
    NatIso.ofComponents
      (fun X => asIso (T.rightDerivedFunctorPlusUnith.app (H.obj X)))
      (fun f => T.rightDerivedFunctorPlusUnith.naturality (H.map f))
  let e : E ⋙ (filteredRightDerivedFunctor T ⋙ grB) ≅ E ⋙ (grA ⋙ T.rightDerivedFunctorPlus) :=
    Functor.isoWhiskerRight (filteredRightDerivedFunctorComparison T) grB ≪≫ eB ≪≫ eT ≪≫
      Functor.isoWhiskerRight eA.symm T.rightDerivedFunctorPlus
  exact (Functor.isoWhiskerRight E.asEquivalence.counitIso
      (filteredRightDerivedFunctor T ⋙ grB)).symm ≪≫
    Functor.isoWhiskerLeft E.inv e ≪≫
    Functor.isoWhiskerRight E.asEquivalence.counitIso (grA ⋙ T.rightDerivedFunctorPlus)

/-- Forgetting the filtration commutes with the filtered right derived functor: for an
additive functor `T : A ⥤ B` out of an abelian category with enough injectives, there is a
natural isomorphism `RT ⋙ forget F ≅ forget F ⋙ RT` of functors `DF⁺(A) ⥤ D⁺(B)`, where the
`RT` on the left is the filtered right derived functor `DF⁺(A) ⥤ DF⁺(B)` and the one on the
right is the right derived functor `D⁺(A) ⥤ D⁺(B)`.

The source assumes `T` left exact; only additivity is used. -/
@[stacks 015V "(forget F) ∘ RT ≅ RT ∘ (forget F) as functors DF⁺(A) ⥤ D⁺(B), for T additive"]
noncomputable def filteredRightDerivedFunctorForgetIso (T : A ⥤ B) [T.Additive]
    [EnoughInjectives A] :
    filteredRightDerivedFunctor T ⋙
        CochainComplex.FilteredDerivedCategory.liftDFPlus FiniteFilteredObject.forget
          CochainComplex.FilteredDerivedCategory.forget_inverts ≅
      CochainComplex.FilteredDerivedCategory.liftDFPlus FiniteFilteredObject.forget
          CochainComplex.FilteredDerivedCategory.forget_inverts ⋙
        T.rightDerivedFunctorPlus := by
  let E := CochainComplex.FilteredDerivedCategory.toPlus A
  let fA := CochainComplex.FilteredDerivedCategory.liftDFPlus
    (FiniteFilteredObject.forget (𝒜 := A))
    CochainComplex.FilteredDerivedCategory.forget_inverts
  let fB := CochainComplex.FilteredDerivedCategory.liftDFPlus
    (FiniteFilteredObject.forget (𝒜 := B))
    CochainComplex.FilteredDerivedCategory.forget_inverts
  let H : (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).FullSubcategory ⥤
      HomotopyCategory.Plus A :=
    (HomotopyCategory.plus A).lift
      ((CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).ι ⋙
        FiniteFilteredObject.forget.mapHomotopyCategory (.up ℤ))
      (fun X => CochainComplex.FilteredDerivedCategory.plus_mapHomotopyCategory_obj _
        (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus_le_plus _ X.property))
  let eA : E ⋙ fA ≅ H ⋙ DerivedCategory.Plus.Qh :=
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft
        (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).ι
        (Localization.fac _ CochainComplex.FilteredDerivedCategory.forget_inverts
          CochainComplex.FilteredDerivedCategory.Qh))
  let eB : filteredInjectivePlusMapToDerivedPlus T ⋙ fB ≅
      H ⋙ T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft
        ((CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).ι ⋙
          (mapFiniteFiltered T).mapHomotopyCategory (.up ℤ))
        (Localization.fac _ CochainComplex.FilteredDerivedCategory.forget_inverts
          CochainComplex.FilteredDerivedCategory.Qh) ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft
            (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).ι
            (mapHomotopyCategoryForgetIso T)) DerivedCategory.Qh)
  have hH (X) (n : ℤ) : Injective ((H.obj X).obj.as.X n) :=
    injective_forget_X X.obj.as (filteredInjectivePlus_as X) n
  let eT : H ⋙ T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      H ⋙ DerivedCategory.Plus.Qh ⋙ T.rightDerivedFunctorPlus :=
    NatIso.ofComponents
      (fun X => asIso (T.rightDerivedFunctorPlusUnith.app (H.obj X)))
      (fun f => T.rightDerivedFunctorPlusUnith.naturality (H.map f))
  let e : E ⋙ (filteredRightDerivedFunctor T ⋙ fB) ≅ E ⋙ (fA ⋙ T.rightDerivedFunctorPlus) :=
    Functor.isoWhiskerRight (filteredRightDerivedFunctorComparison T) fB ≪≫ eB ≪≫ eT ≪≫
      Functor.isoWhiskerRight eA.symm T.rightDerivedFunctorPlus
  exact (Functor.isoWhiskerRight E.asEquivalence.counitIso
      (filteredRightDerivedFunctor T ⋙ fB)).symm ≪≫
    Functor.isoWhiskerLeft E.inv e ≪≫
    Functor.isoWhiskerRight E.asEquivalence.counitIso (fA ⋙ T.rightDerivedFunctorPlus)

end CategoryTheory.FilteredDerived

end
