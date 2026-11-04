module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
import StacksCore.Tactic.StacksAttribute

/-! # The evaluation morphism of derived internal Hom on a ringed site

Let `(C, O)` be a ringed site. Stacks 0A97 asks, for arbitrary objects `K`, `L`, `M` of
`D(Mod(O))`, for a canonical morphism

`RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`

in `D(Mod(O))`, for its computation on K-flat and K-injective representatives in terms of the
evaluation morphism of internal Hom complexes of Stacks 0A92, and for its functoriality in all
three objects.

Both sides are functors of `(K, L, M)`, covariant in `K` and `M` and contravariant in `L`: the
source because `RSheafHom(-, -)` is contravariant in its first variable, the target because the
inner `RSheafHom(K, L)` is contravariant in `K` and sits in the contravariant slot of the outer
one, so the two contravariances cancel. Evaluation is therefore an honest natural
transformation of trifunctors, unlike the composition morphism of Stacks 0A98, which is only
dinatural in its intermediate object.

This file constructs it from a derived internal Hom datum
(`AlgebraicGeometry.RingedSite.DerivedInternalHom`) and a derived tensor product datum
(`Stacks.SheafOfModules.DerivedTensorProduct`, Stacks 06YU), in three steps, following
`StacksDraft.Ch21.Sec34.DerivedCompositionOnASite`.

1. On *complexes*, the evaluation morphism of Stacks 0A92 is transported into the derived
   category along the canonical map `toTensor` from the derived tensor product to the ordinary
   total tensor product of Stacks 0FPH, giving
   `AlgebraicGeometry.RingedSite.homComplexDerivedEvaluation`. No K-flatness is needed, because
   `toTensor` is defined for arbitrary complexes; that is what makes this construction
   choice-free and hence functorial, in contrast to the K-flat resolution that the Stacks proof
   chooses. The K-flat hypothesis reappears only in
   `AlgebraicGeometry.RingedSite.derivedEvaluation_model`, where `toTensor` is identified with
   the K-flat comparison isomorphism.
2. For complexes `K`, `L`, `M` with `L` and `M` K-injective — the *source* `K` is arbitrary,
   since it only ever appears as a tensor factor and as the source of an internal Hom complex —
   the K-injective model comparison of the derived internal Hom turns that into
   `AlgebraicGeometry.RingedSite.derivedEvaluationOnKInjectiveModel`, and the functoriality of
   the complex-level evaluation morphism becomes its three-variable naturality.
3. Every object of `D(Mod(O))` is isomorphic to the class of a K-injective complex, through the
   chosen representative `AlgebraicGeometry.RingedSite.kInjectiveModel`. Transporting step 2
   along those isomorphisms gives
   `AlgebraicGeometry.RingedSite.derivedSheafHomEvaluation` for arbitrary objects, and the
   naturality survives the transport because every morphism of `D(Mod(O))` into the class of a
   K-injective complex is the class of a morphism of complexes.

## Main definitions

* `AlgebraicGeometry.RingedSite.homComplexDerivedEvaluation`: step 1.
* `AlgebraicGeometry.RingedSite.derivedEvaluationOnKInjectiveModel`: step 2.
* `AlgebraicGeometry.RingedSite.derivedSheafHomEvaluation`: step 3, for arbitrary objects and an
  arbitrary derived internal Hom datum.
* `AlgebraicGeometry.RingedSite.derivedEvaluationSourceComparison` and
  `AlgebraicGeometry.RingedSite.derivedEvaluationTargetComparison`: the identifications of the
  source and the target of derived evaluation with the classes of the total tensor complex and
  of the iterated internal Hom complex.
* `AlgebraicGeometry.RingedSite.derivedEvaluation`: **Stacks 0A97**, the evaluation morphism for
  the canonical derived internal Hom and the canonical derived tensor product.

## Main results

* `AlgebraicGeometry.RingedSite.derivedEvaluationOnKInjectiveModel_natural` and
  `AlgebraicGeometry.RingedSite.derivedSheafHomEvaluation_natural`: the three-variable
  functoriality of steps 2 and 3.
* `AlgebraicGeometry.RingedSite.derivedSheafHomEvaluation_eq_onKInjectiveModel`: step 3 agrees
  with step 2 whenever the two targets are already K-injective, i.e. the construction does not
  depend on the chosen representatives.
* `AlgebraicGeometry.RingedSite.derivedEvaluation_model`: **Stacks 0A97**, derived evaluation on
  a K-flat source and K-injective targets is the class of the evaluation morphism of complexes.
* `AlgebraicGeometry.RingedSite.derivedEvaluation_natural`: **Stacks 0A97**, functoriality in
  all three objects.

## Implementation notes

The transport of step 3 is shorter than the corresponding step of Stacks 0A98 precisely because
evaluation is natural rather than dinatural: the composite of the transport maps with their
inverses collapses by two applications of
`AlgebraicGeometry.RingedSite.derivedSheafHomMap_comp`, with no case analysis on which tensor
factor absorbs a morphism.

The middle variable of the transport needs a morphism of complexes `L₁ ⟶ L` rather than
`L ⟶ L₁`, because `L` is contravariant on both sides. That direction is available exactly
because the independence statement assumes `L` itself K-injective, so
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective` applies with `L` as the target.

The universes are the diagonal `RingedSite.{u, u, u}` with the universe `d` of the localization
free, as in every file of the derived internal Hom cluster.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

section HomMapNaturality

variable
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]
  (Hd : DerivedInternalHom.{u, d} X)

/-- **The two routes around the naturality square of the derived internal Hom bifunctor
agree.** The induced map `RSheafHom(A, B) ⟶ RSheafHom(A', B')` may be read by moving the target
first or the source first; this is the naturality of the transformation induced by the
source. -/
lemma derivedSheafHomMap_target_first
    {A A' B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A' ⟶ A) (b : B ⟶ B') :
    derivedSheafHomMap X Hd a b =
      (Hd.hom.obj (op A)).map b ≫ (Hd.hom.map a.op).app B' :=
  ((Hd.hom.map a.op).naturality b).symm

end HomMapNaturality

variable
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable {K K' L L' M M' :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The complex-level identity behind the functoriality of derived evaluation: the
functoriality of Section 17's total tensor product, followed by the comparison with Section
34's spelling and the evaluation morphism of Stacks 0A92, is that comparison followed by
evaluation and the induced map of iterated internal Hom complexes. -/
lemma mapBifunctorMap_comp_evaluationMap (k : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M') :
    HomologicalComplex.mapBifunctorMap (homMap X l m) k
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) ≫
        ((tensorTotalIsoTensorComplex X (sheafHomComplex X L' M').obj K').inv ≫
          evaluationMap X K' L' M') =
      (tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj K).inv ≫
        evaluationMap X K L M ≫ homMap X (homMap X k l) m :=
  (mapBifunctorMap_comp_tensorTotalIso_inv X (homMap X l m) k
      (evaluationMap X K' L' M')).trans
    (congrArg (fun z ↦ (tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj K).inv ≫ z)
      (evaluationMap_natural X k l m))

variable
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)

/-- **Derived evaluation of internal Hom complexes.** The evaluation morphism of internal Hom
complexes of Stacks 0A92, read in the derived category along the canonical map from the derived
tensor product to the ordinary total tensor product. No K-flatness is assumed. -/
def homComplexDerivedEvaluation
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (T.tensor.obj (DerivedCategory.Q.obj (sheafHomComplex X L M).obj)).obj
        (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj
        (sheafHomComplex X (sheafHomComplex X K L).obj M).obj :=
  T.toTensor (sheafHomComplex X L M).obj K ≫
    DerivedCategory.Q.map
      ((tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj K).inv ≫
        evaluationMap X K L M)

/-- **Functoriality of derived evaluation of internal Hom complexes**, in all three complexes
at once. -/
theorem homComplexDerivedEvaluation_natural (k : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M') :
    derivedTensorMap X T (DerivedCategory.Q.map (homMap X l m))
          (DerivedCategory.Q.map k) ≫
        homComplexDerivedEvaluation X T K' L' M' =
      homComplexDerivedEvaluation X T K L M ≫
        DerivedCategory.Q.map (homMap X (homMap X k l) m) := by
  have key : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (homMap X l m) k
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map
          ((tensorTotalIsoTensorComplex X (sheafHomComplex X L' M').obj K').inv ≫
            evaluationMap X K' L' M') =
      DerivedCategory.Q.map
          ((tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj K).inv ≫
            evaluationMap X K L M) ≫
        DerivedCategory.Q.map (homMap X (homMap X k l) m) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Category.assoc]
    exact congrArg DerivedCategory.Q.map (mapBifunctorMap_comp_evaluationMap X k l m)
  dsimp only [homComplexDerivedEvaluation, derivedTensorMap]
  simp only [Category.assoc]
  -- The reassociated naturality of `toTensor` leaves the left-hand side bracketed as
  -- `(a ≫ b) ≫ c`, and the two spellings of the total tensor product agree only
  -- definitionally, so `key` is applied in term position rather than by rewriting.
  rw [reassoc_of% (T.toTensor_naturality (homMap X l m) k)]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z ↦ T.toTensor (sheafHomComplex X L M).obj K ≫ z) key)

section Evaluation

variable (Hd : DerivedInternalHom.{u, d} X)

/-- **Derived evaluation on K-injective targets.** For complexes `K`, `L`, `M` with `L` and `M`
K-injective, the morphism

`RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`

obtained from the evaluation morphism of internal Hom complexes through the K-injective model
comparison of the derived internal Hom. The source complex `K` is arbitrary. -/
def derivedEvaluationOnKInjectiveModel
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [L.IsKInjective] [M.IsKInjective] :
    (T.tensor.obj ((Hd.hom.obj (op (DerivedCategory.Q.obj L))).obj
          (DerivedCategory.Q.obj M))).obj (DerivedCategory.Q.obj K) ⟶
      (Hd.hom.obj (op ((Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj
        (DerivedCategory.Q.obj L)))).obj (DerivedCategory.Q.obj M) :=
  derivedTensorMap X T (Hd.homComparison L M).hom (𝟙 (DerivedCategory.Q.obj K)) ≫
    homComplexDerivedEvaluation X T K L M ≫
    (Hd.homComparison (sheafHomComplex X K L).obj M).inv ≫
    derivedSheafHomMap X Hd (Hd.homComparison K L).hom (𝟙 (DerivedCategory.Q.obj M))

/-- **Functoriality of derived evaluation on K-injective targets**, in all three complexes at
once: covariant in the source and in the target, contravariant in the intermediate complex. -/
theorem derivedEvaluationOnKInjectiveModel_natural (k : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M')
    [L.IsKInjective] [L'.IsKInjective] [M.IsKInjective] [M'.IsKInjective] :
    derivedTensorMap X T (derivedSheafHomMap X Hd (DerivedCategory.Q.map l)
            (DerivedCategory.Q.map m)) (DerivedCategory.Q.map k) ≫
        derivedEvaluationOnKInjectiveModel X T Hd K' L' M' =
      derivedEvaluationOnKInjectiveModel X T Hd K L M ≫
        derivedSheafHomMap X Hd (derivedSheafHomMap X Hd (DerivedCategory.Q.map k)
          (DerivedCategory.Q.map l)) (DerivedCategory.Q.map m) := by
  have hL := derivedSheafHomMap_homComparison X Hd l m
  have hKL := derivedSheafHomMap_homComparison X Hd k l
  have hOut := derivedSheafHomMap_homComparison X Hd (homMap X k l) m
  have src : derivedTensorMap X T (derivedSheafHomMap X Hd (DerivedCategory.Q.map l)
            (DerivedCategory.Q.map m)) (DerivedCategory.Q.map k) ≫
        derivedTensorMap X T (Hd.homComparison L' M').hom
          (𝟙 (DerivedCategory.Q.obj K')) =
      derivedTensorMap X T (Hd.homComparison L M).hom (𝟙 (DerivedCategory.Q.obj K)) ≫
        derivedTensorMap X T (DerivedCategory.Q.map (homMap X l m))
          (DerivedCategory.Q.map k) := by
    rw [derivedTensorMap_comp, derivedTensorMap_comp, hL, Category.comp_id, Category.id_comp]
  have e₁ : derivedSheafHomMap X Hd (Hd.homComparison K L).hom
            (𝟙 (DerivedCategory.Q.obj M)) ≫
          derivedSheafHomMap X Hd (derivedSheafHomMap X Hd (DerivedCategory.Q.map k)
            (DerivedCategory.Q.map l)) (DerivedCategory.Q.map m) =
        derivedSheafHomMap X Hd (DerivedCategory.Q.map (homMap X k l))
            (DerivedCategory.Q.map m) ≫
          derivedSheafHomMap X Hd (Hd.homComparison K' L').hom
            (𝟙 (DerivedCategory.Q.obj M')) := by
    rw [derivedSheafHomMap_comp, derivedSheafHomMap_comp, hKL, Category.id_comp,
      Category.comp_id]
  have e₂ : (Hd.homComparison (sheafHomComplex X K L).obj M).inv ≫
        derivedSheafHomMap X Hd (DerivedCategory.Q.map (homMap X k l))
          (DerivedCategory.Q.map m) =
      DerivedCategory.Q.map (homMap X (homMap X k l) m) ≫
        (Hd.homComparison (sheafHomComplex X K' L').obj M').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hOut
  have tgt : DerivedCategory.Q.map (homMap X (homMap X k l) m) ≫
        (Hd.homComparison (sheafHomComplex X K' L').obj M').inv ≫
          derivedSheafHomMap X Hd (Hd.homComparison K' L').hom
            (𝟙 (DerivedCategory.Q.obj M')) =
      (Hd.homComparison (sheafHomComplex X K L).obj M).inv ≫
        derivedSheafHomMap X Hd (Hd.homComparison K L).hom
            (𝟙 (DerivedCategory.Q.obj M)) ≫
          derivedSheafHomMap X Hd (derivedSheafHomMap X Hd (DerivedCategory.Q.map k)
            (DerivedCategory.Q.map l)) (DerivedCategory.Q.map m) := by
    rw [e₁, ← Category.assoc ((Hd.homComparison (sheafHomComplex X K L).obj M).inv), e₂,
      Category.assoc]
  dsimp only [derivedEvaluationOnKInjectiveModel]
  simp only [Category.assoc]
  rw [reassoc_of% src,
    reassoc_of% (homComplexDerivedEvaluation_natural X T k l m), tgt]

/-- **Transport of derived evaluation along quasi-isomorphisms of K-injective
representatives.** Derived evaluation on K-injective targets does not depend on the chosen
representatives: transporting it along three morphisms of complexes whose classes are
invertible returns it. -/
theorem derivedEvaluationOnKInjectiveModel_transport
    {A A₁ B B₁ C C₁ :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [B.IsKInjective] [B₁.IsKInjective] [C.IsKInjective] [C₁.IsKInjective]
    (a : A ⟶ A₁) (b : B₁ ⟶ B) (c : C ⟶ C₁)
    (ea : DerivedCategory.Q.obj A₁ ≅ DerivedCategory.Q.obj A)
    (eb : DerivedCategory.Q.obj B₁ ≅ DerivedCategory.Q.obj B)
    (ec : DerivedCategory.Q.obj C₁ ≅ DerivedCategory.Q.obj C)
    (ha : DerivedCategory.Q.map a = ea.inv) (hb : DerivedCategory.Q.map b = eb.hom)
    (hc : DerivedCategory.Q.map c = ec.inv) :
    derivedTensorMap X T (derivedSheafHomMap X Hd eb.hom ec.inv) ea.inv ≫
        derivedEvaluationOnKInjectiveModel X T Hd A₁ B₁ C₁ ≫
        derivedSheafHomMap X Hd
          (derivedSheafHomMap X Hd ea.hom eb.inv) ec.hom =
      derivedEvaluationOnKInjectiveModel X T Hd A B C := by
  have hnat := derivedEvaluationOnKInjectiveModel_natural X T Hd a b c
  rw [ha, hb, hc] at hnat
  rw [← Category.assoc, hnat, Category.assoc, derivedSheafHomMap_comp,
    derivedSheafHomMap_comp]
  simp only [Iso.inv_hom_id, derivedSheafHomMap_id, Category.comp_id]

section Objects

variable {E E' F F' G G' :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}

/-- **The evaluation morphism of derived internal Homs.** For arbitrary objects `K`, `L`, `M`
of `D(Mod(O))`, the canonical morphism

`RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`,

obtained from the evaluation morphism of internal Hom complexes of Stacks 0A92 by passing to
the chosen K-injective representatives of the three objects. -/
def derivedSheafHomEvaluation
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (T.tensor.obj ((Hd.hom.obj (op L)).obj M)).obj K ⟶
      (Hd.hom.obj (op ((Hd.hom.obj (op K)).obj L))).obj M :=
  derivedTensorMap X T
      (derivedSheafHomMap X Hd (kInjectiveModelIso X L).hom (kInjectiveModelIso X M).inv)
      (kInjectiveModelIso X K).inv ≫
    derivedEvaluationOnKInjectiveModel X T Hd (kInjectiveModel X K)
      (kInjectiveModel X L) (kInjectiveModel X M) ≫
    derivedSheafHomMap X Hd
      (derivedSheafHomMap X Hd (kInjectiveModelIso X K).hom (kInjectiveModelIso X L).inv)
      (kInjectiveModelIso X M).hom

/-- **Independence of the chosen representatives.** On the classes of complexes whose two
targets are already K-injective, the evaluation morphism for arbitrary objects is the one built
directly from those complexes. -/
theorem derivedSheafHomEvaluation_eq_onKInjectiveModel
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] [C.IsKInjective] :
    derivedSheafHomEvaluation X T Hd (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C) =
      derivedEvaluationOnKInjectiveModel X T Hd A B C := by
  obtain ⟨a, ha⟩ := exists_Q_map_eq_of_isKInjective X
    (I := kInjectiveModel X (DerivedCategory.Q.obj A))
    (kInjectiveModelIso X (DerivedCategory.Q.obj A)).inv
  obtain ⟨b, hb⟩ := exists_Q_map_eq_of_isKInjective X
    (A := kInjectiveModel X (DerivedCategory.Q.obj B)) (I := B)
    (kInjectiveModelIso X (DerivedCategory.Q.obj B)).hom
  obtain ⟨c, hc⟩ := exists_Q_map_eq_of_isKInjective X
    (I := kInjectiveModel X (DerivedCategory.Q.obj C))
    (kInjectiveModelIso X (DerivedCategory.Q.obj C)).inv
  exact derivedEvaluationOnKInjectiveModel_transport X T Hd a b c _ _ _ ha hb hc

/-- If `φ` is the conjugate `e.hom ≫ f ≫ e'.inv` of `f` by two isomorphisms, then `f` is recovered
from `φ` on either side. -/
private theorem comp_eq_and_eq_comp_of_eq_hom_comp_inv {D : Type*} [Category D]
    {A B A' B' : D} (e : A ≅ A') (e' : B ≅ B') (f : A' ⟶ B') (φ : A ⟶ B)
    (h : φ = e.hom ≫ f ≫ e'.inv) : φ ≫ e'.hom = e.hom ≫ f ∧ e.inv ≫ φ = f ≫ e'.inv := by
  subst h
  simp

/-- **Functoriality of the evaluation morphism of derived internal Homs**, in all three
objects at once: covariant in the source and in the target, contravariant in the intermediate
object. -/
theorem derivedSheafHomEvaluation_natural (f : E ⟶ E') (g : F' ⟶ F) (h : G ⟶ G') :
    derivedTensorMap X T (derivedSheafHomMap X Hd g h) f ≫
        derivedSheafHomEvaluation X T Hd E' F' G' =
      derivedSheafHomEvaluation X T Hd E F G ≫
        derivedSheafHomMap X Hd (derivedSheafHomMap X Hd f g) h := by
  obtain ⟨φ, hφ⟩ := exists_Q_map_eq_of_isKInjective X
    (A := kInjectiveModel X E) (I := kInjectiveModel X E')
    ((kInjectiveModelIso X E).hom ≫ f ≫ (kInjectiveModelIso X E').inv)
  obtain ⟨γ, hγ⟩ := exists_Q_map_eq_of_isKInjective X
    (A := kInjectiveModel X F') (I := kInjectiveModel X F)
    ((kInjectiveModelIso X F').hom ≫ g ≫ (kInjectiveModelIso X F).inv)
  obtain ⟨η, hη⟩ := exists_Q_map_eq_of_isKInjective X
    (A := kInjectiveModel X G) (I := kInjectiveModel X G')
    ((kInjectiveModelIso X G).hom ≫ h ≫ (kInjectiveModelIso X G').inv)
  obtain ⟨hf₁, hf₂⟩ := comp_eq_and_eq_comp_of_eq_hom_comp_inv _ _ _ _ hφ
  obtain ⟨hg₁, hg₂⟩ := comp_eq_and_eq_comp_of_eq_hom_comp_inv _ _ _ _ hγ
  obtain ⟨hh₁, hh₂⟩ := comp_eq_and_eq_comp_of_eq_hom_comp_inv _ _ _ _ hη
  have src : derivedTensorMap X T (derivedSheafHomMap X Hd g h) f ≫
        derivedTensorMap X T (derivedSheafHomMap X Hd (kInjectiveModelIso X F').hom
          (kInjectiveModelIso X G').inv) (kInjectiveModelIso X E').inv =
      derivedTensorMap X T (derivedSheafHomMap X Hd (kInjectiveModelIso X F).hom
          (kInjectiveModelIso X G).inv) (kInjectiveModelIso X E).inv ≫
        derivedTensorMap X T (derivedSheafHomMap X Hd (DerivedCategory.Q.map γ)
          (DerivedCategory.Q.map η)) (DerivedCategory.Q.map φ) := by
    rw [derivedTensorMap_comp, derivedTensorMap_comp, derivedSheafHomMap_comp,
      derivedSheafHomMap_comp, hg₁, hh₂, hf₂]
  have tgt : derivedSheafHomMap X Hd (derivedSheafHomMap X Hd (DerivedCategory.Q.map φ)
            (DerivedCategory.Q.map γ)) (DerivedCategory.Q.map η) ≫
          derivedSheafHomMap X Hd (derivedSheafHomMap X Hd (kInjectiveModelIso X E').hom
            (kInjectiveModelIso X F').inv) (kInjectiveModelIso X G').hom =
        derivedSheafHomMap X Hd (derivedSheafHomMap X Hd (kInjectiveModelIso X E).hom
            (kInjectiveModelIso X F).inv) (kInjectiveModelIso X G).hom ≫
          derivedSheafHomMap X Hd (derivedSheafHomMap X Hd f g) h := by
    rw [derivedSheafHomMap_comp, derivedSheafHomMap_comp, derivedSheafHomMap_comp,
      derivedSheafHomMap_comp, hf₁, hg₂, hh₁]
  dsimp only [derivedSheafHomEvaluation]
  simp only [Category.assoc]
  rw [reassoc_of% src,
    reassoc_of% (derivedEvaluationOnKInjectiveModel_natural X T Hd φ γ η), tgt]

end Objects

/-- **The target of derived evaluation is the iterated internal Hom complex.** For complexes
`A`, `B`, `C` with `B` and `C` K-injective, the derived internal Hom of the derived internal
Hom of `A` and `B` into `C` is the class of `SheafHom(SheafHom(A, B), C)`. -/
def derivedEvaluationTargetComparison
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] [C.IsKInjective] :
    (Hd.hom.obj (op ((Hd.hom.obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj B)))).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj
        (sheafHomComplex X (sheafHomComplex X A B).obj C).obj :=
  (Hd.hom.mapIso (Hd.homComparison A B).symm.op).app (DerivedCategory.Q.obj C) ≪≫
    Hd.homComparison (sheafHomComplex X A B).obj C

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The target comparison, read as an induced map on derived internal Hom followed by the
K-injective model comparison. -/
lemma derivedEvaluationTargetComparison_hom
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] [C.IsKInjective] :
    (derivedEvaluationTargetComparison X Hd A B C).hom =
      derivedSheafHomMap X Hd (Hd.homComparison A B).inv
          (𝟙 (DerivedCategory.Q.obj C)) ≫
        (Hd.homComparison (sheafHomComplex X A B).obj C).hom := by
  simp [derivedEvaluationTargetComparison, derivedSheafHomMap]

/-- **The source of derived evaluation is the total tensor complex.** For a K-flat complex `A`
and a K-injective complex `C`, the derived tensor product of the derived internal Hom
`RSheafHom(B, C)` with the class of `A` is the class of `Tot(SheafHom(B, C) ⊗_O A)`, in the
spelling of Section 34 in which the evaluation morphism of Stacks 0A92 is stated. -/
def derivedEvaluationSourceComparison
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [C.IsKInjective] :
    (T.tensor.obj ((Hd.hom.obj (op (DerivedCategory.Q.obj B))).obj
          (DerivedCategory.Q.obj C))).obj (DerivedCategory.Q.obj A) ≅
      DerivedCategory.Q.obj (tensorTotal X (sheafHomComplex X B C).obj A) :=
  (T.tensor.mapIso (Hd.homComparison B C)).app (DerivedCategory.Q.obj A) ≪≫
    T.comparisonRight (sheafHomComplex X B C).obj A hA ≪≫
    DerivedCategory.Q.mapIso
      (tensorTotalIsoTensorComplex X (sheafHomComplex X B C).obj A).symm

/-- The source comparison, read as an induced map on the derived tensor product followed by the
canonical map to the ordinary total tensor product and the comparison of its two spellings. -/
lemma derivedEvaluationSourceComparison_hom
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [C.IsKInjective] :
    (derivedEvaluationSourceComparison X T Hd A B C hA).hom =
      derivedTensorMap X T (Hd.homComparison B C).hom
          (𝟙 (DerivedCategory.Q.obj A)) ≫
        T.toTensor (sheafHomComplex X B C).obj A ≫
          DerivedCategory.Q.map
            (tensorTotalIsoTensorComplex X (sheafHomComplex X B C).obj A).inv := by
  dsimp only [derivedEvaluationSourceComparison, derivedTensorMap, Iso.trans_hom,
    Iso.app_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom]
  rw [← T.toTensor_eq_comparisonRight _ _ hA, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Derived evaluation computes the evaluation morphism of complexes.** For a K-flat complex
`A` and K-injective complexes `B` and `C`, the evaluation morphism of derived internal Homs, read
through the source and target comparisons, is the class of the evaluation morphism of internal
Hom complexes of Stacks 0A92. -/
theorem derivedSheafHomEvaluation_model
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [B.IsKInjective] [C.IsKInjective] :
    derivedSheafHomEvaluation X T Hd (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj C) ≫
        (derivedEvaluationTargetComparison X Hd A B C).hom =
      (derivedEvaluationSourceComparison X T Hd A B C hA).hom ≫
        DerivedCategory.Q.map (evaluationMap X A B C) := by
  have hcancel : derivedSheafHomMap X Hd (Hd.homComparison A B).hom
          (𝟙 (DerivedCategory.Q.obj C)) ≫
        derivedSheafHomMap X Hd (Hd.homComparison A B).inv
          (𝟙 (DerivedCategory.Q.obj C)) =
      𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj (sheafHomComplex X A B).obj))).obj
        (DerivedCategory.Q.obj C)) := by
    rw [derivedSheafHomMap_comp, Iso.inv_hom_id, Category.comp_id, derivedSheafHomMap_id]
  rw [derivedSheafHomEvaluation_eq_onKInjectiveModel,
    derivedEvaluationTargetComparison_hom, derivedEvaluationSourceComparison_hom]
  dsimp only [derivedEvaluationOnKInjectiveModel, homComplexDerivedEvaluation]
  simp only [Category.assoc]
  rw [reassoc_of% hcancel]
  simp only [Iso.inv_hom_id, Category.comp_id, CategoryTheory.Functor.map_comp]

end Evaluation

section Canonical

/-- **Stacks 0A97: the canonical evaluation morphism of derived internal Homs.** For arbitrary
objects `K`, `L`, `M` of `D(Mod(O))` there is a canonical morphism

`RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`. -/
@[stacks 0A97 "the canonical evaluation morphism"]
def derivedEvaluation
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj
        (((derivedInternalHomFunctor.{u, d} X).obj (op L)).obj M)).obj K ⟶
      ((derivedInternalHomFunctor.{u, d} X).obj
        (op (((derivedInternalHomFunctor.{u, d} X).obj (op K)).obj L))).obj M :=
  derivedSheafHomEvaluation X (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X)
    (canonicalDerivedInternalHom.{u, d} X) K L M

/-- **Stacks 0A97.** On a K-flat source and K-injective targets, the canonical evaluation
morphism is the class of the evaluation morphism of internal Hom complexes of Stacks 0A92. -/
@[stacks 0A97 "comparison with evaluation of complexes"]
theorem derivedEvaluation_model
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [B.IsKInjective] [C.IsKInjective] :
    derivedEvaluation X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj C) ≫
        (derivedEvaluationTargetComparison X (canonicalDerivedInternalHom.{u, d} X)
          A B C).hom =
      (derivedEvaluationSourceComparison X
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X)
          (canonicalDerivedInternalHom.{u, d} X) A B C hA).hom ≫
        DerivedCategory.Q.map (evaluationMap X A B C) :=
  derivedSheafHomEvaluation_model X _ _ A B C hA

/-- **Stacks 0A97.** The canonical evaluation morphism is natural in the source object and in
the target object, and contranatural in the intermediate object. -/
@[stacks 0A97 "functoriality in all three objects"]
theorem derivedEvaluation_natural
    {K K' L L' M M' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : K ⟶ K') (g : L' ⟶ L) (h : M ⟶ M') :
    derivedEvaluation X K L M ≫
        ((derivedInternalHomFunctor.{u, d} X).map
          ((((derivedInternalHomFunctor.{u, d} X).obj (op K')).map g ≫
            ((derivedInternalHomFunctor.{u, d} X).map f.op).app L).op)).app M ≫
        ((derivedInternalHomFunctor.{u, d} X).obj
          (op (((derivedInternalHomFunctor.{u, d} X).obj (op K')).obj L'))).map h =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).map
          (((derivedInternalHomFunctor.{u, d} X).map g.op).app M ≫
            ((derivedInternalHomFunctor.{u, d} X).obj (op L')).map h)).app K ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj
          (((derivedInternalHomFunctor.{u, d} X).obj (op L')).obj M')).map f ≫
        derivedEvaluation X K' L' M' := by
  rw [← derivedSheafHomMap_target_first X (canonicalDerivedInternalHom.{u, d} X) f g]
  exact (derivedSheafHomEvaluation_natural X
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X)
        (canonicalDerivedInternalHom.{u, d} X) f g h).symm.trans
    (Category.assoc _ _ _)

end Canonical

end AlgebraicGeometry.RingedSite

end
