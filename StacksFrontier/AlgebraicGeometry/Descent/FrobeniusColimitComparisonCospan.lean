module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStagePseudococone
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectEssSurj
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVect
public import
  StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectEssSurj

/-!
# The comparison functor of [Stacks, Tag 0EXB] commutes with the transition functors

For a morphism `f : X ⟶ Y` of schemes in characteristic `p`, the transition functor along `f`
exists on both models of `colim_F Vect(-)`: on the explicit category of pairs `(E, n)` of
[Stacks, Tag 0EXA] it is `AlgebraicGeometry.OneGeneratorSquare.colimVectPullback`, and on finite
locally free `colim_F 𝒪`-modules it is `AlgebraicGeometry.frobeniusColimitVectorBundlesPullback`.
The comparison functors of [Stacks, Tag 0EXB] commute with the two, because the family
`(frobeniusStageFunctor n, frobeniusStageFunctorPullbackIso n)` is a morphism of pseudo-cocones
(`AlgebraicGeometry.frobeniusStageFunctorPullbackIso_compat`).  For a cospan of schemes this gives
a transformation of cospans, so that `CategoricalPullback.essSurj_mapCospan` applies: every object
of the categorical fibre product of [Stacks, Tag 0EXD] comes from the model.

## Main definitions

* `CategoryTheory.EndoColim.Pseudococone.descIsoOfStageIso`: a morphism of pseudo-cocones induces
  an isomorphism of the functors out of the colimit category.
* `CategoryTheory.EndoColim.Pseudococone.whisker` and `…whiskerDescIso`: a pseudo-cocone followed
  by a functor, and its functor out of the colimit category.
* `CategoryTheory.EndoColim.Pseudococone.descCompIso`: a morphism of pseudo-cocones over a square
  of endofunctors induces `P.desc ⋙ Ψ ≅ EndoColim.map F F' Φ α ⋙ P'.desc`.
* `AlgebraicGeometry.frobeniusColimitVectComparisonPullbackIso`: **the comparison functor of Tag
  0EXB commutes with the transition functors.**
* `AlgebraicGeometry.frobeniusColimitVectCospanTransform`: the comparison functors at the three
  corners of a cospan, as a `CatCospanTransform`.

## Main results

* `AlgebraicGeometry.essSurj_mapCospan_frobeniusColimitVectCospanTransform`: for three
  quasi-compact quasi-separated corners, every object of the categorical fibre product of the
  transition functors on `colim_F 𝒪`-modules comes from the categorical fibre product of the
  models.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.EndoColim.Pseudococone

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ C}

section StageIso

variable {P Q : Pseudococone F D} (γ : ∀ n, P.stage n ≅ Q.stage n)
  (hγ : ∀ (n : ℕ) (E : C), (P.compat n).hom.app E ≫ (γ n).hom.app E =
    (γ (n + 1)).hom.app (F.obj E) ≫ (Q.compat n).hom.app E)

include hγ in
/-- A family of isomorphisms of stage functors compatible with the one-step comparisons is
compatible with the iterated comparisons. -/
theorem iterObjIso_hom_comp_stageIso (n : ℕ) : ∀ (k : ℕ) (E : C),
    (P.iterObjIso n k E).hom ≫ (γ n).hom.app E =
      (γ (n + k)).hom.app ((F.endoIter k).obj E) ≫ (Q.iterObjIso n k E).hom
  | 0, E => by simp [iterObjIso]
  | k + 1, E => by
      rw [iterObjIso_succ_hom, iterObjIso_succ_hom, Category.assoc,
        iterObjIso_hom_comp_stageIso n k E]
      exact (reassoc_of% (hγ (n + k) ((F.endoIter k).obj E))) _

include hγ in
/-- The inverse form of `iterObjIso_hom_comp_stageIso`. -/
theorem iterObjIso_inv_comp_stageIso (n k : ℕ) (E : C) :
    (P.iterObjIso n k E).inv ≫ (γ (n + k)).hom.app ((F.endoIter k).obj E) =
      (γ n).hom.app E ≫ (Q.iterObjIso n k E).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, iterObjIso_hom_comp_stageIso γ hγ n k E,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A family of isomorphisms of stage functors commutes with the comparisons at equal indices. -/
theorem stageHom_app_comp_stageIso {N N' : ℕ} (h : N = N') (X : C) :
    (P.stageHom h).app X ≫ (γ N').hom.app X = (γ N).hom.app X ≫ (Q.stageHom h).app X := by
  subst h
  simp

include hγ in
/-- A family of isomorphisms of stage functors compatible with the comparisons commutes with the
morphisms induced by presented morphisms. -/
theorem mapAt_comp_stageIso (n m a b : ℕ) (h : n + a = m + b) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) :
    P.mapAt n m a b h f ≫ (γ m).hom.app G = (γ n).hom.app E ≫ Q.mapAt n m a b h f := by
  simp only [mapAt, Category.assoc]
  rw [iterObjIso_hom_comp_stageIso γ hγ m b G, reassoc_of% (stageHom_app_comp_stageIso γ h _),
    reassoc_of% ((γ (n + a)).hom.naturality f)]
  exact (reassoc_of% (iterObjIso_inv_comp_stageIso γ hγ n a E)) _

/-- **A morphism of pseudo-cocones induces an isomorphism of the functors out of the colimit
category.** -/
def descIsoOfStageIso : P.desc ≅ Q.desc :=
  NatIso.ofComponents (fun A ↦ (γ A.stage).app A.obj) (fun {A B} u ↦ by
    induction u using Quot.ind with
    | _ x => exact mapAt_comp_stageIso γ hγ _ _ _ _ _ x.hom)

end StageIso

section Whisker

variable {E : Type u₃} [Category.{v₃} E]

/-- A pseudo-cocone followed by a functor. -/
def whisker (P : Pseudococone F E) (Θ : E ⥤ D) : Pseudococone F D where
  stage n := P.stage n ⋙ Θ
  compat n := Functor.isoWhiskerRight (P.compat n) Θ

variable (P : Pseudococone F E) (Θ : E ⥤ D)

/-- The iterated comparisons of a whiskered pseudo-cocone are the whiskered ones. -/
theorem whisker_iterObjIso (n : ℕ) : ∀ (k : ℕ) (X : C),
    (P.whisker Θ).iterObjIso n k X = Θ.mapIso (P.iterObjIso n k X)
  | 0, X => by ext; simp [iterObjIso, whisker]
  | k + 1, X => by
      ext
      rw [iterObjIso_succ_hom, Functor.mapIso_hom, iterObjIso_succ_hom, Functor.map_comp,
        whisker_iterObjIso n k X]
      rfl

/-- The comparisons at equal indices of a whiskered pseudo-cocone are the whiskered ones. -/
theorem whisker_stageHom_app {N N' : ℕ} (h : N = N') (X : C) :
    ((P.whisker Θ).stageHom h).app X = Θ.map ((P.stageHom h).app X) := by
  subst h
  simp only [stageHom_refl, NatTrans.id_app, Functor.map_id]
  rfl

/-- The morphism a whiskered pseudo-cocone induces is the whiskered one. -/
theorem whisker_mapAt (n m a b : ℕ) (h : n + a = m + b) {X Y : C}
    (f : (F.endoIter a).obj X ⟶ (F.endoIter b).obj Y) :
    (P.whisker Θ).mapAt n m a b h f = Θ.map (P.mapAt n m a b h f) := by
  simp only [mapAt, whisker_iterObjIso, whisker_stageHom_app, Functor.map_comp,
    Functor.mapIso_inv, Functor.mapIso_hom]
  rfl

/-- The functor out of the colimit category determined by a whiskered pseudo-cocone is the
whiskered functor. -/
def whiskerDescIso : (P.whisker Θ).desc ≅ P.desc ⋙ Θ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {A B} u ↦ by
    induction u using Quot.ind with
    | _ x =>
        change (P.whisker Θ).mapRep x ≫ 𝟙 _ = 𝟙 _ ≫ Θ.map (P.mapRep x)
        rw [Category.comp_id, Category.id_comp]
        exact whisker_mapAt P Θ _ _ _ _ _ x.hom)

end Whisker

end CategoryTheory.EndoColim.Pseudococone

namespace CategoryTheory.EndoColim

universe v₁ v₂ v₃ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₁} C']
  {D : Type u₃} [Category.{v₂} D] {D' : Type u₄} [Category.{v₃} D']
  {F : C ⥤ C} {F' : C' ⥤ C'} (P : Pseudococone F D) (P' : Pseudococone F' D')
  (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F') (Ψ : D ⥤ D')
  (β : ∀ n, P.stage n ⋙ Ψ ≅ Φ ⋙ P'.stage n)
  (hβ : ∀ (n : ℕ) (E : C), Ψ.map ((P.compat n).hom.app E) ≫ (β n).hom.app E =
      (β (n + 1)).hom.app (F.obj E) ≫ (P'.stage (n + 1)).map (α.hom.app E) ≫
        (P'.compat n).hom.app (Φ.obj E))

/-- The functor of a pseudo-cocone carries the comparison of the pseudo-cocone of
`CategoryTheory.EndoColim.map` to `α` followed by its own comparison. -/
theorem Pseudococone.desc_map_mapPseudococone_compat_hom_app (n : ℕ) (E : C) :
    P'.desc.map ((mapPseudococone F F' Φ α).compat n |>.hom.app E) =
      (P'.stage (n + 1)).map (α.hom.app E) ≫ (P'.compat n).hom.app (Φ.obj E) := by
  have h := mapPseudococone_compatIter_hom F F' Φ α n 0 E
  change ((mapPseudococone F F' Φ α).compat n).hom.app E =
    stageHomOf F' (n + 1) (α.hom.app E) ≫ shiftStepHom F' n (Φ.obj E) at h
  rw [h]
  refine (P'.desc.map_comp (stageHomOf F' (n + 1) (α.hom.app E))
    (shiftStepHom F' n (Φ.obj E))).trans ?_
  rw [P'.desc_map_shiftStepHom]
  exact congrArg (· ≫ _) (P'.homMap_stageFunctor_map (n + 1) (α.hom.app E))

/-- The stage functors of the pseudo-cocone `mapPseudococone F F' Φ α` followed by `P'.desc`,
compared with those of `P` followed by `Ψ`, by `β`. -/
def Pseudococone.mapStageIso (n : ℕ) :
    (P.whisker Ψ).stage n ≅ ((mapPseudococone F F' Φ α).whisker P'.desc).stage n :=
  NatIso.ofComponents (fun E ↦ (β n).app E) (fun {E G} g ↦ by
    have := (β n).hom.naturality g
    change Ψ.map ((P.stage n).map g) ≫ (β n).hom.app G =
      (β n).hom.app E ≫ P'.homMap ((stageFunctor F' n).map (Φ.map g))
    rw [P'.homMap_stageFunctor_map]
    exact this)

include hβ in
/-- The stage isomorphisms `CategoryTheory.EndoColim.Pseudococone.mapStageIso` are compatible with
the comparisons of the two whiskered pseudo-cocones. -/
theorem Pseudococone.mapStageIso_compat (n : ℕ) (E : C) :
    ((P.whisker Ψ).compat n).hom.app E ≫ (P.mapStageIso P' Φ α Ψ β n).hom.app E =
      (P.mapStageIso P' Φ α Ψ β (n + 1)).hom.app (F.obj E) ≫
        (((mapPseudococone F F' Φ α).whisker P'.desc).compat n).hom.app E := by
  change Ψ.map ((P.compat n).hom.app E) ≫ (β n).hom.app E =
    (β (n + 1)).hom.app (F.obj E) ≫
      P'.desc.map ((mapPseudococone F F' Φ α).compat n |>.hom.app E)
  rw [Pseudococone.desc_map_mapPseudococone_compat_hom_app, hβ]
  rfl

/-- **A morphism of pseudo-cocones over a commutative square of endofunctors induces a
commutative square of the functors out of the colimit categories**: `P.desc` followed by `Ψ` is
`EndoColim.map F F' Φ α` followed by `P'.desc`, the component at `(E, n)` being `β n` at `E`. -/
def Pseudococone.descCompIso : P.desc ⋙ Ψ ≅ map F F' Φ α ⋙ P'.desc :=
  (P.whiskerDescIso Ψ).symm ≪≫
    Pseudococone.descIsoOfStageIso (P.mapStageIso P' Φ α Ψ β)
      (Pseudococone.mapStageIso_compat P P' Φ α Ψ β hβ) ≪≫
    (mapPseudococone F F' Φ α).whiskerDescIso P'.desc

/-- The component of `CategoryTheory.EndoColim.Pseudococone.descCompIso` at `(E, n)` is `β n` at
`E`. -/
theorem Pseudococone.descCompIso_hom_app (A : EndoColim F) :
    (P.descCompIso P' Φ α Ψ β hβ).hom.app A = (β A.stage).hom.app A.obj := by
  change 𝟙 _ ≫ (β A.stage).hom.app A.obj ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

end CategoryTheory.EndoColim

namespace AlgebraicGeometry

open Stacks.Frobenius

variable (p : ℕ) [Fact p.Prime]

/-- **The comparison functor of [Stacks, Tag 0EXB] commutes with the transition functors**: on
the model `colim_F Vect(-)` of [Stacks, Tag 0EXA] the transition functor along `f` is
`AlgebraicGeometry.OneGeneratorSquare.colimVectPullback`, and on the finite locally free
`colim_F 𝒪`-modules it is `AlgebraicGeometry.frobeniusColimitVectorBundlesPullback`.  This is the
morphism of pseudo-cocones `(frobeniusStageFunctor n, frobeniusStageFunctorPullbackIso n)`
read on the functors out of the colimit categories. -/
def frobeniusColimitVectComparisonPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) :
    frobeniusColimitVectComparison Y p hY ⋙ frobeniusColimitVectorBundlesPullback p f hX hY ≅
      OneGeneratorSquare.colimVectPullback p hX hY f ⋙ frobeniusColimitVectComparison X p hX :=
  (frobeniusColimitVectPseudococone Y p hY).descCompIso (frobeniusColimitVectPseudococone X p hX)
    (Scheme.Vect.pullback f) (frobeniusVectPullbackIso f p hX hY)
    (frobeniusColimitVectorBundlesPullback p f hX hY) (frobeniusStageFunctorPullbackIso p f hX hY)
    (frobeniusStageFunctorPullbackIso_compat p f hX hY)

/-- The component of `AlgebraicGeometry.frobeniusColimitVectComparisonPullbackIso` at `(E, n)` is
the commutation `AlgebraicGeometry.frobeniusStageFunctorPullbackIso` of the stage functor with the
transition functor. -/
theorem frobeniusColimitVectComparisonPullbackIso_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (A : frobeniusColimitVectModel Y p hY) :
    (frobeniusColimitVectComparisonPullbackIso p f hX hY).hom.app A =
      (frobeniusStageFunctorPullbackIso p f hX hY A.stage).hom.app A.obj :=
  EndoColim.Pseudococone.descCompIso_hom_app _ _ _ _ _ _ _ A

section Cospan

variable {XZ XM XE : Scheme.{u}} (e : XE ⟶ XZ) (d : XE ⟶ XM)
  (hZ : IsInCharacteristic XZ p) (hM : IsInCharacteristic XM p)
  (hE : IsInCharacteristic XE p)

/-- **The comparison functors of [Stacks, Tag 0EXB] at the three corners form a transformation
from the cospan of transition functors on the models `colim_F Vect(-)` to the cospan of
transition functors on the finite locally free `colim_F 𝒪`-modules.** -/
def frobeniusColimitVectCospanTransform :
    CatCospanTransform (OneGeneratorSquare.colimVectPullback p hE hZ e)
      (OneGeneratorSquare.colimVectPullback p hE hM d)
      (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p d hE hM) where
  left := frobeniusColimitVectComparison XZ p hZ
  base := frobeniusColimitVectComparison XE p hE
  right := frobeniusColimitVectComparison XM p hM
  squareLeft := ⟨(frobeniusColimitVectComparisonPullbackIso p e hE hZ).symm⟩
  squareRight := ⟨(frobeniusColimitVectComparisonPullbackIso p d hE hM).symm⟩

/-- **Every object of the categorical fibre product of the cospan of transition functors comes
from the model**, the three corners being quasi-compact and quasi-separated: the induced functor
`CategoricalPullback.mapCospan` from the categorical fibre product of the models
`colim_F Vect(-)` of [Stacks, Tag 0EXA] is essentially surjective, because the comparison functors
of [Stacks, Tag 0EXB] are equivalences. -/
theorem essSurj_mapCospan_frobeniusColimitVectCospanTransform
    [CompactSpace XZ] [QuasiSeparatedSpace XZ] [CompactSpace XM] [QuasiSeparatedSpace XM]
    [CompactSpace XE] [QuasiSeparatedSpace XE] :
    (CategoricalPullback.mapCospan
      (frobeniusColimitVectCospanTransform p e d hZ hM hE)).EssSurj := by
  have := isEquivalence_frobeniusColimitVectComparison XZ p hZ
  have := isEquivalence_frobeniusColimitVectComparison XM p hM
  have := isEquivalence_frobeniusColimitVectComparison XE p hE
  exact CategoricalPullback.essSurj_mapCospan _
    (inferInstanceAs (frobeniusColimitVectComparison XZ p hZ).EssSurj)
    (inferInstanceAs (frobeniusColimitVectComparison XM p hM).EssSurj)
    (inferInstanceAs (frobeniusColimitVectComparison XE p hE).Full)
    (inferInstanceAs (frobeniusColimitVectComparison XE p hE).Faithful)

end Cospan

end AlgebraicGeometry
