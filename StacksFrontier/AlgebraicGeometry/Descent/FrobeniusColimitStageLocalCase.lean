module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageSquare
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStagePseudococone
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorSquare
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorOrdinaryLocal
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorStageTriple
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTrivialisedHom
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPower
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis

/-!
# The local case of [Stacks, Tag 0EXD] at the level of Frobenius colimits

The ordinary local case `Stacks.AlmostBlowUp.exists_vect_iso_of_free_center` produces, from a
triple `(ℰ, 𝒢, φ)` of ordinary finite locally free modules over the square of
[Stacks, Example 0EVH] with `ℰ` free, a finite locally free module `N` on the base whose
ordinary triple is isomorphic to `(ℰ, 𝒢, φ)`.  This file carries that solution to the categorical
fibre product of the Frobenius colimits: the comparison functor of [Stacks, Tag 0EXD] applied to
the stage image `S_n N` is isomorphic to the stage triple of `(ℰ, 𝒢, φ)`.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitStageTripleMapIso`: **an isomorphism of ordinary triples
  induces an isomorphism of their stage triples** at twist `0`.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesComparisonStageIsoOfIso`: for an arbitrary
  commutative square in characteristic `p`, an isomorphism between the ordinary triple of `N` and
  a triple `T` gives `G (S_n N) ≅ S_n T`.

## Main results

* `AlgebraicGeometry.exists_twoGeneratorFrobeniusColimitComparison_iso_of_stageTriple`: **the
  local case of [Stacks, Tag 0EXD]**: an object of the categorical fibre product of the
  Frobenius colimits that is the stage triple of an ordinary triple with free module on the
  centre is in the essential image of the comparison functor, over an arbitrary ring of
  characteristic `p`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

section General

variable (p : ℕ) [Fact p.Prime] {X X' Z E : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)

/-- The structural isomorphism of a stage triple at twist `0`, with the twist written away. -/
theorem frobeniusColimitStageTriple_zero_iso_hom (n : ℕ) (Ec : Z.Vect) (Em : X'.Vect)
    (φ : (Scheme.Vect.pullback e).obj Ec ≅ (Scheme.Vect.pullback q).obj Em) :
    (frobeniusColimitStageTriple p e q hZ hX' hE n 0 Ec Em φ).iso.hom =
      (frobeniusStageFunctorPullbackIso p e hE hZ n).hom.app Ec ≫
        (frobeniusStageFunctor E p hE n).map φ.hom ≫
          (frobeniusStageFunctorPullbackIso p q hE hX' n).inv.app Em :=
  (frobeniusColimitStageTriple_iso_hom p e q hZ hX' hE n 0 Ec Em φ).trans
    (congrArg (fun t => _ ≫ t ≫ _) (frobeniusStageHomMap_zero p E hE n _))

/-- **The compatibility of the comparison functor of [Stacks, Tag 0EXD] with the stage
functors.**  The isomorphism `e^*(z^*S_n 𝒩) ≅ q^*(b^*S_n 𝒩)` the comparison functor attaches to
the stage image `S_n 𝒩` of a finite locally free `𝒪_X`-module is the stage image of the
ordinary square isomorphism `AlgebraicGeometry.vectPullbackSquareIso`, read through the bridges
`AlgebraicGeometry.frobeniusStageFunctorPullbackIso`; this is
`AlgebraicGeometry.frobeniusStageFunctorPullbackIso_square` in the form
`CategoryTheory.Limits.CategoricalPullback.mkIso` asks for. -/
theorem frobeniusColimitVectorBundlesComparisonStageIso_comm (hw : q ≫ b = e ≫ z) (n : ℕ)
    (N : X.Vect) :
    (frobeniusColimitVectorBundlesPullback p e hE hZ).map
          ((frobeniusStageFunctorPullbackIso p z hZ hX n).hom.app N) ≫
        (frobeniusColimitStageTriple p e q hZ hX' hE n 0 ((Scheme.Vect.pullback z).obj N)
          ((Scheme.Vect.pullback b).obj N) ((vectPullbackSquareIso hw.symm).app N)).iso.hom =
      ((frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj
          ((frobeniusStageFunctor X p hX n).obj N)).iso.hom ≫
        (frobeniusColimitVectorBundlesPullback p q hE hX').map
          ((frobeniusStageFunctorPullbackIso p b hX' hX n).hom.app N) := by
  have hT := frobeniusColimitStageTriple_zero_iso_hom p q e hX' hZ hE n
    ((Scheme.Vect.pullback z).obj N) ((Scheme.Vect.pullback b).obj N)
    ((vectPullbackSquareIso hw.symm).app N)
  have hsq := frobeniusStageFunctorPullbackIso_square p b z q e hX hX' hZ hE hw n N
  rw [hT]
  have h2 := congrArg (· ≫ (frobeniusStageFunctorPullbackIso p q hE hX' n).inv.app
    ((Scheme.Vect.pullback b).obj N)) hsq
  simp only [Category.assoc, Iso.hom_inv_id_app] at h2
  exact h2.symm

/-- **The comparison functor of [Stacks, Tag 0EXD] at a stage object** (item 1b of the roadmap in
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitTwoGeneratorSquare.lean`).  For a
commutative square of schemes in characteristic `p` and a finite locally free `𝒪_X`-module `𝒩`,
the comparison functor applied to the stage image `S_n 𝒩` is the object of the categorical fibre
product attached to the ordinary triple `(z^*𝒩, b^*𝒩, φ)`, `φ` the square isomorphism
`AlgebraicGeometry.vectPullbackSquareIso` at twist `0`.  The components are the bridges
`AlgebraicGeometry.frobeniusStageFunctorPullbackIso` at the two legs `z` and `b`. -/
noncomputable def frobeniusColimitVectorBundlesComparisonStageIso (hw : q ≫ b = e ≫ z) (n : ℕ)
    (N : X.Vect) :
    (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj
        ((frobeniusStageFunctor X p hX n).obj N) ≅
      frobeniusColimitStageTriple p e q hZ hX' hE n 0 ((Scheme.Vect.pullback z).obj N)
        ((Scheme.Vect.pullback b).obj N) ((vectPullbackSquareIso hw.symm).app N) :=
  CategoricalPullback.mkIso ((frobeniusStageFunctorPullbackIso p z hZ hX n).app N)
    ((frobeniusStageFunctorPullbackIso p b hX' hX n).app N)
    (frobeniusColimitVectorBundlesComparisonStageIso_comm p b z q e hX hX' hZ hE hw n N)

/-- The algebra behind `AlgebraicGeometry.frobeniusColimitStageTripleMapIso_comm`. -/
lemma frobeniusColimitStageTripleMapIso_aux {C : Type*} [Category C]
    {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : C} {a : x₀ ⟶ y₀} {b' : y₀ ⟶ y₁} {s : y₁ ⟶ y₂} {c' : y₂ ⟶ y₃}
    {b : x₀ ⟶ x₁} {x : x₁ ⟶ y₁} {t : x₁ ⟶ x₂} {y : x₂ ⟶ y₂} {c : x₂ ⟶ x₃} {d : x₃ ⟶ y₃}
    (h₁ : a ≫ b' = b ≫ x) (hw : x ≫ s = t ≫ y) (h₂ : y ≫ c' = c ≫ d) :
    a ≫ (b' ≫ s ≫ c') = (b ≫ t ≫ c) ≫ d := by
  rw [reassoc_of% h₁, reassoc_of% hw, h₂, Category.assoc, Category.assoc]

/-- The compatibility of `AlgebraicGeometry.frobeniusColimitStageTripleMapIso`. -/
theorem frobeniusColimitStageTripleMapIso_comm (n : ℕ)
    {T T' : CategoricalPullback (Scheme.Vect.pullback e) (Scheme.Vect.pullback q)} (i : T ⟶ T') :
    (frobeniusColimitVectorBundlesPullback p e hE hZ).map
          ((frobeniusStageFunctor Z p hZ n).map i.fst) ≫
        (frobeniusColimitStageTriple p e q hZ hX' hE n 0 T'.fst T'.snd T'.iso).iso.hom =
      (frobeniusColimitStageTriple p e q hZ hX' hE n 0 T.fst T.snd T.iso).iso.hom ≫
        (frobeniusColimitVectorBundlesPullback p q hE hX').map
          ((frobeniusStageFunctor X' p hX' n).map i.snd) := by
  have n₁ := (frobeniusStageFunctorPullbackIso p e hE hZ n).hom.naturality i.fst
  have n₂ := (frobeniusStageFunctorPullbackIso p q hE hX' n).inv.naturality i.snd
  simp only [Functor.comp_map] at n₁ n₂
  have hw : (frobeniusStageFunctor E p hE n).map ((Scheme.Vect.pullback e).map i.fst) ≫
      (frobeniusStageFunctor E p hE n).map T'.iso.hom =
      (frobeniusStageFunctor E p hE n).map T.iso.hom ≫
        (frobeniusStageFunctor E p hE n).map ((Scheme.Vect.pullback q).map i.snd) := by
    rw [← Functor.map_comp, ← Functor.map_comp, i.w]
  rw [frobeniusColimitStageTriple_zero_iso_hom, frobeniusColimitStageTriple_zero_iso_hom]
  exact frobeniusColimitStageTripleMapIso_aux n₁ hw n₂

/-- **An isomorphism of ordinary triples induces an isomorphism of their stage triples**, at
twist `0`: the components are the stage functors applied to the two components. -/
noncomputable def frobeniusColimitStageTripleMapIso (n : ℕ)
    {T T' : CategoricalPullback (Scheme.Vect.pullback e) (Scheme.Vect.pullback q)}
    (i : T ≅ T') :
    frobeniusColimitStageTriple p e q hZ hX' hE n 0 T.fst T.snd T.iso ≅
      frobeniusColimitStageTriple p e q hZ hX' hE n 0 T'.fst T'.snd T'.iso :=
  CategoricalPullback.mkIso
    ((frobeniusStageFunctor Z p hZ n).mapIso ((CategoricalPullback.π₁ _ _).mapIso i))
    ((frobeniusStageFunctor X' p hX' n).mapIso ((CategoricalPullback.π₂ _ _).mapIso i))
    (frobeniusColimitStageTripleMapIso_comm p q e hX' hZ hE n i.hom)

/-- **The comparison functor of [Stacks, Tag 0EXD] at the stage image of a solution.**  For a
commutative square of schemes in characteristic `p`, a finite locally free `𝒪_X`-module `N` and
an isomorphism `i` between the ordinary triple `(z^*N, b^*N, can)` of `N` and a triple `T`, the
comparison functor applied to `S_n N` is isomorphic to the stage triple of `T`. -/
noncomputable def frobeniusColimitVectorBundlesComparisonStageIsoOfIso (hw : q ≫ b = e ≫ z)
    (n : ℕ) (N : X.Vect)
    {T : CategoricalPullback (Scheme.Vect.pullback e) (Scheme.Vect.pullback q)}
    (i : (⟨(Scheme.Vect.pullback z).obj N, (Scheme.Vect.pullback b).obj N,
      (vectPullbackSquareIso hw.symm).app N⟩ :
        CategoricalPullback (Scheme.Vect.pullback e) (Scheme.Vect.pullback q)) ≅ T) :
    (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj
        ((frobeniusStageFunctor X p hX n).obj N) ≅
      frobeniusColimitStageTriple p e q hZ hX' hE n 0 T.fst T.snd T.iso :=
  frobeniusColimitVectorBundlesComparisonStageIso p b z q e hX hX' hZ hE hw n N ≪≫
    frobeniusColimitStageTripleMapIso p q e hX' hZ hE n i

/-- The comparison on Hom-sets at twist `j` of the `j`-fold Frobenius pullback of a morphism is
the comparison at twist `0` of the morphism. -/
theorem frobeniusStageHomMap_iter_map (Y : Scheme.{u}) (hY : IsInCharacteristic Y p) (n : ℕ)
    {M M' : Y.Vect} (f : M ⟶ M') : ∀ j : ℕ,
    frobeniusStageHomMap Y p hY n j ((frobeniusPullbackIter Y p hY j).map f) =
      frobeniusStageHomMap Y p hY n 0 f
  | 0 => rfl
  | j + 1 => (frobeniusStageHomMap_succ Y p hY n j ((frobeniusPullbackIter Y p hY j).map f)).trans
      (frobeniusStageHomMap_iter_map Y hY n f j)

/-- **A stage triple at twist `0` is the same object at any twist**, its isomorphism being
carried along the iterated Frobenius pullback. -/
noncomputable def frobeniusColimitStageTripleTwistIso (n j : ℕ) (Ec : Z.Vect) (Em : X'.Vect)
    (φ : (Scheme.Vect.pullback e).obj Ec ≅ (Scheme.Vect.pullback q).obj Em) :
    frobeniusColimitStageTriple p e q hZ hX' hE n 0 Ec Em φ ≅
      frobeniusColimitStageTriple p e q hZ hX' hE n j Ec Em
        ((frobeniusPullbackIter E p hE j).mapIso φ) :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
    rw [frobeniusColimitStageTriple_iso_hom,
      frobeniusColimitStageTriple_zero_iso_hom p q e hX' hZ hE]
    simp only [Functor.mapIso_hom, Iso.refl_hom, Iso.app_hom, Iso.app_inv]
    rw [frobeniusStageHomMap_iter_map p E hE n φ.hom j, frobeniusStageHomMap_zero]
    have h₁ := (frobeniusColimitVectorBundlesPullback p e hE hZ).map_id
      ((frobeniusStageFunctor Z p hZ n).obj Ec)
    have h₂ := (frobeniusColimitVectorBundlesPullback p q hE hX').map_id
      ((frobeniusStageFunctor X' p hX' n).obj Em)
    exact (eq_whisker h₁ _).trans ((Category.id_comp _).trans
      ((Category.comp_id _).symm.trans (whisker_eq _ h₂.symm))))

/-- **A stage triple at twist `0` is a stage triple at any later stage**, of the Frobenius
pullbacks of its two modules. -/
noncomputable def frobeniusColimitStageTripleRaiseIso (n j : ℕ) (Ec : Z.Vect) (Em : X'.Vect)
    (φ : (Scheme.Vect.pullback e).obj Ec ≅ (Scheme.Vect.pullback q).obj Em) :
    frobeniusColimitStageTriple p e q hZ hX' hE n 0 Ec Em φ ≅
      frobeniusColimitStageTriple p e q hZ hX' hE (n + j) 0
        ((frobeniusPullbackIter Z p hZ j).obj Ec) ((frobeniusPullbackIter X' p hX' j).obj Em)
        (frobeniusStageTripleUntwist p e q hZ hX' hE j Ec Em
          ((frobeniusPullbackIter E p hE j).mapIso φ)) :=
  frobeniusColimitStageTripleTwistIso p q e hX' hZ hE n j Ec Em φ ≪≫
    (frobeniusColimitStageTripleUntwistIso p e q hZ hX' hE n j Ec Em
      ((frobeniusPullbackIter E p hE j).mapIso φ)).symm

/-- The free module of rank `r` on a scheme, as an object of `Vect`. -/
noncomputable def Scheme.Vect.freeRank (Y : Scheme.{u}) (r : ℕ) : Y.Vect :=
  ⟨_root_.SheafOfModules.free (ULift.{u} (Fin r)),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r
      (hM := AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free r)⟩

/-- **The stage image of a free module is free.** -/
noncomputable def frobeniusStageFunctorObjFreeIso (Y : Scheme.{u}) (hY : IsInCharacteristic Y p)
    (n r : ℕ) :
    (frobeniusStageFunctor Y p hY n).obj (Scheme.Vect.freeRank Y r) ≅
      ⟨_root_.SheafOfModules.free (ULift.{u} (Fin r)),
        isFiniteLocallyFreeFrobeniusColimitFree p hY (ULift.{u} (Fin r))⟩ :=
  ObjectProperty.isoMk _
    (_root_.SheafOfModules.pullbackObjFreeIso (frobeniusStageStructureMap Y p hY n) _)

/-- **The iterated Frobenius pullback of a free module is free.** -/
noncomputable def frobeniusPullbackIterObjFreeIso (Y : Scheme.{u}) (hY : IsInCharacteristic Y p)
    (j r : ℕ) :
    (frobeniusPullbackIter Y p hY j).obj (Scheme.Vect.freeRank Y r) ≅ Scheme.Vect.freeRank Y r :=
  (frobeniusPullbackIterIso Y p hY j).app _ ≪≫
    ObjectProperty.isoMk _ (Scheme.Modules.pullbackFreeIso _ _)

/-- **A finite locally free module whose stage image is free becomes free after a Frobenius
pullback**, on a quasi-compact quasi-separated scheme. -/
theorem exists_frobeniusPullbackIter_iso_free_of_stage (Y : Scheme.{u})
    (hY : IsInCharacteristic Y p) [CompactSpace Y] [QuasiSeparatedSpace Y] (n r : ℕ)
    (M : Y.Vect)
    (ω : (frobeniusStageFunctor Y p hY n).obj M ≅
      ⟨_root_.SheafOfModules.free (ULift.{u} (Fin r)),
        isFiniteLocallyFreeFrobeniusColimitFree p hY (ULift.{u} (Fin r))⟩) :
    ∃ j : ℕ, Nonempty ((frobeniusPullbackIter Y p hY j).obj M ≅ Scheme.Vect.freeRank Y r) := by
  obtain ⟨k, u, -⟩ := exists_frobeniusStageIso_hom_eq Y p hY n M (Scheme.Vect.freeRank Y r)
    (ω ≪≫ (frobeniusStageFunctorObjFreeIso p Y hY n r).symm)
  exact ⟨n + k, ⟨u ≪≫ frobeniusPullbackIterObjFreeIso p Y hY (n + k) r⟩⟩

end General

section TwoGenerator

open Stacks.AlmostBlowUp

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A) (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0)

include hpA

/-- **The local case of [Stacks, Tag 0EXD].**  Let `A` be a ring in which the prime `p` vanishes
and `f₁, f₂ ∈ A`.  An object `T` of the categorical fibre product of the Frobenius colimits over
the almost blowup square of [Stacks, Example 0EVH] which is isomorphic to the stage triple of an
ordinary triple `(ℰ, 𝒢, φ)` whose module `ℰ` on the centre is free is in the essential image of
the comparison functor `AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison`.

The ordinary solution is `Stacks.AlmostBlowUp.exists_vect_iso_of_free_center`, which needs no
Noetherian hypothesis; it is carried to the Frobenius colimits by
`AlgebraicGeometry.frobeniusColimitVectorBundlesComparisonStageIsoOfIso`. -/
theorem exists_twoGeneratorFrobeniusColimitComparison_iso_of_stageTriple (r n : ℕ)
    (Ec : (Spec (.of (centerRing A f₁ f₂))).Vect)
    (Em : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Vect)
    (φ : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Vect.pullback (exceptionalToCenter A f₁ f₂)).obj Ec ≅
        (Scheme.Vect.pullback (exceptionalToModification A f₁ f₂)).obj Em)
    (hEc : Nonempty (Ec.obj ≅ _root_.SheafOfModules.free (ULift.{u} (Fin r))))
    (T : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (exceptionalToCenter A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA))
        (frobeniusColimitVectorBundlesPullback p (exceptionalToModification A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)))
    (hT : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      Nonempty (T ≅ frobeniusColimitStageTriple p (exceptionalToCenter A f₁ f₂)
        (exceptionalToModification A f₁ f₂)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA) n 0 Ec Em φ)) :
    ∃ N : frobeniusColimitVectorBundles (Spec (.of A)) p (isInCharacteristic_spec A p hpA),
      Nonempty ((twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).obj N ≅ T) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  obtain ⟨N, ⟨i⟩⟩ := exists_vect_iso_of_free_center A f₁ f₂ r Ec Em φ hEc
  obtain ⟨j⟩ := hT
  exact ⟨(frobeniusStageFunctor _ p (isInCharacteristic_spec A p hpA) n).obj N,
    ⟨frobeniusColimitVectorBundlesComparisonStageIsoOfIso p (modificationToBase A f₁ f₂)
      (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
      (isInCharacteristic_spec A p hpA)
      (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
      (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
      (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
      (twoGenerator_isPullback A f₁ f₂).w n N i ≪≫ j.symm⟩⟩

/-- **The local case of [Stacks, Tag 0EXD], at the level of Frobenius colimits.**  Let `A` be a
ring in which the prime `p` vanishes and `f₁, f₂ ∈ A`.  An object `T` of the categorical fibre
product `colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')` over the almost blowup square of
[Stacks, Example 0EVH] whose component on the centre is free is in the essential image of the
comparison functor `AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison`.

`T` is a stage triple of ordinary modules at twist `0`
(`AlgebraicGeometry.exists_frobeniusColimitStageTriple_zero_iso`); its module on the centre has
free stage image, hence becomes free after a Frobenius pullback
(`AlgebraicGeometry.exists_frobeniusPullbackIter_iso_free_of_stage`), and raising the stage
(`AlgebraicGeometry.frobeniusColimitStageTripleRaiseIso`) brings the triple to one with free
module on the centre, which
`AlgebraicGeometry.exists_twoGeneratorFrobeniusColimitComparison_iso_of_stageTriple` solves. -/
theorem mem_essImage_twoGeneratorFrobeniusColimitComparison_of_free_center
    (T : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (exceptionalToCenter A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA))
        (frobeniusColimitVectorBundlesPullback p (exceptionalToModification A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)))
    (I : Type u) [Finite I]
    (hfree : Nonempty (T.fst ≅ ⟨_root_.SheafOfModules.free I,
      isFiniteLocallyFreeFrobeniusColimitFree p
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA) I⟩)) :
    (twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).essImage T := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hMc : CompactSpace (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)) :=
    compactSpace_proj_modificationGrading A f₁ f₂
  have hEc : CompactSpace (AlgebraicGeometry.Proj (exceptionalGrading A f₁ f₂)) :=
    Stacks.ProjAmple.compactSpace_proj_polyGrading (centerRing A f₁ f₂) 1
  have hZ := isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA
  have hM := isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA
  have hE := isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA
  obtain ⟨n, Ec, Em, φ, ⟨iT⟩⟩ := exists_frobeniusColimitStageTriple_zero_iso p
    (exceptionalToCenter A f₁ f₂) (exceptionalToModification A f₁ f₂) hZ hM hE T
  obtain ⟨r, ⟨eI⟩⟩ := Finite.exists_equiv_fin I
  obtain ⟨ε⟩ := hfree
  let eFree : (⟨_root_.SheafOfModules.free I, isFiniteLocallyFreeFrobeniusColimitFree p hZ I⟩ :
      frobeniusColimitVectorBundles _ p hZ) ≅
      ⟨_root_.SheafOfModules.free (ULift.{u} (Fin r)),
        isFiniteLocallyFreeFrobeniusColimitFree p hZ (ULift.{u} (Fin r))⟩ :=
    ObjectProperty.isoMk _
      (_root_.SheafOfModules.freeFunctor.mapIso (eI.trans Equiv.ulift.symm).toIso)
  obtain ⟨j, ⟨u⟩⟩ := exists_frobeniusPullbackIter_iso_free_of_stage p _ hZ n r Ec
    ((CategoricalPullback.π₁ _ _).mapIso iT.symm ≪≫ ε ≪≫ eFree)
  let φ₀ : (Scheme.Vect.pullback (exceptionalToCenter A f₁ f₂)).obj Ec ≅
      (Scheme.Vect.pullback (exceptionalToModification A f₁ f₂)).obj Em := φ
  obtain ⟨N, ⟨iN⟩⟩ := exists_twoGeneratorFrobeniusColimitComparison_iso_of_stageTriple A f₁ f₂ p
    hpA r (n + j) ((frobeniusPullbackIter _ p hZ j).obj Ec)
    ((frobeniusPullbackIter _ p hM j).obj Em)
    (frobeniusStageTripleUntwist p _ _ hZ hM hE j Ec Em
      ((frobeniusPullbackIter _ p hE j).mapIso φ₀))
    ⟨(ObjectProperty.ι _).mapIso u ≪≫ Iso.refl _⟩ T
    ⟨iT ≪≫ frobeniusColimitStageTripleRaiseIso p (exceptionalToModification A f₁ f₂)
      (exceptionalToCenter A f₁ f₂) hM hZ hE n j Ec Em φ₀⟩
  exact ⟨N, ⟨iN⟩⟩

end TwoGenerator

end AlgebraicGeometry

end
