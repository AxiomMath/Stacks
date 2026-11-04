module

public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.FilteredKInjectiveResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The spectral sequence of a filtered complex under a morphism of ringed spaces

Let `f : (X, O_X) ⟶ (Y, O_Y)` be a morphism of ringed spaces and let `F^•` be a filtered complex
of `O_X`-modules. Applying `f_*` degreewise to a filtered K-injective resolution of `F^•`
produces a filtered complex of `O_Y`-modules, whose filtered-complex spectral sequence is the
relative spectral sequence of `F^•`: a cohomological spectral sequence `(E_r, d_r)_{r ≥ 1}` of
bigraded `O_Y`-modules with `d_r` of bidegree `(r, -r + 1)` and
```
E_1^{p, q} = R^{p + q}f_*gr^pF^•.
```
If for every `n` the higher direct image `R^nf_*F^pF^•` vanishes for `p ≫ 0` and agrees with
`R^nf_*F^•` for `p ≪ 0`, the spectral sequence is bounded and converges to `R^*f_*F^•`.

## Main definitions

* `Stacks.Cohomology.FilteredComplex.higherDirectImage` and
  `Stacks.Cohomology.FilteredComplex.higherDirectImageMap`: the higher direct images
  `R^nf_*K^•` of a complex of `O_X`-modules, computed by an unbounded derived pushforward, and
  their functoriality.
* `Stacks.Cohomology.FilteredComplex.pushforwardToHigherDirectImage`: the comparison from the
  cohomology of the pushed-forward complex to the higher direct images, as a natural
  transformation.
* `Stacks.Cohomology.FilteredComplex.pushforwardFilteredComplex` and
  `Stacks.Cohomology.FilteredComplex.pushforwardSpectralSequence`: `f_*`, applied degreewise to
  a filtered complex, and the resulting filtered-complex spectral sequence.

## Main results

* `Stacks.Cohomology.FilteredComplex.isIso_pushforwardToHigherDirectImage_app`: the comparison
  is invertible at a K-injective complex.
* `Stacks.Cohomology.FilteredComplex.relativeSpectralSequence_of_filteredKInjectiveResolution`:
  the first page and the conditional bounded convergence, for a supplied filtered K-injective
  resolution.
* `Stacks.Cohomology.FilteredComplex.exists_relativeSpectralSequence_of_filteredComplex`: such a
  resolution, a derived pushforward functor and the resulting spectral sequence exist for every
  filtered complex of `O_X`-modules.

## Implementation notes

The derived pushforward functor and its derived-functor unit are inputs of the first result,
together with the filtered resolution, so that all of its conclusions concern the same data; the
second result chooses them. The resolution data are those of [Stacks, Tag 0BKI], reused from the
absolute case: the resolution, its filtration steps and its graded pieces must all be
K-injective, since termwise injectivity alone does not compute unbounded derived pushforward.

The spectral sequence is not specified merely by its first page: it is the canonical
cycle-and-boundary spectral sequence of the pushed-forward filtered complex, so its differentials
are the maps induced by the complex differential and have bidegree `(r, -r + 1)` by construction.
Convergence is stated by identifying the infinity page with the associated graded of the finite
decreasing filtration induced on the higher direct images.

Both spaces, their structure rings and the module sheaves share one universe, as the
ringed-space module API requires.

## References

* [Stacks Project, Tag 0FLL](https://stacks.math.columbia.edu/tag/0FLL)
* [Stacks Project, Tag 0BKK](https://stacks.math.columbia.edu/tag/0BKK)
* [Stacks Project, Tag 0BKI](https://stacks.math.columbia.edu/tag/0BKI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.FilteredComplex

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}}

attribute [local instance] modulePushforward_isRightAdjoint

/-- The zero subobject of a sheaf of modules; spelled out because the instance search for the
initial object of a category of sheaves of modules does not reach it on its own. -/
local instance subobjectOrderBot (M : SheafOfModules.{u} (structureSheafRing Y)) :
    OrderBot (Subobject M) :=
  CategoryTheory.Subobject.orderBot

variable (f : X ⟶ Y)

/-- Pushforward of modules along a morphism of ringed spaces, applied degreewise to complexes. -/
abbrev pushforwardComplexFunctor :
    CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ :=
  (modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The homotopy-category functor whose unbounded right derived functor is `Rf_*`. -/
abbrev homotopyPushforward :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The `n`-th higher direct image `R^nf_*K^•` of a complex of `O_X`-modules, computed by an
unbounded derived pushforward functor `Rf_*`. -/
abbrev higherDirectImage
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ) :
    SheafOfModules.{u} (structureSheafRing Y) :=
  (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n).obj
    (Rf.obj (DerivedCategory.Q.obj K))

/-- The map on higher direct images induced by a map of complexes. -/
abbrev higherDirectImageMap
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (g : K ⟶ L) (n : ℤ) :
    higherDirectImage Rf K n ⟶ higherDirectImage Rf L n :=
  (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n).map
    (Rf.map (DerivedCategory.Q.map g))

/-- **The comparison from the cohomology of the pushed-forward complex to the higher direct
images.** It is assembled from the unit `η` of the derived pushforward and the three natural
isomorphisms identifying homology on complexes, on the homotopy category and on the derived
category; being a natural transformation, it is automatically compatible with maps of
complexes. -/
def pushforwardToHigherDirectImage
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (η : homotopyPushforward f ⟶ DerivedCategory.Qh ⋙ Rf) (n : ℤ) :
    pushforwardComplexFunctor f ⋙
        HomologicalComplex.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ) n ⟶
      DerivedCategory.Q ⋙ Rf ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n :=
  Functor.whiskerLeft (pushforwardComplexFunctor f)
      (HomotopyCategory.homologyFunctorFactors
        (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ) n).inv ≫
    Functor.whiskerLeft (pushforwardComplexFunctor f ⋙
        HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctorFactorsh (SheafOfModules.{u} (structureSheafRing Y)) n).inv ≫
    Functor.whiskerRight
      ((modulePushforward f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv
      (DerivedCategory.Qh ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft
        (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)) η)
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n) ≫
    Functor.whiskerRight
      (Functor.whiskerRight
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom Rf)
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n)

/-- Every complex of `O_X`-modules admits a quasi-isomorphism to a K-injective complex, so the
derived pushforward exists as a pointwise right derived functor. -/
lemma hasPointwiseRightDerivedFunctor_homotopyPushforward :
    (homotopyPushforward f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) := inferInstance
  have h := Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (A := SheafOfModules.{u} (structureSheafRing X)) (homotopyPushforward f)
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _)
  have := h.2 (D := DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
  exact h.1

/-- The unit of a right-derived pushforward functor is invertible at a K-injective complex. -/
lemma isIso_pushforwardUnit_app_of_isKInjective
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (η : homotopyPushforward f ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective) :
    IsIso (η.app ((HomotopyCategory.quotient
      (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)).obj I)) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) := inferInstance
  have h := Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (A := SheafOfModules.{u} (structureSheafRing X)) (homotopyPushforward f)
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _)
  exact h.2 DerivedCategory.Qh Rf η I hI

/-- At a K-injective complex the comparison with the higher direct images is invertible. -/
instance isIso_pushforwardToHigherDirectImage_app
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (η : homotopyPushforward f ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] (n : ℤ) :
    IsIso ((pushforwardToHigherDirectImage f Rf η n).app I) := by
  have := isIso_pushforwardUnit_app_of_isKInjective f Rf η I inferInstance
  dsimp only [pushforwardToHigherDirectImage]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- At a K-injective complex, the higher direct images are the cohomology of the pushed-forward
complex. -/
def higherDirectImageIsoPushforwardHomology
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (η : homotopyPushforward f ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] (n : ℤ) :
    higherDirectImage Rf I n ≅ ((pushforwardComplexFunctor f).obj I).homology n :=
  (asIso ((pushforwardToHigherDirectImage f Rf η n).app I)).symm

/-- The identification of the higher direct images with the cohomology of the pushed-forward
complex is compatible with maps of K-injective complexes. -/
lemma higherDirectImageIsoPushforwardHomology_naturality
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (η : homotopyPushforward f ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    {I J : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    [I.IsKInjective] [J.IsKInjective] (g : I ⟶ J) (n : ℤ) :
    higherDirectImageMap Rf g n ≫
        (higherDirectImageIsoPushforwardHomology f Rf η J n).hom =
      (higherDirectImageIsoPushforwardHomology f Rf η I n).hom ≫
        HomologicalComplex.homologyMap ((pushforwardComplexFunctor f).map g) n := by
  have h : CommSq (HomologicalComplex.homologyMap ((pushforwardComplexFunctor f).map g) n)
      (asIso ((pushforwardToHigherDirectImage f Rf η n).app I)).hom
      (asIso ((pushforwardToHigherDirectImage f Rf η n).app J)).hom
      (higherDirectImageMap Rf g n) :=
    ⟨(pushforwardToHigherDirectImage f Rf η n).naturality g⟩
  exact h.vert_inv.w

/-- The filtered complex of `O_Y`-modules obtained by applying `f_*` degreewise to a filtered
complex of `O_X`-modules. -/
def pushforwardFilteredComplex
    (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) :
    CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing Y)) :=
  J.mapOfMono (pushforwardComplexFunctor f) (fun _ => inferInstance)

/-- The underlying complex of `pushforwardFilteredComplex f J` is the pushforward `f_*` of the
underlying complex of `J`. -/
@[simp]
lemma pushforwardFilteredComplex_X
    (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) :
    (pushforwardFilteredComplex f J).X = (pushforwardComplexFunctor f).obj J.X :=
  rfl

/-- The `p`-th filtration step of `pushforwardFilteredComplex f J` is the pushforward `f_*` of the
`p`-th filtration step of `J`. -/
lemma pushforwardFilteredComplex_filtration_obj
    (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (p : ℤᵒᵖ) :
    (pushforwardFilteredComplex f J).filtration.obj p =
      (pushforwardComplexFunctor f).obj (J.filtration.obj p) :=
  rfl

/-- The inclusion of the `p`-th filtration step of `pushforwardFilteredComplex f J` is the
pushforward `f_*` of the inclusion of the `p`-th filtration step of `J`. -/
@[simp]
lemma pushforwardFilteredComplex_filtration_ι_app
    (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (p : ℤᵒᵖ) :
    (pushforwardFilteredComplex f J).filtration.ι.app p =
      (pushforwardComplexFunctor f).map (J.filtration.ι.app p) :=
  rfl

/-- The filtered-complex spectral sequence of the pushforward of a filtered complex of
`O_X`-modules: a cohomological spectral sequence of `O_Y`-modules whose `r`-th differential has
bidegree `(r, -r + 1)`. -/
abbrev pushforwardSpectralSequence
    (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) :
    CohomologicalSpectralSequence (SheafOfModules.{u} (structureSheafRing Y)) 0 :=
  CochainComplex.Filtered.spectralSequenceFunctor.obj (pushforwardFilteredComplex f J)

/-- The first page of the spectral sequence of a filtered complex is the cohomology of its
graded pieces. -/
@[ega "0 11.2.2" "partial", sga "4 Vbis 2.5.2" "(X)"]
lemma nonempty_firstPageIso_gradedPieceHomology {C : Type*} [Category* C] [Abelian C]
    (M : CochainComplex.Filtered C) (p q : ℤ) :
    Nonempty (((CochainComplex.Filtered.spectralSequenceFunctor.obj M).page 1
        (by omega)).X (p, q) ≅ ((FilteredObject.gr p).obj M).homology (p + q)) := by
  obtain ⟨_, _, _, h⟩ := FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage
    M (CochainComplex.filtrationSubobject M) (fun _ _ => rfl)
    (CochainComplex.filtrationSubobject_antitone M)
  exact h p q (p + q) rfl

section Resolution

variable
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (η : homotopyPushforward f ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    {K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))}
    (R : FilteredKInjectiveResolution X K)

/-- The map on higher direct images is functorial. -/
private lemma higherDirectImageMap_comp {A B C : CochainComplex (SheafOfModules.{u}
    (structureSheafRing X)) ℤ} (g : A ⟶ B) (h : B ⟶ C) (n : ℤ) :
    higherDirectImageMap Rf (g ≫ h) n = higherDirectImageMap Rf g n ≫ higherDirectImageMap Rf h n :=
  by simp only [higherDirectImageMap, Functor.map_comp]

include η in
/-- The higher direct images of a filtration step of `K` are the cohomology of the corresponding
filtration step of the pushed-forward resolution. -/
def pushforwardCmpStep (p n : ℤ) :
    higherDirectImage Rf (K.filtration.obj (op p)) n ≅
      ((pushforwardFilteredComplex f R.obj).filtration.obj (op p)).homology n := by
  letI := R.isKInjective_step p
  letI : QuasiIso (R.map.natTrans.app (op p)) := R.quasiIso_step p
  exact (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n).mapIso
      (Rf.mapIso (asIso (DerivedCategory.Q.map (R.map.natTrans.app (op p))))) ≪≫
    higherDirectImageIsoPushforwardHomology f Rf η (R.obj.filtration.obj (op p)) n

include η in
/-- The higher direct images of `K` are the cohomology of the pushed-forward resolution. -/
def pushforwardCmpTotal (n : ℤ) :
    higherDirectImage Rf K.X n ≅ (pushforwardFilteredComplex f R.obj).X.homology n := by
  letI := R.isKInjective
  letI : QuasiIso R.map.hom := R.quasiIso
  exact (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n).mapIso
      (Rf.mapIso (asIso (DerivedCategory.Q.map R.map.hom))) ≪≫
    higherDirectImageIsoPushforwardHomology f Rf η R.obj.X n

/-- The comparisons of the higher direct images with the cohomology of the pushed-forward
resolution are compatible with the inclusion of a filtration step. -/
lemma pushforward_cmp_square (p n : ℤ) :
    (pushforwardCmpStep f Rf η R p n).hom ≫
        HomologicalComplex.homologyMap
          ((pushforwardFilteredComplex f R.obj).filtration.ι.app (op p)) n =
      higherDirectImageMap Rf (K.filtration.ι.app (op p)) n ≫
        (pushforwardCmpTotal f Rf η R n).hom := by
  have := R.isKInjective
  have := R.isKInjective_step p
  have : QuasiIso (R.map.natTrans.app (op p)) := R.quasiIso_step p
  have : QuasiIso R.map.hom := R.quasiIso
  have hnat := higherDirectImageIsoPushforwardHomology_naturality f Rf η
    (I := R.obj.filtration.obj (op p)) (J := R.obj.X)
    (R.obj.filtration.ι.app (op p) : R.obj.filtration.obj (op p) ⟶ R.obj.X) n
  have hcomm : R.map.natTrans.app (op p) ≫ R.obj.filtration.ι.app (op p) =
      K.filtration.ι.app (op p) ≫ R.map.hom := R.map.comm (op p)
  have hmapComm : higherDirectImageMap Rf (R.map.natTrans.app (op p)) n ≫
      higherDirectImageMap Rf (R.obj.filtration.ι.app (op p)) n =
      higherDirectImageMap Rf (K.filtration.ι.app (op p)) n ≫
        higherDirectImageMap Rf R.map.hom n := by
    rw [← higherDirectImageMap_comp, ← higherDirectImageMap_comp, hcomm]
  show (higherDirectImageMap Rf (R.map.natTrans.app (op p)) n ≫
        (higherDirectImageIsoPushforwardHomology f Rf η
          (R.obj.filtration.obj (op p)) n).hom) ≫
      HomologicalComplex.homologyMap
        ((pushforwardComplexFunctor f).map (R.obj.filtration.ι.app (op p))) n =
    higherDirectImageMap Rf (K.filtration.ι.app (op p)) n ≫
      higherDirectImageMap Rf R.map.hom n ≫
        (higherDirectImageIsoPushforwardHomology f Rf η R.obj.X n).hom
  rw [Category.assoc, ← hnat, ← Category.assoc, hmapComm]
  simp only [Category.assoc]

include η in
/-- Eventual vanishing of the higher direct images of the filtration steps transports to the
pushed-forward resolution. -/
lemma pushforward_eventually_isZero_homology {n p₀ : ℤ}
    (h : ∀ p : ℤ, p₀ ≤ p → IsZero (higherDirectImage Rf (K.filtration.obj (op p)) n)) (p : ℤ)
    (hp : p₀ ≤ p) :
    IsZero (((pushforwardFilteredComplex f R.obj).filtration.obj (op p)).homology n) :=
  IsZero.of_iso (h p hp) (pushforwardCmpStep f Rf η R p n).symm

include η in
/-- Eventual invertibility of the maps on higher direct images transports to the pushed-forward
resolution. -/
lemma pushforward_eventually_isIso_homologyMap {n p₁ : ℤ}
    (h : ∀ p : ℤ, p ≤ p₁ → IsIso (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n))
    (p : ℤ) (hp : p ≤ p₁) :
    IsIso (HomologicalComplex.homologyMap
      ((pushforwardFilteredComplex f R.obj).filtration.ι.app (op p)) n) := by
  have := h p hp
  have hformula : HomologicalComplex.homologyMap
      ((pushforwardFilteredComplex f R.obj).filtration.ι.app (op p)) n =
      (pushforwardCmpStep f Rf η R p n).inv ≫
        higherDirectImageMap Rf (K.filtration.ι.app (op p)) n ≫
          (pushforwardCmpTotal f Rf η R n).hom := by
    rw [← pushforward_cmp_square f Rf η R p n]
    simp
  rw [hformula]
  infer_instance

include η in
/-- The first page of the spectral sequence of the pushed-forward resolution consists of the
higher direct images of the graded pieces of `K`. -/
lemma nonempty_pushforwardFirstPageIso (p q : ℤ) :
    Nonempty
      (((pushforwardSpectralSequence f R.obj).page 1 (by omega)).X (p, q) ≅
        higherDirectImage (X := X) (Y := Y) Rf ((FilteredObject.gr p).obj K) (p + q)) := by
  obtain ⟨ePage⟩ := nonempty_firstPageIso_gradedPieceHomology
    (C := SheafOfModules.{u} (structureSheafRing Y)) (pushforwardFilteredComplex f R.obj) p q
  have := R.isKInjective_gr p
  have : QuasiIso ((FilteredObject.gr p).map R.map) := R.quasiIso_gr p
  let egr : (FilteredObject.gr p).obj (pushforwardFilteredComplex f R.obj) ≅
      (pushforwardComplexFunctor f).obj ((FilteredObject.gr p).obj R.obj) := by
    show cokernel ((pushforwardComplexFunctor f).map
        (R.obj.filtration.step (FilteredObject.succHom p))) ≅
      (pushforwardComplexFunctor f).obj
        (cokernel (R.obj.filtration.step (FilteredObject.succHom p)))
    exact CochainComplex.cokernelMapIsoOfInjective (modulePushforward f)
      (R.obj.filtration.step (FilteredObject.succHom p))
      (fun n => R.injective_step (p + 1) n)
  exact ⟨ePage ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (p + q)).mapIso egr ≪≫
    (higherDirectImageIsoPushforwardHomology f Rf η
      ((FilteredObject.gr p).obj R.obj) (p + q)).symm ≪≫
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) (p + q)).mapIso
      (Rf.mapIso (asIso (DerivedCategory.Q.map ((FilteredObject.gr p).map R.map))))).symm⟩

include η in
/-- Eventual vanishing and eventual invertibility of the higher direct images of the filtration
steps, transported to the pushed-forward resolution. -/
lemma pushforward_eventually_homology_bounds
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (higherDirectImage Rf (K.filtration.obj (op p)) n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n)) :
    (∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p → IsZero
      (((pushforwardFilteredComplex f R.obj).filtration.obj (op p)).homology n)) ∧
      ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ → IsIso (HomologicalComplex.homologyMap
        ((pushforwardFilteredComplex f R.obj).filtration.ι.app (op p)) n) :=
  ⟨fun n => ⟨(hzero n).choose,
      pushforward_eventually_isZero_homology f Rf η R (hzero n).choose_spec⟩,
    fun n => ⟨(hiso n).choose,
      pushforward_eventually_isIso_homologyMap f Rf η R (hiso n).choose_spec⟩⟩

/-- The images of the higher direct images of the filtration steps of `K` in those of `K` form a
decreasing filtration. -/
private lemma antitone_imageSubobject_higherDirectImageMap (n : ℤ) :
    Antitone (fun p : ℤ => (imageSubobject
      (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n) :
        Subobject (higherDirectImage Rf K.X n))) := by
  intro p p' hpp'
  have hcomp : K.filtration.diagram.map (homOfLE hpp').op ≫ K.filtration.ι.app (op p) =
      K.filtration.ι.app (op p') := K.filtration.diagram_map_comp_ι_app _
  have hmap : higherDirectImageMap Rf (K.filtration.diagram.map (homOfLE hpp').op) n ≫
      higherDirectImageMap Rf (K.filtration.ι.app (op p)) n =
      higherDirectImageMap Rf (K.filtration.ι.app (op p')) n := by
    rw [← higherDirectImageMap_comp, hcomp]
  apply imageSubobject_le (higherDirectImageMap Rf (K.filtration.ι.app (op p')) n)
    (higherDirectImageMap Rf (K.filtration.diagram.map (homOfLE hpp').op) n ≫
      factorThruImageSubobject
        (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n))
  calc
    _ = higherDirectImageMap Rf (K.filtration.diagram.map (homOfLE hpp').op) n ≫
        higherDirectImageMap Rf (K.filtration.ι.app (op p)) n := by simp
    _ = _ := hmap

/-- If the higher direct images of the filtration steps of `K` map isomorphically to those of `K`
on the left and vanish on the right, the induced filtration is everything on the left and zero on
the right. -/
private lemma exists_imageSubobject_higherDirectImageMap_eq_top_eq_bot {n p₀ p₁ : ℤ}
    (hiso : ∀ p : ℤ, p ≤ p₀ → IsIso (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n))
    (hzero : ∀ p : ℤ, p₁ ≤ p → IsZero (higherDirectImage Rf (K.filtration.obj (op p)) n)) :
    ∃ a b : ℤ, a ≤ b ∧
      imageSubobject (higherDirectImageMap Rf (K.filtration.ι.app (op a)) n) = ⊤ ∧
      imageSubobject (higherDirectImageMap Rf (K.filtration.ι.app (op b)) n) = ⊥ := by
  refine ⟨p₀, max p₀ p₁, le_max_left _ _, ?_, ?_⟩
  · have := hiso p₀ le_rfl
    exact Subobject.imageSubobject_eq_top_of_epi _
  · rw [show higherDirectImageMap Rf (K.filtration.ι.app (op (max p₀ p₁))) n = 0 from
      (hzero _ (le_max_right _ _)).eq_of_src _ _, imageSubobject_zero]

/-- Transported along the comparison with the cohomology of the pushed-forward resolution, the
filtration induced on its cohomology is the image filtration on the higher direct images of
`K`. -/
private lemma mapIsoToOrderIso_inducedFiltrationStep (n s : ℤ) :
    (Subobject.mapIsoToOrderIso (pushforwardCmpTotal f Rf η R n).symm)
        ((pushforwardFilteredComplex f R.obj).inducedFiltrationStep n s) =
      imageSubobject (higherDirectImageMap Rf (K.filtration.ι.app (op s)) n) := by
  have hImage :
      (Subobject.map (pushforwardCmpTotal f Rf η R n).hom).obj (imageSubobject
          (higherDirectImageMap Rf (K.filtration.ι.app (op s)) n)) =
        (pushforwardFilteredComplex f R.obj).inducedFiltrationStep n s := by
    rw [Subobject.map_imageSubobject (higherDirectImageMap Rf (K.filtration.ι.app (op s)) n)
      (pushforwardCmpTotal f Rf η R n)]
    calc
      _ = imageSubobject ((pushforwardCmpStep f Rf η R s n).hom ≫
          HomologicalComplex.homologyMap
            ((pushforwardFilteredComplex f R.obj).filtration.ι.app (op s)) n) := by
        congr 1
        exact (pushforward_cmp_square f Rf η R s n).symm
      _ = _ := imageSubobject_iso_comp (pushforwardCmpStep f Rf η R s n).hom _
  show (Subobject.map (pushforwardCmpTotal f Rf η R n).inv).obj
      ((pushforwardFilteredComplex f R.obj).inducedFiltrationStep n s) =
    imageSubobject (higherDirectImageMap Rf (K.filtration.ι.app (op s)) n)
  rw [← hImage]
  simp_rw [← Subobject.map_comp, Iso.hom_inv_id, Subobject.map_id]

include η in
/-- **Convergence.** If the higher direct images of the filtration steps of `K` eventually vanish
on the right and eventually map isomorphically to those of `K` on the left, then the spectral
sequence of the pushed-forward resolution is bounded, the induced filtration on the higher direct
images of `K` is finite, and the infinity page is its associated graded. -/
lemma pushforward_converges
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (higherDirectImage Rf (K.filtration.obj (op p)) n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n)) :
    (∀ n : ℤ, {p : ℤ | ¬ IsZero
      (((pushforwardSpectralSequence f R.obj).page 1 (by omega)).X (p, n - p))}.Finite) ∧
      ∃ (F : ∀ n : ℤ, ℤ → Subobject (higherDirectImage Rf K.X n))
        (hF : ∀ n : ℤ, Antitone (F n)),
        (∀ n p : ℤ, F n p = imageSubobject
          (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n)) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
        (∀ p q : ℤ, (pushforwardSpectralSequence f R.obj).HasPageInfinityAt (p, q)) ∧
        ∀ p q : ℤ, Nonempty
          ((pushforwardSpectralSequence f R.obj).pageInfinity (p, q) ≅
            cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
              (hF (p + q) (by omega)))) := by
  classical
  obtain ⟨hzeroP, hisoP⟩ := pushforward_eventually_homology_bounds f Rf η R hzero hiso
  refine ⟨CochainComplex.Filtered.finite_not_isZero_page_one _ hzeroP hisoP,
    (fun n p => (imageSubobject (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n) :
      Subobject (higherDirectImage Rf K.X n))),
    antitone_imageSubobject_higherDirectImageMap Rf (K := K), fun _ _ => rfl,
    fun n => exists_imageSubobject_higherDirectImageMap_eq_top_eq_bot Rf
      (hiso n).choose_spec (hzero n).choose_spec,
    fun p q => CochainComplex.Filtered.hasPageInfinityAt_of_eventually _ hzeroP hisoP (p, q),
    fun p q => ?_⟩
  obtain ⟨eGr⟩ := CochainComplex.Filtered.nonempty_pageInfinityIso_inducedFiltrationStep
    _ hzeroP hisoP p q
  have hleFH :
      (pushforwardFilteredComplex f R.obj).inducedFiltrationStep (p + q) (p + 1) ≤
        (pushforwardFilteredComplex f R.obj).inducedFiltrationStep (p + q) p :=
    (pushforwardFilteredComplex f R.obj).inducedFiltrationStep_antitone (p + q) (by omega)
  exact ⟨eGr ≪≫
    Subobject.cokernelMapIso (pushforwardCmpTotal f Rf η R (p + q)).symm _ _ hleFH ≪≫
    Subobject.cokernelOfLEIsoOfEq
      ((Subobject.mapIsoToOrderIso
        (pushforwardCmpTotal f Rf η R (p + q)).symm).map_rel_iff'.2 hleFH)
      (antitone_imageSubobject_higherDirectImageMap Rf (p + q) (show p ≤ p + 1 by omega))
      (mapIsoToOrderIso_inducedFiltrationStep f Rf η R (p + q) (p + 1))
      (mapIsoToOrderIso_inducedFiltrationStep f Rf η R (p + q) p)⟩

end Resolution

section Statement

variable
    (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (η : homotopyPushforward f ⟶ DerivedCategory.Qh ⋙ Rf)
    (K J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X)))

/-- **Stacks 0FLL**, the first page and the conditional bounded convergence, for a supplied
filtered K-injective resolution. The right-derived pushforward, its unit and the resolution are
fixed inputs, so all of the conclusions concern these same data. -/
@[stacks 0FLL "computation by a supplied filtered K-injective resolution"]
theorem relativeSpectralSequence_of_filteredKInjectiveResolution
    (hRf : Rf.IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    (j : K ⟶ J)
    (hj : QuasiIso j.hom)
    (hjStep : ∀ p : ℤ, QuasiIso (j.natTrans.app (op p)))
    (hjGraded : ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map j))
    (hStepInjective : ∀ p n : ℤ, Injective ((J.filtration.obj (op p)).X n))
    (hKInjective : J.X.IsKInjective)
    (hStepKInjective : ∀ p : ℤ, (J.filtration.obj (op p)).IsKInjective)
    (hGradedKInjective : ∀ p : ℤ, ((FilteredObject.gr p).obj J).IsKInjective) :
    let E := pushforwardSpectralSequence f J
    (∀ p q : ℤ, Nonempty
      ((E.page 1 (by omega)).X (p, q) ≅
        higherDirectImage (X := X) (Y := Y) Rf ((FilteredObject.gr p).obj K) (p + q))) ∧
      ((∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
          IsZero (higherDirectImage Rf (K.filtration.obj (op p)) n)) →
        (∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
          IsIso (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n)) →
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) ∧
          ∃ (F : ∀ n : ℤ, ℤ → Subobject (higherDirectImage Rf K.X n))
            (hF : ∀ n : ℤ, Antitone (F n)),
            (∀ n p : ℤ, F n p = imageSubobject
              (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n)) ∧
            (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
            (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
            ∀ p q : ℤ, Nonempty
              (E.pageInfinity (p, q) ≅
                cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
                  (hF (p + q) (by omega))))) := by
  let R : FilteredKInjectiveResolution X K :=
    { obj := J, map := j, quasiIso := hj, quasiIso_step := hjStep, quasiIso_gr := hjGraded
      injective_step := hStepInjective, isKInjective := hKInjective
      isKInjective_step := hStepKInjective, isKInjective_gr := hGradedKInjective }
  exact ⟨nonempty_pushforwardFirstPageIso f Rf η R, pushforward_converges f Rf η R⟩

/-- **Stacks 0FLL.** A filtered complex of `O_X`-modules has a canonical cohomological spectral
sequence of `O_Y`-modules, with `d_r` of bidegree `(r, -r + 1)`, whose first page is
`E_1^{p, q} = R^{p + q}f_*gr^pF^•`. If for every `n` the higher direct image
`R^nf_*F^pF^•` vanishes for `p ≫ 0` and maps isomorphically to `R^nf_*F^•` for `p ≪ 0`, the
spectral sequence is bounded and converges to `R^*f_*F^•`. -/
@[stacks 0FLL]
theorem exists_relativeSpectralSequence_of_filteredComplex :
    ∃ (Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
      (η : homotopyPushforward f ⟶ DerivedCategory.Qh ⋙ Rf),
      Rf.IsRightDerivedFunctor η
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) ∧
      ∃ (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (j : K ⟶ J),
      QuasiIso j.hom ∧
      (∀ p : ℤ, QuasiIso (j.natTrans.app (op p))) ∧
      (∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map j)) ∧
      (∀ n : ℤ, Injective (J.X.X n)) ∧
      (∀ p n : ℤ, Injective ((J.filtration.obj (op p)).X n)) ∧
      (∀ p n : ℤ, Injective (((FilteredObject.gr p).obj J).X n)) ∧
      (∀ p q : ℤ, Nonempty
        (((pushforwardSpectralSequence f J).page 1 (by omega)).X (p, q) ≅
          higherDirectImage (X := X) (Y := Y) Rf ((FilteredObject.gr p).obj K) (p + q))) ∧
      ((∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
          IsZero (higherDirectImage Rf (K.filtration.obj (op p)) n)) →
        (∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
          IsIso (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n)) →
        (∀ n : ℤ, {p : ℤ | ¬ IsZero
          (((pushforwardSpectralSequence f J).page 1 (by omega)).X (p, n - p))}.Finite) ∧
          ∃ (F : ∀ n : ℤ, ℤ → Subobject (higherDirectImage Rf K.X n))
            (hF : ∀ n : ℤ, Antitone (F n)),
            (∀ n p : ℤ, F n p = imageSubobject
              (higherDirectImageMap Rf (K.filtration.ι.app (op p)) n)) ∧
            (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
            (∀ p q : ℤ, (pushforwardSpectralSequence f J).HasPageInfinityAt (p, q)) ∧
            ∀ p q : ℤ, Nonempty
              ((pushforwardSpectralSequence f J).pageInfinity (p, q) ≅
                cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
                  (hF (p + q) (by omega))))) := by
  have hpt := hasPointwiseRightDerivedFunctor_homotopyPushforward f
  -- The twelve conclusions of [Stacks, Tag 0BKI] are read off by projection rather than
  -- destructured by `obtain`: each `obtain` step builds a motive over the conclusion above,
  -- which is large enough that twelve of them exceed the default heartbeat budget.
  obtain ⟨J, j, h⟩ := Stacks.Injectives.exists_filtered_quasiIso_isKInjective K
  have hI := h.1
  have hIStep := h.2.1
  have hKI := h.2.2.2.2.1
  have hKIStep := h.2.2.2.2.2.1
  have hj := h.2.2.2.2.2.2.2.2.1
  have hjStep := h.2.2.2.2.2.2.2.2.2.1
  have hIGraded (p n : ℤ) : Injective (((FilteredObject.gr p).obj J).X n) :=
    h.2.2.2.1 p (p + 1) (by omega) n
  have hKIGraded (p : ℤ) : ((FilteredObject.gr p).obj J).IsKInjective :=
    h.2.2.2.2.2.2.2.1 p (p + 1) (by omega)
  have hjGraded (p : ℤ) : QuasiIso ((FilteredObject.gr p).map j) :=
    h.2.2.2.2.2.2.2.2.2.2.2 p (p + 1) (by omega)
  -- The derived-functor property is synthesized once and then used twice.
  have hRf : ((homotopyPushforward f).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))).IsRightDerivedFunctor
      ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
    inferInstance
  exact ⟨_, _, hRf, J, j, hj, hjStep, hjGraded, hI, hIStep, hIGraded,
    relativeSpectralSequence_of_filteredKInjectiveResolution f _ _ K J hRf j hj hjStep hjGraded
      hIStep hKI hKIStep hKIGraded⟩

end Statement

end Stacks.Cohomology.FilteredComplex
