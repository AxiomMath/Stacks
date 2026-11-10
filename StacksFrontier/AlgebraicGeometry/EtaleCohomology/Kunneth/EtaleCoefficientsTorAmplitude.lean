module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsExactness
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowCanonical
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.InvertibilityAtShiftsReductions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor amplitude on `D(X_étale, Λ)`

Let `Λ` be a commutative ring and `X` a scheme. An object `E` of `D(X_étale, Λ)` has *Tor
amplitude in `[a, ∞]`* when `E ⊗^L_Λ F` has no cohomology below `a` for every sheaf of
`Λ̲`-modules `F` placed in degree zero ([Stacks, Tag 08FZ]). This file reads that predicate on the
derived categories `D(-_étale, Λ)` of `Stacks.EtaleCohomology.EtaleCoefficients` and proves the
three facts about it that the proof of [Stacks, Tag 0F1J] uses:

* a lower Tor bound on one factor and a lower cohomological bound on the other bound the derived
  tensor product `⊗^L_Λ` of `D(X_étale, Λ)` below (`isGE_tensor_obj_of_hasTorAmplitudeGE`);
* the inverse image along a morphism of schemes preserves Tor amplitude in `[a, ∞]`
  (`hasTorAmplitudeGE_pullback_obj`, [Stacks, Tag 08H5] for the half-infinite interval);
* a complex of flat sheaves of `Λ̲`-modules which is K-flat and vanishes below `a` has Tor
  amplitude in `[a, ∞]`, and so do its stupid truncations `σ^{≥N}` above `N`
  (`hasTorAmplitudeGE_Q_obj_stupidTruncGE`), and a flat sheaf of `Λ̲`-modules placed in degree
  `k` has Tor amplitude in `[k, ∞]`.

## The two derived tensor products

The derived tensor product of `D(X_étale, Λ)` is `Stacks.EtaleCohomology.EtaleCoefficients.tensor`,
the bifunctor of `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`; Tor amplitude
and Stacks 0F1M are stated for the derived tensor product datum
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` of the same ringed site. The two bifunctors
are isomorphic (`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules`),
and the bound on `tensor` is transported along that isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.EtaleCoefficients.HasTorAmplitudeGE` — Tor amplitude in `[a, ∞]` on
  `D(X_étale, Λ)`.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
* [Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/-! ### Stupid truncations of K-flat complexes of flat modules -/

namespace Stacks.SheafOfModules.DerivedTensorProduct

open HomologicalComplex ComplexShape StacksDraft.StupidTruncation

section StupidTruncation

variable {X : RingedSite.{u, u, u}}

/-- **A stupid truncation of a complex of flat modules has flat terms**: each of its terms is a
term of the complex or zero. -/
theorem isFlat_stupidTrunc_X {ι : Type*} {c : ComplexShape ι} (e : c.Embedding (.up ℤ))
    [e.IsRelIff]
    (K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i))
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) ((K.stupidTrunc e).X i) := by
  by_cases hi : ∃ j, e.f j = i
  · obtain ⟨j, hj⟩ := hi
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso X.O (K.stupidTruncXIso e hj).symm
      (hflat i)
  · exact isFlat_of_isZero _ (K.isZero_stupidTrunc_X e i (by simpa using hi))

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A quotient stupid truncation `σ^{≤N}K` of a complex of flat modules is K-flat**: it is a
bounded above complex of flat modules (Stacks 06YQ). -/
theorem isKFlat_stupidTruncLE (K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i))
    (N : ℤ) : Stacks.SheafOfModules.IsKFlat X.O (K.stupidTrunc (embeddingUpIntLE N)) :=
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O _ ⟨N, inferInstance⟩
    (isFlat_stupidTrunc_X _ K hflat)

/-- **A stupid truncation `σ^{≥N}K` of a K-flat complex of flat modules is K-flat**: in the short
exact sequence `0 ⟶ σ^{≥N}K ⟶ K ⟶ σ^{≤N-1}K ⟶ 0` the other two terms are K-flat and the third has
flat terms (Stacks 0G7B). -/
theorem isKFlat_stupidTruncGE (K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat X.O K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i))
    (N : ℤ) : Stacks.SheafOfModules.IsKFlat X.O (K.stupidTrunc (embeddingUpIntGE N)) :=
  Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_left_of_shortExact X.O
    (stupidTruncGELEShortComplex K N) (stupidTruncGELEShortComplex_shortExact K N)
    (isFlat_stupidTrunc_X _ K hflat) hK (isKFlat_stupidTruncLE K hflat (N - 1))

end StupidTruncation

end Stacks.SheafOfModules.DerivedTensorProduct

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Tor amplitude in `[a, ∞]` on `D(X_étale, Λ)`** ([Stacks, Tag 08FZ]): for every sheaf of
`Λ̲`-modules `F` on `X_étale`, `E ⊗^L_Λ F` has no cohomology below `a`. It is
`Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE` at the canonical derived tensor
product of the ringed site `(X_étale, Λ̲)`. -/
abbrev HasTorAmplitudeGE {X : Scheme.{u}} (E : DerivedModules Λ X) (a : ℤ) : Prop :=
  Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (ringedTopos Λ X).toRingedSite) E a

variable {X Y : Scheme.{u}}

/-- **A lower Tor bound on one factor and a lower cohomological bound on the other bound the
derived tensor product of `D(X_étale, Λ)` below**: if `E` has Tor amplitude in `[a, ∞]` and `W`
lies in `D^{≥n}`, then `E ⊗^L_Λ W` lies in `D^{≥a+n}`. Represent `E` by a K-flat complex `P`
vanishing below `a` (Stacks 0F1M) and `W` by a complex `Z` vanishing below `n`; a K-flat left
factor computes the derived tensor product, and the total tensor complex of `P` and `Z` vanishes
below `a + n`. -/
@[sga "4 XVII 4.1.9" "(i)⇒(ii)"]
theorem isGE_tensor_obj_of_hasTorAmplitudeGE (E W : DerivedModules Λ X) (a n : ℤ)
    (hE : HasTorAmplitudeGE Λ E a) (hW : W.IsGE n) :
    (((tensor Λ X).obj E).obj W).IsGE (a + n) := by
  obtain ⟨P, hP, -, hPzero, ⟨eP⟩⟩ :=
    (Stacks.SheafOfModules.hasTorAmplitudeGE_iff_exists_kFlatRepresentative
      (X := (ringedTopos Λ X).toRingedSite) E a).1 hE
  have := hW
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := W.exists_iso_Q_obj_of_isGE n
  have : CochainComplex.IsStrictlyGE P a := by
    rw [CochainComplex.isStrictlyGE_iff]; exact hPzero
  have := hZ
  have hTot := Stacks.SheafOfModules.DerivedTensorProduct.isStrictlyGE_mapBifunctor
    (X := (ringedTopos Λ X).toRingedSite) P Z a n
  have hQ : (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P Z
      (Stacks.SheafOfModules.Tensor.sheafTensor (ringedTopos Λ X).O) (ComplexShape.up ℤ))).IsGE
        (a + n) := inferInstance
  have hQ' : (DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex
      (ringedTopos Λ X).O).obj P).obj Z)).IsGE (a + n) := hQ
  have h₁ := DerivedCategory.TStructure.t.isGE_of_iso
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      (ringedTopos Λ X).O).comparisonLeft P Z hP).symm (a + n)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (((tensor Λ X).mapIso eP).app (DerivedCategory.Q.obj Z) ≪≫ ((tensor Λ X).obj E).mapIso eZ.symm)
    (a + n)

/-- A K-flat complex of sheaves of `Λ̲`-modules vanishing below `a` has Tor amplitude in
`[a, ∞]` (the direction of Stacks 0F1M which takes no input). -/
theorem hasTorAmplitudeGE_Q_obj
    (K : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)) ℤ) (a : ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat (ringedTopos Λ X).O K)
    (hzero : ∀ i : ℤ, i < a → IsZero (K.X i)) :
    HasTorAmplitudeGE Λ (DerivedCategory.Q.obj K) a :=
  Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_kFlatRepresentative _ _ a K hK
    hzero (Iso.refl _)

/-- **[Stacks, Tag 08H5] for the interval `[a, ∞]` on `D(-_étale, Λ)`**: the inverse image along a
morphism of schemes `f : X ⟶ Y` preserves Tor amplitude in `[a, ∞]`. A K-flat representative
of `E` with flat terms vanishing below `a` (Stacks 0F1M) stays K-flat with flat terms under
degreewise pullback, which computes `f⁻¹` on it. -/
theorem hasTorAmplitudeGE_pullback_obj (f : X ⟶ Y) (E : DerivedModules Λ Y) (a : ℤ)
    (hE : HasTorAmplitudeGE Λ E a) : HasTorAmplitudeGE Λ ((pullback Λ f).obj E) a := by
  obtain ⟨K, hKflat, hflat, hzero, ⟨e⟩, hpull⟩ :=
    Stacks.SheafOfModules.exists_pullbackStable_kFlatRepresentative_of_hasTorAmplitudeGE
      (X := (ringedTopos Λ Y).toRingedSite) E a hE
  obtain ⟨hpKflat, -⟩ := hpull (ringedTopos Λ X) (ringedToposHom Λ f)
    (isMorphismOfSites_ringedToposHom Λ f)
  refine Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_kFlatRepresentative _ _
    a ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex (ringedToposHom Λ f)).obj K)
    hpKflat (fun i hi => Functor.map_isZero _ (hzero i hi)) ?_
  exact (Stacks.Sheaves.DerivedPullback.flatPullbackIso (ringedToposHom Λ f)
    (isMorphismOfSites_ringedToposHom Λ f) K hKflat hflat).symm ≪≫ (pullback Λ f).mapIso e

/-- **A flat sheaf of `Λ̲`-modules placed in degree `k` has Tor amplitude in `[k, ∞]`**: the single
complex is a bounded above complex of flat modules, hence K-flat (Stacks 06YQ). -/
theorem hasTorAmplitudeGE_singleFunctor_obj
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (ringedTopos Λ X).O) M) (k : ℤ) :
    HasTorAmplitudeGE Λ ((DerivedCategory.singleFunctor _ k).obj M) k := by
  have hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (ringedTopos Λ X).O)
      (((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj M).X i) := by
    intro i
    by_cases hi : i = k
    · subst hi
      exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M).symm hM
    · exact Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero
        (Y := (ringedTopos Λ X).toRingedSite) _
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) k M i hi)
  exact hasTorAmplitudeGE_Q_obj Λ ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj M) k
    (Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat _ _ ⟨k, inferInstance⟩ hflat)
    (fun i hi => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) k M i (by omega))

open HomologicalComplex ComplexShape in
/-- **The stupid truncation `σ^{≥N}K` of a K-flat complex of flat sheaves of `Λ̲`-modules has Tor
amplitude in `[N, ∞]`.** -/
theorem hasTorAmplitudeGE_Q_obj_stupidTruncGE
    (K : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat (ringedTopos Λ X).O K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (ringedTopos Λ X).O) (K.X i)) (N : ℤ) :
    HasTorAmplitudeGE Λ (DerivedCategory.Q.obj (K.stupidTrunc (embeddingUpIntGE N))) N :=
  hasTorAmplitudeGE_Q_obj Λ _ N
    (Stacks.SheafOfModules.DerivedTensorProduct.isKFlat_stupidTruncGE
      (X := (ringedTopos Λ X).toRingedSite) K hK hflat N)
    (fun i hi => K.isZero_stupidTrunc_X _ i (by rw [notMem_range_embeddingUpIntGE_iff]; exact hi))

end Stacks.EtaleCohomology.EtaleCoefficients

end
