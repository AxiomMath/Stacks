module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMapDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyOpenSubfunctor
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardSpecField

/-!
# The chart of Stacks 0B9X: an open of the Hilbert scheme representing the 0B9V locus

Let `f : X ⟶ S` be a proper smooth relative curve with a section `σ`, let `θ` be a Picard class
of `X` of degree `g` on every fibre and killed by `σ^*`, and let `H` represent the degree-`g`
Hilbert functor `Hilb^g_{X/S}`. This file constructs the open `W ⊆ H` of [Stacks, Tag 0B9X] —
the locus over which the universal divisor `D` has `Rf_*𝒪(D)` invertible in degree `0` — and
proves that `W` represents the translate into `Pic⁰_{X/S,σ}` of the subfunctor of
[Stacks, Tag 0B9V], `Stacks.RigidifiedPicard.cohomologySubfunctorZero`.

The map sends a family `D` over `T` (a morphism `T ⟶ W`) to the rigidified class of
`𝒪_{X_T}(D) ⊗ pr_X^*θ^{-1}`. It is a bijection provided every class `ℒ` with `Rf_{T,*}ℒ`
invertible in degree `0` is `𝒪(D)` up to a class pulled back from `T`, for a unique degree-`g`
family `D`; this, and the two halves of [Stacks, Tag 0B91], are hypotheses of the main result.

## Main definitions

* `Stacks.RigidifiedPicard.HasInvertibleDirectImage`: `Rf_{T,*}` of a class is invertible in
  degree `0`.
* `Stacks.RigidifiedPicard.normalize`: the normalisation `c - π^*σ_T^*c` of a class of `X_T`.
* `Stacks.RigidifiedPicard.abelNormalized`: the rigidified class of `𝒪_{X_T}(Z) ⊗ pr_X^*θ^{-1}`
  for a Hilbert family `Z`.

## Main results

* `Stacks.RigidifiedPicard.hasInvertibleDirectImage_add_bcProj_iff`: the condition does not see
  classes pulled back from the base.
* `Stacks.RigidifiedPicard.relativeInvertibleDegreeHomAt_bcProj`: classes pulled back from the
  base have degree zero on every fibre.
* `Stacks.RigidifiedPicard.exists_chartOpen`: the open `W ⊆ H` over which `Rf_*𝒪(D)` is
  invertible in degree `0`.
* `Stacks.RigidifiedPicard.exists_representableBy_cohomologySubfunctorZero`: `W` represents the
  translate into `Pic⁰_{X/S,σ}` of the subfunctor of [Stacks, Tag 0B9V].

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Pullback of Picard classes along `g` preserves zero. -/
private theorem schemePullbackClass_zero {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    Stacks.Picard.schemePullbackClass g (0 : Stacks.Picard.ofScheme Z) = 0 :=
  map_zero (Stacks.Picard.schemePullbackClassHom g)

/-- Pullback of Picard classes along `g` preserves negation. -/
private theorem schemePullbackClass_neg {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (a : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClass g (-a) = -Stacks.Picard.schemePullbackClass g a :=
  map_neg (Stacks.Picard.schemePullbackClassHom g) a

/-- Pullback of Picard classes along `g` preserves subtraction. -/
private theorem schemePullbackClass_sub {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (a b : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClass g (a - b) =
      Stacks.Picard.schemePullbackClass g a - Stacks.Picard.schemePullbackClass g b :=
  map_sub (Stacks.Picard.schemePullbackClassHom g) a b

/-- `Rf_{T,*}` of (the representative of) a class of `X_T` is invertible in degree `0`. -/
def HasInvertibleDirectImage (T : Over S) (c : Stacks.Picard.ofScheme (bc f T)) : Prop :=
  HasDerivedPushforwardRank (bcProj f T) (Stacks.Picard.picardRepresentative _ c).obj 0 1

/-- A class `c` of `X_T` satisfies the condition of `IsCohomologyClass` for `θ` if and only if
`Rf_{T,*}` of `c + pr_X^*θ` is invertible in degree `0`. -/
theorem isCohomologyClass_iff (θ : Stacks.Picard.ofScheme X) (T : Over S)
    (c : Stacks.Picard.ofScheme (bc f T)) :
    IsCohomologyClass f θ T c ↔
      HasInvertibleDirectImage f T
        (c + Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ) :=
  Iff.rfl

/-- For `θ = 0`, a class satisfies `IsCohomologyClass` if and only if `Rf_{T,*}` of it is
invertible in degree `0`. -/
theorem isCohomologyClass_zero_iff (T : Over S) (c : Stacks.Picard.ofScheme (bc f T)) :
    IsCohomologyClass f 0 T c ↔ HasInvertibleDirectImage f T c := by
  rw [isCohomologyClass_iff, schemePullbackClass_zero, add_zero]

/-- A class pulled back from the base has degree zero on every fibre. -/
theorem relativeInvertibleDegreeHomAt_bcProj [IsProper f] [LocallyOfFiniteType f]
    (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1) (T : Over S) (t : T.left)
    (n : Stacks.Picard.ofScheme T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
      (Stacks.Picard.schemePullbackClass (bcProj f T) n) = 0 := by
  have : Subsingleton (Spec (T.left.residueField t)) := by
    change Subsingleton (PrimeSpectrum (T.left.residueField t))
    infer_instance
  have : Nonempty (Spec (T.left.residueField t)) := by
    change Nonempty (PrimeSpectrum (T.left.residueField t))
    infer_instance
  have h0 : Stacks.Picard.schemePullbackClass (T.left.fromSpecResidueField t) n = 0 :=
    Stacks.Picard.eq_zero_of_subsingleton _
  rw [relativeInvertibleDegreeHomAt_apply, Stacks.Picard.schemePullbackClass_comp,
    Scheme.Hom.fiber_fac, ← Stacks.Picard.schemePullbackClass_comp, h0, schemePullbackClass_zero,
    map_zero]

variable [Flat f] [LocallyOfFinitePresentation f] [IsProper f]

/-- If `Rf_{T,*}c` is invertible in degree `0`, then so is `Rf_{T,*}` of `c` plus any class
pulled back from `T`. -/
theorem hasInvertibleDirectImage_add_bcProj (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) (T : Over S) (c : Stacks.Picard.ofScheme (bc f T))
    (n : Stacks.Picard.ofScheme T.left) (hc : HasInvertibleDirectImage f T c) :
    HasInvertibleDirectImage f T (c + Stacks.Picard.schemePullbackClass (bcProj f T) n) := by
  obtain ⟨U₁, hU₁⟩ := exists_opens_isCohomologyClass_iff f h0B91 hbc 0 T c
  obtain ⟨U₂, hU₂⟩ := exists_opens_isCohomologyClass_iff f h0B91 hbc 0 T
    (c + Stacks.Picard.schemePullbackClass (bcProj f T) n)
  have h₁ := hU₁ T (𝟙 T)
  have h₂ := hU₂ T (𝟙 T)
  rw [bcMap_id, Stacks.Picard.schemePullbackClass_id, isCohomologyClass_zero_iff] at h₁ h₂
  refine h₂.2 ?_
  rintro _ ⟨t, rfl⟩
  obtain ⟨V, htV, hV⟩ := Stacks.Picard.exists_mem_schemePullbackClass_eq_zero n t
  let g : Over.mk (V.ι ≫ T.hom) ⟶ T := Over.homMk V.ι rfl
  have hpull : Stacks.Picard.schemePullbackClass (bcMap f g)
      (c + Stacks.Picard.schemePullbackClass (bcProj f T) n) =
      Stacks.Picard.schemePullbackClass (bcMap f g) c := by
    rw [Stacks.Picard.schemePullbackClass_add, schemePullbackClass_bcProj_natural]
    change _ + Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass V.ι n) = _
    rw [hV, schemePullbackClass_zero, add_zero]
  refine (hU₂ _ g).1 ?_ ⟨⟨t, htV⟩, rfl⟩
  rw [hpull]
  exact (hU₁ _ g).2 fun _ _ => h₁.1 hc ⟨_, rfl⟩

/-- **The condition of [Stacks, Tag 0B9V] does not see classes pulled back from the base**:
`Rf_{T,*}` of `c` plus a class pulled back from `T` is invertible in degree `0` if and only if
`Rf_{T,*}c` is. -/
theorem hasInvertibleDirectImage_add_bcProj_iff (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) (T : Over S) (c : Stacks.Picard.ofScheme (bc f T))
    (n : Stacks.Picard.ofScheme T.left) :
    HasInvertibleDirectImage f T (c + Stacks.Picard.schemePullbackClass (bcProj f T) n) ↔
      HasInvertibleDirectImage f T c := by
  refine ⟨fun h => ?_, hasInvertibleDirectImage_add_bcProj f h0B91 hbc T c n⟩
  have h' := hasInvertibleDirectImage_add_bcProj f h0B91 hbc T _ (-n) h
  rwa [schemePullbackClass_neg, add_neg_cancel_right] at h'

/-! ### The normalised Abel class -/

section Abel

variable (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- The normalisation of a class of `X_T` by the induced section: `c - π^*σ_T^*c`. -/
def normalize (T : Over S) (c : Stacks.Picard.ofScheme (bc f T)) :
    Stacks.Picard.ofScheme (bc f T) :=
  c - Stacks.Picard.schemePullbackClass (bcProj f T)
    (Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c)

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] in
/-- The normalisation of a class is killed by pullback along the induced section. -/
theorem schemePullbackClass_bcSection_normalize (T : Over S) (c : Stacks.Picard.ofScheme (bc f T)) :
    Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) (normalize f σ hσ T c) = 0 := by
  change Stacks.Picard.schemePullbackClassHom _ (normalize f σ hσ T c) = 0
  rw [normalize, map_sub, sub_eq_zero]
  exact (schemePullbackClass_bcSection_bcProj f σ hσ T _).symm

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] in
/-- Normalisation is unchanged by adding a class pulled back from the base. -/
theorem normalize_add_bcProj (T : Over S) (c : Stacks.Picard.ofScheme (bc f T))
    (n : Stacks.Picard.ofScheme T.left) :
    normalize f σ hσ T (c + Stacks.Picard.schemePullbackClass (bcProj f T) n) =
      normalize f σ hσ T c := by
  rw [normalize, normalize]
  change _ - Stacks.Picard.schemePullbackClassHom _ (Stacks.Picard.schemePullbackClassHom _
    (c + Stacks.Picard.schemePullbackClass (bcProj f T) n)) = _
  rw [map_add, map_add]
  change _ - (_ + Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _
    (Stacks.Picard.schemePullbackClass _ n))) = _
  rw [schemePullbackClass_bcSection_bcProj]
  let : AddCommGroup (Stacks.Picard.ofScheme (bc f T)) := inferInstance
  abel

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] in
/-- A class killed by pullback along the induced section is its own normalisation. -/
theorem normalize_eq_self (T : Over S) (c : Stacks.Picard.ofScheme (bc f T))
    (hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0) :
    normalize f σ hσ T c = c := by
  rw [normalize, hc, schemePullbackClass_zero, sub_zero]

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] in
/-- Normalisation commutes with pullback along the base change map of a morphism `T' ⟶ T`. -/
theorem normalize_bcMap {T T' : Over S} (g : T' ⟶ T) (c : Stacks.Picard.ofScheme (bc f T)) :
    Stacks.Picard.schemePullbackClass (bcMap f g) (normalize f σ hσ T c) =
      normalize f σ hσ T' (Stacks.Picard.schemePullbackClass (bcMap f g) c) := by
  rw [normalize, normalize]
  refine (schemePullbackClass_sub _ c _).trans ?_
  congr 1
  exact (schemePullbackClass_bcProj_natural f g _).trans
    (congrArg _ (schemePullbackClass_bcSection_natural f σ hσ g c).symm)

variable [hsm : SmoothOfRelativeDimension 1 f]

/-- The structure morphism of `Over.mk f` is smooth of relative dimension `1` when `f` is. -/
instance : SmoothOfRelativeDimension 1 (Over.mk f).hom := hsm

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] hsm in
/-- The family base change map of the Hilbert functor is the base change map of `X_T`. -/
theorem familyBaseChangeMap_eq {T T' : Over S} (g : T' ⟶ T) :
    Stacks.Hilbert.familyBaseChangeMap (Over.mk f) g = bcMap f g :=
  rfl

/-- The Abel class of a Hilbert family, read in the Picard group of `X_T = bc f T`. -/
abbrev abelClass {d : ℕ} {T : Over S} (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T d) :
    Stacks.Picard.ofScheme (bc f T) :=
  Stacks.Hilbert.abelClass Z

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] in
/-- The Abel class of the base change of a Hilbert family is the pullback of its Abel class. -/
theorem abelClass_baseChange {d : ℕ} {T T' : Over S} (g : T' ⟶ T)
    (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T d) :
    Stacks.Picard.schemePullbackClass (bcMap f g) (abelClass f Z) =
      abelClass f (Stacks.Hilbert.baseChange (Over.mk f) g Z) :=
  Stacks.Hilbert.abelClass_baseChange g Z

/-- **The Abel class, translated by `θ` and normalised**: for a Hilbert family `Z` over `T`, the
rigidified class of `𝒪_{X_T}(Z) ⊗ pr_X^*θ^{-1}`. -/
def abelNormalized (θ : Stacks.Picard.ofScheme X) {d : ℕ} {T : Over S}
    (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T d) : Stacks.Picard.ofScheme (bc f T) :=
  normalize f σ hσ T (abelClass f Z -
    Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ)

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] in
/-- The normalised Abel class of the base change of a Hilbert family is the pullback of its
normalised Abel class. -/
theorem abelNormalized_baseChange (θ : Stacks.Picard.ofScheme X) {d : ℕ} {T T' : Over S}
    (g : T' ⟶ T) (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T d) :
    Stacks.Picard.schemePullbackClass (bcMap f g) (abelNormalized f σ hσ θ Z) =
      abelNormalized f σ hσ θ (Stacks.Hilbert.baseChange (Over.mk f) g Z) := by
  rw [abelNormalized, abelNormalized, normalize_bcMap, ← abelClass_baseChange]
  congr 1
  refine (schemePullbackClass_sub _ _ _).trans ?_
  congr 1
  exact (Stacks.Picard.schemePullbackClass_comp _ _ θ).trans (by rw [bcMap_fst])

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] in
/-- The normalised Abel class plus `pr_X^*θ` differs from the Abel class by a class pulled back
from the base. -/
theorem abelNormalized_add_eq (θ : Stacks.Picard.ofScheme X) {d : ℕ} {T : Over S}
    (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T d) :
    ∃ n : Stacks.Picard.ofScheme T.left,
      abelNormalized f σ hσ θ Z + Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ =
        abelClass f Z + Stacks.Picard.schemePullbackClass (bcProj f T) n := by
  refine ⟨-Stacks.Picard.schemePullbackClass (bcSection f σ hσ T)
    (abelClass f Z - Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ), ?_⟩
  rw [abelNormalized, normalize, schemePullbackClass_neg]
  let : AddCommGroup (Stacks.Picard.ofScheme (bc f T)) := inferInstance
  abel

end Abel

/-! ### The chart -/

section Chart

variable [SmoothOfRelativeDimension 1 f] [LocallyOfFiniteType f]
  (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
  (h0B91 : PerfectDerivedPushforward.{u}) (hbc : BaseChangeDerivedPushforward.{u})
  (θ : Stacks.Picard.ofScheme X) {g : ℕ} {H : Over S}
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H g)

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [SmoothOfRelativeDimension 1 f]
  [LocallyOfFiniteType f] in
/-- The family classified by `m : T ⟶ H` is the base change of the universal family. -/
theorem family_eq_baseChange {T : Over S} (m : T ⟶ H) :
    hH.family m = Stacks.Hilbert.baseChange (Over.mk f) m (hH.family (𝟙 H)) := by
  refine Stacks.Hilbert.HilbertFamily.ext ?_
  rw [Stacks.Hilbert.baseChange_ideal, ← hH.naturality m (𝟙 H), Category.comp_id]

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [SmoothOfRelativeDimension 1 f]
  [LocallyOfFiniteType f] in
/-- The family classified by `a ≫ m` is the base change along `a` of the family classified by
`m`. -/
theorem family_comp {T T' : Over S} (a : T' ⟶ T) (m : T ⟶ H) :
    hH.family (a ≫ m) = Stacks.Hilbert.baseChange (Over.mk f) a (hH.family m) :=
  Stacks.Hilbert.HilbertFamily.ext (hH.naturality a m)

omit [LocallyOfFiniteType f] in
include h0B91 hbc in
/-- **The open `W ⊆ H` of [Stacks, Tag 0B9X]**: the locus over which the universal divisor `D`
has `Rf_*𝒪(D)` invertible in degree `0`. -/
theorem exists_chartOpen :
    ∃ W : H.left.Opens, ∀ (T : Over S) (m : T ⟶ H),
      HasInvertibleDirectImage f T (abelClass f (hH.family m)) ↔
        Set.range m.left ⊆ (W : Set H.left) := by
  obtain ⟨W, hW⟩ := exists_opens_isCohomologyClass_iff f h0B91 hbc 0 H
    (abelClass f (hH.family (𝟙 H)))
  refine ⟨W, fun T m => ?_⟩
  rw [← hW, isCohomologyClass_zero_iff, abelClass_baseChange, family_eq_baseChange]

/-- The class attached to a morphism into `H`: the normalised Abel class of the classified
family, translated by `θ`. -/
abbrev chartClass {T : Over S} (m : T ⟶ H) : Stacks.Picard.ofScheme (bc f T) :=
  abelNormalized f σ hσ θ (hH.family m)

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- The class attached to `a ≫ m` is the pullback along `a` of the class attached to `m`. -/
theorem chartClass_comp {T T' : Over S} (a : T' ⟶ T) (m : T ⟶ H) :
    chartClass f σ hσ θ hH (a ≫ m) =
      Stacks.Picard.schemePullbackClass (bcMap f a) (chartClass f σ hσ θ hH m) := by
  rw [chartClass, chartClass, abelNormalized_baseChange, family_comp]

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- The class attached to a morphism into `H` is killed by pullback along the induced section. -/
theorem schemePullbackClass_bcSection_chartClass {T : Over S} (m : T ⟶ H) :
    Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) (chartClass f σ hσ θ hH m) = 0 :=
  schemePullbackClass_bcSection_normalize f σ hσ T _

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- The degree of `pr_X^*θ` on the fibre over `t` is the degree of `θ` on the fibre over the
image of `t`. -/
theorem relativeInvertibleDegreeHomAt_fst (T : Over S) (t : T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
      (Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ) =
      relativeInvertibleDegreeHomAt f hdim (T.hom t) θ :=
  relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback
    (IsPullback.of_hasPullback f T.hom) hdim _ t θ

omit [Flat f] [LocallyOfFinitePresentation f] in
include hdim in
/-- If `θ` has degree `g` on every fibre, the class attached to a morphism into `H` has degree
zero on every fibre. -/
theorem relativeInvertibleDegreeHomAt_chartClass
    (hθ : ∀ s : S, relativeInvertibleDegreeHomAt f hdim s θ = g) {T : Over S} (m : T ⟶ H)
    (t : T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
      (chartClass f σ hσ θ hH m) = 0 := by
  rw [chartClass, abelNormalized, normalize, map_sub, map_sub,
    relativeInvertibleDegreeHomAt_bcProj f hdim T t, relativeInvertibleDegreeHomAt_fst f hdim θ,
    hθ, sub_zero]
  exact sub_eq_zero.2 (@Stacks.Hilbert.relativeInvertibleDegreeHomAt_abelClass S (Over.mk f) _ g
    T (hH.family m) (isProper_bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t)

omit [LocallyOfFiniteType f] in
include h0B91 hbc in
/-- The class attached to `m : T ⟶ H` satisfies `IsCohomologyClass` for `θ` if and only if
`Rf_{T,*}` of the Abel class of the family classified by `m` is invertible in degree `0`. -/
theorem isCohomologyClass_chartClass_iff {T : Over S} (m : T ⟶ H) :
    IsCohomologyClass f θ T (chartClass f σ hσ θ hH m) ↔
      HasInvertibleDirectImage f T (abelClass f (hH.family m)) := by
  obtain ⟨n, hn⟩ := abelNormalized_add_eq f σ hσ θ (hH.family m)
  rw [isCohomologyClass_iff, chartClass, hn, hasInvertibleDirectImage_add_bcProj_iff f h0B91 hbc]

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- Two elements of `Pic⁰_{X/S,σ}(T)` are equal when their classes in `Pic(X_T)` are. -/
theorem ext_functorZero {T : Over S} {z z' : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)}
    (h : smallEquiv _ ((((Multiplicative.toAdd z : groupZero f hdim σ hσ T) : group f σ hσ T)) :
        Stacks.Picard.smallOfScheme (bc f T)) =
      smallEquiv _ ((((Multiplicative.toAdd z' : groupZero f hdim σ hσ T) : group f σ hσ T)) :
        Stacks.Picard.smallOfScheme (bc f T))) : z = z' := by
  change Multiplicative.ofAdd (Multiplicative.toAdd z : groupZero f hdim σ hσ T) =
    Multiplicative.ofAdd (Multiplicative.toAdd z' : groupZero f hdim σ hσ T)
  exact congrArg _ (Subtype.ext (Subtype.ext ((smallEquiv (bc f T)).injective h)))

/-- The element of `Pic_{X/S,σ}(T)` given by a rigidified class. -/
def mkGroup {T : Over S} (c : Stacks.Picard.ofScheme (bc f T))
    (hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0) : group f σ hσ T :=
  ⟨(smallEquiv (bc f T)).symm c, (mem_group_iff f σ hσ T _).2 (by
    rwa [AddEquiv.apply_symm_apply])⟩

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [SmoothOfRelativeDimension 1 f]
  [LocallyOfFiniteType f] in
/-- The class in `Pic(X_T)` of `mkGroup c` is `c`. -/
theorem smallEquiv_mkGroup {T : Over S} (c : Stacks.Picard.ofScheme (bc f T))
    (hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0) :
    smallEquiv _ ((mkGroup f σ hσ c hc : group f σ hσ T) : Stacks.Picard.smallOfScheme (bc f T)) =
      c :=
  AddEquiv.apply_symm_apply _ _

/-- The element of `Pic⁰_{X/S,σ}(T)` given by a rigidified class of degree zero on every fibre. -/
def mkZero {T : Over S} (c : Stacks.Picard.ofScheme (bc f T))
    (hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0)
    (hdeg : ∀ t : T.left, relativeInvertibleDegreeHomAt (bcProj f T)
      (topologicalKrullDim_fiber_bcProj_le f hdim T) t c = 0) :
    (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T) :=
  Multiplicative.ofAdd ⟨mkGroup f σ hσ c hc,
    (mem_groupZero_iff f hdim σ hσ T _).2 fun t => by
      rw [degree_apply, smallEquiv_mkGroup]
      exact hdeg t⟩

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- The class in `Pic(X_T)` of `mkZero c` is `c`. -/
theorem smallEquiv_mkZero {T : Over S} (c : Stacks.Picard.ofScheme (bc f T))
    (hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0)
    (hdeg : ∀ t : T.left, relativeInvertibleDegreeHomAt (bcProj f T)
      (topologicalKrullDim_fiber_bcProj_le f hdim T) t c = 0) :
    smallEquiv _ (((Multiplicative.toAdd (mkZero f hdim σ hσ c hc hdeg) :
      groupZero f hdim σ hσ T) : group f σ hσ T) : Stacks.Picard.smallOfScheme (bc f T)) = c :=
  smallEquiv_mkGroup f σ hσ c hc

/-- The inclusion of the chart `W` into `H`, over `S`. -/
abbrev chartι (W : H.left.Opens) : Over.mk (W.ι ≫ H.hom) ⟶ H := Over.homMk W.ι rfl

include h0B91 hbc hdim hH in
/-- **[Stacks, Tag 0B9X], given its claim and [Stacks, Tag 0B91].** On a proper smooth relative
curve with a section, for `θ` of degree `g` on every fibre and `H` representing
`Hilb^g_{X/S}`, the translate into `Pic⁰_{X/S,σ}` of the subfunctor of [Stacks, Tag 0B9V] is
represented by an open subscheme `W` of `H`. The claim of the source's proof — every class `ℒ`
with `Rf_{T,*}ℒ` invertible in degree `0` is the class of a unique degree-`g` divisor up to a
class from the base — is the pair of hypotheses `hexists`, `huniq`. -/
theorem exists_representableBy_cohomologySubfunctorZero
    (hθ : ∀ s : S, relativeInvertibleDegreeHomAt f hdim s θ = g)
    (hexists : ∀ (T : Over S) (c : Stacks.Picard.ofScheme (bc f T)),
      HasInvertibleDirectImage f T c →
        ∃ (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T g) (n : Stacks.Picard.ofScheme T.left),
          abelClass f Z = c + Stacks.Picard.schemePullbackClass (bcProj f T) n)
    (huniq : ∀ (T : Over S) (Z Z' : Stacks.Hilbert.HilbertFamily (Over.mk f) T g),
      HasInvertibleDirectImage f T (abelClass f Z) →
        (∃ n : Stacks.Picard.ofScheme T.left,
          abelClass f Z' = abelClass f Z + Stacks.Picard.schemePullbackClass (bcProj f T) n) →
          Z = Z') :
    ∃ W : H.left.Opens, Nonempty
      ((cohomologySubfunctorZero f hdim σ hσ h0B91 hbc θ).toFunctor.RepresentableBy
        (Over.mk (W.ι ≫ H.hom))) := by
  obtain ⟨W, hW⟩ := exists_chartOpen f h0B91 hbc hH
  let F := cohomologySubfunctorZero f hdim σ hσ h0B91 hbc θ
  have hmemW : ∀ {T : Over S} (a : T ⟶ Over.mk (W.ι ≫ H.hom)),
      Set.range (a ≫ chartι W).left ⊆ (W : Set H.left) := by
    intro T a
    rintro _ ⟨x, rfl⟩
    rw [← Scheme.Opens.range_ι]
    exact ⟨a.left x, rfl⟩
  let cls : ∀ {T : Over S}, (T ⟶ Over.mk (W.ι ≫ H.hom)) →
      (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T) := fun {T} a =>
    mkZero f hdim σ hσ (chartClass f σ hσ θ hH (a ≫ chartι W))
      (schemePullbackClass_bcSection_chartClass f σ hσ θ hH _)
      (relativeInvertibleDegreeHomAt_chartClass f hdim σ hσ θ hH hθ _)
  have hcls : ∀ {T : Over S} (a : T ⟶ Over.mk (W.ι ≫ H.hom)),
      smallEquiv _ ((((Multiplicative.toAdd (cls a) : groupZero f hdim σ hσ T) :
        group f σ hσ T)) : Stacks.Picard.smallOfScheme (bc f T)) =
        chartClass f σ hσ θ hH (a ≫ chartι W) := fun a => smallEquiv_mkZero _ _ _ _ _ _ _
  have hclsF : ∀ {T : Over S} (a : T ⟶ Over.mk (W.ι ≫ H.hom)), cls a ∈ F.obj (op T) := by
    intro T a
    change IsCohomologyClass f θ T _
    rw [hcls, isCohomologyClass_chartClass_iff f σ hσ h0B91 hbc θ hH, hW]
    exact hmemW a
  let toF : ∀ {T : Over S}, (T ⟶ Over.mk (W.ι ≫ H.hom)) → F.toFunctor.obj (op T) := fun {T} a =>
    ⟨cls a, hclsF a⟩
  have hinj : ∀ {T : Over S}, Function.Injective (toF (T := T)) := by
    intro T a a' h
    have hc : chartClass f σ hσ θ hH (a ≫ chartι W) = chartClass f σ hσ θ hH (a' ≫ chartι W) := by
      rw [← hcls a, ← hcls a']
      exact congrArg (fun z : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T) =>
        smallEquiv _ ((((Multiplicative.toAdd z : groupZero f hdim σ hσ T) :
          group f σ hσ T)) : Stacks.Picard.smallOfScheme (bc f T))) (congrArg Subtype.val h)
    obtain ⟨n, hn⟩ := abelNormalized_add_eq f σ hσ θ (hH.family (a ≫ chartι W))
    obtain ⟨n', hn'⟩ := abelNormalized_add_eq f σ hσ θ (hH.family (a' ≫ chartι W))
    have hZ : hH.family (a ≫ chartι W) = hH.family (a' ≫ chartι W) := by
      refine huniq T _ _ ((hW T _).2 (hmemW a)) ⟨n - n', ?_⟩
      have h1 : abelClass f (hH.family (a' ≫ chartι W)) =
          abelClass f (hH.family (a ≫ chartι W)) +
            Stacks.Picard.schemePullbackClass (bcProj f T) n -
              Stacks.Picard.schemePullbackClass (bcProj f T) n' := by
        rw [← hn, ← chartClass, hc, chartClass, hn']
        let : AddCommGroup (Stacks.Picard.ofScheme (bc f T)) := inferInstance
        abel
      rw [h1, schemePullbackClass_sub]
      let : AddCommGroup (Stacks.Picard.ofScheme (bc f T)) := inferInstance
      abel
    have hm : a ≫ chartι W = a' ≫ chartι W := hH.family.injective hZ
    apply Over.OverMorphism.ext
    exact (cancel_mono W.ι).1 (congrArg CommaMorphism.left hm)
  have hsurj : ∀ {T : Over S}, Function.Surjective (toF (T := T)) := by
    intro T x
    set c : Stacks.Picard.ofScheme (bc f T) := smallEquiv _ ((((Multiplicative.toAdd x.1 :
      groupZero f hdim σ hσ T) : group f σ hσ T)) : Stacks.Picard.smallOfScheme (bc f T)) with hcdef
    have hcrig : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0 :=
      (mem_group_iff f σ hσ T _).1 ((Multiplicative.toAdd x.1 : groupZero f hdim σ hσ T) :
        group f σ hσ T).2
    obtain ⟨Z, n, hZ⟩ := hexists T _ x.2
    let m : T ⟶ H := hH.family.symm Z
    have hmZ : hH.family m = Z := hH.family.apply_symm_apply Z
    have hmW : Set.range m.left ⊆ (W : Set H.left) := by
      rw [← hW, hmZ, hZ, hasInvertibleDirectImage_add_bcProj_iff f h0B91 hbc]
      exact x.2
    let a : T ⟶ Over.mk (W.ι ≫ H.hom) := Over.homMk (IsOpenImmersion.lift W.ι m.left
      (by simpa using hmW)) (by
        change IsOpenImmersion.lift W.ι m.left _ ≫ W.ι ≫ H.hom = T.hom
        rw [IsOpenImmersion.lift_fac_assoc, Over.w m])
    have ham : a ≫ chartι W = m := by
      apply Over.OverMorphism.ext
      exact IsOpenImmersion.lift_fac _ _ _
    refine ⟨a, Subtype.ext ?_⟩
    change cls a = x.1
    refine ext_functorZero f hdim σ hσ ?_
    rw [hcls a, ham, chartClass, hmZ, abelNormalized, hZ, add_sub_right_comm, add_sub_cancel_right,
      normalize_add_bcProj, normalize_eq_self f σ hσ T c hcrig]
  refine ⟨W, ⟨{ homEquiv := Equiv.ofBijective toF ⟨hinj, hsurj⟩, homEquiv_comp := ?_ }⟩⟩
  intro T T' b a
  apply Subtype.ext
  change cls (b ≫ a) = (functorZero f hdim σ hσ ⋙ forget GrpCat).map b.op (cls a)
  refine ext_functorZero f hdim σ hσ ?_
  rw [functorZero_map_val, hcls, hcls, Category.assoc, chartClass_comp]

end Chart

end Stacks.RigidifiedPicard

end
