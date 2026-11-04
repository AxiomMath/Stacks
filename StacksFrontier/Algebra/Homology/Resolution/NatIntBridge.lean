module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Homology.DerivedIndexing.Extend
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The bridge between `ℕ`-indexed and `ℤ`-indexed injective resolutions

Two structures carry the name *injective resolution*. Mathlib's
`CategoryTheory.InjectiveResolution X` resolves an *object* `X` by a cochain complex indexed by
`ℕ`, and it is what `CategoryTheory.Functor.rightDerived` is built on. The `ℤ`-indexed
`CochainComplex.InjectiveResolution K` resolves a *complex* `K`, and it is what the theory of
K-injective complexes, of bounded below resolutions and of the horseshoe lemma is stated for.

This file connects them. The passage from `ℕ` to `ℤ` is extension by zero in the negative degrees,
which Mathlib already performs on the resolving complex
(`CategoryTheory.InjectiveResolution.cochainComplex`, `CategoryTheory.InjectiveResolution.ι'`);
what is added here is that the result is a `CochainComplex.InjectiveResolution`, the passage back,
and the transport of statements across the two.

## Main definitions

* `CategoryTheory.InjectiveResolution.toCochainComplexResolution`: an `ℕ`-indexed injective
  resolution of an object `X`, read as a `ℤ`-indexed injective resolution of the complex `X[0]`.
* `CochainComplex.InjectiveResolution.toNatResolution`: conversely, a `ℤ`-indexed injective
  resolution of `X[0]` which vanishes in the negative degrees, read as an `ℕ`-indexed injective
  resolution of `X`.
* `HomologicalComplex.restrictionExtendIso` and `CochainComplex.extendRestrictionUpNatIso`: the two
  round-trip identifications these constructions are inverse to each other up to.
* `CategoryTheory.Functor.mapExtendIso`: an additive functor commutes with extension along an
  embedding of complex shapes. This is what lets a statement about `F.mapHomologicalComplex` be
  moved across the bridge at all. It is `Stacks.DerivedIndexing.mapExtendIso` read backwards, by
  `CategoryTheory.Functor.mapExtendIso_eq_symm`, so that the two lemma sets are interchangeable.

## Main results

* `CochainComplex.exists_desc_of_quasiIso`: **the descent lemma with minimal hypotheses.** A
  morphism `γ` out of a complex which is quasi-isomorphic to `Z[0]` into a complex of injective
  objects factors through any quasi-isomorphism `ε : Z[0] ⟶ K` on the nose, not merely up to
  homotopy. Neither complex is required to be an injective resolution: the source needs only the
  quasi-isomorphism (its terms are arbitrary) and the target needs only injective terms (it
  resolves nothing). Mathlib's `CategoryTheory.InjectiveResolution.desc` is the special case where
  both are resolutions.
* `CochainComplex.nonempty_homotopy_of_precomp_quasiIso`: the descent is unique up to homotopy,
  under the same minimal hypotheses.
* `CategoryTheory.Functor.RightAcyclicCriterion.map_quasiIso_nat`: the `ℕ`-indexed form of
  `CategoryTheory.Functor.RightAcyclicCriterion.map_quasiIso`, i.e. an additive functor carries a
  quasi-isomorphism of `ℕ`-indexed complexes with terms in an adapted class to a
  quasi-isomorphism.
* `CategoryTheory.InjectiveResolution.isoRightDerivedObjOfQuasiIso`: the two preceding results
  combined, on the `rightDerived` side: `(F.rightDerived n).obj X` is the degree-`n` cohomology of
  `F` applied to *any* resolution of `X` by objects adapted to `F`, injective or not.
* `CategoryTheory.InjectiveResolution.exactAt_mapHomologicalComplex_cochainComplex`: the image
  under an additive functor of an injective resolution of an object right-acyclic for it is exact
  away from degree zero. This is a statement about the `ℤ`-indexed resolving complex whose content
  lives on the `ℕ`-indexed side, so it is read across the bridge.

## Implementation notes

The `ℤ`-indexed resolution attached to an `ℕ`-indexed one is Mathlib's extension by zero, so no
new complex is built; the content of `toCochainComplexResolution` is only that the fields of
`CochainComplex.InjectiveResolution` are then available, which they are as instances.

The passage back restricts along `ComplexShape.embeddingUpNat`, which is why it needs the
hypothesis `[R.cocomplex.IsStrictlyGE 0]`: the resolving complex of a `ℤ`-indexed resolution of
`X[0]` is bounded below and has `IsGE 0` and `IsLE 0`, but its terms in the negative degrees need
not vanish (they may cancel in cohomology), and restricting such a complex forgets them. So the
two structures are *not* equivalent: `CochainComplex.InjectiveResolution ((singleFunctor C 0).obj
X)` is strictly larger than `CategoryTheory.InjectiveResolution X`, and the vanishing hypothesis
is what cuts it down.

No morphism out of the restriction is ever written by hand. Every such morphism is obtained from
its `ℤ`-indexed counterpart through `ComplexShape.Embedding.fullyFaithfulExtendFunctor`, which is
a bijection on morphisms; this is what keeps the `eqToHom` arising from the index arithmetic out of
the proofs. For the same reason the descent lemma is proved by extending to `ℤ`, applying
`CochainComplex.IsKInjective.exists_factorization_of_quasiIso` there, and pulling the result back
along that bijection, rather than by redoing Mathlib's degreewise induction with weakened
hypotheses.

## References

* [Stacks, Tag 013I](https://stacks.math.columbia.edu/tag/013I)
* [Stacks, Tag 013P](https://stacks.math.columbia.edu/tag/013P)
* [Stacks, Tag 013S](https://stacks.math.columbia.edu/tag/013S)
-/

@[expose] public noncomputable section

universe v v' u u'

open CategoryTheory Category Limits ZeroObject HomologicalComplex

section Infrastructure

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- Restricting the extension of a complex along an embedding of complex shapes gives the complex
back: this is the canonical isomorphism `(K.extend e).restriction e ≅ K`, the round trip which
starts in the smaller shape. -/
def restrictionExtendIso (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff] :
    (K.extend e).restriction e ≅ K := by
  have (i : ι) : IsIso ((e.homRestrict (𝟙 (K.extend e))).f i) := by
    rw [e.homRestrict_f _ (rfl : e.f i = e.f i), id_f]
    infer_instance
  have := HomologicalComplex.Hom.isIso_of_components (e.homRestrict (𝟙 (K.extend e)))
  exact asIso (e.homRestrict (𝟙 (K.extend e)))

/-- The components of `HomologicalComplex.restrictionExtendIso`. -/
lemma restrictionExtendIso_hom_f (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff]
    (i : ι) : (K.restrictionExtendIso e).hom.f i =
      ((K.extend e).restrictionXIso e (rfl : e.f i = e.f i)).hom ≫
        (K.extendXIso e (rfl : e.f i = e.f i)).hom := by
  rw [restrictionExtendIso, asIso_hom, e.homRestrict_f _ (rfl : e.f i = e.f i), id_f, id_comp]

end HomologicalComplex

namespace ComplexShape.Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- A lift along an embedding of complex shapes is an isomorphism as soon as the morphism it lifts
is a degreewise isomorphism and the source vanishes outside the image of the embedding. -/
lemma isIso_liftExtend {K : HomologicalComplex C c'} {L : HomologicalComplex C c}
    (e : c.Embedding c') [e.IsRelIff] (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ)
    [∀ i, IsIso (φ.f i)] (h : ∀ i', (∀ i, e.f i ≠ i') → IsZero (K.X i')) :
    IsIso (e.liftExtend φ hφ) := by
  have h' : ∀ i', IsIso ((e.liftExtend φ hφ).f i') := fun i' => by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      rw [e.isIso_liftExtend_f_iff φ hφ rfl]
      infer_instance
    · have h₁ := h i' (by simpa using hi')
      have h₂ := HomologicalComplex.isZero_extend_X L e i' (by simpa using hi')
      exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

end ComplexShape.Embedding

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- For a cochain complex `K` of `C` whose terms vanish in the negative degrees, the canonical
morphism from `K` to the extension of its restriction along `ComplexShape.embeddingUpNat`. It is
an isomorphism, see `CochainComplex.extendRestrictionUpNatIso`. -/
def toExtendRestrictionUpNat (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] :
    K ⟶ (K.restriction ComplexShape.embeddingUpNat).extend ComplexShape.embeddingUpNat :=
  ComplexShape.embeddingUpNat.liftExtend (𝟙 (K.restriction ComplexShape.embeddingUpNat))
    (fun j hj i' hi' => by
      have hneg : i' < 0 := by
        by_contra h
        obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 h)
        exact hj.notMem hi' k (by simp)
      exact (K.isZero_of_isStrictlyGE 0 i' hneg).eq_of_src _ _)

/-- For a cochain complex vanishing in the negative degrees, the canonical morphism to the
extension of its restriction along `ComplexShape.embeddingUpNat` is an isomorphism. -/
instance (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] : IsIso K.toExtendRestrictionUpNat :=
  ComplexShape.Embedding.isIso_liftExtend _ _ _ (fun i' hi' =>
    K.isZero_of_isStrictlyGE 0 i' (by
      by_contra h
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 h)
      exact hi' k (by simp)))

/-- A cochain complex `K` whose terms vanish in the negative degrees is isomorphic to the
extension of its restriction along `ComplexShape.embeddingUpNat`. This is the round trip which
starts in the shape `up ℤ`; the one which starts in `up ℕ` is
`HomologicalComplex.restrictionExtendIso`. -/
def extendRestrictionUpNatIso (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] :
    K ≅ (K.restriction ComplexShape.embeddingUpNat).extend ComplexShape.embeddingUpNat :=
  asIso K.toExtendRestrictionUpNat

end CochainComplex

namespace CategoryTheory.Functor

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive]

/-- An additive functor commutes with extension along an embedding of complex shapes. -/
def mapExtendIso (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff] :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  Stacks.DerivedIndexing.mapExtendIsoSymm F e K

/-- The components of `CategoryTheory.Functor.mapExtendIso`. -/
@[simp]
lemma mapExtendIso_hom_f (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff]
    (i' : ι') : (F.mapExtendIso K e).hom.f i' =
      (Stacks.DerivedIndexing.mapExtendXIsoSymm F K (e.r i')).hom := rfl

/-- `CategoryTheory.Functor.mapExtendIso` is natural in the complex. -/
@[reassoc]
lemma mapExtendIso_hom_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) ≫
        (F.mapExtendIso L e).hom =
      (F.mapExtendIso K e).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e :=
  Stacks.DerivedIndexing.mapExtendIsoSymm_naturality F e φ

/-- An additive functor commutes with extension along an embedding of complex shapes,
naturally in the complex: the natural-isomorphism form of
`CategoryTheory.Functor.mapExtendIso`. -/
def mapExtendNatIso (e : c.Embedding c') [e.IsRelIff] :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents (fun K => F.mapExtendIso K e)
    (fun φ => F.mapExtendIso_hom_naturality φ e)

/-- `HomologicalComplex.extendMap`, read through the comparison isomorphisms at a degree in the
range of the embedding. -/
lemma _root_.HomologicalComplex.extendMap_f_comp_extendXIso
    {K L : HomologicalComplex C c} (ψ : K ⟶ L) (e : c.Embedding c')
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (HomologicalComplex.extendMap ψ e).f i' ≫ (L.extendXIso e h).hom =
      (K.extendXIso e h).hom ≫ ψ.f i := by
  rw [HomologicalComplex.extendMap_f ψ e h]
  simp

/-- `CategoryTheory.Functor.mapExtendIso`, read through the comparison isomorphisms at a degree
in the range of the embedding. -/
lemma mapExtendIso_hom_f_comp_extendXIso
    (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff]
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (F.mapExtendIso K e).hom.f i' ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom =
      F.map (K.extendXIso e h).hom := by
  rw [Functor.mapExtendIso_hom_f,
    Stacks.DerivedIndexing.mapExtendXIsoSymm_hom_of_r_eq_some F e K
      (ComplexShape.Embedding.r_eq_some e h),
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **`CategoryTheory.Functor.mapExtendIso` is `Stacks.DerivedIndexing.mapExtendIso` read
backwards.** The two are the same comparison — an additive functor commutes with extension by
zero along an embedding of complex shapes — in opposite directions, so that the lemmas proved
for either are available for the other. The natural-transformation and homotopy-category forms
live on `Stacks.DerivedIndexing.mapExtendIso`, the degreewise forms on both. -/
lemma mapExtendIso_eq_symm (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff] :
    F.mapExtendIso K e = (Stacks.DerivedIndexing.mapExtendIso F e K).symm := by
  refine Iso.ext ?_
  ext i'
  rcases hr : e.r i' with _ | i
  · exact (HomologicalComplex.isZero_extend_X' _ e i' hr).eq_of_tgt _ _
  · rw [mapExtendIso_hom_f, Stacks.DerivedIndexing.mapExtendXIsoSymm_hom_of_r_eq_some F e K hr]
    exact (Stacks.DerivedIndexing.mapExtendIso_inv_f_eq F e K
      (ComplexShape.Embedding.f_eq_of_r_eq_some e hr)).symm

/-- The composite of `CategoryTheory.Functor.mapExtendIso` with the extension of a morphism out
of `(F.mapHomologicalComplex c).obj K`, read through the comparison isomorphisms at a degree in
the range of the embedding. -/
lemma mapExtendIso_hom_comp_extendFunctor_map_f
    (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff]
    {M : HomologicalComplex D c} (β : (F.mapHomologicalComplex c).obj K ⟶ M)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    ((F.mapExtendIso K e).hom ≫ HomologicalComplex.extendMap β e).f i' ≫
        (M.extendXIso e h).hom =
      F.map (K.extendXIso e h).hom ≫ β.f i := by
  rw [HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex.extendMap_f_comp_extendXIso β e h, ← Category.assoc,
    mapExtendIso_hom_f_comp_extendXIso F K e h]

end CategoryTheory.Functor

end Infrastructure

section Bridge

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- An injective resolution of an object `X`, indexed by `ℕ`, read as an injective resolution of
the cochain complex `X[0]`, indexed by `ℤ`: the resolving complex is extended by zero in the
negative degrees, which is Mathlib's `CategoryTheory.InjectiveResolution.cochainComplex`. -/
@[stacks 013I "the identification of the `ℕ`-graded half of the tag with the `ℤ`-graded one"]
def toCochainComplexResolution (R : InjectiveResolution X) :
    CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor C 0).obj X) where
  cocomplex := R.cochainComplex
  boundedBelow := ⟨0, inferInstance⟩
  ι := R.ι'

/-- The resolving complex of `R.toCochainComplexResolution` is `R.cochainComplex`. -/
@[simp]
lemma toCochainComplexResolution_cocomplex (R : InjectiveResolution X) :
    R.toCochainComplexResolution.cocomplex = R.cochainComplex := rfl

/-- The resolution map of `R.toCochainComplexResolution` is `R.ι'`. -/
@[simp]
lemma toCochainComplexResolution_ι (R : InjectiveResolution X) :
    R.toCochainComplexResolution.ι = R.ι' := rfl

/-- The resolving complex of `R.toCochainComplexResolution` vanishes in the negative degrees. -/
instance (R : InjectiveResolution X) :
    R.toCochainComplexResolution.cocomplex.IsStrictlyGE 0 := by
  rw [toCochainComplexResolution_cocomplex]
  infer_instance

end CategoryTheory.InjectiveResolution

namespace CochainComplex.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- An injective resolution of the cochain complex `X[0]`, indexed by `ℤ` and vanishing in the
negative degrees, read as an injective resolution of the object `X`, indexed by `ℕ`: the resolving
complex is restricted along `ComplexShape.embeddingUpNat`.

The hypothesis that the resolving complex vanish in the negative degrees cannot be dropped; see
the module docstring. -/
@[stacks 013I "the identification of the `ℤ`-graded half of the tag with the `ℕ`-graded one, for \
  a resolving complex vanishing in the negative degrees"]
def toNatResolution
    (R : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor C 0).obj X))
    [R.cocomplex.IsStrictlyGE 0] : CategoryTheory.InjectiveResolution X where
  cocomplex := R.cocomplex.restriction ComplexShape.embeddingUpNat
  injective n := R.injective _
  ι := (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor C).preimage
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 (by simp)).hom ≫
      R.ι ≫ R.cocomplex.extendRestrictionUpNatIso.hom)
  quasiIso := by
    rw [← HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat]
    have h : HomologicalComplex.extendMap
        ((ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor C).preimage
          ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 (by simp)).hom ≫
            R.ι ≫ R.cocomplex.extendRestrictionUpNatIso.hom)) ComplexShape.embeddingUpNat =
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 (by simp)).hom ≫
          R.ι ≫ R.cocomplex.extendRestrictionUpNatIso.hom :=
      (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor C).map_preimage _
    rw [h, quasiIso_iff_comp_left, quasiIso_iff_comp_right]
    infer_instance

/-- The resolving complex of `toNatResolution R` is the restriction of that of `R` along
`ComplexShape.embeddingUpNat`. -/
@[simp]
lemma toNatResolution_cocomplex
    (R : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor C 0).obj X))
    [R.cocomplex.IsStrictlyGE 0] :
    (toNatResolution R).cocomplex = R.cocomplex.restriction ComplexShape.embeddingUpNat := rfl

/-- The resolution map of `CochainComplex.InjectiveResolution.toNatResolution R` becomes, after
extension by zero, the resolution map of `R`, up to the two canonical isomorphisms. This is the
defining property of the construction, and the form in which it is used. -/
lemma extendMap_toNatResolution_ι
    (R : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor C 0).obj X))
    [R.cocomplex.IsStrictlyGE 0] :
    HomologicalComplex.extendMap (toNatResolution R).ι ComplexShape.embeddingUpNat =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 (by simp)).hom ≫
        R.ι ≫ R.cocomplex.extendRestrictionUpNatIso.hom :=
  (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor C).map_preimage _

/-- **The round trip `ℤ → ℕ → ℤ`.** Passing a `ℤ`-indexed injective resolution of `X[0]` which
vanishes in the negative degrees to the `ℕ`-indexed world and back recovers it, up to the
canonical isomorphism `CochainComplex.extendRestrictionUpNatIso`. Its compatibility with the
resolution maps is `CochainComplex.InjectiveResolution.extendMap_toNatResolution_ι`. -/
def toNatResolutionCochainComplexIso
    (R : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor C 0).obj X))
    [R.cocomplex.IsStrictlyGE 0] :
    R.cocomplex ≅ (toNatResolution R).toCochainComplexResolution.cocomplex :=
  R.cocomplex.extendRestrictionUpNatIso

end CochainComplex.InjectiveResolution

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- **The round trip `ℕ → ℤ → ℕ`.** Passing an `ℕ`-indexed injective resolution of `X` to the
`ℤ`-indexed world and back recovers it, up to the canonical isomorphism
`HomologicalComplex.restrictionExtendIso`. -/
def toCochainComplexResolutionNatIso (R : InjectiveResolution X) :
    R.toCochainComplexResolution.toNatResolution.cocomplex ≅ R.cocomplex :=
  R.cocomplex.restrictionExtendIso ComplexShape.embeddingUpNat

end CategoryTheory.InjectiveResolution

end Bridge

section Descent

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A quasi-isomorphism from the complex `Z[0]`, with `Z` in degree zero, to a cochain complex
indexed by `ℕ` is a monomorphism in every degree. For an injective resolution this is Mathlib's
instance on `CategoryTheory.InjectiveResolution.ι`; injectivity of the terms is not used. -/
instance mono_f_of_quasiIso_single₀ {Z : C} {K : CochainComplex C ℕ}
    (ε : (single₀ C).obj Z ⟶ K) [QuasiIso ε] (n : ℕ) : Mono (ε.f n) := by
  match n with
  | 0 =>
    have h : IsIso (HomologicalComplex.homologyMap ε 0) := by
      have h' : QuasiIsoAt ε 0 := inferInstance
      rwa [quasiIsoAt_iff_isIso_homologyMap] at h'
    have h' : IsIso (HomologicalComplex.cyclesMap ε 0) := by
      have e : ((single₀ C).obj Z).isoHomologyπ₀.hom ≫
          HomologicalComplex.homologyMap ε 0 ≫ K.isoHomologyπ₀.inv =
            HomologicalComplex.cyclesMap ε 0 := by
        rw [CochainComplex.isoHomologyπ₀_inv_naturality ε, Iso.hom_inv_id_assoc]
      rw [← e]
      infer_instance
    have key : ε.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 Z).hom ≫
        (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 Z).inv ≫
          HomologicalComplex.cyclesMap ε 0 ≫ K.iCycles 0 := by
      rw [HomologicalComplex.cyclesMap_i,
        HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc, Iso.hom_inv_id_assoc]
    rw [key]
    infer_instance
  | k + 1 =>
    exact (HomologicalComplex.isZero_single_obj_X _ _ Z (k + 1) (by simp)).mono _

variable {Z : C} {K L : CochainComplex C ℕ}

/-- **Stacks 013P, part (2), for `ℕ`-indexed complexes: descent with minimal hypotheses.** Let `C`
be an abelian category, let `ε : Z[0] ⟶ K` be a quasi-isomorphism of cochain complexes of `C`
indexed by `ℕ`, let `L` be a cochain complex of injective objects and let `γ : Z[0] ⟶ L`. Then
`γ = ε ≫ β` for a (unique up to homotopy, see
`CochainComplex.nonempty_homotopy_of_precomp_quasiIso`) morphism `β : K ⟶ L`.

Neither `K` nor `L` is required to be an injective resolution: the terms of `K` are arbitrary and
`L` resolves nothing. Mathlib's `CategoryTheory.InjectiveResolution.desc` is the special case
where both are the resolving complexes of injective resolutions. -/
@[stacks 013P "part (2), for `ℕ`-indexed complexes, with the source required only to be \
  quasi-isomorphic to a complex concentrated in degree zero and the target only to have \
  injective terms", ega "0 12.1.4" "partial"]
theorem exists_desc_of_quasiIso [∀ n, Injective (L.X n)] (ε : (single₀ C).obj Z ⟶ K) [QuasiIso ε]
    (γ : (single₀ C).obj Z ⟶ L) : ∃ β : K ⟶ L, ε ≫ β = γ := by
  have hmono (n : ℤ) :
      Mono ((HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat).f n) := by
    cases n with
    | ofNat k =>
      rw [HomologicalComplex.extendMap_f ε ComplexShape.embeddingUpNat (i := k) (by simp)]
      infer_instance
    | negSucc k => exact (CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)).mono _
  obtain ⟨β, hβ⟩ := (CochainComplex.IsKInjective.exists_factorization_of_quasiIso
    (I := L.extend ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap γ ComplexShape.embeddingUpNat)).2
  refine ⟨(ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor C).preimage β, ?_⟩
  apply (ComplexShape.embeddingUpNat.extendFunctor C).map_injective
  rw [Functor.map_comp]
  erw [(ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor C).map_preimage]
  exact hβ

/-- **Stacks 013S, for `ℕ`-indexed complexes: uniqueness of the descent with minimal
hypotheses.** Two morphisms `β₁, β₂ : K ⟶ L` from a cochain complex quasi-isomorphic to `Z[0]`
into a cochain complex of injective objects which agree, up to homotopy, after precomposition with
a quasi-isomorphism `ε : Z[0] ⟶ K`, are homotopic.

As in `CochainComplex.exists_desc_of_quasiIso`, neither complex need be an injective resolution.
Mathlib's `CategoryTheory.InjectiveResolution.descHomotopy` is the special case where both are;
`CategoryTheory.InjectiveResolution.descHomotopy'` weakens the target alone. -/
@[stacks 013S "for `ℕ`-indexed complexes, with the source required only to be quasi-isomorphic \
  to a complex concentrated in degree zero and the target only to have injective terms",
  ega "0 12.1.4" "partial", sga "2 VIII 1.4" "special case"]
theorem nonempty_homotopy_of_precomp_quasiIso [∀ n, Injective (L.X n)]
    (ε : (single₀ C).obj Z ⟶ K) [QuasiIso ε] {β₁ β₂ : K ⟶ L}
    (h : Homotopy (ε ≫ β₁) (ε ≫ β₂)) : Nonempty (Homotopy β₁ β₂) := by
  obtain ⟨h'⟩ := CochainComplex.IsKInjective.nonempty_homotopy_of_precomp_quasiIso
    (I := L.extend ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat)
    (β₁ := HomologicalComplex.extendMap β₁ ComplexShape.embeddingUpNat)
    (β₂ := HomologicalComplex.extendMap β₂ ComplexShape.embeddingUpNat)
    (((Homotopy.ofEq (by simp)).trans (h.extend ComplexShape.embeddingUpNat)).trans
      (Homotopy.ofEq (by simp)))
  exact ⟨h'.ofExtend⟩

end CochainComplex

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {Y Z : C}

/-- **The descent lemma Mathlib's `CategoryTheory.InjectiveResolution.desc` is missing.** A
morphism `f : Z ⟶ Y` descends to a morphism of complexes from *any* complex `K` carrying a
quasi-isomorphism `ε : Z[0] ⟶ K` — an exact augmented complex, whose terms need not be injective —
into the resolving complex of an injective resolution of `Y`.

Mathlib's `desc` is the case `K = J.cocomplex` for an injective resolution `J` of `Z`, where the
terms of `K` are injective too; that hypothesis is used nowhere. -/
@[sga "2 VIII 1.4" "special case"]
theorem exists_desc_of_quasiIso (f : Z ⟶ Y) (I : InjectiveResolution Y) {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ε] :
    ∃ β : K ⟶ I.cocomplex, ε ≫ β = (CochainComplex.single₀ C).map f ≫ I.ι :=
  CochainComplex.exists_desc_of_quasiIso ε _

/-- Any two descents along `ε` of a morphism `f : Z ⟶ Y` into the resolving complex of an
injective resolution of `Y` are homotopic. This is the uniqueness half of
`CategoryTheory.InjectiveResolution.exists_desc_of_quasiIso`. -/
@[ega "0 12.1.4" "partial", sga "2 VIII 1.4" "special case"]
theorem nonempty_descHomotopy_of_quasiIso (I : InjectiveResolution Y) {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ε] {β₁ β₂ : K ⟶ I.cocomplex}
    (w : ε ≫ β₁ = ε ≫ β₂) : Nonempty (Homotopy β₁ β₂) :=
  CochainComplex.nonempty_homotopy_of_precomp_quasiIso ε (Homotopy.ofEq w)

end CategoryTheory.InjectiveResolution

end Descent

section Acyclic

namespace CategoryTheory.Functor.RightAcyclicCriterion

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]

/-- A class of objects satisfying the hypotheses of [Stacks 05T8] is closed under isomorphism: the
short exact sequence `0 ⟶ 0 ⟶ A ⟶ B ⟶ 0` attached to an isomorphism `A ≅ B` transports
membership. -/
lemma prop_of_iso (F : C ⥤ D) [F.Additive] (I : ObjectProperty C)
    (hI₁ : ∀ X : C, ∃ (Y : C) (_ : I Y) (i : X ⟶ Y), Mono i)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact)
    {A B : C} (u : A ≅ B) (hA : I A) : I B := by
  have hI₀ : ∀ {Z : C}, IsZero Z → I Z := zero_mem F I hI₁ hI₂
  refine (hI₂ (ShortComplex.mk (0 : (0 : C) ⟶ A) u.hom (by simp)) ?_
    (hI₀ (isZero_zero C)) hA).1
  exact { mono_f := (isZero_zero C).mono _
          epi_g := inferInstance
          exact := (ShortComplex.exact_iff_mono _ rfl).2 inferInstance }

/-- **Stacks 05T8 for `ℕ`-indexed complexes.** Let `F : C ⥤ D` be an additive functor between
abelian categories and let `I` be a class of objects of `C` adapted to `F` in the sense of
[Stacks 05T8]. Then `F` carries a quasi-isomorphism of cochain complexes indexed by `ℕ` whose
terms satisfy `I` to a quasi-isomorphism.

This is `CategoryTheory.Functor.RightAcyclicCriterion.map_quasiIso` transported along extension by
zero. The boundedness hypotheses of that statement are automatic here, an `ℕ`-indexed complex
being concentrated in the degrees `≥ 0`. -/
@[stacks 05T8 "the quasi-isomorphism half, for `ℕ`-indexed complexes"]
lemma map_quasiIso_nat (F : C ⥤ D) [F.Additive] (I : ObjectProperty C)
    (hI₁ : ∀ X : C, ∃ (Y : C) (_ : I Y) (i : X ⟶ Y), Mono i)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact)
    {K L : CochainComplex C ℕ} (f : K ⟶ L) [QuasiIso f]
    (hIK : ∀ n, I (K.X n)) (hIL : ∀ n, I (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map f) := by
  have hI₀ : ∀ {Z : C}, IsZero Z → I Z := zero_mem F I hI₁ hI₂
  have hext (M : CochainComplex C ℕ) (hIM : ∀ n, I (M.X n)) (n : ℤ) :
      I ((M.extend ComplexShape.embeddingUpNat).X n) := by
    cases n with
    | ofNat k =>
      exact prop_of_iso F I hI₁ hI₂
        (M.extendXIso ComplexShape.embeddingUpNat (i := k) (by simp)).symm (hIM k)
    | negSucc k => exact hI₀ (CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega))
  have hz := map_quasiIso F I hI₁ hI₂
    (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)
    ⟨0, inferInstance⟩ ⟨0, inferInstance⟩ (hext K hIK) (hext L hIL)
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat]
  have key : HomologicalComplex.extendMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map f) ComplexShape.embeddingUpNat =
        (F.mapExtendIso K ComplexShape.embeddingUpNat).inv ≫
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) ≫
          (F.mapExtendIso L ComplexShape.embeddingUpNat).hom :=
    (Iso.eq_inv_comp _).2 (F.mapExtendIso_hom_naturality f ComplexShape.embeddingUpNat).symm
  rw [key]
  infer_instance

end CategoryTheory.Functor.RightAcyclicCriterion

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C] {X : C}

omit [HasInjectiveResolutions C] in
/-- **Right derived functors are computed by any resolution by `F`-adapted objects.** Let `I` be a
class of objects of `C` adapted to an additive functor `F` in the sense of [Stacks 05T8], let `J`
be an injective resolution of `X` with terms in `I`, and let `ε : X[0] ⟶ K` be a quasi-isomorphism
onto a cochain complex with terms in `I` — a resolution of `X` by `I`-objects, not required to be
injective. Then any descent `β : K ⟶ J.cocomplex` of the identity along `ε` induces an
isomorphism on the cohomology of the images under `F`.

Such a `β` exists by `CategoryTheory.InjectiveResolution.exists_desc_of_quasiIso` and is unique up
to homotopy by `CategoryTheory.InjectiveResolution.nonempty_descHomotopy_of_quasiIso`, so the
resulting identification `CategoryTheory.InjectiveResolution.isoRightDerivedObjOfQuasiIso` of
`(F.rightDerived n).obj X` with `Hⁿ(F(K))` does not depend on the choice. -/
@[stacks 05T8 "the computation of `Rⁿ F` by a resolution by `I`-objects, for `ℕ`-indexed \
  resolutions"]
lemma isIso_homologyMap_map_of_desc (F : C ⥤ D) [F.Additive] (I : ObjectProperty C)
    (hI₁ : ∀ Y : C, ∃ (Z : C) (_ : I Z) (i : Y ⟶ Z), Mono i)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact)
    (J : InjectiveResolution X) {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj X ⟶ K) [QuasiIso ε] (β : K ⟶ J.cocomplex)
    (hβ : ε ≫ β = J.ι) (hIK : ∀ n, I (K.X n)) (hIJ : ∀ n, I (J.cocomplex.X n)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map β) n) := by
  have : QuasiIso (ε ≫ β) := by rw [hβ]; infer_instance
  have : QuasiIso β := _root_.quasiIso_of_comp_left ε β
  have := Functor.RightAcyclicCriterion.map_quasiIso_nat F I hI₁ hI₂ β hIK hIJ
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  infer_instance

/-- The identification of `(F.rightDerived n).obj X` with the degree-`n` cohomology of `F` applied
to a resolution of `X` by `F`-adapted objects, along a descent `β` of the identity. See
`CategoryTheory.InjectiveResolution.isIso_homologyMap_map_of_desc` for the hypotheses and for why
the choice of `β` does not matter. -/
@[stacks 05T8 "the resulting identification of `Rⁿ F (X)` with `Hⁿ (F (K))`"]
def isoRightDerivedObjOfQuasiIso (F : C ⥤ D) [F.Additive] (I : ObjectProperty C)
    (hI₁ : ∀ Y : C, ∃ (Z : C) (_ : I Z) (i : Y ⟶ Z), Mono i)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact)
    (J : InjectiveResolution X) {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj X ⟶ K) [QuasiIso ε] (β : K ⟶ J.cocomplex)
    (hβ : ε ≫ β = J.ι) (hIK : ∀ n, I (K.X n)) (hIJ : ∀ n, I (J.cocomplex.X n)) (n : ℕ) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
  have := isIso_homologyMap_map_of_desc F I hI₁ hI₂ J ε β hβ hIK hIJ n
  J.isoRightDerivedObj F n ≪≫
    (asIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map β) n)).symm

end CategoryTheory.InjectiveResolution

end Acyclic

section AcyclicExactness

namespace CategoryTheory.InjectiveResolution

/-- **The image of an injective resolution of a right-acyclic object is exact away from degree
zero.** In negative degrees the resolution vanishes; in positive degree `n` the homology is the
`n`-th right derived functor, which vanishes by hypothesis. -/
lemma exactAt_mapHomologicalComplex_cochainComplex {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasInjectiveResolutions A] (G : A ⥤ B) [G.Additive] {F : A}
    (J : InjectiveResolution F) (hG : ∀ n : ℕ, 0 < n → IsZero ((G.rightDerived n).obj F))
    (q : ℤ) (hq : q ≠ 0) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.cochainComplex).ExactAt q := by
  rcases lt_trichotomy q 0 with h | h | h
  · exact HomologicalComplex.ExactAt.of_isZero
      (G.map_isZero (J.cochainComplex.isZero_of_isStrictlyGE 0 q h))
  · exact absurd h hq
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = q := ⟨q.toNat, by omega⟩
    have hm : 0 < m := by omega
    refine HomologicalComplex.ExactAt.of_iso ?_
      (G.mapExtendIso J.cocomplex ComplexShape.embeddingUpNat).symm
    refine (HomologicalComplex.extend_exactAt_iff
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f m)).2 ?_
    refine (HomologicalComplex.exactAt_iff_isZero_homology _ m).2 ?_
    exact (hG m hm).of_iso (J.isoRightDerivedObj G m).symm

end CategoryTheory.InjectiveResolution

end AcyclicExactness

end
