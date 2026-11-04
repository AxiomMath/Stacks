module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomTermwiseSplit

/-!
# The internal Hom complex of a termwise split short exact sequence of targets

Let `(C, O)` be a ringed site, let `E` be a complex of `O`-modules, and let

`B₁ ⟶ B₂ ⟶ B₃`

be a short complex of complexes of `O`-modules which is split in every degree. Then

`SheafHom(E, B₁) ⟶ SheafHom(E, B₂) ⟶ SheafHom(E, B₃)`

is again split in every degree. That is
`AlgebraicGeometry.RingedSite.internalHomTermwiseSplittingTarget`, and it is the second of the
two rows of the dévissage of Stacks 0ATN part (2).

Everything here is the companion, in the **target** of the internal Hom, of a construction
already present for the **source**, which is the variable part (1)'s dévissage runs over:
`internalHomShortComplex`, `homDegreeFamilyMap` and `internalHomTermwiseSplitting`. The internal
Hom being covariant in its target and contravariant in its source, the row here preserves the
direction of the arrows where the existing one reverses them, and the splitting data transfers
without the reversal the existing construction has to perform.

## Implementation notes

The terms of an internal Hom complex are produced by `Classical.choice` and are opaque, but
`homDegreeIsLimit` and `homDegreeProjection` present the degree-`n` term as the product over `q`
of `SheafHom(E^{-q}, B^{n-q})`, and that presentation is public. So the degreewise family map is
built exactly as its source-variable companion is, by `Fan.IsLimit.lift`, with postcomposition
`internalHomPost` in place of precomposition `internalHomPre` and with the index `n - q` in place
of `-q`.

The four algebraic identities for `internalHomPost` restated here — `internalHomPost_id`,
`internalHomPost_comp'`, `internalHomPost_add` and `internalHomPost_zero'` — duplicate `private`
lemmas of `StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/HomComplex.lean` in the first
two cases, and are new in the other two. A `private` declaration cannot be named from another
module, so there is no way to reuse them; this is the same situation, and the same remedy, as the
`internalHomPre` identities restated in `InternalHomTermwiseSplit.lean`.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

section Post

variable {A B C D : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- Postcomposition with the identity is the identity on internal Hom sheaves. -/
lemma internalHomPost_id : internalHomPost X (A := A) (𝟙 B) = 𝟙 (internalHomSheaf X A B) := by
  ext U a
  rfl

/-- Postcomposition on internal Hom sheaves is covariantly functorial. -/
lemma internalHomPost_comp' (f : B ⟶ C) (g : C ⟶ D) :
    internalHomPost X (A := A) f ≫ internalHomPost X (A := A) g =
      internalHomPost X (A := A) (f ≫ g) := by
  ext U a
  rfl

/-- Postcomposition on internal Hom sheaves is additive in the morphism. -/
lemma internalHomPost_add (f g : B ⟶ C) :
    internalHomPost X (A := A) (f + g) =
      internalHomPost X (A := A) f + internalHomPost X (A := A) g := by
  ext U a
  rfl

/-- Postcomposition with the zero morphism is zero. -/
lemma internalHomPost_zero' : internalHomPost X (A := A) (0 : B ⟶ C) = 0 := by
  ext U a
  rfl

end Post

section TargetSplit

/-- **The degree-`n` component of `homMap (𝟙 E) ψ` is, in the product description of the terms
of the internal Hom complex, the product of the postcompositions with the components of `ψ`.**
This is the companion of `homDegreeProjection_homMap`, which is the same statement for a morphism
of the sources. -/
@[reassoc]
lemma homDegreeProjection_homMap_right
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (ψ : B ⟶ B')
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n q : ℤ) :
    (homMap X (𝟙 E) ψ).f n ≫ homDegreeProjection X E B' n q =
      homDegreeProjection X E B n q ≫ internalHomPost X (ψ.f (n - q)) := by
  ext U s
  rw [comp_val_app_apply' X, comp_val_app_apply' X, homDegreeProjection_val_app_apply,
    homDegreeProjection_val_app_apply]
  refine Eq.trans (congrArg SheafOfModules.Hom.val
    (sectionsIso_homMap_v X (𝟙 E) ψ U.unop n (-q) (n - q) (by omega) s)) ?_
  rfl

/-- **The morphism of degree-`n` terms of internal Hom complexes induced by a family of
morphisms `B^q ⟶ B'^q` of the terms of the targets.**

No compatibility with the differentials is required: the degree-`n` term of `SheafHom(E, B)` is
the product over `q` of `SheafHom(E^{-q}, B^{n-q})` by `homDegreeIsLimit`, so a family of
morphisms of the terms induces one of the products. This is the companion of
`homDegreeFamilyMap`, which is the same construction for a family of morphisms of the sources. -/
def homDegreeFamilyMapTarget
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (ψ : ∀ q : ℤ, B.X q ⟶ B'.X q)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (sheafHomComplex X E B).obj.X n ⟶ (sheafHomComplex X E B').obj.X n :=
  Fan.IsLimit.lift (homDegreeIsLimit X E B' n)
    (fun q => homDegreeProjection X E B n q ≫ internalHomPost X (ψ (n - q)))

/-- The defining property of `homDegreeFamilyMapTarget`. -/
@[reassoc]
lemma homDegreeFamilyMapTarget_homDegreeProjection
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (ψ : ∀ q : ℤ, B.X q ⟶ B'.X q)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n q : ℤ) :
    homDegreeFamilyMapTarget X ψ E n ≫ homDegreeProjection X E B' n q =
      homDegreeProjection X E B n q ≫ internalHomPost X (ψ (n - q)) :=
  Fan.IsLimit.fac (homDegreeIsLimit X E B' n) _ q

/-- The map of internal Hom complexes induced by a zero morphism of the targets vanishes. -/
lemma homMap_zero_right
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    homMap X (𝟙 E) (0 : B ⟶ B') = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.zero_f]
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [homDegreeProjection_homMap_right, HomologicalComplex.zero_f, internalHomPost_zero',
    comp_zero, zero_comp]

section Split

variable
  (S : ShortComplex
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
  (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The two induced maps of internal Hom complexes into a short complex of targets compose to
zero. -/
lemma internalHomShortComplexTarget_zero :
    homMap X (𝟙 E) S.f ≫ homMap X (𝟙 E) S.g = 0 := by
  rw [homMap_comp, Category.comp_id, S.zero, homMap_zero_right]

/-- **The short complex `SheafHom(E, B₁) ⟶ SheafHom(E, B₂) ⟶ SheafHom(E, B₃)` of internal Hom
complexes obtained from a short complex `B₁ ⟶ B₂ ⟶ B₃` of targets.** Unlike
`internalHomShortComplex`, which is the same construction in the source and reverses the arrows,
this one preserves their direction, the internal Hom being covariant in its target. -/
def internalHomShortComplexTarget :
    ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  ShortComplex.mk (homMap X (𝟙 E) S.f) (homMap X (𝟙 E) S.g)
    (internalHomShortComplexTarget_zero X S E)

/-- A degreewise retraction of `S.f` induces a degreewise retraction of the induced map of
internal Hom complexes. -/
lemma homMap_f_comp_homDegreeFamilyMapTarget (r : ∀ p : ℤ, S.X₂.X p ⟶ S.X₁.X p)
    (hr : ∀ p : ℤ, S.f.f p ≫ r p = 𝟙 (S.X₁.X p)) (n : ℤ) :
    (homMap X (𝟙 E) S.f).f n ≫ homDegreeFamilyMapTarget X r E n =
      𝟙 ((sheafHomComplex X E S.X₁).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Category.assoc, homDegreeFamilyMapTarget_homDegreeProjection,
    homDegreeProjection_homMap_right_assoc, internalHomPost_comp', hr, internalHomPost_id,
    Category.comp_id, Category.id_comp]

/-- A degreewise section of `S.g` induces a degreewise section of the induced map of internal
Hom complexes. -/
lemma homDegreeFamilyMapTarget_comp_homMap_g (s : ∀ p : ℤ, S.X₃.X p ⟶ S.X₂.X p)
    (hs : ∀ p : ℤ, s p ≫ S.g.f p = 𝟙 (S.X₃.X p)) (n : ℤ) :
    homDegreeFamilyMapTarget X s E n ≫ (homMap X (𝟙 E) S.g).f n =
      𝟙 ((sheafHomComplex X E S.X₃).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Category.assoc, homDegreeProjection_homMap_right,
    homDegreeFamilyMapTarget_homDegreeProjection_assoc, internalHomPost_comp', hs,
    internalHomPost_id, Category.comp_id, Category.id_comp]

/-- The compatibility identity of a degreewise splitting is inherited by the induced maps of
internal Hom complexes. -/
lemma homDegreeFamilyMapTarget_splitting_id (r : ∀ p : ℤ, S.X₂.X p ⟶ S.X₁.X p)
    (s : ∀ p : ℤ, S.X₃.X p ⟶ S.X₂.X p)
    (hid : ∀ p : ℤ, r p ≫ S.f.f p + S.g.f p ≫ s p = 𝟙 (S.X₂.X p)) (n : ℤ) :
    homDegreeFamilyMapTarget X r E n ≫ (homMap X (𝟙 E) S.f).f n +
        (homMap X (𝟙 E) S.g).f n ≫ homDegreeFamilyMapTarget X s E n =
      𝟙 ((sheafHomComplex X E S.X₂).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, homDegreeProjection_homMap_right,
    homDegreeFamilyMapTarget_homDegreeProjection,
    homDegreeFamilyMapTarget_homDegreeProjection_assoc,
    homDegreeProjection_homMap_right_assoc, internalHomPost_comp', internalHomPost_comp',
    ← Preadditive.comp_add, ← internalHomPost_add, hid, internalHomPost_id, Category.comp_id,
    Category.id_comp]

/-- **The internal Hom complex preserves a termwise split short exact sequence of targets, and
the result is again termwise split.**

Only the degreewise splitting data of the given short complex is used, through the product
description of the terms of the internal Hom complex. Because the internal Hom is covariant in
its target, the splitting data transfers without the reversal that
`internalHomTermwiseSplitting` has to perform. -/
def internalHomTermwiseSplittingTarget
    (σ : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).Splitting) (n : ℤ) :
    ((internalHomShortComplexTarget X S E).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := homDegreeFamilyMapTarget X (fun p => show S.X₂.X p ⟶ S.X₁.X p from (σ p).r) E n
  s := homDegreeFamilyMapTarget X (fun p => show S.X₃.X p ⟶ S.X₂.X p from (σ p).s) E n
  f_r := homMap_f_comp_homDegreeFamilyMapTarget X S E _ (fun p => (σ p).f_r) n
  s_g := homDegreeFamilyMapTarget_comp_homMap_g X S E _ (fun p => (σ p).s_g) n
  id := homDegreeFamilyMapTarget_splitting_id X S E _ _ (fun p => (σ p).id) n

end Split

end TargetSplit

end AlgebraicGeometry.RingedSite

end
