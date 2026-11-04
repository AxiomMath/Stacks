module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex of a termwise split short exact sequence

Let `(C, O)` be a ringed site, let `B` be a complex of `O`-modules, and let

`E₁ ⟶ E₂ ⟶ E₃`

be a short complex of complexes of `O`-modules which is split in every degree. This file shows
that the internal Hom complex of Stacks 0A8Z turns it into a short complex

`SheafHom(E₃, B) ⟶ SheafHom(E₂, B) ⟶ SheafHom(E₁, B)`

which is again split in every degree.

The mechanism is the product description of the terms of the internal Hom complex: by
`AlgebraicGeometry.RingedSite.homDegreeIsLimit` the degree-`n` term of `SheafHom(E, B)` is the
product, over `q : ℤ`, of the internal Hom sheaves `SheafHom(E^{-q}, B^{n-q})`, with no
hypothesis on `E`. A family of morphisms of the terms of the source, not required to be
compatible with the differentials, therefore induces a morphism of the degree-`n` terms of the
internal Hom complexes; that is `homDegreeFamilyMap`, and the degreewise components of
`AlgebraicGeometry.RingedSite.homMap` in the contravariant variable are the special case of a
chain map. The splitting identities are then read off one projection at a time from the
degreewise splittings of the given short complex.

## Main definitions

* `AlgebraicGeometry.RingedSite.homDegreeFamilyMap`: the morphism of degree-`n` terms of
  internal Hom complexes induced by a degreewise family of morphisms of the sources.
* `AlgebraicGeometry.RingedSite.internalHomShortComplex`: the short complex of internal Hom
  complexes obtained from a short complex of sources.

## Main results

* `AlgebraicGeometry.RingedSite.homDegreeProjection_homMap`: the degreewise component of
  `homMap k (𝟙 B)` is the product of the precompositions with the components of `k`.
* `AlgebraicGeometry.RingedSite.homMap_zero_left`: the zero map of sources induces the zero map
  of internal Hom complexes.
* `AlgebraicGeometry.RingedSite.internalHomTermwiseSplitting`: the termwise splitting of the
  internal Hom complex of a termwise split short complex of sources.

## Implementation notes

The internal Hom complex of Stacks 0A8Z is produced by `Classical.choice` from the structure
`AlgebraicGeometry.RingedSite.SheafHomComplex`, so its terms are opaque and the only access to
them is through `homDegreeProjection` and `homDegreeIsLimit` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/StrictlyPerfectInternalHomGeneral.lean`,
together with the characterisation `homDegreeProjection_val_app_apply` of the projection on
sections. Nothing below inspects the construction.

Every splitting identity is proved after composing with a single projection
`homDegreeProjection X E B n q`, never by comparing two families of morphisms of the terms of
the sources. The reason is that the degreewise splitting of a short complex `S` of complexes
provides morphisms typed at `(S.map (HomologicalComplex.eval _ _ p)).X₃ ⟶ …`, which is the
term of `S.X₃` only after unfolding `ShortComplex.map`, so a rewrite with a lemma about a
family `∀ p, E.X p ⟶ E'.X p` has to solve `?E.X p =?= (S.map _).X₃` and fails. At a fixed `q`
no such higher-order problem arises.

The four algebraic identities for `internalHomPre` restated here —
`internalHomPre_id`, `internalHomPre_comp`, `internalHomPre_add` and `internalHomPre_zero` —
duplicate `private` lemmas of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/HomComplex.lean`. A `private` declaration
cannot be named from another module, so there is no way to reuse them; dropping `private` in that
file is the one-line change that would retire these four.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})


section Pre

variable {A B C D : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- Precomposition with the identity is the identity on internal Hom sheaves. -/
lemma internalHomPre_id : internalHomPre X (C := C) (𝟙 A) = 𝟙 (internalHomSheaf X A C) := by
  ext U a
  rfl

/-- Precomposition on internal Hom sheaves is contravariantly functorial. -/
lemma internalHomPre_comp (f : A ⟶ B) (g : B ⟶ C) :
    internalHomPre X (C := D) g ≫ internalHomPre X (C := D) f =
      internalHomPre X (C := D) (f ≫ g) := by
  ext U a
  rfl

/-- Restriction to a slice of the site is additive on the underlying presheaves of modules. -/
private lemma restrFun_map_add (f g : A ⟶ B) (U : X.C) :
    (restrFun X.O.obj U).map (homOf X (f + g)) =
      (restrFun X.O.obj U).map (homOf X f) + (restrFun X.O.obj U).map (homOf X g) := by
  ext V x
  rfl

/-- Restriction to a slice of the site sends the zero morphism to zero. -/
private lemma restrFun_map_zero (U : X.C) :
    (restrFun X.O.obj U).map (homOf X (0 : A ⟶ B)) = 0 := by
  ext V x
  rfl

/-- Precomposition on internal Hom sheaves is additive in the morphism. -/
lemma internalHomPre_add (f g : A ⟶ B) :
    internalHomPre X (C := C) (f + g) =
      internalHomPre X (C := C) f + internalHomPre X (C := C) g := by
  ext U a
  change _ ≫ (a : _ ⟶ _) = _ ≫ (a : _ ⟶ _) + _ ≫ (a : _ ⟶ _)
  rw [restrFun_map_add]
  exact Preadditive.add_comp _ _ _ _ _ _

/-- Precomposition with the zero morphism is zero. -/
lemma internalHomPre_zero : internalHomPre X (C := C) (0 : A ⟶ B) = 0 := by
  ext U a
  change _ ≫ (a : _ ⟶ _) = 0
  rw [restrFun_map_zero]
  exact zero_comp

end Pre

/-- The degree-`n` component of `homMap k (𝟙 B)` is, in the product description of the terms of
the internal Hom complex, the product of the precompositions with the components of `k`. -/
@[reassoc]
lemma homDegreeProjection_homMap
    {E E' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : E' ⟶ E)
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n q : ℤ) :
    (homMap X k (𝟙 B)).f n ≫ homDegreeProjection X E' B n q =
      homDegreeProjection X E B n q ≫ internalHomPre X (k.f (-q)) := by
  ext U s
  rw [comp_val_app_apply, comp_val_app_apply, homDegreeProjection_val_app_apply,
    homDegreeProjection_val_app_apply]
  refine Eq.trans (congrArg SheafOfModules.Hom.val
    (sectionsIso_homMap_v X k (𝟙 B) U.unop n (-q) (n - q) (by omega) s)) ?_
  rfl

/-- Two morphisms into the degree-`n` term of an internal Hom complex agree as soon as their
composites with all the projections of `homDegreeIsLimit` agree. -/
lemma homDegree_hom_ext {T : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {E B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (n : ℤ)
    (f g : T ⟶ (sheafHomComplex X E B).obj.X n)
    (h : ∀ q, f ≫ homDegreeProjection X E B n q = g ≫ homDegreeProjection X E B n q) :
    f = g :=
  Fan.IsLimit.hom_ext (homDegreeIsLimit X E B n) f g h

/-- The morphism of degree-`n` terms of internal Hom complexes induced by a family of morphisms
`E'^p ⟶ E^p` of the terms of the sources.

No compatibility with the differentials is required: the degree-`n` term of `SheafHom(E, B)` is
the product over `q` of `SheafHom(E^{-q}, B^{n-q})` by `homDegreeIsLimit`, so a family of
morphisms of the terms induces one of the products. -/
def homDegreeFamilyMap
    {E E' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : ∀ p : ℤ, E'.X p ⟶ E.X p)
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (sheafHomComplex X E B).obj.X n ⟶ (sheafHomComplex X E' B).obj.X n :=
  Fan.IsLimit.lift (homDegreeIsLimit X E' B n)
    (fun q => homDegreeProjection X E B n q ≫ internalHomPre X (φ (-q)))

/-- The defining property of `homDegreeFamilyMap`. -/
@[reassoc]
lemma homDegreeFamilyMap_homDegreeProjection
    {E E' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : ∀ p : ℤ, E'.X p ⟶ E.X p)
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n q : ℤ) :
    homDegreeFamilyMap X φ B n ≫ homDegreeProjection X E' B n q =
      homDegreeProjection X E B n q ≫ internalHomPre X (φ (-q)) :=
  Fan.IsLimit.fac (homDegreeIsLimit X E' B n) _ q

/-- The zero morphism of sources induces the zero morphism of internal Hom complexes. -/
lemma homMap_zero_left
    {E E' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    homMap X (0 : E' ⟶ E) (𝟙 B) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.zero_f]
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [homDegreeProjection_homMap, HomologicalComplex.zero_f, internalHomPre_zero, comp_zero,
    zero_comp]

section Split

variable
  (S : ShortComplex (CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
  (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The two induced maps of internal Hom complexes out of a short complex of sources compose to
zero. -/
lemma internalHomShortComplex_zero :
    homMap X S.g (𝟙 B) ≫ homMap X S.f (𝟙 B) = 0 := by
  rw [homMap_comp, S.zero, Category.comp_id, homMap_zero_left]

/-- The short complex `SheafHom(E₃, B) ⟶ SheafHom(E₂, B) ⟶ SheafHom(E₁, B)` of internal Hom
complexes obtained from a short complex `E₁ ⟶ E₂ ⟶ E₃` of sources. -/
@[reducible] def internalHomShortComplex :
    ShortComplex (CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  ShortComplex.mk (homMap X S.g (𝟙 B)) (homMap X S.f (𝟙 B)) (internalHomShortComplex_zero X S B)

/-- A degreewise section of `S.g` induces a degreewise retraction of the induced map of
internal Hom complexes. -/
lemma homMap_g_comp_homDegreeFamilyMap (s : ∀ p : ℤ, S.X₃.X p ⟶ S.X₂.X p)
    (hs : ∀ p : ℤ, s p ≫ S.g.f p = 𝟙 (S.X₃.X p)) (n : ℤ) :
    (homMap X S.g (𝟙 B)).f n ≫ homDegreeFamilyMap X s B n =
      𝟙 ((sheafHomComplex X S.X₃ B).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Category.assoc, homDegreeFamilyMap_homDegreeProjection, homDegreeProjection_homMap_assoc,
    internalHomPre_comp, hs, internalHomPre_id, Category.comp_id, Category.id_comp]

/-- A degreewise retraction of `S.f` induces a degreewise section of the induced map of
internal Hom complexes. -/
lemma homDegreeFamilyMap_comp_homMap_f (r : ∀ p : ℤ, S.X₂.X p ⟶ S.X₁.X p)
    (hr : ∀ p : ℤ, S.f.f p ≫ r p = 𝟙 (S.X₁.X p)) (n : ℤ) :
    homDegreeFamilyMap X r B n ≫ (homMap X S.f (𝟙 B)).f n =
      𝟙 ((sheafHomComplex X S.X₁ B).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Category.assoc, homDegreeProjection_homMap, homDegreeFamilyMap_homDegreeProjection_assoc,
    internalHomPre_comp, hr, internalHomPre_id, Category.comp_id, Category.id_comp]

/-- The compatibility identity of a degreewise splitting is inherited by the induced maps of
internal Hom complexes. -/
lemma homDegreeFamilyMap_splitting_id (r : ∀ p : ℤ, S.X₂.X p ⟶ S.X₁.X p)
    (s : ∀ p : ℤ, S.X₃.X p ⟶ S.X₂.X p)
    (hid : ∀ p : ℤ, S.g.f p ≫ s p + r p ≫ S.f.f p = 𝟙 (S.X₂.X p)) (n : ℤ) :
    homDegreeFamilyMap X s B n ≫ (homMap X S.g (𝟙 B)).f n +
        (homMap X S.f (𝟙 B)).f n ≫ homDegreeFamilyMap X r B n =
      𝟙 ((sheafHomComplex X S.X₂ B).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, homDegreeProjection_homMap,
    homDegreeFamilyMap_homDegreeProjection, homDegreeFamilyMap_homDegreeProjection_assoc,
    homDegreeProjection_homMap_assoc, internalHomPre_comp, internalHomPre_comp,
    ← Preadditive.comp_add, ← internalHomPre_add, hid, internalHomPre_id, Category.comp_id,
    Category.id_comp]

/-- **The internal Hom complex reverses a termwise split short exact sequence of sources, and
the result is again termwise split.**

Only the degreewise splitting data of the given short complex is used, through the product
description of the terms of the internal Hom complex. -/
def internalHomTermwiseSplitting
    (σ : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).Splitting) (n : ℤ) :
    ((internalHomShortComplex X S B).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := homDegreeFamilyMap X (fun p => show S.X₃.X p ⟶ S.X₂.X p from (σ p).s) B n
  s := homDegreeFamilyMap X (fun p => show S.X₂.X p ⟶ S.X₁.X p from (σ p).r) B n
  f_r := homMap_g_comp_homDegreeFamilyMap X S B _ (fun p => (σ p).s_g) n
  s_g := homDegreeFamilyMap_comp_homMap_f X S B _ (fun p => (σ p).f_r) n
  id := homDegreeFamilyMap_splitting_id X S B _ _ (fun p => by rw [add_comm]; exact (σ p).id) n

end Split

end AlgebraicGeometry.RingedSite

end
