module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.CohomologyBridge
public import StacksFrontier.Homology.Ext.SpectralSequence
public import StacksFrontier.Homology.Injectives.DerivedCategory.Existence
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex

/-!
# The descent spectral sequence attached to a resolution of an abelian étale sheaf

Let `Y` be a scheme and let `F` be an abelian sheaf on its small étale site. Suppose given a
resolution
```
0 → F → G⁰ → G¹ → G² → ⋯
```
of `F` by abelian sheaves on the same site. This file produces the cohomological spectral
sequence
```
E₁^{p,q} = H^q(Y, G^p)  ⟹  H^{p+q}(Y, F),
```
with a finite decreasing filtration of each abutment group whose graded pieces are the terms of
the late pages.

This is the second half of [Stacks, Tag 09Z2]. The source constructs the resolution from the Čech
nerve of a finite surjection `f : X ⟶ Y`, taking `G^p = f_{p,*} f_p^{-1} F`, and the exactness of
the displayed sequence is the geometric content of the tag. **That exactness is a hypothesis
here**: every statement below takes the monomorphism `F ⟶ G⁰` and the exactness of the two kinds
of short complexes as input, so nothing in this file depends on where the resolution comes from.
Combining it with the exactness statement for the Čech resolution is what completes 09Z2, and for
that reason no `@[stacks]` attribute is placed here.

## Main definitions

* `Stacks.EtaleCohomology.cechCochainComplex`: the resolution read as a cochain complex of abelian
  sheaves in the nonnegative degrees.
* `Stacks.EtaleCohomology.cechAugmentation`: the augmentation `F[0] ⟶ G^•` determined by
  `a : F ⟶ G⁰`.
* `Stacks.EtaleCohomology.isoQCechCochainComplex`: the resolution represents `F` in the derived
  category.

## Main results

* `Stacks.EtaleCohomology.quasiIso_cechAugmentation`: **the augmentation is a
  quasi-isomorphism.** Exactness of `0 → F → G⁰ → G¹ → ⋯` says exactly that the augmentation
  induces an isomorphism on `H⁰` and that the higher cohomology sheaves of `G^•` vanish.
* `Stacks.EtaleCohomology.exists_resolution_sheafH_spectralSequence`: **the spectral sequence of
  the second half of [Stacks, Tag 09Z2].**

## Implementation notes

The complex is built as an `ℕ`-indexed cochain complex with `CochainComplex.of` and then extended
by zero along `ComplexShape.embeddingUpNat`; this is what makes `CochainComplex.IsStrictlyGE … 0`
an instance rather than a lemma to be proved, and it lets the quasi-isomorphism be checked at the
`ℕ`-indexing, where there are only two cases, and then transported by
`HomologicalComplex.quasiIso_extendMap_iff`.

At the `ℕ`-indexing the degree-`0` statement is the one that carries content: the short complex
there is `G⁰ →0→ G⁰ →d→ G¹`, so its left homology is the kernel of `d⁰`, and `a` exhibits `F` as
that kernel precisely because `0 → F → G⁰ → G¹` is exact with `a` a monomorphism. This is spelled
out by handing `ShortComplex.LeftHomologyMapData.ofIsLimitKernelFork` the kernel fork that
`ShortComplex.Exact.fIsKernel` produces, the source side being the kernel of a zero map.

The spectral sequence itself is
`StacksDraft.ExtSpectralSequence.exists_ext_complex_spectralSequence` ([Stacks, Tag 0AVI]) for
`M` the constant sheaf `ℤ` and `K` the complex above. Two identifications turn its conclusion into
a statement about étale cohomology. At the first page, degree `p` of the complex is `G^p` and
`Stacks.EtaleCohomology.sheafHAddEquivZExt` rewrites the `ℤ`-graded `zExt` out of the constant
sheaf as `CategoryTheory.Sheaf.H`. At the abutment, `isoQCechCochainComplex` replaces the derived
object represented by the complex by `F` placed in degree zero, and `sheafHAddEquivZExt` again
rewrites the resulting group as `H^n(Y, F)`; the filtration of 0AVI is carried along that
isomorphism of abutments by `CategoryTheory.Subobject.mk`, and the comparison of graded pieces
survives because the transported inclusion agrees with the original one up to the two chosen
underlying isomorphisms, both inclusions being monomorphisms over the same arrows.

Coefficients are `AddCommGrpCat.{u + 1}` for `Y : Scheme.{u}`, the convention of the whole
`Stacks.EtaleCohomology` namespace. Three instances are installed locally for that reason: abelian
sheaves on the small étale site are Grothendieck abelian relative to `u + 1`, hence have enough
injectives, and hence (Tag 079Q,
`Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian`) admit a derived category whose
morphism types also lie in `u + 1`. The last of these, and not `HasDerivedCategory.standard`, is
what makes the spectral sequence land in `AddCommGrpCat.{u + 1}`, the universe
`CategoryTheory.Sheaf.H` lives in.

## References

* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
* [Stacks Project, Tag 0AVI](https://stacks.math.columbia.edu/tag/0AVI)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w v' u' u

namespace Stacks.EtaleCohomology

/-- Transporting the second argument of an `Ext`-group in the derived category along an
isomorphism. This is the covariant companion of the contravariant transport used elsewhere in the
development; both are `Stacks.Injectives.homCongrAddEquiv`. -/
private def extIsoOfIsoRight {C : Type u'} [Category.{v'} C] [Abelian C]
    [HasDerivedCategory.{w} C] (X : DerivedCategory C) {P Q : DerivedCategory C} (e : P ≅ Q)
    (n : ℤ) :
    AddCommGrpCat.of (DerivedCategory.Ext X P n) ≅
      AddCommGrpCat.of (DerivedCategory.Ext X Q n) :=
  (Stacks.Injectives.homCongrAddEquiv (Iso.refl X)
    ((shiftFunctor (DerivedCategory C) n).mapIso e)).toAddCommGrpIso

/-- Transporting a pair of nested subobjects along an isomorphism of the ambient object does not
change the quotient of the larger by the smaller. The transported subobjects are written as
`CategoryTheory.Subobject.mk` of the composite arrows; the square relating the transported
inclusion to the original one commutes because both are monomorphisms over the same arrow into
the ambient object. -/
public def cokernelMkIso {C : Type u'} [Category.{v'} C] [Abelian C] {B B' : C} (e : B ≅ B')
    (P Q : Subobject B) (h : P ≤ Q) :
    cokernel (Subobject.ofLE P Q h) ≅
      cokernel (Subobject.ofLE (Subobject.mk (P.arrow ≫ e.hom)) (Subobject.mk (Q.arrow ≫ e.hom))
        (Subobject.mk_le_mk_of_comm (Subobject.ofLE P Q h)
          (by rw [← Category.assoc, Subobject.ofLE_arrow]))) :=
  cokernel.mapIso _ _ (Subobject.underlyingIso _).symm (Subobject.underlyingIso _).symm
    (by rw [← cancel_mono (Subobject.mk (Q.arrow ≫ e.hom)).arrow]; simp)

/-- Exactness of a short complex depends only on its two morphisms, not on the proof that they
compose to zero, so it may be transported along equalities of those morphisms. -/
private lemma exact_congr {C : Type u'} [Category.{v'} C] [Abelian C] {X Z W : C} {f f' : X ⟶ Z}
    {g g' : Z ⟶ W} (hf : f = f') (hg : g = g') (w : f ≫ g = 0) (w' : f' ≫ g' = 0)
    (h : (ShortComplex.mk f g w).Exact) : (ShortComplex.mk f' g' w').Exact := by
  subst hf
  subst hg
  exact h

/-- The left-homology criterion used at the bottom degree of an augmented resolution. Let
`φ : S₁ ⟶ S₂` be a morphism of short complexes with `S₁` having both maps zero and `S₂` having its
first map zero. If `α : A ⟶ S₂.X₂` is a kernel of `S₂.g` and `φ.τ₂` factors through `α` by an
isomorphism, then `φ` is a quasi-isomorphism: both sides compute the kernel of the second map. -/
private lemma shortComplex_quasiIso_of_isLimit {C : Type u'} [Category.{v'} C] [Abelian C]
    {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0)
    {A : C} (α : A ⟶ S₂.X₂) (hα : α ≫ S₂.g = 0) (hlim : IsLimit (KernelFork.ofι α hα))
    (β : S₁.X₂ ⟶ A) (hβ : β ≫ α = φ.τ₂) (hβiso : IsIso β) :
    ShortComplex.QuasiIso φ := by
  have := hβiso
  exact (ShortComplex.LeftHomologyMapData.ofIsLimitKernelFork φ hf₁ _
    (KernelFork.IsLimit.ofId S₁.g hg₁) hf₂ (KernelFork.ofι α hα) hlim β
    ((Category.id_comp φ.τ₂).trans hβ.symm)).quasiIso_iff.2
    (by exact inferInstanceAs (IsIso β))

-- Abelian sheaves on the small étale site of `Y : Scheme.{u}` with coefficients in
-- `AddCommGrpCat.{u + 1}` form a Grothendieck abelian category relative to `u + 1`, which is what
-- makes `CategoryTheory.Sheaf.H` elaborate without any hypothesis. It is kept local, as in the
-- file that proves it.
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtaleTopology

/-- A Grothendieck abelian category has enough injectives; this is the instance for abelian
sheaves on a small étale site with the coefficient universe pinned, which is what instance search
cannot guess. It is local for the same reason the Grothendieck abelian structure is. -/
local instance enoughInjectives_sheaf_smallEtaleTopology (Y : Scheme.{u}) :
    EnoughInjectives (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :=
  IsGrothendieckAbelian.enoughInjectives

/-- Abelian sheaves on the small étale site of `Y : Scheme.{u}` admit a derived category whose
morphism types lie in `u + 1`, by [Stacks, Tag 079Q]. This, and not
`CategoryTheory.HasDerivedCategory.standard`, is the model used throughout this file: it is the
one whose `Ext`-groups land in the same universe as `CategoryTheory.Sheaf.H`. -/
local instance hasDerivedCategory_sheaf_smallEtaleTopology (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :=
  Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _

/-- The constant abelian sheaf `ℤ` on the small étale site of `Y`, the coefficient object étale
cohomology is `Ext` out of. -/
public abbrev constZ (Y : Scheme.{u}) : Sheaf (smallEtaleTopology Y) Ab.{u + 1} :=
  (constantSheaf (smallEtaleTopology Y) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

variable {Y : Scheme.{u}} (G : ℕ → Sheaf (smallEtaleTopology Y) Ab.{u + 1})
  (d : ∀ n, G n ⟶ G (n + 1)) (hdd : ∀ n, d n ≫ d (n + 1) = 0)

/-- **The resolution `G⁰ → G¹ → G² → ⋯` as a cochain complex of abelian sheaves**, placed in the
nonnegative degrees: degree `n ≥ 0` carries `Gⁿ` and the negative degrees are zero.

It is the `ℕ`-indexed complex extended by zero along `ComplexShape.embeddingUpNat`, which is the
indexing the hyper-`Ext` spectral sequence of [Stacks, Tag 0AVI] is stated for. -/
def cechCochainComplex : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ :=
  (CochainComplex.of G d hdd).extend ComplexShape.embeddingUpNat

/-- The resolution complex is concentrated in the nonnegative degrees. This is Mathlib's instance
for an extension along `ComplexShape.embeddingUpNat`, restated for
`Stacks.EtaleCohomology.cechCochainComplex`, which is a definition and so opaque to instance
search. -/
instance isStrictlyGE_cechCochainComplex :
    CochainComplex.IsStrictlyGE (cechCochainComplex G d hdd) 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    ((CochainComplex.of G d hdd).extend ComplexShape.embeddingUpNat) 0)

/-- Degree `p ≥ 0` of the resolution complex is `Gᵖ`. -/
def cechCochainComplexXIso (p : ℕ) : (cechCochainComplex G d hdd).X (p : ℤ) ≅ G p :=
  (CochainComplex.of G d hdd).extendXIso ComplexShape.embeddingUpNat (i := p) rfl

/-- The differential of the `ℕ`-indexed resolution complex is `d`. -/
private lemma of_d_eq (n : ℕ) : (CochainComplex.of G d hdd).d n (n + 1) = d n := by
  simp

variable (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (a : F ⟶ G 0) (haug : a ≫ d 0 = 0)

/-- The augmentation of the `ℕ`-indexed resolution complex by `F` placed in degree zero,
determined by `a : F ⟶ G⁰`. -/
def cechNatAugmentation :
    (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj F ⟶ CochainComplex.of G d hdd :=
  HomologicalComplex.mkHomFromSingle a (fun k hk => by
    obtain rfl : k = 1 := by simpa [ComplexShape.up] using hk.symm
    rw [of_d_eq]
    exact haug)

/-- In degree zero the augmentation of the `ℕ`-indexed resolution complex is `a`. -/
private lemma cechNatAugmentation_f_zero :
    (cechNatAugmentation G d hdd F a haug).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).hom ≫ a :=
  HomologicalComplex.mkHomFromSingle_f _ _

variable (hmono : Mono a) (hex0 : (ShortComplex.mk a (d 0) haug).Exact)
  (hex : ∀ n, (ShortComplex.mk (d n) (d (n + 1)) (hdd n)).Exact)

include hmono hex0 hex in
/-- **Exactness of `0 → F → G⁰ → G¹ → ⋯` makes the augmentation of the `ℕ`-indexed complex a
quasi-isomorphism.** In degree zero this is the statement that `a` exhibits `F` as the kernel of
`d⁰`, and in the positive degrees it is exactness of `Gⁿ⁻¹ → Gⁿ → Gⁿ⁺¹`. -/
lemma quasiIso_cechNatAugmentation :
    QuasiIso (cechNatAugmentation G d hdd F a haug) := by
  have := hmono
  rw [quasiIso_iff]
  rintro (_ | n)
  · rw [CochainComplex.quasiIsoAt₀_iff]
    have w : a ≫ (CochainComplex.of G d hdd).d 0 1 = 0 := by rw [of_d_eq]; exact haug
    have hex0' : (ShortComplex.mk a ((CochainComplex.of G d hdd).d 0 1) w).Exact :=
      exact_congr rfl (of_d_eq G d hdd 0).symm haug w hex0
    exact shortComplex_quasiIso_of_isLimit _
      (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 F 0 0)
      (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 F 0 1)
      ((CochainComplex.of G d hdd).shape 0 0 (by simp)) a w hex0'.fIsKernel
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).hom
      (cechNatAugmentation_f_zero G d hdd F a haug).symm (Iso.isIso_hom _)
  · rw [quasiIsoAt_iff_exactAt _ (n + 1)
      (HomologicalComplex.ExactAt.of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 F (n + 1) (by omega))),
      HomologicalComplex.exactAt_iff' (K := CochainComplex.of G d hdd) (i := n) (j := n + 1)
        (k := n + 2) (CochainComplex.prev_nat_succ n) ((ComplexShape.up ℕ).next_eq' rfl)]
    exact exact_congr (of_d_eq G d hdd n).symm (of_d_eq G d hdd (n + 1)).symm _ _ (hex n)

/-- **The augmentation `F[0] ⟶ G^•` of the resolution complex** determined by `a : F ⟶ G⁰`: the
augmentation of the `ℕ`-indexed complex, extended by zero and read through the identification of
the extension of a single complex with a single complex. -/
def cechAugmentation :
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F ⟶ cechCochainComplex G d hdd :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
    HomologicalComplex.extendMap (cechNatAugmentation G d hdd F a haug)
      ComplexShape.embeddingUpNat

include hmono hex0 hex in
/-- **The augmentation of an exact resolution is a quasi-isomorphism.** This is
`Stacks.EtaleCohomology.quasiIso_cechNatAugmentation` carried across the extension by zero: a
quasi-isomorphism of `ℕ`-indexed complexes extends to one of `ℤ`-indexed complexes by
`HomologicalComplex.quasiIso_extendMap_iff`, and the remaining factor is an isomorphism. -/
lemma quasiIso_cechAugmentation : QuasiIso (cechAugmentation G d hdd F a haug) := by
  have := quasiIso_cechNatAugmentation G d hdd F a haug hmono hex0 hex
  exact inferInstanceAs (QuasiIso ((HomologicalComplex.extendSingleIso
      ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
    HomologicalComplex.extendMap (cechNatAugmentation G d hdd F a haug)
      ComplexShape.embeddingUpNat))

include hmono hex0 hex in
/-- **An exact resolution represents the sheaf it resolves, in the derived category.** The
augmentation becomes an isomorphism
`F[0] ≅ G^•` in `D(Ab(Y_étale))`, because it is a quasi-isomorphism. -/
def isoQCechCochainComplex :
    (DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).obj F ≅
      DerivedCategory.Q.obj (cechCochainComplex G d hdd) := by
  have h : IsIso (DerivedCategory.Q.map (cechAugmentation G d hdd F a haug)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact quasiIso_cechAugmentation G d hdd F a haug hmono hex0 hex
  exact asIso (DerivedCategory.Q.map (cechAugmentation G d hdd F a haug))

include hmono hex0 hex in
/-- **The spectral sequence of the second half of [Stacks, Tag 09Z2].** Let `F` be an abelian
sheaf on the small étale site of a scheme `Y` and let
```
0 → F → G⁰ → G¹ → G² → ⋯
```
be an exact sequence of abelian sheaves on that site. Then there is a cohomological spectral
sequence of abelian groups, starting on page one, with

```
E₁^{p,q} = H^q(Y, G^p),
```

together with a finite decreasing filtration `Fil^p H^n(Y, F)` of the étale cohomology of `F` in
each degree whose graded pieces are the terms of all sufficiently late pages, the differentials
into and out of each bidegree vanishing from some page on.

The shape of the convergence statement is the one
`StacksDraft.ExtSpectralSequence.exists_ext_complex_spectralSequence` ([Stacks, Tag 0AVI])
produces, transported along the identification of its abutment
`Ext^n(ℤ, G^•)` with `H^n(Y, F)`; that identification is
`Stacks.EtaleCohomology.isoQCechCochainComplex` followed by
`Stacks.EtaleCohomology.sheafHAddEquivZExt`.

In the source the resolution is the one coming from the Čech nerve of a finite surjection
`f : X ⟶ Y`, with `G^p = f_{p,*} f_p^{-1} F`; its exactness is the other half of the tag and is a
hypothesis here. -/
theorem exists_resolution_sheafH_spectralSequence :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1,
      (∀ p q : ℕ, Nonempty ((E.page 1).X ((p : ℤ), (q : ℤ)) ≅
          AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} (G p) q))) ∧
        ∃ (Fil : ∀ (_p : ℤ) (n : ℕ),
            Subobject (AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} F n)))
          (hFil : ∀ (p p' : ℤ) (n : ℕ), p ≤ p' → Fil p' n ≤ Fil p n),
          (∀ n : ℕ, ∃ s t : ℤ, s ≤ t ∧ Fil s n = ⊤ ∧ Fil t n = ⊥) ∧
            ∀ (p q : ℤ) (n : ℕ), p + q = (n : ℤ) → ∃ r₀ : ℤ, 1 ≤ r₀ ∧
              ∀ (r : ℤ) (hr : 1 ≤ r), r₀ ≤ r →
                (E.page r hr).d (p, q) (p + r, q + 1 - r) = 0 ∧
                  (E.page r hr).d (p - r, q + r - 1) (p, q) = 0 ∧
                    Nonempty ((E.page r hr).X (p, q) ≅
                      cokernel (Subobject.ofLE (Fil (p + 1) n) (Fil p n)
                        (hFil p (p + 1) n (by omega)))) := by
  classical
  obtain ⟨E, e₁, Fil₀, hFil₀, hfin, hconv⟩ :=
    StacksDraft.ExtSpectralSequence.exists_ext_complex_spectralSequence
      (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (constZ Y) (cechCochainComplex G d hdd)
      ⟨0, inferInstance⟩
  -- the identification of the abutment of 0AVI with étale cohomology
  have eAb : ∀ n : ℕ, AddCommGrpCat.of (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).obj (constZ Y))
      (DerivedCategory.Q.obj (cechCochainComplex G d hdd)) (n : ℤ)) ≅
      AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} F n) := fun n =>
    extIsoOfIsoRight _ (isoQCechCochainComplex G d hdd F a haug hmono hex0 hex).symm (n : ℤ) ≪≫
      (sheafHAddEquivZExt F n).symm.toAddCommGrpIso
  refine ⟨E, fun p q => ⟨e₁ (p : ℤ) (q : ℤ) ≪≫
    extIsoOfIsoRight _ ((DerivedCategory.singleFunctor
        (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).mapIso
      (cechCochainComplexXIso G d hdd p)) (q : ℤ) ≪≫
    (sheafHAddEquivZExt (G p) q).symm.toAddCommGrpIso⟩,
    fun p n => Subobject.mk ((Fil₀ p (n : ℤ)).arrow ≫ (eAb n).hom), ?_, ?_, ?_⟩
  · intro p p' n hp
    exact Subobject.mk_le_mk_of_comm (Subobject.ofLE _ _ (hFil₀ p p' (n : ℤ) hp))
      (by rw [← Category.assoc, Subobject.ofLE_arrow])
  · intro n
    obtain ⟨s, t, hst, hs, ht⟩ := hfin (n : ℤ)
    refine ⟨s, t, hst, ?_, ?_⟩
    · change Subobject.mk ((Fil₀ s (n : ℤ)).arrow ≫ (eAb n).hom) = ⊤
      rw [hs]
      exact Subobject.mk_eq_top_of_isIso _
    · change Subobject.mk ((Fil₀ t (n : ℤ)).arrow ≫ (eAb n).hom) = ⊥
      rw [ht, Subobject.mk_eq_bot_iff_zero, Subobject.bot_arrow, zero_comp]
  · -- the comparison of graded pieces, with the abutment degree an arbitrary integer equal to `n`
    have key : ∀ (n : ℕ) (m : ℤ), m = (n : ℤ) → ∀ (p : ℤ)
        (h₀ : Fil₀ (p + 1) m ≤ Fil₀ p m)
        (h₁ : Subobject.mk ((Fil₀ (p + 1) (n : ℤ)).arrow ≫ (eAb n).hom) ≤
          Subobject.mk ((Fil₀ p (n : ℤ)).arrow ≫ (eAb n).hom)),
        Nonempty (cokernel (Subobject.ofLE _ _ h₀) ≅ cokernel (Subobject.ofLE _ _ h₁)) := by
      intro n m hm p h₀ _
      subst hm
      exact ⟨cokernelMkIso (eAb n) _ _ h₀⟩
    intro p q n hn
    obtain ⟨r₀, hr₀, H⟩ := hconv p q
    refine ⟨r₀, hr₀, fun r hr hle => ⟨(H r hr hle).1, (H r hr hle).2.1, ?_⟩⟩
    exact ⟨(H r hr hle).2.2.some ≪≫ (key n (p + q) hn p _ _).some⟩

end Stacks.EtaleCohomology

end
