module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.HomBicomplexSpectralSequences
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.AntiInvariantSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.HomBicomplex
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.KoszulResolution

/-!
# The termwise `Ext` spectral sequence of the alternating Čech complex

Let `X` be an algebraic space over a scheme `S`, let `U` be an algebraic space étale over `X`
and let `ℱ` be an abelian sheaf on the spaces-étale site of `X`.  Writing `K^p = ∧^{p+1} j_{U!} ℤ`
for the terms of the Koszul complex, the Hom bicomplex `Hom(K^p, I^q)` of an injective
resolution `ℱ ⟶ I^•` has a total complex, and the filtration of that total complex by the Koszul
degree produces a cohomological spectral sequence whose first page is
`E₁^{p,q} = Ext^q_{Ab(X_étale)}(K^p, ℱ)`.

This is the spectral sequence of Stacks 0725.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.zExtKoszulCochainComplexXIso` identifies the `Ext` group
  out of the term of the Koszul complex read in cochain degree `-p` with the one out of `K^p`.
* `AlgebraicGeometry.Space.SpacesEtale.koszulCochainAugmentation` is the augmentation
  `K^• ⟶ ℤ[0]` read in nonpositive cochain degrees, and
  `AlgebraicGeometry.Space.SpacesEtale.koszulCochainComplexQIso` is the isomorphism
  `K^• ≅ ℤ[0]` it induces in the derived category for a surjective `U ⟶ X`.
* `AlgebraicGeometry.Space.SpacesEtale.sheafHIsoZExt` identifies the sheaf cohomology
  `H^n(X, ℱ)` of Mathlib with the `Ext` group out of the constant sheaf `ℤ`.
* `AlgebraicGeometry.Space.SpacesEtale.zExtZeroKoszulSignSectionsAddEquiv` identifies the `Ext`
  group in degree `0` out of `K^p` with the `S_{p+1}`-anti-invariant sections of `ℱ` over `W_p`,
  for a separated `U ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.exists_alternatingCechExtSpectralSequence`: the
  cohomological spectral sequence with `E₁^{p,q} = Ext^q(K^p, ℱ)`, abutting to the hyper-`Ext`
  groups `Ext^{p+q}(K^•, ℱ)` of the Koszul complex.
* `AlgebraicGeometry.Space.SpacesEtale.exists_alternatingCechCohomologySpectralSequence`:
  for a *surjective* `U ⟶ X`, the same spectral sequence, concentrated in the first quadrant
  and abutting to the sheaf cohomology `H^{p+q}(X, ℱ)`.
* `AlgebraicGeometry.Space.SpacesEtale.exists_alternatingCechSignTwistedSpectralSequence`:
  **Stacks 0728** for a surjective, étale and separated `U ⟶ X`, the same spectral sequence with
  the row `q = 0` of its first page read as the `S_{p+1}`-anti-invariant sections of `ℱ` over
  `W_p`, and converging to `H^{p+q}(X, ℱ)`.

## Implementation notes

The spectral sequence is the one of [Stacks 07AA],
`CochainComplex.exists_termwiseExtSpectralSequence`, applied to the Koszul complex read in
nonpositive cochain degrees: that complex is bounded above by
`AlgebraicGeometry.Space.SpacesEtale.koszulCochainComplex_minus`, which is the only hypothesis
of the source. Its first page is `Ext^q` of the term in cochain degree `-p`, which is `K^p` by
`AlgebraicGeometry.Space.SpacesEtale.koszulCochainComplexXIso`; transporting the `Ext` group
along that isomorphism is `zExtKoszulCochainComplexXIso`, precomposition in the derived
category, written as the Yoneda image of the isomorphism so that its naturality is inherited.

The abutment of [Stacks 07AA] is the hyper-`Ext` of the Koszul complex, `Ext^n(K^•, ℱ)`. For a
surjective `U ⟶ X` it is the sheaf cohomology `H^n(X, ℱ)` asserted by Stacks 0725: Mathlib's
`CategoryTheory.Sheaf.H` *defines* `H^n(X, ℱ)` as `Ext^n` out of the constant sheaf `ℤ`, which
is `AlgebraicGeometry.Space.SpacesEtale.constantIntSheaf`, and the augmentation `K^• ⟶ ℤ[0]` is
then a quasi-isomorphism by [Stacks 0723],
`AlgebraicGeometry.Space.SpacesEtale.koszulAugmentation_quasiIso`. That augmentation is a map of
chain complexes indexed by `ℕ`, so it is carried to the cochain indexing by
`HomologicalComplex.extendMap` along `ComplexShape.embeddingDownNat` and
`HomologicalComplex.extendSingleIso`, both of which preserve quasi-isomorphisms; the abutment is
then transported by `CategoryTheory.SpectralSequence.AbutsTo.of_iso`.

The first page vanishes outside the first quadrant: for `p < 0` because the Koszul complex has
no term in positive cochain degree, and for `q < 0` because `Ext^q` out of an object of the heart
into an object of the heart vanishes in negative degrees, which is the degenerate case
`DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE` of [Stacks 06XS].

Stacks 0728 reads the first page of this spectral sequence as the cohomology of the quotient
`U_p = W_p/S_{p+1}` of the complement of the diagonals in the `(p+1)`-fold self-product of `U`
over `X`, with coefficients twisted by the sign character.  Only the row `q = 0` is available
here, as the group of anti-invariant sections of `ℱ` over `W_p`: that row is
`Hom(K^p, ℱ)`, which is the anti-invariant sections by [Stacks 0726],
`AlgebraicGeometry.Space.SpacesEtale.koszulHomSignSectionsEquiv`, and which [Stacks 0727]
identifies with `H^0(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))`.  The higher rows would need the quotient `U_p`
itself, hence [Stacks 071S] for a free action of a finite group on an algebraic space, which is
available only for an action on an object of the big fppf site.  That row is stated as an
`AddEquiv` rather than as an isomorphism of `AddCommGrpCat`: the pages of the spectral sequence
live at level `u + 2` and the sections of `ℱ` at level `u + 1`, so the two groups are objects of
different categories and only their carriers can be compared.

Two instances are supplied file-locally rather than assumed.
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` is a global instance, but the universe
of `CategoryTheory.IsGrothendieckAbelian` is not determined by its conclusion, so instance
search cannot find it; `enoughInjectivesSheafSpacesEtale` below pins that universe to `u + 1`,
the level at which the spaces-étale site is a small category, and is an instance so that the
source of [Stacks 07AA] applies. `CategoryTheory.HasDerivedCategory.standard` is deliberately
not a global instance in Mathlib, since the universe of the derived category is a choice; it is
made a local instance here, which fixes that universe at `u + 2`, the level at which
[Stacks 07AA] states its pages.

## References

* [Stacks, Tag 0725](https://stacks.math.columbia.edu/tag/0725)
* [Stacks, Tag 07AA](https://stacks.math.columbia.edu/tag/07AA)
* [Stacks, Tag 0723](https://stacks.math.columbia.edu/tag/0723)
* [Stacks, Tag 0724](https://stacks.math.columbia.edu/tag/0724)
* [Stacks, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- Abelian sheaves on the spaces-étale site of an algebraic space have enough injectives,
being a Grothendieck abelian category at the level at which that site is small. -/
instance enoughInjectivesSheafSpacesEtale :
    EnoughInjectives (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) := by
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) := inferInstance
  infer_instance

/-- The image in the derived category of the identification of the term of the Koszul complex in
cochain degree `-p` with `K^p`. -/
def singleKoszulCochainComplexXIso (U : SpacesEtale B S hS X) (p : ℕ) :
    (DerivedCategory.singleFunctor
        (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj
        ((koszulCochainComplex B S hS X U).X (-(p : ℤ))) ≅
      (DerivedCategory.singleFunctor
        (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj
        ((koszulComplex B S hS X U).X p) :=
  (DerivedCategory.singleFunctor _ 0).mapIso (koszulCochainComplexXIso B S hS X U p)

/-- The `Ext` group out of the term of the Koszul complex read in cochain degree `-p` is the
`Ext` group out of `K^p`. -/
def zExtKoszulCochainComplexXIso (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ) (q : ℤ) :
    AddCommGrpCat.of
        (Abelian.zExt ((koszulCochainComplex B S hS X U).X (-(p : ℤ))) F q) ≅
      AddCommGrpCat.of (Abelian.zExt ((koszulComplex B S hS X U).X p) F q) :=
  (preadditiveYoneda.obj ((shiftFunctor _ q).obj
      ((DerivedCategory.singleFunctor
        (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj F))).mapIso
    (singleKoszulCochainComplexXIso B S hS X U p).symm.op

/-- **Stacks 0725, the first page of the spectral sequence.** Let `X` be an algebraic space over
a scheme `S`, let `U` be an algebraic space étale over `X` and let `ℱ` be an abelian sheaf on the
spaces-étale site of `X`. There is a cohomological spectral sequence, starting on page one, with
`E₁^{p,q} = Ext^q_{Ab(X_étale)}(K^p, ℱ)` for `K^p = ∧^{p+1} j_{U!} ℤ` the terms of the Koszul
complex, abutting to the hyper-`Ext` groups `Ext^{p+q}(K^•, ℱ)` of the Koszul complex.

It is the spectral sequence of the total complex of the Hom bicomplex `Hom(K^p, I^q)` filtered
by the Koszul degree, for `I^•` an injective resolution of `ℱ`. -/
@[stacks 0725 "the spectral sequence with E₁^{p,q} = Ext^q(K^p, ℱ), abutting to Ext^{p+q}(K^•, ℱ)"]
theorem exists_alternatingCechExtSpectralSequence (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 2} 1,
      (∀ (p : ℕ) (q : ℤ), Nonempty ((E.page 1).X ((p : ℤ), q) ≅
        AddCommGrpCat.of (Abelian.zExt ((koszulComplex B S hS X U).X p) F q))) ∧
      SpectralSequence.AbutsTo E (fun n ↦ AddCommGrpCat.of
        (DerivedCategory.Ext (DerivedCategory.Q.obj (koszulCochainComplex B S hS X U))
          ((DerivedCategory.singleFunctor
            (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj F) n)) := by
  obtain ⟨E, hE, hAbuts⟩ := CochainComplex.exists_termwiseExtSpectralSequence
    (koszulCochainComplex B S hS X U) (koszulCochainComplex_minus B S hS X U) F
  refine ⟨E, fun p q => ?_, hAbuts⟩
  obtain ⟨e⟩ := hE (p : ℤ) q
  exact ⟨e ≪≫ zExtKoszulCochainComplexXIso B S hS X U F p q⟩

/-! ### The abutment for a surjective cover -/

/-- `Ext` groups of abelian sheaves on the spaces-étale site of an algebraic space are small at
the level at which that site is a small category. -/
instance hasExtSheafSpacesEtale :
    HasExt.{u + 2} (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- The augmentation `K^• ⟶ ℤ[0]` of the Koszul complex of `U`, read as a map of cochain
complexes indexed by `ℤ` with `K^p` in degree `-p`. -/
def koszulCochainAugmentation (U : SpacesEtale B S hS X) :
    koszulCochainComplex B S hS X U ⟶
      (HomologicalComplex.single (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ) 0).obj (constantIntSheaf B S hS X) :=
  HomologicalComplex.extendMap (koszulAugmentation B S hS X U) ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (constantIntSheaf B S hS X) 0 0 (by simp)).hom

/-- For `U` surjective over `X` the augmentation read in cochain degrees is a
quasi-isomorphism, extension by zero along `ComplexShape.embeddingDownNat` preserving
quasi-isomorphisms. -/
theorem quasiIso_koszulCochainAugmentation (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom) :
    QuasiIso (koszulCochainAugmentation B S hS X U) := by
  have h := koszulAugmentation_quasiIso B S hS X U hsurj
  have h₁ : QuasiIso (HomologicalComplex.extendMap (koszulAugmentation B S hS X U)
      ComplexShape.embeddingDownNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 h
  exact quasiIso_comp (HomologicalComplex.extendMap (koszulAugmentation B S hS X U)
    ComplexShape.embeddingDownNat) _

/-- For `U` surjective over `X` the Koszul complex is isomorphic in the derived category to the
constant sheaf `ℤ` placed in degree `0`. -/
def koszulCochainComplexQIso (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom) :
    DerivedCategory.Q.obj (koszulCochainComplex B S hS X U) ≅
      (DerivedCategory.singleFunctor
        (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj (constantIntSheaf B S hS X) :=
  have : IsIso (DerivedCategory.Q.map (koszulCochainAugmentation B S hS X U)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_koszulCochainAugmentation B S hS X U hsurj)
  asIso (DerivedCategory.Q.map (koszulCochainAugmentation B S hS X U))

/-- For `U` surjective over `X` the hyper-`Ext` group `Ext^n(K^•, ℱ)` is the `Ext` group
`Ext^n(ℤ, ℱ)` out of the constant sheaf of integers. -/
def extKoszulCochainComplexIso (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (n : ℤ) :
    AddCommGrpCat.of (DerivedCategory.Ext
        (DerivedCategory.Q.obj (koszulCochainComplex B S hS X U))
        ((DerivedCategory.singleFunctor
          (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj F) n) ≅
      AddCommGrpCat.of (Abelian.zExt (constantIntSheaf B S hS X) F n) :=
  (preadditiveYoneda.obj ((shiftFunctor _ n).obj
      ((DerivedCategory.singleFunctor
        (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj F))).mapIso
    (koszulCochainComplexQIso B S hS X U hsurj).symm.op

/-- The sheaf cohomology `H^n(X, ℱ)` of an abelian sheaf on the spaces-étale site of `X` is the
`Ext` group `Ext^n(ℤ, ℱ)` out of the constant sheaf of integers, read in the derived category. -/
def sheafHIsoZExt (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H F n) ≅
      AddCommGrpCat.of (Abelian.zExt (constantIntSheaf B S hS X) F (n : ℤ)) :=
  Abelian.Ext.homAddEquiv.toAddCommGrpIso

/-- **Stacks 0725.** Let `X` be an algebraic space over a scheme `S`, let `U` be an algebraic
space étale and *surjective* over `X` and let `ℱ` be an abelian sheaf on the spaces-étale site
of `X`. There is a first-quadrant cohomological spectral sequence, starting on page one, with
`E₁^{p,q} = Ext^q_{Ab(X_étale)}(K^p, ℱ)` for `K^p = ∧^{p+1} j_{U!} ℤ` the terms of the Koszul
complex, abutting to the sheaf cohomology `H^{p+q}(X, ℱ)`.

The abutment is written as the `Ext` group out of the constant sheaf `ℤ`, which is Mathlib's
definition of sheaf cohomology; the last conjunct records that identification. -/
@[stacks 0725 "the abutment is the cohomology of X, for a surjective cover"]
theorem exists_alternatingCechCohomologySpectralSequence (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 2} 1,
      (∀ (p : ℕ) (q : ℤ), Nonempty ((E.page 1).X ((p : ℤ), q) ≅
        AddCommGrpCat.of (Abelian.zExt ((koszulComplex B S hS X U).X p) F q))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 1).X (p, q))) ∧
      SpectralSequence.AbutsTo E
        (fun n ↦ AddCommGrpCat.of (Abelian.zExt (constantIntSheaf B S hS X) F n)) ∧
      ∀ n : ℕ, Nonempty (AddCommGrpCat.of (Sheaf.H F n) ≅
        AddCommGrpCat.of (Abelian.zExt (constantIntSheaf B S hS X) F (n : ℤ))) := by
  obtain ⟨E, hE, hAbuts⟩ := CochainComplex.exists_termwiseExtSpectralSequence
    (koszulCochainComplex B S hS X U) (koszulCochainComplex_minus B S hS X U) F
  refine ⟨E, fun p q => ?_, fun p q hpq => ?_,
    hAbuts.of_iso fun n => extKoszulCochainComplexIso B S hS X U hsurj F n,
    fun n => ⟨sheafHIsoZExt B S hS X F n⟩⟩
  · obtain ⟨e⟩ := hE (p : ℤ) q
    exact ⟨e ≪≫ zExtKoszulCochainComplexXIso B S hS X U F p q⟩
  · obtain ⟨e⟩ := hE p q
    refine IsZero.of_iso ?_ e
    have : Subsingleton (Abelian.zExt ((koszulCochainComplex B S hS X U).X (-p)) F q) := by
      refine subsingleton_of_forall_eq 0 fun f => ?_
      rcases hpq with hp | hq
      · have hterm : IsZero ((koszulCochainComplex B S hS X U).X (-p)) :=
          isZero_koszulCochainComplex_X B S hS X U (-p) (by omega)
        exact (Functor.map_isZero (DerivedCategory.singleFunctor _ 0) hterm).eq_of_src _ _
      · have hbij := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
          ((DerivedCategory.singleFunctor
            (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj
              ((koszulCochainComplex B S hS X U).X (-p)))
          ((DerivedCategory.singleFunctor
            (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj F) 0 0 q q
          (by omega) (by omega)
        have hzero : IsZero ((DerivedCategory.homologyFunctor
            (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) q).obj
            ((DerivedCategory.singleFunctor
              (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj F)) :=
          DerivedCategory.isZero_of_isGE _ 0 q (by omega)
        exact hbij.1 (hzero.eq_of_tgt _ _)
    exact AddCommGrpCat.isZero_of_subsingleton _

/-! ### The row `q = 0` of the first page, for a separated cover -/

/-- The `Ext` group in degree `0` between two abelian sheaves is the group of morphisms between
them. -/
def zExtZeroAddEquivHom (A F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    Abelian.zExt A F 0 ≃+ (A ⟶ F) :=
  (show Abelian.zExt A F 0 ≃+ Abelian.Ext A F 0 from
    Abelian.Ext.homAddEquiv.symm).trans Abelian.Ext.addEquiv₀

/-- The `Ext` group in degree `0` out of `K^p` is the group of `S_{p+1}`-anti-invariant sections
of `ℱ` over `W_p`, by the identification of [Stacks 0726]. -/
def zExtZeroKoszulSignSectionsAddEquiv (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    Abelian.zExt ((koszulComplex B S hS X U).X p) F 0 ≃+
      characterSections (diagonalComplement B S hS X U (p + 1) hsep)
        (diagonalComplementAut B S hS X U (p + 1) hsep) Equiv.Perm.sign F.obj :=
  (zExtZeroAddEquivHom B S hS X ((koszulComplex B S hS X U).X p) F).trans
    (koszulHomSignSectionsEquiv B S hS X U p hsep F)

/-- **Stacks 0728.** Let `S` be a scheme, let `f : U ⟶ X` be a surjective, étale and separated
morphism of algebraic spaces over `S` and let `ℱ` be an abelian sheaf on the spaces-étale site
of `X`.  The spectral sequence of [Stacks 0725] is concentrated in the first quadrant, the row
`q = 0` of its first page is the group of `S_{p+1}`-anti-invariant sections of `ℱ` over
`W_p = U ×_X ⋯ ×_X U ∖ (all diagonals)`, and it converges to the sheaf cohomology
`H^{p+q}(X, ℱ)`.

The group of anti-invariant sections is what [Stacks 0727] identifies with
`H^0(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))` for `U_p = W_p/S_{p+1}`; the higher rows of the first page are
stated here as the `Ext` groups out of `K^p` of [Stacks 0725], the quotient `U_p` of an
algebraic space by a free action of a finite group not being available. -/
@[stacks 0728 "the row q = 0 of the E₁-page, as the S_{p+1}-anti-invariant sections of ℱ over \
W_p, and the convergence to H^{p+q}(X, ℱ)"]
theorem exists_alternatingCechSignTwistedSpectralSequence (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (hsep : IsSeparated B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 2} 1,
      (∀ (p : ℕ) (q : ℤ), Nonempty ((E.page 1).X ((p : ℤ), q) ≅
        AddCommGrpCat.of (Abelian.zExt ((koszulComplex B S hS X U).X p) F q))) ∧
      (∀ p : ℕ, Nonempty ((E.page 1).X ((p : ℤ), 0) ≃+
        characterSections (diagonalComplement B S hS X U (p + 1) hsep)
          (diagonalComplementAut B S hS X U (p + 1) hsep) Equiv.Perm.sign F.obj)) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 1).X (p, q))) ∧
      SpectralSequence.AbutsTo E
        (fun n ↦ AddCommGrpCat.of (Abelian.zExt (constantIntSheaf B S hS X) F n)) ∧
      ∀ n : ℕ, Nonempty (AddCommGrpCat.of (Sheaf.H F n) ≅
        AddCommGrpCat.of (Abelian.zExt (constantIntSheaf B S hS X) F (n : ℤ))) := by
  obtain ⟨E, hE, hvanish, hAbuts, hH⟩ :=
    exists_alternatingCechCohomologySpectralSequence B S hS X U hsurj F
  refine ⟨E, hE, fun p => ?_, hvanish, hAbuts, hH⟩
  obtain ⟨e⟩ := hE p 0
  exact ⟨e.addCommGroupIsoToAddEquiv.trans
    (zExtZeroKoszulSignSectionsAddEquiv B S hS X U p hsep F)⟩

end AlgebraicGeometry.Space.SpacesEtale

end
