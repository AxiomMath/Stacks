module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Scheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.CoverBound
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.BaseChange
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.TopologicalBasis
import StacksFrontier.CategoryTheory.Sites.Hypercovering.Spaces

/-!
# A complex universally computing the direct images of a quasi-coherent module

Let `f : X ⟶ S` be a morphism of schemes and let `𝓕` be a quasi-coherent `𝒪_X`-module.
[Stacks, Tag 01XN] asserts that there is a bounded below complex `𝓚⁼` of quasi-coherent
`𝒪_S`-modules such that for *every* morphism `g : S' ⟶ S` the ordinary inverse image `g^*𝓚⁼`
represents `Rf'_*𝓕'`, with the notation of the cartesian square of [Stacks, Tag 02KF].  The
pullback is the ordinary one and not the derived one, so this is a statement about the complex
`𝓚⁼` itself and not about its class in the derived category.

**This file proves the tag for an affine morphism `f`**, where the complex can be written down:
`𝓚⁼` is the ordinary direct image `f_*𝓕` placed in degree zero and zero elsewhere.  Its terms are
quasi-coherent, and for every `g : S' ⟶ S` the inverse image `g^*𝓚⁼` represents `Rf'_*𝓕'` because

* `g^*f_*𝓕 ≅ f'_*𝓕'` is the affine base-change isomorphism of [Stacks, Tag 02KG], which holds at
  every quasi-coherent module as soon as `f` is affine, for an arbitrary base change `g`;  and
* `Rf'_*𝓕' ≅ (f'_*𝓕')[0]`, because `f'` is again affine, being a base change of `f`, so the
  higher direct images of the quasi-coherent module `𝓕'` along it vanish ([Stacks, Tag 01XC]).

The file also supplies, for the general quasi-compact quasi-separated case, the hypercovering
`K = (I, {U_i})` of `X` by affine opens with every `I_n` finite ([Stacks, Tag 01H7]) and the
complex built from it:  writing `f_i : U_i ⟶ S` for the restriction of `f`,

`𝓚⁼ = ( ∏_{i ∈ I₀} f_{i,*}𝓕|_{U_i} ⟶ ∏_{i ∈ I₁} f_{i,*}𝓕|_{U_i} ⟶ ⋯ )`,

together with the quasi-coherence of its terms and of the terms of each of its inverse images.

## Main definitions

* `opensOverTop`:  the site of opens of `X` over the top open, regarded as objects over `X`.
* `pushforwardPresheaf`:  the presheaf `U ↦ (U.ι ≫ f)_* (U.ι)^*𝓕` of `𝒪_S`-modules on that site.
* `hypercoveringPushforwardComplex`:  the complex `𝓚⁼` above, for a simplicial object `K` of
  formal coproducts of opens of `X`, as a bounded below complex of `𝒪_S`-modules.
* `canonicalBaseChangeDiagram`:  the cartesian square of [Stacks, Tag 02KF] obtained from `f` and
  `g : S' ⟶ S` by taking the fibre product `X ×_S S'`.
* `singleComplexPlus`:  an `𝒪_S`-module placed in degree zero, as a bounded below complex.
* `UniversalPushforwardComplex`:  a bounded below complex of `𝒪_S`-modules with the two properties
  [Stacks, Tag 01XN] asserts — quasi-coherent terms, and an isomorphism `g^*𝓚⁼ ≅ Rf'_*𝓕'` in
  `D⁺(S')` for every `g`.  The isomorphisms are fields, not an existence statement, so the data
  travel as data.
* `affineBaseChangeSingleIso`:  for `f` affine, the isomorphism `g^*(f_*𝓕)[0] ≅ Rf'_*𝓕'` in
  `D⁺(S')`, for every `g : S' ⟶ S`.

## Main results

* `universalPushforwardComplex`:  **[Stacks, Tag 01XN] for an affine morphism** — the complex
  `(f_*𝓕)[0]`, with quasi-coherent terms and with the base-change isomorphism for every `g`.
* `exists_finite_affine_hypercovering`:  **a quasi-compact, quasi-separated scheme has a
  hypercovering of its site of opens, finite in every simplicial degree, all of whose members are
  affine opens.**
* `exists_finite_affine_hypercovering_isAffineHom`:  under the quasi-compactness and
  quasi-separatedness hypotheses of [Stacks, Tag 01XN] the same hypercovering has, in addition,
  the property that the restriction `f_i : U_i ⟶ S` of `f` to each of its members is affine.
* `hypercoveringPushforwardComplex_obj_isQuasicoherent`:  **every term of the hypercovering
  complex is a quasi-coherent `𝒪_S`-module**, as soon as every `I_n` is finite, every member of
  the hypercovering is affine, and `S` is separated.
* `isQuasicoherent_pullback_X`:  every term of every inverse image of a complex with
  quasi-coherent terms is quasi-coherent, which is [Stacks, Tag 01BG] read degreewise.
* `isAffineOpen_inf_preimage_of_isAffineHom` and `isAffineOpen_hypercovering_inf_preimage`:  **an
  open `U` of `X` with `f_U : U ⟶ S` affine meets `f^{-1}(V)` in an affine open for every affine
  open `V` of `S`**, and in particular every member of the hypercovering does.
* `iSup_inf_preimage_eq_preimage`:  in degree zero those intersections cover `f^{-1}(V)`.
* `hypercoveringPushforwardComplexXZeroIso` and `iSup_left_eq_top`:  the degree zero term of the
  hypercovering complex is the product of the `f_{i,*}𝓕|_{U_i}` over `I₀`, and those `U_i` cover
  `X`.
* `isZero_derivedPushforward'_of_isZero`:  a complex with the universal property can pull back to
  a zero object only where `Rf'_*𝓕'` vanishes, so a zero witness asserts nothing only when the
  derived direct image itself is zero.
* `universalPushforwardComplex_complex` and `universalPushforwardComplexXZeroIso`:  the complex
  delivered for an affine morphism is `(f_*𝓕)[0]`, and its degree zero term is `f_*𝓕`.

## Implementation notes

For an affine morphism the three fields of `UniversalPushforwardComplex` are discharged
independently:  quasi-coherence of `f_*𝓕` is [Stacks, Tag 01XD], the terms in the other degrees
are zero objects, and the base-change isomorphism is `affineBaseChangeSingleIso`, which uses
nothing about `S'` — the base change of an affine morphism is affine over an arbitrary base, so
the universal quantification over `g` costs nothing.  `DerivedCategory.Plus.Q` of a single
complex *is* the single object of `D⁺`, so no comparison is needed on that side.

*Not covered.*  The general quasi-compact quasi-separated case is not proved here, nor anywhere
in the library.  What it needs is a comparison between a hypercovering complex and a derived
*direct* image.  The library has the hypercovering comparison of [Stacks, Tag 01GY] against
derived *global sections* — `Stacks.CategoryTheory.Hypercovering.hypercoverComparisonMap`, whose
target is `derivedSectionsFunctor` — and it has it as an *isomorphism* whenever the coefficient
sheaf is acyclic on the members of the hypercovering
(`Stacks.CategoryTheory.Hypercovering.isIso_hypercoverComparisonMap_app`), hence in particular
for a quasi-coherent module and a hypercovering by affine opens
(`Stacks.Cohomology.HypercoveringModules.isIso_cechModuleCohomology_app`).  What is absent is the
relative comparison *morphism* `𝓚⁼ ⟶ Rf_*𝓕` in `D⁺(S)`, which the source obtains from an
injective resolution of `𝓕` and leaves as "details omitted".

The case in which `X` has affine diagonal does not need any of that and is proved, through the
relative Čech complex of [Stacks, Tag 01XM], in
`StacksFrontier.AlgebraicGeometry.RelativeCechComplex.UniversalPushforwardAffineDiagonal`.

The hypercovering is obtained from the general construction over a topological basis by taking
the basis of affine opens:  it is a basis, its members are quasi-compact, and finite intersections
of quasi-compact opens of a quasi-separated space are quasi-compact, which are exactly the three
hypotheses of that construction.  Quasi-compactness and quasi-separatedness of `X` itself follow
from the hypotheses of the tag, the second one because a separated scheme is quasi-separated.

Affineness of `f_i` is affineness of a morphism with affine source into a separated scheme; no
hypothesis on `f` enters.  This is also what makes the terms of the complex quasi-coherent,
through the same three closure properties as for the Čech complex of an affine open covering:
an inverse image of a quasi-coherent module is quasi-coherent, a direct image along an affine
morphism is, and a finite product of quasi-coherent modules is.

The hypercovering complex is Mathlib's cochain complex of a simplicial object of formal
coproducts, whose degree `n` term is the product, over the index type of `K_n`, of the values of
the coefficient presheaf on the components — that is the shape of the complex of the tag, with no
Čech nerve and no intersections, because a hypercovering already carries the higher degrees.  The
coefficient presheaf is the one of [Stacks, Tag 01XL] on `Over X`, restricted along
`opensOverTop`.  Indexing is converted from `ℕ` to `ℤ` by `ComplexShape.embeddingUpNat`, which is
also what witnesses the lower bound.  The index type of each `K_n` is forced into `Type u`:  the
cochain complex functor needs products of that size in `S.Modules`, which has products of size
`u` only.

## References

* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 01H7](https://stacks.math.columbia.edu/tag/01H7)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02KF](https://stacks.math.columbia.edu/tag/02KF)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.UniversalPushforward

open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.CategoryTheory.Hypercovering

/-! ### Hypercoverings by affine opens -/

/-- **A quasi-compact, quasi-separated scheme has a hypercovering by affine opens which is finite
in every simplicial degree.**  The affine opens form a basis of the topology, each of them is
quasi-compact, and a finite intersection of quasi-compact opens of a quasi-separated space is
quasi-compact; these are the hypotheses under which a hypercovering subordinate to a basis,
degreewise finite, exists. -/
theorem exists_finite_affine_hypercovering (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))),
      IsHypercovering (Opens.pretopology X) K ∧
        ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I ∧
          ∀ i : (K.obj (op ⦋n⦌)).I, IsAffineOpen ((K.obj (op ⦋n⦌)).obj i).left := by
  obtain ⟨K, hK, hfin⟩ :=
    exists_finite_hypercovering_of_isTopologicalBasis
      (((↑) : X.Opens → Set X) '' X.affineOpens) X.isBasis_affineOpens
      CompactSpace.isCompact_univ
      (by rintro U ⟨V, hV, rfl⟩; exact hV.isCompact)
      QuasiSeparatedSpace.inter_isCompact
  refine ⟨K, hK, fun n => ⟨(hfin n).1, fun i => ?_⟩⟩
  obtain ⟨V, hV, hVe⟩ := (hfin n).2 i
  exact (SetLike.coe_injective hVe : V = _) ▸ hV

/-- **The hypercovering of [Stacks, Tag 01XN], together with the affineness of the restrictions of
`f` to its members.**  For `f` quasi-compact and quasi-separated and `S` quasi-compact and
separated, `X` is itself quasi-compact and quasi-separated, so it has a degreewise finite
hypercovering by affine opens `U_i`; and `f_i : U_i ⟶ S` is affine because its source is affine
and `S` is separated. -/
theorem exists_finite_affine_hypercovering_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] [S.IsSeparated] :
    ∃ K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))),
      IsHypercovering (Opens.pretopology X) K ∧
        ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I ∧
          ∀ i : (K.obj (op ⦋n⦌)).I,
            IsAffineOpen ((K.obj (op ⦋n⦌)).obj i).left ∧
              IsAffineHom (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨K, hK, hfin⟩ := exists_finite_affine_hypercovering X
  refine ⟨K, hK, fun n => ⟨(hfin n).1, fun i => ⟨(hfin n).2 i, ?_⟩⟩⟩
  have : IsAffine ((K.obj (op ⦋n⦌)).obj i).left := (hfin n).2 i
  exact isAffineHom_of_isAffine_source _

/-! ### The coefficient presheaf on the site of opens -/

/-- **The opens of `X` over the top open, as objects over `X`.**  An open `U` goes to the open
immersion `U.ι : U ⟶ X`. -/
noncomputable def opensOverTop (X : Scheme.{u}) : Over (⊤ : Opens X) ⥤ Over X :=
  Over.forget _ ⋙ Stacks.CechSiteChange.opensOver X

/-- The value of `opensOverTop` is the open immersion of the open subscheme. -/
theorem opensOverTop_obj {X : Scheme.{u}} (A : Over (⊤ : Opens X)) :
    (opensOverTop X).obj A = Over.mk (Scheme.Opens.ι (X := X) A.left) := rfl

variable {X S : Scheme.{u}}

/-- **The coefficient presheaf of the complex of [Stacks, Tag 01XN].**  It is the coefficient
presheaf of [Stacks, Tag 01XL] on `Over X`, restricted along `opensOverTop`:  an open `U` of `X`
goes to the `𝒪_S`-module `(U.ι ≫ f)_* (U.ι)^*𝓕`, with the canonical restriction maps, and the
whole is functorial in the quasi-coherent `𝒪_X`-module `𝓕`. -/
noncomputable def pushforwardPresheaf (f : X ⟶ S) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      ((Over (⊤ : Opens X))ᵒᵖ ⥤ S.Modules) :=
  relativeCechPresheaf f ⋙
    (Functor.whiskeringLeft (Over (⊤ : Opens X))ᵒᵖ (Over X)ᵒᵖ S.Modules).obj
      (opensOverTop X).op

/-- The value of the coefficient presheaf is the direct image of the restriction. -/
theorem pushforwardPresheaf_obj_obj (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (A : Over (⊤ : Opens X)) :
    ((pushforwardPresheaf f).obj F).obj (op A)
      = (Scheme.Modules.pushforward (Scheme.Opens.ι (X := X) A.left ≫ f)).obj
          ((Scheme.Modules.pullback (Scheme.Opens.ι (X := X) A.left)).obj F.obj) :=
  rfl

/-! ### The complex -/

/-- **The complex of pushforwards along a hypercovering**, for a simplicial object `K` of formal
coproducts of opens of `X`:  the cochain complex of `K` with coefficients in
`pushforwardPresheaf f`, indexed by `ℤ` and bounded below by `0`.  Its degree `n` term is the
product over the index type of `K_n` of the modules `f_{i,*}𝓕|_{U_i}`, and its differential is the
alternating sum of the coface maps of `K`. -/
noncomputable def hypercoveringPushforwardComplex (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      CochainComplex.Plus S.Modules :=
  ObjectProperty.lift _
    (pushforwardPresheaf f ⋙ FormalCoproduct.cochainComplexFunctor K ⋙
      ComplexShape.embeddingUpNat.extendFunctor S.Modules)
    (fun F ↦ ⟨0, by
      change CochainComplex.IsStrictlyGE
        (((FormalCoproduct.cochainComplexFunctor K).obj
          ((pushforwardPresheaf f).obj F)).extend ComplexShape.embeddingUpNat) 0
      infer_instance⟩)

/-- The underlying `ℤ`-indexed complex is the extension, along `ComplexShape.embeddingUpNat`, of
the `ℕ`-indexed cochain complex of `K`. -/
theorem hypercoveringPushforwardComplex_obj_obj (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((hypercoveringPushforwardComplex f K).obj F).obj
      = ((FormalCoproduct.cochainComplexFunctor K).obj
          ((pushforwardPresheaf f).obj F)).extend ComplexShape.embeddingUpNat :=
  rfl

/-- **The degree `n` term of the `ℕ`-indexed complex is the product, over the index type of `K_n`,
of the values of the coefficient presheaf on the components of `K_n`.**  Together with
`pushforwardPresheaf_obj_obj` this is the term `∏_{i ∈ I_n} f_{i,*}𝓕|_{U_i}` of the complex of
[Stacks, Tag 01XN]. -/
theorem cochainComplexFunctor_obj_X (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (n : ℕ) :
    ((FormalCoproduct.cochainComplexFunctor K).obj ((pushforwardPresheaf f).obj F)).X n
      = ∏ᶜ (fun i : (K.obj (op ⦋n⦌)).I ↦
          ((pushforwardPresheaf f).obj F).obj (op ((K.obj (op ⦋n⦌)).obj i))) :=
  rfl

/-- **Every term of the `ℕ`-indexed complex is quasi-coherent**, when the index type of `K_n` is
finite and every component of `K_n` is an affine open of `X`:  the term is a finite product of
modules `f_{i,*}𝓕|_{U_i}`, each quasi-coherent because `𝓕|_{U_i}` is and because `f_i` is an
affine morphism, `U_i` being affine and `S` separated. -/
theorem isQuasicoherent_cochainComplex_X (f : X ⟶ S) [S.IsSeparated]
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) (n : ℕ)
    [Finite (K.obj (op ⦋n⦌)).I]
    (hK : ∀ i : (K.obj (op ⦋n⦌)).I, IsAffineOpen ((K.obj (op ⦋n⦌)).obj i).left)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (((FormalCoproduct.cochainComplexFunctor K).obj
        ((pushforwardPresheaf f).obj F)).X n).IsQuasicoherent := by
  have hdiag : IsAffineHom (Limits.pullback.diagonal (terminal.from S)) := inferInstance
  have key : (∏ᶜ (fun i : (K.obj (op ⦋n⦌)).I ↦
      ((relativeCechPresheaf f).obj F).obj
        (op ((opensOverTop X).obj ((K.obj (op ⦋n⦌)).obj i))))).IsQuasicoherent := by
    refine Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isQuasicoherent_pi _ (fun i ↦ ?_)
    have : IsAffine ((opensOverTop X).obj ((K.obj (op ⦋n⦌)).obj i)).left := hK i
    exact Stacks.AlgebraicGeometry.RelativeCechComplex.isQuasicoherent_presheaf_obj f _ F
  exact key

/-- **Every term of the complex of pushforwards along a hypercovering by affine opens is a
quasi-coherent `𝒪_S`-module.**  In nonnegative degrees this is the previous statement, and in
negative degrees the term is a zero module. -/
theorem hypercoveringPushforwardComplex_obj_isQuasicoherent (f : X ⟶ S) [S.IsSeparated]
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I ∧
      ∀ i : (K.obj (op ⦋n⦌)).I, IsAffineOpen ((K.obj (op ⦋n⦌)).obj i).left)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (p : ℤ) :
    (((hypercoveringPushforwardComplex f K).obj F).obj.X p).IsQuasicoherent := by
  rcases le_or_gt 0 p with hp | hp
  · lift p to ℕ using hp with n
    have := (hK n).1
    exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
        (i := n) (i' := (n : ℤ)) (by simp)).symm
      (isQuasicoherent_cochainComplex_X f K n (hK n).2 F)
  · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
      (R := S.ringCatSheaf)
      (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
        (fun i ↦ by simp only [ComplexShape.embeddingUpNat_f]; omega))

/-- **The inverse image of a bounded below complex with quasi-coherent terms has quasi-coherent
terms.**  This is [Stacks, Tag 01BG] read in each degree; it is what makes `g^*𝓚⁼` a complex of
quasi-coherent `𝒪_{S'}`-modules for every `g`. -/
theorem isQuasicoherent_pullback_X {S' : Scheme.{u}} (g : S' ⟶ S)
    (K : CochainComplex.Plus S.Modules) (hK : ∀ p : ℤ, (K.obj.X p).IsQuasicoherent) (p : ℤ) :
    ((((Scheme.Modules.pullback g).mapCochainComplexPlus.obj K).obj.X p)).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback g (K.obj.X p) (hK p)

/-- **The degree zero opens of a hypercovering cover `X`** ([Stacks, Tag 01H2]).  Together with
`hypercoveringPushforwardComplexXZeroIso` this says that the degree zero term of the complex is
the product of the direct images of `𝓕` over a genuine covering of `X` by affine opens. -/
theorem iSup_left_eq_top (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology X) K) :
    (⨆ i : (K.obj (op ⦋0⦌)).I, ((K.obj (op ⦋0⦌)).obj i).left) = ⊤ :=
  iSup_eq_top_of_isHypercovering K hK

/-- **The degree zero term of the complex is `∏_{i ∈ I₀} f_{i,*}𝓕|_{U_i}`.**  The `ℤ`-indexed
complex is the extension of the `ℕ`-indexed one, whose degree zero term is that product by
definition. -/
noncomputable def hypercoveringPushforwardComplexXZeroIso (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((hypercoveringPushforwardComplex f K).obj F).obj.X 0 ≅
      ∏ᶜ (fun i : (K.obj (op ⦋0⦌)).I ↦
        (Scheme.Modules.pushforward
            (Scheme.Opens.ι (X := X) ((K.obj (op ⦋0⦌)).obj i).left ≫ f)).obj
          ((Scheme.Modules.pullback
            (Scheme.Opens.ι (X := X) ((K.obj (op ⦋0⦌)).obj i).left)).obj F.obj)) :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
    (i := 0) (i' := (0 : ℤ)) (by simp)

/-! ### Restriction to an affine open of the base -/

/-- **An open of `Y` whose structure morphism to `T` is affine meets the inverse image of an
affine open `V` of `T` in an affine open.**  That intersection is the inverse image of `V` along
`U.ι ≫ a`, read as an open of `Y` through the open immersion `U.ι`. -/
theorem isAffineOpen_inf_preimage_of_isAffineHom {Y T : Scheme.{u}} (a : Y ⟶ T) (U : Y.Opens)
    [IsAffineHom (Scheme.Opens.ι (X := Y) U ≫ a)] {V : T.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ a ⁻¹ᵁ V) := by
  have h := hV.preimage (Scheme.Opens.ι (X := Y) U ≫ a)
  rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (Scheme.Opens.ι (X := Y) U)] at h
  rwa [show (Scheme.Opens.ι (X := Y) U ≫ a) ⁻¹ᵁ V = U.ι ⁻¹ᵁ (a ⁻¹ᵁ V) from rfl,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at h

/-- **Every member of a hypercovering whose restriction of `f` is affine meets `f^{-1}(V)` in an
affine open**, for every affine open `V` of `S`.  No affineness of the member itself is used:
affineness of `f_i` alone gives it. -/
theorem isAffineOpen_hypercovering_inf_preimage (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      IsAffineHom (Scheme.Opens.ι (X := X) ((K.obj (op ⦋n⦌)).obj i).left ≫ f))
    {V : S.Opens} (hV : IsAffineOpen V) (n : ℕ) (i : (K.obj (op ⦋n⦌)).I) :
    IsAffineOpen (((K.obj (op ⦋n⦌)).obj i).left ⊓ f ⁻¹ᵁ V) :=
  have := hK n i
  isAffineOpen_inf_preimage_of_isAffineHom f _ hV

/-- **The degree zero members of a hypercovering, intersected with `f^{-1}(V)`, cover
`f^{-1}(V)`.**  With the previous statement this exhibits the degree zero level of the
restriction of the hypercovering to `f^{-1}(V)` as a covering of `f^{-1}(V)` by affine opens. -/
theorem iSup_inf_preimage_eq_preimage (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology X) K) (V : S.Opens) :
    (⨆ i : (K.obj (op ⦋0⦌)).I, ((K.obj (op ⦋0⦌)).obj i).left ⊓ f ⁻¹ᵁ V) = f ⁻¹ᵁ V := by
  rw [← iSup_inf_eq, iSup_left_eq_top K hK, top_inf_eq]

/-! ### The statement of the tag -/

section Statement

attribute [local instance] HasDerivedCategory.standard

/-- **The cartesian square of [Stacks, Tag 02KF] determined by `f : X ⟶ S` and `g : S' ⟶ S`**,
with upper-left corner the fibre product `X ×_S S'` and with the quasi-coherent module `𝓕` on its
upper-right corner. -/
noncomputable def canonicalBaseChangeDiagram (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {S' : Scheme.{u}} (g : S' ⟶ S) : BaseChangeDiagram.{u} where
  X' := Limits.pullback f g
  X := X
  S' := S'
  S := S
  g' := Limits.pullback.fst f g
  f' := Limits.pullback.snd f g
  f := f
  g := g
  isPullback := IsPullback.of_hasPullback f g
  F := F.obj
  isQuasicoherent := F.property

/-- **A module placed in degree zero**, as a bounded below complex:  the complex with the given
`𝒪_T`-module in degree zero and zero objects in every other degree, together with the witness
`0` of the lower bound. -/
noncomputable def singleComplexPlus {T : Scheme.{u}} (M : T.Modules) :
    CochainComplex.Plus T.Modules :=
  ⟨(CochainComplex.singleFunctor T.Modules 0).obj M, 0, inferInstance⟩

/-- **Every term of `M[0]` is quasi-coherent when `M` is.**  The term in degree zero is `M`
itself, and every other term is a zero object, which is quasi-coherent. -/
theorem isQuasicoherent_singleComplexPlus_X {T : Scheme.{u}} (M : T.Modules)
    (hM : M.IsQuasicoherent) (p : ℤ) :
    ((singleComplexPlus M).obj.X p).IsQuasicoherent := by
  by_cases hp : p = 0
  · subst hp
    exact (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).symm hM
  · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
      (R := T.ringCatSheaf)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M p hp)

/-- **The conclusion of [Stacks, Tag 01XN]:** a bounded below complex `𝓚⁼` of `𝒪_S`-modules whose
terms are quasi-coherent and whose ordinary inverse image `g^*𝓚⁼` represents `Rf'_*𝓕'` in `D⁺(S')`
for every morphism `g : S' ⟶ S`, with the notation of the cartesian square of
[Stacks, Tag 02KF].  The isomorphisms are fields rather than the content of an existence
statement, so no choice is hidden in them. -/
structure UniversalPushforwardComplex (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) where
  /-- The bounded below complex `𝓚⁼` of `𝒪_S`-modules. -/
  complex : CochainComplex.Plus S.Modules
  /-- Every term of `𝓚⁼` is a quasi-coherent `𝒪_S`-module. -/
  isQuasicoherent : ∀ p : ℤ, (complex.obj.X p).IsQuasicoherent
  /-- For every `g : S' ⟶ S` the inverse image `g^*𝓚⁼` represents `Rf'_*𝓕'` in `D⁺(S')`. -/
  baseChangeIso : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
    DerivedCategory.Plus.Q.obj
        ((Scheme.Modules.pullback g).mapCochainComplexPlus.obj complex) ≅
      (canonicalBaseChangeDiagram f F g).derivedPushforward'

/-- **The base-change isomorphism of [Stacks, Tag 01XN] for an affine morphism.**  For `f`
affine, `𝓕` quasi-coherent and an arbitrary `g : S' ⟶ S`, the ordinary inverse image of the
complex `(f_*𝓕)[0]` represents `Rf'_*𝓕'` in `D⁺(S')`.

Three steps.  Inverse image commutes with placing a module in degree zero, so `g^*(f_*𝓕)[0]` is
`(g^*f_*𝓕)[0]`; the base-change morphism `g^*f_*𝓕 ⟶ f'_*𝓕'` is invertible because `f` is affine
and `𝓕` quasi-coherent ([Stacks, Tag 02KG]); and `(f'_*𝓕')[0] ≅ Rf'_*𝓕'` because `f'` is affine,
being a base change of `f`, so the quasi-coherent module `𝓕'` has no higher direct images along
it ([Stacks, Tag 01XC]).  Nothing is assumed about `S'`. -/
noncomputable def affineBaseChangeSingleIso (f : X ⟶ S) [IsAffineHom f]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {S' : Scheme.{u}} (g : S' ⟶ S) :
    DerivedCategory.Plus.Q.obj ((Scheme.Modules.pullback g).mapCochainComplexPlus.obj
        (singleComplexPlus ((Scheme.Modules.pushforward f).obj F.obj))) ≅
      (canonicalBaseChangeDiagram f F g).derivedPushforward' :=
  haveI : IsAffineHom (Limits.pullback.snd f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g)
      inferInstance
  haveI : ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F.obj).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback _ F.obj F.property
  haveI := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    (IsPullback.of_hasPullback f g) F.obj
  DerivedCategory.Plus.Q.mapIso
      ((CochainComplex.Plus.fullyFaithfulι S'.Modules).preimageIso
        (Y := singleComplexPlus
          ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F.obj)))
        ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pullback g)
          (ComplexShape.up ℤ) 0).app ((Scheme.Modules.pushforward f).obj F.obj))) ≪≫
    (DerivedCategory.Plus.singleFunctor S'.Modules 0).mapIso
      (asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
        (IsPullback.of_hasPullback f g).w).app F.obj)) ≪≫
    (Stacks.Cohomology.AffineComparison.rightDerivedFunctorPlusObjSingleIso
      (Scheme.Modules.pushforward (Limits.pullback.snd f g))
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F.obj)
      (Stacks.Cohomology.AffineComparison.rightAcyclic_pushforward_of_isAffineHom _ _)).symm

/-- **Stacks Project, Tag 01XN, for an affine morphism.**  Let `f : X ⟶ S` be an affine morphism
of schemes and `𝓕` a quasi-coherent `𝒪_X`-module.  Then `f_*𝓕` placed in degree zero is a bounded
below complex of quasi-coherent `𝒪_S`-modules whose ordinary inverse image along *every*
`g : S' ⟶ S` represents `Rf'_*𝓕'` in `D⁺(S')`, with the notation of the cartesian square of
[Stacks, Tag 02KF].

The three fields are discharged separately.  The complex is the single complex, so its terms are
`f_*𝓕` in degree zero — quasi-coherent because `f` is affine ([Stacks, Tag 01XD]) — and zero
objects elsewhere.  The base-change isomorphism for every `g` is `affineBaseChangeSingleIso`:
affineness is stable under base change, so no hypothesis on `S'` is needed and the universal
quantification over `g` is genuine. -/
@[stacks 01XN "for an affine morphism"]
noncomputable def universalPushforwardComplex (f : X ⟶ S) [IsAffineHom f]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    UniversalPushforwardComplex f F where
  complex := singleComplexPlus ((Scheme.Modules.pushforward f).obj F.obj)
  isQuasicoherent :=
    isQuasicoherent_singleComplexPlus_X _
      (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom f F.obj F.property)
  baseChangeIso g := affineBaseChangeSingleIso f F g

/-- The complex produced by `universalPushforwardComplex` is `f_*𝓕` placed in degree zero, so the
existence statement is witnessed by that complex and not by a zero object. -/
theorem universalPushforwardComplex_complex (f : X ⟶ S) [IsAffineHom f]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (universalPushforwardComplex f F).complex =
      singleComplexPlus ((Scheme.Modules.pushforward f).obj F.obj) :=
  rfl

/-- **A complex with the property of [Stacks, Tag 01XN] can pull back to zero only where
`Rf'_*𝓕'` vanishes.**  So the existence statement of the tag is not satisfied by a degenerate
witness:  a complex whose inverse image along `g` is a zero object of `D⁺(S')` forces the derived
direct image of that base change to be zero. -/
theorem isZero_derivedPushforward'_of_isZero (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (U : UniversalPushforwardComplex f F) {S' : Scheme.{u}} (g : S' ⟶ S)
    (h : IsZero (DerivedCategory.Plus.Q.obj
      ((Scheme.Modules.pullback g).mapCochainComplexPlus.obj U.complex))) :
    IsZero (canonicalBaseChangeDiagram f F g).derivedPushforward' :=
  IsZero.of_iso h (U.baseChangeIso g).symm

/-- **The degree zero term of the complex delivered by `universalPushforwardComplex` is `f_*𝓕`**,
so the witness of the existence statement of [Stacks, Tag 01XN] is not a zero object:  it carries
the direct image itself in degree zero. -/
noncomputable def universalPushforwardComplexXZeroIso (f : X ⟶ S) [IsAffineHom f]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (universalPushforwardComplex f F).complex.obj.X 0 ≅
      (Scheme.Modules.pushforward f).obj F.obj :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    ((Scheme.Modules.pushforward f).obj F.obj)

/-- **The degree zero members of the hypercovering of
`exists_finite_affine_hypercovering_isAffineHom` cover `X`** ([Stacks, Tag 01H2]), so the product
indexing the degree zero term of the hypercovering complex is taken over a genuine covering of
`X` by affine opens. -/
theorem iSup_left_choose_eq_top (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S] [S.IsSeparated] :
    (⨆ i : ((exists_finite_affine_hypercovering_isAffineHom f).choose.obj (op ⦋0⦌)).I,
      (((exists_finite_affine_hypercovering_isAffineHom f).choose.obj (op ⦋0⦌)).obj i).left)
      = ⊤ :=
  iSup_left_eq_top _ (exists_finite_affine_hypercovering_isAffineHom f).choose_spec.1

end Statement

end Stacks.AlgebraicGeometry.UniversalPushforward

end
