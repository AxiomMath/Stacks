module

public import StacksFrontier.Cotangent.SurjectivePresentationSequence

/-!
# Higher homology of the conormal sheaf (Stacks 09D5)

Let `A → B` be a ring map. Stacks 09D5 records, after the four term exact sequence of sheaves on
the full subcategory `C'_{B/A} ⊆ C_{B/A}` of *surjective* presentations `P → B`

```
0 ⟶ H₁(L_{B/A}) ⟶ 𝒥/𝒥² --d--> Ω ⟶ H₀(L_{B/A}) ⟶ 0,
```

two further assertions: that `Ker(d)` and `Coker(d)` have vanishing homology on `C_{B/A}` in
positive degrees, because they are constant; and that consequently

```
H_n(C_{B/A}, 𝒥/𝒥²) ⟶ H_n(L_{B/A})
```

is an isomorphism for every `n ≥ 2`. This file proves both.

The sequence itself, and the constancy of its outer terms, are
`StacksFrontier/Cotangent/SurjectivePresentationSequence.lean`; this file is built on that one.
Homology on `C_{B/A}` is read, through Tag 08PS, on the standard resolution `P_• ⟶ B` of
Tag 08PN: `08PS` says that the homology of a sheaf of modules on `C_{B/A}` is the homology of
the simplicial module it gives at a resolution, and the standard resolution is one by Tag 08PT.
Each of its terms `εₙ : Pₙ → B` is a *surjection* from a polynomial `A`-algebra — that is
`CommAlgCat.surjective_standardResolution_augmentation` together with
`CommAlgCat.standardResolution_obj_isPolynomialAlgebra` — hence an object of `C'_{B/A}`, so the
four term sequence and the constancy of its outer terms apply degreewise.

## Main definitions

* `Stacks.Cotangent.conormalExtension`: the term `εₙ : Pₙ → B` of the standard resolution read as
  an `Algebra.Extension A B`.
* `Stacks.Cotangent.conormalSimplicialModule`: the simplicial `B`-module `𝒥/𝒥²` of the standard
  resolution, `n ↦ (ker εₙ)/(ker εₙ)²`, and `Stacks.Cotangent.conormalToCotangent`, the morphism
  `d` from it to the cotangent simplicial module of Tag 08PN.
* `Stacks.Cotangent.conormalMooreComplex` and `Stacks.Cotangent.conormalToCotangentMoore`: the
  Moore complex computing `H_*(C_{B/A}, 𝒥/𝒥²)`, and `d` on Moore complexes.
* `Stacks.Cotangent.conormalComplex` and `Stacks.Cotangent.conormalToCotangentComplex`: the same
  two, reindexed into cohomological degrees `≤ 0` as `CommAlgCat.cotangentComplex` is.
* `Stacks.Cotangent.kernelConormalToCotangentMooreIso` and
  `Stacks.Cotangent.cokernelConormalToCotangentMooreIso`: `Ker(d)` is the constant complex on
  `Algebra.H1Cotangent A B` and `Coker(d)` is the constant complex on `Ω[B⁄A]`.

## Main results

* `Stacks.Cotangent.conormal_exact_app`: the sequence of Tag 09D5 holds at every term of the
  standard resolution; this is `Stacks.Cotangent.surjectivePresentation_exact` applied there.
* `Stacks.Cotangent.isZero_homology_kernel_conormalToCotangentMoore` and
  `Stacks.Cotangent.isZero_homology_cokernel_conormalToCotangentMoore`: **Stacks 09D5**,
  `Ker(d)` and `Coker(d)` have vanishing higher homology on `C_{B/A}`.
* `Stacks.Cotangent.isIso_homologyMap_conormalToCotangentComplex`: **Stacks 09D5**,
  `H_n(C_{B/A}, 𝒥/𝒥²) → H_n(L_{B/A})` is an isomorphism for `n ≥ 2`.
* `Stacks.Cotangent.isIso_homologyMap_of_isZero_homology_kernel_cokernel`: the homological
  input, in an arbitrary abelian category: a morphism of complexes whose kernel and cokernel are
  acyclic in the relevant degrees is an isomorphism on homology.

## Implementation notes

**The homological argument.** The source deduces the isomorphism in degrees `≥ 2` from the
vanishing of the higher homology of `Ker(d)` and `Coker(d)`. Written out, `d` factors as
`𝒥/𝒥² ↠ Coim(d) ≅ Im(d) ↪ Ω`; the two short exact sequences
`0 → Ker(d) → 𝒥/𝒥² → Coim(d) → 0` and `0 → Im(d) → Ω → Coker(d) → 0` give long exact sequences
in which, in degree `n`, the four neighbouring terms are `H_n(Ker d)`, `H_{n-1}(Ker d)`,
`H_n(Coker d)` and `H_{n+1}(Coker d)`. All four vanish as soon as `n ≥ 2`, so both outer maps
are isomorphisms in that degree, and the middle one is because the category is abelian. That is
`Stacks.Cotangent.isIso_homologyMap_of_isZero_homology_kernel_cokernel`, stated for an arbitrary
complex shape, with the three relevant degrees passed explicitly.

**Tag 08PS is used, not reproved.** The translation of `H_n(C_{B/A}, ℱ)` into the homology of
`ℱ(P_•, ε)` is the conclusion of Tag 08PS; in this library that conclusion is available only at
the small model of the footnote-restricted site
(`StacksFrontier/Cotangent/ResolutionPointCriterionSmallOfModules.lean`), and its hypothesis at the
standard resolution is `StacksFrontier/Cotangent/ResolutionPointCriterion.lean`. Nothing below
reproves it or depends on a declaration for it: every statement here is about the Moore complex
of the simplicial module on the standard resolution, which is the right-hand side of Tag 08PS.

**Which clauses of 09D5 this covers.** The remark has five assertions. The four term exact
sequence and the constancy of its outer terms are in
`StacksFrontier/Cotangent/SurjectivePresentationSequence.lean`; the two proved here are the
vanishing of the higher homology of `Ker(d)` and `Coker(d)` and the isomorphism in degrees
`≥ 2`. The remaining two — that the spectral sequence differential
`H₂(C_{B/A}, 𝒥/𝒥²) → H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` is an isomorphism, and the resulting formula
`H₂(L_{B/A}) = H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` — need the Tor sheaves and the spectral sequence of
Tag 08R7, of which only the augmentation and its ideal are in this library; see the
implementation notes of `StacksFrontier/Cotangent/PolynomialAlgebraSiteAugmentationIdeal.lean`.

**The left-hand term.** As in `StacksFrontier/Cotangent/SurjectivePresentationSequence.lean`, the
constant value of `Ker(d)` is `Algebra.H1Cotangent A B`, Mathlib's presentation-independent
`H¹` of the naive cotangent complex. Nothing below needs it identified with `H₁` of the
cotangent complex of Tag 08PN, since the vanishing of the higher homology of `Ker(d)` only uses
that `Ker(d)` is *constant*; that identification is
`Stacks.Cotangent.cotangentComplexHomologyNegOneIsoH1Cotangent` of
`StacksFrontier/Cotangent/CotangentComplexHomologyNegOne.lean`, which runs the argument of this
file in the one degree `Stacks.Cotangent.isIso_homologyMap_conormalToCotangentComplex` below
does not reach. It is less than Tag 08RB in degree `-1`, which asserts in addition that the
isomorphism is the one the comparison map of Tag 08R9 induces.

**Two spellings of the same module.** `Algebra.Extension.CotangentSpace` of
`Stacks.Cotangent.conormalExtension` and `CommAlgCat.cotangentTerm` are the same object of
`ModuleCat B` — `B ⊗[Pₙ] Ω[Pₙ⁄A]` — but reached through different instance paths, so the
identification is by definitional unfolding rather than by an isomorphism. It is performed once
and for all, in `Stacks.Cotangent.conormalToCotangentApp` and
`Stacks.Cotangent.cotangentTermToKaehler`, and everything after those two definitions is stated
in the library's own spelling. The two bridging computations are
`Stacks.Cotangent.conormalToCotangentApp_mk` (`d` sends the class of `x` to `1 ⊗ d x`) and
`Stacks.Cotangent.cotangentTermToKaehler_D` (the augmentation sends `1 ⊗ d p` to `d (εₙ p)`).

**The chosen section of an extension.** `Algebra.Extension` carries a set-theoretic section `σ`
of its surjection, which `Stacks.Cotangent.conormalExtension` takes from the surjectivity of the
augmentation; it is characterised by `Algebra.Extension.algebraMap_σ`, and neither
`Algebra.Extension.Cotangent` nor any map used below depends on which section is taken.

## References

* [Stacks Project, Tag 09D5](https://stacks.math.columbia.edu/tag/09D5)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08R7](https://stacks.math.columbia.edu/tag/08R7)
* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped TensorProduct ChangeOfRings

universe u v

namespace Stacks.Cotangent

open CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-- The augmentation of the standard resolution is surjective in every simplicial degree. -/
theorem surjective_standardResolutionAugmentationHom (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (standardResolutionAugmentationHom A B n) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = op ⦋m⦌ := ⟨n.unop.len, rfl⟩
  intro b
  obtain ⟨p, hp⟩ := surjective_standardResolution_augmentation A B m b
  exact ⟨p, by simpa [standardResolutionAugmentationHom] using hp⟩

/-- The term of the standard resolution in degree `n`, as an extension of `B` over `A`. -/
def conormalExtension (n : SimplexCategoryᵒᵖ) : Algebra.Extension.{max u v} A B where
  Ring := (standardResolution A B).left.obj n
  algebra₂ := (standardResolutionAugmentationHom A B n).toAlgebra
  isScalarTower :=
    letI : Algebra ((standardResolution A B).left.obj n : Type (max u v))
        (B : Type (max u v)) := (standardResolutionAugmentationHom A B n).toAlgebra
    IsScalarTower.of_algebraMap_eq (fun a =>
      (((standardResolution A B).hom.app n).hom.commutes a).symm)
  σ := fun b => (surjective_standardResolutionAugmentationHom A B n b).choose
  algebraMap_σ := fun b => (surjective_standardResolutionAugmentationHom A B n b).choose_spec

/-- Every term of the standard resolution is a polynomial algebra over `A`. -/
theorem isPolynomialAlgebra_conormalExtension_ring (n : SimplexCategoryᵒᵖ) :
    Algebra.IsPolynomialAlgebra A (conormalExtension A B n).Ring := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = op ⦋m⦌ := ⟨n.unop.len, rfl⟩
  exact standardResolution_obj_isPolynomialAlgebra A B _

/-- A simplicial operator, read as a morphism of extensions. -/
def conormalExtensionHom {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    (conormalExtension A B i).Hom (conormalExtension A B j) where
  toRingHom := ((standardResolution A B).left.map f).hom.toRingHom
  toRingHom_algebraMap a := ((standardResolution A B).left.map f).hom.commutes a
  algebraMap_toRingHom x :=
    RingHom.congr_fun (standardResolutionAugmentationHom_naturality A B f) x

/-- The degree `n` term `(ker εₙ)/(ker εₙ)²` of the conormal simplicial module. -/
abbrev conormalTerm (n : SimplexCategoryᵒᵖ) : ModuleCat.{max u v} B :=
  ModuleCat.of B (conormalExtension A B n).Cotangent

/-- The simplicial structure map of the conormal simplicial module. -/
def conormalMap {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    conormalTerm A B i ⟶ conormalTerm A B j :=
  ModuleCat.ofHom (Algebra.Extension.Cotangent.map (conormalExtensionHom A B f))

/-- `conormalExtensionHom` is functorial. -/
theorem conormalExtensionHom_comp {i j k : SimplexCategoryᵒᵖ} (f : i ⟶ j) (g : j ⟶ k) :
    conormalExtensionHom A B (f ≫ g) =
      (conormalExtensionHom A B g).comp (conormalExtensionHom A B f) := by
  apply Algebra.Extension.Hom.ext
  show ((standardResolution A B).left.map (f ≫ g)).hom.toRingHom = _
  rw [(standardResolution A B).left.map_comp]
  rfl

/-- `conormalExtensionHom` sends the identity to the identity. -/
theorem conormalExtensionHom_id (i : SimplexCategoryᵒᵖ) :
    conormalExtensionHom A B (𝟙 i) = Algebra.Extension.Hom.id (conormalExtension A B i) := by
  apply Algebra.Extension.Hom.ext
  show ((standardResolution A B).left.map (𝟙 i)).hom.toRingHom = _
  rw [(standardResolution A B).left.map_id]
  rfl

/-- The conormal simplicial `B`-module `n ↦ (ker εₙ)/(ker εₙ)²`, i.e. the sheaf `𝒥/𝒥²` of
Stacks 09D5 evaluated on the standard resolution. -/
def conormalSimplicialModule : SimplicialObject (ModuleCat.{max u v} B) where
  obj := conormalTerm A B
  map f := conormalMap A B f
  map_id i := by
    change ModuleCat.ofHom
      (Algebra.Extension.Cotangent.map (conormalExtensionHom A B (𝟙 i))) = 𝟙 _
    rw [conormalExtensionHom_id, Algebra.Extension.Cotangent.map_id]
    rfl
  map_comp f g := by
    change ModuleCat.ofHom (Algebra.Extension.Cotangent.map (conormalExtensionHom A B (f ≫ g))) =
      ModuleCat.ofHom (Algebra.Extension.Cotangent.map (conormalExtensionHom A B f)) ≫
        ModuleCat.ofHom (Algebra.Extension.Cotangent.map (conormalExtensionHom A B g))
    rw [conormalExtensionHom_comp, Algebra.Extension.Cotangent.map_comp]
    rfl

/-- The map `d : (ker εₙ)/(ker εₙ)² → Ω[Pₙ⁄A] ⊗[Pₙ] B` in simplicial degree `n`. -/
def conormalToCotangentApp (n : SimplexCategoryᵒᵖ) :
    conormalTerm A B n ⟶ cotangentTerm A B n := by
  change conormalTerm A B n ⟶ ModuleCat.of B ((conormalExtension A B n).CotangentSpace)
  exact ModuleCat.ofHom (conormalExtension A B n).cotangentComplex

/-- `d` sends the class of `x ∈ ker εₙ` to the pure differential `1 ⊗ d x`. -/
theorem conormalToCotangentApp_mk (n : SimplexCategoryᵒᵖ) (x : (conormalExtension A B n).ker) :
    conormalToCotangentApp A B n (Algebra.Extension.Cotangent.mk x) =
      cotangentTermDifferential A B n x.1 := rfl

/-- The right-hand map `Ω[Pₙ⁄A] ⊗[Pₙ] B → Ω[B⁄A]` of the sequence of Stacks 09D5 in simplicial
degree `n`. -/
def cotangentTermToKaehler (n : SimplexCategoryᵒᵖ) :
    cotangentTerm A B n ⟶ ModuleCat.of B (KaehlerDifferential A B) := by
  change ModuleCat.of B ((conormalExtension A B n).CotangentSpace) ⟶
    ModuleCat.of B (KaehlerDifferential A B)
  exact ModuleCat.ofHom (conormalExtension A B n).toKaehler

/-- For any extension `P → S`, the map `P.toKaehler` sends `1 ⊗ d q` to `d` of the image of
`q` in `S`. -/
theorem toKaehler_one_tmul_D {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) (q : P.Ring) :
    P.toKaehler ((1 : S) ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring q) =
      KaehlerDifferential.D R S (algebraMap P.Ring S q) := by
  rw [Algebra.Extension.toKaehler, KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.map_D]

/-- The right-hand map sends the pure differential `1 ⊗ d p` to `d (εₙ p)`. -/
theorem cotangentTermToKaehler_D (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution A B).left.obj n) :
    cotangentTermToKaehler A B n (cotangentTermDifferential A B n p) =
      KaehlerDifferential.D A B (standardResolutionAugmentationHom A B n p) :=
  toKaehler_one_tmul_D (conormalExtension A B n) p

/-! ### The constant outer terms -/

/-- The constant simplicial `B`-module on `H₁(L_{B/A})`, the left-hand term of the sequence of
Stacks 09D5. -/
abbrev h1ConstSimplicialModule : SimplicialObject (ModuleCat.{max u v} B) :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ModuleCat.of B (Algebra.H1Cotangent A B))

/-- The constant simplicial `B`-module on `Ω[B⁄A]`, the right-hand term of the sequence of
Stacks 09D5. -/
abbrev kaehlerConstSimplicialModule : SimplicialObject (ModuleCat.{max u v} B) :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ModuleCat.of B (KaehlerDifferential A B))

/-- The left-hand map `H₁(L_{B/A}) ⟶ 𝒥/𝒥²` as a morphism from a *constant* simplicial module:
its naturality is the first clause of `Stacks.Cotangent.outerTerms_constant`. -/
def h1ToConormal : h1ConstSimplicialModule A B ⟶ conormalSimplicialModule A B where
  app n := ModuleCat.ofHom (h1CotangentIncl (conormalExtension A B n))
  naturality i j f := by
    change 𝟙 _ ≫ ModuleCat.ofHom (h1CotangentIncl (conormalExtension A B j)) =
      ModuleCat.ofHom (h1CotangentIncl (conormalExtension A B i)) ≫ conormalMap A B f
    rw [Category.id_comp]
    refine ModuleCat.hom_ext ?_
    exact (outerTerms_constant (conormalExtensionHom A B f)).1.symm

/-- The right-hand map `Ω ⟶ Ω[B⁄A]` as a morphism to a *constant* simplicial module: this is
the second clause of `Stacks.Cotangent.outerTerms_constant`, read on the standard resolution. -/
def cotangentToKaehlerConst :
    (cotangentSimplicialModule A B).object ⟶ kaehlerConstSimplicialModule A B where
  app n := cotangentTermToKaehler A B n
  naturality i j f := by
    change cotangentMap A B f ≫ cotangentTermToKaehler A B j =
      cotangentTermToKaehler A B i ≫ 𝟙 _
    rw [Category.comp_id]
    refine cotangentTerm_hom_ext A B i _ _ fun p => ?_
    rw [ModuleCat.comp_apply, cotangentMap_D, cotangentTermToKaehler_D, cotangentTermToKaehler_D]
    exact congrArg _ (RingHom.congr_fun (standardResolutionAugmentationHom_naturality A B f) p)

/-- The morphism `d` of simplicial `B`-modules from `𝒥/𝒥²` to `Ω`, on the standard
resolution. -/
def conormalToCotangent :
    conormalSimplicialModule A B ⟶ (cotangentSimplicialModule A B).object where
  app n := conormalToCotangentApp A B n
  naturality i j f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    change (conormalMap A B f ≫ conormalToCotangentApp A B j) _ =
      (conormalToCotangentApp A B i ≫ cotangentMap A B f) _
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    change conormalToCotangentApp A B j (Algebra.Extension.Cotangent.map
        (conormalExtensionHom A B f) (Algebra.Extension.Cotangent.mk y)) = _
    rw [Algebra.Extension.Cotangent.map_mk, conormalToCotangentApp_mk,
      conormalToCotangentApp_mk]
    exact (cotangentMap_D A B f y.1).symm

/-! ### The four-term exact sequence, read degreewise on the standard resolution -/

/-- **The sequence of Stacks 09D5 at the degree `n` term of the standard resolution.** Every
term of the standard resolution is a surjection from a polynomial algebra, hence an object of
`C'_{B/A}`, so `Stacks.Cotangent.surjectivePresentation_exact` applies to it. -/
theorem conormal_exact_app (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((h1ToConormal A B).app n).hom ∧
      Function.Exact ((h1ToConormal A B).app n).hom ((conormalToCotangent A B).app n).hom ∧
        Function.Exact ((conormalToCotangent A B).app n).hom
            ((cotangentToKaehlerConst A B).app n).hom ∧
          Function.Surjective ((cotangentToKaehlerConst A B).app n).hom :=
  surjectivePresentation_exact (conormalExtension A B n)
    (isPolynomialAlgebra_conormalExtension_ring A B n)

/-! ### The Moore complexes -/

/-- The Moore complex of the conormal simplicial module: by Tag 08PS this computes
`H_*(C_{B/A}, 𝒥/𝒥²)`. -/
abbrev conormalMooreComplex : ChainComplex (ModuleCat.{max u v} B) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
    (conormalSimplicialModule A B)

/-- The Moore complex of the constant simplicial module on `H₁(L_{B/A})`. -/
abbrev h1ConstMooreComplex : ChainComplex (ModuleCat.{max u v} B) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
    (h1ConstSimplicialModule A B)

/-- The Moore complex of the constant simplicial module on `Ω[B⁄A]`. -/
abbrev kaehlerConstMooreComplex : ChainComplex (ModuleCat.{max u v} B) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
    (kaehlerConstSimplicialModule A B)

/-- `d` on Moore complexes: the map `H_*(C_{B/A}, 𝒥/𝒥²) → H_*(L_{B/A})` of Stacks 09D5 is the
map it induces on homology. -/
def conormalToCotangentMoore : conormalMooreComplex A B ⟶ cotangentMooreComplex A B :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).map
    (conormalToCotangent A B)

/-- The left-hand map on Moore complexes. -/
def h1ToConormalMoore : h1ConstMooreComplex A B ⟶ conormalMooreComplex A B :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).map (h1ToConormal A B)

/-- The right-hand map on Moore complexes. -/
def cotangentToKaehlerMoore : cotangentMooreComplex A B ⟶ kaehlerConstMooreComplex A B :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).map
    (cotangentToKaehlerConst A B)

/-- The composite `H₁(L_{B/A}) ⟶ 𝒥/𝒥² ⟶ Ω` of simplicial modules is zero. -/
theorem h1ToConormal_comp_conormalToCotangent :
    h1ToConormal A B ≫ conormalToCotangent A B = 0 := by
  apply NatTrans.ext
  funext n
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact (conormal_exact_app A B n).2.1.apply_apply_eq_zero x

/-- The composite `𝒥/𝒥² ⟶ Ω ⟶ Ω[B⁄A]` of simplicial modules is zero. -/
theorem conormalToCotangent_comp_cotangentToKaehlerConst :
    conormalToCotangent A B ≫ cotangentToKaehlerConst A B = 0 := by
  apply NatTrans.ext
  funext n
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact (conormal_exact_app A B n).2.2.1.apply_apply_eq_zero x

/-- The Moore complex functor sends a zero composite of simplicial modules to a zero composite. -/
private theorem alternatingFaceMapComplex_map_comp_eq_zero
    {X Y Z : SimplicialObject (ModuleCat.{max u v} B)} {f : X ⟶ Y} {g : Y ⟶ Z} (h : f ≫ g = 0) :
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).map f ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).map g = 0 := by
  rw [← Functor.map_comp, h, Functor.map_zero]

/-- The composite `H₁(L_{B/A}) ⟶ 𝒥/𝒥² ⟶ Ω` of Moore complexes is zero. -/
theorem h1ToConormalMoore_comp_conormalToCotangentMoore :
    h1ToConormalMoore A B ≫ conormalToCotangentMoore A B = 0 :=
  alternatingFaceMapComplex_map_comp_eq_zero A B (h1ToConormal_comp_conormalToCotangent A B)

/-- The composite `𝒥/𝒥² ⟶ Ω ⟶ Ω[B⁄A]` of Moore complexes is zero. -/
theorem conormalToCotangentMoore_comp_cotangentToKaehlerMoore :
    conormalToCotangentMoore A B ≫ cotangentToKaehlerMoore A B = 0 :=
  alternatingFaceMapComplex_map_comp_eq_zero A B
    (conormalToCotangent_comp_cotangentToKaehlerConst A B)

/-- The left-hand map on Moore complexes is a monomorphism. -/
theorem mono_h1ToConormalMoore : Mono (h1ToConormalMoore A B) :=
  HomologicalComplex.mono_of_mono_f _ fun n =>
    (ModuleCat.mono_iff_injective _).mpr (conormal_exact_app A B (op ⦋n⦌)).1

/-- The right-hand map on Moore complexes is an epimorphism. -/
theorem epi_cotangentToKaehlerMoore : Epi (cotangentToKaehlerMoore A B) :=
  HomologicalComplex.epi_of_epi_f _ fun n =>
    (ModuleCat.epi_iff_surjective _).mpr (conormal_exact_app A B (op ⦋n⦌)).2.2.2

/-- The sequence `H₁(L_{B/A}) ⟶ 𝒥/𝒥² ⟶ Ω` of Moore complexes is exact. -/
theorem h1ConormalShortComplex_exact :
    (ShortComplex.mk (h1ToConormalMoore A B) (conormalToCotangentMoore A B)
      (h1ToConormalMoore_comp_conormalToCotangentMoore A B)).Exact :=
  HomologicalComplex.exact_of_degreewise_exact _ fun n =>
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      (LinearMap.exact_iff.mp (conormal_exact_app A B (op ⦋n⦌)).2.1).symm

/-- The sequence `𝒥/𝒥² ⟶ Ω ⟶ Ω[B⁄A]` of Moore complexes is exact. -/
theorem conormalKaehlerShortComplex_exact :
    (ShortComplex.mk (conormalToCotangentMoore A B) (cotangentToKaehlerMoore A B)
      (conormalToCotangentMoore_comp_cotangentToKaehlerMoore A B)).Exact :=
  HomologicalComplex.exact_of_degreewise_exact _ fun n =>
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      (LinearMap.exact_iff.mp (conormal_exact_app A B (op ⦋n⦌)).2.2.1).symm

/-! ### `Ker(d)` and `Coker(d)` are the constant complexes, hence have no higher homology -/

/-- **`Ker(d)` is the constant sheaf `H₁(L_{B/A})`.** On the standard resolution the kernel of
`d : 𝒥/𝒥² ⟶ Ω` is the Moore complex of the constant simplicial module on
`Algebra.H1Cotangent A B`. -/
def kernelConormalToCotangentMooreIso :
    kernel (conormalToCotangentMoore A B) ≅ h1ConstMooreComplex A B :=
  haveI := mono_h1ToConormalMoore A B
  IsLimit.conePointUniqueUpToIso (kernelIsKernel (conormalToCotangentMoore A B))
    (h1ConormalShortComplex_exact A B).fIsKernel

/-- **`Coker(d)` is the constant sheaf `Ω[B⁄A]`.** On the standard resolution the cokernel of
`d : 𝒥/𝒥² ⟶ Ω` is the Moore complex of the constant simplicial module on `Ω[B⁄A]`. -/
def cokernelConormalToCotangentMooreIso :
    cokernel (conormalToCotangentMoore A B) ≅ kaehlerConstMooreComplex A B :=
  haveI := epi_cotangentToKaehlerMoore A B
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (conormalToCotangentMoore A B))
    (conormalKaehlerShortComplex_exact A B).gIsCokernel

/-- **Stacks 92.4.1**: the Moore complex of a constant simplicial module has no homology in
positive degrees. -/
theorem isZero_homology_alternatingFaceMapComplex_const (M : ModuleCat.{max u v} B) (n : ℕ)
    (hn : 0 < n) :
    IsZero (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
      ((Functor.const SimplexCategoryᵒᵖ).obj M)).homology n) := by
  have e : (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
      ((Functor.const SimplexCategoryᵒᵖ).obj M) ≅ ChainComplex.alternatingConst.obj M :=
    AlgebraicTopology.alternatingFaceMapComplexConst.app M
  have h : IsZero ((ChainComplex.alternatingConst.obj M).homology n) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (ChainComplex.alternatingConst_exactAt M n (by lia))
  exact IsZero.of_iso h
    ((HomologicalComplex.homologyFunctor (ModuleCat.{max u v} B) (ComplexShape.down ℕ) n).mapIso e)

/-- A complex isomorphic to the Moore complex of a constant simplicial module has no homology in
positive degrees. -/
private theorem isZero_homology_of_iso_alternatingFaceMapComplex_const
    {K : ChainComplex (ModuleCat.{max u v} B) ℕ} (M : ModuleCat.{max u v} B) (n : ℕ) (hn : 0 < n)
    (e : K ≅ (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
      ((Functor.const SimplexCategoryᵒᵖ).obj M)) :
    IsZero (K.homology n) :=
  IsZero.of_iso (isZero_homology_alternatingFaceMapComplex_const A B M n hn)
    ((HomologicalComplex.homologyFunctor (ModuleCat.{max u v} B) (ComplexShape.down ℕ) n).mapIso
      e)

/-! ### A homological criterion -/

section Homological

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

/-- In a short exact sequence of complexes whose first term has vanishing homology in the
degrees `i` and `j`, with `c.Rel i j`, the second map induces an isomorphism on homology in
degree `i`. -/
theorem isIso_homologyMap_g_of_isZero {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (S.X₁.homology i)) (h₂ : IsZero (S.X₁.homology j)) :
    IsIso (HomologicalComplex.homologyMap S.g i) := by
  have : Mono (HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₂ i).mono_g (h₁.eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₃ i j hij).epi_f (h₂.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- In a short exact sequence of complexes whose third term has vanishing homology in the
degrees `i` and `k`, with `c.Rel k i`, the first map induces an isomorphism on homology in
degree `i`. -/
theorem isIso_homologyMap_f_of_isZero {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i k : ι) (hki : c.Rel k i)
    (h₁ : IsZero (S.X₃.homology i)) (h₂ : IsZero (S.X₃.homology k)) :
    IsIso (HomologicalComplex.homologyMap S.f i) := by
  have : Mono (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₁ k i hki).mono_g (h₂.eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₂ i).epi_f (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- **A morphism of complexes with acyclic kernel and cokernel is a homology isomorphism.** If
`Ker(φ)` has vanishing homology in the degrees `i` and `j` and `Coker(φ)` has vanishing homology
in the degrees `i` and `k`, with `c.Rel i j` and `c.Rel k i`, then `φ` induces an isomorphism on
homology in degree `i`.

The proof is the factorisation of `φ` through its coimage and image: the projection onto the
coimage is the third map of the short exact sequence `0 → Ker(φ) → X → Coim(φ) → 0` and the
inclusion of the image is the first map of `0 → Im(φ) → Y → Coker(φ) → 0`, so each is a homology
isomorphism in degree `i` by the two lemmas above, and the coimage-image comparison is an
isomorphism because the category is abelian. -/
theorem isIso_homologyMap_of_isZero_homology_kernel_cokernel
    {X Y : HomologicalComplex C c} (φ : X ⟶ Y) (i j k : ι) (hij : c.Rel i j) (hki : c.Rel k i)
    (hKi : IsZero ((kernel φ).homology i)) (hKj : IsZero ((kernel φ).homology j))
    (hQi : IsZero ((cokernel φ).homology i)) (hQk : IsZero ((cokernel φ).homology k)) :
    IsIso (HomologicalComplex.homologyMap φ i) := by
  have hS₁ : (ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_cokernel (kernel.ι φ) }
  have hS₂ : (ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_kernel (cokernel.π φ) }
  have h₁ : IsIso (HomologicalComplex.homologyMap (Abelian.coimage.π φ) i) :=
    isIso_homologyMap_g_of_isZero hS₁ i j hij hKi hKj
  have h₂ : IsIso (HomologicalComplex.homologyMap (Abelian.image.ι φ) i) :=
    isIso_homologyMap_f_of_isZero hS₂ i k hki hQi hQk
  have h₃ : IsIso (HomologicalComplex.homologyMap (Abelian.coimageImageComparison φ) i) :=
    inferInstanceAs (IsIso ((HomologicalComplex.homologyFunctor _ c i).map
      (Abelian.coimageImageComparison φ)))
  rw [← Abelian.coimage_image_factorisation φ, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  infer_instance

end Homological

/-! ### Assertions (3) and (4) of Stacks 09D5 -/

/-- **Stacks 09D5**, the kernel of `d` has no higher homology on `C_{B/A}`. By Tag 08PS the
homology of a sheaf on `C_{B/A}` is the homology of the simplicial module it gives on the
standard resolution, and `Ker(d)` is there the *constant* simplicial module on
`Algebra.H1Cotangent A B` (`Stacks.Cotangent.kernelConormalToCotangentMooreIso`, which is the
constancy of `Stacks.Cotangent.outerTerms_constant` combined with the exactness of
`Stacks.Cotangent.surjectivePresentation_exact`); the Moore complex of a constant simplicial
module has no homology in positive degrees. -/
@[stacks 09D5 "Ker(d) has vanishing higher homology on C_{B/A}"]
theorem isZero_homology_kernel_conormalToCotangentMoore (n : ℕ) (hn : 0 < n) :
    IsZero ((kernel (conormalToCotangentMoore A B)).homology n) :=
  isZero_homology_of_iso_alternatingFaceMapComplex_const A B
    (ModuleCat.of B (Algebra.H1Cotangent A B)) n hn (kernelConormalToCotangentMooreIso A B)

/-- **Stacks 09D5**, the cokernel of `d` has no higher homology on `C_{B/A}`: on the standard
resolution `Coker(d)` is the *constant* simplicial module on `Ω[B⁄A]`
(`Stacks.Cotangent.cokernelConormalToCotangentMooreIso`), and the Moore complex of a constant
simplicial module has no homology in positive degrees. -/
@[stacks 09D5 "Coker(d) has vanishing higher homology on C_{B/A}"]
theorem isZero_homology_cokernel_conormalToCotangentMoore (n : ℕ) (hn : 0 < n) :
    IsZero ((cokernel (conormalToCotangentMoore A B)).homology n) :=
  isZero_homology_of_iso_alternatingFaceMapComplex_const A B
    (ModuleCat.of B (KaehlerDifferential A B)) n hn (cokernelConormalToCotangentMooreIso A B)

/-- **Stacks 09D5**, the map `H_n(C_{B/A}, 𝒥/𝒥²) → H_n(L_{B/A})` is an isomorphism for every
`n ≥ 2`. Both sides are computed on the standard resolution — the source by Tag 08PS, the target
by definition (Tag 08PN) — and the map is the one induced by `d`. It is an isomorphism because
`Ker(d)` and `Coker(d)` have no homology in positive degrees, which bounds the two connecting
maps away in all degrees `≥ 2`. -/
theorem isIso_homologyMap_conormalToCotangentMoore (n : ℕ) (hn : 2 ≤ n) :
    IsIso (HomologicalComplex.homologyMap (conormalToCotangentMoore A B) n) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by lia⟩
  refine isIso_homologyMap_of_isZero_homology_kernel_cokernel _ (m + 2) (m + 1) (m + 3) rfl rfl
    (isZero_homology_kernel_conormalToCotangentMoore A B _ (by lia))
    (isZero_homology_kernel_conormalToCotangentMoore A B _ (by lia))
    (isZero_homology_cokernel_conormalToCotangentMoore A B _ (by lia))
    (isZero_homology_cokernel_conormalToCotangentMoore A B _ (by lia))

/-- The conormal complex: the Moore complex of `𝒥/𝒥²` on the standard resolution, reindexed
into cohomological degrees `≤ 0` exactly as `CommAlgCat.cotangentComplex` is. -/
def conormalComplex : CochainComplex (ModuleCat.{max u v} B) ℤ :=
  (conormalMooreComplex A B).extend (ComplexShape.embeddingUpIntLE 0)

/-- `d`, read as a morphism from the conormal complex to the cotangent complex `L_{B/A}` of
Tag 08PN. -/
def conormalToCotangentComplex : conormalComplex A B ⟶ cotangentComplex A B :=
  HomologicalComplex.extendMap (conormalToCotangentMoore A B) (ComplexShape.embeddingUpIntLE 0)

/-- **Stacks 09D5**, the map `H_n(C_{B/A}, 𝒥/𝒥²) → H_n(L_{B/A})` is an isomorphism for every
`n ≥ 2`, stated at the cotangent complex `CommAlgCat.cotangentComplex` of Tag 08PN, whose
homology in cohomological degree `-n` is `H_n(L_{B/A})`. This is
`Stacks.Cotangent.isIso_homologyMap_conormalToCotangentMoore` transported along the reindexing,
which changes no homology. -/
@[stacks 09D5 "H_n(C_{B/A}, 𝒥/𝒥²) → H_n(L_{B/A}) is an isomorphism for n ≥ 2, at the \
  cotangent complex of Tag 08PN"]
theorem isIso_homologyMap_conormalToCotangentComplex (n : ℕ) (hn : 2 ≤ n) :
    IsIso (HomologicalComplex.homologyMap (conormalToCotangentComplex A B) (-(n : ℤ))) := by
  have hj' : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  have h : QuasiIsoAt (conormalToCotangentMoore A B) n :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mpr
      (isIso_homologyMap_conormalToCotangentMoore A B n hn)
  have h2 : QuasiIsoAt (HomologicalComplex.extendMap (conormalToCotangentMoore A B)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))) (-(n : ℤ)) :=
    (HomologicalComplex.quasiIsoAt_extendMap_iff _ _ hj').mpr h
  exact (quasiIsoAt_iff_isIso_homologyMap _ (-(n : ℤ))).mp h2

end Stacks.Cotangent

end
