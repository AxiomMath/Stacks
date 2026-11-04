module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.HodgeToDeRham
public import StacksFrontier.AlgebraicGeometry.DeRham.HypercohomologyBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UnderlyingAbelianSheafRightDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.StupidTruncationSpectralSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hodge-to-de Rham spectral sequence of the brutal filtration

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a topological space, with
`𝒪_X` the structure sheaf of a ringed space `X`, and let `Ω^•_{𝒪_X/A}` be the relative de Rham
complex. Stacks Section 50.7 reads the brutal truncations `σ^{≥p}Ω^•_{𝒪_X/A}` as a decreasing
filtration of `Ω^•_{𝒪_X/A}` by subcomplexes, identifies its graded pieces, and asserts that the
spectral sequence of that filtered complex of sheaves ([Stacks, Tag 0BKK]) is the Hodge-to-de
Rham spectral sequence of Section 50.6, the one built from the brutal filtration by
[Stacks, Tag 0FLK]. This file proves those three assertions for the de Rham complex.

The de Rham complex, extended by zero to negative degrees, is concentrated in degrees `≥ 0`, so
[Stacks, Tag 0BKL] — the bounded-below form of Tag 0BKK, which needs no filtered K-injective
resolution — applies to its brutal filtration. Feeding it the derived global-sections functor
`AlgebraicGeometry.SheafOfModules.derivedSectionsBase` used by
`AlgebraicGeometry.SheafOfModules.deRhamCohomology` produces one spectral sequence that carries
both descriptions at once: it is by construction the Tag 0BKK sequence of the brutal filtration,
and it is packaged as the Tag 0FLK brutal-truncation spectral sequence, whose `e₁Iso` field is
`E_1^{p, q} = H^q(X, Ω^p_{𝒪_X/A})`. It is bounded and it converges to `H^n_{dR}(X/A)`; the
filtration it converges along is the image of the hypercohomology of the brutal truncations, that
is the Hodge filtration `AlgebraicGeometry.SheafOfModules.hodgeFiltration` of
[Stacks, Tag 0FM8], and that identification is the last conjunct of
`AlgebraicGeometry.SheafOfModules.exists_hodgeToDeRhamSpectralSequence`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamStupidSubcomplex`: the brutal truncation
  `σ^{≥p}Ω^•_{𝒪_X/A}` as a subobject of the de Rham complex in the category of cochain
  complexes of sheaves of `A`-modules.
* `AlgebraicGeometry.SheafOfModules.deRhamStupidGradedPieceIso` and
  `AlgebraicGeometry.SheafOfModules.deRhamStupidGradedPieceDerivedIso`: the `p`-th graded piece
  of the brutal filtration, as the single complex on the `p`-th term of the de Rham complex and
  as `Ω^p_{𝒪_X/A}[-p]` in the derived category.
* `AlgebraicGeometry.SheafOfModules.deRhamComplexIntXIso`: the term of the de Rham complex in a
  nonnegative degree `p` is the sheaf `Ω^p_{𝒪_X/A}` of relative `p`-forms.

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamStupidSubcomplex_antitone` and
  `AlgebraicGeometry.SheafOfModules.deRhamStupidSubcomplex_zero`: the brutal truncations are a
  decreasing filtration of the de Rham complex by subcomplexes, starting at the de Rham complex
  itself: `Ω^• = σ^{≥0}Ω^• ⊃ σ^{≥1}Ω^• ⊃ σ^{≥2}Ω^• ⊃ ⋯`.
* `AlgebraicGeometry.SheafOfModules.hodgeFiltration_eq_imageSubobject` and
  `AlgebraicGeometry.SheafOfModules.hodgeFiltration_antitone`: the Hodge filtration is the image
  of the hypercohomology of the brutal truncations, and it is decreasing.
* `AlgebraicGeometry.SheafOfModules.hodgeToDeRhamFirstPageXIso`: the first-page term
  `E_1^{p, q}`, with its `A(X)`-module structure forgotten, is the term in position `p` of
  `AlgebraicGeometry.SheafOfModules.hodgeToDeRhamFirstPage`, the first page of Section 0FM6 as
  built in the abelian-sheaf realization.
* `AlgebraicGeometry.SheafOfModules.exists_hodgeToDeRhamSpectralSequence`: **the
  Hodge-to-de Rham spectral sequence** of the brutal filtration of the de Rham complex —
  bounded, abutting to `H^*_{dR}(X/A)`, with first page the Hodge cohomology groups of Section
  0FM6 and limiting filtration the Hodge filtration.

## Implementation notes

The spectral sequence is obtained from [Stacks, Tag 0BKL]
(`Stacks.Cohomology.FilteredComplex.exists_spectralSequence_of_boundedBelowFilteredComplex`)
rather than from its brutal-truncation specialisation
`Stacks.Cohomology.FilteredComplex.exists_boundedBelowStupidTruncationSpectralSequence`, because
the latter chooses its own derived global-sections functor existentially and the conclusion here
has to be about the one `AlgebraicGeometry.SheafOfModules.deRhamCohomology` and
`AlgebraicGeometry.SheafOfModules.hodgeFiltration` are taken with, namely
`AlgebraicGeometry.SheafOfModules.derivedSectionsBase`. With that functor fixed, the filtration
Tag 0BKL produces on the abutment is *equal* to the Hodge filtration, not merely isomorphic to
it: both are `imageSubobject` of the map on hypercohomology induced by the inclusion of the
brutal truncation, and `AlgebraicGeometry.SheafOfModules.hodgeFiltration_eq_imageSubobject`
records that this holds by definition. The Tag 0FLK package is then assembled from the same
replacement, so its first-page descriptions apply to the very same spectral sequence.

The identification `structureSheafRing (baseRingedSpace A) = underlyingRingSheaf A` holds by
definition, which is what lets the Tag 0BKL machinery — stated for sheaves of modules over the
structure sheaf of a ringed space — be applied to the complex of sheaves of `A`-modules. Each
occurrence of `deRhamComplexInt` inside a statement about `baseRingedSpace A` pins the ringed
space with `(X := X)`: without it the elaborator solves the ringed-space metavariable from
`baseRingedSpace A` instead of from `B`, and the de Rham data no longer typecheck.

The first page is identified with the one of Section 50.6 across the two realizations of de Rham
cohomology. `AlgebraicGeometry.SheafOfModules.hodgeToDeRhamFirstPage` is a complex of abelian
groups formed with `CategoryTheory.Functor.rightDerived` of sections of abelian sheaves, whereas
the first page of the package built here consists of modules over `A(X)` formed with the
unbounded derived global-sections functor of sheaves of `A`-modules. The bridge is
`Stacks.Cohomology.UnderlyingAbelianSheaf.homologyDerivedSectionsSingleIsoRightDerivedAbelian`,
which runs through [Stacks, Tag 0D5Y] to forget the module structure and through
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` to pass from the unbounded
derived category to the classical right derived functor. Applied to the `p`-th term of the de
Rham complex it gives `AlgebraicGeometry.SheafOfModules.hodgeToDeRhamFirstPageXIso`, which is
the fourth conjunct of
`AlgebraicGeometry.SheafOfModules.exists_hodgeToDeRhamSpectralSequence`. The identification is of
the terms of the two first pages; their differentials `d_1` are not compared.

## References

* [Stacks Project, Section 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
* [Stacks Project, Tag 0FM8](https://stacks.math.columbia.edu/tag/0FM8)
* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
* [Stacks Project, Tag 0BKK](https://stacks.math.columbia.edu/tag/0BKK)
* [Stacks Project, Tag 0BKL](https://stacks.math.columbia.edu/tag/0BKL)
* [Stacks Project, Tag 0FLK](https://stacks.math.columbia.edu/tag/0FLK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray (derivedSectionsOverOpen derivedSectionsOverOpenUnit)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (homotopySections)
open HomologicalComplex StacksDraft.StupidTruncation
open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.Cohomology.OpenSubspace (sectionsOnOpen)

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] StacksDraft.StupidTruncation.mono_ιStupidTrunc

variable {X : RingedSpace.{u, u}}
variable {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The brutal filtration of the de Rham complex -/

/-- The `p`-th brutal truncation `σ^{≥p}Ω^•_{𝒪_X/A}` as a **subcomplex** of the relative de Rham
complex: its canonical inclusion is a monomorphism, so it names a subobject of `Ω^•_{𝒪_X/A}` in
the category of cochain complexes of sheaves of `A`-modules. -/
def deRhamStupidSubcomplex (p : ℤ) : Subobject (deRhamComplexInt B D) :=
  Subobject.mk (ιStupidTrunc (deRhamComplexInt B D) (embeddingUpIntGE p))

/-- The brutal truncations form a **decreasing** chain of subcomplexes of the de Rham complex:
`σ^{≥1}Ω^• ⊃ σ^{≥2}Ω^• ⊃ ⋯`, because for `p ≤ q` the inclusion of `σ^{≥q}Ω^•` factors through
`σ^{≥p}Ω^•`. -/
@[stacks 0FM7 "the brutal truncations are subcomplexes of the relative de Rham complex and form
a decreasing filtration of it, the chain Ω^• = σ^{≥0}Ω^• ⊃ σ^{≥1}Ω^• ⊃ σ^{≥2}Ω^• ⊃ ⋯; this is
the decreasing half, that σ^{≥q}Ω^• ⊆ σ^{≥p}Ω^• for p ≤ q"]
theorem deRhamStupidSubcomplex_antitone : Antitone (deRhamStupidSubcomplex B D) := by
  intro p q h
  exact Subobject.mk_le_mk_of_comm (stupidTruncGEMapLE (deRhamComplexInt B D) h)
    (stupidTruncGEMapLE_ι (deRhamComplexInt B D) h)

/-- The inclusion of the brutal truncation `σ^{≥a}K^• ⟶ K^•` is an isomorphism when `K^•` is
concentrated in degrees `≥ a`: in a degree `n ≥ a` it is the identification of the retained
terms, and in a degree `n < a` both sides vanish. -/
theorem isIso_ιStupidTrunc_of_isStrictlyGE {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    IsIso (ιStupidTrunc K (embeddingUpIntGE a)) := by
  have (n : ℤ) : IsIso ((ιStupidTrunc K (embeddingUpIntGE a)).f n) := by
    by_cases hn : a ≤ n
    · rw [ιStupidTruncGE_f K a n hn]
      infer_instance
    · exact IsZero.isIso
        (CochainComplex.isZero_of_isStrictlyGE (K.stupidTrunc (embeddingUpIntGE a)) a n (by omega))
        (CochainComplex.isZero_of_isStrictlyGE K a n (by omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The chain of brutal truncations starts at the de Rham complex itself:
`Ω^•_{𝒪_X/A} = σ^{≥0}Ω^•_{𝒪_X/A}`, because the de Rham complex is concentrated in nonnegative
degrees. -/
@[stacks 0FM7 "the chain Ω^• = σ^{≥0}Ω^• ⊃ σ^{≥1}Ω^• ⊃ ⋯ starts at the de Rham complex itself:
the equality Ω^•_{X/S} = σ^{≥0}Ω^•_{X/S} at the left end of the display"]
theorem deRhamStupidSubcomplex_zero : deRhamStupidSubcomplex B D 0 = ⊤ :=
  have := isIso_ιStupidTrunc_of_isStrictlyGE (deRhamComplexInt (X := X) B D) 0
  Subobject.mk_eq_top_of_isIso _

/-! ### The graded pieces -/

/-- **The graded pieces of the brutal filtration of the de Rham complex.** The `p`-th graded
piece `gr^p(Ω^•_{𝒪_X/A})` is the single complex on the `p`-th term of the de Rham complex,
placed in degree `p`. -/
def deRhamStupidGradedPieceIso (p : ℤ) :
    (FilteredObject.gr p).obj
        (CochainComplex.stupidTruncationFiltration (deRhamComplexInt (X := X) B D)) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj
        ((deRhamComplexInt (X := X) B D).X p) :=
  CochainComplex.stupidGradedPieceIso (deRhamComplexInt (X := X) B D) p

/-- The term of the de Rham complex in a nonnegative degree `p` is the sheaf `Ω^p_{𝒪_X/A}` of
relative `p`-forms: extending a complex by zero does not change its terms in the degrees it
already had. -/
def deRhamComplexIntXIso (p : ℕ) :
    (deRhamComplexInt B D).X (p : ℤ) ≅ (deRhamComplex B D).X p :=
  (deRhamComplex B D).extendXIso embeddingUpNat (i := p) rfl

/-- **`gr^p(Ω^•_{𝒪_X/A}) = Ω^p_{𝒪_X/A}[-p]`.** In the derived category of sheaves of
`A`-modules the `p`-th graded piece of the brutal filtration of the de Rham complex is the sheaf
`Ω^p_{𝒪_X/A}` of relative `p`-forms, shifted down by `p`. -/
@[stacks 0FM7 "gr^p(Ω^•_{X/S}) = Ω^p_{X/S}[-p], the identification of the graded pieces of the
brutal filtration of the relative de Rham complex"]
def deRhamStupidGradedPieceDerivedIso (p : ℕ) :
    DerivedCategory.Q.obj ((FilteredObject.gr (p : ℤ)).obj
        (CochainComplex.stupidTruncationFiltration (deRhamComplexInt (X := X) B D))) ≅
      ((DerivedCategory.singleFunctor _ 0).obj ((deRhamComplex B D).X p))⟦(-(p : ℤ))⟧ :=
  CochainComplex.stupidGradedPieceDerivedIso (deRhamComplexInt (X := X) B D) (p : ℤ) ≪≫
    ((DerivedCategory.singleFunctor _ 0 ⋙
      shiftFunctor _ (-(p : ℤ))).mapIso (deRhamComplexIntXIso B D p))

/-! ### The Hodge filtration is a decreasing filtration -/

/-- The Hodge filtration `F^pH^n_{dR}(X/A)` is the image of the map
`H^n(X, σ^{≥p}Ω^•_{𝒪_X/A}) ⟶ H^n_{dR}(X/A)` induced by the inclusion of the brutal truncation. -/
theorem hodgeFiltration_eq_imageSubobject (p n : ℤ) :
    hodgeFiltration B D p n =
      imageSubobject (Stacks.Cohomology.FilteredComplex.hypercohomologyMap (baseRingedSpace A)
        (derivedSectionsBase A)
        (ιStupidTrunc (deRhamComplexInt (X := X) B D) (embeddingUpIntGE p)) n) :=
  rfl

/-- **The Hodge filtration is decreasing.** For `p ≤ q` the map
`H^n(X, σ^{≥q}Ω^•) ⟶ H^n_{dR}` factors through `H^n(X, σ^{≥p}Ω^•)`, so its image is contained
in the image of the latter. -/
theorem hodgeFiltration_antitone (n : ℤ) : Antitone (fun p => hodgeFiltration B D p n) := by
  intro p q h
  refine (imageSubobject_comp_le
    ((DerivedCategory.homologyFunctor _ n).map ((derivedSectionsBase A).map
      (DerivedCategory.Q.map (stupidTruncGEMapLE (deRhamComplexInt (X := X) B D) h)))) _).trans_eq'
    ?_
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, stupidTruncGEMapLE_ι]

/-! ### The first page in the abelian-sheaf realization -/

/-- **The first-page term of the Hodge-to-de Rham spectral sequence is the Hodge cohomology group
of Section 0FM6**, across the two realizations. The spectral sequence of
`AlgebraicGeometry.SheafOfModules.exists_hodgeToDeRhamSpectralSequence` has
`E_1^{p, q} = H^q(X, Ω^p_{𝒪_X/A})` computed by the unbounded derived global sections of sheaves
of `A`-modules, as a module over `A(X)`; forgetting that module structure gives the term in
position `p` of `AlgebraicGeometry.SheafOfModules.hodgeToDeRhamFirstPage`, which is formed with
Mathlib's classical right derived functor of sections of abelian sheaves.

The content is
`Stacks.Cohomology.UnderlyingAbelianSheaf.homologyDerivedSectionsSingleIsoRightDerivedAbelian`,
through [Stacks, Tag 0D5Y]; what is added here is that the `p`-th term of the `ℤ`-indexed de Rham
complex is the sheaf `Ω^p_{𝒪_X/A}` of relative `p`-forms. -/
def hodgeToDeRhamFirstPageXIso (p q : ℕ) :
    (forget₂ (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) (q : ℤ)).obj
          ((derivedSectionsBase A).obj
            ((DerivedCategory.singleFunctor
              (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) 0).obj
                ((deRhamComplexInt B D).X (p : ℤ))))) ≅
      (hodgeToDeRhamFirstPage B D q).X p :=
  Stacks.Cohomology.UnderlyingAbelianSheaf.homologyDerivedSectionsSingleIsoRightDerivedAbelian
      (structureSheafRing (baseRingedSpace A)) ⊤ (derivedSectionsBase A)
      (derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤)
      ((deRhamComplexInt (X := X) B D).X (p : ℤ)) q ≪≫
    ((sectionsFunctor X.carrier ⊤).rightDerived q).mapIso
      ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapIso
        (deRhamComplexIntXIso B D p))

/-! ### The Hodge-to-de Rham spectral sequence -/

/-- **The Hodge-to-de Rham spectral sequence of the brutal filtration of the de Rham complex.**

Read `Ω^•_{𝒪_X/A}` as a filtered complex of sheaves through its brutal truncations
`σ^{≥p}Ω^•_{𝒪_X/A}`. Its spectral sequence in the sense of [Stacks, Tag 0BKK] exists — through
the bounded-below form [Stacks, Tag 0BKL], the de Rham complex being concentrated in nonnegative
degrees — and comes packaged as a
`Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence`, the brutal-truncation
spectral sequence of [Stacks, Tag 0FLK], whose `e₁Iso` field is the first-page formula
`E_1^{p, q} = H^q(X, Ω^p_{𝒪_X/A})` of the Hodge-to-de Rham spectral sequence of Section 50.6. So
the two spectral sequences of Section 50.7's third assertion are one object, constructed once.

It is **bounded**, it **abuts to relative de Rham cohomology** `H^n_{dR}(X/A)`, and the
filtration of the abutment along which it converges is the **Hodge filtration**
`AlgebraicGeometry.SheafOfModules.hodgeFiltration` of [Stacks, Tag 0FM8]: the last conjunct
identifies `E_∞^{p, q}` with `F^pH^{p + q}_{dR} / F^{p + 1}H^{p + q}_{dR}`.

The fourth conjunct reads the first page in the abelian-sheaf realization: with the `A(X)`-module
structure forgotten, `E_1^{p, q}` is the term in position `p` of
`AlgebraicGeometry.SheafOfModules.hodgeToDeRhamFirstPage B D q`, the `q`-th row of the first page
of Section 50.6. -/
@[stacks 0FM7 "the spectral sequence of Cohomology Lemma 0BKK for Ω^•_{X/S} viewed as a filtered
complex of sheaves is the Hodge-to-de Rham spectral sequence built by Cohomology Example 0FLK:
one object, carrying the Tag 0FLK first page E_1^{p,q} = H^q(X, Ω^p), bounded, abutting to
H^n_dR(X/S), and converging along the Hodge filtration of Tag 0FM8. Its first page is identified
term by term with the abelian-sheaf first page `hodgeToDeRhamFirstPage` of Section 0FM6; the
differentials d_1 of the two first pages are not compared", sga "7 XXII 3.3" "more general"]
theorem exists_hodgeToDeRhamSpectralSequence :
    ∃ S : Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence
        (baseRingedSpace A) (deRhamComplexInt (X := X) B D),
      IsBounded S.spectralSequence ∧
      SpectralSequence.AbutsTo S.spectralSequence (deRhamCohomology (X := X) B D) ∧
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ hodgeFiltration B D a n = ⊤ ∧
        hodgeFiltration B D b n = ⊥) ∧
      (∀ p q : ℕ, Nonempty
        ((forget₂ (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
            (((Stacks.Cohomology.FilteredComplex.globalSectionsSpectralSequence
                (baseRingedSpace A) S.replacement).page 1 (by omega)).X ((p : ℤ), (q : ℤ))) ≅
          (hodgeToDeRhamFirstPage B D q).X p)) ∧
      ∀ p q : ℤ, Nonempty (S.spectralSequence.pageInfinity (p, q) ≅
        cokernel (Subobject.ofLE (hodgeFiltration B D (p + 1) (p + q))
          (hodgeFiltration B D p (p + q))
          (hodgeFiltration_antitone B D (p + q) (by omega)))) := by
  obtain ⟨I, i, hIge, hIfin, hIfilInj, hgr, hstep, hhom, -, hfirst, hbdd,
      F, hF, hFeq, hFfin, hinf, hinfIso⟩ :=
    Stacks.Cohomology.FilteredComplex.exists_spectralSequence_of_boundedBelowFilteredComplex
      (baseRingedSpace A) (derivedSectionsBase A)
      (derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤) inferInstance
      (CochainComplex.stupidTruncationFiltration (deRhamComplexInt (X := X) B D)) 0
      (isStrictlyGE_deRhamComplexInt B D)
      (CochainComplex.stupidTruncationFiltration_isDegreewiseFinite _)
  have hFH : F = fun n p => hodgeFiltration B D p n := by
    funext n p
    rw [hFeq n p]
    rfl
  subst hFH
  have hShift (p q : ℤ) : Nonempty
      (((Stacks.Cohomology.FilteredComplex.globalSectionsSpectralSequence
            (baseRingedSpace A) I).page 1 (by omega)).X (p, q) ≅
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) (p + q)).obj
          ((derivedSectionsBase A).obj
            (((DerivedCategory.singleFunctor
              (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) 0).obj
                ((deRhamComplexInt B D).X p))⟦(-p : ℤ)⟧))) := by
    obtain ⟨e⟩ := hfirst p q
    exact ⟨e ≪≫ Stacks.Cohomology.FilteredComplex.stupidGradedPieceHypercohomologyIso
      (baseRingedSpace A) (derivedSectionsBase A) (deRhamComplexInt (X := X) B D) p q⟩
  have hE1 (p q : ℤ) := (hShift p q).map fun e =>
    e ≪≫ Stacks.Cohomology.FilteredComplex.shiftHypercohomologyIso
      (baseRingedSpace A) (derivedSectionsBase A)
      (derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤) inferInstance
      ((deRhamComplexInt B D).X p) p q
  refine ⟨{ RΓ := derivedSectionsBase A
            α := derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤
            isRightDerived := inferInstance
            replacement := I
            replacementMap := i
            replacementMap_quasiIso := hhom
            replacementMap_step_quasiIso := hstep
            replacementMap_gr_quasiIso := hgr
            e₁IsoShift := hShift
            e₁Iso := hE1 },
    hbdd, ?_, hFfin, ?_, ?_⟩
  · exact SpectralSequence.AbutsTo.shiftStart
      (E := Stacks.Cohomology.FilteredComplex.globalSectionsSpectralSequence
        (baseRingedSpace A) I)
      ⟨hinf, _, hF, hFfin, hinfIso⟩ (by omega)
  · intro p q
    obtain ⟨e⟩ := hE1 (p : ℤ) (q : ℤ)
    exact ⟨(forget₂ (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapIso e ≪≫ hodgeToDeRhamFirstPageXIso B D p q⟩
  · intro p q
    have := hinf p q
    obtain ⟨e⟩ := hinfIso p q
    exact ⟨SpectralSequence.shiftStart_pageInfinityIso _ (by omega) (p, q) ≪≫ e⟩

end AlgebraicGeometry.SheafOfModules

end
