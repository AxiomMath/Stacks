module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineQuadrupleBijection
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineVeroneseNaturality

/-!
# [Stacks, Tag 01NU]: the functor `F_d` is represented by `U_d`

Let `S` be an **affine** scheme, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous
pieces (Situation 01NN), `A = Γ(S, 𝒜)` its graded ring of global sections, `d ≥ 1` and
`U_d ⊆ Proj(A)` the open of Equation 27.12.0.1. This file proves that the functor `F_d` of strict
equivalence classes of quadruples of Section 01NS is **representable by `U_d`**, as a
`CategoryTheory.Functor.RepresentableBy` for
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.functor`.

What stood between
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.fdEquiv` — the bijection
`F_d(T) ≃ Mor(T, U_d)` at a *fixed* test scheme `T` — and that `RepresentableBy` was the
**naturality in `T`** of the identification of `F_d` with the functor of triples of Section 01N4,
namely

`veroneseSections (ψ.pullback g)
  = ProjTriplePullback.pullbackSections _ (veroneseSections ψ) g`

for `g : T' ⟶ T`. Its two halves are proved in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineVeroneseNaturality.lean`, and joining
them needed exactly one identification of spellings, which is
`pullbackSectionHom_top_eq_pullbackUnit` below.

## Main results

* `...RelativeProjQcohSheaf.pullbackSectionHom_top_eq_pullbackUnit`: **the unit of
  `g^* ⊣ g_*` on sheaves of modules over a ringed space and the pullback of a global section over
  `AlgebraicGeometry.Scheme.Modules` are the same map of sections.** This is the identification
  the two halves of the naturality are stated across.
* `...RelativeProjQcohSheaf.veroneseSections_pullback`: **the identification `F_d = F_d^{triples}`
  is natural in the test scheme.**
* `...RelativeProjQcohSheaf.Quadruple.classifyingHom_pullback` and
  `...Quadruple.classifyingHomOfClass_pullback`: the classifying morphism of a pulled-back
  quadruple is the pullback of the classifying morphism.
* `...RelativeProjQcohSheaf.Fd.representableByDegreeOpen`: **[Stacks, Tag 01NU] for an affine
  base**, `(Fd.functor (situationAlgebra B) d).RepresentableBy U_d`, and
  `...Fd.isRepresentable_functor_of_isAffine` in the bare form.

## The identification, and why it holds

`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.sectionHom` carries a section along `g`
by `Stacks.RingedSpace.pullbackUnit`, the unit of the adjunction `g^* ⊣ g_*` on sheaves of
modules over the *ringed space* underlying `g`, whose left adjoint is
`Stacks.RingedSpace.pullbackFunctor`. `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection`
is built from `AlgebraicGeometry.pullbackSectionHom`, whose adjunction is
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`. Both left adjoints are
`CategoryTheory.SheafOfModules.pullback` of the same morphism of sheaves of rings — that is
`...RelativeProjQcohSheaf.modulesPullback_eq_pullbackFunctor`, which holds by `rfl` — and the
`CategoryTheory.Functor.IsRightAdjoint` argument each supplies is a proof of a proposition, so
the two adjunctions, and with them their units, are the same term. What is left is the
restriction along `⊤ ≤ g⁻¹⊤` that `pullbackSectionHom` carries and `pullbackUnit` does not; the
two opens are equal, the category of opens is thin, so that restriction is the identity. The
precedent this is copied from is
`Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSection_eq_pullbackUnitSections` together
with `...SectionsBaseChange.pullbackSectionsHom_top`, which say the same thing for
`...SectionsBaseChange.pullbackUnitSections`, the `Scheme.Modules`-level unit.

## From the naturality to the representability

With the identification in hand the degreewise naturality `veroneseRaw_pullback` is the two
halves composed: `...RelativeProjQcohSheaf.Twisting.globalSectionHom_pullback` rewrites the
degree-`n` value of the pulled-back twisting as the unit image of the original value, the
naturality `Stacks.RingedSpace.pullbackUnit_naturality` of the unit moves the comparison
`L ^⊗ n ≅ L^{⊗ n}` of [Stacks, Tag 01CU] past it, and
`...RelativeProjQcohSheaf.pullPowCompare_eq_powComparePull` — the square — exchanges that
comparison with the pullback of the powers. `veroneseSections_pullback` is that degreewise,
a `VeroneseSections` being determined by its degreewise family.

The classifying morphism then commutes with pullback by the triple-level naturality
`Stacks.AlgebraicGeometry.ProjClassifyingPullback.classifyingHom_pullbackSections`, and the
`RepresentableBy` is `Quadruple.fdEquiv` in the inverse direction, whose naturality clause is
exactly `Quadruple.classifyingHomOfClass_pullback` read through the bijection.

## The hypotheses the representability carries

`IsAffine S`, the quasi-coherence of every homogeneous piece of `situationAlgebra B`, and
`0 < d`. They are the hypotheses of the tag: the affineness and the quasi-coherence are what
`Quadruple.fdEquiv` needs (through the generation condition
`...RelativeProjQcohSheaf.Quadruple.iSup_nonvanishingOpen_psiSection_eq_top` and the converse
direction `...AffineTripleSections.quadruple`), and `0 < d` is the tag's `d ≥ 1`. Nothing is
carried beyond them: the naturality statements above are unconditional.

`U_d` here is the open of Equation 27.12.0.1 inside `Proj Γ(S, 𝒜)`, not the degree-`d` open of
the *relative* `Proj` of a `...RelativeProjQcohSheaf.RelativeProjData`; turning this into the
relative statement is the glueing problem described in the "What is not here" section of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineQuadrupleBijection.lean`.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry Stacks.RingedSpace
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare powCompare_hom_app_inv_app
  powCompare_inv_app_hom_app)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (psiSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso
  top_le_preimage_top)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The two spellings of the pullback of a global section -/

/-- **The pullback of a global section is the image of the unit of `g^* ⊣ g_*` on sheaves of
modules over a ringed space.** For `g : T' ⟶ T` and an `𝒪_T`-module `M`,
`AlgebraicGeometry.pullbackSectionHom`, built from
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, and
`Stacks.RingedSpace.pullbackUnit`, built from the adjunction over the underlying morphism of
ringed spaces, are the same map on global sections.

The two left adjoints are the same functor — `modulesPullback_eq_pullbackFunctor`, by `rfl` — and
the `CategoryTheory.Functor.IsRightAdjoint` argument each adjunction supplies is a proof of a
proposition, so the two units are the same morphism; the restriction along `⊤ ≤ g⁻¹⊤` that
`pullbackSectionHom` carries is the identity because the category of opens is thin. -/
public theorem pullbackSectionHom_top_eq_pullbackUnit {T' T : Scheme.{u}} (g : T' ⟶ T)
    (M : T.Modules) (x : M.val.obj (op (⊤ : Opens T.toRingedSpace.carrier))) :
    (AlgebraicGeometry.pullbackSectionHom g M ⊤ ⊤ (top_le_preimage_top g) x :
      ((Scheme.Modules.pullback g).obj M).val.obj (op (⊤ : Opens T'.toRingedSpace.carrier)))
      = pullbackUnit (ringedSpaceHom g) M (op (⊤ : Opens T.toRingedSpace.carrier)) x := by
  change ((Scheme.Modules.pullback g).obj M).presheaf.map _ _ = _
  rw [show (homOfLE (top_le_preimage_top g)).op = 𝟙 _ from Subsingleton.elim _ _]
  simp
  rfl

/-- Reading a composite of morphisms of modules on a global section. -/
private theorem comp_val_app_apply {T : Scheme.{u}} {M N P : T.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (U : (Opens T.toRingedSpace.carrier)ᵒᵖ) (z : M.val.obj U) :
    (a ≫ b).val.app U z = b.val.app U (a.val.app U z) :=
  rfl

/-! ### The naturality of the Veronese family in the test scheme -/

section Naturality

variable {T' T S : Scheme.{u}} {f : T ⟶ S} {B : SheafGradedAlgebra S} {d : ℕ}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]

/-- **The pullback of a global section of `L ^⊗ n`, in the unit spelling.**
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection` is the unit image of the section
read through the comparison `(g^*L) ^⊗ n ≅ g^*(L ^⊗ n)`. -/
public theorem pullSection_eq_pullbackUnit (g : T' ⟶ T) (n : ℕ) (w : Γ(natTensorPow L n, ⊤)) :
    pullSection g L n w
      = (pullbackNatTensorPowIso g L n).inv.app ⊤
          (pullbackUnit (ringedSpaceHom g) (natTensorPow L n : T.Modules)
            (op (⊤ : Opens T.toRingedSpace.carrier)) w) :=
  congrArg (fun z => (pullbackNatTensorPowIso g L n).inv.app ⊤ z)
    (pullbackSectionHom_top_eq_pullbackUnit g (natTensorPow L n) w)

/-- `pullPowCompare_eq_powComparePull` read on a global section of `g^*(L ^⊗ n)`. -/
private theorem powCompare_hom_app_pullbackNatTensorPowIso_inv (g : T' ⟶ T) (n : ℕ)
    (z : ((Scheme.Modules.pullback g).obj (natTensorPow L n)).val.obj
      (op (⊤ : Opens T'.toRingedSpace.carrier))) :
    (powCompare (LaurentPullback.pullbackModule g L) n).hom.app ⊤
        ((pullbackNatTensorPowIso g L n).inv.app ⊤ z)
      = (laurentPullback g L (n : ℤ)).val.app (op (⊤ : Opens T'.toRingedSpace.carrier))
          (((Scheme.Modules.pullback g).map (powCompare L n).hom).val.app
            (op (⊤ : Opens T'.toRingedSpace.carrier)) z) :=
  (comp_val_app_apply (pullbackNatTensorPowIso g L n).inv
      (powCompare (LaurentPullback.pullbackModule g L) n).hom
      (op (⊤ : Opens T'.toRingedSpace.carrier)) z).symm.trans
    ((congrArg (fun φ : (Scheme.Modules.pullback g).obj (natTensorPow L n) ⟶
          (laurent (LaurentPullback.pullbackModule g L)).piece (n : ℤ) =>
        φ.val.app (op (⊤ : Opens T'.toRingedSpace.carrier)) z)
      (pullPowCompare_eq_powComparePull g L n)).trans
      (comp_val_app_apply ((Scheme.Modules.pullback g).map (powCompare L n).hom)
        (laurentPullback g L (n : ℤ)) (op (⊤ : Opens T'.toRingedSpace.carrier)) z))

/-- The unit of `g^* ⊣ g_*` is natural in the module, read on the comparison `L ^⊗ n ≅ L^{⊗ n}`
of [Stacks, Tag 01CU] and a global section. -/
private theorem pullbackUnit_app_powCompare_hom (g : T' ⟶ T) (n : ℕ)
    (w : Γ(natTensorPow L n, ⊤)) :
    ((Scheme.Modules.pullback g).map (powCompare L n).hom).val.app
        (op (⊤ : Opens T'.toRingedSpace.carrier))
        (pullbackUnit (ringedSpaceHom g) (natTensorPow L n : T.Modules)
          (op (⊤ : Opens T.toRingedSpace.carrier)) w)
      = pullbackUnit (ringedSpaceHom g) ((laurent L).piece (n : ℤ))
          (op (⊤ : Opens T.toRingedSpace.carrier)) ((powCompare L n).hom.app ⊤ w) :=
  pullbackUnit_naturality (f := ringedSpaceHom g) (powCompare L n).hom
    (op (⊤ : Opens T.toRingedSpace.carrier)) w

/-- **The degree-`n` value of the Veronese family of a pulled-back twisting is the pullback of
the degree-`n` value of the Veronese family.** This is the two halves of the naturality in `T`
joined by `pullbackSectionHom_top_eq_pullbackUnit`:
`Twisting.globalSectionHom_pullback` presents the value of `g^*ψ` as the unit image of the value
of `ψ`, `pullbackUnit_app_powCompare_hom` moves the comparison `L ^⊗ n ≅ L^{⊗ n}` of
[Stacks, Tag 01CU] past the unit, and `pullPowCompare_eq_powComparePull` exchanges that
comparison with the pullback of the powers.

Unconditional: no affineness of `S` and no quasi-coherence of `𝒜` is used. -/
public theorem veroneseRaw_pullback (ψ : Twisting f (situationAlgebra B) (d : ℤ) L)
    (g : T' ⟶ T) (n : ℕ) (x : B.sectionPieces ⊤ (n * d)) :
    veroneseRaw (ψ.pullback g) n x = pullSection g L n (veroneseRaw ψ n x) := by
  have hA : (ψ.pullback g).globalSectionHom (n : ℤ) x
      = (powCompare (LaurentPullback.pullbackModule g L) n).hom.app ⊤
          ((pullbackNatTensorPowIso g L n).inv.app ⊤
            (pullbackUnit (ringedSpaceHom g) (natTensorPow L n : T.Modules)
              (op (⊤ : Opens T.toRingedSpace.carrier)) (veroneseRaw ψ n x))) :=
    (Twisting.globalSectionHom_pullback ψ g (n : ℤ) x).trans
      ((congrArg (fun z => (laurentPullback g L (n : ℤ)).val.app
            (op (⊤ : Opens T'.toRingedSpace.carrier)) z)
          ((congrArg (fun u => pullbackUnit (ringedSpaceHom g) ((laurent L).piece (n : ℤ))
                (op (⊤ : Opens T.toRingedSpace.carrier)) u)
              (powCompare_hom_app_inv_app L n (ψ.globalSectionHom (n : ℤ) x)).symm).trans
            (pullbackUnit_app_powCompare_hom g n (veroneseRaw ψ n x)).symm)).trans
        (powCompare_hom_app_pullbackNatTensorPowIso_inv g n _).symm)
  exact (congrArg (fun z => (powCompare (LaurentPullback.pullbackModule g L) n).inv.app ⊤ z)
      hA).trans
    ((powCompare_inv_app_hom_app (LaurentPullback.pullbackModule g L) n _).trans
      (pullSection_eq_pullbackUnit g n (veroneseRaw ψ n x)).symm)

/-- A triple's graded map is determined by its degreewise family, the multiplicativity being a
proposition. -/
private theorem veroneseSections_ext {Y : Scheme.{u}} {N : Y.Modules}
    {X Z : VeroneseSections (B.grading (⊤ : S.Opens)) d N}
    (h : ∀ n, X.toFun n = Z.toFun n) : X = Z := by
  cases X with
  | mk tx hx =>
    cases Z with
    | mk ty hy =>
      have htx : tx = ty := funext h
      subst htx
      rfl

/-- **Stacks Project, Tag 01NU: the identification of `F_d` with the functor of triples of
Section 01N4 is natural in the test scheme.** For a morphism `g : T' ⟶ T` of test schemes the
triple of Section 01N4 induced by the pullback along `g` of the twisting of a quadruple of
Section 01NS is the pullback along `g` of the triple the twisting induces.

Degreewise this is `veroneseRaw_pullback`, and a `VeroneseSections` is determined by its
degreewise family.

Unconditional: no affineness of `S` and no quasi-coherence of `𝒜` is used. -/
public theorem veroneseSections_pullback (ψ : Twisting f (situationAlgebra B) (d : ℤ) L)
    (g : T' ⟶ T) :
    veroneseSections (ψ.pullback g)
      = ProjTriplePullback.pullbackSections (B.grading (⊤ : S.Opens)) (veroneseSections ψ) g :=
  veroneseSections_ext fun n => AddMonoidHom.ext fun a =>
    veroneseRaw_pullback ψ g n ((a : B.sectionRing ⊤) (n * d))

end Naturality

/-! ### `F_d` is represented by `U_d` -/

section Representable

variable {T' T S : Scheme.{u}} {f : T ⟶ S} {B : SheafGradedAlgebra S} {k : ℕ}

/-- **Rewriting the graded map inside a classifying morphism.** The generation condition
`Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom` takes is a proposition whose
statement mentions the graded map, so an equality of graded maps cannot be rewritten under it;
after `subst` the two generation conditions are proofs of the same proposition and the two sides
are definitionally equal. -/
private theorem classifyingHom_congr {Y : Scheme.{u}} {N : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y N]
    (hk : 0 < k) {χ χ' : VeroneseSections (B.grading (⊤ : S.Opens)) k N} (h : χ = χ')
    (hg : ⨆ g : B.grading (⊤ : S.Opens) k,
      nonvanishingOpen Y N (psiSection (B.grading (⊤ : S.Opens)) χ g) = ⊤)
    (hg' : ⨆ g : B.grading (⊤ : S.Opens) k,
      nonvanishingOpen Y N (psiSection (B.grading (⊤ : S.Opens)) χ' g) = ⊤) :
    Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
          (B.grading (⊤ : S.Opens)) hk χ hg
      = Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
          (B.grading (⊤ : S.Opens)) hk χ' hg' := by
  subst h
  rfl

/-- **Stacks Project, Tag 01NU: the classifying morphism of a quadruple is natural in the test
scheme.** The morphism `T' ⟶ U_d` classified by the pullback of a quadruple along `g : T' ⟶ T` is
`g` followed by the morphism classified by the quadruple.

Two inputs: the naturality `veroneseSections_pullback` of the identification with the triples of
Section 01N4, and the naturality
`Stacks.AlgebraicGeometry.ProjClassifyingPullback.classifyingHom_pullbackSections` of the
classification of [Stacks, Tag 01N8] in the test scheme. -/
public theorem Quadruple.classifyingHom_pullback [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (P : Quadruple f (situationAlgebra B) (k : ℤ)) (g : T' ⟶ T) :
    Quadruple.classifyingHom hk hqc (P.pullback g)
      = g ≫ Quadruple.classifyingHom hk hqc P :=
  (classifyingHom_congr hk (veroneseSections_pullback P.twisting g)
      (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc (P.pullback g))
      (ProjTriplePullback.iSup_nonvanishingOpen_pullbackSections (B.grading (⊤ : S.Opens))
        (veroneseSections P.twisting) g
        (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc P))).trans
    (ProjClassifyingPullback.classifyingHom_pullbackSections (B.grading (⊤ : S.Opens)) hk
      (veroneseSections P.twisting)
      (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc P) g)

/-- **Stacks Project, Tag 01NU: the map `F_d(T) → Mor(T, U_d)` is natural in the test scheme**,
on strict equivalence classes. This is `Quadruple.classifyingHom_pullback` read on the quotient,
on which `...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass` is `Quotient.lift` of
`...RelativeProjQcohSheaf.Quadruple.classifyingHom`. -/
public theorem Quadruple.classifyingHomOfClass_pullback [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent) (g : T' ⟶ T)
    (ξ : Fd (situationAlgebra B) (k : ℤ) T) :
    Quadruple.classifyingHomOfClass hk hqc (Fd.pullback g ξ).2
      = g ≫ Quadruple.classifyingHomOfClass hk hqc ξ.2 := by
  obtain ⟨h, q⟩ := ξ
  induction q using Quotient.ind with
  | _ P => exact Quadruple.classifyingHom_pullback hk hqc P g

/-- **Stacks Project, Tag 01NU: the functor `F_d` of Section 01NS is represented by the open
`U_d ⊆ Proj Γ(S, 𝒜)` of Equation 27.12.0.1.** Let `S` be affine, `𝒜` a graded `𝒪_S`-algebra with
quasi-coherent homogeneous pieces (Situation 01NN) and `d ≥ 1`. The bijections
`...RelativeProjQcohSheaf.Quadruple.fdEquiv` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineQuadrupleBijection.lean`, one for each
test scheme, form a natural isomorphism `Mor(−, U_d) ≅ F_d`: the naturality clause is
`Quadruple.classifyingHomOfClass_pullback`, transported across the bijection.

The hypotheses are exactly `IsAffine S`, the quasi-coherence of the homogeneous pieces, and
`0 < d`; the naturality statements the proof rests on are unconditional. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   Hypotheses carried: IsAffine S, quasi-coherence of every homogeneous piece of situationAlgebra B,
--   and 0 < d. NOT the RELATIVE statement: U_d here is the open inside Proj Gamma(S, A) for an affine S,
--   not the degree-d open of the relative Proj of a RelativeProjData; the glueing of these affine-local
--   representations over a cover of the base is ChartDegreeOpenEquiv.ProjDegreeRepresentation.ofCharts,
--   so residue (i) of Tag 01NY is proved over an arbitrary base and Tag 01NY itself is
--   RelativeProjRepresents.F.isRepresentable_relativeProjOfCharts
@[stacks 01NU "THE TAG, for an AFFINE base: for S affine, A with quasi-coherent homogeneous pieces \
(Situation 01NN) and d >= 1, the functor F_d of strict equivalence classes of quadruples of Section 01NS is \
REPRESENTABLE by the open U_d of Equation 27.12.0.1 inside Proj Gamma(S, A) a \
CategoryTheory.Functor.RepresentableBy for Fd.functor, i.e. the bijections Quadruple.fdEquiv together with \
their naturality in the test scheme (Quadruple.classifyingHomOfClass_pullback, which rests on the \
unconditional veroneseSections_pullback)."]
public def Fd.representableByDegreeOpen [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent) :
    (Fd.functor (situationAlgebra B) (k : ℤ)).RepresentableBy
      (degreeOpen (B.grading (⊤ : S.Opens)) k).toScheme where
  homEquiv {X} := (Quadruple.fdEquiv hk hqc).symm
  homEquiv_comp {X X'} g φ :=
    (Quadruple.fdEquiv hk hqc).injective
      (((Quadruple.fdEquiv hk hqc).apply_symm_apply (g ≫ φ)).trans
        ((congrArg (fun z => g ≫ z)
            ((Quadruple.fdEquiv hk hqc).apply_symm_apply φ)).symm.trans
          (Quadruple.classifyingHomOfClass_pullback hk hqc g
            ((Quadruple.fdEquiv hk hqc).symm φ)).symm))

/-- **Stacks Project, Tag 01NU in the bare form.** `Fd.representableByDegreeOpen` forgetting the
representing scheme. -/
public theorem Fd.isRepresentable_functor_of_isAffine [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent) :
    (Fd.functor (situationAlgebra B) (k : ℤ)).IsRepresentable :=
  (Fd.representableByDegreeOpen hk hqc).isRepresentable

end Representable

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
