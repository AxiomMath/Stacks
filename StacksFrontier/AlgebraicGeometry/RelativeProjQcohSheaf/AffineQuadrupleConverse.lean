module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleMorphismConverse
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineQuadrupleRoundTrip
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

/-!
# Strict equivalence of quadruples from one morphism into `U_d`

Let `S` be an **affine** scheme, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous
pieces (Situation 01NN), `A = Γ(S, 𝒜)`, `d ≥ 1` and `U_d ⊆ Proj(A)` the open of Equation
27.12.0.1. A quadruple `(d, f : T → S, L, ψ)` of Section 01NS induces a triple `(d, L, ψ^♭)` of
Section 01N4 (`...RelativeProjQcohSheaf.veroneseSections`), and [Stacks, Tag 01N8] attaches to
that triple a pair `(φ, α)` with `φ : T ⟶ U_d` and `α : φ⁎𝒪(d) ≅ L`.

`...ProjTripleMorphismConverse.sectionsEquiv_of_isCompatible` says that two triples carried by
two compatible pairs over **one and the same** `φ` are strictly equivalent *as triples*: there is
an isomorphism `β = α⁻¹ ∘ α' : L ≅ L'` whose **natural-number** tensor powers
`Stacks.AmplePullbackPart1.natTensorPowCongr` carry one graded map to the other. That is not what
strict equivalence of **quadruples** is defined by: `...Quadruple.StrictlyEquivalent` demands an
isomorphism `γ` of the **Laurent algebras** `⨁_{n ∈ ℤ} L^{⊗ n}` of [Stacks, Tag 01CU] carrying
`ψ` to `ψ'` in every **integral** degree, which the tensor powers of `β` say nothing about.

**This file supplies the missing lift**, and `Quadruple.strictlyEquivalent_of_isCompatible` is
the conclusion: two quadruples over the same `f` whose induced triples are compatible with pairs
over one `φ` are strictly equivalent.

## The route, and why it avoids a comparison of the two spellings of a tensor power

The candidate `γ` is not new: it is `...LaurentAlgebraCongr.laurentCongrIso` applied to `β`,
which has been available since that module and whose degree-one component is `β` itself
(`laurentCongrIso_app_one`). What was missing is that it satisfies the degreewise conditions, and
the obvious route to those — identifying `comparisonFamily (laurentCongrIso β)` with
`natTensorPowCongr β` degreewise, so that the strict equivalence of triples transports — is a
comparison of two systems of tensor powers across two monoidal structures and is **not** carried
out here. It is not needed.

What is used instead is that the degreewise squares of [Stacks, Tag 01N8] hold for *any*
multiplicative degreewise family of comparisons agreeing with `β` in degrees zero and one. The
three statements of `...ProjTripleMorphismConverse` that produce those squares were stated for
the tensor powers of `β` alone and are generalised, in place, to an arbitrary family:
`zero_pow_of_isoFamily`, `one_of_isoFamily`, `pow_of_isCompatible_of_isoFamily` and
`toFun_of_pow_of_isoFamily`, over `...ProjTripleClassifying.pow_of_isoFamily`. Feeding them
`comparisonFamily (laurentCongrIso β)` then needs exactly three facts about it, all proved below
and none of them a comparison of tensor-power systems:

* `mulSections_comparisonFamily`: it is multiplicative for the product of honest global sections.
  This is the `map_mul` field of a homomorphism of sheaves of graded algebras, read through
  `...CoherentMulSections.mulSections_mulBilinear`.
* `comparisonFamily_zero_unitGlobal` with `laurentCongrIso_app_zero`: its degree-zero component
  carries the unit section to the unit section, because the degree-zero component of
  `laurentCongrIso` is the identity.
* `unitorPow_comparisonFamily_laurentCongrIso_one`: its degree-one component is `β` through the
  two left unitors, which is `...RelativeProjQcohSheaf.unitorPow_comparisonFamily_one` fed
  `laurentCongrIso_app_one`.

The remaining step is from the degreewise squares, which live on global sections of the iterated
tensor powers, back to the morphism-level identity `ψ ≫ γ = ψ'` that a strict equivalence is
stated by. That is where the affineness of `S` and the quasi-coherence of `𝒜` enter, and only
there: in each degree both sides are morphisms out of the pullback of a quasi-coherent module
over an affine base, hence determined by their effect on global sections
(`Stacks.AlgebraicGeometry.AffineHomRecovery.hom_ext`). In a negative degree there is nothing to
check, the source having no nonzero global section.

## Main results

* `...RelativeProjQcohSheaf.mulSections_comparisonFamily`: **the comparison of the induced
  triples attached to an isomorphism of the Laurent algebras is multiplicative** on global
  sections.
* `...RelativeProjQcohSheaf.toFun_comparisonFamily_laurentCongrIso`: **the comparison attached to
  `β = α⁻¹ ∘ α'` carries one graded map to the other in every degree**, in the Laurent-algebra
  spelling. Unconditional.
* `...RelativeProjQcohSheaf.Twisting.app_comp_eq_of_globalSectionHom`: **a homomorphism of the
  Laurent algebras carries one twisting to another as soon as it does so on global sections**,
  over an affine base. This is the converse of
  `...RelativeProjQcohSheaf.Twisting.app_globalSectionHom`.
* `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_of_isCompatible`: **the lift to
  quadruples** — two quadruples whose induced triples are compatible with pairs over one
  morphism `T ⟶ U_d` are strictly equivalent.

## What is not here

The second composite `F_d(T) → Mor(T, U_d) → F_d(T)` of [Stacks, Tag 01NU] is not here, but it is
no longer missing: the two compatible pairs over one `φ` are **hypotheses** of
`Quadruple.strictlyEquivalent_of_isCompatible`, and
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineQuadrupleBijection.lean` produces them
— for a quadruple `P` from `...ProjTripleClassifying.classifyingPair` of its own induced triple,
for the quadruple `...AffineTripleSections.quadrupleOfHom` attached to `φ` from the same
construction read through `...RelativeProjQcohSheaf.Quadruple.classifyingHom_quadrupleOfHom` —
and concludes `...RelativeProjQcohSheaf.Quadruple.fdOfHom_classifyingHomOfClass` and the
bijection `...RelativeProjQcohSheaf.Quadruple.fdEquiv`.

What is still **not** proved is the representability of `F_d` asserted by the tag: the bijection
is one of sets for each fixed test scheme, and no naturality in `T` is established. Nothing below
carries an attribute claiming the composite, the bijection, or the representability.

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

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.CoherentMulSections
open Stacks.AlgebraicGeometry.MorphismsIntoProj (pullbackTwist)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (IsCompatible psiSection unitorPow)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections mulSections)
open Stacks.AlgebraicGeometry.ProjTripleStructureMorphism (unitGlobal)
open Stacks.AlgebraicGeometry.ProjTripleMorphismConverse
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {T : Scheme.{u}} {M N : T.Modules}
  [Stacks.Ample.IsInvertibleModule T M] [Stacks.Ample.IsInvertibleModule T N]

/-- **The degreewise comparison of the induced triples attached to an isomorphism of the Laurent
algebras is multiplicative for the product of honest global sections.** -/
theorem mulSections_comparisonFamily (γ : laurent M ≅ laurent N) (p q : ℕ)
    (s : Γ(natTensorPow M p, ⊤)) (t : Γ(natTensorPow M q, ⊤)) :
    (comparisonFamily γ (p + q)).hom.app ⊤ (mulSections M s t)
      = mulSections N ((comparisonFamily γ p).hom.app ⊤ s)
          ((comparisonFamily γ q).hom.app ⊤ t) := by
  set x := (powCompare M p).hom.app ⊤ s with hx
  set y := (powCompare M q).hom.app ⊤ t with hy
  have hs : (powCompare M p).inv.app ⊤ x = s := powCompare_inv_app_hom_app M p s
  have ht : (powCompare M q).inv.app ⊤ y = t := powCompare_inv_app_hom_app M q t
  have hmulM : (powCompare M (p + q)).hom.app ⊤ (mulSections M s t)
      = (Stacks.SheafOfModules.TensorPower.mulBilinear T.presheaf (hStruct T) M
          (p : ℤ) (q : ℤ)).app (op ⊤) x y := by
    rw [← hs, ← ht, mulSections_mulBilinear M p q x y]
    exact powCompare_hom_app_inv_app M (p + q) _
  have key : (γ.hom.app ((p : ℤ) + (q : ℤ))).val.app (op (⊤ : Opens T.toRingedSpace.carrier))
        ((Stacks.SheafOfModules.TensorPower.mulBilinear T.presheaf (hStruct T) M
          (p : ℤ) (q : ℤ)).app (op ⊤) x y)
      = (Stacks.SheafOfModules.TensorPower.mulBilinear T.presheaf (hStruct T) N
          (p : ℤ) (q : ℤ)).app (op ⊤)
            ((γ.hom.app (p : ℤ)).val.app (op ⊤) x) ((γ.hom.app (q : ℤ)).val.app (op ⊤) y) :=
    γ.hom.map_mul (p : ℤ) (q : ℤ) (op ⊤) x y
  have hstep : (γ.hom.app ((p : ℤ) + (q : ℤ))).val.app
        (op (⊤ : Opens T.toRingedSpace.carrier))
        ((powCompare M (p + q)).hom.app ⊤ (mulSections M s t))
      = (Stacks.SheafOfModules.TensorPower.mulBilinear T.presheaf (hStruct T) N
          (p : ℤ) (q : ℤ)).app (op ⊤)
            ((γ.hom.app (p : ℤ)).val.app (op ⊤) x) ((γ.hom.app (q : ℤ)).val.app (op ⊤) y) :=
    (congrArg (fun z => (γ.hom.app ((p : ℤ) + (q : ℤ))).val.app
      (op (⊤ : Opens T.toRingedSpace.carrier)) z) hmulM).trans key
  refine (comparisonFamily_hom_app γ (p + q) (mulSections M s t)).trans ?_
  refine (congrArg (fun z => (powCompare N (p + q)).inv.app ⊤ z) hstep).trans ?_
  refine (mulSections_mulBilinear N p q
    ((γ.hom.app (p : ℤ)).val.app (op ⊤) x) ((γ.hom.app (q : ℤ)).val.app (op ⊤) y)).symm.trans ?_
  rw [comparisonFamily_hom_app γ p s, comparisonFamily_hom_app γ q t]

/-- **The degree-zero component of the comparison attached to an isomorphism of Laurent algebras
whose degree-zero component is the identity carries the unit section to the unit section.** -/
theorem comparisonFamily_zero_unitGlobal (γ : laurent M ≅ laurent N)
    (h0 : γ.hom.app 0 = CategoryStruct.id _) :
    (comparisonFamily γ 0).hom.app ⊤ (unitGlobal M) = unitGlobal N := by
  have hid : ∀ z, (γ.hom.app ((0 : ℕ) : ℤ)).val.app
      (op (⊤ : Opens T.toRingedSpace.carrier)) z = z := by
    have hz : γ.hom.app ((0 : ℕ) : ℤ) = CategoryStruct.id _ := h0
    intro z
    rw [hz]
    rfl
  refine Function.LeftInverse.injective (powCompare_inv_app_hom_app N 0)
    (Eq.trans ?_ (powCompare_zero_globalSection_id N).symm)
  refine Eq.trans (congrArg (fun z => (powCompare N 0).hom.app ⊤ z)
    (comparisonFamily_hom_app γ 0 (unitGlobal M))) ?_
  refine (powCompare_hom_app_inv_app N 0 _).trans ?_
  exact (hid _).trans (powCompare_zero_globalSection_id M)

/-- **The degree-zero component of the comparison of Laurent algebras induced by an isomorphism
of the invertible modules is the identity.** The degree-zero pieces of the two Laurent algebras
are both the structure sheaf, and the recursion defining the comparison starts from the identity
there. -/
theorem laurentCongrIso_app_zero (β : M ≅ N) :
    (laurentCongrIso β).hom.app 0 = CategoryStruct.id _ := rfl

/-- **The degree-one compatibility of the comparison of the induced triples with `β`**, the
hypothesis `Stacks.AlgebraicGeometry.ProjTripleClassifying.isCompatible_of_isoFamily` and
`...ProjTripleMorphismConverse.one_of_isoFamily` ask for. It holds because the degree-one
component of the comparison of the Laurent algebras is `β` itself, read through the
identification `L^{⊗ 1} ≅ L` of [Stacks, Tag 01CU]
(`...LaurentAlgebraCongr.laurentCongrIso_app_one`). -/
theorem unitorPow_comparisonFamily_laurentCongrIso_one (β : M ≅ N)
    (y : Γ(natTensorPow M 1, ⊤)) :
    (unitorPow N).hom.app ⊤ ((comparisonFamily (laurentCongrIso β) 1).hom.app ⊤ y)
      = β.hom.app ⊤ ((unitorPow M).hom.app ⊤ y) :=
  unitorPow_comparisonFamily_one β (laurentCongrIso β)
    (fun u => val_app_of_eq_comp_inv ((laurentCongrIso β).hom.app 1) (onePowIso M).hom β.hom
      (onePowIso N) ⊤ u (laurentCongrIso_app_one β)) y

section Degreewise

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ}

/-- **Stacks Project, Tag 01NU: the comparison of the two induced triples attached to the
isomorphism `β = α⁻¹ ∘ α'` of the invertible modules carries one graded map to the other in
every degree.**

Let `(d, L, ψ)` and `(d, L', ψ')` be triples of Section 01N4 for the graded ring `A` over a
scheme `T` which are compatible, in the sense of [Stacks, Tag 01N8], with pairs `(φ, α)` and
`(φ, α')` over **one and the same** morphism `φ : T ⟶ U_d`, and let
`β = α⁻¹ ∘ α' : L ≅ L'`. Then the comparison of the Laurent algebras of [Stacks, Tag 01CU] that
`β` induces (`...LaurentAlgebraCongr.laurentCongrIso`), read on the iterated tensor powers
(`...RelativeProjQcohSheaf.comparisonFamily`), carries the degree-`n` component of `ψ` to that of
`ψ'` for every `n`.

The point is that the comparison is produced **in the Laurent-algebra spelling**, not in the
spelling `Stacks.AmplePullbackPart1.natTensorPowCongr` of iterated tensor powers of `β`, which
is the spelling `...ProjTripleMorphismConverse.sectionsEquiv_of_isCompatible` supplies and the
only one the strict equivalence of *triples* of Section 01N4 is stated with. A strict equivalence
of *quadruples* of Section 01NS is defined by an isomorphism of the Laurent algebras, so it is
this spelling that a quadruple-level comparison has to be assembled from.

Three inputs: the multiplicativity `mulSections_comparisonFamily` of the comparison, which is
the multiplicativity of a homomorphism of sheaves of graded algebras read on sections; the
degree-zero value `comparisonFamily_zero_unitGlobal`, available because the degree-zero component
of the comparison is the identity (`laurentCongrIso_app_zero`); and the degree-one compatibility
`unitorPow_comparisonFamily_laurentCongrIso_one` with `β`. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   , and ONLY that: for two triples of Section 01N4 compatible with two pairs of Tag 01N8 over
--   the SAME morphism phi, the comparison of the Laurent algebras of Tag 01CU induced by beta =
--   alpha^{-1} alpha', read on the iterated tensor powers, carries the degree-n component of one
--   graded map to that of the other in every degree n. Unconditional no affineness of S and no
--   quasi-coherence. This is the converse direction of comparisonFamily_toFun, whose hypothesis
--   it supplies in the spelling a strict equivalence of QUADRUPLES of Section 01NS is defined by.
--   It is NOT that strict equivalence the morphism-level identity psi . gamma = psi' is not
--   obtained here NOT the bijection Mor(T, U_d) = F_d(T) and NOT the representability of F_d
--   that the tag asserts, which is Fd.representableByDegreeOpen of AffineFdRepresentable
theorem toFun_comparisonFamily_laurentCongrIso {ψ : VeroneseSections 𝒜 d M}
    {ψ' : VeroneseSections 𝒜 d N}
    (hgen : ⨆ g : 𝒜 d, nonvanishingOpen T M (psiSection 𝒜 ψ g) = ⊤)
    (hgen' : ⨆ g : 𝒜 d, nonvanishingOpen T N (psiSection 𝒜 ψ' g) = ⊤)
    {φ : T ⟶ (degreeOpen 𝒜 d).toScheme} {α : pullbackTwist 𝒜 φ (d : ℤ) ≅ M}
    {α' : pullbackTwist 𝒜 φ (d : ℤ) ≅ N}
    (hp : IsCompatible 𝒜 ψ ⟨φ, α⟩) (hp' : IsCompatible 𝒜 ψ' ⟨φ, α'⟩) (n : ℕ)
    (x : 𝒜 (n * d)) :
    (comparisonFamily (laurentCongrIso (α.symm ≪≫ α')) n).hom.app ⊤ (ψ.toFun n x)
      = ψ'.toFun n x :=
  toFun_of_pow_of_isoFamily 𝒜 hgen hp hp'
    (comparisonFamily (laurentCongrIso (α.symm ≪≫ α'))) n
    (fun g => pow_of_isCompatible_of_isoFamily 𝒜 hgen hgen'
      (comparisonFamily (laurentCongrIso (α.symm ≪≫ α')))
      (mulSections_comparisonFamily (laurentCongrIso (α.symm ≪≫ α')))
      (comparisonFamily_zero_unitGlobal (laurentCongrIso (α.symm ≪≫ α'))
        (laurentCongrIso_app_zero (α.symm ≪≫ α')))
      (unitorPow_comparisonFamily_laurentCongrIso_one (α.symm ≪≫ α')) hp hp' n g.2) x

end Degreewise

/-! ### From the degreewise maps on global sections back to the morphisms -/

section Morphisms

variable {S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-- **Over an affine base with quasi-coherent homogeneous pieces, a homomorphism of the Laurent
algebras carries one twisting to another as soon as it does so on the degreewise maps on global
sections.** This is the converse of
`...RelativeProjQcohSheaf.Twisting.app_globalSectionHom`, which reads the morphism-level identity
`ψ ≫ γ = ψ'` on global sections.

In each degree both sides are morphisms out of the pullback of a quasi-coherent module over an
affine base, which are determined by their effect on global sections
(`Stacks.AlgebraicGeometry.AffineHomRecovery.hom_ext`); that effect is
`Twisting.globalSectionHom` for `ψ'`, and for the composite it is the effect of `ψ` followed by
the degree-`i` component of `γ`. -/
theorem Twisting.app_comp_eq_of_globalSectionHom [IsAffine S]
    (hqc : ∀ i : ℤ, (AffineTwisting.pieceMod A i).IsQuasicoherent)
    {ψ : Twisting f A d M} {ψ' : Twisting f A d N} (γ : laurent M ⟶ laurent N)
    (h : ∀ (i : ℤ) (y : (A.piece (i * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier))),
      (γ.app i).val.app (op (⊤ : Opens T.toRingedSpace.carrier)) (ψ.globalSectionHom i y)
        = ψ'.globalSectionHom i y)
    (i : ℤ) : ψ.app i ≫ γ.app i = ψ'.app i := by
  let := hqc (i * d)
  refine AffineHomRecovery.hom_ext f (AffineTwisting.pieceMod A (i * d))
    ((laurent N).piece i) fun x => ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply (ψ.app i) (γ.app i) _ _).symm ?_
  refine Eq.trans (congrArg
    (fun z => (γ.app i).val.app (op (⊤ : Opens T.toRingedSpace.carrier)) z)
    (Twisting.globalSectionHom_eq_sectionHom ψ i x)).symm ?_
  exact (h i x).trans (Twisting.globalSectionHom_eq_sectionHom ψ' i x)

end Morphisms

/-! ### The strict equivalence of quadruples -/

section Quadruple

variable {S : Scheme.{u}} {f : T ⟶ S} {B : SheafGradedAlgebra S} {k : ℕ}

/-- **The degreewise square on the induced triples, read back on the degreewise maps on global
sections.** This is `...RelativeProjQcohSheaf.comparisonFamily_toFun` in the opposite direction:
the comparison `L ^⊗ n ≅ L^{⊗ n}` of [Stacks, Tag 01CU] is cancelled on both sides, leaving the
degree-`n` component of `γ` acting on the global sections of the integral tensor powers. -/
theorem Twisting.globalSectionHom_of_comparisonFamily_toFun
    (ψ : Twisting f (situationAlgebra B) (k : ℤ) M)
    (ψ' : Twisting f (situationAlgebra B) (k : ℤ) N) (γ : laurent M ≅ laurent N) (n : ℕ)
    (hsq : ∀ x : B.grading (⊤ : S.Opens) (n * k),
      (comparisonFamily γ n).hom.app ⊤ ((veroneseSections ψ).toFun n x)
        = (veroneseSections ψ').toFun n x)
    (y : ((situationAlgebra B).piece ((n : ℤ) * (k : ℤ))).val.obj
      (op (⊤ : Opens S.toRingedSpace.carrier))) :
    (γ.hom.app (n : ℤ)).val.app (op (⊤ : Opens T.toRingedSpace.carrier))
        (ψ.globalSectionHom (n : ℤ) y)
      = ψ'.globalSectionHom (n : ℤ) y := by
  have ha : ((B.ofGrading ⊤ (n * k) y : B.grading (⊤ : S.Opens) (n * k)) :
      B.sectionRing ⊤) (n * k) = y :=
    DirectSum.of_eq_same (β := B.sectionPieces ⊤) (n * k) y
  have e1 : (veroneseSections ψ).toFun n (B.ofGrading ⊤ (n * k) y)
      = (powCompare M n).inv.app ⊤ (ψ.globalSectionHom (n : ℤ) y) :=
    congrArg (veroneseRaw ψ n) ha
  have e1' : (veroneseSections ψ').toFun n (B.ofGrading ⊤ (n * k) y)
      = (powCompare N n).inv.app ⊤ (ψ'.globalSectionHom (n : ℤ) y) :=
    congrArg (veroneseRaw ψ' n) ha
  refine Function.LeftInverse.injective (powCompare_hom_app_inv_app N n) ?_
  refine Eq.trans ?_ ((hsq (B.ofGrading ⊤ (n * k) y)).trans e1')
  refine Eq.trans ?_ (congrArg (fun z => (comparisonFamily γ n).hom.app ⊤ z) e1).symm
  refine Eq.trans ?_ (comparisonFamily_hom_app γ n
    ((powCompare M n).inv.app ⊤ (ψ.globalSectionHom (n : ℤ) y))).symm
  exact congrArg (fun z => (powCompare N n).inv.app ⊤
      ((γ.hom.app (n : ℤ)).val.app (op (⊤ : Opens T.toRingedSpace.carrier)) z))
    (powCompare_hom_app_inv_app M n (ψ.globalSectionHom (n : ℤ) y)).symm

/-- **The morphism-level identity `ψ ≫ γ = ψ'` from the degreewise squares on the induced
triples**, over an affine base with quasi-coherent homogeneous pieces.

In a nonnegative degree this is `Twisting.globalSectionHom_of_comparisonFamily_toFun` fed to
`Twisting.app_comp_eq_of_globalSectionHom`; in a negative degree the source has no nonzero global
section (`...AffineTripleSections.sections_eq_zero_of_neg`), so both sides vanish and nothing is
asked of `γ`. -/
theorem Twisting.app_comp_eq_of_comparisonFamily_toFun [IsAffine S] (hk : 0 < k)
    (ψ : Twisting f (situationAlgebra B) (k : ℤ) M)
    (ψ' : Twisting f (situationAlgebra B) (k : ℤ) N) (γ : laurent M ≅ laurent N)
    (hsq : ∀ (n : ℕ) (x : B.grading (⊤ : S.Opens) (n * k)),
      (comparisonFamily γ n).hom.app ⊤ ((veroneseSections ψ).toFun n x)
        = (veroneseSections ψ').toFun n x)
    (i : ℤ) : ψ.app i ≫ γ.hom.app i = ψ'.app i := by
  refine Twisting.app_comp_eq_of_globalSectionHom (fun j => B.isQuasicoherent j) γ.hom
    (fun j y => ?_) i
  match j with
  | .ofNat n => exact Twisting.globalSectionHom_of_comparisonFamily_toFun ψ ψ' γ n (hsq n) y
  | .negSucc m =>
      have hy : y = 0 :=
        AffineTripleSections.sections_eq_zero_of_neg B hk (Int.negSucc_lt_zero m) y
      rw [hy, map_zero, map_zero, map_zero]

/-- **Stacks Project, Tag 01NU: two quadruples whose induced triples are compatible with two
pairs of [Stacks, Tag 01N8] over one and the same morphism `T ⟶ U_d` are strictly
equivalent.**

Let `S` be affine, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous pieces (Situation
01NN), `d ≥ 1`, and let `P = (d, f, L, ψ)` and `Q = (d, f, L', ψ')` be quadruples of Section 01NS
over the same morphism `f : T ⟶ S`. If the triples of Section 01N4 they induce are compatible
with pairs `(φ, α)` and `(φ, α')` over **one** morphism `φ : T ⟶ U_d` — which is what the
uniqueness half of [Stacks, Tag 01N8] gives when their classifying morphisms agree — then `P`
and `Q` are strictly equivalent.

This is the **lift to quadruples** of
`...ProjTripleMorphismConverse.sectionsEquiv_of_isCompatible`, which concludes only a strict
equivalence of *triples*. The lift is what the definition of
`...RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent` needs and what a strict equivalence of
triples does not supply: an isomorphism of the **Laurent algebras** of [Stacks, Tag 01CU]
carrying `ψ` to `ψ'` in every *integral* degree. It is `...LaurentAlgebraCongr.laurentCongrIso`
applied to `β = α⁻¹ ∘ α'`, whose degreewise squares on the induced triples are
`toFun_comparisonFamily_laurentCongrIso` and whose morphism-level identity is then
`Twisting.app_comp_eq_of_comparisonFamily_toFun`. The isomorphism `β` of the invertible modules
that the definition also asks for is read off the degree-one component by
`...Quadruple.strictlyEquivalent_iff_exists_hom`. -/
theorem Quadruple.strictlyEquivalent_of_isCompatible [IsAffine S] (hk : 0 < k)
    (P Q : Quadruple f (situationAlgebra B) (k : ℤ))
    (hgenP : ⨆ g : B.grading (⊤ : S.Opens) k, nonvanishingOpen T P.L
      (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections P.twisting) g) = ⊤)
    (hgenQ : ⨆ g : B.grading (⊤ : S.Opens) k, nonvanishingOpen T Q.L
      (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections Q.twisting) g) = ⊤)
    {φ : T ⟶ (degreeOpen (B.grading (⊤ : S.Opens)) k).toScheme}
    {α : pullbackTwist (B.grading (⊤ : S.Opens)) φ (k : ℤ) ≅ P.L}
    {α' : pullbackTwist (B.grading (⊤ : S.Opens)) φ (k : ℤ) ≅ Q.L}
    (hp : IsCompatible (B.grading (⊤ : S.Opens)) (veroneseSections P.twisting) ⟨φ, α⟩)
    (hp' : IsCompatible (B.grading (⊤ : S.Opens)) (veroneseSections Q.twisting) ⟨φ, α'⟩) :
    Quadruple.StrictlyEquivalent P Q :=
  (Quadruple.strictlyEquivalent_iff_exists_hom P Q).mpr
    ⟨laurentCongrIso (α.symm ≪≫ α'),
      Twisting.app_comp_eq_of_comparisonFamily_toFun hk P.twisting Q.twisting
        (laurentCongrIso (α.symm ≪≫ α'))
        (toFun_comparisonFamily_laurentCongrIso (B.grading (⊤ : S.Opens)) hgenP hgenQ hp hp')⟩

end Quadruple

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
