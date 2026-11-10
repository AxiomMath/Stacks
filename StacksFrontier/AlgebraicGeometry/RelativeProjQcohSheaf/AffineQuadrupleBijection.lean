module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineClassifyingRoundTrip
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineQuadrupleConverse

/-!
# The bijection `Mor(T, U_d) = F_d(T)` of [Stacks, Tag 01NU]

Let `S` be an **affine** scheme, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous
pieces (Situation 01NN), `A = Γ(S, 𝒜)` its graded ring of global sections, `d ≥ 1`, `T` a test
scheme and `U_d ⊆ Proj(A)` the open of Equation 27.12.0.1. The two maps of the bijection
[Stacks, Tag 01NU] asserts are
`...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass : F_d(T) → Mor(T, U_d)` and
`...AffineTripleSections.fdOfHom : Mor(T, U_d) → F_d(T)`, and
`...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass_fdOfHom` already says the composite
`Mor(T, U_d) → F_d(T) → Mor(T, U_d)` is the identity.

**This file proves the other composite**, `F_d(T) → Mor(T, U_d) → F_d(T)`, and assembles the two
into the bijection `Quadruple.fdEquiv`.

## The route

Let `P = (d, f, L, ψ)` be a quadruple, `φ` its classifying morphism and `Q` the quadruple
`...AffineTripleSections.quadrupleOfHom` builds from `φ`. Both halves of the comparison are
bookkeeping on statements that are already available.

* The two triples `veroneseSections Q.twisting` and `veroneseSections P.twisting` are carried by
  compatible pairs of [Stacks, Tag 01N8] over **one and the same** morphism `T ⟶ U_d`: take for
  each the pair `...ProjTripleClassifying.classifyingPair` attaches to it, whose first component
  is its classifying morphism by definition. Those two morphisms agree because `Q`'s is `φ`,
  which is `...RelativeProjQcohSheaf.Quadruple.classifyingHom_quadrupleOfHom` — the *first*
  composite. The lift of the resulting strict equivalence of triples to a strict equivalence of
  **quadruples** is `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_of_isCompatible`.
* The two quadruples are *a priori* fibred over different morphisms `T ⟶ S`: `f` for `P` and
  `...AffineTripleSections.structureHom` of the pulled-back universal family for `Q`. They agree
  because `structureHom` only sees a triple's degree-zero component
  (`AffineTripleSections.structureHom_eq_of_toFun_zero_eq`), the degree-zero component is
  unchanged by a strict equivalence of triples
  (`AffineTripleSections.toFun_zero_eq_of_sectionsEquiv`, the zeroth tensor power of an
  isomorphism being the identity of the monoidal unit), and `structureHom` of a quadruple's own
  induced triple is the quadruple's base morphism
  (`...AffineTripleSections.structureHom_veroneseSections`).

`Fd.mk_eq_mk_of_isCompatible` packages the two: it takes the equality of base morphisms and the
two compatible pairs and concludes an equality of classes in `F_d(T)`, the transport being a
`subst` rather than a `...RelativeProjQcohSheaf.Quadruple.congrBase`.

## Main results

* `...RelativeProjQcohSheaf.Quadruple.fdOfHom_classifyingHom`: **the composite
  `F_d(T) → Mor(T, U_d) → F_d(T)` is the identity**, on a quadruple.
* `...RelativeProjQcohSheaf.Quadruple.fdOfHom_classifyingHomOfClass`: the same on classes.
* `...RelativeProjQcohSheaf.Quadruple.fdEquiv`: **the bijection
  `F_d(T) ≃ Mor(T, U_d)` of [Stacks, Tag 01NU]**, for `S` affine and `𝒜` quasi-coherent.

## What is not here

**Naturality in `T`**, and therefore the representability of `F_d` — a
`CategoryTheory.Functor.RepresentableBy` for `...RelativeProjQcohSheaf.Fd.functor` — is not in
this file, and nothing below carries an attribute claiming it. The bijection below is a
bijection of sets for each fixed `T`; that the family of bijections is a natural transformation
needs the identification `F_d = F_d^{triples}` of this directory to be natural, i.e.

`veroneseSections (P.twisting.pullback g)
  = ProjTriplePullback.pullbackSections _ (veroneseSections P.twisting) g`.

That statement is `...RelativeProjQcohSheaf.veroneseSections_pullback` and the representability
it yields is `...RelativeProjQcohSheaf.Fd.representableByDegreeOpen`, both in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineFdRepresentable.lean`, which consumes
this file. Its inputs are the triple-level naturality
(`Stacks.AlgebraicGeometry.ProjClassifyingPullback.classifyingHom_pullbackSections`) and the
**two halves** proved in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineVeroneseNaturality.lean`: that the
pulled-back twisting acts on global sections by pulling back the original action
(`...RelativeProjQcohSheaf.Twisting.globalSectionHom_pullback`), and that the comparison
`L ^⊗ n ≅ L^{⊗ n}` of [Stacks, Tag 01CU] commutes with pullback
(`...RelativeProjQcohSheaf.pullPowCompare_eq_powComparePull`).

Nor is `U_d` here the degree-`d` open of the *relative* `Proj` of
`...RelativeProjQcohSheaf.RelativeProjData`: it is the open of Equation 27.12.0.1 inside
`Proj Γ(S, 𝒜)` for an affine `S`. Turning the bijection below into the one
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ProjDegreeRepresentation.equiv` is stated in —
residue (i) of [Stacks, Tag 01NY] — is a **glueing** problem over the charts rather than a second
representability proof: the chart identification
`P.chart U hU ⁻¹ᵁ P.degreeOpen d = AlgebraicGeometry.Proj.degreeOpen (A.grading U) d` makes the
relative `U_d` a union of opens, one per affine open of the base, each of which *is* an absolute
`U_d`, so what residue (i) still owes is the descent of the unique classifying morphisms across
chart overlaps together with the smallness of `F_d(W)`. For the smallness,
`...RelativeProjQcohSheaf.Fd.small_of_baseCover` reduces the question to the affine-local
subfunctors and `...RelativeProjQcohSheaf.Fd.baseFibreEquiv` of [Stacks, Tag 01NT] turns one of
those into an `F_d` for the restricted algebra, which `Quadruple.fdEquiv` below puts in bijection
with a `Type u` set of morphisms; the brick missing from that composition is the identification of
`...RelativeProjQcohSheaf.baseAlgebra` of the inclusion of an affine open with the
`...RelativeProjQcohSheaf.situationAlgebra` of a restriction of the `SheafGradedAlgebra`.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (pullbackTwist)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (IsCompatible psiSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.ProjTripleStructureMorphism (degreeZeroHom divUnit zeroVeronese)
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

variable {T S : Scheme.{u}} {B : SheafGradedAlgebra S} {k : ℕ} {f : T ⟶ S}

/-! ### The base morphism of a triple sees only its degree-zero component -/

/-- **A strict equivalence of triples does not change the degree-zero component.** The zeroth
tensor power of the isomorphism `β : L ≅ L'` that
`Stacks.AlgebraicGeometry.ProjTripleClassifying.SectionsEquiv` supplies is the identity of the
monoidal unit, and the degree-zero components of the two triples are global sections of that one
object. -/
theorem AffineTripleSections.toFun_zero_eq_of_sectionsEquiv {L L' : T.Modules}
    {χ : VeroneseSections (B.grading (⊤ : S.Opens)) k L}
    {χ' : VeroneseSections (B.grading (⊤ : S.Opens)) k L'}
    (h : Stacks.AlgebraicGeometry.ProjTripleClassifying.SectionsEquiv
      (B.grading (⊤ : S.Opens)) χ χ')
    (a : B.grading (⊤ : S.Opens) (0 * k)) : χ.toFun 0 a = χ'.toFun 0 a := by
  obtain ⟨β, hβ⟩ := h
  refine Eq.trans ?_ (hβ 0 a)
  change χ.toFun 0 a = (Iso.refl (natTensorPow L 0)).hom.app ⊤ (χ.toFun 0 a)
  rw [Iso.refl_hom, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

/-- **The morphism `T ⟶ S` a triple determines over an affine base depends only on the triple's
degree-zero component.** By [Stacks, Tag 01I1] the morphism is determined by its effect on global
sections, which `...AffineTripleSections.structureHom_appTop` reads off the degree-zero ring map
`...ProjTripleStructureMorphism.degreeZeroHom`; and that ring map is the degree-zero component of
the triple divided by the unit section of `L^{⊗ 0}`, which is the structure sheaf whatever `L`
is. -/
theorem AffineTripleSections.structureHom_eq_of_toFun_zero_eq [IsAffine S] {L L' : T.Modules}
    [Stacks.Ample.IsInvertibleModule T L] [Stacks.Ample.IsInvertibleModule T L']
    (χ : VeroneseSections (B.grading (⊤ : S.Opens)) k L)
    (χ' : VeroneseSections (B.grading (⊤ : S.Opens)) k L')
    (hgen : (⨆ g : B.grading (⊤ : S.Opens) k,
      nonvanishingOpen T L (psiSection (B.grading (⊤ : S.Opens)) χ g)) = ⊤)
    (hgen' : (⨆ g : B.grading (⊤ : S.Opens) k,
      nonvanishingOpen T L' (psiSection (B.grading (⊤ : S.Opens)) χ' g)) = ⊤)
    (h0 : ∀ a : B.grading (⊤ : S.Opens) (0 * k), χ.toFun 0 a = χ'.toFun 0 a) :
    AffineTripleSections.structureHom B χ hgen
      = AffineTripleSections.structureHom B χ' hgen' := by
  refine (Stacks.RelativeSpec.affineHomEquiv S T).injective ?_
  change (AffineTripleSections.structureHom B χ hgen).appTop
      = (AffineTripleSections.structureHom B χ' hgen').appTop
  rw [AffineTripleSections.structureHom_appTop, AffineTripleSections.structureHom_appTop]
  refine congrArg (fun θ : (B.grading (⊤ : S.Opens) 0) →+* Γ(T, ⊤) =>
    AffineTripleSections.structureRingHom B ≫ CommRingCat.ofHom θ) (RingHom.ext fun z => ?_)
  change divUnit (χ.toFun 0 (zeroVeronese (B.grading (⊤ : S.Opens)) k z))
      = divUnit (χ'.toFun 0 (zeroVeronese (B.grading (⊤ : S.Opens)) k z))
  exact congrArg (fun x : Γ(natTensorPow L 0, ⊤) => divUnit x) (h0 _)

/-! ### Equality of two classes in `F_d(T)` -/

/-- **Two quadruples over equal base morphisms whose induced triples are carried by compatible
pairs of [Stacks, Tag 01N8] with the same first component have the same class in `F_d(T)`.** The
transport along the equality of base morphisms is a `subst`, after which
`...RelativeProjQcohSheaf.Fd.mk_eq_mk_iff` reduces the goal to strict equivalence and
`...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_of_isCompatible` supplies it. -/
theorem Fd.mk_eq_mk_of_isCompatible [IsAffine S] (hk : 0 < k) {g : T ⟶ S}
    (Q : Quadruple g (situationAlgebra B) (k : ℤ))
    (P : Quadruple f (situationAlgebra B) (k : ℤ)) (hbase : g = f)
    (hgenQ : ⨆ b : B.grading (⊤ : S.Opens) k, nonvanishingOpen T Q.L
      (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections Q.twisting) b) = ⊤)
    (hgenP : ⨆ b : B.grading (⊤ : S.Opens) k, nonvanishingOpen T P.L
      (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections P.twisting) b) = ⊤)
    {φ φ' : T ⟶ (degreeOpen (B.grading (⊤ : S.Opens)) k).toScheme}
    {α : pullbackTwist (B.grading (⊤ : S.Opens)) φ (k : ℤ) ≅ Q.L}
    {α' : pullbackTwist (B.grading (⊤ : S.Opens)) φ' (k : ℤ) ≅ P.L}
    (hp : IsCompatible (B.grading (⊤ : S.Opens)) (veroneseSections Q.twisting) ⟨φ, α⟩)
    (hp' : IsCompatible (B.grading (⊤ : S.Opens)) (veroneseSections P.twisting) ⟨φ', α'⟩)
    (hfst : φ = φ') : Fd.mk g Q = Fd.mk f P := by
  subst hbase
  obtain rfl : φ = φ' := hfst
  exact (Fd.mk_eq_mk_iff Q P).mpr
    (Quadruple.strictlyEquivalent_of_isCompatible hk Q P hgenQ hgenP hp hp')

/-! ### The second composite, and the bijection -/

/-- **Stacks Project, Tag 01NU: the composite `F_d(T) → Mor(T, U_d) → F_d(T)` is the identity.**
Let `S` be affine, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous pieces (Situation
01NN), `d ≥ 1`, `A = Γ(S, 𝒜)` and `U_d ⊆ Proj(A)` the open of Equation 27.12.0.1. For a quadruple
`P` of Section 01NS over `f : T ⟶ S`, pulling the universal family of [Stacks, Tag 01N9] back
along `P`'s classifying morphism and rebuilding a quadruple returns `P`'s own class in `F_d(T)`.

Two steps, both of them bookkeeping. The pulled-back family and the triple `P` induces are
carried by the compatible pairs of [Stacks, Tag 01N8] attached to them, whose first components
agree by `Quadruple.classifyingHom_quadrupleOfHom` — the first composite — so
`Quadruple.strictlyEquivalent_of_isCompatible` makes the two quadruples strictly equivalent; and
their base morphisms agree because `...AffineTripleSections.structureHom` sees only a triple's
degree-zero component, which a strict equivalence of triples leaves alone. -/
theorem Quadruple.fdOfHom_classifyingHom [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (P : Quadruple f (situationAlgebra B) (k : ℤ)) :
    AffineTripleSections.fdOfHom B (Quadruple.classifyingHom hk hqc P) hk = Fd.mk f P := by
  set φ := Quadruple.classifyingHom hk hqc P with hφ
  set Q := AffineTripleSections.quadrupleOfHom B φ hk with hQ
  have hgenQ := Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc Q
  have hgenP := Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc P
  have hcQ := Stacks.AlgebraicGeometry.ProjTripleClassifying.isCompatible_classifyingPair
    (B.grading (⊤ : S.Opens)) hk (veroneseSections Q.twisting) hgenQ
  have hcP := Stacks.AlgebraicGeometry.ProjTripleClassifying.isCompatible_classifyingPair
    (B.grading (⊤ : S.Opens)) hk (veroneseSections P.twisting) hgenP
  have hfst : Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
        (B.grading (⊤ : S.Opens)) hk (veroneseSections Q.twisting) hgenQ
      = Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
        (B.grading (⊤ : S.Opens)) hk (veroneseSections P.twisting) hgenP :=
    Quadruple.classifyingHom_quadrupleOfHom hk hqc φ
  have hequiv := Stacks.AlgebraicGeometry.ProjTripleMorphismConverse.sectionsEquiv_of_fst_eq
    (B.grading (⊤ : S.Opens)) hgenQ hgenP hcQ hcP hfst
  have hbase : AffineTripleSections.structureHom B
        (AffineTripleSections.pullbackUniversalSections B φ)
        (AffineTripleSections.iSup_nonvanishingOpen_pullbackUniversalSections B φ) = f :=
    ((AffineTripleSections.structureHom_veroneseSections Q.twisting hgenQ).symm.trans
      (AffineTripleSections.structureHom_eq_of_toFun_zero_eq
        (veroneseSections Q.twisting) (veroneseSections P.twisting) hgenQ hgenP
        (AffineTripleSections.toFun_zero_eq_of_sectionsEquiv hequiv))).trans
      (AffineTripleSections.structureHom_veroneseSections P.twisting hgenP)
  exact Fd.mk_eq_mk_of_isCompatible hk Q P hbase hgenQ hgenP hcQ hcP hfst

/-- **Stacks Project, Tag 01NU: the composite `F_d(T) → Mor(T, U_d) → F_d(T)` is the identity**,
read on strict equivalence classes. This is `Quadruple.fdOfHom_classifyingHom` on the quotient,
on which `...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass` is `Quotient.lift` of
`...RelativeProjQcohSheaf.Quadruple.classifyingHom`. -/
theorem Quadruple.fdOfHom_classifyingHomOfClass [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (ξ : Fd (situationAlgebra B) (k : ℤ) T) :
    AffineTripleSections.fdOfHom B (Quadruple.classifyingHomOfClass hk hqc ξ.2) hk = ξ := by
  obtain ⟨g, q⟩ := ξ
  induction q using Quotient.ind with
  | _ P => exact Quadruple.fdOfHom_classifyingHom hk hqc P

/-- **Stacks Project, Tag 01NU: the bijection `F_d(T) = Mor(T, U_d)`.** Let `S` be affine, `𝒜` a
graded `𝒪_S`-algebra with quasi-coherent homogeneous pieces (Situation 01NN), `d ≥ 1`,
`A = Γ(S, 𝒜)` and `U_d ⊆ Proj(A)` the open of Equation 27.12.0.1. The set `F_d(T)` of strict
equivalence classes of quadruples of Section 01NS over a test scheme `T` is in bijection with
the morphisms `T ⟶ U_d`.

The two maps are `...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass` and
`...AffineTripleSections.fdOfHom`, and the two composites are
`...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass_fdOfHom` and
`Quadruple.fdOfHom_classifyingHomOfClass`.

This is a bijection of sets for each fixed `T`; **no naturality in `T` is claimed here**, so
this is not by itself the representability of `F_d` that the tag asserts. The naturality, and
the `CategoryTheory.Functor.RepresentableBy` these bijections assemble into, is
`...RelativeProjQcohSheaf.Fd.representableByDegreeOpen` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineFdRepresentable.lean`. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   The same bijection carried to the relative U_d is Quadruple.fdEquivDegreeOpen of
--   AffineRelativeDegreeOpen, and its descent along the charts to a general base residue (i) of
--   Tag 01NY, which the tag itself does not claim is Fd.degreeOpenEquiv of ChartDegreeOpenEquiv
def Quadruple.fdEquiv [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent) :
    Fd (situationAlgebra B) (k : ℤ) T
      ≃ (T ⟶ (degreeOpen (B.grading (⊤ : S.Opens)) k).toScheme) where
  toFun ξ := Quadruple.classifyingHomOfClass hk hqc ξ.2
  invFun φ := AffineTripleSections.fdOfHom B φ hk
  left_inv ξ := Quadruple.fdOfHom_classifyingHomOfClass hk hqc ξ
  right_inv φ := Quadruple.classifyingHomOfClass_fdOfHom hk hqc φ

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
