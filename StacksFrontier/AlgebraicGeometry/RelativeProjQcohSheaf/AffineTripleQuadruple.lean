module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTriplePullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections
public import StacksFrontier.AlgebraicGeometry.TwistTensor.UniversalVeroneseSections

/-!
# From a triple over an affine base to a quadruple

Let `S` be an **affine** scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN),
`A = Γ(S, 𝒜)` its graded ring of global sections, `d ≥ 1`, `T` a test scheme and `L` an invertible
`𝒪_T`-module. A *triple* of Section 01N4 over `T` is such an `L` together with a graded map
`ψ : A^{(d)} ⟶ Γ_*(T, L)` whose degree-`d` values generate `L`; a *quadruple* of Section 01NS is
a morphism `f : T ⟶ S`, an invertible `L` and a homomorphism of sheaves of graded algebras
`f^*𝒜^{(d)} ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` whose degree-one component is surjective.

The twisting `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.twisting`
assembled from a triple, together with the generation condition of the triple re-indexed by the
global sections of `𝒜_d`, is a quadruple: this is the triples-to-quadruples direction of
[Stacks, Tag 01NU].

A morphism `φ : T ⟶ U_d` into the open `U_d ⊆ Proj A` of Equation 27.12.0.1 pulls the universal
family of [Stacks, Tag 01N9] back to a triple over `T`; composing with the above gives the map
`Mor(T, U_d) → F_d(T)`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.quadruple`: the quadruple
  of Section 01NS attached to a triple of Section 01N4 over an affine base.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.quadrupleOfHom` and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.fdOfHom`: the quadruple, and
  its class in `F_d(T)`, attached to a morphism `T ⟶ U_d`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.veroneseSections_twisting`:
  the graded map on sections that the twisting assembled from a triple induces is `ψ` again.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.globalSectionHom_twisting`:
  the degreewise maps on global sections of the assembled twisting are those of the triple.
* `AffineTripleSections.iSup_nonvanishingOpen_degreeOneSectionHom_eq_top`: the degree-one sections
  of the assembled twisting generate `L`.

## Implementation notes

`L` is bound at the spelling `SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf
T.toRingedSpace)` rather than `AlgebraicGeometry.Scheme.Modules T`. The two are the same type by
`rfl`, but `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent` is stated at the first and
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections` at the second, and a statement
mixing them is not type-correct at the transparency `rw` uses.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare powCompare_inv_app_hom_app)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (psiSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {T S : Scheme.{u}} (B : SheafGradedAlgebra S) {d : ℕ}
  {L : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf T.toRingedSpace)}
  [Stacks.Ample.IsInvertibleModule T L]
  (ψ : VeroneseSections (B.grading (⊤ : S.Opens)) d L)
  (hgen : (⨆ g : B.grading (⊤ : S.Opens) d,
    nonvanishingOpen T L (psiSection (B.grading (⊤ : S.Opens)) ψ g)) = ⊤)

/-! ### The degreewise maps of the assembled twisting -/

/-- **Restricting a section of `L^{⊗ i}` along `f⁻¹⊤ = ⊤` does nothing.** -/
theorem restrict_preimage_top (f : T ⟶ S) (i : ℤ)
    (z : Γ((laurent L).piece i,
      (RingedSpaceModuleAdjunction.opensMap (ringedSpaceHom f)).obj
        (⊤ : Opens S.toRingedSpace.carrier))) :
    ((laurent L).piece i).val.restrictₛₗ
        (eqToHom (congrArg op (Twisting.preimage_top f))) z = z :=
  (PresheafOfModules.restrictₛₗ_apply ((laurent L).piece i).val _ z).trans
    (ConcreteCategory.congr_hom
      (((laurent L).piece i).val.map_id (op (⊤ : Opens T.toRingedSpace.carrier))) z)

/-- **The twisting assembled from a triple induces, on global sections, exactly the degreewise
maps of the triple.** The degree-`i` component of the transposed map
`A^{(d)} ⟶ Γ_*(T, L)` of Section 01N4 attached to
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.twisting` is the family
`sectionsMapInt` that twisting was built from. -/
theorem globalSectionHom_twisting [IsAffine S] (hd : 0 < d) (i : ℤ)
    (x : Γ(AffineTwisting.pieceMod (situationAlgebra B) (i * (d : ℤ)), ⊤)) :
    Twisting.globalSectionHom (twisting B ψ hgen hd) i x
      = sectionsMapInt B ψ hgen i x := by
  show ((laurent L).piece i).val.restrictₛₗ
      (eqToHom (congrArg op (Twisting.preimage_top (structureHom B ψ hgen))))
      (Twisting.sectionHom (twisting B ψ hgen hd) i
        (op (⊤ : Opens S.toRingedSpace.carrier)) x) = _
  exact (congrArg (((laurent L).piece i).val.restrictₛₗ
        (eqToHom (congrArg op (Twisting.preimage_top (structureHom B ψ hgen)))))
      (twisting_app_pullbackUnit B ψ hgen hd i x)).trans
    (restrict_preimage_top (structureHom B ψ hgen) i _)

/-- **The Veronese family of the assembled twisting, degreewise, is the triple's own `ψ`.** -/
theorem veroneseRaw_twisting [IsAffine S] (hd : 0 < d) (n : ℕ)
    (x : B.sectionPieces ⊤ (n * d)) :
    veroneseRaw (twisting B ψ hgen hd) n x = ψ.toFun n (B.ofGrading ⊤ (n * d) x) :=
  (congrArg (fun z => (powCompare L n).inv.app ⊤ z)
      (globalSectionHom_twisting B ψ hgen hd (n : ℤ) x)).trans
    (powCompare_inv_app_hom_app L n _)

omit [Stacks.Ample.IsInvertibleModule T L] in
private theorem veroneseSections_ext
    {X Y : VeroneseSections (B.grading (⊤ : S.Opens)) d L}
    (h : ∀ n, X.toFun n = Y.toFun n) : X = Y := by
  cases X with
  | mk tx hx =>
    cases Y with
    | mk ty hy =>
      have htx : tx = ty := funext h
      subst htx
      rfl

/-- **Stacks Project, Tag 01NU: the passage from a triple to a twisting and back is the
identity.** For an affine base the twisting assembled from a triple `(d, L, ψ)` of Section 01N4
induces, on the graded ring `A = Γ(S, 𝒜)` of Situation 01NN, the very map `ψ` it was built from. -/
theorem veroneseSections_twisting [IsAffine S] (hd : 0 < d) :
    veroneseSections (twisting B ψ hgen hd) = ψ :=
  veroneseSections_ext B fun n => AddMonoidHom.ext fun a =>
    (veroneseRaw_twisting B ψ hgen hd n ((a : B.sectionRing ⊤) (n * d))).trans
      (congrArg (ψ.toFun n) (Subtype.ext (B.of_component (⊤ : S.Opens) a)))

/-! ### Generation, and the quadruple -/

/-- **The nonvanishing open of a degree-one section of the assembled twisting is the nonvanishing
open of the corresponding value of the triple.** -/
theorem nonvanishingOpen_degreeOneSectionHom_twisting [IsAffine S] (hd : 0 < d)
    (b : B.sectionPieces ⊤ d) :
    nonvanishingOpen T L (psiSection (B.grading (⊤ : S.Opens)) ψ (B.ofGrading ⊤ d b))
      = nonvanishingOpen T L (Twisting.degreeOneSectionHom (twisting B ψ hgen hd) b) :=
  (congrArg (fun χ : VeroneseSections (B.grading (⊤ : S.Opens)) d L =>
      nonvanishingOpen T L (psiSection (B.grading (⊤ : S.Opens)) χ (B.ofGrading ⊤ d b)))
    (veroneseSections_twisting B ψ hgen hd).symm).trans
    (nonvanishingOpen_psiSection_veroneseSections (twisting B ψ hgen hd) b)

/-- **The degree-one sections of the assembled twisting generate `L`**: the nonvanishing opens of
`Twisting.degreeOneSectionHom` at the global sections of `𝒜_d` cover `T`. -/
theorem iSup_nonvanishingOpen_degreeOneSectionHom_eq_top [IsAffine S] (hd : 0 < d) :
    (⨆ b : ((situationAlgebra B).piece ((d : ℕ) : ℤ)).val.obj
        (op (⊤ : Opens S.toRingedSpace.carrier)),
      nonvanishingOpen T L
        (Twisting.degreeOneSectionHom (twisting B ψ hgen hd) b)) = ⊤ :=
  top_unique (le_of_eq_of_le hgen.symm (iSup_le fun g =>
    le_iSup_of_le ((g : B.sectionRing ⊤) d) (le_of_eq
      (Eq.trans
        (congrArg (fun z => nonvanishingOpen T L (psiSection (B.grading (⊤ : S.Opens)) ψ z))
          (Subtype.ext (B.of_component (⊤ : S.Opens) g)).symm)
        (nonvanishingOpen_degreeOneSectionHom_twisting B ψ hgen hd
          ((g : B.sectionRing ⊤) d))))))

/-- **Stacks Project, Tag 01NU: the quadruple of Section 01NS attached to a triple of Section
01N4 over an affine base.** Let `S` be affine, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent
homogeneous pieces (Situation 01NN), `d > 0`, and let `(d, L, ψ)` be a triple over a test scheme
`T` for the graded ring `A = Γ(S, 𝒜)`. Then `T` acquires a morphism `f : T ⟶ S` — the one the
degree-zero ring map of `ψ` determines — and `(d, f, L, ψ̃)` is a quadruple: the twisting `ψ̃` is
`AffineTripleSections.twisting`, and its degree-one component is surjective because the sections
`ψ(a)` generate `L`. -/
def quadruple [IsAffine S] (hd : 0 < d) :
    Quadruple (structureHom B ψ hgen) (situationAlgebra B) (d : ℤ) :=
  AffineTwisting.quadrupleOfTwisting (structureHom B ψ hgen) (situationAlgebra B) (d : ℤ) L
    (twisting B ψ hgen hd) (iSup_nonvanishingOpen_degreeOneSectionHom_eq_top B ψ hgen hd)

/-- The invertible module of the quadruple of a triple is the triple's own `L`. -/
@[simp]
theorem quadruple_L [IsAffine S] (hd : 0 < d) : (quadruple B ψ hgen hd).L = L := rfl

/-- The twisting of the quadruple of a triple is the twisting assembled from the triple. -/
@[simp]
theorem quadruple_twisting [IsAffine S] (hd : 0 < d) :
    (quadruple B ψ hgen hd).twisting = twisting B ψ hgen hd := rfl

/-! ### A quadruple out of a morphism into `U_d` -/

section OfHom

open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents (universalTwist)
open Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple (universalVeroneseSections
  iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top)
open Stacks.AlgebraicGeometry.ProjTriplePullback (pullbackSections
  iSup_nonvanishingOpen_pullbackSections)

variable (φ : T ⟶ (degreeOpen (B.grading (⊤ : S.Opens)) d).toScheme)

/-- **The triple a morphism `φ : T ⟶ U_d` induces**: the pullback along `φ` of the universal
family `(d, 𝒪_{U_d}(d), ψ^d)` of [Stacks, Tag 01N9]. -/
def pullbackUniversalSections :
    VeroneseSections (B.grading (⊤ : S.Opens)) d
      ((Scheme.Modules.pullback φ).obj (universalTwist (B.grading (⊤ : S.Opens)) d)) :=
  pullbackSections (B.grading (⊤ : S.Opens))
    (universalVeroneseSections (B.grading (⊤ : S.Opens)) d) φ

/-- **The pulled-back universal family generates `φ^*𝒪_{U_d}(d)`**: the nonvanishing opens of its
degree-`d` values cover `T`. -/
theorem iSup_nonvanishingOpen_pullbackUniversalSections :
    (⨆ f : B.grading (⊤ : S.Opens) d,
      nonvanishingOpen T
        ((Scheme.Modules.pullback φ).obj (universalTwist (B.grading (⊤ : S.Opens)) d))
        (psiSection (B.grading (⊤ : S.Opens)) (pullbackUniversalSections B φ) f)) = ⊤ :=
  iSup_nonvanishingOpen_pullbackSections (B.grading (⊤ : S.Opens))
    (universalVeroneseSections (B.grading (⊤ : S.Opens)) d) φ
    (iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top
      (B.grading (⊤ : S.Opens)) d)

/-- **Stacks Project, Tag 01NU: the quadruple a morphism `T ⟶ U_d` gives rise to.** Let `S` be
affine, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous pieces (Situation 01NN),
`d > 0`, `A = Γ(S, 𝒜)` and `U_d ⊆ Proj(A)` the open of Equation 27.12.0.1. A morphism
`φ : T ⟶ U_d` pulls the universal family of [Stacks, Tag 01N9] back to a triple
`(d, φ^*𝒪_{U_d}(d), φ^*ψ^d)` over `T`, and `quadruple` turns that triple into a quadruple of
Section 01NS, over the morphism `T ⟶ S` the triple's own degree-zero ring map determines. -/
def quadrupleOfHom [IsAffine S] (hd : 0 < d) :
    Quadruple (structureHom B (pullbackUniversalSections B φ)
        (iSup_nonvanishingOpen_pullbackUniversalSections B φ)) (situationAlgebra B) (d : ℤ) :=
  quadruple B (pullbackUniversalSections B φ)
    (iSup_nonvanishingOpen_pullbackUniversalSections B φ) hd

/-- **The class in `F_d(T)` of the quadruple a morphism `T ⟶ U_d` gives rise to**, i.e. the value
at `φ` of the map `Mor(T, U_d) → F_d(T)`. -/
def fdOfHom [IsAffine S] (hd : 0 < d) : Fd (situationAlgebra B) (d : ℤ) T :=
  Fd.mk _ (quadrupleOfHom B φ hd)

/-- The morphism to `S` recorded by the class of a morphism `T ⟶ U_d` is the one the pulled-back
universal family's degree-zero ring map determines. -/
@[simp]
theorem fdOfHom_fst [IsAffine S] (hd : 0 < d) :
    (fdOfHom B φ hd).1 = structureHom B (pullbackUniversalSections B φ)
      (iSup_nonvanishingOpen_pullbackUniversalSections B φ) := rfl

end OfHom

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections

end
