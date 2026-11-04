module

public import StacksFrontier.AlgebraicGeometry.Constructions.CoherentMulSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpenRepresents
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineGeneration
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TripleComparisonSectionRing

/-!
# A quadruple over an affine base, as a triple over the graded ring of sections

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN) and fix `d > 0`. Section 01NS
attaches to a test scheme `T` the quadruples `(d, g : T → S, L, ψ)`, and [Stacks, Tag 01NU] says
that for `S` affine the functor `F_d` of their strict equivalence classes is representable by the
open `U_d ⊆ Proj(A)`, `A = Γ(S, 𝒜)`; its proof identifies `F_d` with the functor of *triples* of
Section 01N4, for which `U_d` represents the analogous functor by [Stacks, Tag 01N9].

To the twisting of a quadruple this file attaches a triple over the graded ring `A = Γ(S, 𝒜)`,
presented with its internal `ℕ`-grading
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.grading`: its degreewise maps are
those of `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.globalSectionHom`, read on the
iterated tensor powers `L ^⊗ n` through the comparison
`Stacks.AlgebraicGeometry.CoherentMulSections.powCompare` with the integral tensor powers of
[Stacks, Tag 01CU]. For `S` affine and `𝒜` quasi-coherent, the degree-`d` values of this triple
generate `L`, so every quadruple over an affine base has exactly one classifying morphism
`T ⟶ U_d`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.veroneseRaw`: the degree-`n` value of the
  transposed map, read on the iterated tensor power `L ^⊗ n`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.veroneseSections`: the datum `ψ` of a triple
  of Section 01N4 attached to the twisting of a quadruple, on the graded ring `A = Γ(S, 𝒜)`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.onePowIso`: the identification
  `L^{⊗ 1} ≅ L` of [Stacks, Tag 01CU] over `AlgebraicGeometry.Scheme.Modules`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.mulSections_veroneseRaw`: the family is
  multiplicative across degrees for the product
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections` of sections of iterated tensor powers.
* `RelativeProjQcohSheaf.Quadruple.iSup_nonvanishingOpen_psiSection_eq_top`: over an affine base,
  the degree-`d` values of the triple attached to a quadruple generate `L`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.existsUnique_hom_toDegreeOpen`: the
  unique classifying morphism `T ⟶ U_d` of a quadruple over an affine base.

## Implementation notes

A triple's `ψ` is indexed by a family of subgroups `𝒜 : ℕ → σ` with `[GradedRing 𝒜]`, while the
sheaf side offers the summand types
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionPieces`;
`SheafGradedAlgebra.grading` is the family of ranges of the summand inclusions, and
`of_component` passes between a subgroup element and its summand.

`Nat.cast (k * d) = (k : ℤ) * (d : ℤ)` and `Nat.cast (k + l) = (k : ℤ) + (l : ℤ)` hold
definitionally; the one transport needed is the `eqToHom` along `kd + ld = (k + l)d` that
`Twisting.globalSectionHom_mul` carries, handled by `eqToHom_piece_app_eq`.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.CoherentMulSections
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {T S : Scheme.{u}} {f : T ⟶ S} {B : SheafGradedAlgebra S} {d : ℕ}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]

/-! ### Degree bookkeeping in the graded ring of sections -/

/-- The degree-`n` summand inclusion of the degree-`n` component of an element of the degree-`n`
part of the section ring returns that element. -/
theorem of_component {n : ℕ} (a : B.grading (⊤ : S.Opens) n) :
    DirectSum.of (B.sectionPieces ⊤) n ((a : B.sectionRing ⊤) n) = (a : B.sectionRing ⊤) := by
  obtain ⟨y, hy⟩ := a.2
  rw [← hy, DirectSum.of_eq_same]

/-- Reindexing a summand inclusion along an equality of degrees: the degree-`i` inclusion of a
homogeneous section is the degree-`j` inclusion of its degree-`j` component. -/
theorem of_eq_of_apply {i j : ℕ} (hij : i = j) (w : B.sectionPieces ⊤ i) :
    DirectSum.of (B.sectionPieces ⊤) i w
      = DirectSum.of (B.sectionPieces ⊤) j (DirectSum.of (B.sectionPieces ⊤) i w j) := by
  subst hij
  rw [DirectSum.of_eq_same]

/-- **The transport of a homogeneous section along an equality of degrees, on sections over `S`.**
If the degree-`i` summand inclusion of `w` agrees with the degree-`j` summand inclusion of `z`,
then the transport of `w` to degree `j` is `z`. -/
theorem eqToHom_piece_app_eq {i j : ℕ} (hij : i = j)
    (p : (situationAlgebra B).piece ((i : ℕ) : ℤ)
      = (situationAlgebra B).piece ((j : ℕ) : ℤ))
    (w : B.sectionPieces ⊤ i) (z : B.sectionPieces ⊤ j)
    (hz : DirectSum.of (B.sectionPieces ⊤) i w = DirectSum.of (B.sectionPieces ⊤) j z) :
    (eqToHom p).val.app (op (⊤ : Opens S.toRingedSpace.carrier)) w = z := by
  subst hij
  have hw : w = z := by
    have h := congrArg (fun u : B.sectionRing ⊤ => u i) hz
    simpa using h
  subst hw
  rw [eqToHom_refl]
  rfl

/-! ### The Veronese family of sections of a twisting -/

/-- **The degree-`n` value of the map `A^{(d)} ⟶ Γ_*(T, L)` of Section 01N4 attached to a
twisting**, `A = Γ(S, 𝒜)`, read on the *iterated* tensor power `L ^⊗ n`: the transposed map
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.sectionRingHom` on sections, followed by the
inverse of the comparison `L ^⊗ n ≅ L^{⊗ n}` of [Stacks, Tag 01CU]. -/
def veroneseRaw (ψ : Twisting f (situationAlgebra B) (d : ℤ) L) (n : ℕ)
    (x : B.sectionPieces ⊤ (n * d)) : Γ(natTensorPow L n, ⊤) :=
  (powCompare L n).inv.app ⊤ (sectionRingHom ψ n x)

/-- `veroneseRaw` as an additive map. -/
def veroneseRawHom (ψ : Twisting f (situationAlgebra B) (d : ℤ) L) (n : ℕ) :
    B.sectionPieces ⊤ (n * d) →+ Γ(natTensorPow L n, ⊤) :=
  AddMonoidHom.mk' (veroneseRaw ψ n) fun x y =>
    (congrArg (fun z => (powCompare L n).inv.app ⊤ z)
      (map_add (sectionRingHom ψ n) x y)).trans (map_add _ _ _)

/-- **The Veronese family is multiplicative across degrees.** The product
`Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections` of the values on `x` and `y` is the
value on any homogeneous section `z` of degree `(n + m)d` whose summand inclusion agrees with
that of the graded product of `x` and `y`. -/
theorem mulSections_veroneseRaw (ψ : Twisting f (situationAlgebra B) (d : ℤ) L) (n m : ℕ)
    (x : B.sectionPieces ⊤ (n * d)) (y : B.sectionPieces ⊤ (m * d))
    (z : B.sectionPieces ⊤ ((n + m) * d))
    (hz : DirectSum.of (B.sectionPieces ⊤) (n * d + m * d)
          (GradedMonoid.GMul.mul x y)
        = DirectSum.of (B.sectionPieces ⊤) ((n + m) * d) z) :
    mulSections L (veroneseRaw ψ n x) (veroneseRaw ψ m y) = veroneseRaw ψ (n + m) z := by
  have key : (eqToHom (congrArg (situationAlgebra B).piece
        (by ring : (n : ℤ) * (d : ℤ) + (m : ℤ) * (d : ℤ)
          = ((n : ℤ) + (m : ℤ)) * (d : ℤ)))).val.app
      (op (⊤ : Opens S.toRingedSpace.carrier))
      (((situationAlgebra B).mul ((n : ℤ) * (d : ℤ)) ((m : ℤ) * (d : ℤ))).app
        (op (⊤ : Opens S.toRingedSpace.carrier)) x y) = z :=
    eqToHom_piece_app_eq ((add_mul n m d).symm) _ _ z hz
  refine (mulSections_mulBilinear L n m (sectionRingHom ψ n x) (sectionRingHom ψ m y)).trans ?_
  exact congrArg (fun w => (powCompare L (n + m)).inv.app ⊤ w)
    ((ψ.globalSectionHom_mul (n : ℤ) (m : ℤ) x y).trans
      (congrArg (fun w => ψ.globalSectionHom ((n : ℤ) + (m : ℤ)) w) key))

/-- **Stacks Project, Tag 01NU: the datum `ψ` of a triple of Section 01N4 attached to the
twisting of a quadruple.** It is the degreewise family `A_{nd} →+ Γ(L ^⊗ n, ⊤)` that the twisting
induces on the graded ring `A = Γ(S, 𝒜)` of Situation 01NN, with its internal `ℕ`-grading. -/
def veroneseSections (ψ : Twisting f (situationAlgebra B) (d : ℤ) L) :
    VeroneseSections (B.grading (⊤ : S.Opens)) d L where
  toFun n := AddMonoidHom.mk'
    (fun a => veroneseRaw ψ n ((a : B.sectionRing ⊤) (n * d)))
    fun a b => map_add (veroneseRawHom ψ n) ((a : B.sectionRing ⊤) (n * d))
      ((b : B.sectionRing ⊤) (n * d))
  map_mul n m a b ab hab := by
    have ha := of_component a
    have hb := of_component b
    have hab' : DirectSum.of (B.sectionPieces ⊤) (n * d + m * d)
          (GradedMonoid.GMul.mul ((a : B.sectionRing ⊤) (n * d))
            ((b : B.sectionRing ⊤) (m * d)))
        = (ab : B.sectionRing ⊤) :=
      (DirectSum.of_mul_of _ _).symm.trans
        (((congrArg (fun u : B.sectionRing ⊤ =>
              u * DirectSum.of (B.sectionPieces ⊤) (m * d)
                ((b : B.sectionRing ⊤) (m * d))) ha).trans
          (congrArg (fun v : B.sectionRing ⊤ => (a : B.sectionRing ⊤) * v) hb)).trans hab.symm)
    have hz := (of_eq_of_apply ((add_mul n m d).symm)
        (GradedMonoid.GMul.mul ((a : B.sectionRing ⊤) (n * d))
          ((b : B.sectionRing ⊤) (m * d)))).trans
      (congrArg (fun u : B.sectionRing ⊤ =>
        DirectSum.of (B.sectionPieces ⊤) ((n + m) * d) (u ((n + m) * d))) hab')
    exact (mulSections_veroneseRaw ψ n m _ _ _ hz).symm

/-! ### The degree-one value -/

/-- The first integral tensor power `L^{⊗ 1}` of [Stacks, Tag 01CU], read as an object of
`AlgebraicGeometry.Scheme.Modules`. -/
def onePowModule (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L] : T.Modules :=
  (laurent L).piece 1

/-- **`L^{⊗ 1} ≅ L`** of [Stacks, Tag 01CU], read over `AlgebraicGeometry.Scheme.Modules`. -/
def onePowIso (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L] : onePowModule L ≅ L :=
  letI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    T.toRingedSpace.presheaf (isSheafStruct T) L
  Stacks.SheafOfModules.TensorPower.tensorPowerOneIso T.toRingedSpace.presheaf
    (isSheafStruct T) L

/-- The degree-one value of the transposed map on a global section of `𝒜_d`, before the
identification `L^{⊗ 1} ≅ L`. -/
def degreeOneLaurentSection (ψ : Twisting f (situationAlgebra B) (d : ℤ) L)
    (b : B.sectionPieces ⊤ d) : Γ(onePowModule L, ⊤) :=
  ψ.globalSectionHom 1 ((eqToHom (congrArg (situationAlgebra B).piece
    (one_mul ((d : ℕ) : ℤ)).symm)).val.app (op (⊤ : Opens S.toRingedSpace.carrier)) b)

/-- `Twisting.degreeOneSectionHom` is that section read through `L^{⊗ 1} ≅ L`. -/
theorem onePowIso_hom_app_degreeOneLaurentSection
    (ψ : Twisting f (situationAlgebra B) (d : ℤ) L) (b : B.sectionPieces ⊤ d) :
    (onePowIso L).hom.app ⊤ (degreeOneLaurentSection ψ b) = ψ.degreeOneSectionHom b := rfl

/-- **The degree-one value of the Veronese family is the degree-one value of the transposed
map**, read across the comparison `L ^⊗ 1 ≅ L^{⊗ 1}` of [Stacks, Tag 01CU]. -/
theorem pow_veroneseSections_one (ψ : Twisting f (situationAlgebra B) (d : ℤ) L)
    {a : B.grading (⊤ : S.Opens) d} (b : B.sectionPieces ⊤ d)
    (hab : (a : B.sectionRing ⊤) = DirectSum.of (B.sectionPieces ⊤) d b) :
    (veroneseSections ψ).pow a.2 1
      = (powCompare L 1).inv.app ⊤ (degreeOneLaurentSection ψ b) := by
  have hq : DirectSum.of (B.sectionPieces ⊤) d b (1 * d)
      = (eqToHom (congrArg (situationAlgebra B).piece
          (one_mul ((d : ℕ) : ℤ)).symm)).val.app
            (op (⊤ : Opens S.toRingedSpace.carrier)) b :=
    (eqToHom_piece_app_eq ((one_mul d).symm) _ b _
      (of_eq_of_apply ((one_mul d).symm) b)).symm
  show veroneseRaw ψ 1 (((a : B.sectionRing ⊤) ^ 1) (1 * d))
      = veroneseRaw ψ 1 ((eqToHom (congrArg (situationAlgebra B).piece
          (one_mul ((d : ℕ) : ℤ)).symm)).val.app
            (op (⊤ : Opens S.toRingedSpace.carrier)) b)
  exact congrArg (fun w : B.sectionPieces ⊤ (1 * d) => veroneseRaw ψ 1 w)
    ((congrArg (fun u : B.sectionRing ⊤ => u (1 * d))
      ((congrArg (fun u : B.sectionRing ⊤ => u ^ 1) hab).trans
        (pow_one (DirectSum.of (B.sectionPieces ⊤) d b)))).trans hq)

/-! ### Generation, and the classifying morphism over an affine base -/

/-- **The nonvanishing open of a degree-one value of the Veronese family is that of the
corresponding degree-one section of the twisting.** -/
theorem nonvanishingOpen_psiSection_veroneseSections
    (ψ : Twisting f (situationAlgebra B) (d : ℤ) L) (b : B.sectionPieces ⊤ d) :
    nonvanishingOpen T L (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections ψ)
        ⟨DirectSum.of (B.sectionPieces ⊤) d b, B.of_mem_grading (⊤ : S.Opens) b⟩)
      = nonvanishingOpen T L (ψ.degreeOneSectionHom b) := by
  rw [nonvanishingOpen_psiSection, pow_veroneseSections_one ψ b rfl,
    ← onePowIso_hom_app_degreeOneLaurentSection ψ b]
  refine Opens.ext ?_
  rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen,
    Stacks.NonvanishingOpen.coe_nonvanishingOpen,
    Stacks.Ample.nonvanishingLocus_congr (onePowIso L) _]
  exact Stacks.Ample.nonvanishingLocus_congr (powCompare L 1).symm _

/-- **Stacks Project, Tag 01NU: the generation condition in the form a triple of Section 01N4
carries it.** For an affine base and a quasi-coherent graded algebra, the degree-`d` values of
the Veronese family of a quadruple's twisting generate `L`: their nonvanishing opens cover `T`. -/
theorem Quadruple.iSup_nonvanishingOpen_psiSection_eq_top [IsAffine S]
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (P : Quadruple f (situationAlgebra B) (d : ℤ)) :
    (⨆ a : B.grading (⊤ : S.Opens) d, nonvanishingOpen T P.L
        (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections P.twisting) a)) = ⊤ := by
  refine top_unique ?_
  rw [← Quadruple.iSup_nonvanishingOpen_eq_top hqc P]
  refine iSup_le fun b => le_iSup_of_le ⟨DirectSum.of (B.sectionPieces ⊤) d b,
    B.of_mem_grading (⊤ : S.Opens) b⟩ (le_of_eq ?_)
  exact (nonvanishingOpen_psiSection_veroneseSections P.twisting b).symm

/-- **Stacks Project, Tag 01NU: the classifying morphism of a quadruple over an affine base.**
Let `S` be affine, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous pieces (Situation
01NN), let `d > 0`, and let `A = Γ(S, 𝒜)` be the graded ring of its global sections. For every
quadruple `(d, g : T → S, L, ψ)` over a test scheme `T` (Section 01NS) there is **one and only
one** morphism `φ : T ⟶ U_d ⊆ Proj(A)` for which the pullback `φ⁎(d, 𝒪_{U_d}(d), ψ^d)` of the
universal family of [Stacks, Tag 01N9] is strictly equivalent to the triple the quadruple
induces. -/
theorem Quadruple.existsUnique_hom_toDegreeOpen [IsAffine S] (hd : 0 < d)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (P : Quadruple f (situationAlgebra B) (d : ℤ)) :
    ∃! φ : T ⟶ (degreeOpen (B.grading (⊤ : S.Opens)) d).toScheme,
      ∃ α : pullbackTwist (B.grading (⊤ : S.Opens)) φ (d : ℤ) ≅ P.L,
        IsCompatible (B.grading (⊤ : S.Opens)) (veroneseSections P.twisting) ⟨φ, α⟩ :=
  ProjDegreeOpenRepresents.existsUnique_hom (B.grading (⊤ : S.Opens)) hd
    (veroneseSections P.twisting)
    (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc P)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
