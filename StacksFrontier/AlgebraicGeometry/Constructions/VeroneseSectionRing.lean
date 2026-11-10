module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.VeronesePower
public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjRatios
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.Basic
public import StacksFrontier.Algebra.DirectSum.ExternalGrading

/-!
# The section ring is its own Veronese datum

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `S = Γ_*(X, L)` the graded section ring of
Stacks Tag 01CV. [Stacks, Tag 01N8] takes as input a graded ring map `ψ : A^{(d)} ⟶ Γ_*(Y, M)` in
the shape `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`, and the one instance of
it that identifies the twists pulled back along the canonical morphism of [Stacks, Tag 01PZ] is
`A = S`, `Y = X`, `M = L ^⊗ d` and `ψ` the **identity**: the degree-`n` piece of `S^{(d)}` is
`Γ(X, L ^⊗ (n d))` and the degree-`n` piece of `Γ_*(X, L ^⊗ d)` is `Γ(X, (L ^⊗ d) ^⊗ n)`, and the
two are the same thing.

"The same thing" is not a tautology in Lean, and this file is what makes it one: the comparison is
the Veronese identification `Stacks.GradedSections.powPowIso` of the sibling file
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/VeronesePower.lean`, and the multiplicativity the
structure requires is `Stacks.GradedSections.ofPowPow_mul`.

**No `VeroneseSections` had ever been constructed.** The structure is used as a hypothesis in
some forty places across the `ProjChart*` files — the entire existence-and-uniqueness machinery of
[Stacks, Tag 01N8] and the representability statement of [Stacks, Tag 01N9] are stated over it —
and no term of it existed, so none of that machinery had ever been applied to anything. The
missing input was exactly the identification above, recorded as absent in the implementation notes
of `StacksFrontier/AlgebraicGeometry/Constructions/ProjChartFullGradedGluing.lean` and of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjDegreeOpenRepresents.lean`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartFromRatios.veroneseToFun` — the degree-`n` component
  `S_{nd} ⟶ Γ(X, (L ^⊗ d) ^⊗ n)`: extract the homogeneous piece of the section ring, reindex
  `n d` to `d n`, and read it along the Veronese identification.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.sectionRingVeronese` — **the Veronese datum
  `S^{(d)} ⟶ Γ_*(X, L ^⊗ d)`**, the input [Stacks, Tag 01N8] asks for, for every `d`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartFromRatios.veroneseToFun_apply` — the component written out.
* `Stacks.AlgebraicGeometry.ProjChartFromRatios.comp_powCongr_eq_of_of_eq` — two homogeneous
  pieces with the same image in the section ring agree, after the reindexing their degrees differ
  by. This is the one piece of `DirectSum` bookkeeping the multiplicativity needs, and it is
  stated with the two degrees as variables so that the equality between them can be substituted.

## Implementation notes

**Why the reindexing `n d` to `d n` appears.** `VeroneseSections` indexes its degree-`n`
component by `𝒜 (n * d)`, the Veronese grading of Section 27.12, while the recursion of
`Stacks.GradedSections.powPowIso` produces the exponent `d * n`, `Nat.mul` recursing on its second
argument. The two are the same natural number but not the same term, so one transport
(`Stacks.GradedSections.powCongrHom`) stands between them. It is applied once, in the definition
of the component, and `Nat.mul_comm` is the only arithmetic fact used.

**The grading is external.** `Stacks.AmpleFiniteAvoidance.grading L` is
`Stacks.ExternalGrading.summand (powSections L)`, the image of `Γ(X, L ^⊗ i)` in
`⨁_i Γ(X, L ^⊗ i)`, so its degree-`i` piece is additively `powSections L i` by
`Stacks.ExternalGrading.summandEquiv` and extracting the piece is that equivalence's inverse —
evaluation of the direct sum at `i`. That is why the component below is a composite of three
additive maps and not a single formula.

**The hypothesis of `map_mul` is an equation in the section ring, not in a homogeneous piece.**
The structure states multiplicativity as: for `ab` of degree `(n + m) d` whose underlying ring
element is the product of those of `a` and `b`, the component at `n + m` of `ab` is the product of
the components. Turning that into an equation of homogeneous pieces is
`comp_powCongr_eq_of_of_eq` applied to `DirectSum.of_mul_of`, after which
`Stacks.GradedSections.ofPowPow_mul` is the whole content and
`Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections_globalSection` crosses from the
`Stacks.GradedSections.mul` spelling to the `mulSections` spelling the field is written in.

**No ampleness is used.** `L` is only required to be invertible, which is what the section ring
and the tensor powers need; ampleness enters [Stacks, Tag 01N8] through its generation hypothesis,
which is about a particular `d` and is not part of this datum.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV) — the graded section ring.
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8) — the lemma this datum is
  the input of.
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9) — the representability
  statement over the same datum.

## What is not done

**No attribute is attached, and no consequence of [Stacks, Tag 01N8] is drawn here.** This file
supplies an input; applying the tag additionally needs its generation hypothesis — that the
nonvanishing opens of the degree-`d` sections cover `X`, which for `L` ample holds for every
`d` beyond the bound of
`Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple` — and that application, together
with the identification of the morphism it produces with
`Stacks.SectionRingProjMorphism.projHomOfIsAmple`, is not carried out here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul powCongr sectionRing)
open Stacks.SectionProduct (globalSection)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartFromRatios

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### Extracting a homogeneous piece -/

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **Two homogeneous pieces with the same image in the section ring agree**, after the reindexing
their degrees differ by. Both degrees are variables, so the equality between them is substituted
and what is left is the injectivity of `DirectSum.of`, read off by evaluating at the common
degree. -/
theorem comp_powCongr_eq_of_of_eq {i j : ℕ} (h : i = j) {x : powSections L i}
    {y : powSections L j}
    (hxy : DirectSum.of (powSections L) i x = DirectSum.of (powSections L) j y) :
    x ≫ powCongr L h = y := by
  subst h
  have hx := congrArg (fun z : sectionRing L => z i) hxy
  simp only [DirectSum.of_eq_same] at hx
  rw [Stacks.GradedSections.powCongr_rfl, Category.comp_id]
  exact hx

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The homogeneous piece underlying an element of the external grading. -/
theorem of_piece (i : ℕ) (z : Stacks.AmpleFiniteAvoidance.grading L i) :
    DirectSum.of (powSections L) i
        ((Stacks.ExternalGrading.summandEquiv (powSections L) i).symm z)
      = (z : sectionRing L) := by
  obtain ⟨z₀, hz₀⟩ := z.2
  have hsym : (Stacks.ExternalGrading.summandEquiv (powSections L) i).symm z = z₀ := by
    have : (z : sectionRing L) i = z₀ := by rw [← hz₀, DirectSum.of_eq_same]
    exact this
  rw [hsym, hz₀]

/-! ### The Veronese datum of the section ring -/

/-- **The degree-`n` component of the Veronese comparison**
`S_{nd} ⟶ Γ(X, (L ^⊗ d) ^⊗ n)`: extract the homogeneous piece of the section ring, reindex the
degree `n d` as `d n`, read it along the Veronese identification
`Stacks.GradedSections.powPowIso`, and cross to honest global sections. -/
def veroneseToFun (d n : ℕ) :
    Stacks.AmpleFiniteAvoidance.grading L (n * d) →+
      Γ(natTensorPow (natTensorPow L d) n, ⊤) :=
  ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
        (natTensorPow (natTensorPow L d) n)).toAddMonoidHom.comp
      ((Stacks.GradedSections.ofPowPowHom L d n).comp
        (Stacks.GradedSections.powCongrHom L (Nat.mul_comm n d)))).comp
    (Stacks.ExternalGrading.summandEquiv (powSections L) (n * d)).symm.toAddMonoidHom

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The value of `veroneseToFun` on `z` is the global section of `(L ^⊗ d) ^⊗ n` obtained from
the homogeneous piece of `z` by reindexing along `n * d = d * n` and applying
`Stacks.GradedSections.ofPowPow`. -/
theorem veroneseToFun_apply (d n : ℕ) (z : Stacks.AmpleFiniteAvoidance.grading L (n * d)) :
    veroneseToFun L d n z
      = globalSection X _ (Stacks.GradedSections.ofPowPow L d n
          ((Stacks.ExternalGrading.summandEquiv (powSections L) (n * d)).symm z ≫
            powCongr L (Nat.mul_comm n d))) := rfl

/-- **The Veronese datum `S^{(d)} ⟶ Γ_*(X, L ^⊗ d)` of [Stacks, Tag 01N8]**, for the section ring
`S = Γ_*(X, L)` of `L` itself and the invertible module `L ^⊗ d`. The degree-`n` component is
`veroneseToFun`, and multiplicativity is the multiplicativity
`Stacks.GradedSections.ofPowPow_mul` of the Veronese identification: the hypothesis is turned into
an equation of homogeneous pieces by `comp_powCongr_eq_of_of_eq` applied to `DirectSum.of_mul_of`,
and `mulSections_globalSection` crosses to the `mulSections` spelling. -/
def sectionRingVeronese (d : ℕ) :
    VeroneseSections (Stacks.AmpleFiniteAvoidance.grading L) d (natTensorPow L d) where
  toFun n := veroneseToFun L d n
  map_mul n m a b ab hab := by
    set a₀ := (Stacks.ExternalGrading.summandEquiv (powSections L) (n * d)).symm a with ha₀
    set b₀ := (Stacks.ExternalGrading.summandEquiv (powSections L) (m * d)).symm b with hb₀
    set ab₀ := (Stacks.ExternalGrading.summandEquiv (powSections L) ((n + m) * d)).symm ab
      with hab₀
    have hof : DirectSum.of (powSections L) ((n + m) * d) ab₀
        = DirectSum.of (powSections L) (n * d + m * d) (mul a₀ b₀) := by
      rw [of_piece, hab, ← of_piece L (n * d) a, ← of_piece L (m * d) b, DirectSum.of_mul_of,
        Stacks.GradedSections.gMul_def]
    have hpiece : ab₀ ≫ powCongr L (Nat.add_mul n m d) = mul a₀ b₀ :=
      comp_powCongr_eq_of_of_eq L (Nat.add_mul n m d) hof
    have hab₀eq : ab₀ = mul a₀ b₀ ≫ powCongr L (Nat.add_mul n m d).symm := by
      rw [← hpiece]; simp
    have hkey : mul (Stacks.GradedSections.ofPowPow L d n (a₀ ≫ powCongr L (Nat.mul_comm n d)))
          (Stacks.GradedSections.ofPowPow L d m (b₀ ≫ powCongr L (Nat.mul_comm m d)))
        = Stacks.GradedSections.ofPowPow L d (n + m)
            (ab₀ ≫ powCongr L (Nat.mul_comm (n + m) d)) := by
      rw [Stacks.GradedSections.ofPowPow_mul]
      congr 1
      rw [Stacks.GradedSections.mul_def, hab₀eq]
      simp only [Category.assoc,
        Stacks.GradedSections.powCongr_comp_mulMap_assoc,
        Stacks.GradedSections.mulMap_comp_powCongr, Stacks.GradedSections.mul_def, eqToHom_trans]
    rw [veroneseToFun_apply, veroneseToFun_apply, veroneseToFun_apply,
      mulSections_globalSection, hkey]

end Stacks.AlgebraicGeometry.ProjChartFromRatios

end
