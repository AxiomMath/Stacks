module

public import StacksFrontier.AlgebraicGeometry.ChartCocycleRigidity.DegreeOne
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.GeneratedInDegreeOne

/-!
# The chart cocycle of Tag 01NO in degree one, and the twist `𝒪(1)` it glues

Along a chain `W ⊆ W' ⊆ U` of affine opens of the base, the endomorphism of the degree-one twist
on the chart of `W` obtained by cancelling Tag 01NO's comparison for `W ⊆ U` against the two
comparisons through the chart of `W'` is the identity, provided the graded ring of sections over
each affine open has, at every point of its `Proj`, a nonvanishing element of degree one.

Consequently `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle A 1` holds, and
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist A 1`, the glued twist on the
relative projective spectrum, exists. For the symmetric algebra of a quasi-coherent module `E`,
whose relative `Proj` is the projective bundle, this gives `𝒪_{𝐏(E)}(1)` with no hypothesis
beyond quasi-coherence of `E` and of the pieces of `Sym(E)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.symGluedTwistOne`: **the twist `𝒪_{𝐏(E)}(1)`**
  on the projective bundle of a quasi-coherent module, unconditionally.

## Main results

* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.eq_id_res_legEndo`: **degree-one rigidity for the
  generic three-leg endomorphism.** With the three open immersions and the three comparisons as
  variables, an endomorphism of the twists on `Proj Γ(W, A)` built by cancelling three
  comparisons is the identity in degree one as soon as it fixes the homogeneous global sections
  of the elements restricted from a larger affine open.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legEndoChart_eq_id_one` and
  `cocycleEndo_eq_id_one`: **the cocycle endomorphism is the identity in degree one**, at the two
  readings of the structure sheaf of a projective spectrum.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.isNestedCocycle_one`:
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle A 1`.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.isNestedCocycle_one_sym`: the same for `Sym(E)`,
  with no hypothesis left.

## Implementation notes

The twists are sheaves of modules over `CategoryTheory.sheafCompose` of the forgetful functor with
`AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf`, while
`Stacks.AlgebraicGeometry.ChartCocycleRigidity.legEndo` is indexed by the chart's own
`AlgebraicGeometry.Scheme.ringCatSheaf`. The two are definitionally equal, but the check is
affordable only when every ingredient is a variable, which is why `eq_id_res_legEndo` takes the
open immersions and comparisons as variables. `legEndoChart_eq_id_one` and
`cocycleEndo_eq_id_one` are kept as two declarations: proved in one step, the statement for
`cocycleEndo` hits a deterministic timeout in the kernel.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.NestedCocycleReduction
open Stacks.AlgebraicGeometry.NestedCocycleTail
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.ChartCocycleRigidity

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### Degree-one rigidity for the generic three-leg endomorphism -/

/-- **Degree-one rigidity for the endomorphism obtained by cancelling three comparisons.** Let
three open immersions out of and into the chart of an affine open `W` of the base satisfy
`p₁ ≫ p₂ = p₃`, and let three comparisons identify the restriction of each outer module with the
next one in, the two inner targets being the twists on that chart. If the resulting endomorphism
fixes, in every degree, the homogeneous global section attached to the restriction to `W` of a
homogeneous element over a larger affine open `U`, then it is the identity in degree one. -/
public theorem eq_id_res_legEndo {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W U : S.Opens)
    (h : W ≤ U) (hW : IsAffineOpen W) (hU : IsAffineOpen U)
    {X Z : Scheme.{u}} (p₁ : AlgebraicGeometry.Proj (A.grading W) ⟶ Z) (p₂ : Z ⟶ X)
    (p₃ : AlgebraicGeometry.Proj (A.grading W) ⟶ X)
    [IsOpenImmersion p₁] [IsOpenImmersion p₂] [IsOpenImmersion p₃] (hp : p₁ ≫ p₂ = p₃)
    {M : ℤ → X.Modules} {N : ℤ → Z.Modules}
    (e₂ : ∀ n : ℤ, (Scheme.Modules.restrictFunctor p₂).obj (M n) ≅ N n)
    (e₁ : ∀ n : ℤ, (Scheme.Modules.restrictFunctor p₁).obj (N n) ≅ twistingSheaf (A.grading W) n)
    (e₃ : ∀ n : ℤ, (Scheme.Modules.restrictFunctor p₃).obj (M n) ≅ twistingSheaf (A.grading W) n)
    (hdeg : ∀ x : ProjectiveSpectrum (A.grading W),
      ∃ a : (A.grading W) 1, (a : A.sectionRing W) ∉ x.asHomogeneousIdeal)
    (hfix : ∀ (k : ℕ) (c : (A.grading U) k),
      (legEndo p₁ p₂ p₃ hp (e₂ (k : ℤ)) (e₁ (k : ℤ)) (e₃ (k : ℤ))).val.app (op ⊤)
          (degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩) =
        degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩) :
    legEndo p₁ p₂ p₃ hp (e₂ 1) (e₁ 1) (e₃ 1) =
      𝟙 (twistingSheaf (A.grading W) (1 : ℤ)) :=
  Stacks.AlgebraicGeometry.TwistRigidityDegreeOne.eq_id_res A W U h hW hU
    (α := fun n ↦ legEndo p₁ p₂ p₃ hp (e₂ n) (e₁ n) (e₃ n)) hdeg hfix

/-! ### The cocycle endomorphism in degree one -/

section Chain

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W W' U : S.Opens) (hWW' : W ≤ W')
  (hW'U : W' ≤ U) (hWU : W ≤ U) (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
  (hU : IsAffineOpen U)
  (hdeg : ∀ x : ProjectiveSpectrum (A.grading W),
    ∃ a : (A.grading W) 1, (a : A.sectionRing W) ∉ x.asHomogeneousIdeal)

include hWW' hW'U hWU hW hW' hU hdeg

/-- **Tag 01NO's comparison for the outer pair of a chain of affine opens, cancelled against the
two comparisons through the middle chart, is the identity on the degree-one twist.** The one
hypothesis is that at every point of `Proj Γ(W, A)` some degree-one element does not vanish.
The endomorphism is written with `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legEndo`, which
reads the twists over the chart's own sheaf of rings. -/
public theorem legEndoChart_eq_id_one :
    legEndo (projInclusionMap A W W' hWW' hW hW')
        (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
        (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
        (restrictTwistIso A W' U hW'U hW' hU 1) (restrictTwistIso A W W' hWW' hW hW' 1)
        (restrictTwistIso A W U hWU hW hU 1) =
      𝟙 (twistingSheaf (A.grading W) (1 : ℤ)) :=
  eq_id_res_legEndo A W U hWU hW hU (projInclusionMap A W W' hWW' hW hW')
    (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
    (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
    (restrictTwistIso A W' U hW'U hW' hU) (restrictTwistIso A W W' hWW' hW hW')
    (restrictTwistIso A W U hWU hW hU) hdeg
    (legEndoChart_val_app_top A W W' U hWW' hW'U hWU hW hW' hU)

/-- **The same for `Stacks.AlgebraicGeometry.ChartCocycleRigidity.cocycleEndo`**, whose declared
type reads the twists over `CategoryTheory.sheafCompose` of the forgetful functor with the
structure sheaf of the projective spectrum. -/
public theorem cocycleEndo_eq_id_one :
    cocycleEndo A W W' U hWW' hW'U hWU hW hW' hU 1 =
      𝟙 (twistingSheaf (A.grading W) (1 : ℤ)) :=
  legEndoChart_eq_id_one A W W' U hWW' hW'U hWU hW hW' hU hdeg

end Chain

/-! ### The nested cocycle in degree one -/

/-- **`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle A 1`.** For every chain of
affine opens of the base and every open of the relative projective spectrum inside the inverse
images of the two smaller ones, Tag 01NO's pushed-forward twist comparison for the outer pair is
the composite of the two comparisons through the middle chart, provided that over every affine
open of the base each point of the projective spectrum of the sections has a nonvanishing
degree-one element. -/
public theorem isNestedCocycle_one {S : Scheme.{u}} (A : SheafGradedAlgebra S)
    (hdeg : ∀ (W : S.Opens), IsAffineOpen W → ∀ x : ProjectiveSpectrum (A.grading W),
      ∃ a : (A.grading W) 1, (a : A.sectionRing W) ∉ x.asHomogeneousIdeal) :
    IsNestedCocycle A 1 := by
  intro W W' U hWW' hW'U hWU hW hW' hU V hV hV'
  refine isComposite_of_eval (cmpNested A W' U hW'U hW' hU 1) (cmpNested A W W' hWW' hW hW' 1)
      (cmpNested A W U hWU hW hU 1) V hV hV' _ _ _
      (cmpNested_app_val A W' U hW'U hW' hU 1 V hV')
      (cmpNested_app_val A W W' hWW' hW hW' 1 V hV)
      (cmpNested_app_val A W U hWU hW hU 1 V hV) ?_
  exact isEvalComposite_of_legEndo_eq_id (projInclusionMap A W W' hWW' hW hW')
    (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
    (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
    (restrictTwistIso A W' U hW'U hW' hU 1) (restrictTwistIso A W W' hWW' hW hW' 1)
    (restrictTwistIso A W U hWU hW hU 1)
    (legEndoChart_eq_id_one A W W' U hWW' hW'U hWU hW hW' hU (hdeg W hW))
    (homOfLE (image_preimage_le_preimage A W W' hWW' hW hW' V))
    (homOfLE (image_preimage_le_preimage A W' U hW'U hW' hU V))
    (homOfLE (image_preimage_le_preimage A W U hWU hW hU V))

/-! ### The twist `𝒪(1)` on a projective bundle -/

section Sym

variable {Y : Scheme.{u}} (E : Y.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)

/-- **The nested cocycle in degree one for the symmetric algebra of a quasi-coherent
module.** -/
public theorem isNestedCocycle_one_sym :
    IsNestedCocycle (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc) 1 :=
  isNestedCocycle_one _ fun _ hV ↦ Stacks.SymGraded.exists_degreeOne_notMem E hqc hV

/-- **The twist `𝒪_{𝐏(E)}(1)` on the projective bundle of a quasi-coherent module**: the sheaf of
modules obtained by glueing the degree-one twists of the charts of `Proj Sym(E)` along Tag 01NO's
comparisons. -/
public def symGluedTwistOne :
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme.Modules :=
  gluedTwist (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc) 1
    (isNestedCocycle_one_sym E hqc)

end Sym

end Stacks.AlgebraicGeometry.ChartCocycleRigidity

end
