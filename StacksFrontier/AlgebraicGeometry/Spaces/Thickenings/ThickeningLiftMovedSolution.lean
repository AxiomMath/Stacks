module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningLiftDerivationBaseVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpRestrictedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedData
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftComorphism

/-!
# The solution of the lifting problem moved by a linear map, and the morphism it realizes

Let `Z ⊆ X` be a first order thickening of algebraic spaces over a scheme `S` with inclusion
`i : Z ⟶ X`, let `W₀ ⊆ W` be a closed subspace with inclusion `j : W₀ ⟶ W`, let `c : X ⟶ W`
carry `i ≫ c = e₀ ≫ j` for a morphism `e₀ : Z ⟶ W₀`, let `qb : W ⟶ Bas` with `c ≫ qb = p`, and
let `b : W₀ ⟶ Bas₀` fit a commutative square `j ≫ qb = b ≫ iB`.

For an `𝒪_Z`-linear map `θ : e₀^*Ω_{W₀/Bas₀} ⟶ 𝒞_{Z/X}` the transported comorphism of `c` is
moved by the `𝒪_{Bas₀}`-derivation attached to `θ` by Equation [Stacks Project, Tag 0619] to a
second solution

`g = c^♯ − ι ∘ D ∘ j^♯`

of the lifting problem on the small étale site of `W₀`
(`AlgebraicGeometry.Space.liftDifferenceDataOfHom`).  This file shows that **`g` is realized by
a morphism `X ⟶ W` over `Bas` agreeing with `c` on `Z`** — the existence clause of
[Stacks Project, Tag 04D0] in the comorphism form the `ThickeningSharp*` machinery consumes and
produces.

## The argument

1. `g` agrees with the transported comorphism of `c` on every function read from the ambient
   base `Bas`: the two differ by the derivation attached to `θ`, which kills those functions by
   `AlgebraicGeometry.Space.derivationFamilyOfHom_app_inverseImage_eq_zero`.
2. `g` has the same reduction as the transported comorphism of `c`: their difference takes
   values in the square-zero ideal, which the reduction annihilates
   (`AlgebraicGeometry.Space.liftDifferenceDataOfHom_g_comp_eq`,
   `AlgebraicGeometry.Space.app_reduction_restrictedSquareZeroValues_ι_eq_zero`).  Carried back
   to the ambient site of `W` and transported to the tautological index, that reduction is the
   comorphism of `i ≫ c`
   (`AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening_comp_reduction`,
   `AlgebraicGeometry.Space.thickeningLiftOfIndex_comp_reduction`).
3. Step 1 supplies the hypothesis `hbase` and step 2 the hypothesis `hred` of
   `AlgebraicGeometry.Space.exists_hom_of_thickeningLiftRingSheaf`, which produces the morphism.

## Main definitions

* `AlgebraicGeometry.Space.movedThickeningLift`: the pair consisting of the transported
  comorphism of `c` and the solution `g` it is moved to by `θ`.

## Main results

* `AlgebraicGeometry.Space.inverseImage_comp_movedThickeningLift_g_eq`: **step 1.**
* `AlgebraicGeometry.Space.movedThickeningLift_g_comp_reduction_eq` and
  `AlgebraicGeometry.Space.comp_reduction_eq_of_movedThickeningLift`: **step 2**, on the
  site of `W₀` and on the ambient site of `W`.
* `AlgebraicGeometry.Space.app_movedThickeningLift_eq`: step 1 in the shape
  `AlgebraicGeometry.Space.exists_hom_of_thickeningLiftRingSheaf` consumes it.
* `AlgebraicGeometry.Space.exists_hom_of_movedThickeningLift`: **the morphism `X ⟶ W` realizing
  the moved solution** — over `Bas`, agreeing with `c` on `Z`, and restricting on every chart to
  the morphism of charts the moved solution attaches.
* `AlgebraicGeometry.Space.restrictedSharpThroughThickening_eq_movedThickeningLift_g`: **the
  transported comorphism of that morphism is the moved solution**, so the pair of transported
  comorphisms of `c` and of it is the datum `movedThickeningLift` itself, whose descended
  difference is `θ`.

## Implementation notes

Every step is a generic instance of a result already in the tree; the groupoid instance of
[Stacks Project, Tag 0CKE] performs the same steps at its own data, in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsInfinitesimalLift.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsInfinitesimalAmalgamate.lean`.
What is new is that the data is arbitrary, so the statement can be read at an arbitrary object
of a site rather than at the single global object a groupoid section lives over.

**The hypotheses of `AlgebraicGeometry.Space.liftDifferenceDataOfHom` are never passed
eta-expanded.**  Writing `fun A x ↦ h … A x` for an `h` that already has that type is a
deterministic `whnf` timeout here: the two readings of the sections of the inverse
image of the structure sheaf — at `CommRingCat` and at `RingCat` — are then compared under a
binder instead of once.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceSurjective.lean` record the same hazard for
the section-indexed families of that file.

**No `@[stacks]` attribute is placed.**  What is proved here is the existence clause of
[Stacks Project, Tag 04D0] together with the identification of the difference with `θ`; the
uniqueness clause is `AlgebraicGeometry.Space.eq_of_restrictedSharpThroughThickening_eq`, which
lives elsewhere, so no single declaration here carries the tag.

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0), the tag whose existence
  clause this is.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the derivation attached
  to a linear map.
* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN), the recovery of a
  morphism from its comorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W Bas Bas₀ : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (hZ : IsFirstOrderThickening B S hS X Z.1)
  (c : X ⟶ W)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
  (b : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Bas₀)
  (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
    conormalModule B S hS X Z)

/-! ### The moved solution -/

/-- **The transported comorphism of `c` and the solution it is moved to by the derivation
attached to `θ`**, as a `Stacks.Sites.LiftDifferenceData` for the quotient map
`j^♯ : j⁻¹𝒪_W ⟶ 𝒪_{W₀}`.  Its second map is

`g = c^♯ − ι ∘ D ∘ j^♯`,

the solution of the lifting problem whose descended difference from `c^♯` is `θ`. -/
def movedThickeningLift :
    LiftDifferenceData
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀))
      (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ) :=
  liftDifferenceDataOfHom B S hS b e₀ (conormalModule B S hS X Z)
    (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c hc x m)
    θ

/-! ### Step 1: agreement on the functions read from the ambient base -/

section Base

variable (qb : W ⟶ Bas) (iB : Bas₀ ⟶ Bas)
  (hsq : subspaceInclusion B S hS W W₀ ≫ qb = b ≫ iB)

include hsq in
/-- **The moved solution agrees with the transported comorphism of `c` after `j⁻¹(qb^♯)`:** the
two differ by the derivation attached to `θ`, which kills the functions read from the ambient
base `Bas` by
`AlgebraicGeometry.Space.derivationFamilyOfHom_app_inverseImage_eq_zero`.

This is the hypothesis under which the morphism of charts attached to the moved solution is a
morphism over `Bas`. -/
theorem inverseImage_comp_movedThickeningLift_g_eq :
    (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
        (structureSharpRingInverseImage B S hS qb) ≫
      (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g =
    (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
        (structureSharpRingInverseImage B S hS qb) ≫
      restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc :=
  comp_liftDifferenceDataOfHom_g_eq B S hS b e₀ (conormalModule B S hS X Z)
    (q := structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)) _ _ θ _
    (derivationFamilyOfHom_app_inverseImage_eq_zero B S hS W₀ qb iB b hsq e₀
      (conormalModule B S hS X Z) θ)

include hsq in
/-- **Step 1 in the shape `AlgebraicGeometry.Space.exists_hom_of_thickeningLiftRingSheaf`
consumes it:** read on the ambient site of `W` at the tautological index, the moved solution
agrees with the comorphism of `c` read through the thickening on every regular function read
from `Bas`.

This is
`AlgebraicGeometry.Space.app_liftRestrictedSharpThroughThickening_eq` with the index
transported, exactly as
`AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_index` transports it. -/
theorem app_movedThickeningLift_eq (V : SmallEtale B S hS W.1)
    (s : ToType ((structureRingSheafInverseImage B S hS qb).obj.obj (op V))) :
    (thickeningLiftOfIndex B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hc
      (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀
        (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g)).hom.app (op V)
        ((structureSharpRingInverseImage B S hS qb).hom.app (op V) s) =
      (structureSharpThroughThickening B S hS Z c).hom.app (op V)
        ((structureSharpRingInverseImage B S hS qb).hom.app (op V) s) :=
  (app_thickeningLiftOfIndex_congr B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hc
        (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀
          (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g)
        (structureSharpThroughThickeningAt B S hS Z c
          (e₀ ≫ subspaceInclusion B S hS W W₀) hc) (op V) _
        (app_liftRestrictedSharpThroughThickening_eq B S hS Z W₀ c e₀ hc qb
          (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g
          (inverseImage_comp_movedThickeningLift_g_eq B S hS Z W₀ hZ c e₀ hc b θ qb iB hsq)
          (op V) s)).trans
    (congrArg (fun n : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c ↦
        n.hom.app (op V) ((structureSharpRingInverseImage B S hS qb).hom.app (op V) s))
      (thickeningLiftOfIndex_structureSharpThroughThickeningAt B S hS Z c
        (e₀ ≫ subspaceInclusion B S hS W W₀) hc))

end Base

/-! ### Step 2: the reduction is unchanged -/

/-- **The moved solution has the same reduction as the transported comorphism of `c`:** the two
differ by a map with values in the square-zero ideal `(e₀)_*𝒞_{Z/X}`, and the conormal module is
the kernel of the reduction, so the reduction does not see the difference
(`AlgebraicGeometry.Space.app_reduction_restrictedSquareZeroValues_ι_eq_zero`).  For the
transported comorphism of `c` the reduction is computed by
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_reduction_structureSharp`. -/
theorem movedThickeningLift_g_comp_reduction_eq :
    (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallToposMorphismTypeU B S hS e₀).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀) ≫
        structureSharp B S hS e₀ :=
  (liftDifferenceDataOfHom_g_comp_eq B S hS b e₀ (conormalModule B S hS X Z) _ _ θ _
    (app_reduction_restrictedSquareZeroValues_ι_eq_zero B S hS Z W₀ e₀ hZ)).trans
    (restrictedSharpThroughThickening_comp_reduction_structureSharp B S hS Z W₀ e₀ c hc)

/-- **The moved solution, read on the ambient site of `W` at the tautological index, has the
comorphism of `i ≫ c` for its reduction.**

On the site of `W₀` the reduction is `j^♯` followed by the comorphism of `e₀`, which is
`AlgebraicGeometry.Space.movedThickeningLift_g_comp_reduction_eq`; carrying it back to the site
of `W` preserves that, by
`AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening_comp_reduction`, and the transport
to the index `i ≫ c` preserves it again, by
`AlgebraicGeometry.Space.thickeningLiftOfIndex_comp_reduction`. -/
theorem comp_reduction_eq_of_movedThickeningLift :
    (thickeningLiftOfIndex B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hc
      (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀
        (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g)) ≫
        thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c) :=
  thickeningLiftOfIndex_comp_reduction B S hS Z c _ hc _
    (liftRestrictedSharpThroughThickening_comp_reduction B S hS Z W₀ e₀
      (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g
      (movedThickeningLift_g_comp_reduction_eq B S hS Z W₀ hZ c e₀ hc b θ))

/-! ### The morphism realizing the moved solution -/

section Realize

variable (qb : W ⟶ Bas) (iB : Bas₀ ⟶ Bas)
  (hsq : subspaceInclusion B S hS W W₀ ≫ qb = b ≫ iB)
  (p : X ⟶ Bas) (hp : c ≫ qb = p)

include hsq hp in
/-- **The existence clause of [Stacks Project, Tag 04D0] in comorphism form.**  The solution of
the lifting problem obtained by moving the transported comorphism of `c` by the derivation
attached to `θ` is realized by a morphism `ε : X ⟶ W` which lies over `Bas`, agrees with `c` on
the thickening `Z`, and whose restriction to any chart of `X` carrying an index over any affine
chart of `W` is the morphism of charts the moved solution attaches.

This is `AlgebraicGeometry.Space.exists_hom_of_thickeningLiftRingSheaf` with its two hypotheses
discharged: `hred` by
`AlgebraicGeometry.Space.comp_reduction_eq_of_movedThickeningLift` and `hbase` by
`AlgebraicGeometry.Space.app_movedThickeningLift_eq`. -/
theorem exists_hom_of_movedThickeningLift :
    ∃ ε : X.1 ⟶ W.1, ε ≫ qb.hom = p.hom ∧ Z.1.ι ≫ ε = Z.1.ι ≫ c.hom ∧
      ∀ (V : SmallEtale B S hS W.1)
        [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
        (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
        (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
          (SmallEtale.toOver B S hS W.1).obj V),
        (BigFppfOver.toScheme B S hS).map ψ =
            thickeningLiftChartHom B S hS Z hZ.1 c
              (thickeningLiftOfIndex B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hc
      (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀
        (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g)) V j →
        j.right.unop.1.hom ≫ ε = yoneda.map ψ ≫ V.1.hom :=
  exists_hom_of_thickeningLiftRingSheaf B S hS Z hZ.1 c
    (thickeningLiftOfIndex B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hc
      (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀
        (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g))
    (comp_reduction_eq_of_movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ) qb p hp
    (app_movedThickeningLift_eq B S hS Z W₀ hZ c e₀ hc b θ qb iB hsq)

end Realize

/-! ### The comorphism of the realized morphism is the moved solution -/

section Identify

variable (qb : W ⟶ Bas) (iB : Bas₀ ⟶ Bas)
  (hsq : subspaceInclusion B S hS W W₀ ≫ qb = b ≫ iB)

include hsq in
/-- **The transported comorphism of a morphism realizing the moved solution is that solution.**
Let `ε : X ⟶ W` agree with `c` on the thickening and restrict, on every chart of `X` carrying an
index over an affine chart of `W`, to the morphism of charts the moved solution attaches.  Then
the comorphism of `ε` read through the thickening on the site of `W₀` *is* the moved solution.

With `AlgebraicGeometry.Space.exists_hom_of_movedThickeningLift` this says that the pair of
transported comorphisms of `c` and of `ε` is literally
`AlgebraicGeometry.Space.movedThickeningLift`.  So hypothesis (2) of
[Stacks Project, Tag 0618] for that pair needs nothing — it is the field
`app_eq_of_app_eq_zero` of a datum already constructed — and the descended difference of the
pair is `θ`, by
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_liftDifferenceDataOfHom`.

The comorphism of `ε` is identified with the moved solution on the ambient site of `W` by
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom`, whose
two hypotheses are `AlgebraicGeometry.Space.comp_reduction_eq_of_movedThickeningLift` and
`AlgebraicGeometry.Space.app_movedThickeningLift_eq`; the index is transported by
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt_eq_of_eq_thickeningLiftOfIndex`, and
the transport to the site of `W₀` is injective
(`AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening_injective`). -/
theorem restrictedSharpThroughThickening_eq_movedThickeningLift_g (ε : X ⟶ W)
    (hres : subspaceInclusion B S hS X Z ≫ ε = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hchart : ∀ (Q : SmallEtale B S hS W.1)
        (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS W.1).obj Q)))
        (j : StructuredArrow (op (chartBaseChange B S hS c Q))
          (comparisonFunctor B S hS X).op)
        (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
          (SmallEtale.toOver B S hS W.1).obj Q),
      (BigFppfOver.toScheme B S hS).map ψ =
          thickeningLiftChartHom B S hS Z hZ.1 c
            (thickeningLiftOfIndex B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hc
              (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀
                (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g)) Q j →
        j.right.unop.1.hom ≫ ε.hom = yoneda.map ψ ≫ Q.1.hom) :
    restrictedSharpThroughThickening B S hS Z W₀ ε e₀ hres =
      (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g := by
  have hA : structureSharpThroughThickeningAt B S hS Z ε
        (e₀ ≫ subspaceInclusion B S hS W W₀) hres =
      liftRestrictedSharpThroughThickening B S hS Z W₀ e₀
        (movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ).g := by
    refine structureSharpThroughThickeningAt_eq_of_eq_thickeningLiftOfIndex B S hS Z c ε
      (e₀ ≫ subspaceInclusion B S hS W W₀) hc hres _ ?_
    exact structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom B S hS Z hZ.1 c ε
      (hres.trans hc.symm) _
      (comp_reduction_eq_of_movedThickeningLift B S hS Z W₀ hZ c e₀ hc b θ) qb
      (app_movedThickeningLift_eq B S hS Z W₀ hZ c e₀ hc b θ qb iB hsq) hchart
  exact liftRestrictedSharpThroughThickening_injective B S hS Z W₀ e₀ _ _
    ((liftRestrictedSharpThroughThickening_restrictedSharpThroughThickening
      B S hS Z W₀ ε e₀ hres).trans hA)

end Identify

end AlgebraicGeometry.Space

end
