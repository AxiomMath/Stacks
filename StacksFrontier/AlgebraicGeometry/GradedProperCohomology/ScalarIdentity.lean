module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedBaseAlgebraHom
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedSemilinear

/-!
# The scalar identity of [Stacks, Tag 0897]

`Stacks.AlgebraicGeometry.GradedProperCohomology.IsScalarIdentity` is the one datum tying the
structure morphism `f' : X' ⟶ Spec B` of [Stacks, Tag 0897]'s base change to the graded sections
of `𝓑`: through [Stacks, Tag 01LX] part (3), the degree-`k` inclusion of the global section of
`𝓑ₖ` named by a homogeneous `b ∈ 𝒜ₖ` is the function on `X'` by which `b` acts on every
`𝒪_{X'}`-module. **This file proves it** for the `f'` that
`Stacks.AlgebraicGeometry.GradedProperCohomology.HomogeneousSections.structureHom` builds.

## The shape of the argument

Both sides are restrictions of their values over `⊤`: the left by
`Stacks.Cohomology.FormalFunctions.gradedAlgebra_ungradedSheaf_map_ungradedIncl_eval` together
with the naturality of [Stacks, Tag 01LX] part (3), the right by the definition of
`AlgebraicGeometry.baseRingToSections`. Over `⊤` the identity is
`HomogeneousSections.specAlgebraRingHom_structureHom_coe`, which is
`GradedQcohAlgebra.appTop_structureHom_eq` — the ring map of `f'` on global sections, reduced to
the algebra-pullback unit followed by `ψ` — evaluated by
`HomogeneousSections.basePullbackHom_app_unit` and `HomogeneousSections.secRingHom_coe`.

## Main results

* `HomogeneousSections.specAlgebraRingHom_structureHom_coe`: **the ring map of `f'` on a
  homogeneous element of degree `k` is the degree-`k` inclusion of the global section that
  element names**, read in `Γ(X', ⊤)` through [Stacks, Tag 01LX] part (3).
* `HomogeneousSections.isScalarIdentity_structureHom`: **the scalar identity.**

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open scoped DirectSum AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

namespace HomogeneousSections

variable {X : Scheme.{u}} {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {𝒜 : ℕ → Submodule A B} [_root_.GradedAlgebra 𝒜] (D : GradedQcohAlgebra X)
  (S : HomogeneousSections D.alg 𝒜) (f : X ⟶ Spec (.of A))

/-- **The ring map of `f' : X' ⟶ Spec B` on a homogeneous element of degree `k` of `B`**: it is
the degree-`k` inclusion, into the ungraded realization of `𝓑`, of the global section of `𝓑ₖ`
that element names, read in `Γ(X', ⊤)` through [Stacks, Tag 01LX] part (3). -/
theorem specAlgebraRingHom_structureHom_coe (hsc : IsStructureCompatible D S f) {k : ℕ}
    (b : ↥(𝒜 k)) :
    specAlgebraRingHom B (structureHom D S f hsc) (b : B) =
      ((pushforwardAlgebraIso D.sheaf).inv.right.hom.app (op ⊤)).hom
        (secIncl D S b (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens)))) := by
  have happ := congrArg (fun φ : Γ(Spec (.of B), ⊤) ⟶ Γ(D.relSpec.left, ⊤) =>
      φ.hom ((Scheme.ΓSpecIso (.of B)).inv.hom (b : B)))
    (GradedQcohAlgebra.appTop_structureHom_eq B f D (basePullbackHom D S f hsc))
  change (structureHom D S f hsc).appTop.hom ((Scheme.ΓSpecIso (.of B)).inv.hom (b : B)) = _
  refine happ.trans ?_
  refine congrArg (fun z => ((pushforwardAlgebraIso D.sheaf).inv.right.hom.app (op ⊤)).hom z) ?_
  refine (basePullbackHom_app_unit D S f hsc _).trans ?_
  change secRingHom D S (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens)))
      ((Scheme.ΓSpecIso (.of B)).hom.hom ((Scheme.ΓSpecIso (.of B)).inv.hom (b : B))) = _
  rw [Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of B)) (b : B)]
  exact secRingHom_coe D S b _

/-- **The scalar identity of [Stacks, Tag 0897]**, for the structure morphism
`f' : X' ⟶ Spec B` of `HomogeneousSections.structureHom`: the degree-`k` inclusion of the global
section of `𝓑ₖ` named by a homogeneous `b ∈ 𝒜ₖ` is the function on `X'` by which `b` acts.

Both sides are the restriction of their value over `⊤`, and over `⊤` the identity is
`HomogeneousSections.specAlgebraRingHom_structureHom_coe`. -/
theorem isScalarIdentity_structureHom (hsc : IsStructureCompatible D S f) :
    IsScalarIdentity D S (structureHom D S f hsc) := by
  intro k b U
  have hres :=
    Stacks.Cohomology.FormalFunctions.gradedAlgebra_ungradedSheaf_map_ungradedIncl_eval D.alg
      (k : ℤ) (S.sec b) (U.unop.leTop.op : (op (⊤ : X.Opens)) ⟶ U)
  have hnat := NatTrans.naturality_apply (pushforwardRingIso D.sheaf).inv.hom
    (U.unop.leTop.op : (op (⊤ : X.Opens)) ⟶ U)
    (D.alg.ungradedIncl (k : ℤ) ((S.sec b).eval (op (⊤ : X.Opens))))
  refine Eq.trans (congrArg (fun z => ((pushforwardRingIso D.sheaf).inv.hom.app U).hom z)
    hres.symm) ?_
  refine hnat.trans ?_
  exact congrArg
    (fun z => (((Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing
      (relativeSpecToBase D.sheaf).base
      (relativeSpec D.sheaf).ringCatSheaf).obj.map
        (U.unop.leTop.op : (op (⊤ : X.Opens)) ⟶ U)).hom) z)
    (specAlgebraRingHom_structureHom_coe D S f hsc b).symm

end HomogeneousSections

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
