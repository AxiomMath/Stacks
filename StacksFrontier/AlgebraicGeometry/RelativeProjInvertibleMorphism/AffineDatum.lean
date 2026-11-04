module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGraded
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMulRestrict
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionComponent
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.AffineRestriction

/-!
# The [Stacks, Tag 01NK] datum over an open of the base, from the global `(ℒ, ψ)` of Tag 01O8

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `f : T ⟶ S` a morphism of
schemes and `P = (ℒ, ψ)` the datum of [Stacks, Tag 01O8], carried by
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap`.  Clause (3) of
[Stacks, Tag 01O9] compares the restriction of the triple `(U(ψ), r_{ℒ,ψ}, θ)` over an affine
open `V ⊆ S` with the triple of [Stacks, Tag 01NK] for the graded ring `A = 𝒜(V)` and the map
`ψ' : A → Γ_*(f^{-1}(V), ℒ|_{f^{-1}(V)})` induced by `ψ`.  **This file constructs that induced
datum `ψ'`, and identifies its covering open.**

That construction is the step that the global morphism of [Stacks, Tag 01O9] needs beyond what
`StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjMorphismFromSections` and
`StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.AffineRestriction` prove about the
*open* `U(ψ)`: the per-affine-open [Stacks, Tag 01NK] datum derived from a global `(ℒ, ψ)`.

## What makes it work

Two things, both available:

* the multiplicativity of `ψ` across degrees, the field
  `…GradedPowerMap.map_mul` — item (6) of [Stacks, Tag 01O8] read as what it says, that `ψ` is a
  homomorphism of graded `𝒪_X`-algebras — stated against the product
  `Stacks.AlgebraicGeometry.NatTensorPowLocalMul.localMulSections` of two sections of tensor
  powers over one arbitrary open;
* its transport to the open subscheme,
  `Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection_localMulSections`,
  which carries that product to
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`, the product of *global* sections
  that [Stacks, Tag 01NK]'s datum is stated against.

The remaining friction is bookkeeping: the degree-`n` part of the graded ring `𝒜(V)` is an
`AddSubgroup` of a direct sum, not the group `Γ(𝒜_n, V)` of homogeneous sections, and
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.componentEquiv` is the
identification of the two.  Under it the product of a degree-`n` and a degree-`m` element of the
graded ring is the algebra's own multiplication on components, which is what lets
`…GradedPowerMap.value_mul` discharge the `map_mul` field of the datum.

## Main definitions

* `…GradedPowerMap.valueHom`: the component `ψ_n`, read on sections over an open of the base, as
  an additive map.
* `…GradedPowerMap.affineDatum`: **the [Stacks, Tag 01NK] datum `ψ'` over an open `V` of the
  base** — a `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections` for the graded ring
  `𝒜(V)` on the scheme `f^{-1}(V)` with the invertible module `ℒ|_{f^{-1}(V)}`, whose degree-`n`
  component sends a homogeneous section `a` to `ψ(a)` read as a global section of
  `(ℒ|_{f^{-1}(V)})^{⊗ n}`.

## Main results

* `…GradedPowerMap.nonvanishingOpenAt_affineDatum`: the open `T_{ψ'(a)}` of the induced datum is
  the part of `U_{ψ(a)}` lying in `f^{-1}(V)`.
* `…GradedPowerMap.coveringOpen_affineDatum`: **`U(ψ') = (f^{-1}(V))^{-1}(U(ψ_V))`** — the
  covering open of the induced datum is exactly the open `U(ψ_V)` of
  `…GradedPowerMap.coveringOpenOver`, read inside the open subscheme `f^{-1}(V)`.  Composed with
  `…GradedPowerMap.coveringOpen_inf_preimage_eq`, which says `U(ψ_V) = U(ψ) ∩ f^{-1}(V)` for `V`
  affine, this says the source of the [Stacks, Tag 01NK] prescription over `V` is precisely the
  part of `U(ψ)` lying over `V`, with nothing cut away.

## No tag is claimed here

The datum is an *input* to clause (3) of [Stacks, Tag 01O9], not one of the tag's assertions:
Tag 01O9 names the induced map `ψ'` in clause (3) and says nothing about it beyond that it is
induced by `ψ`.  The assertions of the tag are about the triple built from it.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul
  (restrictPowSection restrictPowSectionHom restrictPowSection_localMulSections
    nonvanishingOpen_restrictPowSection)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.SectionPowerOpen (nonvanishingOpenOn)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-! ### The components of `ψ` as additive maps -/

/-- **The component `ψ_n`, read on the homogeneous sections over an open `V` of the base, as an
additive map** `Γ(𝒜_n, V) →+ Γ(ℒ^{⊗ n}, f^{-1}(V))`.  This is
`…GradedPowerMap.value` bundled; the component is a morphism of sheaves of modules, so it is
additive on sections. -/
public def valueHom (n : ℕ) (V : S.Opens) :
    Γ(A.piece (n : ℤ), V) →+ Γ(natTensorPow P.L n, f ⁻¹ᵁ V) :=
  ((P.ψ n).val.app (op V)).hom.toAddMonoidHom

/-- The additive map `valueHom P n V` sends a section `a` to `P.value n V a`. -/
@[simp] public theorem valueHom_apply (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) :
    P.valueHom n V a = P.value n V a := rfl

/-! ### The datum -/

/-- **The [Stacks, Tag 01NK] datum induced by `ψ` over an open `V` of the base.**  For the graded
ring `A = 𝒜(V)` of homogeneous sections over `V`, the scheme `f^{-1}(V)` and the invertible
module `ℒ|_{f^{-1}(V)}`, the degreewise family sending a homogeneous `a ∈ 𝒜_n(V)` to the value
`ψ(a) ∈ Γ(f^{-1}(V), ℒ^{⊗ n})` read as a *global* section of `(ℒ|_{f^{-1}(V)})^{⊗ n}` on the open
subscheme.

This is the map `ψ' : A → Γ_*(f^{-1}(V), ℒ|_{f^{-1}(V)})` that clause (3) of [Stacks, Tag 01O9]
says is *induced by* `ψ`.  Its multiplicativity across degrees — the one axiom
[Stacks, Tag 01NK]'s datum imposes — is the field `…GradedPowerMap.map_mul` of [Stacks, Tag 01O8]
carried to the open subscheme by
`…ProjChartRatioPullbackLocalMul.restrictPowSection_localMulSections`.

`V` is not required to be affine: affineness is needed only by the charts of [Stacks, Tag 01NQ]
that the morphism of clause (3) composes with, not by the datum. -/
public def affineDatum (V : S.Opens) :
    GradedSections (A.grading V) ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) where
  toFun n := (restrictPowSectionHom P.L (f ⁻¹ᵁ V) n).comp
    ((P.valueHom n V).comp (A.componentEquiv V n).toAddMonoidHom)
  map_mul n m a b ab hab := by
    obtain ⟨a', ha'⟩ := (A.mem_grading_iff V (a : A.sectionRing V)).mp a.2
    obtain ⟨b', hb'⟩ := (A.mem_grading_iff V (b : A.sectionRing V)).mp b.2
    obtain ⟨c', hc'⟩ := (A.mem_grading_iff V (ab : A.sectionRing V)).mp ab.2
    have hA : (a : A.sectionRing V) n = a' := by rw [← ha']; exact DirectSum.of_eq_same _ _
    have hB : (b : A.sectionRing V) m = b' := by rw [← hb']; exact DirectSum.of_eq_same _ _
    have hC : (ab : A.sectionRing V) (n + m) = c' := by
      rw [← hc']; exact DirectSum.of_eq_same _ _
    have h1 : DirectSum.of (A.sectionPieces V) (n + m) c'
        = DirectSum.of (A.sectionPieces V) (n + m)
            ((A.mul (n : ℤ) (m : ℤ)).app V a' b') := by
      rw [hc', hab, ← ha', ← hb', DirectSum.of_mul_of]
      rfl
    have key : c' = (A.mul (n : ℤ) (m : ℤ)).app V a' b' :=
      ((DirectSum.of_eq_same (n + m) c').symm.trans
        (congrArg (fun z : A.sectionRing V => z (n + m)) h1)).trans
          (DirectSum.of_eq_same _ _)
    change restrictPowSection P.L (f ⁻¹ᵁ V) (n + m)
        (P.value (n + m) V ((ab : A.sectionRing V) (n + m)))
      = Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections _
          (restrictPowSection P.L (f ⁻¹ᵁ V) n (P.value n V ((a : A.sectionRing V) n)))
          (restrictPowSection P.L (f ⁻¹ᵁ V) m (P.value m V ((b : A.sectionRing V) m)))
    rw [hC, key, hA, hB, P.value_mul n m V]
    exact restrictPowSection_localMulSections P.L (f ⁻¹ᵁ V) n m _ _

/-- The degree-`n` component of `P.affineDatum V` sends `a` to the restriction to the open
subscheme `f ⁻¹ᵁ V` of `P.value n V` applied to the homogeneous section underlying `a`. -/
@[simp] public theorem affineDatum_toFun_apply (V : S.Opens) (n : ℕ) (a : A.grading V n) :
    (P.affineDatum V).toFun n a
      = restrictPowSection P.L (f ⁻¹ᵁ V) n (P.value n V (A.componentEquiv V n a)) := rfl

/-! ### The covering open of the induced datum -/

/-- **The open `T_{ψ'(a)}` of the induced datum is the part of `U_{ψ(a)}` lying in
`f^{-1}(V)`.**  Both are the nonvanishing locus of the same section, read once on the open
subscheme `f^{-1}(V)` and once on `T`; `…ProjChartRatioPullbackLocalMul`
`.nonvanishingOpen_restrictPowSection` identifies them. -/
public theorem nonvanishingOpenAt_affineDatum (V : S.Opens) (e : ℕ) (g : A.grading V e) :
    (P.affineDatum V).nonvanishingOpenAt e g
      = (f ⁻¹ᵁ V).ι ⁻¹ᵁ P.nonvanishingOpenAt e V (A.componentEquiv V e g) :=
  nonvanishingOpen_restrictPowSection P.L (f ⁻¹ᵁ V) e
    (P.value e V (A.componentEquiv V e g))

/-- **`U(ψ') = U(ψ_V)`, read inside `f^{-1}(V)`.**  The covering open of the induced
[Stacks, Tag 01NK] datum over `V` — the union of the opens on which the values of `ψ'` at the
homogeneous elements of positive degree of `𝒜(V)` do not vanish — is the preimage under the
inclusion of `f^{-1}(V)` of the open `U(ψ_V)` of `…GradedPowerMap.coveringOpenOver`.

With `…GradedPowerMap.coveringOpen_inf_preimage_eq`, which says `U(ψ_V) = U(ψ) ∩ f^{-1}(V)` for
`V` affine, this identifies the source of the clause (3) prescription over `V` with the part of
`U(ψ)` lying over `V`.

The two unions are indexed differently — over the homogeneous elements of the graded ring on one
side and over the homogeneous sections over `V` on the other — and
`…SheafGradedAlgebra.componentEquiv` matches the index sets. -/
public theorem coveringOpen_affineDatum (V : S.Opens) :
    (P.affineDatum V).coveringOpen = (f ⁻¹ᵁ V).ι ⁻¹ᵁ P.coveringOpenOver V := by
  rw [GradedPowerMap.coveringOpenOver, Scheme.Hom.preimage_iSup]
  refine le_antisymm (iSup_le fun p => ?_) (iSup_le fun p => ?_)
  · exact le_trans (le_of_eq (P.nonvanishingOpenAt_affineDatum V (p.1 + 1) p.2))
      (le_iSup (fun q : (d : ℕ) × Γ(A.piece ((d + 1 : ℕ) : ℤ), V) =>
        (f ⁻¹ᵁ V).ι ⁻¹ᵁ P.nonvanishingOpenAt (q.1 + 1) V q.2)
        ⟨p.1, A.componentEquiv V (p.1 + 1) p.2⟩)
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun q : (e : ℕ) × A.grading V (e + 1) =>
        (P.affineDatum V).nonvanishingOpenAt (q.1 + 1) q.2)
        ⟨p.1, (A.componentEquiv V (p.1 + 1)).symm p.2⟩)
    rw [P.nonvanishingOpenAt_affineDatum V (p.1 + 1)
      ((A.componentEquiv V (p.1 + 1)).symm p.2), AddEquiv.apply_symm_apply]

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
