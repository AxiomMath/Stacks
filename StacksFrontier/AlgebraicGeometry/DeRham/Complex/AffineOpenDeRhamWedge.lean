module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamWedgeSections
public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.AffineOpenWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamComparison

/-!
# The de Rham differential on an affine open, through the degreewise comparison

`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso` identifies `Γ(Ω^p_{X/S}, U)` with
`⋀^p_A Ω[A⁄R]` for affine opens `U ⊆ X` and `V ⊆ S` with `U ≤ f^{-1}V`, writing `A := Γ(X, U)`
and `R := Γ(S, V)`. It says nothing about the de Rham differential. **This file supplies the
differential square**, by computing the comparison on the wedges `d a₁ ∧ ⋯ ∧ d a_p`, which span
`⋀^p_A Ω[A⁄R]`.

## Main results

* `Stacks.AlgebraicGeometry.AffineOpenDeRham.exteriorGenerator_d_eq_exactOne`: the degree-one
  generator of `⋀(Ω_{X/S})` on a universal relative differential is the exact one-form
  `AlgebraicGeometry.SheafOfModules.exactOne`. The two spellings of `d b` are definitionally
  equal; the lemma exists because nothing said so, which is why no consumer could find it.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_inv_ιMulti_d`: **the degreewise
  comparison, on a wedge of universal differentials.** Its inverse carries
  `d a₁ ∧ ⋯ ∧ d a_p` to the ordered product of the exact one-forms of the `a_i` over `U`.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamComplex_d_formsSectionsIso`: **the
  differential square, in every degree.** On `a₀ · (d a₁ ∧ ⋯ ∧ d a_p)` the de Rham differential
  of `Ω^•_{X/S}`, read over `U` through the degreewise comparison, is
  `d a₀ ∧ d a₁ ∧ ⋯ ∧ d a_p`.

## Implementation notes

The route is the one the globally-affine case takes. There,
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamComplex_d_sectionsIso` is
`differentialFormsSectionsIso_ιMulti_d` on both sides of the square followed by
`AlgebraicGeometry.Scheme.Hom.deRhamComplex_d_homogeneousProdLeft`; since that de Rham rule is
already stated at an arbitrary open of an arbitrary morphism, the only thing the affine-open case
needs is its own `ιMulti` computation, and that is the first result above.

That computation has two steps, because `formsSectionsIso` is
`affineOpenExteriorPowerΓIso ≪≫ exteriorPowerCongr kaehlerSectionsEquiv.symm`. The inverse of the
outer factor is `exteriorPower.map p` of the degree-one comparison, so
`exteriorPower.map_apply_ιMulti` moves it inside the wedge, where
`Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d` turns each
`CommRingCat.KaehlerDifferential.d a` into a universal relative differential; the inner factor is
then `Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso_inv_ιMulti`.

**The two spellings of an exact one-form.** The product that the de Rham rule consumes is written
with `AlgebraicGeometry.SheafOfModules.exactOne`, which is the degree-one generator of the
*chosen* package `AlgebraicGeometry.Scheme.Hom.deRhamAlgebras` applied to a universal
differential; the product that Tag 01I8 produces is written with
`AlgebraicGeometry.Scheme.Modules.exteriorGenerator`. The packages agree by
`AlgebraicGeometry.Scheme.Hom.deRhamAlgebras_exterior`, which is `rfl`, so the two spellings are
definitionally equal — in the globally-affine template that identification is implicit inside
`differentialFormsSectionsIso_ιMulti_d`, and that is exactly why it could not be cited. It is
recorded here as `exteriorGenerator_d_eq_exactOne`.

The ordered product is written left-handed, as the source writes it and as the de Rham rule
consumes it; Tag 01I8 produces the transport-free right-handed spelling, and the two are
exchanged by `Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd`.

## What this does not supply

The three gaps recorded in
`StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamComparison` that are not the
differential square are untouched: the abelian-sheaf mismatch, naturality in the square, and the
restriction of scalars from `Γ(X, U)` to `Γ(S, V)`. So this is still an input to
[Stacks, Tag 0FUI] and carries no tag attribute.

## References

* [Stacks Project, Tag 0FUI](https://stacks.math.columbia.edu/tag/0FUI)
* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open SheafOfModules.GradedAlgebra (IsExteriorAlgebra)

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenDeRham

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} {V : S.Opens}
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)

/-- **The degree-one generator of `⋀(Ω_{X/S})` on a universal relative differential is the exact
one-form.** The chosen package `AlgebraicGeometry.Scheme.Hom.deRhamAlgebras`, whose degree-one
generator `AlgebraicGeometry.SheafOfModules.exactOne` is built from, has the same exterior
algebra as `AlgebraicGeometry.Scheme.Modules.exteriorAlgebra` of the sheaf of relative
differentials (`AlgebraicGeometry.Scheme.Hom.deRhamAlgebras_exterior`, which is `rfl`), and the
same degree-one generator; so the two spellings are the same section. -/
theorem exteriorGenerator_d_eq_exactOne (W : (X.Opens)ᵒᵖ) (b : Γ(X, W.unop)) :
    (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials f)).val.app W
        ((Scheme.Hom.universalRelativeDerivation f).d b) =
      _root_.AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f) W b :=
  rfl

include hU hV in
/-- **The degree-one comparison on a universal differential.** The `Γ(X, U)`-linear equivalence
`Ω[Γ(X,U)⁄Γ(S,V)] ≅ Γ(Ω_{X/S}, U)` carries `d a` to the universal relative differential of `a`.
This is `Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d`, read on the
equivalence that `kaehlerSectionsEquiv` builds from that map. -/
theorem kaehlerSectionsEquiv_d (a : Γ(X, U)) :
    kaehlerSectionsEquiv f hU hV e (CommRingCat.KaehlerDifferential.d a) =
      (Scheme.Hom.universalRelativeDerivation f).d a :=
  AffineDifferentials.kaehlerToSections_d f V U e a

include hU hV in
/-- **The degreewise comparison on an affine open, on a wedge of universal differentials.** Its
inverse carries `d a₁ ∧ ⋯ ∧ d a_p` to the ordered product of the exact one-forms of the `a_i`
over `U`.

These wedges span `⋀^p_{Γ(X,U)} Ω[Γ(X,U)⁄Γ(S,V)]`, so this determines the comparison in every
degree. It is the affine-open analogue of
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.differentialFormsSectionsIso_ιMulti_d`. -/
theorem formsSectionsIso_inv_ιMulti_d (p : ℕ) (a : Fin p → Γ(X, U)) :
    (formsSectionsIso f hU hV e p).inv
        (exteriorPower.ιMulti Γ(X, U) p fun i ↦
          CommRingCat.KaehlerDifferential.d (a i)) =
      (Scheme.Hom.deRhamAlgebras f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        (op U) p fun i ↦
          _root_.AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f)
            (op U) (a i) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentials f
  change (Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso
      (Scheme.Hom.relativeDifferentials f) hU
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) p).inv
    (exteriorPower.map p (kaehlerSectionsEquiv f hU hV e).toLinearMap _) = _
  rw [exteriorPower.map_apply_ιMulti,
    Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso_inv_ιMulti,
    (Scheme.Hom.deRhamAlgebras
      f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft_eq_homogeneousProd]
  exact congrArg _ (funext fun i ↦ (congrArg _ (kaehlerSectionsEquiv_d f hU hV e (a i))).trans
    (exteriorGenerator_d_eq_exactOne f (op U) (a i)))

include hU hV in
/-- **The differential square of the affine-open de Rham comparison, in every degree.** On the
image of the generator `a₀ · (d a₁ ∧ ⋯ ∧ d a_p)` of `⋀^p_{Γ(X,U)} Ω[Γ(X,U)⁄Γ(S,V)]`, the de Rham
differential of `Ω^•_{X/S}` read over `U` is the image of `d a₀ ∧ d a₁ ∧ ⋯ ∧ d a_p`.

These generators span the source over `Γ(S, V)`, so this is the whole degree-`p` square of
[Stacks, Tag 0FLW] over a pair of affine opens, for every `p`. It is the affine-open analogue of
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamComplex_d_sectionsIso`, and it is that
proof verbatim with the top open replaced by `U`, because
`AlgebraicGeometry.Scheme.Hom.deRhamComplex_d_homogeneousProdLeft` is already stated at an
arbitrary open. -/
theorem deRhamComplex_d_formsSectionsIso (p : ℕ) (a : Fin (p + 1) → Γ(X, U)) :
    ((f.deRhamComplex.d p (p + 1)).val.app (op U))
        ((formsSectionsIso f hU hV e p).inv
          (a 0 • exteriorPower.ιMulti Γ(X, U) p fun i ↦
            CommRingCat.KaehlerDifferential.d (a i.succ))) =
      (formsSectionsIso f hU hV e (p + 1)).inv
        (exteriorPower.ιMulti Γ(X, U) (p + 1) fun i ↦
          CommRingCat.KaehlerDifferential.d (a i)) := by
  rw [map_smul, formsSectionsIso_inv_ιMulti_d, formsSectionsIso_inv_ιMulti_d]
  exact Scheme.Hom.deRhamComplex_d_homogeneousProdLeft f (op U) p a

end Stacks.AlgebraicGeometry.AffineOpenDeRham

end
