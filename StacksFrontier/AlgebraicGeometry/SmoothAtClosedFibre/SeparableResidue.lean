module

public import StacksFrontier.AlgebraicGeometry.NumericalCriterion.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.SmoothAtClosedFibre.Basic
public import StacksFrontier.RingTheory.FormallySmooth.Field
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness at a point where the stalk map is flat and weakly unramified

A morphism locally of finite presentation is smooth at a point `x` as soon as the induced map of
local rings is flat, carries the maximal ideal of `𝒪_{S,f x}` onto the maximal ideal of
`𝒪_{X,x}`, and induces a formally smooth — for instance separable — extension of residue fields.

## Main definitions

* `Stacks.SmoothAtClosedFibre.residueFieldIsoFibreStalk`: the local ring of the
  scheme-theoretic fibre at `x` is the residue field `κ(x)` when the stalk map is weakly
  unramified at `x`.

## Main results

* `Stacks.SmoothAtClosedFibre.smoothAt_of_flat_of_formallySmooth_kappaToFibreStalk`: flatness of
  the stalk map together with formal smoothness of the local ring of the fibre over `κ(f x)`
  gives smoothness at `x`.
* `Stacks.SmoothAtClosedFibre.smoothAt_of_flat_of_formallySmooth_residueFieldMap`: the same
  conclusion from weak unramifiedness of the stalk map and formal smoothness of `κ(f x) → κ(x)`.
* `Stacks.SmoothAtClosedFibre.smoothAt_of_mem_genericPoints_of_formallySmooth_residueFieldMap`:
  at a generic point lying over a generic point of a reduced base, only formal smoothness of the
  residue field extension is needed.

## Implementation notes

The fibre dictionary of `StacksFrontier.AlgebraicGeometry.SmoothAtClosedFibre.Basic` presents the
`κ(f x)`-algebra structure of the local ring of the fibre as
`Stacks.SmoothAtClosedFibre.kappaToFibreStalk`; condition (2) of Tag 01V9 is read on it. Weak
unramifiedness turns `AlgebraicGeometry.quotientStalkEquivFiberStalk` into an isomorphism onto
the residue field, under which that algebra structure becomes
`AlgebraicGeometry.Scheme.Hom.residueFieldMap`.

Formal smoothness is taken as the hypothesis rather than separability, because it is the shape in
which Tag 09E7 delivers the conclusion for an extension of discrete valuation rings; the
separable case is `Algebra.FormallySmooth.iff_isSeparableExtension`.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)
* [Stacks Project, Tag 09E7](https://stacks.math.columbia.edu/tag/09E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SmoothAtClosedFibre

/-- A ring homomorphism out of a ring which is a field is flat. -/
theorem flat_of_isField_source {R T : Type u} [CommRing R] [CommRing T] (φ : R →+* T)
    (hR : IsField R) : φ.Flat := by
  let : Field R := hR.toField
  rw [RingHom.Flat]
  let : Algebra R T := φ.toAlgebra
  infer_instance

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- **The local ring of the fibre is the residue field at a weakly unramified point.** If the
stalk map of `f` at `x` carries the maximal ideal of `𝒪_{S,f x}` onto the maximal ideal of
`𝒪_{X,x}`, then the local ring of the scheme-theoretic fibre of `f` through `x` is `κ(x)`. -/
def residueFieldIsoFibreStalk
    (hm : Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    X.residueField x ≅ (f.fiber (f x)).presheaf.stalk (f.asFiber x) :=
  RingEquiv.toCommRingCatIso
    ((Ideal.quotEquivOfEq hm.symm).trans (quotientStalkEquivFiberStalk f x))

/-- **The `κ(f x)`-structure on the local ring of the fibre is the residue field extension.**
At a weakly unramified point the action of `κ(f x)` on the fibre stalk is
`AlgebraicGeometry.Scheme.Hom.residueFieldMap` followed by
`Stacks.SmoothAtClosedFibre.residueFieldIsoFibreStalk`. -/
theorem kappaToFibreStalk_eq_residueFieldMap_comp
    (hm : Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    kappaToFibreStalk f x =
      f.residueFieldMap x ≫ (residueFieldIsoFibreStalk f x hm).hom := by
  have hepi : Epi (S.residue (f x)) :=
    ConcreteCategory.epi_of_surjective _ IsLocalRing.residue_surjective
  rw [← cancel_epi (S.residue (f x)), residue_kappaToFibreStalk f x,
    ← Category.assoc (S.residue (f x)) (f.residueFieldMap x),
    Scheme.residue_residueFieldMap f x, Category.assoc]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun t => ?_)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact (quotientStalkEquivFiberStalk_mk f x _).symm

/-- The residue field extension and the `κ(f x)`-algebra structure of the local ring of the
fibre are isomorphic arrows at a weakly unramified point. -/
def arrowIsoResidueFieldMapKappaToFibreStalk
    (hm : Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    Arrow.mk (f.residueFieldMap x) ≅ Arrow.mk (kappaToFibreStalk f x) :=
  Arrow.isoMk (Iso.refl _) (residueFieldIsoFibreStalk f x hm)
    (by simpa using kappaToFibreStalk_eq_residueFieldMap_comp f x hm)

/-- **Condition (2) of Tag 01V9, read on the stalk map.** A morphism locally of finite
presentation is smooth at `x` as soon as its stalk map at `x` is flat and the local ring of the
scheme-theoretic fibre through `x` is formally smooth over `κ(f x)`. -/
@[sga "3 XV 1.1" "partial"]
theorem smoothAt_of_flat_of_formallySmooth_kappaToFibreStalk [LocallyOfFinitePresentation f]
    (hflat : (f.stalkMap x).hom.Flat)
    (hsm : (kappaToFibreStalk f x).hom.FormallySmooth) :
    InfinitesimalLifting.SmoothAt f x := by
  have hfp : LocallyOfFinitePresentation (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFinitePresentation
      (pullback.snd f (S.fromSpecResidueField (f x))))
  have hsl : ((f.fiberToSpecResidueField (f x)).stalkMap (f.asFiber x)).hom.FormallySmooth :=
    (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (arrowIso_kappaToFibreStalk f x)).mp hsm
  exact Stacks.Tag01V9Closure.condition2_imp_condition1 f x
    ⟨hflat, (Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus
      (f.fiberToSpecResidueField (f x)) (f.asFiber x)).mpr
      (Scheme.Hom.mem_smoothLocus.mpr hsl)⟩

/-- **Smoothness at a flat, weakly unramified point with formally smooth residue extension.**
If the stalk map of a morphism locally of finite presentation is flat at `x`, carries the
maximal ideal of `𝒪_{S,f x}` onto the maximal ideal of `𝒪_{X,x}`, and induces a formally smooth
extension of residue fields, then the morphism is smooth at `x`.

For an extension of discrete valuation rings the last two hypotheses together are formal
smoothness in the adic topology of the maximal ideal, by Tag 09E7. -/
@[ega "IV 17.5.1" "b ⇒ a when m_{Y"]
theorem smoothAt_of_flat_of_formallySmooth_residueFieldMap [LocallyOfFinitePresentation f]
    (hflat : (f.stalkMap x).hom.Flat)
    (hm : Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hres : (f.residueFieldMap x).hom.FormallySmooth) :
    InfinitesimalLifting.SmoothAt f x :=
  smoothAt_of_flat_of_formallySmooth_kappaToFibreStalk f x hflat
    ((RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (arrowIsoResidueFieldMapKappaToFibreStalk f x hm)).mp hres)

/-- **Smoothness at a generic point lying over a generic point.** For a morphism locally of
finite presentation between reduced schemes, smoothness at a generic point of the source lying
over a generic point of the target follows from formal smoothness of the residue field
extension alone.

Both local rings are then fields, so flatness and weak unramifiedness are automatic. -/
theorem smoothAt_of_mem_genericPoints_of_formallySmooth_residueFieldMap
    [LocallyOfFinitePresentation f] [IsReduced X] [IsReduced S]
    (hx : x ∈ genericPoints X) (hfx : f x ∈ genericPoints S)
    (hres : (f.residueFieldMap x).hom.FormallySmooth) :
    InfinitesimalLifting.SmoothAt f x := by
  have hSfield := isField_stalk_of_closure_mem_irreducibleComponents S (f x) hfx
  have hXfield := isField_stalk_of_closure_mem_irreducibleComponents X x hx
  refine smoothAt_of_flat_of_formallySmooth_residueFieldMap f x ?_ ?_ hres
  · exact flat_of_isField_source (f.stalkMap x).hom hSfield
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hSfield,
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hXfield, Ideal.map_bot]

end Stacks.SmoothAtClosedFibre

end
