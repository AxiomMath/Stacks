module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Geometric irreducibility over a point passes to and from a dense open

Let `g : X ⟶ S` be a morphism of schemes whose target is the spectrum of a field, and let
`j : U ⟶ X` be an open immersion with dense image. Then `X` is geometrically irreducible over
`S` if and only if `U` is.

Mathlib has the direction which restricts to an open subscheme; the direction which extends from
a dense open is proved here. Over the spectrum of a field every morphism is universally open, so
the projection of a base change `X ×_S Spec K ⟶ X` is an open map, and the preimage of a dense
set under an open map is dense. The base change of `U` is therefore an irreducible dense subset
of the base change of `X`, which makes the latter irreducible.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_of_dense_isOpenImmersion`: geometric
  irreducibility of a dense open over the spectrum of a field extends to the ambient scheme.
* `AlgebraicGeometry.geometricallyIrreducible_of_dense_open`: the same for an open subscheme.
* `AlgebraicGeometry.geometricallyIrreducible_dense_open_comp_iff`: the resulting equivalence.
* `AlgebraicGeometry.geometricallyIrreducible_fiberToSpecResidueField_of_dense_open`: the form
  used for the fibres of a morphism, where the open is cut out of the total space.

## Implementation notes

The hypothesis on the target is `IsIntegral S` together with `Subsingleton S`, which is how
Mathlib states "the spectrum of a field" for the purpose of universal openness; both hold for
`Spec (Y.residueField y)`, the target of
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`.

The main statement is in terms of an arbitrary open immersion rather than of an open subscheme,
because the opens that arise in the fibres of a morphism are the base changes of opens of the
total space, which are open immersions not presented as open subschemes.

The extension direction needs no nonemptiness hypothesis: the dense open being geometrically
irreducible over a nonempty target already forces it to be nonempty. The restriction direction
does, since a morphism between empty schemes is vacuously geometrically irreducible; it appears
as `Nonempty X` in the equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme which is geometrically irreducible over the spectrum of a field on a dense open
subscheme is geometrically irreducible. -/
public theorem geometricallyIrreducible_of_dense_isOpenImmersion {U X S : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : X ⟶ S) [IsIntegral S] [Subsingleton S]
    (hj : Dense (Set.range j)) (h : GeometricallyIrreducible (j ≫ g)) :
    GeometricallyIrreducible g := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  have hpOpen := Scheme.Hom.isOpenMap (pullback.fst g x)
  have hirrUp : IrreducibleSpace ↥(pullback j (pullback.fst g x)) := by
    have hbase : IrreducibleSpace ↥(pullback (j ≫ g) x) :=
      pullback_of_geometrically h.geometrically_irreducibleSpace K x
    exact (pullbackRightPullbackFstIso g x j).hom.homeomorph.irreducibleSpace_iff.mpr hbase
  have hrange : IsIrreducible (Set.range (pullback.snd j (pullback.fst g x))) := by
    have h1 := (IrreducibleSpace.isIrreducible_univ ↥(pullback j (pullback.fst g x))).image
      (pullback.snd j (pullback.fst g x))
      (pullback.snd j (pullback.fst g x)).continuous.continuousOn
    simpa using h1
  rw [IsOpenImmersion.range_pullbackSnd] at hrange
  have hdense : Dense ((pullback.fst g x ⁻¹ᵁ j.opensRange : (pullback g x).Opens) :
      Set ↥(pullback g x)) := hj.preimage hpOpen
  have hcl := hrange.closure
  rw [hdense.closure_eq] at hcl
  exact (irreducibleSpace_def _).mpr (by simpa using hcl)

/-- A scheme which is geometrically irreducible over the spectrum of a field on a dense open
subscheme is geometrically irreducible. -/
public theorem geometricallyIrreducible_of_dense_open {X S : Scheme.{u}} (g : X ⟶ S)
    [IsIntegral S] [Subsingleton S] (U : X.Opens) (hU : Dense (U : Set X))
    (h : GeometricallyIrreducible (U.ι ≫ g)) : GeometricallyIrreducible g :=
  geometricallyIrreducible_of_dense_isOpenImmersion U.ι g (by rwa [U.range_ι]) h

/-- Over the spectrum of a field, a nonempty scheme is geometrically irreducible exactly when
one of its dense open subschemes is. -/
public theorem geometricallyIrreducible_dense_open_comp_iff {X S : Scheme.{u}} (g : X ⟶ S)
    [IsIntegral S] [Subsingleton S] [Nonempty X] (U : X.Opens) (hU : Dense (U : Set X)) :
    GeometricallyIrreducible (U.ι ≫ g) ↔ GeometricallyIrreducible g := by
  refine ⟨geometricallyIrreducible_of_dense_open g U hU, fun h ↦ ?_⟩
  have hUne : Nonempty U := Set.nonempty_coe_sort.mpr hU.nonempty
  have : Surjective (U.ι ≫ g) := by
    constructor
    intro s
    obtain ⟨u⟩ := hUne
    exact ⟨u, Subsingleton.elim _ _⟩
  infer_instance

/-- If an open subscheme of the total space meets a fibre in a dense open which is
geometrically irreducible over the residue field of that point, then the fibre itself is
geometrically irreducible. -/
public theorem geometricallyIrreducible_fiberToSpecResidueField_of_dense_open
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (U : X.Opens)
    (hU : Dense ((f.fiberι y ⁻¹ᵁ U : (f.fiber y).Opens) : Set ↥(f.fiber y)))
    (h : GeometricallyIrreducible
      ((f.fiberι y ⁻¹ᵁ U).ι ≫ f.fiberToSpecResidueField y)) :
    GeometricallyIrreducible (f.fiberToSpecResidueField y) :=
  geometricallyIrreducible_of_dense_open (f.fiberToSpecResidueField y) _ hU h

end AlgebraicGeometry

end
