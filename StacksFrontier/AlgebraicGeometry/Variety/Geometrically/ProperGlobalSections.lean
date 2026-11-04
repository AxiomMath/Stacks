module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.GeomConnectedFibres.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# Constant global functions on a proper scheme over a field

For a proper geometrically reduced scheme over a field, having only the constants as global
regular functions is the same as being geometrically connected. If the scheme is moreover
geometrically normal, these conditions are also equivalent to geometric irreducibility and to
geometric integrality.

## Main results

* `AlgebraicGeometry.isIso_globalSections_iff_geometricallyConnected`: a proper geometrically
  reduced scheme over a field has only constant global functions exactly when it is
  geometrically connected.
* `AlgebraicGeometry.isIso_globalSections_of_geometricallyIntegral`: a proper geometrically
  integral scheme over a field has only constant global functions.
* `AlgebraicGeometry.isIso_globalSections_tfae_geometricallyConnected_irreducible_integral`: for a
  proper geometrically normal scheme over a field, having only constant global functions,
  geometric connectedness, geometric irreducibility and geometric integrality are equivalent.

## Implementation notes

The equality `H⁰(X, 𝒪_X) = k` is expressed canonically by saying that the homomorphism from `k`
to `Γ(X, ⊤)` induced by the structure morphism is an isomorphism; the standard identification
`Γ(Spec k, 𝒪) ≅ k` is part of that map.

In the normal case the step from geometric connectedness to geometric irreducibility goes through
the decomposition of a Noetherian normal scheme as a finite coproduct of normal integral schemes
(Tag 033M): a connected finite coproduct of irreducible schemes has exactly one summand.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0FD2](https://stacks.math.columbia.edu/tag/0FD2)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty
open Stacks.AlgebraicGeometry.ProperGeomConnected Stacks.AlgebraicGeometry.ProperSectionsGeom

universe u

namespace AlgebraicGeometry

/-- A proper geometrically reduced scheme over a field has only constant global functions
exactly when it is geometrically connected. -/
@[stacks 0FD2]
theorem isIso_globalSections_iff_geometricallyConnected
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [GeometricallyReduced f] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ↔ GeometricallyConnected f := by
  refine ⟨fun h => ?_, fun _ => isIso_globalSections_of_isProper k f⟩
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv _
  have : MorphismProperty.RespectsIso (@GeometricallyConnected) := by
    rw [GeometricallyConnected.eq_geometrically]
    infer_instance
  apply (cancel_right_of_respectsIso (P := @GeometricallyConnected) f (Spec (.of k)).toSpecΓ).mp
  simpa only [Scheme.toSpecΓ_naturality f] using
    (cancel_right_of_respectsIso (P := @GeometricallyConnected) _ _).mpr
      (geometricallyConnected_toSpecΓ_of_isProper_over_field k X f)

/-- The canonical homomorphism from a field to the global sections of a geometrically integral
proper scheme over that field is an isomorphism. -/
@[stacks 0BUG "clause (8): for a GEOMETRICALLY INTEGRAL proper scheme over a field k, the global \
sections are k. The equality A = k is stated canonically, as the induced homomorphism from k to \
the global sections being an isomorphism. The source deduces this clause from clause (7): a \
geometrically integral morphism is geometrically reduced, and geometrically connected because \
every base change of it has an integral, hence irreducible, hence connected, underlying space."]
theorem isIso_globalSections_of_geometricallyIntegral
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [GeometricallyIntegral f] [IsProper f] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  have : GeometricallyConnected f := ⟨fun _ _ y Z fst snd h => by
    have := (‹GeometricallyIntegral f›).geometrically_isIntegral y fst snd h
    infer_instance⟩
  exact isIso_globalSections_of_isProper k f

/-- A connected finite coproduct of irreducible schemes is irreducible: the index set of the
coproduct must be a single point. -/
private lemma irreducibleSpace_of_connectedSpace_coproduct
    {ι : Type u} (Y : ι → Scheme.{u}) [∀ i, IrreducibleSpace (Y i)]
    [ConnectedSpace (∐ Y : Scheme.{u})] : IrreducibleSpace (∐ Y : Scheme.{u}) := by
  have : ConnectedSpace (Σ i, Y i) :=
    (AlgebraicGeometry.sigmaMk Y).connectedSpace_iff.mpr inferInstance
  obtain ⟨i, _, _, heq⟩ := Sigma.isConnected_iff.mp
    (isConnected_univ : IsConnected (Set.univ : Set (Σ i, Y i)))
  have hi (j : ι) : j = i := by
    obtain ⟨y, _, hxy⟩ := heq ▸ Set.mem_univ (⟨j, Nonempty.some inferInstance⟩ : Σ i, Y i)
    exact congrArg Sigma.fst hxy.symm
  have hsurj : Function.Surjective (fun x : Y i => (⟨i, x⟩ : Σ j, Y j)) := by
    rintro ⟨j, x⟩
    cases hi j
    exact ⟨x, rfl⟩
  exact (AlgebraicGeometry.sigmaMk Y).irreducibleSpace_iff.mp
    (hsurj.irreducibleSpace (continuous_sigmaMk (i := i)))

/-- For a proper geometrically normal scheme over a field, having only constant global
functions, geometric connectedness, geometric irreducibility, and geometric integrality are
equivalent. -/
@[stacks 0FD3]
theorem isIso_globalSections_tfae_geometricallyConnected_irreducible_integral
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (hnormal : IsGeometricallyNormal f) :
    List.TFAE [
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop),
      GeometricallyConnected f,
      GeometricallyIrreducible f,
      GeometricallyIntegral f] := by
  have : GeometricallyReduced f :=
    (geometricallyReduced_iff_forall_isGeometricallyReducedAt f).2
      fun x K _ _ x' hx' => (hnormal x K x' hx').isReduced
  have hnormal' : ∀ (K : Type u) [Field K] [Algebra k K],
      IsNormal (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    ((geometricallyNormal_tfae k X f).out 1 2).mp hnormal
  tfae_have 1 ↔ 2 := isIso_globalSections_iff_geometricallyConnected k f
  tfae_have 2 → 3 := by
    intro hc
    refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ => ?_⟩
    let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
    have : ConnectedSpace (pullback f g : Scheme.{u}) :=
      (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mp
        hc.geometrically_connectedSpace) K
    have : IsLocallyNoetherian (pullback f g) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
    have : CompactSpace (pullback f g : Scheme.{u}) :=
      (quasiCompact_iff_compactSpace (pullback.snd f g)).mp inferInstance
    have : IsNoetherian (pullback f g) := ⟨⟩
    obtain ⟨ι, _, Y, _, hintY, ⟨e⟩⟩ :=
      (isNormal_iff_exists_iso_finite_coproduct_integral_normal _).mp (hnormal' K)
    have : ∀ i, IsIntegral (Y i) := hintY
    have : ConnectedSpace (∐ Y : Scheme.{u}) :=
      e.hom.homeomorph.connectedSpace_iff.mp inferInstance
    exact e.hom.homeomorph.irreducibleSpace_iff.mpr (irreducibleSpace_of_connectedSpace_coproduct Y)
  tfae_have 3 → 4 := fun _ =>
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  tfae_have 4 → 2 := fun _ =>
    ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ =>
      ((geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mp
        (GeometricallyIrreducible.geometrically_irreducibleSpace (f := f))) K).connectedSpace⟩
  tfae_finish

end AlgebraicGeometry
