module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap

/-!
# An étale separated morphism with geometrically irreducible fibres is an isomorphism

A morphism which is étale and separated and all of whose fibres are geometrically irreducible is
an isomorphism. Over a field the statement is the structure theory of étale algebras: an étale
scheme over `κ` is a disjoint union of spectra of finite separable extensions, and geometric
irreducibility cuts that down to `Spec κ` itself. The proof given here avoids the structure
theory: a separated étale morphism has a diagonal which is both an open and a closed immersion,
so over an irreducible base its range is a nonempty clopen subset of the irreducible scheme
`X ×_S X` and therefore everything; hence the morphism is a monomorphism, and a flat
monomorphism locally of finite presentation is an open immersion, which together with the
surjectivity that geometric irreducibility already provides makes it an isomorphism.

The general case follows fibre by fibre: each fibre is an isomorphism onto the spectrum of the
residue field, which is exactly injectivity on points together with triviality of the residue
field extensions, i.e. universal injectivity by Stacks 01S4. Stacks 02LC then makes the morphism
an open immersion and surjectivity makes it an isomorphism.

This is the input to the base case `n = 0` of the induction in the first proof of Stacks 05I5:
there `X ⟶ S` is smooth of relative dimension `0` — equivalently étale — between affine schemes,
with geometrically integral fibres, and the source concludes `X = S` from Stacks 02LC and the
closed point of the local scheme `S` being in the image. The statement below is stronger: no
locality of the base is needed, because geometric irreducibility of *every* fibre already forces
surjectivity.

## Main results

* `AlgebraicGeometry.isIso_of_etale_of_isSeparated_of_geometricallyIrreducible`: an étale
  separated morphism with geometrically irreducible fibres is an isomorphism.
* `AlgebraicGeometry.isIso_fiberToSpecResidueField_of_etale_of_isSeparated`: each of its fibres
  is the spectrum of the residue field of its image point.
* `AlgebraicGeometry.isIso_residueFieldMap_of_isIso_fiberToSpecResidueField`: a morphism whose
  fibre through a point is the spectrum of the residue field of the image induces an isomorphism
  on the residue field at that point. This step needs no hypothesis on the morphism.
* `AlgebraicGeometry.universallyInjective_of_etale_of_isSeparated_of_geometricallyIrreducible`:
  the universal injectivity which feeds Stacks 02LC.
* `AlgebraicGeometry.isIso_of_smoothOfRelativeDimension_zero_of_geometricallyIntegral_fibers`:
  the form in which the base case of Stacks 05I5 uses it, with the hypotheses of an elementary
  dévissage of relative dimension `0` — smoothness of relative dimension `0`, affine source and
  target, and geometrically integral fibres stated fibre by fibre.

## Implementation notes

The hypothesis is `AlgebraicGeometry.GeometricallyIrreducible` rather than
`AlgebraicGeometry.GeometricallyIntegral`: an étale scheme over a field is automatically reduced,
so the reducedness half of integrality is not used. The weaker hypothesis is also the one that is
cheapest to supply, since `GeometricallyIntegral` implies it by instance.

Separatedness cannot be dropped: the affine line with a doubled origin is étale over the affine
line with irreducible — indeed one- or two-point — fibres and is not a monomorphism. In the
application the morphism is affine, hence separated.

## References

* [Stacks Project, Tag 02LC](https://stacks.math.columbia.edu/tag/02LC)
* [Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **An étale separated morphism with geometrically irreducible fibres over a one-point base is
an isomorphism.** The diagonal is an open immersion because the morphism is étale and a closed
immersion because it is separated, so its range is a nonempty clopen subset of the irreducible
scheme `X ×_S X`, hence all of it; the morphism is therefore a monomorphism, and a flat
monomorphism locally of finite presentation is an open immersion. Geometric irreducibility
supplies the surjectivity. -/
theorem isIso_of_etale_of_isSeparated_of_subsingleton (f : X ⟶ S) [Etale f] [IsSeparated f]
    [GeometricallyIrreducible f] [Subsingleton S] [Nonempty S] : IsIso f := by
  have hirrX : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
  have hirrP : IrreducibleSpace ↥(pullback f f) :=
    GeometricallyIrreducible.irreducibleSpace (pullback.snd f f) (pullback.snd f f).isOpenMap
  have hsurj : Surjective (pullback.diagonal f) := by
    refine ⟨?_⟩
    have hcl : IsClopen (Set.range (pullback.diagonal f).base) :=
      ⟨(pullback.diagonal f).isClosedEmbedding.isClosed_range,
        (pullback.diagonal f).isOpenEmbedding.isOpen_range⟩
    rw [← Set.range_eq_univ]
    exact hcl.eq_univ ⟨pullback.diagonal f (Nonempty.some hirrX.toNonempty), ⟨_, rfl⟩⟩
  have : Mono f := (pullback.isIso_diagonal_iff f).mp
    ((isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hsurj⟩)
  exact (isIso_iff_isOpenImmersion_and_surjective f).mpr
    ⟨IsOpenImmersion.of_flat_of_mono f, inferInstance⟩

/-- **The fibres of an étale separated morphism with geometrically irreducible fibres are the
spectra of the residue fields of their image points.** The fibre morphism is a base change of
`f`, so it is again étale and separated and geometrically irreducible, and its target is a
one-point scheme. -/
theorem isIso_fiberToSpecResidueField_of_etale_of_isSeparated (f : X ⟶ S) [Etale f]
    [IsSeparated f] [GeometricallyIrreducible f] (s : S) :
    IsIso (f.fiberToSpecResidueField s) := by
  have hpb : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f
      (S.fromSpecResidueField s) := IsPullback.of_hasPullback _ _
  have : Etale (f.fiberToSpecResidueField s) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb ‹Etale f›
  have : IsSeparated (f.fiberToSpecResidueField s) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb ‹IsSeparated f›
  exact isIso_of_etale_of_isSeparated_of_subsingleton (f.fiberToSpecResidueField s)

/-- Each fibre of an étale separated morphism with geometrically irreducible fibres has at most
one point. -/
theorem subsingleton_fiber_of_etale_of_isSeparated (f : X ⟶ S) [Etale f] [IsSeparated f]
    [GeometricallyIrreducible f] (s : S) : Subsingleton (f.fiber s) :=
  have := isIso_fiberToSpecResidueField_of_etale_of_isSeparated f s
  ⟨fun _ _ => (f.fiberToSpecResidueField s).injective (Subsingleton.elim _ _)⟩

/-- An étale separated morphism with geometrically irreducible fibres is injective on points: two
points with the same image lie in the same fibre, which has at most one point. -/
theorem injective_of_etale_of_isSeparated_of_geometricallyIrreducible (f : X ⟶ S) [Etale f]
    [IsSeparated f] [GeometricallyIrreducible f] : Function.Injective f := by
  intro x₁ x₂ hx
  obtain ⟨w₁, hw₁⟩ : x₁ ∈ Set.range (f.fiberι (f x₁)) := by
    rw [f.range_fiberι]
    rfl
  obtain ⟨w₂, hw₂⟩ : x₂ ∈ Set.range (f.fiberι (f x₁)) := by
    rw [f.range_fiberι]
    exact hx.symm
  have := subsingleton_fiber_of_etale_of_isSeparated f (f x₁)
  rw [← hw₁, ← hw₂, Subsingleton.elim w₁ w₂]

/-- If the fibre of `f` through `x` is the spectrum of the residue field of `f x`, then `f`
induces an isomorphism on the residue field at `x`. The square of
`AlgebraicGeometry.Scheme.Hom.fiber_fac` expresses the composite `κ(f x) ⟶ κ(x) ⟶ κ(w)`, for `w`
the point of the fibre over `x`, as a composite of two residue field maps which are isomorphisms
— the one of `Spec κ(f x) ⟶ S`, a preimmersion, and the one of the fibre morphism — and the
second factor `κ(x) ⟶ κ(w)` is an isomorphism because `f.fiberι` is a preimmersion. -/
theorem isIso_residueFieldMap_of_isIso_fiberToSpecResidueField (f : X ⟶ S) (x : X)
    [IsIso (f.fiberToSpecResidueField (f x))] : IsIso (f.residueFieldMap x) := by
  have h₁ : IsIso ((f.fiberι (f x)).residueFieldMap (f.asFiber x)) :=
    isIso_residueFieldMap_of_isPreimmersion _ _
  have h₂ : IsIso ((S.fromSpecResidueField (f x)).residueFieldMap
      (f.fiberToSpecResidueField (f x) (f.asFiber x))) :=
    isIso_residueFieldMap_of_isPreimmersion _ _
  have hRHS : IsIso ((f.fiberToSpecResidueField (f x) ≫
      S.fromSpecResidueField (f x)).residueFieldMap (f.asFiber x)) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' h₂ inferInstance
  rw [← Scheme.Hom.fiber_fac f (f x), Scheme.residueFieldMap_comp] at hRHS
  have hfin : IsIso (f.residueFieldMap (f.fiberι (f x) (f.asFiber x))) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ ((f.fiberι (f x)).residueFieldMap (f.asFiber x))
      h₁ hRHS
  rwa [Scheme.Hom.fiberι_asFiber] at hfin

/-- An étale separated morphism with geometrically irreducible fibres induces isomorphisms on
residue fields. -/
theorem isIso_residueFieldMap_of_etale_of_isSeparated_of_geometricallyIrreducible
    (f : X ⟶ S) [Etale f] [IsSeparated f] [GeometricallyIrreducible f] (x : X) :
    IsIso (f.residueFieldMap x) :=
  have := isIso_fiberToSpecResidueField_of_etale_of_isSeparated f (f x)
  isIso_residueFieldMap_of_isIso_fiberToSpecResidueField f x

/-- A bijective homomorphism of commutative rings is purely inseparable: every element of the
target is already in the image. -/
private theorem isPurelyInseparable_of_bijective {F E : Type u} [Field F] [Field E]
    (φ : F →+* E) (hφ : Function.Bijective φ) : RingHom.IsPurelyInseparable φ := by
  let _ : Algebra F E := φ.toAlgebra
  have hsurj : Function.Surjective (algebraMap F E) := hφ.2
  rw [show RingHom.IsPurelyInseparable φ = IsPurelyInseparable F E from rfl,
    isPurelyInseparable_iff]
  intro y
  obtain ⟨z, rfl⟩ := hsurj y
  exact ⟨isIntegral_algebraMap, fun _ => ⟨z, rfl⟩⟩

/-- **An étale separated morphism with geometrically irreducible fibres is universally
injective.** This is condition (3) of Stacks 01S4: it is injective on points, and its residue
field extensions are trivial, hence purely inseparable. -/
theorem universallyInjective_of_etale_of_isSeparated_of_geometricallyIrreducible
    (f : X ⟶ S) [Etale f] [IsSeparated f] [GeometricallyIrreducible f] :
    UniversallyInjective f := by
  have hc : Function.Injective f ∧
      ∀ x : X, (f.residueFieldMap x).hom.IsPurelyInseparable := by
    refine ⟨injective_of_etale_of_isSeparated_of_geometricallyIrreducible f, fun x => ?_⟩
    have := isIso_residueFieldMap_of_etale_of_isSeparated_of_geometricallyIrreducible f x
    exact isPurelyInseparable_of_bijective _
      ((ConcreteCategory.isIso_iff_bijective (f.residueFieldMap x)).mp inferInstance)
  exact ((tfae_universallyInjective f).out 3 1).mp hc

/-- **An étale separated morphism with geometrically irreducible fibres is an isomorphism.** It
is universally injective, hence an open immersion by Stacks 02LC, and geometric irreducibility of
the fibres makes it surjective. -/
theorem isIso_of_etale_of_isSeparated_of_geometricallyIrreducible (f : X ⟶ S) [Etale f]
    [IsSeparated f] [GeometricallyIrreducible f] : IsIso f :=
  have := universallyInjective_of_etale_of_isSeparated_of_geometricallyIrreducible f
  (isIso_iff_isOpenImmersion_and_surjective f).mpr ⟨inferInstance, inferInstance⟩

/-- **The base case of the induction in the first proof of Stacks 05I5.** A morphism of affine
schemes which is smooth of relative dimension `0` and has geometrically integral fibres is an
isomorphism.

This is the form in which the hypotheses occur in an elementary dévissage
(`AlgebraicGeometry.ElementaryDevissage`) of relative dimension `0`: the smooth morphism
`h : Y ⟶ V` has `AlgebraicGeometry.SmoothOfRelativeDimension 0`, affine source and target, and
geometrically integral fibres recorded fibre by fibre. Smoothness of relative dimension `0` is
étaleness, affineness of source and target makes the morphism affine hence separated, and
geometric integrality of every fibre is geometric integrality of the morphism. -/
theorem isIso_of_smoothOfRelativeDimension_zero_of_geometricallyIntegral_fibers
    (f : X ⟶ S) [SmoothOfRelativeDimension 0 f] [IsAffine X] [IsAffine S]
    (hfib : ∀ s : S, GeometricallyIntegral (f.fiberToSpecResidueField s)) : IsIso f := by
  have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero f).mpr inferInstance
  have : GeometricallyIntegral f :=
    (GeometricallyIntegral.iff_geometricallyIntegral_fiber f).mpr hfib
  have : IsAffineHom f := inferInstance
  have : IsSeparated f := inferInstance
  exact isIso_of_etale_of_isSeparated_of_geometricallyIrreducible f

end AlgebraicGeometry

end
