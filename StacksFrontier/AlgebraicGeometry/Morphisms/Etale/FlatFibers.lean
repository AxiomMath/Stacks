module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.FiberCriterion

/-!
# Étale morphisms from flatness and their fibres

A flat, locally finitely presented morphism of schemes is étale if each of its fibres is a
disjoint union of spectra of finite separable extensions of the corresponding residue field.

The hypothesis makes every fibre étale, hence smooth, over the residue field of its base point,
so the morphism is smooth by the fibrewise criterion for smoothness; it also makes the morphism
unramified by the fibrewise criterion for unramifiedness. Being étale at a point is being smooth
and unramified there.

## Main results

* `AlgebraicGeometry.etale_of_flat_of_fibers_finite_separable` gives the fibrewise criterion for
  an étale morphism.

## Implementation notes

The disjoint union is represented by a coproduct of spectra. The isomorphism of a fibre with
this coproduct respects its structure morphism to the spectrum of the residue field. Finiteness
and separability of each field extension are expressed by `Module.Finite` and
`Algebra.IsSeparable`.

## References

* [Stacks Project, Tag 02GM](https://stacks.math.columbia.edu/tag/02GM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A flat, locally finitely presented morphism with fibres that are disjoint unions of spectra
of finite separable extensions of residue fields is étale. -/
@[stacks 02GM,
  ega "IV 17.6.2" "c') => a)",
  ega "IV 18.2.3" "a') ⇒ a)",
  sga "1 IX 1.2" "converse direction", sga "4 VII 1.1" "flat+fibers => étale"]
public theorem etale_of_flat_of_fibers_finite_separable
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S,
      ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i))
        (_ : ∀ i, Algebra (S.residueField s) (K i))
        (_ : ∀ i, Module.Finite (S.residueField s) (K i))
        (_ : ∀ i, Algebra.IsSeparable (S.residueField s) (K i))
        (e : f.fiber s ≅ ∐ fun i ↦ Spec (.of (K i))),
        e.hom ≫ Sigma.desc (fun i ↦
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (K i)))) =
            f.fiberToSpecResidueField s) :
    Etale f := by
  let : Smooth f := Smooth.of_smooth_fiberToSpecResidueField f fun s => by
    let : Etale (f.fiberToSpecResidueField s) :=
      (etale_iff_iso_coproduct_spectra_finite_separable
        (S.residueField s) (f.fiberToSpecResidueField s)).2 (h s)
    infer_instance
  let : Unramified f := unramified_of_fibres f h
  refine (etale_iff_forall_etaleAt f).2 fun x => (etaleAt_iff_smoothAt_and_unramifiedAt f x).2 ?_
  obtain ⟨V, hV, U, hU, hxU, hUV, hs⟩ := Smooth.exists_isStandardSmooth f x
  exact ⟨(InfinitesimalLifting.smoothAt_iff_exists_affine f x).2
    ⟨U, V, hU, hV, hxU, hUV, hs.smooth⟩, Unramified.unramifiedAt x⟩

end AlgebraicGeometry
