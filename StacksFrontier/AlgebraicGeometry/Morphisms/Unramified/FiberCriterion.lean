module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.FiberMaximalIdeal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Unramified morphisms from their fibres

A morphism whose fibres are disjoint unions of spectra of finite separable extensions of the
corresponding residue fields is unramified when it is locally of finite type, and G-unramified
when it is locally of finite presentation.

The hypothesis says exactly that every fibre is étale over the residue field of its base point,
so at each point of the source the residue-field extension is separable and the maximal ideal of
the base local ring generates the maximal ideal upstairs. Those two facts are Mathlib's
criterion for formal unramifiedness of a local homomorphism, and formal unramifiedness is local
on prime spectra, so it propagates from the stalks to the morphism.

## Main results

* `AlgebraicGeometry.formallyUnramified_of_fibres` is the fibrewise criterion for formal
  unramifiedness.
* `AlgebraicGeometry.unramified_of_fibres` is the fibrewise criterion for unramifiedness.
* `AlgebraicGeometry.gUnramified_of_fibres` is the fibrewise criterion for G-unramifiedness.

## Implementation notes

The decomposition of each fibre is an isomorphism over the spectrum of the residue field. The
structure maps on its components are those induced by the displayed algebra structures.

The fibre hypothesis alone gives formal unramifiedness; the two conclusions differ only in the
finiteness condition carried alongside it, which is `LocallyOfFiniteType` for unramifiedness and
`LocallyOfFinitePresentation` for G-unramifiedness. Both are obtained from the conjunctive
characterizations in
`StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties`. The formal-unramifiedness proof
needs essential finite type of the stalk maps, so it is stated under `LocallyOfFiniteType`, which
the finite-presentation case supplies by instance.

## References

* [Stacks Project, Tag 02G8](https://stacks.math.columbia.edu/tag/02G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism locally of finite type whose fibres are disjoint unions of spectra of finite
separable extensions of the corresponding residue fields is formally unramified. -/
@[ega "IV 17.4.2" "Implication d′ ⇒ a", sga "3 XI 1.3" "(i) e) ⇒ a)"]
public theorem formallyUnramified_of_fibres {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (h : ∀ s : S,
      ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i))
        (_ : ∀ i, Algebra (S.residueField s) (K i))
        (_ : ∀ i, Module.Finite (S.residueField s) (K i))
        (_ : ∀ i, Algebra.IsSeparable (S.residueField s) (K i))
        (e : f.fiber s ≅ ∐ fun i ↦ Spec (.of (K i))),
        e.hom ≫ Sigma.desc (fun i ↦
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (K i)))) =
            f.fiberToSpecResidueField s) :
    FormallyUnramified f := by
  have hfib : ∀ s : S, Etale (f.fiberToSpecResidueField s) := fun s ↦
    (etale_iff_iso_coproduct_spectra_finite_separable
      (S.residueField s) (f.fiberToSpecResidueField s)).2 (h s)
  have hstalk : ∀ x : X, (f.stalkMap x).hom.FormallyUnramified := by
    intro x
    algebraize [(f.stalkMap x).hom]
    have : Algebra.EssFiniteType (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
      rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
      exact LocallyOfFiniteType.stalkMap f x
    have : IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
    let : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    have : Algebra.IsSeparable
        (IsLocalRing.ResidueField <| S.presheaf.stalk (f x))
        (IsLocalRing.ResidueField <| X.presheaf.stalk x) := by
      convert! isSeparable_residueField_of_etale_fibers f hfib x
      refine Algebra.algebra_ext _ _ fun y ↦ ?_
      obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
      rfl
    exact Algebra.FormallyUnramified.of_map_maximalIdeal
      (map_maximalIdeal_eq_of_etale_fibers f hfib x)
  exact HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime hstalk

/-- A morphism locally of finite type whose fibres are disjoint unions of spectra of finite
separable extensions of the corresponding residue fields is unramified. -/
@[stacks 02G8 "part (2): a morphism locally of finite type all of whose fibres are disjoint
unions of spectra of finite separable extensions of the residue field of the base point is
unramified", ega "IV 17.4.2" "Implication d′ ⇒ a", sga "3 XI 1.3" "(i)(e)⇒(a)"]
public theorem unramified_of_fibres {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (h : ∀ s : S,
      ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i))
        (_ : ∀ i, Algebra (S.residueField s) (K i))
        (_ : ∀ i, Module.Finite (S.residueField s) (K i))
        (_ : ∀ i, Algebra.IsSeparable (S.residueField s) (K i))
        (e : f.fiber s ≅ ∐ fun i ↦ Spec (.of (K i))),
        e.hom ≫ Sigma.desc (fun i ↦
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (K i)))) =
            f.fiberToSpecResidueField s) :
    Unramified f :=
  (unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mpr
    ⟨inferInstance, formallyUnramified_of_fibres f h⟩

/-- A morphism locally of finite presentation whose fibres are disjoint unions of spectra of
finite separable extensions of the corresponding residue fields is G-unramified. -/
@[stacks 02G8 "part (3): a morphism locally of finite presentation all of whose fibres are
disjoint unions of spectra of finite separable extensions of the residue field of the base point
is G-unramified", ega "IV 17.4.2" "Implication d′ ⇒ a", sga "3 XI 1.3" "(i)(e)⇒(a)"]
public theorem gUnramified_of_fibres {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f]
    (h : ∀ s : S,
      ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i))
        (_ : ∀ i, Algebra (S.residueField s) (K i))
        (_ : ∀ i, Module.Finite (S.residueField s) (K i))
        (_ : ∀ i, Algebra.IsSeparable (S.residueField s) (K i))
        (e : f.fiber s ≅ ∐ fun i ↦ Spec (.of (K i))),
        e.hom ≫ Sigma.desc (fun i ↦
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (K i)))) =
            f.fiberToSpecResidueField s) :
    GUnramified f :=
  (gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified f).mpr
    ⟨inferInstance, formallyUnramified_of_fibres f h⟩

end AlgebraicGeometry
