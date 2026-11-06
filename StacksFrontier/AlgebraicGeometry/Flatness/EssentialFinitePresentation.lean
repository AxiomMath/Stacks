module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.RingTheory.Flat.FibreCriterionNilpotent
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Essential finite presentation of local ring maps and of stalk maps

A ring map is *essentially of finite presentation* when its target is, as an algebra over the
source, a localization of an algebra of finite presentation; this is
`RingHom.EssentiallyOfFinitePresentation`, the Stacks Project's Tag 00QM (2).

This file records the two facts needed to feed a scheme morphism into the fibrewise criteria of
flatness, whose hypotheses are about local rings:

* the class of ring maps essentially of finite presentation is invariant under isomorphisms of
  the source and of the target;
* if `f : R →+* S` is of finite presentation and `q ⊆ S` is prime, then the induced map of local
  rings `R_{f^{-1}q} → S_q` is essentially of finite presentation.

Together with `AlgebraicGeometry.HasRingHomProperty.stalkMap_of_respectsIso` the second item
upgrades to the statement that every stalk map of a morphism locally of finite presentation is
essentially of finite presentation. This is the finite-presentation counterpart of Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.stalkMap`, which gives `RingHom.EssFiniteType`.

## Main results

* `RingHom.EssentiallyOfFinitePresentation.comp_ringEquiv_source` and
  `RingHom.essentiallyOfFinitePresentation_respectsIso`: iso invariance.
* `RingHom.EssentiallyOfFinitePresentation.localRingHom_of_finitePresentation`: the local ring
  map attached to a prime of the target of a map of finite presentation.
* `AlgebraicGeometry.LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap`: the
  stalk maps of a morphism locally of finite presentation.
* `RingHom.EssentiallyOfFinitePresentation.isEssentiallyOfFinitePresentation`: the bridge to the
  single-universe spelling `IsEssentiallyOfFinitePresentation` of Tag 00QM (2).

## Implementation notes

The local ring map is factored as `R_p → (f(p^c))⁻¹S → S_q`, following
`RingHom.HoldsForLocalization.isLocalizationMap`. The first factor is of finite presentation
because finite presentation is preserved by localization
(`RingHom.finitePresentation_localizationPreserves`), and the second exhibits `S_q` as a
localization of it, so the composite is essentially of finite presentation by
`RingHom.EssentiallyOfFinitePresentation.of_isLocalization`. No new ring theory is needed.

## References

* [Stacks Project, Tag 00QM](https://stacks.math.columbia.edu/tag/00QM)
* [Stacks Project, Tag 07DS](https://stacks.math.columbia.edu/tag/07DS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace RingHom

/-- Precomposing a ring map essentially of finite presentation with a ring isomorphism gives a
ring map essentially of finite presentation. -/
theorem EssentiallyOfFinitePresentation.comp_ringEquiv_source {R R₂ S : Type u} [CommRing R]
    [CommRing R₂] [CommRing S] {f : R →+* S} (hf : f.EssentiallyOfFinitePresentation)
    (e : R₂ ≃+* R) : (f.comp (e : R₂ →+* R)).EssentiallyOfFinitePresentation := by
  let := f.toAlgebra
  obtain ⟨A, _, _, _, _, _, T, hloc⟩ := hf
  let := (f.comp (e : R₂ →+* R)).toAlgebra
  let : Algebra R₂ A := ((algebraMap R A).comp (e : R₂ →+* R)).toAlgebra
  have : IsScalarTower R₂ A S := IsScalarTower.of_algebraMap_eq' <| by
    show f.comp (e : R₂ →+* R) = (algebraMap A S).comp ((algebraMap R A).comp (e : R₂ →+* R))
    rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R A S]
    rfl
  have : Algebra.FinitePresentation R₂ A :=
    RingHom.finitePresentation_algebraMap.mp
      (RingHom.finitePresentation_respectsIso.2 (algebraMap R A) e
        (RingHom.finitePresentation_algebraMap.mpr inferInstance))
  exact RingHom.EssentiallyOfFinitePresentation.of_isLocalization (C := A) T

/-- Being essentially of finite presentation is invariant under isomorphisms of the source and
of the target. -/
theorem essentiallyOfFinitePresentation_respectsIso :
    RingHom.RespectsIso
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) =>
        f.EssentiallyOfFinitePresentation) :=
  ⟨fun _ e hf => hf.comp_ringEquiv e, fun _ e hf => hf.comp_ringEquiv_source e⟩

/-- If `f : R →+* S` is of finite presentation and `q ⊆ S` is a prime ideal, then the induced
map of local rings `R_{f^{-1}q} → S_q` is essentially of finite presentation. -/
@[ega "IV 1.3.10" "partial"]
theorem EssentiallyOfFinitePresentation.localRingHom_of_finitePresentation {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : f.FinitePresentation) (q : Ideal S)
    [q.IsPrime] :
    (Localization.localRingHom (q.comap f) q f rfl).EssentiallyOfFinitePresentation := by
  set p := q.comap f with hp
  have hple : p.primeCompl ≤ Submonoid.comap f q.primeCompl := fun _ hx => hx
  have hle : p.primeCompl.map f ≤ q.primeCompl := by
    simpa [Submonoid.map_le_iff_le_comap] using hple
  let C := Localization (p.primeCompl.map f)
  let : Algebra C (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (p.primeCompl.map f) q.primeCompl hle
  have : IsScalarTower S C (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have : IsLocalization (q.primeCompl.map (algebraMap S C)) (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (p.primeCompl.map f) q.primeCompl hle
  let g : Localization.AtPrime p →+* C :=
    IsLocalization.map (M := p.primeCompl) (T := p.primeCompl.map f) C f p.primeCompl.le_comap_map
  have hg : g.FinitePresentation :=
    RingHom.finitePresentation_localizationPreserves f p.primeCompl _ _ hf
  have heq : Localization.localRingHom p q f rfl =
      (algebraMap C (Localization.AtPrime q)).comp g := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext x
    simp [Localization.localRingHom, g, ← IsScalarTower.algebraMap_apply]
  rw [heq]
  let : Algebra (Localization.AtPrime p) C := g.toAlgebra
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    ((algebraMap C (Localization.AtPrime q)).comp g).toAlgebra
  have : IsScalarTower (Localization.AtPrime p) C (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FinitePresentation (Localization.AtPrime p) C := hg
  exact RingHom.EssentiallyOfFinitePresentation.of_isLocalization (C := C)
    (q.primeCompl.map (algebraMap S C))

/-- The two spellings of Stacks Tag 00QM (2) agree in a single universe: a ring map essentially
of finite presentation in the sense of `RingHom.EssentiallyOfFinitePresentation` satisfies
`IsEssentiallyOfFinitePresentation`. -/
theorem EssentiallyOfFinitePresentation.isEssentiallyOfFinitePresentation {R S : Type u}
    [CommRing R] [CommRing S] {f : R →+* S} (hf : f.EssentiallyOfFinitePresentation) :
    IsEssentiallyOfFinitePresentation R S f := by
  obtain ⟨A, _, _, _, _, _, T, hloc⟩ := hf
  exact ⟨A, inferInstance, inferInstance, inferInstance, T, inferInstance,
    inferInstance, inferInstance⟩

end RingHom

namespace AlgebraicGeometry

/-- Every stalk map of a morphism of schemes locally of finite presentation is essentially of
finite presentation. This is the finite-presentation analogue of
`AlgebraicGeometry.LocallyOfFiniteType.stalkMap`. -/
theorem LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X) :
    (f.stalkMap x).hom.EssentiallyOfFinitePresentation :=
  HasRingHomProperty.stalkMap_of_respectsIso (P := @LocallyOfFinitePresentation)
    RingHom.essentiallyOfFinitePresentation_respectsIso
    (fun f hf J _ =>
      RingHom.EssentiallyOfFinitePresentation.localRingHom_of_finitePresentation f hf J)
    inferInstance x

end AlgebraicGeometry

end
