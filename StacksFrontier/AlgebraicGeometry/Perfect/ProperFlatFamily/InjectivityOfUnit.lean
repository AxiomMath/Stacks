module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# The injective half of part (a) of Tag 0E62

Tag 0E62 asserts, for a proper flat finitely presented `f : X ⟶ S` all of whose fibres have
only constant functions, that `𝒪_S ⟶ f_* 𝒪_X` is invertible and remains so after any base
change.  On sections over an open `V` of the base that conclusion is the *bijectivity* of
`f.app V`.  This file proves the injectivity half of it, for every base change at once, using
only `Flat f` and the fibre condition: properness and local finite presentation are not needed.

The argument has two steps.

* The fibre condition **forces `f` to be surjective**.  The hypothesis at `s` says that
  `κ(s) ⟶ Γ(X_s, 𝒪_{X_s})` is bijective
  (`Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_fiberToSpecResidueField_unit_iff`).
  If `s` were outside the range of `f` the fibre would be the empty scheme,
  whose ring of sections is trivial, and no injection from a field lands there.
* A **flat surjective** morphism has `f.app U` injective for every `U`.  Each stalk map
  `𝒪_{S,f x} ⟶ 𝒪_{X,x}` is a flat local homomorphism of local rings, hence faithfully flat,
  hence injective; surjectivity supplies a point of `X` over every point of `U`, so every
  germ of a section killed by `f.app U` vanishes, and a section of a sheaf with vanishing
  germs is zero.

Both are stable under base change: `Flat` and `Surjective` are, so the conclusion holds for
every `pullback.snd f g` without re-deriving the fibre condition for the base change.

Consequently part (a) of Tag 0E62 is *equivalent*, under `Flat f` and the fibre condition
alone, to the **surjectivity** of `f'.app V` after every base change
(`baseChange_isIso_c_iff_surjective`).

## Main results

* `injective_of_flat_of_isLocalHom`: a flat local homomorphism of local rings is injective.
* `injective_app_of_flat_of_surjective`: for flat surjective `f`, the comparison
  `𝒪_S ⟶ f_* 𝒪_X` is injective on the sections over every open.
* `isEmpty_fiber_of_notMem_range`: the scheme-theoretic fibre over a point outside the range
  is the empty scheme.
* `surjective_of_forall_isIso_fiber_unit`: the fibre hypothesis implies `f` surjective.
* `injective_app_of_baseChange`: the injectivity half of part (a), for every base change.
* `baseChange_isIso_c_iff_surjective`: part (a) is equivalent to surjectivity on sections
  after every base change.

## Implementation notes

`injective_of_flat_of_isLocalHom` goes through `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
so the `Algebra` structure induced by the homomorphism has to be introduced by hand;
`RingHom.Flat` is by definition `Module.Flat` for exactly that structure.

## References

* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ProperFlatFamilyUnit

universe u

/-- A flat local homomorphism of local rings is injective: it is faithfully flat. -/
theorem injective_of_flat_of_isLocalHom {R T : Type*} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] (φ : R →+* T) (hφ : φ.Flat) [IsLocalHom φ] :
    Function.Injective φ := by
  let _ : Algebra R T := φ.toAlgebra
  have hflat : Module.Flat R T := hφ
  have hlocal : IsLocalHom (algebraMap R T) := ‹IsLocalHom φ›
  have : Module.FaithfullyFlat R T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (RingHom.faithfullyFlat_algebraMap_iff.2 this).injective

/-- Every stalk map of a flat morphism of schemes is injective. -/
theorem injective_stalkMap {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom :=
  injective_of_flat_of_isLocalHom _ (AlgebraicGeometry.Flat.stalkMap f x)

/-- For a flat surjective morphism of schemes the comparison `𝒪_S ⟶ f_* 𝒪_X` is injective on
the sections over every open of the base: flatness makes each stalk map injective, and
surjectivity makes the stalk maps jointly detect vanishing of a section. -/
theorem injective_app_of_flat_of_surjective {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [Surjective f] (U : S.Opens) : Function.Injective (f.app U) := by
  intro a b hab
  have key : ∀ (s : S) (hs : s ∈ U), S.presheaf.germ U s hs a = S.presheaf.germ U s hs b := by
    intro s hs
    obtain ⟨x, rfl⟩ := f.surjective s
    refine injective_stalkMap f x ?_
    rw [f.germ_stalkMap_apply U x hs, f.germ_stalkMap_apply U x hs, hab]
  exact TopCat.Presheaf.section_ext S.sheaf U a b key

/-- The scheme-theoretic fibre over a point outside the range of `f` is the empty scheme. -/
theorem isEmpty_fiber_of_notMem_range {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (hs : s ∉ Set.range f.base) : IsEmpty ↥(f.fiber s) := by
  rw [← Set.range_eq_empty_iff (f := (f.fiberι s).base), f.range_fiberι s]
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  exact fun h => hs ⟨x, h⟩

/-- The fibre hypothesis of Tag 0E62 forces `f` to be surjective.  The condition at `s` makes
`κ(s) ⟶ Γ(X_s, 𝒪_{X_s})` bijective, and a field admits no injection into the trivial ring of
sections of the empty scheme. -/
theorem surjective_of_forall_isIso_fiber_unit {X S : Scheme.{u}} (f : X ⟶ S)
    (hH0 : ∀ s : S, IsIso (SheafOfModules.unitToPushforwardObjUnit
      (f.fiberToSpecResidueField s).toRingCatSheafHom)) :
    Surjective f := by
  refine ⟨fun s => ?_⟩
  by_contra hs
  have : IsEmpty ↥(f.fiber s) := isEmpty_fiber_of_notMem_range f hs
  obtain ⟨a, b, hab⟩ := exists_pair_ne (S.residueField s)
  exact hab (((isIso_fiberToSpecResidueField_unit_iff f s).1 (hH0 s)).1 (Subsingleton.elim _ _))

/-- The injectivity half of part (a) of Tag 0E62, in the absolute case: under flatness the
fibre hypothesis makes `𝒪_S ⟶ f_* 𝒪_X` injective on sections over every open. -/
theorem injective_app_of_forall_isIso_fiber_unit {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (hH0 : ∀ s : S, IsIso (SheafOfModules.unitToPushforwardObjUnit
      (f.fiberToSpecResidueField s).toRingCatSheafHom)) (U : S.Opens) :
    Function.Injective (f.app U) :=
  have := surjective_of_forall_isIso_fiber_unit f hH0
  injective_app_of_flat_of_surjective f U

/-- The injectivity half of part (a) of Tag 0E62, after an arbitrary base change: the
surjectivity of `f` given by the fibre condition and the flatness of `f` are both stable under
base change. -/
theorem injective_app_of_baseChange {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (hH0 : ∀ s : S, IsIso (SheafOfModules.unitToPushforwardObjUnit
      (f.fiberToSpecResidueField s).toRingCatSheafHom))
    {S' : Scheme.{u}} (g : S' ⟶ S) (V : S'.Opens) :
    Function.Injective ((pullback.snd f g).app V) :=
  have : Surjective f := surjective_of_forall_isIso_fiber_unit f hH0
  injective_app_of_flat_of_surjective (pullback.snd f g) V

/-- Part (a) of Tag 0E62 is equivalent, under flatness and the fibre hypothesis alone, to the
**surjectivity** of the comparison on sections after every base change, the injectivity being
`injective_app_of_baseChange`. -/
theorem baseChange_isIso_c_iff_surjective {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (hH0 : ∀ s : S, IsIso (SheafOfModules.unitToPushforwardObjUnit
      (f.fiberToSpecResidueField s).toRingCatSheafHom)) :
    (∀ {S' : Scheme.{u}} (g : S' ⟶ S), IsIso (pullback.snd f g).toLRSHom.toHom.c) ↔
      ∀ {S' : Scheme.{u}} (g : S' ⟶ S) (V : S'.Opens),
        Function.Surjective ((pullback.snd f g).app V) := by
  refine ⟨fun h _ g V => ((baseChange_isIso_c_iff_bijective f).1 h g V).2, fun h => ?_⟩
  exact (baseChange_isIso_c_iff_bijective f).2 fun g V =>
    ⟨injective_app_of_baseChange f hH0 g V, h g V⟩

end Stacks.AlgebraicGeometry.ProperFlatFamilyUnit
