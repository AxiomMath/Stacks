module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksCore.Tactic.StacksAttribute

/-!
# Covering the fibres near the generic point

Let `f : X ⟶ Y` be a finite type morphism of schemes with `Y` irreducible with generic point
`η`. If a family of subsets covers the generic fibre `X_η`, then over some nonempty open subset
of `Y` the closures in `X` of their images cover every fibre. Specializing to the empty family
gives: an empty generic fibre forces every fibre over a nonempty open subset to be empty.

## Main results

* `AlgebraicGeometry.exists_open_fiber_covered_by_closures`: the open subset over which the
  closures cover the fibres.
* `AlgebraicGeometry.exists_open_preimage_eq_bot_of_isEmpty_generic_fiber`: an empty generic
  fibre forces the base change to a nonempty open subset of the target to be empty.

## Implementation notes

The family may have an arbitrary index type and its members need not be closed. The closure of
each subset of the generic fibre is taken in `X` after applying the canonical morphism from
that fibre. The hypothesis that `η` is a generic point of all of `Y` already expresses
irreducibility of `Y`. Finite type is expressed by `LocallyOfFiniteType` together with
`QuasiCompact`.

The proof passes to the reduction `Y₀` of `Y`, which is universally homeomorphic to `Y`, so
that generic flatness applies; over a dense open of `Y₀` the base change of `f` is flat, hence
generalizing, and every point of a fibre over that open is a specialization of a point of the
generic fibre.

## References

* [Stacks Project, Tag 054Y](https://stacks.math.columbia.edu/tag/054Y)
* [Stacks Project, Tag 054W](https://stacks.math.columbia.edu/tag/054W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- If `g` is flat over an open `U`, then a specialization `y ⤳ g x` inside `U` lifts to a
specialization `x' ⤳ x` with `g x' = y`. -/
theorem exists_specializes_of_flat_resLE {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    [Flat (g.resLE U (g ⁻¹ᵁ U) le_rfl)] {x : X} {y : Y} (hy : y ∈ U) (hx : g x ∈ U)
    (h : y ⤳ g x) : ∃ x' : X, g x' = y ∧ x' ⤳ x := by
  let gU := g.resLE U (g ⁻¹ᵁ U) le_rfl
  have : Flat gU := ‹_›
  let xU : (g ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  let ηU : U.toScheme := ⟨y, hy⟩
  have hres (a : (g ⁻¹ᵁ U).toScheme) : (gU a).1 = g a.1 := by
    simpa [gU] using Scheme.Hom.coe_resLE_apply (f := g) (e := le_rfl) a
  have hspecU : ηU ⤳ gU xU := (subtype_specializes_iff _ _).2 (by rwa [hres])
  obtain ⟨xgenU, hgenSpec, hgenMap⟩ := Flat.generalizingMap gU hspecU
  exact ⟨xgenU.1, (hres xgenU).symm.trans (congrArg Subtype.val hgenMap),
    (subtype_specializes_iff xgenU xU).1 hgenSpec⟩

/-- Let `f : X ⟶ Y` be a finite type morphism with `Y` irreducible with generic point `η`.
Over some nonempty open subset of `Y`, every point of `X` specializes from a point over `η`. -/
theorem exists_open_forall_exists_specializes_generic_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧ ∀ x : X, f x ∈ V → ∃ x' : X, f x' = η ∧ x' ⤳ x := by
  let Y₀ := Y.nilradical.subscheme
  let r : Y₀ ⟶ Y := Y.nilradical.subschemeι
  let X₀ := pullback f r
  let p : X₀ ⟶ X := pullback.fst f r
  let g : X₀ ⟶ Y₀ := pullback.snd f r
  have hr : IsHomeomorph r :=
    (inferInstance : UniversalHomeomorphism r).universally_isHomeomorph _ _ _
      IsPullback.of_id_snd
  have hpull : IsPullback p g f r := IsPullback.of_hasPullback f r
  have hp : IsHomeomorph p :=
    (inferInstance : UniversalHomeomorphism r).universally_isHomeomorph _ _ _ hpull
  have _ : IsReduced Y₀ := by
    simpa only [Y₀, ← Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := Y) ⊤
  let F : X₀.Modules := SheafOfModules.unit X₀.ringCatSheaf
  have _ : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X₀
  have _ : F.IsFiniteType := structureSheaf_isFiniteType X₀
  obtain ⟨U, hUdense, hflat, -, -, -⟩ := exists_dense_open_flat_finitePresentation g F
  let eY : Y₀ ≃ₜ Y := hr.homeomorph
  let η₀ : Y₀ := eY.symm η
  have hη₀ : IsGenericPoint η₀ Set.univ := by simpa [η₀] using hη.image eY.symm.continuous
  have hηU : η₀ ∈ U :=
    (hη₀.mem_open_set_iff U.2).2 (by simpa using hUdense.nonempty_iff.mpr ⟨η₀⟩)
  refine ⟨r '' (U : Set Y₀), hr.isOpenMap _ U.2, ⟨r η₀, ⟨η₀, hηU, rfl⟩⟩, ?_⟩
  rintro x ⟨y₀, hy₀, hxy⟩
  obtain ⟨x₀, rfl⟩ := hp.surjective x
  have hcomm (a : X₀) : f (p a) = r (g a) := by
    simpa using congrArg (fun k : X₀ ⟶ Y => k a) hpull.w
  obtain rfl : g x₀ = y₀ := hr.injective ((hcomm x₀).symm.trans hxy.symm)
  obtain ⟨x', hx', hspec⟩ :=
    exists_specializes_of_flat_resLE g U hηU hy₀ (hη₀.specializes (Set.mem_univ _))
  refine ⟨p x', ?_, hspec.map p.continuous⟩
  rw [hcomm x', hx']
  exact eY.apply_symm_apply η

/-- **Stacks Project, Tag 054Y.** Let `f : X ⟶ Y` be a finite type morphism with `Y`
irreducible with generic point `η`. If the subsets `Z i` cover the generic fibre, then over
some nonempty open subset of `Y` the closures in `X` of their images cover every fibre. -/
@[stacks 054Y]
theorem exists_open_fiber_covered_by_closures
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    {ι : Type v}
    (Z : ι → Set (f.fiber η))
    (hcover : ∀ x : f.fiber η, ∃ i, x ∈ Z i) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, ∀ x : f.fiber y,
        ∃ i, f.fiberι y x ∈ closure (f.fiberι η '' Z i) := by
  obtain ⟨V, hVopen, hVne, hV⟩ := exists_open_forall_exists_specializes_generic_fiber f η hη
  refine ⟨V, hVopen, hVne, fun y hy x => ?_⟩
  have hfx : f (f.fiberι y x) = y := by
    simpa using congrArg (fun k : f.fiber y ⟶ Y => k x) (Scheme.Hom.fiber_fac f y)
  obtain ⟨x', hx', hspec⟩ := hV (f.fiberι y x) (by rwa [hfx])
  obtain ⟨aη, haη⟩ : x' ∈ Set.range (f.fiberι η) := by
    rwa [Scheme.Hom.range_fiberι]
  obtain ⟨i, hi⟩ := hcover aη
  exact ⟨i, hspec.mem_closed isClosed_closure (subset_closure ⟨aη, hi, haη⟩)⟩

/-- If the fibre of a finite type morphism over a generic point `η` of `Y` is empty, then the
fibres over some nonempty open subset of `Y` are all empty. -/
theorem exists_open_isEmpty_fiber_of_isEmpty_generic_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ) (hempty : IsEmpty (f.fiber η)) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧ ∀ y ∈ V, IsEmpty (f.fiber y) := by
  obtain ⟨V, hVopen, hVne, hV⟩ :=
    exists_open_fiber_covered_by_closures f η hη
      (fun i : PEmpty.{1} => (i.elim : Set (f.fiber η)))
      isEmptyElim
  exact ⟨V, hVopen, hVne, fun y hy => ⟨fun x => (hV y hy x).elim fun i _ => i.elim⟩⟩

/-- **Stacks Project, Tag 054W.** Let `f : X ⟶ Y` be a finite type morphism with `Y`
irreducible with generic point `η`. If the fibre over `η` is empty, then the base change of `f`
to some nonempty open subset `V` of `Y` is empty, that is, `f ⁻¹ᵁ V = ⊥`. -/
@[stacks 054W]
theorem exists_open_preimage_eq_bot_of_isEmpty_generic_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ) (hempty : IsEmpty (f.fiber η)) :
    ∃ V : Y.Opens, Nonempty V ∧ f ⁻¹ᵁ V = ⊥ := by
  obtain ⟨V, hVopen, hVne, hV⟩ :=
    exists_open_isEmpty_fiber_of_isEmpty_generic_fiber f η hη hempty
  exact ⟨⟨V, hVopen⟩, hVne.to_subtype,
    eq_bot_iff.2 fun x hx => (hV (f x) hx).elim (f.asFiber x)⟩

end AlgebraicGeometry

end
