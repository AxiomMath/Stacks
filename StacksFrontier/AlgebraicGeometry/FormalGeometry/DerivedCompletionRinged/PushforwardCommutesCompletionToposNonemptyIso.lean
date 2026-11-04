module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCommutesCompletionToposCriterion

/-!
# A non-canonical display suffices, for a morphism of ringed topoi

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed topoi — an arbitrary
`AlgebraicGeometry.RingedToposHom` — and let `ℐ ⊂ 𝒪`, `ℐ' ⊂ 𝒪'` be sheaves of ideals related as
[Stacks, Tag 099J] asks. `PushforwardCommutesCompletionTopoi.lean` builds the canonical comparison
map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` of [Stacks, Tag 0A0G] at that generality.

This file proves, at that generality, that the display `Rf_*(D^∧) ≅ (Rf_*D)^∧` **as objects** —
an isomorphism asked to be neither canonical nor natural, but quantified over all `D` — already
forces the canonical map invertible at every `K`. It is the transport to morphisms of ringed topoi
of `AlgebraicGeometry.RingedSite.isIso_derivedCompletionPushforwardComparison_of_nonempty_iso`,
whose argument is reproduced: apply the display at the cone `C` of the completion map `K ⟶ K^∧`,
which is orthogonal to the derived-complete objects, so `Rf_*C` is too, and a triangle whose
third object is orthogonal to `N` in both its shifts makes composition with `Rf_*(K ⟶ K^∧)` a
bijection — which is
`AlgebraicGeometry.RingedToposHom.isIso_derivedCompletionPushforwardComparison_iff_bijective`.

## Why this is the useful shape

Reaching [Stacks, Tag 0A0G] for a morphism of ringed topoi from the ringed-sites case goes
through the square of [Stacks, Tag 03CR], which commutes only up to a 2-isomorphism. Identifying
the canonical comparison map of `f` with that of the square's bottom arrow across the two
equivalences is a coherence between mates. The statement below removes that burden: what has to
be transported across the square is the mere *existence* of an isomorphism of objects, which any
assembly of equivalences provides, and no compatibility between that isomorphism and the
canonical map is needed.

## The two instance obligations, discharged

`PushforwardCommutesCompletionToposCriterion.lean` records two concrete gaps that stood in the way
of this transport. Both are discharged here.

* `ObjectProperty.IsStableUnderShift (RingedSite.IsDerivedComplete X.toRingedSite I) ℤ` is not
  found by instance search at a ringed site presented as `X.toRingedSite`, although
  `CompleteShift.lean` declares it at a bare `AlgebraicGeometry.RingedSite`: `toRingedSite` is a
  reducible abbreviation for a structure literal, whose fields reduce away under the reducible
  transparency of the discrimination tree. `isStableUnderShift_isDerivedComplete_toRingedSite`
  restates it in that shape, from the general theorem
  `AlgebraicGeometry.RingedSite.isDerivedComplete_shiftFunctor_obj`, exactly as
  `PushforwardCompletionTopos.lean` does for [Stacks, Tag 099F]'s reflector.
* `Rf_*` for a `RingedToposHom` has no `CategoryTheory.Functor.IsTriangulated` instance at an
  arbitrary `f`. The generic `Stacks.Injectives.rightDerivedFunctor_isTriangulated` applies, at
  the degreewise direct image `AlgebraicGeometry.RingedToposHom.pushforwardModules` and the unit
  `Stacks.Cohomology.DerivedPushforward.derivedPushforwardUnit'`;
  `isTriangulated_derivedPushforward_rightDerivedFunctor` is that instantiation, and fixes the
  `CategoryTheory.Functor.CommShift` the conclusion is stated relative to. (The existing
  `AlgebraicGeometry.RingedToposHom.isTriangulated_derivedPushforward` is a different route, from
  `Rf_*` being a right adjoint, and needs `f^♯` invertible.)

## Main results

* `AlgebraicGeometry.RingedToposHom.isTriangulated_derivedPushforward_rightDerivedFunctor`:
  `Rf_*` is triangulated, at an arbitrary morphism of ringed topoi.
* `AlgebraicGeometry.RingedToposHom.leftOrthogonal_isDerivedComplete_derivedPushforward`: `Rf_*`
  carries an object orthogonal to the derived-complete objects to one orthogonal to them, granted
  the display at that object.
* `AlgebraicGeometry.RingedToposHom.isIso_derivedCompletionPushforwardComparison_of_nonempty_iso`:
  the display at every object makes the canonical comparison map invertible at every object.

## No attribute

Nothing here carries `@[stacks 0A0G]`. The display is a hypothesis of both statements, not a
conclusion; what is proved is that it is *equivalent* to the tag's assertion, not that it holds.

## References

* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Stacks.Cohomology

universe u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance 100000] HasDerivedCategory.standard

/-- **Derived completeness at a ringed site presented as `X.toRingedSite` is stable under the
shift.** This is `AlgebraicGeometry.RingedSite.isDerivedComplete_shiftFunctor_obj`, packaged as the
instance `CategoryTheory.ObjectProperty.IsStableUnderShift`. The instance declared in
`CompleteShift.lean` at a bare `AlgebraicGeometry.RingedSite` is not found at a site of this shape,
because `AlgebraicGeometry.RingedTopos.toRingedSite` is a reducible abbreviation for a structure
literal whose fields reduce away in the discrimination tree. -/
instance isStableUnderShift_isDerivedComplete_toRingedSite (Z : RingedTopos.{u, u, u})
    (J : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Z.toRingedSite.O)))) :
    ObjectProperty.IsStableUnderShift
      (RingedSite.IsDerivedComplete.{u, u, u, u} Z.toRingedSite J) ℤ where
  isStableUnderShiftBy n :=
    ⟨fun _ hK ↦ RingedSite.isDerivedComplete_shiftFunctor_obj Z.toRingedSite J n hK⟩

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))))
  (I' : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))))

/-- **`Rf_*` is triangulated**, for an arbitrary morphism of ringed topoi, relative to the
`CategoryTheory.Functor.CommShift` structure that its universal property as a right derived
functor provides. Sheaves of `𝒪'`-modules form a Grothendieck abelian category, so
`Stacks.Injectives.rightDerivedFunctor_isTriangulated` applies to the degreewise direct image
`AlgebraicGeometry.RingedToposHom.pushforwardModules` with the unit
`Stacks.Cohomology.DerivedPushforward.derivedPushforwardUnit'`.

The name records where it comes from, because there is a second route to the same conclusion under
a hypothesis this one does not need:
`AlgebraicGeometry.RingedToposHom.isTriangulated_derivedPushforward` of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/HypercoveringModuleBoundedBelowEquivalence.lean` gets it from `Rf_*` being a right *adjoint*, and
so holds only when `f^♯` is invertible. This statement is for an arbitrary morphism. -/
theorem isTriangulated_derivedPushforward_rightDerivedFunctor :
    letI := Functor.IsRightDerivedFunctor.commShift
      (DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f)
      (DerivedPushforward.derivedPushforwardUnit' f)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) ℤ
    (DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).IsTriangulated := by
  have _ := SheafOfModules.isGrothendieckAbelianU (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  exact Stacks.Injectives.rightDerivedFunctor_isTriangulated
    (pushforwardModules.{u, u, u, u, u, u} f)
    (DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f)
    (DerivedPushforward.derivedPushforwardUnit' f)

section Commutation

variable (hI : IdealCompatible f I I')
  [(ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I')).IsRightAdjoint]
  [(ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I)).IsRightAdjoint]

/-- **`Rf_*` carries an object orthogonal to the derived-complete objects of `D(𝒪')` to one
orthogonal to the derived-complete objects of `D(𝒪)`**, for a morphism of ringed topoi, as soon as
the display `Rf_*(D^∧) ≅ (Rf_*D)^∧` of [Stacks, Tag 0A0G] holds at the level of objects.

Orthogonality is vanishing of the derived completion, by
`AlgebraicGeometry.RingedSite.leftOrthogonal_isDerivedComplete_iff_isZero_derivedCompletion`; so
the hypothesis says `D^∧ = 0`, whence `Rf_*(D^∧) = 0`, and the display transports that vanishing
to `(Rf_*D)^∧`. The display is used at the object `D` only, which is why the hypothesis is
quantified over all objects in the consumer below rather than over one. -/
theorem leftOrthogonal_isDerivedComplete_derivedPushforward
    [(DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).PreservesZeroMorphisms]
    (habs : ∀ D : DerivedCategory
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))),
      Nonempty ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj
          ((RingedSite.derivedCompletion X.toRingedSite I').obj D) ≅
        (RingedSite.derivedCompletion Y.toRingedSite I).obj
          ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj D)))
    {D : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)))}
    (hD : ObjectProperty.leftOrthogonal
      (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I') D) :
    ObjectProperty.leftOrthogonal (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I)
      ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj D) := by
  rw [RingedSite.leftOrthogonal_isDerivedComplete_iff_isZero_derivedCompletion] at hD ⊢
  obtain ⟨e⟩ := habs D
  exact (Functor.map_isZero
    (DerivedPushforward.derivedPushforward (X := X) (Y := Y) f) hD).of_iso e.symm

include hI in
/-- **The display at the level of objects, for every object, makes the canonical comparison map
of [Stacks, Tag 0A0G] invertible — for an arbitrary morphism of ringed topoi.** If
`Rf_*(D^∧) ≅ (Rf_*D)^∧` for every `D ∈ D(𝒪')` — an isomorphism of objects, not asked to be
canonical or natural — then
`AlgebraicGeometry.RingedToposHom.derivedCompletionPushforwardComparison`, the canonical map
`(Rf_*K)^∧ ⟶ Rf_*(K^∧)`, is invertible at every `K`.

So the step from the source's display to the source's actual assertion costs nothing beyond
quantifying the display over all objects, at the level of ringed topoi just as at the level of
ringed sites. The argument applies it at the cone `C` of the completion map `K ⟶ K^∧`: that cone
is orthogonal to the derived-complete objects by
`AlgebraicGeometry.RingedSite.leftOrthogonal_isDerivedComplete_cone_derivedCompletionUnit`, so
`Rf_*C` is orthogonal to them too by `leftOrthogonal_isDerivedComplete_derivedPushforward`, and so
is `(Rf_*C)⟦-1⟧` because that orthogonal is stable under the shift. `Rf_*` is triangulated by
`isTriangulated_derivedPushforward_rightDerivedFunctor`, hence carries the triangle
`K ⟶ K^∧ ⟶ C` to a distinguished triangle, and a triangle whose third object is orthogonal to `N`
in both its shifts makes
composition with `Rf_*(K ⟶ K^∧)` a bijection `Hom(Rf_*(K^∧), N) ≃ Hom(Rf_*K, N)` — which is
`isIso_derivedCompletionPushforwardComparison_iff_bijective`.

The sheaves of ideals are arbitrary, subject only to `hI`, the relation of [Stacks, Tag 099J]
between them, which the comparison map needs in order to exist. -/
theorem isIso_derivedCompletionPushforwardComparison_of_nonempty_iso
    (habs : ∀ D : DerivedCategory
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))),
      Nonempty ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj
          ((RingedSite.derivedCompletion X.toRingedSite I').obj D) ≅
        (RingedSite.derivedCompletion Y.toRingedSite I).obj
          ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj D)))
    (K : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)))) :
    IsIso ((derivedCompletionPushforwardComparison f I I' hI).app K) := by
  let _ := Functor.IsRightDerivedFunctor.commShift
    (DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f)
    (DerivedPushforward.derivedPushforwardUnit' f)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) ℤ
  have : (DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).IsTriangulated :=
    isTriangulated_derivedPushforward_rightDerivedFunctor f
  rw [isIso_derivedCompletionPushforwardComparison_iff_bijective f I I' hI K]
  intro N hN
  obtain ⟨Cn, v, w, hT⟩ :=
    distinguished_cocone_triangle ((RingedSite.derivedCompletionUnit X.toRingedSite I').app K)
  have hPC : ObjectProperty.leftOrthogonal
      (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I)
      ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj Cn) :=
    leftOrthogonal_isDerivedComplete_derivedPushforward f I I' habs
      (RingedSite.leftOrthogonal_isDerivedComplete_cone_derivedCompletionUnit
        X.toRingedSite I' v w hT)
  have hPC' : ObjectProperty.leftOrthogonal
      (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I)
      (((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj Cn)⟦(-1 : ℤ)⟧) :=
    ObjectProperty.le_shift _ (-1 : ℤ) _ hPC
  have hS := (DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).map_distinguished _ hT
  have key : ∀ φ : (DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj
        ((RingedSite.derivedCompletion X.toRingedSite I').obj K) ⟶ N,
      (DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).map
          ((RingedSite.derivedCompletionUnit X.toRingedSite I').app K) ≫ φ = 0 → φ = 0 := by
    intro φ hφ0
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ hS φ hφ0
    rw [hg, hPC g hN]
    exact comp_zero
  constructor
  · intro φ₁ φ₂ hφ
    refine sub_eq_zero.mp (key (φ₁ - φ₂) ?_)
    rwa [Preadditive.comp_sub, sub_eq_zero]
  · intro h
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hS) h (hPC' _ hN)
    exact ⟨g, hg.symm⟩

end Commutation

end AlgebraicGeometry.RingedToposHom

end
