module

public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.RingTheory.Flat.CompleteDevissage
public import StacksFrontier.RingTheory.Smooth.GeometricallyIrreducibleFibres

/-!
# The algebra underlying a one-step dévissage

All four schemes of a one-step dévissage `(Z, Y, i, π, 𝒢)` of `ℱ/X/S` are affine, so the whole
datum is determined by rings and ring maps: writing `R = Γ(S, ⊤)` for the base, the closed
immersion `i` becomes a surjective `R`-algebra map `Γ(X, ⊤) → Γ(Z, ⊤)` of finite presentation,
the finite morphism `π` becomes a finite ring map `Γ(Y, ⊤) → Γ(Z, ⊤)`, the smooth structure
morphism `g` becomes a smooth `R`-algebra `Γ(Y, ⊤)` whose spectrum has geometrically irreducible
fibres over `Spec R`, and the module `𝒢` becomes a finite `Γ(Z, ⊤)`-module `Γ(𝒢, ⊤)` whose
restriction of scalars along `i` is the module being dévissed.

This file collects that translation. It is the stagewise half of the dictionary between the
scheme-theoretic notion of a complete dévissage, `AlgebraicGeometry.CompleteDevissage`, and the
ring-theoretic one, `Module.CompleteDevissage`: each item below produces exactly one field of
`Module.CompleteDevissage` out of the corresponding field of
`AlgebraicGeometry.OneStepDevissage`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.sectionsLinearEquiv`: an isomorphism of modules on a scheme
  restricts to a linear equivalence of the sections over any open.
* `AlgebraicGeometry.OneStepDevissage.closedSectionsLinearEquiv`: the sections of the module
  being dévissed, as a module over the ring of functions on the source, are the sections of the
  module on the closed subscheme with scalars restricted along the closed immersion.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_specMap_appTop`: a morphism of affine schemes with
  geometrically irreducible fibres induces a ring map whose spectrum again has geometrically
  irreducible fibres.
* `AlgebraicGeometry.OneStepDevissage.surjective_i_appTop` and
  `AlgebraicGeometry.OneStepDevissage.finitePresentation_i_appTop`: the closed immersion of a
  one-step dévissage is a surjection of finite presentation on functions.
* `AlgebraicGeometry.OneStepDevissage.finite_π_appTop`: the finite morphism of a one-step
  dévissage is a finite ring map on functions.
* `AlgebraicGeometry.OneStepDevissage.smooth_g_appTop` and
  `AlgebraicGeometry.OneStepDevissage.algebraSmooth_g_appTop`: the structure morphism of the
  smooth scheme of a one-step dévissage is a smooth ring map on functions, in its ring-map and
  its algebra formulation.
* `AlgebraicGeometry.OneStepDevissage.geometricallyIrreducible_specMap_algebraMap`: the fibres
  of the spectrum of that algebra are geometrically irreducible, in the shape in which
  `Module.CompleteDevissage` records the condition.
* `AlgebraicGeometry.OneStepDevissage.map_isPrime_g_appTop`: the extension of a prime of the
  base to the functions on the smooth scheme is prime.
* `AlgebraicGeometry.OneStepDevissage.appTop_over_base`: the three maps of a one-step dévissage
  commute on functions.
* `AlgebraicGeometry.OneStepDevissage.finite_sections_closedModule`: the module on the closed
  subscheme has finite global sections.
* `AlgebraicGeometry.isEmpty_nonemptyCompleteDevissageAt_of_isZero` and
  `AlgebraicGeometry.nonempty_completeDevissageAt_of_isZero`: the zero sheaf has no nonempty
  complete dévissage at a point, and therefore exactly the empty one.
* `Module.nonempty_completeDevissageAt_of_subsingleton`: the ring-theoretic counterpart.

## Implementation notes

The algebra structures are the ones induced by the morphisms themselves, through
`RingHom.toAlgebra`, so that `algebraMap` is literally the map on functions; this is what makes
the two conditions `Module.CompleteDevissage` states scheme-theoretically — smoothness and
geometric irreducibility of the fibres — transfer by rewriting rather than by transport.

Geometric irreducibility is stable under isomorphism of the arrow because
`AlgebraicGeometry.geometrically` is a `CategoryTheory.MorphismProperty.universally`, and those
respect isomorphisms. That is what carries the condition from the structure morphism `g` of the
dévissage to `Spec.map` of the induced ring map, which differ by the two canonical isomorphisms
of an affine scheme with the spectrum of its functions.

The module structure on the sections of a direct image along a morphism of schemes is, by
construction of the direct image, the restriction of scalars of the sections of the original
module. So no comparison map is needed in
`AlgebraicGeometry.OneStepDevissage.closedSectionsLinearEquiv` beyond the sections of the
isomorphism recorded by the dévissage; the restriction-of-scalars module structure appearing in
`Module.CompleteDevissage.initialEquiv` is the same structure.

## References

* [Stacks Project, Tag 05H4](https://stacks.math.columbia.edu/tag/05H4)
* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Geometric irreducibility of a morphism of schemes is invariant under pre- and
postcomposition with an isomorphism. -/
instance geometricallyIrreducible_respectsIso :
    MorphismProperty.RespectsIso @GeometricallyIrreducible := by
  rw [GeometricallyIrreducible.eq_geometrically, geometrically_eq_universally]
  exact MorphismProperty.universally_respectsIso _

/-- A morphism of affine schemes with geometrically irreducible fibres induces a map of
functions whose spectrum again has geometrically irreducible fibres. -/
lemma geometricallyIrreducible_specMap_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) (hg : GeometricallyIrreducible g) :
    GeometricallyIrreducible (Spec.map g.appTop) := by
  have h : Spec.map g.appTop = X.isoSpec.inv ≫ g ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality]; simp
  rw [h]
  exact MorphismProperty.RespectsIso.precomp _ X.isoSpec.inv _
    (MorphismProperty.RespectsIso.postcomp _ Y.isoSpec.hom _ hg)

namespace Scheme.Modules

/-- An isomorphism of modules on a scheme restricts to a linear equivalence of the sections
over any open. -/
def sectionsLinearEquiv {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) where
  toFun := e.hom.app U
  map_add' _ _ := map_add _ _ _
  map_smul' r x := Hom.app_smul e.hom r x
  invFun := e.inv.app U
  left_inv x := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.hom_inv_id, Hom.id_app]
    simp
  right_inv x := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id, Hom.id_app]
    simp

end Scheme.Modules

namespace OneStepDevissage

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]

variable (D : OneStepDevissage f F s)

/-- The closed immersion of a one-step dévissage is surjective on functions. -/
lemma surjective_i_appTop : Function.Surjective (D.i.appTop).hom := by
  have := D.affine_X
  have := D.affine_Z
  have := D.closed_immersion
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine (f := D.i)).2

/-- The closed immersion of a one-step dévissage is of finite presentation on functions. -/
lemma finitePresentation_i_appTop : (D.i.appTop).hom.FinitePresentation := by
  have := D.affine_X
  have := D.affine_Z
  exact (HasRingHomProperty.iff_of_isAffine
    (P := @LocallyOfFinitePresentation)).1 D.finite_presentation.1

/-- The finite morphism of a one-step dévissage is a finite ring map on functions. -/
lemma finite_π_appTop : (D.π.appTop).hom.Finite := by
  have := D.affine_Y
  have := D.affine_Z
  have := D.finite
  exact Scheme.Hom.finite_appTop D.π

/-- The structure morphism of the smooth scheme of a one-step dévissage is a smooth ring map
on functions. -/
lemma smooth_g_appTop : (D.g.appTop).hom.Smooth := by
  have := D.affine_Y
  have := D.affine_S
  have := D.smooth
  exact (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).1 ‹_›

/-- The functions on the smooth scheme of a one-step dévissage form a smooth algebra over the
functions on the base. -/
lemma algebraSmooth_g_appTop :
    letI := (D.g.appTop).hom.toAlgebra
    Algebra.Smooth Γ(S, ⊤) Γ(D.Y, ⊤) := by
  let _ := (D.g.appTop).hom.toAlgebra
  exact RingHom.smooth_algebraMap.1 D.smooth_g_appTop

/-- The spectrum of the algebra of functions on the smooth scheme of a one-step dévissage has
geometrically irreducible fibres over the spectrum of the functions on the base. This is the
shape in which `Module.CompleteDevissage` records the condition. -/
lemma geometricallyIrreducible_specMap_algebraMap :
    letI := (D.g.appTop).hom.toAlgebra
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(D.Y, ⊤)))) := by
  have := D.affine_Y
  have := D.affine_S
  exact geometricallyIrreducible_specMap_appTop D.g D.geometrically_irreducible

/-- The extension of a prime of the base to the functions on the smooth scheme of a one-step
dévissage is prime: it is the generic point of the fibre over that prime. This is the field
`Module.CompleteDevissage.map_isPrime`. -/
lemma map_isPrime_g_appTop (r : Ideal Γ(S, ⊤)) [r.IsPrime] :
    letI := (D.g.appTop).hom.toAlgebra
    (Ideal.map (algebraMap Γ(S, ⊤) Γ(D.Y, ⊤)) r).IsPrime := by
  let _ := (D.g.appTop).hom.toAlgebra
  have := D.algebraSmooth_g_appTop
  have := D.geometricallyIrreducible_specMap_algebraMap
  exact Ideal.isPrime_map_of_smooth_of_geometricallyIrreducible Γ(S, ⊤) Γ(D.Y, ⊤) r

/-- The three maps of a one-step dévissage commute on functions. -/
lemma appTop_over_base : f.appTop ≫ D.i.appTop = D.g.appTop ≫ D.π.appTop := by
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, D.over_base]

/-- The module on the closed subscheme of a one-step dévissage has finite global sections. -/
instance finite_sections_closedModule : Module.Finite Γ(D.Z, ⊤) Γ(D.G, ⊤) := by
  have := D.affine_Z
  have := D.quasi_coherent_G
  have := D.finite_type_G
  exact Stacks.AlgebraicGeometry.CoherentFinite.finite_sections D.G (isAffineOpen_top D.Z)

/-- The global sections of the module being dévissed are the global sections of the module on
the closed subscheme, with scalars restricted along the closed immersion. -/
def closedSectionsLinearEquiv :
    Γ(F, ⊤) ≃ₗ[Γ(X, ⊤)] Γ((Scheme.Modules.pushforward D.i).obj D.G, (⊤ : X.Opens)) :=
  Scheme.Modules.sectionsLinearEquiv D.module_iso ⊤

/-- The restriction of scalars appearing in `closedSectionsLinearEquiv` is the one
`Module.CompleteDevissage` uses. -/
lemma module_pushforward_sections_eq_compHom :
    (inferInstance :
        Module Γ(X, ⊤) Γ((Scheme.Modules.pushforward D.i).obj D.G, (⊤ : X.Opens))) =
      Module.compHom Γ(D.G, (⊤ : D.Z.Opens)) (D.i.appTop).hom :=
  rfl

end OneStepDevissage

/-! ### The empty dévissage

A dévissage at a point, as formalized here, pins the point to the support of the fibre module,
so a *nonempty* dévissage of the zero module cannot exist. This is why Tag 05HI admits the
empty dévissage for the zero sheaf, and why `AlgebraicGeometry.CompleteDevissageAt` has its
`empty` constructor: without it the zero sheaf would have no dévissage at all, while the
ring-theoretic `Module.CompleteDevissageAt` is inhabited by its own `empty` constructor, and
the comparison of the two notions would fail at every zero module. The statements below record
both halves of that: no nonempty dévissage exists, and the dévissage that does exist is the
empty one. -/

/-- A one-step dévissage at a point requires the point to lie in the support of the fibre
module, so a zero module has none. -/
lemma isEmpty_oneStepDevissageAt_of_isZero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hF : Limits.IsZero F) : IsEmpty (OneStepDevissageAt f F x) := by
  refine ⟨fun D => ?_⟩
  have h := D.mem_fiber_support
  rw [Stacks.Modules.supp_pullback,
    Stacks.AlgebraicGeometry.ConfinedDevissage.supp_eq_empty_of_isZero F hF] at h
  simp at h

/-- The one-step dévissage at the current point carried by the first stage of a pointed
dévissage chain. -/
private def atPointOfPointedChain {S : Scheme.{u}} {s : S} {X : Scheme.{u}} {f : X ⟶ S}
    {F : X.Modules} {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent}
    {ht : F.IsFiniteType} {x : X} {c : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x c) :
    @OneStepDevissageAt X S f F x hl hq ht := by
  cases P with
  | last _ _ _ p => exact p.atPoint
  | more _ _ _ _ _ _ p _ => exact p.atPoint

/-- A zero module has no nonempty complete dévissage at a point: every stage of one is a
one-step dévissage at a point of the support of the fibre module, and that support is empty. -/
lemma isEmpty_nonemptyCompleteDevissageAt_of_isZero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hF : Limits.IsZero F) : IsEmpty (NonemptyCompleteDevissageAt f F x) :=
  ⟨fun D => (isEmpty_oneStepDevissageAt_of_isZero f F x hF).elim
    (atPointOfPointedChain D.pointed)⟩

/-- A zero module has the empty complete dévissage at every point, and by
`AlgebraicGeometry.isEmpty_nonemptyCompleteDevissageAt_of_isZero` that is the only one. -/
lemma nonempty_completeDevissageAt_of_isZero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hF : Limits.IsZero F) : Nonempty (CompleteDevissageAt f F x) :=
  ⟨.empty hF⟩

end AlgebraicGeometry

namespace Module

variable {R : Type u} {S : Type*} {N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]

/-- The zero module has the empty complete dévissage at every prime. -/
lemma nonempty_completeDevissageAt_of_subsingleton (q : Ideal S) [q.IsPrime]
    [Subsingleton N] : Nonempty (CompleteDevissageAt R S N q) :=
  ⟨.empty ‹_›⟩

end Module

end
