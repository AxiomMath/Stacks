module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCommutesCompletionCanonical
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCommutesCompletionTopoi

/-!
# What makes the comparison map of [Stacks, Tag 0A0G] invertible, for a morphism of ringed topoi

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed topoi — an arbitrary
`AlgebraicGeometry.RingedToposHom`, that is a geometric morphism of the underlying topoi together
with `f^♯` — and let `ℐ ⊂ 𝒪`, `ℐ' ⊂ 𝒪'` be sheaves of ideals related as [Stacks, Tag 099J] asks.
`PushforwardCommutesCompletionTopoi.lean` builds the canonical comparison map
`(Rf_*K)^∧ ⟶ Rf_*(K^∧)` at that generality and characterises it by the universal property of
derived completion. This file says what its invertibility amounts to, and reduces it to a
statement that carries no canonicity at all.

## The result

`AlgebraicGeometry.RingedToposHom.isIso_derivedCompletionPushforwardComparison_iff_bijective`
rewrites invertibility at `K` as a bijection of hom-sets: the comparison map is invertible
exactly when `Rf_*(K^∧)`, together with `Rf_*(K ⟶ K^∧)`, *is* a derived completion of `Rf_*K`.
This is an equivalence, so it loses nothing; it is the tag's assertion restated in the form in
which the universal property of [Stacks, Tag 099F] can be fed to it.

## What this is for, and what is still owed

The source proves [Stacks, Tag 0A0G] for a morphism of ringed topoi by reducing to a morphism of
ringed *sites* through [Stacks, Tag 03CR], which is what
`AlgebraicGeometry.RingedToposHom.exists_twoSided_isDenseSubsite_morphismOfSites` provides and
what `PushforwardTopoi.lean` already does for [Stacks, Tag 099J]. The obstacle to doing the same
here is that the 03CR square commutes only up to a 2-isomorphism, so an identification of `Rf_*`
with a composite of derived direct images along the square's other three arrows produces an
isomorphism between the two sides of the tag that is assembled from those equivalences, and is
*not* on the nose the canonical comparison map of `f`. Proving it to be that map is a coherence
between mates across two equivalences.

That coherence can be avoided, and the statement proved here is the first half of avoiding it.
The site-level development carries
`AlgebraicGeometry.RingedSite.isIso_derivedCompletionPushforwardComparison_of_nonempty_iso`,
which shows that the display `Rf_*(D^∧) ≅ (Rf_*D)^∧` at the level of *objects* — an isomorphism
asked to be neither canonical nor natural, but quantified over all `D` — already forces the
canonical map invertible at every `K`. Its proof applies the display at one object only, the cone
of the completion map `K ⟶ K^∧`, and uses nothing about the isomorphism beyond its existence,
because orthogonality to the derived-complete objects is the vanishing of the derived completion
and an isomorphism of objects transports a vanishing however it is built. The statement below is
the input that argument needs on the topos side.

Transporting that argument itself to a morphism of ringed topoi is not done here, and two
concrete instance obligations are what stand in the way: `Rf_*` for a `RingedToposHom` has no
`CategoryTheory.Functor.IsTriangulated` instance (the generic
`Stacks.Injectives.rightDerivedFunctor_isTriangulated` applies, with the unit
`Stacks.Cohomology.DerivedPushforward.derivedPushforwardUnit'`, but has to be instantiated), and
`ObjectProperty.IsStableUnderShift (RingedSite.IsDerivedComplete X.toRingedSite I) ℤ` is not found
at a ringed site presented as `X.toRingedSite`, although `CompleteShift.lean` declares it at a
bare `AlgebraicGeometry.RingedSite`.

Beyond those, reaching the tag at this generality still needs a topos-level form of the ideal
sheaf `ℐ' = f^{-1}ℐ · 𝒪_X` — the site-level
`AlgebraicGeometry.RingedSite.inverseImageIdealSheaf` is built from the functor `u`, while
`AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap` and
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule` are the ingredients for a topos-level one —
the transport of a sheaf of ideals along the dense-subsite replacement of [Stacks, Tag 03CR]
together with the invariance of `SheafOfModules.IsFiniteType` under it, and the commutation of
derived completion with the derived direct image along that replacement.

## No attribute

The statement below carries no `@[stacks 0A0G]`. It is an equivalent rephrasing of the tag
rather than a proof of it, and attaching the tag would claim as proved something it does not
prove. The registrations of Tag 0A0G stay where they are.

## References

* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology

universe u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance 100000] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))))
  (I' : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))))
  (hI : IdealCompatible f I I')
  [(ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I')).IsRightAdjoint]
  [(ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I)).IsRightAdjoint]

/-- **[Stacks, Tag 0A0G] as a universal property, for a morphism of ringed topoi.** The
comparison map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` is invertible at `K` if and only if `Rf_*(K^∧)`, with the
map `Rf_*(K ⟶ K^∧)`, has the universal property of the derived completion of `Rf_*K`:
composition with `Rf_*(K ⟶ K^∧)` is a bijection `Hom(Rf_*(K^∧), N) ≃ Hom(Rf_*K, N)` for every
derived-complete `N`. -/
theorem isIso_derivedCompletionPushforwardComparison_iff_bijective
    (K : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)))) :
    IsIso ((derivedCompletionPushforwardComparison f I I' hI).app K) ↔
      ∀ N : DerivedCategory (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))),
        RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I N →
          Function.Bijective (fun φ : (DerivedPushforward.derivedPushforward (X := X) (Y := Y)
              f).obj ((RingedSite.derivedCompletion X.toRingedSite I').obj K) ⟶ N ↦
            (DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).map
              ((RingedSite.derivedCompletionUnit X.toRingedSite I').app K) ≫ φ) := by
  constructor
  · intro hc N hN
    have key : (fun φ : (DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj
          ((RingedSite.derivedCompletion X.toRingedSite I').obj K) ⟶ N ↦
        (DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).map
          ((RingedSite.derivedCompletionUnit X.toRingedSite I').app K) ≫ φ) =
        (fun ψ : (RingedSite.derivedCompletion Y.toRingedSite I).obj
            ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj K) ⟶ N ↦
          (RingedSite.derivedCompletionUnit Y.toRingedSite I).app
            ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj K) ≫ ψ) ∘
        (fun φ : (DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj
            ((RingedSite.derivedCompletion X.toRingedSite I').obj K) ⟶ N ↦
          (derivedCompletionPushforwardComparison f I I' hI).app K ≫ φ) := by
      funext φ
      dsimp only [Function.comp_apply]
      rw [← Category.assoc,
        derivedCompletionUnit_comp_derivedCompletionPushforwardComparison f I I' hI K]
    rw [key]
    exact (RingedSite.bijective_derivedCompletionUnit_comp Y.toRingedSite I hN).comp
      ⟨fun a b e ↦ (cancel_epi ((derivedCompletionPushforwardComparison f I I' hI).app K)).mp e,
        fun ψ ↦ ⟨inv ((derivedCompletionPushforwardComparison f I I' hI).app K) ≫ ψ, by simp⟩⟩
  · intro hb
    have hd := RingedSite.isDerivedComplete_derivedCompletion_obj Y.toRingedSite I
      ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj K)
    obtain ⟨ψ, hψ⟩ := (hb _ hd).2
      ((RingedSite.derivedCompletionUnit Y.toRingedSite I).app
        ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj K))
    beta_reduce at hψ
    refine ⟨ψ, ?_, ?_⟩
    · refine RingedSite.derivedCompletion_hom_ext Y.toRingedSite I hd ?_
      rw [← Category.assoc,
        derivedCompletionUnit_comp_derivedCompletionPushforwardComparison f I I' hI K, hψ]
      exact (Category.comp_id _).symm
    · refine (hb _ (isDerivedComplete_derivedPushforward_derivedCompletion f I I' hI K)).1 ?_
      dsimp only
      rw [← Category.assoc, hψ,
        derivedCompletionUnit_comp_derivedCompletionPushforwardComparison f I I' hI K]
      exact (Category.comp_id _).symm

end AlgebraicGeometry.RingedToposHom

end
