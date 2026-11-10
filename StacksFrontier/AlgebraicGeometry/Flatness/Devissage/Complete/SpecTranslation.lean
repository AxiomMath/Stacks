module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraTranslationAt
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.RingTheory.Flat.CompleteDevissageSpecTransport

/-!
# The dictionary of Stacks 05I0 (2) stated for a ring map

`Module.nonempty_completeDevissageAt_of_completeDevissageAt` is Stacks 05I0 (2) on global
sections: a complete dévissage of `ℱ/X/S` at a point `x`, for `X` and `S` affine, gives a
complete dévissage of `Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` at the prime of `x`. The source states the same
result for a ring map `A → B` of finite type, a finite `B`-module `N` and a prime `q` of `B`,
and that is the shape in which the consumers of Stacks 05I4 need it: it is
`AlgebraicGeometry.GeometricCompleteDevissageAtGivesAlgebraic`.

The two differ only by the identification of `Γ(Spec A, ⊤)`, `Γ(Spec B, ⊤)` and `Γ(Ñ, ⊤)` with
`A`, `B` and `N`, which are isomorphisms and never equalities. This file performs that
identification and proves
`AlgebraicGeometry.GeometricCompleteDevissageAtGivesAlgebraic` outright, discharging the
hypothesis carried by `AlgebraicGeometry.isFinitePresentation_isFlatOver_of_completeDevissageAt`
and by the consumers below it.

## Main results

* `AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic`: **Stacks 05I0 (2) for a ring
  map**, which is the proposition
  `AlgebraicGeometry.GeometricCompleteDevissageAtGivesAlgebraic`.
* `AlgebraicGeometry.asIdeal_isoSpec_hom_spec`: the prime of `Γ(Spec B, ⊤)` attached to a point
  of `Spec B` is the contraction of that prime of `B` along
  `AlgebraicGeometry.Scheme.ΓSpecIso`.

## Implementation notes

The identification is `Module.nonempty_completeDevissageAt_ofRingEquiv`, whose three
isomorphisms are here `AlgebraicGeometry.Scheme.ΓSpecIso` twice and
`AlgebraicGeometry.tilde.isoTop` once. Its two compatibility hypotheses are
`AlgebraicGeometry.Scheme.ΓSpecIso_naturality` for the structure map and the
`B`-linearity of `AlgebraicGeometry.tilde.isoTop` for the action.

The `Γ(Spec B, ⊤)`-action on `Γ(Ñ, ⊤)` that the dévissage uses and the `B`-action for which
`AlgebraicGeometry.tilde.isoTop` is linear differ by `AlgebraicGeometry.Scheme.ΓSpecIso`: by the
definition of `AlgebraicGeometry.modulesSpecToSheaf` the latter is the restriction of scalars of
the former along `(Scheme.ΓSpecIso _).inv`, so the two agree definitionally once the ring element
is moved across the isomorphism. That `B`-module structure on `Γ(Ñ, ⊤)` is supplied by hand from
`AlgebraicGeometry.moduleSpecΓFunctor`, because instance synthesis does not find it on the type
of sections, only on the object of `ModuleCat B` whose carrier that type is.

## References

* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The prime of `Γ(Spec B, ⊤)` attached to a point of `Spec B` is the contraction of the
corresponding prime of `B` along `AlgebraicGeometry.Scheme.ΓSpecIso`, because the canonical
isomorphism of `Spec B` with the spectrum of its functions is `Spec.map` of that
isomorphism. -/
theorem asIdeal_isoSpec_hom_spec {B : Type u} [CommRing B] (q : PrimeSpectrum B) :
    ((Spec (CommRingCat.of B)).isoSpec.hom q).asIdeal
      = Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.toRingHom
        q.asIdeal := by
  rw [Scheme.isoSpec_Spec_hom]
  rfl

/-- **Stacks Project, Tag 05I0 (2)**, in the direction the source uses and in the form stated for
a ring map: for `A → B` of finite type, `N` a finite `B`-module and `q` a prime of `B`, a
complete dévissage of `Ñ/Spec B/Spec A` at `q` gives a complete dévissage of `N/B/A` at `q`.

This is the proposition `AlgebraicGeometry.GeometricCompleteDevissageAtGivesAlgebraic`, which
`AlgebraicGeometry.isFinitePresentation_isFlatOver_of_completeDevissageAt` and its consumers take
as a hypothesis. The dévissage is translated on global sections by
`Module.nonempty_completeDevissageAt_of_completeDevissageAt` and then carried from
`Γ(Spec A, ⊤)`, `Γ(Spec B, ⊤)` and `Γ(Ñ, ⊤)` back to `A`, `B` and `N` by
`Module.nonempty_completeDevissageAt_ofRingEquiv`. -/
theorem geometricCompleteDevissageAtGivesAlgebraic :
    GeometricCompleteDevissageAtGivesAlgebraic.{u} := by
  intro A B _ _ _ _ N _ _ _ q hD
  obtain ⟨D⟩ := hD
  have hqp : q.asIdeal.IsPrime := q.isPrime
  set X : Scheme.{u} := Spec (CommRingCat.of B)
  set S : Scheme.{u} := Spec (CommRingCat.of A)
  set M : ModuleCat.{u} (CommRingCat.of B) := ModuleCat.of B N
  set f : X ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap A B))
  set F : X.Modules := tilde M
  have hl : LocallyOfFiniteType f := locallyOfFiniteType_specMap_algebraMap A B
  have ht : F.IsFiniteType := (tilde_isFiniteType_iff M).2 inferInstance
  have hQp : ((X.isoSpec.hom q).asIdeal).IsPrime := (X.isoSpec.hom q).isPrime
  -- Stacks 05I0 (2) on global sections.
  have key := @Module.nonempty_completeDevissageAt_of_completeDevissageAt X S _ _ f F q hl _ ht
    (X.isoSpec.hom q).asIdeal hQp rfl D
  -- The three isomorphisms identifying the global sections with the original data.
  let eR : ↥Γ(S, ⊤) ≃+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let eS : ↥Γ(X, ⊤) ≃+* B := (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv
  let eN : ↥Γ(F, (⊤ : X.Opens)) ≃+ N := (tilde.isoTop M).toLinearEquiv.symm.toAddEquiv
  let algΓ : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := (Scheme.Hom.appTop f).hom.toAlgebra
  let ftΓ : Algebra.FiniteType ↥Γ(S, ⊤) ↥Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
  let finΓ : Module.Finite ↥Γ(X, ⊤) ↥Γ(F, (⊤ : X.Opens)) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
  let instB : Module B ↥Γ(F, (⊤ : X.Opens)) :=
    inferInstanceAs (Module ↥(CommRingCat.of B) ↥(moduleSpecΓFunctor.obj F))
  have halg : ∀ x : ↥Γ(S, ⊤), algebraMap A B (eR x) = eS (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) x) :=
    fun x => (congrArg (fun k : Γ(S, ⊤) ⟶ CommRingCat.of B => k.hom x)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B)))).symm
  have hinv : ∀ s : ↥Γ(X, ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (eS s) = s := fun s =>
    congrArg (fun k : Γ(X, ⊤) ⟶ Γ(X, ⊤) => k.hom s)
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id
  have hsmul : ∀ (s : ↥Γ(X, ⊤)) (n : ↥Γ(F, (⊤ : X.Opens))), eN (s • n) = eS s • eN n := by
    intro s n
    have hact : (eS s) • n = s • n := by
      change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (eS s)) • n = s • n
      rw [hinv]
    rw [← hact]
    exact (tilde.isoTop M).toLinearEquiv.symm.map_smul (eS s) n
  have hprime : (X.isoSpec.hom q).asIdeal = Ideal.comap eS.toRingHom q.asIdeal :=
    asIdeal_isoSpec_hom_spec q
  exact Module.nonempty_completeDevissageAt_ofRingEquiv eR eS eN halg hsmul hprime key

end AlgebraicGeometry

end
