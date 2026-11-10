module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.FiniteStageDescent
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.FiniteStageFixed

/-!
# The Picard group as the Galois invariants of the Picard group of a base change

Let `k` be a field, let `X` be a quasi-compact, quasi-separated scheme over `k` with
`H⁰(X, 𝒪_X) = k` and a `k`-rational point, and let `k'/k` be a Galois extension. Then pullback
along the projection `X_{k'} ⟶ X` identifies `Pic(X)` with the subgroup of `Pic(X_{k'})` fixed
by the Galois action, which is [Stacks, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT).

The Galois action and the easy inclusion are those of
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/GaloisAction.lean`: pullback along
`id_X × Spec(σ)` is a left action on `Pic(X_{k'})`, and a class pulled back from `X` is fixed
because a twist does not move the projection. Injectivity is Tag 0CC5, in
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/Injectivity.lean`. Surjectivity — Galois
descent of an invariant class — is assembled here from the two halves described in the
implementation notes.

## Main definitions

* `Stacks.Picard.galoisFixedSubgroup`: the Galois-fixed Picard classes of the base change, as a
  subgroup of `Pic(X_S)`. The action is by homomorphisms, so the fixed classes form one.

## Main results

* `Stacks.Picard.surjOn_schemePullbackClass_galoisFixedClasses`: **the surjectivity clause of
  Tag 0CDT.** Every Galois-fixed class of `Pic(X_{k'})` is pulled back from `Pic(X)`.
* `Stacks.Picard.bijOn_schemePullbackClass_galoisFixedClasses`: **Tag 0CDT.** Pullback along
  `X_{k'} ⟶ X` is a bijection of `Pic(X)` onto the Galois-fixed classes of `Pic(X_{k'})`.

## Implementation notes

**The two halves of surjectivity.** The source proves it from Galois descent for quasi-coherent
modules along a *finite* Galois extension
([Stacks, Tag 0CDR](https://stacks.math.columbia.edu/tag/0CDR), which this repository has as
`Stacks.Descent.nonempty_equivalence_galoisDescentData_baseChange`, an equivalence of
categories), after reducing an infinite Galois extension to its finite subextensions by `Pic` of
a limit of schemes being the colimit of the `Pic`s
([Stacks, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)).

* *The reduction to a finite Galois stage* —
  `StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/FiniteStageContinuity.lean` and
  `StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/FiniteStageFixed.lean`. Every class of
  `Pic(X_{k'})` descends to a finite subextension by Tag 0B8W (2)
  (`Stacks.Picard.exists_finiteSubextension_schemePullbackClass_eq`), and a
  `Gal(k'/k)`-fixed class descends to a finite *Galois* subextension and is fixed there
  (`Stacks.Picard.exists_finiteGaloisSubextension_galoisFixed`). No eventual-injectivity
  statement is needed: the transition maps are honestly injective, which is Tag 0CC5 at the
  stage (`Stacks.Picard.injective_schemePullbackClass_stageProjection`, resting on
  `Stacks.Picard.isIso_appTop_stage`, i.e. `H⁰(X_E, 𝒪) = E` by Tag 02KH).
* *Descent at the finite Galois stage* —
  `StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/FiniteStageDescent.lean`, as
  `Stacks.Picard.exists_schemePullbackClass_eq_of_galoisFixed`. A fixed class supplies an
  isomorphism `ℒ ≅ f_σ^* ℒ` for each `σ` separately and nothing pins the family down to a
  cocycle; that is what the rational point is for. `Pic(Spec E) = 0` trivialises the restriction
  of `ℒ` to the induced `E`-rational point, the structure morphism `X_E ⟶ Spec E` has invariant
  structure sheaf, so an isomorphism of invertible modules on `X_E` is determined by its
  restriction to the point, and the family normalised against the trivialisation is a cocycle
  (`Stacks.Picard.twistNormalizedIso_mul` of
  `StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/NormalizedPullback.lean`). The resulting
  Galois descent datum is effective by Tag 0CDR in invertible form,
  `Stacks.Descent.exists_isInvertible_pullback_iso_of_galoisDescentData_baseChange` of
  `StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/InvertibleDescent.lean`.

**The rational point is used only through the stage.** It enters as the induced `E`-rational
point `Stacks.Picard.baseChangePoint` of the finite Galois stage `X_E`, which is where the
normalisation happens; the infinite extension `k'` never carries a descent datum.

**The continuity clause of Tag 0CDT** — that the action of `Gal(k'/k)` on `Pic(X_{k'})` is
continuous for the Krull topology and the discrete topology — is proved in
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/FiniteStageContinuity.lean`, as
`Stacks.Picard.continuousSMul_galoisPicardAction`: a class descends to a finite subextension
`E` by the reduction above, and is then fixed by the open subgroup `Gal(k'/E)`.

**The Picard group and its pullback** are `Stacks.Picard.ofScheme` and
`Stacks.Picard.schemePullbackClass`, the spelling both Tag 0CC5
(`Stacks.AlgebraicGeometry.PicardBaseChange.injective_picardPullback_of_fieldExtension`) and
the Galois action of Tag 038J are already stated at.

**`H⁰(X, 𝒪_X) = k` is spelled** `IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)`: the
canonical map from `k = H⁰(Spec k, 𝒪)` to `H⁰(X, 𝒪_X)` induced by the structure morphism is an
isomorphism of rings.

## References

* [Stacks Project, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT)
* [Stacks Project, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5)
* [Stacks Project, Tag 0CDR](https://stacks.math.columbia.edu/tag/0CDR)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

/-! ### The Galois-fixed classes as a subgroup -/

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (X : Over (Spec (.of R)))

/-- **The Galois-fixed Picard classes of a base change, as a subgroup.** Pullback along a twist
`id_X × Spec(σ)` is a homomorphism of abelian groups, so the classes it fixes form a subgroup of
`Pic(X_S)`; its carrier is `Stacks.Picard.galoisFixedClasses`. -/
def galoisFixedSubgroup : AddSubgroup (ofScheme (SchemeOver.baseChange R S X)) where
  carrier := galoisFixedClasses R S X
  add_mem' {x y} hx hy σ := by
    rw [schemePullbackClass_add, hx σ, hy σ]
  zero_mem' σ := map_zero (schemePullbackClassHom (galoisTwist R S X σ))
  neg_mem' {x} hx σ := by
    have h : schemePullbackClassHom (galoisTwist R S X σ) (-x) =
        -schemePullbackClassHom (galoisTwist R S X σ) x :=
      map_neg (schemePullbackClassHom (galoisTwist R S X σ)) x
    rw [show schemePullbackClass (galoisTwist R S X σ) (-x) =
      schemePullbackClassHom (galoisTwist R S X σ) (-x) from rfl, h,
      show schemePullbackClassHom (galoisTwist R S X σ) x =
        schemePullbackClass (galoisTwist R S X σ) x from rfl, hx σ]

/-- The carrier of `Stacks.Picard.galoisFixedSubgroup` is `Stacks.Picard.galoisFixedClasses`. -/
@[simp]
theorem coe_galoisFixedSubgroup :
    (galoisFixedSubgroup R S X : Set (ofScheme (SchemeOver.baseChange R S X))) =
      galoisFixedClasses R S X :=
  rfl

/-- A class of `Pic(X_S)` lies in `Stacks.Picard.galoisFixedSubgroup` if and only if pullback
along the twist `id_X × Spec(σ)` fixes it for every `σ ∈ Aut_R(S)`. -/
@[simp]
theorem mem_galoisFixedSubgroup {x : ofScheme (SchemeOver.baseChange R S X)} :
    x ∈ galoisFixedSubgroup R S X ↔
      ∀ σ : S ≃ₐ[R] S, schemePullbackClass (galoisTwist R S X σ) x = x :=
  Iff.rfl

/-! ### The identification `Pic(X) = Pic(X_{k'})^{Gal(k'/k)}` -/

/-- **The surjectivity clause of Stacks Tag 0CDT.** Let `k` be a field, let `X` be a
quasi-compact, quasi-separated scheme over `k` with `H⁰(X, 𝒪_X) = k` admitting a `k`-rational
point, and let `k'/k` be a Galois extension. Then every class of `Pic(X_{k'})` fixed by
`Gal(k'/k)` is pulled back from `Pic(X)`.

The class descends to a finite Galois subextension `E/k`, still fixed
(`Stacks.Picard.exists_finiteGaloisSubextension_galoisFixed`, which is Tag 0B8W (2) followed by
the injectivity of Tag 0CC5 at the stage), and there Galois descent applies
(`Stacks.Picard.exists_schemePullbackClass_eq_of_galoisFixed`, which is Tag 0CDR after the
descent cocycle has been normalised at the `E`-rational point induced by the `k`-rational
point). `H⁰(X_E, 𝒪) = E` is `Stacks.Picard.isIso_appTop_stage`, and `E/k` is Galois because it
is normal and a subextension of a separable extension. -/
theorem surjOn_schemePullbackClass_galoisFixedClasses (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (X : Over (Spec (.of k)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop))
    (pt : Spec (.of k) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 (Spec (.of k))) :
    Set.SurjOn (schemePullbackClass (pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) Set.univ
      (galoisFixedClasses k k' X) := by
  intro y hy
  obtain ⟨E, hEfin, hEnormal, z, hz, hzfix⟩ :=
    exists_finiteGaloisSubextension_galoisFixed X hΓ y hy
  let := hEfin
  let := hEnormal
  have : Algebra.IsSeparable k (E : IntermediateField k k') :=
    Algebra.isSeparable_tower_bot_of_isSeparable k (E : IntermediateField k k') k'
  have : IsGalois k (E : IntermediateField k k') := ⟨⟩
  obtain ⟨x, hx⟩ := exists_schemePullbackClass_eq_of_galoisFixed X
    (isIso_appTop_stage X hΓ E) pt hpt z hzfix
  refine ⟨x, Set.mem_univ x, ?_⟩
  rw [← hz, ← hx, schemePullbackClass_comp, stageProjection_comp_fst]

/-- **Stacks Project, Tag 0CDT.** Let `k` be a field, let `X` be a quasi-compact,
quasi-separated scheme over `k` with `H⁰(X, 𝒪_X) = k` admitting a `k`-rational point, and let
`k'/k` be a Galois extension. Then pullback along `X_{k'} ⟶ X` is a bijection of `Pic(X)` onto
the classes of `Pic(X_{k'})` fixed by `Gal(k'/k)`. -/
@[stacks 0CDT "the identification `Pic(X) = Pic(X_{k'})^{Gal(k'/k)}`. The continuity clause of \
the tag is `Stacks.Picard.continuousSMul_galoisPicardAction`"]
theorem bijOn_schemePullbackClass_galoisFixedClasses (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (X : Over (Spec (.of k)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop))
    (pt : Spec (.of k) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 (Spec (.of k))) :
    Set.BijOn (schemePullbackClass (pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) Set.univ
      (galoisFixedClasses k k' X) :=
  ⟨mapsTo_schemePullbackClass_galoisFixedClasses k k' X,
    (injective_schemePullbackClass_of_globalSectionsIso (algebraMap k k') X.hom hΓ).injOn,
    surjOn_schemePullbackClass_galoisFixedClasses k k' X hΓ pt hpt⟩

end Stacks.Picard

end
