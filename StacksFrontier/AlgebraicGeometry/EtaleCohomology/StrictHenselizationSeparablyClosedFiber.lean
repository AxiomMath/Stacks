module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Topology.LocallyConstant.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse

/-!
# Étale cohomology over a separably closed point of a strict henselization

Let `f : X ⟶ S` be a morphism of schemes, let `x̄` be a geometric point of `X` with image `s̄` in
`S`, and let `Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` be a point of the strict henselization of `S` at `s̄`
with `K` separably closed. For an abelian sheaf `ℱ` on the small étale site of `Spec K` and
`q ≥ 0`, Tag 0EZV asserts the equivalence of

1. `H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K, ℱ) = H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K, ℱ)`,
2. `H^q(Spec(𝒪^{sh}_{X,x̄}) ×_{Spec(𝒪^{sh}_{S,s̄})} Spec K, ℱ) = H^q(Spec K, ℱ)`,

each equality read as bijectivity of the canonical restriction map.

The two restriction maps are taken along base changes of one and the same morphism, the morphism
of strict henselizations `Spec(𝒪^{sh}_{X,x̄}) ⟶ Spec(𝒪^{sh}_{S,s̄})` of Tag 0GJN: along the
projection `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` in the first case and along the
given point `Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` in the second. The source deduces the equivalence from
the fact that, `K` being separably closed, `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is a cofiltered limit
of finite disjoint unions of copies of `Spec K` over nonempty index sets, so that both cohomology
groups of (1) are groups of locally constant functions on the limit index space with values in
the corresponding groups of (2).

## Main definitions

* `Stacks.EtaleCohomology.specIsoSigmaOfIsSepClosed` — the spectrum of an étale algebra over a
  separably closed field is a finite coproduct of copies of the spectrum of that field.
* `Stacks.EtaleCohomology.strictHenselizationFiberMap` — the canonical morphism
  `Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K ⟶ Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K`.
* `Stacks.EtaleCohomology.strictHenselizationBaseFiberSection` — the section of the projection
  `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K ⟶ Spec K` determined by the given point.
* `Stacks.EtaleCohomology.strictHenselizationBaseFiberIsoSpec` — the identification of
  `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` with `Spec(𝒪^{sh}_{S,s̄} ⊗_{𝒪_{S,s}} K)`.
* `Stacks.EtaleCohomology.SepClosedFiberLocallyConstantPresentation` — data exhibiting the
  restriction map of condition (1) as the map induced by the restriction map of condition (2) on
  locally constant functions on a nonempty space.

## Main results

* `Stacks.EtaleCohomology.finite_primeSpectrum_of_etale` — an étale algebra over a field has
  finitely many primes.
* `Stacks.EtaleCohomology.isPullback_strictHenselizationFiberMap` — the morphism
  `Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K ⟶ Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is a base change of the
  morphism of strict henselizations.
* `Stacks.EtaleCohomology.isAffine_strictHenselizationBaseFiber`,
  `Stacks.EtaleCohomology.isAffine_strictHenselizationSourceFiber`,
  `Stacks.EtaleCohomology.isAffine_strictHenselizationPointFiber` — all three fibre products
  occurring in the tag are affine, although `S` need not be.
* `Stacks.EtaleCohomology.indEtale_strictHenselizationBaseFiberRing` — the coordinate ring of
  `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is ind-étale over `K`, that is, a filtered colimit of étale
  `K`-algebras. This is the first sentence of the source's proof.
* `Stacks.EtaleCohomology.locallyConstant_map_bijective_iff` — post-composition with a map is
  bijective on locally constant functions on a nonempty space exactly when the map is.
* `Stacks.EtaleCohomology.bijective_strictHenselizationFiberRestriction_iff_of_presentation` — the
  equivalence of the two conditions as printed in Tag 0EZV, for a locally constant presentation of
  the cohomology over `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K`.

Tag 0EZV as printed is false, and such a presentation need not exist; see
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationFiberErratum`. The corrected
statement, condition (1) if and only if condition (2) at every lift `k'` of `Spec K ⟶ S` to the
strict henselization, is
`Stacks.EtaleCohomology.bijective_strictHenselizationFiberCohomologyPullback_iff` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSeparablyClosedFiberCohomology`.

## Implementation notes

An equality of cohomology groups of the source is read, as elsewhere in the library, as
bijectivity of the canonical restriction map
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` on `H^q`. The coefficient sheaf upstairs
is accordingly the inverse image along the comparison morphism of the coefficient sheaf
downstairs, which is itself the inverse image of `ℱ` along the projection to `Spec K`; the source
writes `ℱ` for all four groups.

The structure `Stacks.EtaleCohomology.SepClosedFiberLocallyConstantPresentation` records the
cohomological identification of the source's proof: that the two cohomology groups over
`Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` are locally constant functions on the limit index space with
values in the two groups of condition (2) at the given point, compatibly with restriction. That
identification is where the source's proof goes wrong: the copies of `Spec K` in the stages of the
limit correspond to the different lifts `k'` of `Spec K ⟶ S` to `Spec(𝒪^{sh}_{S,s̄})`, and the
fibres of the morphism of strict henselizations over them need not agree with the fibre over the
given point. The correct form of the argument, with each copy over its own lift, is carried out in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSeparablyClosedFiberCohomology`,
which uses the geometric input proved here: the local structure of étale schemes over a separably
closed field, the identification which turns both conditions into conditions on base changes of a
single morphism, the affineness of all three fibre products, and the presentation of the
coordinate ring of `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` as a filtered colimit of étale `K`-algebras.

The index space of the presentation is a topological space and the two identifications are of
locally constant functions on it, rather than a filtered colimit of finite direct sums over the
index sets: for a cofiltered limit of finite discrete spaces the two descriptions agree, and the
locally constant form is what the final step uses. Nonemptiness of the index space is a field of
the datum; its geometric source is
`Stacks.EtaleCohomology.strictHenselizationBaseFiberSection`, the section of the projection
coming from the given point of the strict henselization, which is the source's reason for the
index sets `A_i` being nonempty.

## References

* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

open scoped TensorProduct

universe u v w

namespace Stacks.EtaleCohomology

/-! ### Étale schemes over a separably closed field -/

section SepClosedEtale

/-- An étale algebra over a field is finite as a module and hence artinian, so it has only
finitely many primes. -/
public theorem finite_primeSpectrum_of_etale (K : Type u) [Field K] (A : Type u) [CommRing A]
    [Algebra K A] [Algebra.Etale K A] : Finite (PrimeSpectrum A) := by
  have := Algebra.FormallyUnramified.finite_of_free K A
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  infer_instance

/-- An algebra admitting a point with values in the base field is nontrivial, so its prime
spectrum is nonempty. -/
public theorem nonempty_primeSpectrum_of_algHom (K : Type u) [Field K] (A : Type u) [CommRing A]
    [Algebra K A] (g : A →ₐ[K] K) : Nonempty (PrimeSpectrum A) := by
  have : Nontrivial A := ⟨0, 1, fun h => one_ne_zero (α := K) (by simpa using congrArg g h.symm)⟩
  infer_instance

/-- **An étale scheme over a separably closed field is a finite disjoint union of copies of that
field.** An étale algebra `A` over a separably closed field `K` is the product of copies of `K`
indexed by its finitely many primes, by `Algebra.FormallyEtale.equivPiOfIsSepClosed`, and the
spectrum of a finite product of rings is the coproduct of their spectra. -/
@[ega "IV 17.6.2" "special case"]
public def specIsoSigmaOfIsSepClosed (K : Type u) [Field K] [IsSepClosed K] (A : Type u)
    [CommRing A] [Algebra K A] [Algebra.Etale K A] :
    Spec (CommRingCat.of A) ≅ ∐ fun _ : PrimeSpectrum A => Spec (CommRingCat.of K) :=
  haveI : Finite (PrimeSpectrum A) := finite_primeSpectrum_of_etale K A
  let e : CommRingCat.of A ≅ CommRingCat.of (PrimeSpectrum A → K) :=
    (Algebra.FormallyEtale.equivPiOfIsSepClosed K A).toRingEquiv.toCommRingCatIso
  asIso (Spec.map e.inv) ≪≫ (asIso (sigmaSpec fun _ : PrimeSpectrum A => CommRingCat.of K)).symm

end SepClosedEtale

/-! ### Bijectivity for locally constant functions -/

section LocallyConstant

variable {A : Type*} [TopologicalSpace A] {M N : Type*}

/-- Post-composition with a bijection is bijective on locally constant functions: a two-sided
inverse is post-composition with the inverse map. -/
public theorem locallyConstant_map_bijective (φ : M → N) (hφ : Function.Bijective φ) :
    Function.Bijective (LocallyConstant.map (X := A) φ) := by
  refine ⟨fun g g' h => LocallyConstant.ext fun a => hφ.1 (DFunLike.congr_fun h a), fun h => ?_⟩
  exact ⟨LocallyConstant.map (Function.surjInv hφ.2) h,
    LocallyConstant.ext fun a => Function.surjInv_eq hφ.2 (h a)⟩

/-- If post-composition with `φ` is bijective on locally constant functions on a nonempty space,
then `φ` is bijective: constant functions detect injectivity, and evaluating a preimage of a
constant function at a point of the space detects surjectivity. -/
public theorem bijective_of_locallyConstant_map_bijective [Nonempty A] (φ : M → N)
    (h : Function.Bijective (LocallyConstant.map (X := A) φ)) : Function.Bijective φ := by
  obtain ⟨a⟩ := ‹Nonempty A›
  refine ⟨fun m m' hm => ?_, fun n => ?_⟩
  · exact DFunLike.congr_fun (h.1 (a₁ := LocallyConstant.const A m)
      (a₂ := LocallyConstant.const A m') (LocallyConstant.ext fun _ => hm)) a
  · obtain ⟨g, hg⟩ := h.2 (LocallyConstant.const A n)
    exact ⟨g a, DFunLike.congr_fun hg a⟩

/-- Post-composition with a map is bijective on locally constant functions on a nonempty space
exactly when the map is bijective. -/
public theorem locallyConstant_map_bijective_iff [Nonempty A] (φ : M → N) :
    Function.Bijective (LocallyConstant.map (X := A) φ) ↔ Function.Bijective φ :=
  ⟨bijective_of_locallyConstant_map_bijective φ, locallyConstant_map_bijective φ⟩

end LocallyConstant

/-! ### Fibre products over a monomorphism -/

section Mono

/-- A cartesian square stays cartesian after composing both maps to the base with a
monomorphism: the universal property is unchanged, because the monomorphism may be cancelled
from the compatibility condition of a competing cone. -/
public theorem isPullback_comp_mono {C : Type*} [Category C] {P X Y Z W : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z} (sq : IsPullback fst snd a b) (m : Z ⟶ W) [Mono m] :
    IsPullback fst snd (a ≫ m) (b ≫ m) where
  w := by rw [← Category.assoc, sq.w, Category.assoc]
  isLimit' := ⟨PullbackCone.IsLimit.mk _ (fun s => sq.lift s.fst s.snd
      ((cancel_mono m).mp (by simpa only [Category.assoc] using s.condition)))
    (fun s => sq.lift_fst _ _ _) (fun s => sq.lift_snd _ _ _)
    (fun s t hfst hsnd => sq.hom_ext (by simpa using hfst) (by simpa using hsnd))⟩

/-- A fibre product of affine schemes over an arbitrary base is affine as soon as both structure
morphisms factor through a monomorphism from an affine scheme: the fibre product over the base
is then the fibre product over that affine scheme. -/
@[ega "I 3.2.2" "more general"]
public theorem isAffine_pullback_of_mono {X Y Z W : Scheme.{u}} (m : Z ⟶ W) [Mono m]
    {a : X ⟶ W} {b : Y ⟶ W} (a' : X ⟶ Z) (b' : Y ⟶ Z)
    (ha : a' ≫ m = a) (hb : b' ≫ m = b) [IsAffine X] [IsAffine Y] [IsAffine Z] :
    IsAffine (pullback a b) := by
  subst ha
  subst hb
  exact IsAffine.of_isIso
    (isPullback_comp_mono (IsPullback.of_hasPullback a' b') m).isoPullback.inv

end Mono

/-! ### The two fibre products at a geometric point -/

section Fibers

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X) {K : Type u} [Field K]
  (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))

/-- The structure morphism `Spec K ⟶ S` of a point of the strict henselization of `S` at the
image of a geometric point of `X`. -/
public abbrev sepClosedPointToBase : Spec (CommRingCat.of K) ⟶ S :=
  k ≫ strictHenselizationToBase B S hS (x.map f)

/-- The fibre product `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K`, where `s̄` is the image of the geometric
point `x̄` and `Spec K ⟶ S` is the structure morphism of the given point. -/
public abbrev strictHenselizationBaseFiber : Scheme.{u} :=
  pullback (strictHenselizationToBase B S hS (x.map f)) (sepClosedPointToBase B hS f x k)

/-- The fibre product `Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K`. -/
public abbrev strictHenselizationSourceFiber : Scheme.{u} :=
  pullback (strictHenselizationToBase B X hX x ≫ f) (sepClosedPointToBase B hS f x k)

/-- The fibre product `Spec(𝒪^{sh}_{X,x̄}) ×_{Spec(𝒪^{sh}_{S,s̄})} Spec K`, taken along the
morphism of strict henselizations and the given point. -/
public abbrev strictHenselizationPointFiber : Scheme.{u} :=
  pullback (strictHenselizationSquareMap B hX hS f x) k

/-- The canonical morphism `Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K ⟶ Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K`: the
morphism of strict henselizations on the first factor and the identity on the second. -/
public def strictHenselizationFiberMap :
    strictHenselizationSourceFiber B hX hS f x k ⟶ strictHenselizationBaseFiber B hS f x k :=
  pullback.lift
    (pullback.fst (strictHenselizationToBase B X hX x ≫ f) (sepClosedPointToBase B hS f x k) ≫
      strictHenselizationSquareMap B hX hS f x)
    (pullback.snd (strictHenselizationToBase B X hX x ≫ f) (sepClosedPointToBase B hS f x k))
    (by
      rw [Category.assoc, strictHenselizationSquareMap_comp]
      exact pullback.condition)

@[simp]
public lemma strictHenselizationFiberMap_comp_fst :
    strictHenselizationFiberMap B hX hS f x k ≫
        pullback.fst (strictHenselizationToBase B S hS (x.map f))
          (sepClosedPointToBase B hS f x k) =
      pullback.fst (strictHenselizationToBase B X hX x ≫ f)
          (sepClosedPointToBase B hS f x k) ≫
        strictHenselizationSquareMap B hX hS f x :=
  pullback.lift_fst _ _ _

@[simp]
public lemma strictHenselizationFiberMap_comp_snd :
    strictHenselizationFiberMap B hX hS f x k ≫
        pullback.snd (strictHenselizationToBase B S hS (x.map f))
          (sepClosedPointToBase B hS f x k) =
      pullback.snd (strictHenselizationToBase B X hX x ≫ f)
        (sepClosedPointToBase B hS f x k) :=
  pullback.lift_snd _ _ _

/-- The canonical morphism `Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K ⟶ Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is a
base change of the morphism of strict henselizations along the projection
`Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})`: both fibre products are
`Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K`. -/
public theorem isPullback_strictHenselizationFiberMap :
    IsPullback
      (pullback.fst (strictHenselizationToBase B X hX x ≫ f)
        (sepClosedPointToBase B hS f x k))
      (strictHenselizationFiberMap B hX hS f x k)
      (strictHenselizationSquareMap B hX hS f x)
      (pullback.fst (strictHenselizationToBase B S hS (x.map f))
        (sepClosedPointToBase B hS f x k)) := by
  refine IsPullback.of_bot ?_ (strictHenselizationFiberMap_comp_fst B hX hS f x k).symm
    (IsPullback.of_hasPullback _ _)
  rw [strictHenselizationFiberMap_comp_snd, strictHenselizationSquareMap_comp]
  exact IsPullback.of_hasPullback _ _

/-- The section of the projection `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K ⟶ Spec K` determined by the
given point `Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})`. Its existence is why the index sets of the limit
presentation of `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` by disjoint unions of copies of `Spec K` are
nonempty. -/
public def strictHenselizationBaseFiberSection :
    Spec (CommRingCat.of K) ⟶ strictHenselizationBaseFiber B hS f x k :=
  pullback.lift k (𝟙 _) (by simp)

@[simp]
public lemma strictHenselizationBaseFiberSection_comp_fst :
    strictHenselizationBaseFiberSection B hS f x k ≫
        pullback.fst (strictHenselizationToBase B S hS (x.map f))
          (sepClosedPointToBase B hS f x k) = k :=
  pullback.lift_fst _ _ _

@[simp]
public lemma strictHenselizationBaseFiberSection_comp_snd :
    strictHenselizationBaseFiberSection B hS f x k ≫
        pullback.snd (strictHenselizationToBase B S hS (x.map f))
          (sepClosedPointToBase B hS f x k) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The canonical morphism from the strict henselization at a geometric point to the local
scheme at its image: the spectrum of the ordinary-to-étale germ map. -/
public def strictHenselizationToStalk :
    strictHenselization B S hS (x.map f) ⟶
      Spec (CommRingCat.of ↥(S.presheaf.stalk
        ((x.map f).hom (IsLocalRing.closedPoint (x.map f).residueField)))) :=
  Spec.map (CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS (x.map f)))

/-- The structure morphism of the strict henselization factors through the local scheme at the
image of the geometric point; this is how `AlgebraicGeometry.strictHenselizationToBase` is
defined. -/
public theorem strictHenselizationToStalk_comp :
    strictHenselizationToStalk B hS f x ≫
        S.fromSpecStalk ((x.map f).hom (IsLocalRing.closedPoint (x.map f).residueField)) =
      strictHenselizationToBase B S hS (x.map f) := rfl

/-- **`Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is affine**, although `S` need not be: both structure
morphisms factor through the monomorphism `Spec(𝒪_{S,s}) ⟶ S`, so the fibre product is the
fibre product over the affine local scheme at `s`. -/
public theorem isAffine_strictHenselizationBaseFiber :
    IsAffine (strictHenselizationBaseFiber B hS f x k) :=
  isAffine_pullback_of_mono
    (S.fromSpecStalk ((x.map f).hom (IsLocalRing.closedPoint (x.map f).residueField)))
    (strictHenselizationToStalk B hS f x) (k ≫ strictHenselizationToStalk B hS f x)
    (strictHenselizationToStalk_comp B hS f x)
    (by rw [Category.assoc, strictHenselizationToStalk_comp])

/-- **`Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K` is affine.** Same argument as for
`Stacks.EtaleCohomology.isAffine_strictHenselizationBaseFiber`, the structure morphism of
`Spec(𝒪^{sh}_{X,x̄})` factoring through `Spec(𝒪_{S,s}) ⟶ S` via the morphism of strict
henselizations. -/
public theorem isAffine_strictHenselizationSourceFiber :
    IsAffine (strictHenselizationSourceFiber B hX hS f x k) :=
  isAffine_pullback_of_mono
    (S.fromSpecStalk ((x.map f).hom (IsLocalRing.closedPoint (x.map f).residueField)))
    (strictHenselizationSquareMap B hX hS f x ≫ strictHenselizationToStalk B hS f x)
    (k ≫ strictHenselizationToStalk B hS f x)
    (by rw [Category.assoc, strictHenselizationToStalk_comp, strictHenselizationSquareMap_comp])
    (by rw [Category.assoc, strictHenselizationToStalk_comp])

/-- **`Spec(𝒪^{sh}_{X,x̄}) ×_{Spec(𝒪^{sh}_{S,s̄})} Spec K` is affine**, being a fibre product of
affine schemes over an affine scheme. -/
public theorem isAffine_strictHenselizationPointFiber :
    IsAffine (strictHenselizationPointFiber B hX hS f x k) :=
  AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
    (strictHenselizationSquareMap B hX hS f x) k

/-! ### The base fibre as the spectrum of an ind-étale `K`-algebra -/

/-- The ordinary local ring of `S` at the image of the geometric point `x̄`. -/
public abbrev stalkRingAtImage : Type u :=
  ↥(S.presheaf.stalk ((x.map f).hom (IsLocalRing.closedPoint (x.map f).residueField)))

/-- The `𝒪_{S,s}`-algebra structure on `K` determined by the given point of the strict
henselization: the ring map underlying `Spec K ⟶ Spec(𝒪^{sh}_{S,s̄}) ⟶ Spec(𝒪_{S,s})`. -/
@[instance_reducible]
public def sepClosedPointAlgebra : Algebra (stalkRingAtImage f x) K :=
  (Spec.preimage (k ≫ strictHenselizationToStalk B hS f x)).hom.toAlgebra

/-- **`Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is the spectrum of `𝒪^{sh}_{S,s̄} ⊗_{𝒪_{S,s}} K`.** By
`Stacks.EtaleCohomology.isAffine_strictHenselizationBaseFiber` the fibre product over `S` is the
fibre product over the affine local scheme at `s`, and a fibre product of affine schemes over an
affine scheme is the spectrum of the tensor product of their coordinate rings. -/
public def strictHenselizationBaseFiberIsoSpec :
    letI := sepClosedPointAlgebra B hS f x k
    strictHenselizationBaseFiber B hS f x k ≅
      Spec (CommRingCat.of (↥(etaleLocalRing B S hS (x.map f)) ⊗[stalkRingAtImage f x] K)) :=
  letI := sepClosedPointAlgebra B hS f x k
  have hk : Spec.map (CommRingCat.ofHom (algebraMap (stalkRingAtImage f x) K)) =
      k ≫ strictHenselizationToStalk B hS f x := by
    have halg : algebraMap (stalkRingAtImage f x) K =
        (Spec.preimage (k ≫ strictHenselizationToStalk B hS f x)).hom :=
      RingHom.algebraMap_toAlgebra _
    rw [halg, CommRingCat.ofHom_hom, Spec.map_preimage]
  (isPullback_comp_mono (IsPullback.of_hasPullback
      (strictHenselizationToStalk B hS f x) (k ≫ strictHenselizationToStalk B hS f x))
    (S.fromSpecStalk
      ((x.map f).hom (IsLocalRing.closedPoint (x.map f).residueField)))).isoPullback.symm ≪≫
    eqToIso (by rw [hk, strictHenselizationToStalk, algebraMap_etaleLocalRing]) ≪≫
    pullbackSpecIso (stalkRingAtImage f x) _ K

/-- **The coordinate ring of `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is ind-étale over `K`**, that is, a
filtered colimit of étale `K`-algebras: the étale local ring is ind-étale over the ordinary local
ring at the image of `x̄` by `AlgebraicGeometry.indEtale_etaleLocalRing`, and ind-étaleness is
stable under base change by Stacks 0BSH.

This is the first sentence of the proof of Tag 0EZV. Together with
`Stacks.EtaleCohomology.specIsoSigmaOfIsSepClosed`, which turns each étale `K`-algebra of the
presentation into a finite coproduct of copies of `Spec K`, it is the geometric input the tag's
limit computation rests on. -/
public theorem indEtale_strictHenselizationBaseFiberRing :
    letI := sepClosedPointAlgebra B hS f x k
    StacksDraft.IndEtale K (K ⊗[stalkRingAtImage f x] ↥(etaleLocalRing B S hS (x.map f))) :=
  letI := sepClosedPointAlgebra B hS f x k
  StacksDraft.indEtale_tensorProduct K (indEtale_etaleLocalRing B S hS (x.map f))

end Fibers

/-! ### The two restriction maps on cohomology -/

section Restriction

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X) {K : Type u} [Field K]
  (k : Spec (CommRingCat.of K) ⟶ strictHenselization B S hS (x.map f))
  [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (strictHenselizationBaseFiber B hS f x k).smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (strictHenselizationSourceFiber B hX hS f x k).smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (strictHenselizationPointFiber B hX hS f x k).smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v}]

/-- The coefficient sheaf on `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K`: the inverse image of an abelian
sheaf on the small étale site of `Spec K` along the projection. -/
public abbrev strictHenselizationBaseFiberCoeff
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    Sheaf (strictHenselizationBaseFiber B hS f x k).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v} :=
  (etaleAbelianInverseImage.{u, v}
    (pullback.snd (strictHenselizationToBase B S hS (x.map f))
      (sepClosedPointToBase B hS f x k))).obj F

variable
  [HasExt.{w} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf (strictHenselizationBaseFiber B hS f x k).smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf (strictHenselizationSourceFiber B hX hS f x k).smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf (strictHenselizationPointFiber B hX hS f x k).smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v})]

/-- The canonical restriction map
`H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K, ℱ) ⟶ H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K, ℱ)`, whose
bijectivity is condition (1) of Tag 0EZV. -/
public abbrev strictHenselizationFiberRestriction
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (q : ℕ) :
    Sheaf.H.{w} (strictHenselizationBaseFiberCoeff.{u, v} B hS f x k F) q →+
      Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v}
        (strictHenselizationFiberMap B hX hS f x k)).obj
          (strictHenselizationBaseFiberCoeff.{u, v} B hS f x k F)) q :=
  etaleCohomologyRestrictionMap.{u, v, w} (strictHenselizationFiberMap B hX hS f x k)
    (strictHenselizationBaseFiberCoeff.{u, v} B hS f x k F) q

/-- The canonical restriction map
`H^q(Spec K, ℱ) ⟶ H^q(Spec(𝒪^{sh}_{X,x̄}) ×_{Spec(𝒪^{sh}_{S,s̄})} Spec K, ℱ)`, whose bijectivity
is condition (2) of Tag 0EZV. -/
public abbrev strictHenselizationPointRestriction
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (q : ℕ) :
    Sheaf.H.{w} F q →+
      Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v}
        (pullback.snd (strictHenselizationSquareMap B hX hS f x) k)).obj F) q :=
  etaleCohomologyRestrictionMap.{u, v, w}
    (pullback.snd (strictHenselizationSquareMap B hX hS f x) k) F q

/-- **A locally constant presentation of the cohomology over `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K`.**
The proof of Tag 0EZV in the source writes that scheme as a cofiltered limit of finite disjoint
unions of copies of `Spec K` and describes both cohomology groups of condition (1) as locally
constant functions on the limit index space with values in the corresponding cohomology groups of
condition (2) at the given point `k`. This structure records such a description over a nonempty
space `A`, together with the fact that under it the restriction map of condition (1) is computed
pointwise from the restriction map of condition (2).

The description is in general wrong: each copy of `Spec K` lies over its own lift of
`Spec K ⟶ S` to the strict henselization, whose fibre need not be the fibre over `k`, and at the
counterexample to the tag the structure is empty
(`Stacks.EtaleCohomology.isEmpty_sepClosedFiberLocallyConstantPresentation`). -/
public structure SepClosedFiberLocallyConstantPresentation [IsSepClosed K] (A : Type u)
    [TopologicalSpace A]
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (q : ℕ) where
  /-- The index space of the limit presentation is nonempty, because the point
  `Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` is given. -/
  nonempty : Nonempty A
  /-- The cohomology over `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is the group of locally constant
  functions on `A` with values in the cohomology over `Spec K`. -/
  baseEquiv : Sheaf.H.{w} (strictHenselizationBaseFiberCoeff.{u, v} B hS f x k F) q ≃+
    LocallyConstant A (Sheaf.H.{w} F q)
  /-- The cohomology over `Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K` is the group of locally constant
  functions on `A` with values in the cohomology over
  `Spec(𝒪^{sh}_{X,x̄}) ×_{Spec(𝒪^{sh}_{S,s̄})} Spec K`. -/
  sourceEquiv : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v}
      (strictHenselizationFiberMap B hX hS f x k)).obj
        (strictHenselizationBaseFiberCoeff.{u, v} B hS f x k F)) q ≃+
    LocallyConstant A (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v}
      (pullback.snd (strictHenselizationSquareMap B hX hS f x) k)).obj F) q)
  /-- Under these descriptions the restriction map over `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` is
  post-composition with the restriction map over `Spec K`. -/
  compat : ∀ c, sourceEquiv
      (strictHenselizationFiberRestriction.{u, v, w} B hX hS f x k F q c) =
    LocallyConstant.map
      (strictHenselizationPointRestriction.{u, v, w} B hX hS f x k F q) (baseEquiv c)

/-- **The printed equivalence of Tag 0EZV, for a locally constant presentation.** Let
`f : X ⟶ S` be a morphism of schemes, `x̄` a geometric point of `X` with image `s̄`,
`k : Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` with `K` separably closed, `ℱ` an abelian sheaf on `Spec K` and
`q ≥ 0`. Given a presentation `Stacks.EtaleCohomology.SepClosedFiberLocallyConstantPresentation`
of the two cohomology groups over `Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K` as locally constant functions on
a nonempty space with values in the two groups over `Spec K`, compatibly with restriction, the
restriction map of condition (1) is bijective if and only if that of condition (2) at `k` is.

Such a presentation need not exist, and the equivalence fails in general: Tag 0EZV as printed is
false (`Stacks.EtaleCohomology.not_forall_bijective_strictHenselizationFiberRestriction_iff`), and
at its counterexample no presentation exists over any index space
(`Stacks.EtaleCohomology.isEmpty_sepClosedFiberLocallyConstantPresentation`). The corrected
statement, condition (1) if and only if condition (2) at every lift `k'` of `Spec K ⟶ S`, is
`Stacks.EtaleCohomology.bijective_strictHenselizationFiberCohomologyPullback_iff`. -/
public theorem bijective_strictHenselizationFiberRestriction_iff_of_presentation
    [IsSepClosed K] (A : Type u) [TopologicalSpace A]
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (q : ℕ)
    (P : SepClosedFiberLocallyConstantPresentation.{u, v, w} B hX hS f x k A F q) :
    Function.Bijective (strictHenselizationFiberRestriction.{u, v, w} B hX hS f x k F q) ↔
      Function.Bijective (strictHenselizationPointRestriction.{u, v, w} B hX hS f x k F q) := by
  have := P.nonempty
  have hcomp : (⇑P.sourceEquiv) ∘
      (⇑(strictHenselizationFiberRestriction.{u, v, w} B hX hS f x k F q)) =
      LocallyConstant.map
        (⇑(strictHenselizationPointRestriction.{u, v, w} B hX hS f x k F q)) ∘
          (⇑P.baseEquiv) :=
    funext P.compat
  calc Function.Bijective (strictHenselizationFiberRestriction.{u, v, w} B hX hS f x k F q)
      ↔ Function.Bijective ((⇑P.sourceEquiv) ∘
          (⇑(strictHenselizationFiberRestriction.{u, v, w} B hX hS f x k F q))) :=
        (P.sourceEquiv.bijective.of_comp_iff' _).symm
    _ ↔ Function.Bijective (LocallyConstant.map
          (⇑(strictHenselizationPointRestriction.{u, v, w} B hX hS f x k F q)) ∘
            (⇑P.baseEquiv)) := by rw [hcomp]
    _ ↔ Function.Bijective (LocallyConstant.map (X := A)
          (⇑(strictHenselizationPointRestriction.{u, v, w} B hX hS f x k F q))) :=
        Function.Bijective.of_comp_iff _ P.baseEquiv.bijective
    _ ↔ Function.Bijective
          (strictHenselizationPointRestriction.{u, v, w} B hX hS f x k F q) :=
        locallyConstant_map_bijective_iff _

end Restriction

end Stacks.EtaleCohomology

end
