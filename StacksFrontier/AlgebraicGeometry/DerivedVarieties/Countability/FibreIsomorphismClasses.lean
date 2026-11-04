module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.IsomorphismClasses
public import StacksFrontier.AlgebraicGeometry.Limits.CountableIsomorphismFamilies
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Isomorphism classes of the fibres of a family

Let `K` be a field, let `q : S ⟶ Spec K` and let `Y` be a scheme over `S`. This file counts the
isomorphism classes, as schemes over `K`, of the fibres `Y_t` of `Y` at the `K`-points
`t : Spec K ⟶ S` of `S`, possibly restricted to the points where some condition holds.

Two mechanisms are provided.

* A family that is *locally constant* — `S` is covered by opens `U` over which `Y` becomes a
  constant family `Y₀ ×_K U` — has only **finitely** many isomorphism classes of fibres, as soon
  as `S` is quasi-compact. This is the step that turns the conclusion of [Stacks, Tag 0G0S] into
  a finiteness statement.
* If a countable family of morphisms `Tᵢ ⟶ S` jointly accounts for all the `K`-points of `S`
  under consideration, then the isomorphism classes of fibres of `Y` at those points are
  exhausted by the isomorphism classes of fibres of the base changes `Y ×_S Tᵢ`. This is the step
  that turns the conclusion of [Stacks, Tag 0G0X] into a countability statement.

Combining the two with [Stacks, Tag 0G0X] itself gives the paragraph of [Stacks, Tag 0G11] that
begins "Let `S` be a finite type scheme over `K`": for `X` and `Y` over a finite-type `S` and a
fixed `X₀` over `K`, the isomorphism classes of the fibres `Y_t` at those `K`-points `t` with
`X_t ≅ X₀` form a countable set, **provided** every finite-type base change `T ⟶ S` over which
`X` becomes the constant family `X₀ × T` makes `Y ×_S T ⟶ T` locally constant. That proviso is
exactly what [Stacks, Tag 0G0K] and [Stacks, Tag 0G0S] supply, and it is the only input to
[Stacks, Tag 0G11] that is not proved here.

A last lemma assembles the outer layer of [Stacks, Tag 0G11]: a countable family of systems
accounting for every object satisfying a predicate `D`, together with countability of the fibre
classes of each system, bounds the isomorphism classes of objects satisfying `D`. Fed with
[Stacks, Tag 0G0Y] and with the paragraph above, this is [Stacks, Tag 0G11].

## Main definitions

* `AlgebraicGeometry.IsomorphismClassOver` — isomorphism classes of schemes over `Spec K`.
* `AlgebraicGeometry.fibreClassSet` — the set of isomorphism classes of fibres of a family at the
  `K`-points of its base satisfying a given condition.
* `AlgebraicGeometry.IsLocallyConstantFamily` — the conclusion of [Stacks, Tag 0G0S]: the base is
  covered by opens over which the family is a constant family.

## Main results

* `AlgebraicGeometry.exists_mem_opens_of_rationalPoints` — over an algebraically closed field,
  opens around the images of all `K`-points cover a locally-of-finite-type base.
* `AlgebraicGeometry.isLocallyConstantFamily_of_rationalPoints` — over an algebraically closed
  field, trivialising near the image of every `K`-point already gives an open cover of the base.
* `AlgebraicGeometry.finite_fibreClassSet_of_isLocallyConstantFamily` — a locally constant family
  over a quasi-compact base has finitely many isomorphism classes of fibres.
* `AlgebraicGeometry.countable_fibreClassSet_of_countable_family` — a countable family of base
  changes accounting for the relevant `K`-points bounds the fibre classes.
* `AlgebraicGeometry.countable_fibreClassSet_of_locallyConstant_baseChanges` — the inner paragraph
  of [Stacks, Tag 0G11].
* `AlgebraicGeometry.countable_isomorphismClasses_of_countable_systems` — the outer layer of
  [Stacks, Tag 0G11].

## Implementation notes

A `K`-point of `S` relative to `q : S ⟶ Spec K` is a morphism `t : Spec K ⟶ S` with
`t ≫ q = 𝟙 (Spec K)`; the fibre of `Y : Over S` at `t` is `(Over.pullback t).obj Y`, an object of
`Over (Spec K)`. Isomorphism classes are taken in `Over (Spec K)`, i.e. isomorphism over `K`,
which is what the source means by "isomorphism classes of smooth proper schemes over `K`".

"At most countably many isomorphism classes of objects satisfying `D`" is rendered as
`Set.Countable` of the set of classes represented by some object satisfying `D`; this is the
honest reading of the source's phrase and does not require `D` to be invariant under
isomorphism.

Nothing below assumes the fibres are smooth, proper, or of finite type: the counting arguments
need none of that, so the lemmas are stated without those hypotheses and apply a fortiori in the
situation of the source.

## References

* [Stacks Project, Tag 0G11](https://stacks.math.columbia.edu/tag/0G11)
* [Stacks Project, Tag 0G0X](https://stacks.math.columbia.edu/tag/0G0X)
* [Stacks Project, Tag 0G0S](https://stacks.math.columbia.edu/tag/0G0S)
* [Stacks Project, Tag 0G0Y](https://stacks.math.columbia.edu/tag/0G0Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Isomorphism classes of schemes over `Spec K`, i.e. of objects of `Over (Spec K)`. -/
abbrev IsomorphismClassOver (K : Type u) [Field K] : Type (u + 1) :=
  Quotient (isIsomorphicSetoid (Over (Spec (CommRingCat.of K))))

/-- The isomorphism class over `K` of a scheme over `Spec K`. -/
abbrev isomorphismClassOver (Z : Over (Spec (CommRingCat.of K))) : IsomorphismClassOver K :=
  Quotient.mk _ Z

/-- The fibre of a family `Y` over `S` at a morphism `t : Spec K ⟶ S`, as a scheme over
`Spec K`. -/
abbrev fibreOver {S : Scheme.{u}} (Y : Over S) (t : Spec (CommRingCat.of K) ⟶ S) :
    Over (Spec (CommRingCat.of K)) :=
  (Over.pullback t).obj Y

/-- The set of isomorphism classes over `K` of the fibres of `Y : Over S` at the `K`-points of
`S` relative to `q : S ⟶ Spec K` at which the condition `P` holds. -/
def fibreClassSet {S : Scheme.{u}} (q : S ⟶ Spec (CommRingCat.of K)) (Y : Over S)
    (P : (Spec (CommRingCat.of K) ⟶ S) → Prop) : Set (IsomorphismClassOver K) :=
  {c | ∃ t : Spec (CommRingCat.of K) ⟶ S,
    t ≫ q = 𝟙 _ ∧ P t ∧ c = isomorphismClassOver (fibreOver Y t)}

/-- **The conclusion of [Stacks, Tag 0G0S].** The family `Y ⟶ S` over `q : S ⟶ Spec K` is
*locally constant* if `S` is covered by opens `U` over which `Y` becomes the constant family
`Y₀ ×_K U` for some scheme `Y₀` over `K`.

The source also records that `Y₀` is smooth and proper over `K`; that is not needed for the
counting below and so is not part of the predicate. -/
def IsLocallyConstantFamily {S : Scheme.{u}} (q : S ⟶ Spec (CommRingCat.of K))
    (Y : Over S) : Prop :=
  ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ ∃ Y₀ : Over (Spec (CommRingCat.of K)),
    Nonempty ((Over.pullback U.ι).obj Y ≅ (Over.pullback (U.ι ≫ q)).obj Y₀)

section Fibres

/-- Taking the fibre of a base change `Y ×_S T` at `t : Spec K ⟶ T` is taking the fibre of `Y`
at the composite `t ≫ a : Spec K ⟶ S`. -/
noncomputable def fibreOverPullbackIso {S T : Scheme.{u}} (a : T ⟶ S) (Y : Over S)
    (t : Spec (CommRingCat.of K) ⟶ T) :
    fibreOver ((Over.pullback a).obj Y) t ≅ fibreOver Y (t ≫ a) :=
  ((Over.pullbackComp t a).app Y).symm

/-- The fibre of a constant family `Y₀ ×_K S` at a `K`-point of `S` is `Y₀`. -/
noncomputable def fibreOverConstantIso {S : Scheme.{u}} {q : S ⟶ Spec (CommRingCat.of K)}
    (Y₀ : Over (Spec (CommRingCat.of K))) {t : Spec (CommRingCat.of K) ⟶ S}
    (ht : t ≫ q = 𝟙 _) : fibreOver ((Over.pullback q).obj Y₀) t ≅ Y₀ :=
  fibreOverPullbackIso q Y₀ t ≪≫
    eqToIso (congrArg (fun h => (Over.pullback h).obj Y₀) ht) ≪≫ Over.pullbackId.app Y₀

/-- The fibre of a base change `Y ×_S T` at `t'` is the fibre of `Y` at `t` when `t' ≫ a = t`. -/
private theorem nonempty_fibreOver_pullback_iso {S T : Scheme.{u}} (a : T ⟶ S) (Y : Over S)
    {t' : Spec (CommRingCat.of K) ⟶ T} {t : Spec (CommRingCat.of K) ⟶ S} (h : t' ≫ a = t) :
    Nonempty (fibreOver ((Over.pullback a).obj Y) t' ≅ fibreOver Y t) := by
  subst h
  exact ⟨fibreOverPullbackIso a Y t'⟩

/-- **Opens around the `K`-points already cover.** Over an algebraically closed field, if `S` is
locally of finite type and every `K`-point of `S` has its image in some open `U` with property
`P`, then every point of `S` lies in an open with property `P`.

A locally-of-finite-type scheme over a field is a Jacobson space, so every point has a closed
point in the closure of its singleton; over an algebraically closed field a closed point is the
image of a `K`-point ([Mathlib's `AlgebraicGeometry.pointOfClosedPoint`]), hence lies in one of
the given opens, and an open neighbourhood of a point of `closure {x}` contains `x`. -/
@[sga "3 VIB 1.3.0" "special case", sga "3 XXV 4.4" "more general"]
theorem exists_mem_opens_of_rationalPoints [IsAlgClosed K] {S : Scheme.{u}}
    (q : S ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] (P : S.Opens → Prop)
    (h : ∀ t : Spec (CommRingCat.of K) ⟶ S, t ≫ q = 𝟙 _ →
      ∃ U : S.Opens, Set.range t.base ⊆ (U : Set S) ∧ P U) :
    ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ P U := by
  have : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace q
  -- the union of the opens with property `P`
  set W : Set S := {z | ∃ U : S.Opens, P U ∧ z ∈ U} with hW
  have hWopen : IsOpen W := by
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro z ⟨U, hU, hzU⟩
    exact ⟨(U : Set S), fun w hw => ⟨U, hU, hw⟩, U.2, hzU⟩
  -- every closed point of `S` lies in `W`, because it is the image of a `K`-point
  have hWclosed : ∀ y : S, IsClosed {y} → y ∈ W := by
    intro y hy
    obtain ⟨U, hrange, hU⟩ := h (pointOfClosedPoint q y hy) (pointOfClosedPoint_comp q y hy)
    exact ⟨U, hU, hrange ⟨IsLocalRing.closedPoint K, pointOfClosedPoint_apply q y hy _⟩⟩
  intro x
  have hxW : x ∈ W := by
    obtain ⟨y, hyx, hy⟩ :=
      nonempty_inter_closedPoints (X := S) (Z := closure {x})
        ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hyW : y ∈ W := hWclosed y hy
    have := (mem_closure_iff.1 hyx) W hWopen hyW
    obtain ⟨z, hzW, hzx⟩ := this
    rwa [Set.mem_singleton_iff.1 hzx] at hzW
  obtain ⟨U, hU, hxU⟩ := hxW
  exact ⟨U, hxU, hU⟩

/-- **Trivialising near every `K`-point is enough.** Over an algebraically closed field, if `S`
is locally of finite type and `Y ⟶ S` becomes a constant family on an open neighbourhood of the
image of every `K`-point of `S`, then the family is locally constant: those opens already cover
`S`. This is `AlgebraicGeometry.exists_mem_opens_of_rationalPoints`.

This is provided because [Stacks, Tag 0G0R], the input to [Stacks, Tag 0G0S], produces its open
one `K`-rational point at a time; the source's [Stacks, Tag 0G0S] states the cover of all of
`S`, and this lemma is the passage between the two. -/
theorem isLocallyConstantFamily_of_rationalPoints [IsAlgClosed K] {S : Scheme.{u}}
    (q : S ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] (Y : Over S)
    (h : ∀ t : Spec (CommRingCat.of K) ⟶ S, t ≫ q = 𝟙 _ →
      ∃ U : S.Opens, Set.range t.base ⊆ (U : Set S) ∧
        ∃ Y₀ : Over (Spec (CommRingCat.of K)),
          Nonempty ((Over.pullback U.ι).obj Y ≅ (Over.pullback (U.ι ≫ q)).obj Y₀)) :
    IsLocallyConstantFamily q Y :=
  exists_mem_opens_of_rationalPoints q _ h

end Fibres

section Finite

/-- **Finiteness from a locally constant family.** If `S` is quasi-compact and `Y ⟶ S` becomes a
constant family on each member of an open cover of `S`, then the fibres of `Y` at the `K`-points
of `S` fall into finitely many isomorphism classes over `K`.

This is the step "In fact, this number is finite by Lemma 0G0S" of the proof of
[Stacks, Tag 0G11]: a finite subcover exists by quasi-compactness, each `K`-point of `S` lies in
one of its members, and over that member the fibre is the corresponding `Y₀`. -/
theorem finite_fibreClassSet_of_isLocallyConstantFamily {S : Scheme.{u}} [CompactSpace S]
    (q : S ⟶ Spec (CommRingCat.of K)) (Y : Over S)
    (P : (Spec (CommRingCat.of K) ⟶ S) → Prop) (hY : IsLocallyConstantFamily q Y) :
    (fibreClassSet q Y P).Finite := by
  choose U hxU Y₀ hiso using hY
  obtain ⟨F, hF⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := S))
    (fun x : S => (U x : Set S)) (fun x => (U x).2)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine Set.Finite.subset (Set.Finite.image (fun x => isomorphismClassOver (Y₀ x))
    F.finite_toSet) ?_
  rintro c ⟨t, ht, -, rfl⟩
  -- the unique point of `Spec K` and its image in `S`
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨x, hxF, hxmem⟩ : ∃ x ∈ F, t.base p ∈ (U x : Set S) := by
    have := hF (Set.mem_univ (t.base p))
    simpa only [Set.mem_iUnion, exists_prop] using this
  -- `t` factors through the open `U x`
  have hrange : Set.range t.base ⊆ Set.range (U x).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨z, rfl⟩
    rwa [Subsingleton.elim z p]
  refine ⟨x, hxF, ?_⟩
  let t' : Spec (CommRingCat.of K) ⟶ (U x : Scheme.{u}) :=
    IsOpenImmersion.lift (U x).ι t hrange
  have ht' : t' ≫ (U x).ι = t := IsOpenImmersion.lift_fac _ _ hrange
  have ht'q : t' ≫ (U x).ι ≫ q = 𝟙 _ := by rw [← Category.assoc, ht', ht]
  have key : Y₀ x ≅ fibreOver Y t :=
    calc Y₀ x
        ≅ fibreOver ((Over.pullback ((U x).ι ≫ q)).obj (Y₀ x)) t' :=
          (fibreOverConstantIso (q := (U x).ι ≫ q) (Y₀ x) ht'q).symm
      _ ≅ fibreOver ((Over.pullback (U x).ι).obj Y) t' :=
          (Over.pullback t').mapIso (Classical.choice (hiso x)).symm
      _ ≅ fibreOver Y t := (nonempty_fibreOver_pullback_iso (U x).ι Y ht').some
  exact Quotient.sound (⟨key⟩ : IsIsomorphic (Y₀ x) (fibreOver Y t))

end Finite

section Countable

/-- **Countability from a countable family of base changes.** Suppose every `K`-point `t` of `S`
satisfying `P` factors as `t = u ≫ (T i).hom` for some member `T i` of a countable family of
schemes over `S`, and suppose each base change `Y ×_S T i` has countably many isomorphism classes
of fibres at `K`-points. Then `Y` has countably many isomorphism classes of fibres at the
`K`-points of `S` satisfying `P`.

This is the step "Since `I` is countable, by property (3) it suffices to prove ..." of the proof
of [Stacks, Tag 0G11]. -/
theorem countable_fibreClassSet_of_countable_family {S : Scheme.{u}}
    (q : S ⟶ Spec (CommRingCat.of K)) (Y : Over S)
    (P : (Spec (CommRingCat.of K) ⟶ S) → Prop)
    {I : Type*} [Countable I] (T : I → Over S)
    (hfac : ∀ t : Spec (CommRingCat.of K) ⟶ S, t ≫ q = 𝟙 _ → P t →
      ∃ i, ∃ u : Spec (CommRingCat.of K) ⟶ (T i).left, u ≫ (T i).hom = t)
    (hc : ∀ i, (fibreClassSet ((T i).hom ≫ q) ((Over.pullback (T i).hom).obj Y)
      (fun _ => True)).Countable) :
    (fibreClassSet q Y P).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_iUnion hc)
  rintro c ⟨t, ht, hPt, rfl⟩
  obtain ⟨i, u, hu⟩ := hfac t ht hPt
  refine Set.mem_iUnion.2 ⟨i, u, ?_, trivial, ?_⟩
  · rw [← Category.assoc, hu, ht]
  · exact Quotient.sound ((nonempty_fibreOver_pullback_iso (T i).hom Y hu).map Iso.symm)

end Countable

section Inner

variable [IsAlgClosed K]

/-- **The inner paragraph of [Stacks, Tag 0G11].** Let `S` be of finite type over an
algebraically closed field `K`, let `X` and `Y` be of finite type over `S`, and let `X₀` be of
finite type over `K`. Assume that for every finite-type `T ⟶ S` over which `X` becomes the
constant family `X₀ ×_K T`, the base change `Y ×_S T ⟶ T` is locally constant. Then the fibres
`Y_t` at those `K`-points `t` of `S` with `X_t ≅ X₀` fall into countably many isomorphism classes
over `K`.

The proof is the source's: [Stacks, Tag 0G0X] applied to the two families `X₀ ×_K S` and `X`
produces a countable family of finite-type `T i ⟶ S` carrying an isomorphism
`X₀ ×_K T i ≅ X ×_S T i` and accounting for every `K`-point at which the two fibres agree — and
the fibre of `X₀ ×_K S` at a `K`-point is `X₀`, so those are exactly the points with `X_t ≅ X₀`.
The hypothesis then makes each `Y ×_S T i` locally constant, hence with finitely many fibre
classes, and the countable family bounds the whole.

In the source the hypothesis is supplied by [Stacks, Tag 0G0K] (the pullback of the Fourier–Mukai
kernel along `T ⟶ S` is again the kernel of a relative equivalence) followed by
[Stacks, Tag 0G0S]. -/
theorem countable_fibreClassSet_of_locallyConstant_baseChanges
    (S : Over (Spec (CommRingCat.of K))) [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    (X Y : Over S.left) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (X₀ : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (hLC : ∀ T : Over S.left, LocallyOfFiniteType T.hom → QuasiCompact T.hom →
      Nonempty ((Over.pullback T.hom).obj ((Over.pullback S.hom).obj X₀) ≅
        (Over.pullback T.hom).obj X) →
      IsLocallyConstantFamily (T.hom ≫ S.hom) ((Over.pullback T.hom).obj Y)) :
    (fibreClassSet S.hom Y (fun t => Nonempty (fibreOver X t ≅ X₀))).Countable := by
  -- the constant family `X₀ ×_K S`, of finite type over `S`
  set C : Over S.left := (Over.pullback S.hom).obj X₀ with hC
  have hCft : LocallyOfFiniteType C.hom :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback X₀.hom S.hom) inferInstance
  have hCqc : QuasiCompact C.hom :=
    quasiCompact_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback X₀.hom S.hom) inferInstance
  obtain ⟨I, hI, T, hTft, hTiso, hTsurj⟩ :=
    exists_countable_finiteType_isomorphism_families_of_isAlgClosed S C X
  -- `S` and each `T i` are quasi-compact schemes
  have hScompact : CompactSpace S.left :=
    QuasiCompact.compactSpace_of_compactSpace S.hom
  refine countable_fibreClassSet_of_countable_family S.hom Y _ T ?_ ?_
  · -- every `K`-point with `X_t ≅ X₀` factors through one of the `T i`
    intro t ht hPt
    have hfib : Nonempty (fibreOver C t ≅ fibreOver X t) :=
      ⟨fibreOverConstantIso (q := S.hom) X₀ ht ≪≫ (Classical.choice hPt).symm⟩
    exact hTsurj (Over.homMk t ht) hfib
  · -- each base change has finitely many fibre classes, by the hypothesis and quasi-compactness
    intro i
    have : QuasiCompact (T i).hom := (hTft i).2
    have : CompactSpace (T i).left := QuasiCompact.compactSpace_of_compactSpace (T i).hom
    exact (finite_fibreClassSet_of_isLocallyConstantFamily _ _ _
      (hLC (T i) (hTft i).1 (hTft i).2 ⟨hTiso i⟩)).countable

end Inner

section Outer

/-- **The outer layer of [Stacks, Tag 0G11].** Let `D` be a condition on schemes over `K`.
Suppose a countable family of systems `(S i, X i, Y i)` accounts for every `Z` satisfying `D`, in
the sense that there is a `K`-point `t` of `S i` with `X i` having fibre `X₀` at `t` and `Y i`
having fibre `Z` at `t`. If for each `i` the fibres of `Y i` at the `K`-points where `X i` has
fibre `X₀` fall into countably many isomorphism classes, then the schemes satisfying `D` fall
into countably many isomorphism classes over `K`.

This is "Clearly it suffices to show that the set of isomorphism classes of fibres `Y_s` for
`s ∈ S(K)` such that `X_s ≅ X` is countable" of the proof of [Stacks, Tag 0G11], with the
countable family of systems supplied by [Stacks, Tag 0G0Y] and property (4) of that lemma
supplying `haccount`. -/
theorem countable_isomorphismClasses_of_countable_systems
    {D : Over (Spec (CommRingCat.of K)) → Prop} (X₀ : Over (Spec (CommRingCat.of K)))
    {I : Type*} [Countable I] (S : I → Over (Spec (CommRingCat.of K)))
    (X Y : ∀ i, Over (S i).left)
    (haccount : ∀ Z : Over (Spec (CommRingCat.of K)), D Z →
      ∃ i, ∃ t : Spec (CommRingCat.of K) ⟶ (S i).left, t ≫ (S i).hom = 𝟙 _ ∧
        Nonempty (fibreOver (X i) t ≅ X₀) ∧ Nonempty (fibreOver (Y i) t ≅ Z))
    (hsystem : ∀ i, (fibreClassSet (S i).hom (Y i)
      (fun t => Nonempty (fibreOver (X i) t ≅ X₀))).Countable) :
    {c : IsomorphismClassOver K | ∃ Z, D Z ∧ c = isomorphismClassOver Z}.Countable := by
  refine Set.Countable.mono ?_ (Set.countable_iUnion hsystem)
  rintro c ⟨Z, hZ, rfl⟩
  obtain ⟨i, t, ht, hX, hY⟩ := haccount Z hZ
  exact Set.mem_iUnion.2 ⟨i, t, ht, hX, (Quotient.sound hY).symm⟩

end Outer

end AlgebraicGeometry

end
