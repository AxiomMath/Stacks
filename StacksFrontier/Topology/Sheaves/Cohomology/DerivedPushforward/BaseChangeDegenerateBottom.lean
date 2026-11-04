module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting

/-!
# The derived base change map of a square whose bottom row is an identity

For morphisms of ringed spaces `p : Z ⟶ X` and `f : X ⟶ S` the square

```
Z --p--> X
|p ≫ f   |f
S --𝟙--> S
```

commutes, and the derived base change map of [Stacks, Tag 08HY] attached to it is a map
`L(𝟙)^* (Rf_* K) ⟶ R(p ≫ f)_* (Lp^* K)`.  This file proves that it is the **derived pushforward
along `f` of the derived unit** of `Lp^* ⊣ Rp_*` of [Stacks, Tag 079W], read through the identity
isomorphism `L(𝟙)^* ≅ 𝟭` of `Stacks.Cohomology.DerivedPushforwardAssociativity` and the
composition isomorphism `Rf_* ⋙ Rp_* ≅ R(p ≫ f)_*` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`.

This is the companion of
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_self_id`, which treats the square whose
*right* leg is an identity; together they are the two degenerate cases the pasting law of
[Stacks, Tag 0ATL] needs in order to compute the transpose of the derived base change map of an
arbitrary commutative square.

## Main results

All in the namespace `Stacks.Cohomology.DerivedBaseChange`.

* `derivedPullbackCompIsoLeft_comp_id_hom_app`: at this square the comparison down the left and
  along the bottom is the derived pullback along `p ≫ f` of the identity isomorphism
  `L(𝟙 S)^* ≅ 𝟭`; in particular the transport carried by
  `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` is an identity.
* `compIsoCanonical_hom_comp_degenerate`: the comparison of the two iterated derived pullbacks
  cancels against its inverse, leaving the derived pullback along `p` of a transpose under
  `Lf^* ⊣ Rf_*`.
* `derivedAdjunction_homEquiv_derivedPullback_map`: transposing a derived pullback along `p`
  appends the derived unit of `Lp^* ⊣ Rp_*`.
* `derivedAdjunction_homEquiv_comp_unit`: transposing, under `Lf^* ⊣ Rf_*`, a composite whose
  first factor is itself a transpose deletes the transposition.
* `derivedAdjunction_homEquiv_inner_degenerate` and `derivedAdjunction_homEquiv_degenerate`: the
  iterated transpose, under `Lp^* ⊣ Rp_*` and then under `Lf^* ⊣ Rf_*`, of the pullback of the
  counit is the derived pushforward along `f` of the derived unit of `Lp^* ⊣ Rp_*`.
* `derivedAdjunction_comp_homEquiv_degenerate`: the same read through the adjunction for the
  composite `p ≫ f`.
* `derivedBaseChangeMap_comp_id`: **the derived base change map of the square with identity
  bottom row is the derived pushforward of the derived unit, followed by the composition
  isomorphism.**

## Implementation notes

*Every step is its own declaration, and that is forced.*  The heartbeat budget is counted per
declaration, and this cube has eight categories and sixteen functors: each of
`derivedBaseChangeMap_adjoint`, the two transposition steps and the identification of the
comparison down the left costs a substantial fraction of the budget on its own.  Assembled as
`have`s inside one proof two or three of them together exceed 200000 heartbeats and the
declaration fails with `(deterministic) timeout at whnf`, even though each step checks in seconds
in isolation.  Raising `maxHeartbeats` is not a way to finish; splitting is.

*Reassociation is hoisted onto variables.*  `rw [← Category.assoc]` on a composite of morphisms
of the unbounded derived category of module sheaves is a `(deterministic) timeout at isDefEq`:
the object between two neighbouring factors is spelled as a composite functor applied to an
object on one side and as the iterated application on the other.  The three private lemmas
`comp_eq_assoc`, `comp_id_of_eq` and `comp_cancel_of_naturality` therefore carry out every
rearrangement with each subterm a variable of an abstract category, and the unifier reconciles
the two spellings at the application site.  A bare `.inv.naturality` of a natural transformation
is cheap and is used directly.

*Assembling with `congrArg`, not `rw`.*  The two transposition steps are composed by `congrArg`
applied to the transposition bijection, and the final step by
`refine Eq.trans ?_ (…).symm`: rewriting with an equation whose left-hand side is one of these
composites forms a motive over it, which is what times out.  `Eq.trans` and `congrArg` form none.

*The transport is killed at a complex, not at a functor.*
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` carries
`eqToIso (congrArg derivedPullback sq.symm)` for `sq : p ≫ f = (p ≫ f) ≫ 𝟙 S`, a transport
between two *functors*, and `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`
is a reducible abbreviation over a total derived functor: deciding an equality of two such
functors makes the kernel unfold the abbreviation.
A transport quantified over both morphisms, proved by `subst` inside the proof of
`derivedPullbackCompIsoLeft_comp_id_hom_app`, turns it into an `eqToHom` between objects of the
derived category first, and
`eqToHom_derivedPullback_obj_comp_id` then identifies it with the identity by
`CategoryTheory.eqToHom_refl`, which only needs the two objects to be definitionally equal --
they are, because `derivedPullback ((p ≫ f) ≫ 𝟙 S)` and `derivedPullback (p ≫ f)` are, which is
already what makes the statement of
`Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_comp_id`
typecheck.

*No `stacks` attribute is placed.*  Nothing here is a conclusion of a tag: the degenerate case of
[Stacks, Tag 08HY]'s base change map is a step inside the computation of its transpose.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0ATL](https://stacks.math.columbia.edu/tag/0ATL)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPushforwardAssociativity

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

section DegenerateBottom

/-! ### Rearrangements on variables

Each of these is an identity of composites in an abstract category, with every factor a
variable; carried out in place they would reassociate composites of morphisms of the unbounded
derived category. -/

/-- A factor appended to both sides of a two-factor identity, reassociated on the right. -/
private theorem comp_eq_assoc {E : Type*} [Category E] {A B C D : E} {a : A ⟶ C} {x : A ⟶ B}
    {y : B ⟶ C} (h : a = x ≫ y) (m : C ⟶ D) : a ≫ m = x ≫ y ≫ m := by
  rw [h, Category.assoc]

/-- A second factor that is the identity is deleted. -/
private theorem comp_id_of_eq {E : Type*} [Category E] {A B : E} (x : A ⟶ B) {y : B ⟶ B}
    (h : y = 𝟙 B) : x ≫ y = x := by
  rw [h, Category.comp_id]

/-- Two middle factors swapped by a naturality square, the outer ones then cancelling. -/
private theorem comp_cancel_of_naturality {E : Type*} [Category E] {A B C D F : E} {h : A ⟶ B}
    {i : B ⟶ C} {j : C ⟶ D} {j₀ : B ⟶ A} {i₀ : A ⟶ D} {k : D ⟶ F} (hn : i ≫ j = j₀ ≫ i₀)
    (hc : h ≫ j₀ = 𝟙 A) : h ≫ i ≫ j ≫ k = i₀ ≫ k := by
  rw [← Category.assoc i, hn, Category.assoc, ← Category.assoc h, hc, Category.id_comp]

/-! ### The comparison down the left and along the bottom -/

variable {Z X S : RingedSpace.{u, u}}

/-- The transport along the right unit law `a ≫ 𝟙 = a` is an identity: the two objects of the
derived category it compares are definitionally equal. -/
private theorem eqToHom_derivedPullback_obj_comp_id {A C : RingedSpace.{u, u}} {a : A ⟶ C}
    (e : a ≫ 𝟙 C = a) (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing C))) :
    eqToHom (congrArg (fun q : A ⟶ C => (derivedPullback q).obj M) e) =
      𝟙 ((derivedPullback a).obj M) :=
  eqToHom_refl _ _

/-- One unfolding step of the comparison down the left and along the bottom, with the two
factors left unreduced. -/
private theorem derivedPullbackCompIsoLeft_comp_id_eq (p : Z ⟶ X) (f : X ⟶ S)
    (sq : p ≫ f = (p ≫ f) ≫ 𝟙 S) :
    derivedPullbackCompIsoLeft p (p ≫ f) f (𝟙 S) sq =
      derivedPullbackCompIsoCanonical (p ≫ f) (𝟙 S) ≪≫
        eqToIso (congrArg (fun q : Z ⟶ S => derivedPullback q) sq.symm) :=
  rfl

/-- The composition isomorphism of [Stacks, Tag 0D5S] at `(a, 𝟙)`, read at a complex: it is the
derived pullback along `a` of the identity isomorphism `L(𝟙)^* ≅ 𝟭`. -/
private theorem compIsoCanonical_comp_id_hom_app {A C : RingedSpace.{u, u}} (a : A ⟶ C)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing C))) :
    (derivedPullbackCompIsoCanonical a (𝟙 C)).hom.app M =
      (derivedPullback a).map ((derivedPullbackIdIso C).hom.app M) := by
  rw [derivedPullbackCompIsoCanonical_comp_id]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  exact Category.comp_id _

/-- For the square with identity bottom row the comparison down the left and along the bottom,
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`, is the derived pullback along
`p ≫ f` of the identity isomorphism `L(𝟙 S)^* ≅ 𝟭`: the transport it carries is an identity. -/
theorem derivedPullbackCompIsoLeft_comp_id_hom_app (p : Z ⟶ X) (f : X ⟶ S)
    (sq : p ≫ f = (p ≫ f) ≫ 𝟙 S)
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (derivedPullbackCompIsoLeft p (p ≫ f) f (𝟙 S) sq).hom.app N =
      (derivedPullback (p ≫ f)).map ((derivedPullbackIdIso S).hom.app N) := by
  have htransport : ∀ {a b : Z ⟶ S} (e : a = b),
      (eqToIso (congrArg (fun q : Z ⟶ S => derivedPullback q) e)).hom.app N =
        eqToHom (congrArg (fun q : Z ⟶ S => (derivedPullback q).obj N) e) := by
    intro a b e
    subst e
    simp
  rw [derivedPullbackCompIsoLeft_comp_id_eq, Iso.trans_hom, NatTrans.comp_app,
    htransport sq.symm]
  exact Eq.trans (comp_id_of_eq _ (eqToHom_derivedPullback_obj_comp_id sq.symm N))
    (compIsoCanonical_comp_id_hom_app (p ≫ f) N)

/-! ### Transposition -/

/-- The derived pullback along `p` of a transpose under `Lf^* ⊣ Rf_*`, split into its two
factors. -/
private theorem derivedPullback_map_homEquiv_symm (p : Z ⟶ X) (f : X ⟶ S)
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (α : M ⟶ (derivedPushforward f).obj K) :
    (derivedPullback p).map (((derivedAdjunction f).homEquiv M K).symm α) =
      (derivedPullback p).map ((derivedPullback f).map α) ≫
        (derivedPullback p).map ((derivedAdjunction f).counit.app K) := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp]

/-- The comparison of the two iterated derived pullbacks cancels against its inverse: after
moving the inverse past the map of `α` by naturality, what is left is the derived pullback along
`p` of the transpose of `α` under `Lf^* ⊣ Rf_*`. -/
theorem compIsoCanonical_hom_comp_degenerate (p : Z ⟶ X) (f : X ⟶ S)
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (α : M ⟶ (derivedPushforward f).obj K) :
    (derivedPullbackCompIsoCanonical p f).hom.app M ≫
        (derivedPullback (p ≫ f)).map α ≫
        (derivedPullbackCompIsoCanonical p f).inv.app ((derivedPushforward f).obj K) ≫
        (derivedPullback p).map ((derivedAdjunction f).counit.app K) =
      (derivedPullback p).map (((derivedAdjunction f).homEquiv M K).symm α) :=
  Eq.trans (comp_cancel_of_naturality ((derivedPullbackCompIsoCanonical p f).inv.naturality α)
      (Iso.hom_inv_id_app _ _))
    (derivedPullback_map_homEquiv_symm p f α).symm

/-- Transposing a derived pullback along `p` under `Lp^* ⊣ Rp_*` appends the derived unit. -/
theorem derivedAdjunction_homEquiv_derivedPullback_map (p : Z ⟶ X)
    {A K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (β : A ⟶ K) :
    (derivedAdjunction p).homEquiv A ((derivedPullback p).obj K) ((derivedPullback p).map β) =
      β ≫ (derivedAdjunction p).unit.app K := by
  rw [Adjunction.homEquiv_unit]
  exact (derivedAdjunction p).unit_naturality β

/-- Transposing, under `Lf^* ⊣ Rf_*`, a composite whose first factor is itself a transpose
deletes the transposition. -/
theorem derivedAdjunction_homEquiv_comp_unit (f : X ⟶ S)
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    {K B : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (α : M ⟶ (derivedPushforward f).obj K) (y : K ⟶ B) :
    (derivedAdjunction f).homEquiv M B (((derivedAdjunction f).homEquiv M K).symm α ≫ y) =
      α ≫ (derivedPushforward f).map y := by
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]

/-- The inner transposition: under `Lp^* ⊣ Rp_*` the pullback of the counit of `Lf^* ⊣ Rf_*`,
transported across the composition isomorphism of [Stacks, Tag 0D5S], becomes the transpose of
`α` followed by the derived unit of `Lp^* ⊣ Rp_*`. -/
theorem derivedAdjunction_homEquiv_inner_degenerate (p : Z ⟶ X) (f : X ⟶ S)
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (α : M ⟶ (derivedPushforward f).obj K) :
    (derivedAdjunction p).homEquiv ((derivedPullback f).obj M) ((derivedPullback p).obj K)
        ((derivedPullbackCompIsoCanonical p f).hom.app M ≫
          (derivedPullback (p ≫ f)).map α ≫
          (derivedPullbackCompIsoCanonical p f).inv.app ((derivedPushforward f).obj K) ≫
          (derivedPullback p).map ((derivedAdjunction f).counit.app K)) =
      ((derivedAdjunction f).homEquiv M K).symm α ≫ (derivedAdjunction p).unit.app K :=
  Eq.trans
    (congrArg
      ((derivedAdjunction p).homEquiv ((derivedPullback f).obj M) ((derivedPullback p).obj K))
      (compIsoCanonical_hom_comp_degenerate p f α))
    (derivedAdjunction_homEquiv_derivedPullback_map p (((derivedAdjunction f).homEquiv M K).symm α))

/-- The iterated transpose, under `Lp^* ⊣ Rp_*` and then under `Lf^* ⊣ Rf_*`, of the derived
pullback of the counit: it is `α` followed by the derived pushforward along `f` of the derived
unit of `Lp^* ⊣ Rp_*`. -/
theorem derivedAdjunction_homEquiv_degenerate (p : Z ⟶ X) (f : X ⟶ S)
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (α : M ⟶ (derivedPushforward f).obj K) :
    (derivedAdjunction f).homEquiv M ((derivedPushforward p).obj ((derivedPullback p).obj K))
        ((derivedAdjunction p).homEquiv ((derivedPullback f).obj M) ((derivedPullback p).obj K)
          ((derivedPullbackCompIsoCanonical p f).hom.app M ≫
            (derivedPullback (p ≫ f)).map α ≫
            (derivedPullbackCompIsoCanonical p f).inv.app ((derivedPushforward f).obj K) ≫
            (derivedPullback p).map ((derivedAdjunction f).counit.app K))) =
      α ≫ (derivedPushforward f).map ((derivedAdjunction p).unit.app K) :=
  Eq.trans
    (congrArg
      ((derivedAdjunction f).homEquiv M
        ((derivedPushforward p).obj ((derivedPullback p).obj K)))
      (derivedAdjunction_homEquiv_inner_degenerate p f α))
    (derivedAdjunction_homEquiv_comp_unit f α ((derivedAdjunction p).unit.app K))

/-- The same identity read through the derived adjunction for the composite `p ≫ f`, which is
the adjunction the base change map of this square is adjoint under. -/
theorem derivedAdjunction_comp_homEquiv_degenerate (p : Z ⟶ X) (f : X ⟶ S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedAdjunction (p ≫ f)).homEquiv
        ((derivedPullback (𝟙 S)).obj ((derivedPushforward f).obj K))
        ((derivedPullback p).obj K)
        ((derivedPullback (p ≫ f)).map
            ((derivedPullbackIdIso S).hom.app ((derivedPushforward f).obj K)) ≫
          (derivedPullbackCompIsoCanonical p f).inv.app ((derivedPushforward f).obj K) ≫
          (derivedPullback p).map ((derivedAdjunction f).counit.app K)) =
      (derivedPullbackIdIso S).hom.app ((derivedPushforward f).obj K) ≫
        (derivedPushforward f).map ((derivedAdjunction p).unit.app K) ≫
        (derivedPushforwardCompIso p f).hom.app ((derivedPullback p).obj K) :=
  Eq.trans (derivedAdjunction_comp_homEquiv p f _ _ _).symm
    (comp_eq_assoc (derivedAdjunction_homEquiv_degenerate p f
      ((derivedPullbackIdIso S).hom.app ((derivedPushforward f).obj K))) _)

/-- The transpose, under the derived adjunction for `p ≫ f`, of the derived pushforward of the
derived unit followed by the composition isomorphism. -/
private theorem derivedAdjunction_comp_homEquiv_symm_degenerate (p : Z ⟶ X) (f : X ⟶ S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((derivedAdjunction (p ≫ f)).homEquiv
        ((derivedPullback (𝟙 S)).obj ((derivedPushforward f).obj K))
        ((derivedPullback p).obj K)).symm
        ((derivedPullbackIdIso S).hom.app ((derivedPushforward f).obj K) ≫
          (derivedPushforward f).map ((derivedAdjunction p).unit.app K) ≫
          (derivedPushforwardCompIso p f).hom.app ((derivedPullback p).obj K)) =
      (derivedPullback (p ≫ f)).map
          ((derivedPullbackIdIso S).hom.app ((derivedPushforward f).obj K)) ≫
        (derivedPullbackCompIsoCanonical p f).inv.app ((derivedPushforward f).obj K) ≫
        (derivedPullback p).map ((derivedAdjunction f).counit.app K) :=
  (Equiv.symm_apply_eq _).2 (derivedAdjunction_comp_homEquiv_degenerate p f K).symm

/-- **The derived base change map of a commutative square whose bottom row is an identity is the
derived pushforward of the derived unit, followed by the composition isomorphism.**  For
`p : Z ⟶ X` and `f : X ⟶ S` the square with legs `p ≫ f` and `f` and bottom row `𝟙 S` has base
change map `L(𝟙 S)^* (Rf_* K) ⟶ R(p ≫ f)_* (Lp^* K)`, and it is the identity isomorphism
`L(𝟙 S)^* ≅ 𝟭`, then `Rf_*` of the derived unit of `Lp^* ⊣ Rp_*`, then the composition
isomorphism `Rf_* ⋙ Rp_* ≅ R(p ≫ f)_*`. -/
theorem derivedBaseChangeMap_comp_id (p : Z ⟶ X) (f : X ⟶ S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap p (p ≫ f) f (𝟙 S) (Category.comp_id _).symm K =
      (derivedPullbackIdIso S).hom.app ((derivedPushforward f).obj K) ≫
        (derivedPushforward f).map ((derivedAdjunction p).unit.app K) ≫
        (derivedPushforwardCompIso p f).hom.app ((derivedPullback p).obj K) := by
  refine ((derivedAdjunction (p ≫ f)).homEquiv
    ((derivedPullback (𝟙 S)).obj ((derivedPushforward f).obj K))
    ((derivedPullback p).obj K)).symm.injective ?_
  refine Eq.trans ?_ (derivedAdjunction_comp_homEquiv_symm_degenerate p f K).symm
  rw [derivedBaseChangeMap_adjoint, derivedPullbackCompIsoLeft_comp_id_hom_app]

end DegenerateBottom

end Stacks.Cohomology.DerivedBaseChange

end

