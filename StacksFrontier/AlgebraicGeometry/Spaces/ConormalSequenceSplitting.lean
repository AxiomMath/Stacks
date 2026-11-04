module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsIdComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Splitting the conormal sequence of an immersion with a left inverse

Let `i : Z ⟶ X` be an immersion of algebraic spaces over an algebraic space `Bb`, with structure
morphism `b : X ⟶ Bb`.  Stacks 05ZA attaches to it the canonical sequence
```
  0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
whose second arrow is `AlgebraicGeometry.Space.pullbackDifferentialsMap`, the comparison map `c_i`
of Stacks 04CX at the square with top edge `i`, right edge `b`, left edge `i ≫ b` and bottom edge
the identity of `Bb`.  Stacks 05ZB says that if `i` (étale locally) has a left inverse over `Bb`,
then that sequence is (étale locally) split exact.

A short exact sequence is split exactly when its epimorphism admits a section, and exactness is
Stacks 05ZA's business, not this file's.  So the content of Stacks 05ZB delivered here is that the
*second arrow is a split epimorphism*, globally when `i` has a left inverse and after restriction
along the induced étale morphism when it has one étale locally.  Nothing below mentions
`𝒞_{Z/X}`, which is why this file imports the module that builds the second arrow and not the one
that builds the conormal module.

The source's clarification is the whole global argument: if `g : X ⟶ Z` is a left inverse of `i`
over `Bb`, then `i^*c_g` is a right inverse of `c_i`.  Here `c_g` is the comparison map of
Stacks 04CX at the square with top edge `g`, and `i^*c_g` is read as a morphism out of
`Ω_{Z/Bb}` through the composition comparison `(i ≫ g)^* ≅ i^*g^*` of Stacks 03LU and the
transport of `i ≫ g = 𝟙 Z`.  Stacks 05Z7 says that `c_i ∘ i^*c_g` is the comparison map of the
outer square, whose top edge is `i ≫ g = 𝟙 Z`; so it is the comparison map `c_{𝟙 Z}` at an
identity square, and that map is invertible.

The étale-local clause localizes along an étale `φ : X' ⟶ X` to the *target* of the immersion,
which is how Stacks 04CO and 04CU localize.  Given the restricted immersion `i' : Z' ⟶ X'` and
the induced morphism `a : Z' ⟶ Z` with `i' ≫ φ = a ≫ i`, the assertion is that the inverse image
along `a` of the second arrow is a split epimorphism.  That is one assertion per member of an
étale covering `{φ_j}` of `X`, and the covering adds no mathematics beyond the per-member
statement, so no covering datum appears below: the statement is made for a single étale `φ`.

## Main results

* `CategoryTheory.comp_eq_id_of_retraction_factorization` and
  `CategoryTheory.comp_eq_id_of_retraction_factorization₂` are the two pieces of category
  arithmetic the splittings consist of, stated at an arbitrary category.
* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_eqToHom_comp`: being a comparison map of
  Stacks 04CX is transported along an equality of the upper edges of the square.
* `AlgebraicGeometry.Space.eqToHom_comp_eq_comp_pullbackDifferentialsMap`: **the clarification of
  Stacks 05ZB**, as an identity of comparison maps and before anything is divided out: the
  comparison map at the identity square, transported along `i ≫ g = 𝟙 Z`, is `i^*c_g` followed
  by `c_i`.
* `AlgebraicGeometry.Space.comp_pullbackDifferentialsMap_eq_id_of_leftInverse`: the explicit right
  inverse of the second arrow of the sequence of Stacks 05ZA, written out.
* `AlgebraicGeometry.Space.isSplitEpi_pullbackDifferentialsMap_of_leftInverse`: **Stacks 05ZB**,
  the global clause.  If `i` has a left inverse over `Bb`, the second arrow of the sequence of
  Stacks 05ZA is a split epimorphism, so that sequence is split exact.
* `AlgebraicGeometry.Space.isSplitEpi_pullbackDifferentialsMap_of_retraction`: **Stacks 05ZB**,
  the global clause with nothing carried.  Same conclusion from `i`, `b`, `g`, `i ≫ g = 𝟙 Z` and
  `g ≫ i ≫ b = b` alone.
* `AlgebraicGeometry.Space.comp_comp_eq_eqToHom_comp`: the two routes from `(a ≫ i)^*Ω_{X/Bb}` to
  `Ω_{Z'/Bb}` given by the two factorizations of `i' ≫ φ = a ≫ i` agree.  No invertibility is
  needed for this.
* `AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etaleLeftInverse`:
  **Stacks 05ZB**, the étale-local clause.  If the restriction of `i` along an étale
  `φ : X' ⟶ X` has a left inverse over `Bb`, the inverse image along the induced `a : Z' ⟶ Z` of
  the second arrow is a split epimorphism.
* `AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etaleRetraction`:
  **Stacks 05ZB**, the étale-local clause with no comparison map at the identity square supplied.
  It still takes the invertibility of the two comparison maps of Stacks 04CU as instances, so it
  applies to any square, étale or not, where they are invertible.
* `AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etale`: **Stacks 05ZB**, the
  étale-local clause with nothing carried.  Same conclusion from `φ` and `a` étale, the commuting
  square `i' ≫ φ = a ≫ i` and the left inverse `g'` of `i'` over `Bb` alone — the hypotheses of
  the source and nothing else.

## Implementation notes

### What is carried as a hypothesis, and why

**The unit law of Stacks 04CX is available, and both clauses are delivered unconditionally in
it.**  Both clauses need that the comparison map of Stacks 04CX at a square whose horizontal edges
are identities is invertible — this is the unit law of 04CX, equivalently the unit coherence of
Stacks 03LU.  That law is now proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsIdComparison.lean`:

* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_modulePullbackIdIso`
  (`SheafOfDifferentialsIdComparison.lean:265`) says that the unit law of Stacks 03LU at
  `Ω_{X/Y}`, namely `(modulePullbackIdIso B S hS X).hom.app (sheafOfDifferentials B S hS p)`, is a
  comparison map of Stacks 04CX for the square whose horizontal edges are `𝟙 X`;
* `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_id`
  (`SheafOfDifferentialsIdComparison.lean:274`) says that *any* comparison map at an identity
  square is invertible, by uniqueness of the comparison map.

Instantiating the first at `X := Z` and `p := i ≫ b` supplies `cid` and `hcid`, and the second
then supplies `[IsIso cid]`.  That is what
`AlgebraicGeometry.Space.isSplitEpi_pullbackDifferentialsMap_of_retraction` and
`AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etaleRetraction` do, and
nothing else: neither assumes anything the hypothesis-carrying version does not, beyond what is
discharged here.

The hypothesis-carrying forms are kept deliberately.  The original
`isSplitEpi_pullbackDifferentialsMap_of_leftInverse`,
`comp_pullbackDifferentialsMap_eq_id_of_leftInverse`,
`eqToHom_comp_eq_comp_pullbackDifferentialsMap` and
`isSplitEpi_map_pullbackDifferentialsMap_of_etaleLeftInverse` still take that datum as explicit
parameters: a morphism `cid` out of `(𝟙 Z)^*Ω_{Z/Bb}`, its characterizing property `hcid` of
Stacks 04CX, and `[IsIso cid]`.  They are strictly more general — they apply to whatever
comparison map at the identity square a caller already has in hand, and
`eqToHom_comp_eq_comp_pullbackDifferentialsMap` is an identity *about* that map, so it has nothing
to discharge — and by `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap` the property
`hcid` pins `cid` down uniquely, so the triple is exactly the unit law and nothing more.  No
statement below had to be restated when the unit law arrived.

**The étale-localization clause of Stacks 04CU is available, and the étale-local clause is
delivered unconditionally in it.**  The étale-local clause needs the invertibility of two
comparison maps of Stacks 04CX — the one along `a` and the one along `φ` — which is the
étale-localization clause of Stacks 04CU.  That clause is now proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsEtaleComparison.lean`:

* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom`
  says that the identification `a^*Ω_{X/Y} ≅ Ω_{U/Y}` of Stacks 04CU,
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso`, is a comparison map
  of Stacks 04CX for the square whose top edge is the étale `a` and whose bottom edge is an
  identity;
* `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_etale` concludes, by uniqueness of
  the comparison map, that *any* such comparison map is invertible, and
  `AlgebraicGeometry.Space.isIso_pullbackDifferentialsMap_of_isEtale` is that at
  `AlgebraicGeometry.Space.pullbackDifferentialsMap`.

`AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etale` supplies both
instances from those, taking `φ` and `a` étale instead.  Its hypotheses are the source's: in the
situation of the source `φ` is étale and `a`, being a base change of `φ`, is étale too, so
assuming the two of them is weaker than assuming that `Z'` is the preimage of `Z`.

The instance-carrying forms are kept deliberately, for the same reason as the hypothesis-carrying
forms above: they are stated for an arbitrary `φ`, `i'`, `a` with `i' ≫ φ = a ≫ i` and never
mention étaleness, the proof using only that commuting square and the two invertibility
instances, so they apply to any square where the two comparison maps happen to be invertible.

**No immersion hypothesis.**  `i` is an arbitrary morphism below.  The source's `i` is an
immersion because the sequence of Stacks 05ZA needs it, but splitness of the second arrow does
not: the proof uses only the left inverse.  A morphism with a left inverse is a split mono in any
case.

**The left inverse and the localizing morphism are parameters.**  `g`, and in the étale clause
`φ`, `i'`, `a`, `g'`, are explicit parameters, never extracted from an existential.

### The proof

Both clauses are consequences of uniqueness of the comparison map.  Globally, Stacks 05Z7
(`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp`) says that `i^*c_g` followed by `c_i`,
precomposed with the composition comparison of Stacks 03LU, is a comparison map for the square
with top edge `i ≫ g`; transporting `hcid` along `i ≫ g = 𝟙 Z` says that `cid` is one too; and
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap` identifies the two.  Dividing by `cid`
leaves a right inverse of `c_i`.

Étale locally, Stacks 05Z7 is applied twice, to the two factorizations of `i' ≫ φ = a ≫ i`
through `Z` and through `X'` respectively, and uniqueness identifies the two resulting routes
from `(a ≫ i)^*Ω_{X/Bb}` to `Ω_{Z'/Bb}`.  The global clause at `i'` splits the comparison map
along `i'`, and the two invertible comparison maps of Stacks 04CU turn that into a splitting of
`a^*c_i`.  This is the pattern of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsDescent.lean`.

### Why no `def` names the two sections

Each section is written out inside the statement that asserts it is a right inverse, and no `def`
names it.  A `def` naming such a morphism of sheaves of modules *and* an equation about that
`def` cannot be checked together here: the kernel then has to decide the definitional equality of
the `def` with its own body inside a composite of sheaf morphisms, and that exceeds the heartbeat
budget, which this development does not raise.  The same measurement rules out assembling the
splitting as a `CategoryTheory.SplitEpi` structure instance, whose field proof is elaborated into
an auxiliary declaration with the same problem.  Writing the sections out keeps every check
structural, and the `CategoryTheory.SplitEpi` that the two tagged results are built from is
anonymous, so its section field *is* the written-out morphism.

The two pieces of arithmetic are for the same reason stated at an arbitrary category, so that the
rewriting they need happens on small terms.  This is the device
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsComp.lean` already uses, with its
`CategoryTheory.comp_assoc₃` and friends.

## References

* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence
  of an immersion, whose second arrow is `AlgebraicGeometry.Space.pullbackDifferentialsMap`.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
* [Stacks Project, Tag 05Z7](https://stacks.math.columbia.edu/tag/05Z7), the comparison maps of
  two stacked squares compose.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU) and
  [Tag 04CO](https://stacks.math.columbia.edu/tag/04CO), étale localization of the sheaf of
  differentials, whose invertibility clause the étale-local statements consume; it is proved in
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsEtaleComparison.lean`.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the unit and composition
  laws for inverse images of modules.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C]

/-- The arithmetic of the global splitting of Stacks 05ZB, at an arbitrary category so that it is
performed on small terms: if `e` is a retraction of `e'`, if `cid` is invertible and if `e' ≫ cid`
factors as `t ≫ k ≫ ci`, then `inv cid ≫ e ≫ t ≫ k` is a right inverse of `ci`. -/
theorem comp_eq_id_of_retraction_factorization {A A₁ P Q W : C} (e : A ⟶ A₁) (e' : A₁ ⟶ A)
    (he : e ≫ e' = 𝟙 A) (cid : A ⟶ W) [IsIso cid] (t : A₁ ⟶ P) (k : P ⟶ Q) (ci : Q ⟶ W)
    (key : e' ≫ cid = t ≫ k ≫ ci) :
    (inv cid ≫ e ≫ t ≫ k) ≫ ci = 𝟙 W := by
  have h₁ : e ≫ t ≫ k ≫ ci = e ≫ e' ≫ cid := by rw [key]
  simp only [Category.assoc]
  rw [h₁, ← Category.assoc e e' cid, he, Category.id_comp, IsIso.inv_hom_id]

/-- The arithmetic of the étale-local splitting of Stacks 05ZB, at an arbitrary category so that
it is performed on small terms: a right inverse `r` of `ci'`, two invertible morphisms `ca` and
`kk`, two retraction pairs `(th, tinv)` and `(e, e')`, and a factorization of `tc ≫ d ≫ ca`
through them, assemble into a right inverse of `d`. -/
theorem comp_eq_id_of_retraction_factorization₂ {W Ω M N P P' V : C} (ca : W ⟶ Ω) [IsIso ca]
    (r : Ω ⟶ M) (ci' : M ⟶ Ω) (hr : r ≫ ci' = 𝟙 Ω) (kk : N ⟶ M) [IsIso kk] (th : N ⟶ P)
    (tinv : P ⟶ N) (ht : th ≫ tinv = 𝟙 N) (e : P ⟶ P') (e' : P' ⟶ P) (he : e ≫ e' = 𝟙 P)
    (tc : P' ⟶ V) (d : V ⟶ W) (key : tc ≫ d ≫ ca = e' ≫ tinv ≫ kk ≫ ci') :
    (ca ≫ r ≫ inv kk ≫ th ≫ e ≫ tc) ≫ d = 𝟙 W := by
  have h₁ : e ≫ e' ≫ tinv ≫ kk ≫ ci' = tinv ≫ kk ≫ ci' := by
    rw [← Category.assoc, he, Category.id_comp]
  have h₂ : th ≫ tinv ≫ kk ≫ ci' = kk ≫ ci' := by
    rw [← Category.assoc, ht, Category.id_comp]
  have h₃ : inv kk ≫ kk ≫ ci' = ci' := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [← cancel_mono ca]
  simp only [Category.assoc, key, h₁, h₂, h₃, hr, Category.comp_id, Category.id_comp]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transport

variable {X X' Y Y' : AlgebraicSpaces B S hS}

/-- Being a comparison map of Stacks 04CX for a commutative square depends on the upper edge of
the square only through its value, so it transports along an equality of upper edges. -/
theorem isSheafOfDifferentialsMap_eqToHom_comp {f f₁ : X' ⟶ X} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {c : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS f p p' c) (h : f₁ = f) :
    IsSheafOfDifferentialsMap B S hS f₁ p p'
      (eqToHom (congrArg (fun r : X' ⟶ X =>
          (modulePullback B S hS r).obj (sheafOfDifferentials B S hS p)) h) ≫ c) := by
  subst h
  simpa using hc

end Transport

section Global

variable {X Z Bb : AlgebraicSpaces B S hS}

/-- **The clarification of Stacks 05ZB, as an identity of comparison maps.**  For a left inverse
`g : X ⟶ Z` of `i : Z ⟶ X` over `Bb`, the carried comparison map `cid` at the identity square,
transported along `i ≫ g = 𝟙 Z`, is the composition comparison of Stacks 03LU followed by the
pullback along `i` of the comparison map of `g` and then by the second arrow of the sequence of
Stacks 05ZA.

Both sides are comparison maps of Stacks 04CX for the square with top edge `i ≫ g` — the right
one by Stacks 05Z7, the left one by transport — and such a map is unique.  Nothing is divided
out here, so no invertibility is used. -/
theorem eqToHom_comp_eq_comp_pullbackDifferentialsMap (i : Z ⟶ X) (b : X ⟶ Bb) (g : X ⟶ Z)
    (hg : i ≫ g = 𝟙 Z) (hgb : g ≫ i ≫ b = b)
    (cid : (modulePullback B S hS (𝟙 Z)).obj (sheafOfDifferentials B S hS (i ≫ b)) ⟶
      sheafOfDifferentials B S hS (i ≫ b))
    (hcid : IsSheafOfDifferentialsMap B S hS (𝟙 Z) (i ≫ b) (i ≫ b) cid) :
    eqToHom (congrArg (fun r : Z ⟶ Z =>
          (modulePullback B S hS r).obj (sheafOfDifferentials B S hS (i ≫ b))) hg) ≫ cid =
      (modulePullbackCompIso B S hS i g).inv.app (sheafOfDifferentials B S hS (i ≫ b)) ≫
        (modulePullback B S hS i).map
            (sheafOfDifferentialsMap B S hS g (i ≫ b) b (𝟙 Bb)
              (hgb.trans (Category.comp_id b).symm)) ≫
          pullbackDifferentialsMap B S hS i b :=
  eq_of_isSheafOfDifferentialsMap B S hS (i ≫ g) (i ≫ b) (i ≫ b)
    (isSheafOfDifferentialsMap_eqToHom_comp B S hS hcid hg)
    (isSheafOfDifferentialsMap_comp B S hS g i (i ≫ b) b (i ≫ b)
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS g (i ≫ b) b (𝟙 Bb)
        (hgb.trans (Category.comp_id b).symm))
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS i b (i ≫ b) (𝟙 Bb) (by simp)))

/-- **The right inverse of Stacks 05ZB, written out.**  For a left inverse `g : X ⟶ Z` of
`i : Z ⟶ X` over `Bb`, the comparison map `c_g` of Stacks 04CX pulled back along `i`, read as a
morphism out of `Ω_{Z/Bb}` through the composition comparison `(i ≫ g)^* ≅ i^*g^*` of
Stacks 03LU, the transport of `i ≫ g = 𝟙 Z`, and the inverse of the carried comparison map `cid`
at the identity square, is a right inverse of the second arrow of the sequence of
Stacks 05ZA. -/
theorem comp_pullbackDifferentialsMap_eq_id_of_leftInverse (i : Z ⟶ X) (b : X ⟶ Bb) (g : X ⟶ Z)
    (hg : i ≫ g = 𝟙 Z) (hgb : g ≫ i ≫ b = b)
    (cid : (modulePullback B S hS (𝟙 Z)).obj (sheafOfDifferentials B S hS (i ≫ b)) ⟶
      sheafOfDifferentials B S hS (i ≫ b)) [IsIso cid]
    (hcid : IsSheafOfDifferentialsMap B S hS (𝟙 Z) (i ≫ b) (i ≫ b) cid) :
    (inv cid ≫ eqToHom (congrArg (fun r : Z ⟶ Z =>
          (modulePullback B S hS r).obj (sheafOfDifferentials B S hS (i ≫ b))) hg.symm) ≫
        (modulePullbackCompIso B S hS i g).inv.app (sheafOfDifferentials B S hS (i ≫ b)) ≫
          (modulePullback B S hS i).map (sheafOfDifferentialsMap B S hS g (i ≫ b) b (𝟙 Bb)
            (hgb.trans (Category.comp_id b).symm))) ≫
        pullbackDifferentialsMap B S hS i b =
      𝟙 (sheafOfDifferentials B S hS (i ≫ b)) :=
  comp_eq_id_of_retraction_factorization _ _ ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
    cid _ _ _ (eqToHom_comp_eq_comp_pullbackDifferentialsMap B S hS i b g hg hgb cid hcid)

/-- **Stacks 05ZB**, the global clause: a left inverse of `i` over `Bb` makes the second arrow of
the sequence of Stacks 05ZA a split epimorphism, so that sequence is split exact.

The comparison map of Stacks 04CX at the identity square is carried as the parameters `cid`,
`hcid` and `[IsIso cid]`; see the implementation notes. -/
@[stacks 05ZB "the global clause: a left inverse of `i` over `B` splits the second arrow of the \
conormal sequence of 05ZA, so that sequence is split exact"]
theorem isSplitEpi_pullbackDifferentialsMap_of_leftInverse (i : Z ⟶ X) (b : X ⟶ Bb) (g : X ⟶ Z)
    (hg : i ≫ g = 𝟙 Z) (hgb : g ≫ i ≫ b = b)
    (cid : (modulePullback B S hS (𝟙 Z)).obj (sheafOfDifferentials B S hS (i ≫ b)) ⟶
      sheafOfDifferentials B S hS (i ≫ b)) [IsIso cid]
    (hcid : IsSheafOfDifferentialsMap B S hS (𝟙 Z) (i ≫ b) (i ≫ b) cid) :
    IsSplitEpi (pullbackDifferentialsMap B S hS i b) :=
  IsSplitEpi.mk'
    ⟨_, comp_pullbackDifferentialsMap_eq_id_of_leftInverse B S hS i b g hg hgb cid hcid⟩

/-- **Stacks 05ZB**, the global clause, unconditionally: a left inverse of `i` over `Bb` makes the
second arrow of the sequence of Stacks 05ZA a split epimorphism, so that sequence is split exact.

This is `AlgebraicGeometry.Space.isSplitEpi_pullbackDifferentialsMap_of_leftInverse` with the
comparison map of Stacks 04CX at the identity square supplied rather than carried: it is the unit
law of Stacks 03LU at `Ω_{Z/Bb}`, which is a comparison map by
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_modulePullbackIdIso`, and invertible by
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_id`.  Nothing is assumed beyond the
left inverse. -/
@[stacks 05ZB "the global clause, unconditionally: a left inverse of `i` over `B` splits the \
second arrow of the conormal sequence of 05ZA, so that sequence is split exact"]
theorem isSplitEpi_pullbackDifferentialsMap_of_retraction (i : Z ⟶ X) (b : X ⟶ Bb) (g : X ⟶ Z)
    (hg : i ≫ g = 𝟙 Z) (hgb : g ≫ i ≫ b = b) :
    IsSplitEpi (pullbackDifferentialsMap B S hS i b) := by
  have hcid := isSheafOfDifferentialsMap_modulePullbackIdIso B S hS (i ≫ b)
  have := isIso_of_isSheafOfDifferentialsMap_id B S hS _ hcid
  exact isSplitEpi_pullbackDifferentialsMap_of_leftInverse B S hS i b g hg hgb _ hcid

end Global

section EtaleLocal

variable {X Z X' Z' Bb : AlgebraicSpaces B S hS}

/-- **Stacks 05Z7 at the two factorizations of `i' ≫ φ = a ≫ i`.**  Going from
`(a ≫ i)^*Ω_{X/Bb}` to `Ω_{Z'/Bb}` through `i^*Ω_{X/Bb}` and the comparison map `ca` along `a` is
the same as going through `φ^*Ω_{X/Bb}` and the comparison map along `i'`, after the transport of
`i' ≫ φ = a ≫ i`.

Both sides are comparison maps of Stacks 04CX for the square with top edge `a ≫ i`, by
Stacks 05Z7 for the two factorizations, and such a map is unique.  No invertibility is used. -/
theorem comp_comp_eq_eqToHom_comp (i : Z ⟶ X) (b : X ⟶ Bb) (φ : X' ⟶ X) (i' : Z' ⟶ X')
    (a : Z' ⟶ Z) (hsq : i' ≫ φ = a ≫ i)
    (ca : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS (i ≫ b)) ⟶
      sheafOfDifferentials B S hS (i' ≫ φ ≫ b))
    (hca : IsSheafOfDifferentialsMap B S hS a (i ≫ b) (i' ≫ φ ≫ b) ca) :
    (modulePullbackCompIso B S hS a i).inv.app (sheafOfDifferentials B S hS b) ≫
        (modulePullback B S hS a).map (pullbackDifferentialsMap B S hS i b) ≫ ca =
      eqToHom (congrArg (fun r : Z' ⟶ X =>
          (modulePullback B S hS r).obj (sheafOfDifferentials B S hS b)) hsq.symm) ≫
        (modulePullbackCompIso B S hS i' φ).inv.app (sheafOfDifferentials B S hS b) ≫
          (modulePullback B S hS i').map (pullbackDifferentialsMap B S hS φ b) ≫
            pullbackDifferentialsMap B S hS i' (φ ≫ b) :=
  eq_of_isSheafOfDifferentialsMap B S hS (a ≫ i) b (i' ≫ φ ≫ b)
    (isSheafOfDifferentialsMap_comp B S hS i a b (i ≫ b) (i' ≫ φ ≫ b)
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS i b (i ≫ b) (𝟙 Bb) (by simp))
      hca)
    (isSheafOfDifferentialsMap_eqToHom_comp B S hS
      (isSheafOfDifferentialsMap_comp B S hS φ i' b (φ ≫ b) (i' ≫ φ ≫ b)
        (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS φ b (φ ≫ b) (𝟙 Bb) (by simp))
        (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS i' (φ ≫ b) (i' ≫ φ ≫ b)
          (𝟙 Bb) (by simp)))
      hsq.symm)

/-- **Stacks 05ZB**, the étale-local clause: if the restriction of `i` along an étale
`φ : X' ⟶ X` has a left inverse over `Bb`, the inverse image along the induced `a : Z' ⟶ Z` of the
second arrow of the sequence of Stacks 05ZA is a split epimorphism, so the restricted sequence is
split exact.

The section is the chosen section of the global clause at `i'`, conjugated by the two invertible
comparison maps of Stacks 04CU and the composition comparisons of Stacks 03LU.  The comparison
map at the identity square and the étale-localization clause of Stacks 04CU are carried as
parameters and instances; see the implementation notes. -/
@[stacks 05ZB "the étale-local clause: a left inverse of the restriction of `i` along an étale \
`φ : X' ⟶ X` splits the inverse image along the induced `a : Z' ⟶ Z` of the second arrow of the \
conormal sequence of 05ZA"]
theorem isSplitEpi_map_pullbackDifferentialsMap_of_etaleLeftInverse (i : Z ⟶ X) (b : X ⟶ Bb)
    (φ : X' ⟶ X) (i' : Z' ⟶ X') (a : Z' ⟶ Z) (hsq : i' ≫ φ = a ≫ i) (g' : X' ⟶ Z')
    (hg' : i' ≫ g' = 𝟙 Z') (hg'b : g' ≫ i' ≫ φ ≫ b = φ ≫ b)
    (cid' : (modulePullback B S hS (𝟙 Z')).obj
        (sheafOfDifferentials B S hS (i' ≫ φ ≫ b)) ⟶
      sheafOfDifferentials B S hS (i' ≫ φ ≫ b)) [IsIso cid']
    (hcid' : IsSheafOfDifferentialsMap B S hS (𝟙 Z') (i' ≫ φ ≫ b) (i' ≫ φ ≫ b) cid')
    (ca : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS (i ≫ b)) ⟶
      sheafOfDifferentials B S hS (i' ≫ φ ≫ b)) [IsIso ca]
    (hca : IsSheafOfDifferentialsMap B S hS a (i ≫ b) (i' ≫ φ ≫ b) ca)
    [IsIso (pullbackDifferentialsMap B S hS φ b)] :
    IsSplitEpi ((modulePullback B S hS a).map (pullbackDifferentialsMap B S hS i b)) := by
  have : IsSplitEpi (pullbackDifferentialsMap B S hS i' (φ ≫ b)) :=
    isSplitEpi_pullbackDifferentialsMap_of_leftInverse B S hS i' (φ ≫ b) g' hg' hg'b cid' hcid'
  exact IsSplitEpi.mk' ⟨_, comp_eq_id_of_retraction_factorization₂ ca
    (section_ (pullbackDifferentialsMap B S hS i' (φ ≫ b))) _
    (IsSplitEpi.id (pullbackDifferentialsMap B S hS i' (φ ≫ b)))
    ((modulePullback B S hS i').map (pullbackDifferentialsMap B S hS φ b))
    ((modulePullbackCompIso B S hS i' φ).hom.app (sheafOfDifferentials B S hS b)) _
    (Iso.hom_inv_id_app _ _)
    (eqToHom (congrArg (fun r : Z' ⟶ X =>
      (modulePullback B S hS r).obj (sheafOfDifferentials B S hS b)) hsq)) _
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _)) _ _
    (comp_comp_eq_eqToHom_comp B S hS i b φ i' a hsq ca hca)⟩

/-- **Stacks 05ZB**, the étale-local clause, with the comparison map at the identity square no
longer carried: if the restriction of `i` along an étale `φ : X' ⟶ X` has a left inverse over
`Bb`, the inverse image along the induced `a : Z' ⟶ Z` of the second arrow of the sequence of
Stacks 05ZA is a split epimorphism, so the restricted sequence is split exact.

This is `AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etaleLeftInverse` with
the unit law of Stacks 04CX supplied rather than carried, by
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_modulePullbackIdIso` and
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_id`.  So this clause is unconditional
in Stacks 04CX.

It still takes the invertibility of the two comparison maps as the instances `[IsIso ca]` and
`[IsIso (pullbackDifferentialsMap B S hS φ b)]`, which is the conclusion of the
étale-localization clause of Stacks 04CU at `a` and at `φ`; étaleness of `φ` and of `a` is not
assumed, so this applies to any square where those two maps are invertible.
`AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etale` is the form that
assumes étaleness and discharges the two instances. -/
@[stacks 05ZB "the étale-local clause, unconditional in 04CX: a left inverse of the restriction \
of `i` along an étale `φ : X' ⟶ X` splits the inverse image along the induced `a : Z' ⟶ Z` of the \
second arrow of the conormal sequence of 05ZA"]
theorem isSplitEpi_map_pullbackDifferentialsMap_of_etaleRetraction (i : Z ⟶ X) (b : X ⟶ Bb)
    (φ : X' ⟶ X) (i' : Z' ⟶ X') (a : Z' ⟶ Z) (hsq : i' ≫ φ = a ≫ i) (g' : X' ⟶ Z')
    (hg' : i' ≫ g' = 𝟙 Z') (hg'b : g' ≫ i' ≫ φ ≫ b = φ ≫ b)
    (ca : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS (i ≫ b)) ⟶
      sheafOfDifferentials B S hS (i' ≫ φ ≫ b)) [IsIso ca]
    (hca : IsSheafOfDifferentialsMap B S hS a (i ≫ b) (i' ≫ φ ≫ b) ca)
    [IsIso (pullbackDifferentialsMap B S hS φ b)] :
    IsSplitEpi ((modulePullback B S hS a).map (pullbackDifferentialsMap B S hS i b)) := by
  have hcid' := isSheafOfDifferentialsMap_modulePullbackIdIso B S hS (i' ≫ φ ≫ b)
  have := isIso_of_isSheafOfDifferentialsMap_id B S hS _ hcid'
  exact isSplitEpi_map_pullbackDifferentialsMap_of_etaleLeftInverse B S hS i b φ i' a hsq g' hg'
    hg'b _ hcid' ca hca

/-- **Stacks 05ZB**, the étale-local clause, with nothing carried: if `φ : X' ⟶ X` and the
induced `a : Z' ⟶ Z` are étale and the restriction `i' : Z' ⟶ X'` of `i` along `φ` has a left
inverse over `Bb`, then the inverse image along `a` of the second arrow of the sequence of
Stacks 05ZA is a split epimorphism, so the restricted sequence is split exact.

This is `AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etaleRetraction` with
the two invertible comparison maps supplied rather than carried: the comparison map of
Stacks 04CX along an étale morphism, over a fixed base, is invertible by
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_etale`, which is the
étale-localization clause of Stacks 04CU.  So nothing is assumed here beyond the hypotheses of
the source: `φ` is étale, `a` — a base change of `φ` in the situation of the source — is étale,
the square `i' ≫ φ = a ≫ i` commutes, and `i'` has the left inverse `g'` over `Bb`. -/
@[stacks 05ZB "the étale-local clause, with nothing carried: for étale `φ : X' ⟶ X` and `a`, a \
left inverse of the restriction of `i` along `φ` splits the inverse image along `a` of the \
second arrow of the conormal sequence of 05ZA"]
theorem isSplitEpi_map_pullbackDifferentialsMap_of_etale (i : Z ⟶ X) (b : X ⟶ Bb)
    (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom) (i' : Z' ⟶ X') (a : Z' ⟶ Z)
    (ha : IsEtale B S hS a.hom) (hsq : i' ≫ φ = a ≫ i) (g' : X' ⟶ Z')
    (hg' : i' ≫ g' = 𝟙 Z') (hg'b : g' ≫ i' ≫ φ ≫ b = φ ≫ b) :
    IsSplitEpi ((modulePullback B S hS a).map (pullbackDifferentialsMap B S hS i b)) := by
  have hpath : a ≫ i ≫ b = i' ≫ φ ≫ b := by
    rw [← Category.assoc, ← hsq, Category.assoc]
  have hca := isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS a (i ≫ b)
    (i' ≫ φ ≫ b) (𝟙 Bb) (hpath.trans (Category.comp_id _).symm)
  have := isIso_of_isSheafOfDifferentialsMap_etale B S hS a ha _ _ hpath hca
  have : IsIso (pullbackDifferentialsMap B S hS φ b) :=
    isIso_pullbackDifferentialsMap_of_isEtale B S hS φ hφ b
  exact isSplitEpi_map_pullbackDifferentialsMap_of_etaleRetraction B S hS i b φ i' a hsq g'
    hg' hg'b _ hca

end EtaleLocal

end AlgebraicGeometry.Space

end
