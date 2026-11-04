module

public import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generating a topology by the covering families with prescribed sources

A presheaf is a sheaf for a Grothendieck topology as soon as it satisfies the sheaf condition for
*enough* covering families: enough meaning that every covering sieve contains one of them.  No
stability of the chosen collection under base change is needed, because the topology itself
supplies the covering sieves the pullbacks generate, and separatedness — which is all a pullback
is used for — only ever grows when a presieve grows.

The application is a site in which the objects of a distinguished class, here the affine ones,
cover every object.  The arrows of a covering sieve whose source lies in the class then already
generate a covering sieve, by one application of the transitivity axiom, so a presheaf which is a
sheaf for the covering families with sources in the class is a sheaf.  Under the extra assumption
that an object has the finite subcovering property, the family may moreover be taken finite, which
is what reduces a covering of an affine object to a single morphism out of a disjoint union of
affines.

## Main definitions

* `CategoryTheory.Sieve.restrictToObjects`: the arrows of a sieve whose source satisfies a given
  property of objects.
* `CategoryTheory.GrothendieckTopology.precoverageOfObjects`: the precoverage of the covering
  families all of whose members have source satisfying a given property of objects.

## Main results

* `CategoryTheory.Precoverage.generates_of_refines`: **a precoverage whose covering families
  refine every covering sieve generates the topology**, in the sense of
  `CategoryTheory.Precoverage.Generates`; so by
  `CategoryTheory.Precoverage.Generates.isSheaf_iff` a presheaf with values in any category is a
  sheaf as soon as it satisfies the sheaf condition for those families.
* `CategoryTheory.Presieve.IsSeparatedFor.mono`: separatedness grows with the presieve.
* `CategoryTheory.GrothendieckTopology.generate_restrictToObjects_mem`: if the objects satisfying
  `Q` cover every object, the arrows of a covering sieve with source satisfying `Q` generate a
  covering sieve.
* `CategoryTheory.GrothendieckTopology.generates_precoverageOfObjects`: **the covering families
  with sources in a covering class of objects generate the topology.**
* `CategoryTheory.GrothendieckTopology.not_generates_precoverageOfObjects_eqTrue`: **the
  hypothesis that the distinguished objects cover every object cannot be weakened to their
  covering one another.**  A two-object poset, with the larger object distinguished, is a site on
  which the distinguished covering families impose nothing and a representable presheaf fails the
  sheaf condition.

## Implementation notes

`CategoryTheory.Precoverage.Generates` is stated for presheaves of types in the universe
`max u v`, and `CategoryTheory.Precoverage.Generates.isSheaf_of_forall` upgrades it to any
universe; so the results below are proved for that one universe and used at any.

The index type of the covering families produced by a class of objects is left as a universe
parameter rather than fixed at `max u v`: in the application the class of affine objects of a
category fibred in groupoids produces families indexed by the index type of an affine open cover
of a scheme, which is one level above the morphisms of the site.

`CategoryTheory.Precoverage.Generates` has, in Mathlib, the single constructor
`CategoryTheory.Coverage.generates_toGrothendieck`, which asks the collection of covering
families to be a coverage — that is, to admit, over every morphism, a covering family factoring
through the given one.  `CategoryTheory.Precoverage.generates_of_refines` asks instead only that
every covering *sieve* be refined, which needs no fibre products in the site; it is plausibly
worth having in Mathlib itself.

For the big fpqc site of all schemes the corresponding statement is already in Mathlib, as
`AlgebraicGeometry.isSheaf_propQCTopology_iff` (Stacks 022H): a presheaf on `Scheme` is an fpqc
sheaf exactly when it is a Zariski sheaf and satisfies the sheaf condition for every flat
surjection between affine schemes.  That result is about the category of all schemes, so it
transfers neither to a size-bounded big site, nor to a slice of one, nor to a category fibred in
groupoids over one; its proof is however the template followed here — reduce to the distinguished
objects, then to a single morphism.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0D05](https://stacks.math.columbia.edu/tag/0D05)
* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
-/

@[expose] public section

open CategoryTheory Opposite

universe w w' v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Presieve

/-- **Separatedness grows with the presieve.**  A family of elements for the larger presieve
restricts to one for the smaller, and the two have the same amalgamations. -/
theorem IsSeparatedFor.mono {P : Cᵒᵖ ⥤ Type w} {X : C} {R R' : Presieve X}
    (hR : IsSeparatedFor P R) (h : R ≤ R') : IsSeparatedFor P R' := fun x t₁ t₂ ht₁ ht₂ =>
  hR (x.restrict h) t₁ t₂ (isAmalgamation_restrict h x t₁ ht₁)
    (isAmalgamation_restrict h x t₂ ht₂)

end Presieve

namespace Precoverage

/-- **A precoverage whose covering families refine every covering sieve generates the topology.**
Separatedness for an arbitrary covering sieve follows from separatedness for the refining family,
because separatedness grows with the presieve; and that is exactly the hypothesis
`CategoryTheory.Presieve.isSheafFor_subsieve_aux` needs about the pullbacks of the refining
family, which are themselves covering.  No stability of `K` under base change is used, and no
fibre products in the site are needed; this is plausibly worth having in Mathlib, whose only
constructor for `CategoryTheory.Precoverage.Generates` asks `K` to be a coverage. -/
theorem generates_of_refines (K : Precoverage C) (J : GrothendieckTopology C)
    (hle : K ≤ J.toPrecoverage)
    (hrefine : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
      ∃ R ∈ K X, (R : Presieve X) ≤ (S : Presieve X)) :
    K.Generates J where
  le_toPrecoverage := hle
  isSheaf_of_forall_max F H := by
    have hsep : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
        Presieve.IsSeparatedFor F (S : Presieve X) := by
      intro X S hS
      obtain ⟨R, hR, hRS⟩ := hrefine S hS
      exact (H R hR).isSeparatedFor.mono hRS
    intro X S hS
    obtain ⟨R, hR, hRS⟩ := hrefine S hS
    exact Presieve.isSheafFor_subsieve_aux F (S := Sieve.generate R)
      ((Sieve.generate_le_iff R S).2 hRS) ((Presieve.isSheafFor_iff_generate R).1 (H R hR))
      fun {_} {f} _ => hsep _ (J.pullback_stable f (hle _ hR))

end Precoverage

/-- The arrows of a sieve whose source satisfies a property of objects. -/
def Sieve.restrictToObjects {X : C} (S : Sieve X) (Q : C → Prop) : Presieve X :=
  fun Y f => S f ∧ Q Y

/-- The arrows of a sieve with source satisfying a property of objects form a sub-presieve of
the sieve. -/
lemma Sieve.restrictToObjects_le {X : C} (S : Sieve X) (Q : C → Prop) :
    S.restrictToObjects Q ≤ (S : Presieve X) := fun _ _ hf => hf.1

/-- Membership in `CategoryTheory.Sieve.restrictToObjects`, unfolded. -/
lemma Sieve.restrictToObjects_apply {X Y : C} (S : Sieve X) (Q : C → Prop) (f : Y ⟶ X) :
    S.restrictToObjects Q f ↔ S f ∧ Q Y := Iff.rfl

namespace GrothendieckTopology

/-- The covering families all of whose members have source satisfying a property of objects. -/
def precoverageOfObjects (J : GrothendieckTopology C) (Q : C → Prop) : Precoverage C where
  coverings X := {R | Sieve.generate R ∈ J X ∧ ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Q Y}

/-- Membership in `CategoryTheory.GrothendieckTopology.precoverageOfObjects`, unfolded. -/
lemma mem_precoverageOfObjects_iff (J : GrothendieckTopology C) (Q : C → Prop) {X : C}
    (R : Presieve X) :
    R ∈ J.precoverageOfObjects Q X ↔
      Sieve.generate R ∈ J X ∧ ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Q Y := Iff.rfl

variable (J : GrothendieckTopology C) (Q : C → Prop)
  (hQ : ∀ X : C, ∃ (I : Type w') (Y : I → C) (g : ∀ i, Y i ⟶ X),
    (∀ i, Q (Y i)) ∧ Sieve.ofArrows Y g ∈ J X)

include hQ

/-- **The arrows of a covering sieve whose source satisfies `Q` generate a covering sieve**, when
the objects satisfying `Q` cover every object.  One application of the transitivity axiom: over a
member of the given sieve, the covering family of objects satisfying `Q` composes into the sieve,
and its members are among the arrows retained. -/
@[sga "4 II 3.0.4" "more general"]
theorem generate_restrictToObjects_mem {X : C} (S : Sieve X) (hS : S ∈ J X) :
    Sieve.generate (S.restrictToObjects Q) ∈ J X := by
  refine J.transitive hS _ fun {Y} f hf => ?_
  obtain ⟨I, Z, g, hQZ, hcov⟩ := hQ Y
  refine J.superset_covering (fun W a ha => ?_) hcov
  rw [Sieve.mem_ofArrows_iff] at ha
  obtain ⟨i, c, rfl⟩ := ha
  exact ⟨Z i, c, g i ≫ f, ⟨S.downward_closed hf (g i), hQZ i⟩, by simp⟩

/-- **The covering families with sources in a covering class of objects generate the topology.**
Together with `CategoryTheory.Precoverage.Generates.isSheaf_iff` this says that a presheaf with
values in any category is a sheaf as soon as it satisfies the sheaf condition for the covering
families whose members all have source satisfying `Q`. -/
theorem generates_precoverageOfObjects : (J.precoverageOfObjects Q).Generates J :=
  Precoverage.generates_of_refines _ _ (fun _ _ hR => hR.1) fun {_} S hS =>
    ⟨S.restrictToObjects Q, ⟨generate_restrictToObjects_mem J Q hQ S hS, fun _ _ hf => hf.2⟩,
      S.restrictToObjects_le Q⟩

omit hQ

/-- The topology whose covering sieves are those containing every morphism out of a fixed object:
that object alone is a covering of each object of the site. -/
def ofGenerator (w : C) : GrothendieckTopology C where
  sieves X := {S | ∀ f : w ⟶ X, S f}
  top_mem' _ _ := True.intro
  pullback_stable' _ _ _ f hS g := hS (g ≫ f)
  transitive' _ _ hS R hR f := by
    simpa using hR (hS f) (𝟙 w)

/-- Membership in `CategoryTheory.GrothendieckTopology.ofGenerator`, unfolded. -/
lemma mem_ofGenerator_iff {w X : C} (S : Sieve X) :
    S ∈ ofGenerator w X ↔ ∀ f : w ⟶ X, S f := Iff.rfl

/-- **The hypothesis of `CategoryTheory.GrothendieckTopology.generates_precoverageOfObjects` that
the objects satisfying `Q` cover *every* object cannot be weakened to their covering only the
objects satisfying `Q`.**

The site is the two-element poset `false ≤ true`, with the topology whose covering sieves are
those containing every morphism out of `false`, and `Q` is the property of being `true`.  The
object `true` is covered by itself, so `Q` does supply a covering family of every object
satisfying it; but no covering family of either object has all its sources satisfying `Q` except
the identity of `true`, so the covering families of
`CategoryTheory.GrothendieckTopology.precoverageOfObjects` impose nothing.  The presheaf
represented by `false` is nevertheless not a sheaf: the morphism `false ⟶ true` generates a
covering sieve of `true`, and a section over `false` has no restriction from `true`, there being
no morphism `true ⟶ false`.

This is the reason the comparison criterion for a big site of schemes must be given the sheaf
condition for coverings by affine objects of *arbitrary* objects, and not only of affine ones:
without it, nothing at all is required of the presheaf at an object the affine objects do not
reach. -/
theorem not_generates_precoverageOfObjects_eqTrue :
    ¬ ((ofGenerator (false : Bool)).precoverageOfObjects (fun X => X = true)).Generates
        (ofGenerator (false : Bool)) := by
  intro H
  have key : ∀ ⦃X : Bool⦄, ∀ R ∈ (ofGenerator (false : Bool)).precoverageOfObjects
      (fun X => X = true) X,
      Presieve.IsSheafFor (yoneda.obj (false : Bool)) R := by
    intro X R hR
    obtain ⟨hgen, hsrc⟩ := hR
    obtain ⟨Y, a, b, hb, hab⟩ := hgen (homOfLE (Bool.false_le X))
    cases hsrc b hb
    have hid : Sieve.generate R (𝟙 X) := by
      rw [show (𝟙 X) = homOfLE (Bool.le_true X) ≫ b from Subsingleton.elim _ _]
      exact (Sieve.generate R).downward_closed (Sieve.le_generate R _ _ hb) _
    rw [Presieve.isSheafFor_iff_generate, Sieve.id_mem_iff_eq_top.1 hid]
    simpa using Presieve.isSheafFor_top (yoneda.obj (false : Bool)) (X := X)
  have hsheaf := H.isSheaf_type_iff.2 key
  have hcov : Sieve.generate (Presieve.singleton (homOfLE (Bool.false_le true))) ∈
      ofGenerator (false : Bool) true := fun f => by
    rw [show f = homOfLE (Bool.false_le true) from Subsingleton.elim _ _]
    exact Sieve.le_generate _ _ _ Presieve.singleton.mk
  have h1 : Presieve.IsSheafFor (yoneda.obj (false : Bool))
      (Presieve.singleton (homOfLE (Bool.false_le true))) :=
    (Presieve.isSheafFor_iff_generate _).2 (hsheaf _ hcov)
  rw [Presieve.isSheafFor_singleton] at h1
  obtain ⟨y, -⟩ :=
    (h1 (𝟙 (false : Bool)) fun p₁ p₂ _ => by rw [Subsingleton.elim p₁ p₂]).exists
  exact absurd (leOfHom y) (by decide)

end GrothendieckTopology

end CategoryTheory

end
