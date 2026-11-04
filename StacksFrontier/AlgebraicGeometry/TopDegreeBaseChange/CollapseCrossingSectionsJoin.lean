module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SectionsRestrictMatch

/-!
# The collapse crossing of conclusion (c) of [Stacks, Tag 0EX3] against 01E5 on sections

`…TopDegreeBaseChange.collapse_crossing_restrictedMorphism` (`CollapseCrossingGeometric.lean`)
identifies the collapse of [Stacks, Tag 01XK] that the `ψ` side of conclusion (c) of
[Stacks, Tag 0EX3] arrives in with the one the `γ⁺` side arrives in, and its right-hand side
begins with two factors — `…TopDegreeBaseChange.openSubschemeTopSections V` of the
**ringed-space** [Stacks, Tag 01E5]
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso`, then
`…TopDegreeBaseChange.restrictCompSectionsIso`.

`…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso_hom_eq_restrictCompSectionsIso`
(`SectionsRestrictMatch.lean`) ends at that second factor, and its own second factor is the
*scheme-level* 01E5 read under the same outer functor, which
`…TopDegreeBaseChange.higherDirectImageRestrictIso_hom_eq` exhibits as the ringed-space one
conjugated by two casts. **This file identifies the two sets of factors**: the three factors the
match carries from its scheme-level 01E5 onwards are the two the crossing begins with, with the
source cast of the scheme-level 01E5 in front and the sections over `V` of the comparison of the
two indexings at `f` behind.

That identification is the content of the join. **The join itself is not performed here**: welding
this identification onto `…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso` — so that the
`ψ` side's collapse composite is read as [Stacks, Tag 01E5] on sections — is a
`(kernel) deterministic timeout` in every known form, and the last section of these notes
records those forms and where the obstruction lies.

## Main results

* `…TopDegreeBaseChange.whiskerRight_higherDirectImageRestrictIso_hom_eq` and
  `…TopDegreeBaseChange.openSubschemeTopSections_map_higherDirectImageRestrictIso_hom_app` — **the
  split of the scheme-level 01E5 under the `ψ` side's outer functor**, performed at the level of
  natural transformations and only then read at a module. Every module-level route to it is a
  kernel timeout; see the implementation notes.
* `…TopDegreeBaseChange.restrictCompSectionsIso_hom_app_naturality_of_eq` — **the step that moves
  `restrictCompSectionsIso` to the front.** A morphism of modules on the open subscheme `V`,
  conjugated into the ringed-space restriction of a morphism on `Y`, read under the outer functor
  and followed by `restrictCompSectionsIso` at the target, is `restrictCompSectionsIso` at the
  source followed by the sections over `V` of that morphism. Its conjugating morphisms are
  variables, which is what keeps it cheap, and
  `…TopDegreeBaseChange.restrictCompSectionsIso_hom_app_naturality_rightDerivedIso` is its
  instantiation at the comparison of the two indexings at `f`.
* `…TopDegreeBaseChange.moduleRestriction_map_eq_restrictFunctor_map`,
  `…TopDegreeBaseChange.eqToIso_higherDirectImageRestrictIso_target_hom_app` and
  `…TopDegreeBaseChange.higherDirectImageRestrictIso_target_app_comp_restrictFunctor_map` — the
  two readings of the `restrictFunctor`-versus-`moduleRestriction` cast and the hypothesis the
  naturality step is applied with.
* `…TopDegreeBaseChange.higherDirectImageRestrictIso_hom_app_comp_restrictCompSectionsIso_eq` and
  `…TopDegreeBaseChange.schemeHigherDirectImageRestrictIso_hom_app_comp_tail_eq` — **the
  identification, in both orientations.** The second is the first inverted, and it is declared
  rather than taken with `Eq.symm` where it is needed: see the implementation notes.

**Nothing is assumed** anywhere in this file: no affineness, no quasi-compactness, no
quasi-separatedness, no quasi-coherence, and no hypothesis on the degree.

## Implementation notes

*The split of the scheme-level 01E5 under the outer functor must be paid at the level of natural
transformations, and four module-level routes to it are kernel timeouts.* Each of the following times out in the kernel, on a
statement and proof that **elaborate** without error:

* `congrArg (fun t => (openSubschemeTopSections V).map t)` applied to the cast entry at a module;
* the same with that `congrArg` hoisted into a lemma stated at variable morphisms, so that only
  its instantiation is left at the concrete ones;
* `…openSubschemeTopSections_map_comp` against the composite spelled
  `(higherDirectImageRestrictIso f V p).hom.app M`, relying on the definitional unfolding of the
  comparison rather than on an equation — one split and the full three-way split alike;
* and a generic `G.map (a ≫ b ≫ c) = G.map a ≫ G.map b ≫ G.map c` applied as a term.

What is **not** expensive, and this is what locates the cost: the same `…map_comp` at the same
concrete morphisms with the composite written out explicitly checks in seconds, as does the cast
entry itself at a module. So neither the outer functor nor the cast entry is the obstruction; it is
identifying `(…higherDirectImageRestrictIso f V p).hom.app M` with the explicit composite
*underneath* `(openSubschemeTopSections V).map`. Whiskering the cast entry by the outer functor and
only then taking the component at `M` avoids that identification altogether —
`CategoryTheory.Functor.whiskerRight_comp` splits where no object is applied, and
`(Functor.whiskerRight α G).app M` is `G.map (α.app M)` definitionally — and the two declarations
together check in seconds.

*The second cast is therefore never pushed under the outer functor.* It stays as
`(eqToIso (higherDirectImageRestrictIso_target f V p).symm).hom.app M`, and the naturality step is
stated with its conjugating morphisms as **variables** plus the hypothesis that the conjugate is
the ringed-space restriction of the morphism. That hypothesis is an equation inside the modules on
`V` — no outer functor — and there `…eqToIso_higherDirectImageRestrictIso_target_hom_app` and
`…moduleRestriction_map_eq_restrictFunctor_map` discharge it.

*Two rewrite patterns fail at these spellings.* `rw [eqToIso.hom]` and
`simp only [eqToIso.hom, eqToHom_app]` on
`(eqToIso (higherDirectImageRestrictIso_target f V p).symm).hom.app M` both report "did not find an
occurrence" (verbatim), with the note that the target is not type-correct at `implicit`
transparency: the functor equality is elaborated at the ringed-space spelling of the two functor
categories while `M` is at the scheme spelling. The step is a term, `congrArg` of
`CategoryTheory.eqToIso.hom` and then `CategoryTheory.eqToHom_app`.

*The orientation of the identification decides whether it can be proved at all.* Written with the
crossing's own factors first it is the term `comp₄_split_head_absorb` produces and checks in
seconds; written with the match's factors first the **same** term is a
`(kernel) deterministic timeout`, and so are `simp only` and `rw` at either orientation (the latter
leaving an unsolved goal rather than timing out). This is the discipline that `theorem _ : A = B`
elaborates `A` and then `B` against `A`'s type, so that a spelling crossing is paid once rather
than twice. The match-first orientation is then reached by `Eq.symm` **in its own declaration**,
where it checks; taken with `.symm` inside a larger term it does not.

*Why the segment rewrites are declared at a variable category.* The composites here are long enough
that `rw [Category.assoc]` does not find its pattern on the goal, which is the reason `StacksFrontier.CategoryTheory.CompositeCancellation` exists. The three
statements of the first section are the segment rewrites this identification needs and none of them
is in that module; they are stated at a variable category and applied as terms, so that the
caller's morphisms keep their own spellings and the objects between them are checked at default
transparency. A fourth, `comp₅_split_mid_absorb`, is deliberately not provided: proved by
`rw`/`simp only` at variables it is a kernel timeout when instantiated here, because a rewrite's
`Eq.mpr` motives are then type-checked at the concrete objects, whereas the term-proved
`comp₄_split_head_absorb` is not.

*What the weld owes.* With the identification in
hand in either orientation, the join is one `Eq.trans` with the match and one cancellation of the
comparison of the two indexings against its inverse. Six routes to that one step are known and
**all six are `(kernel) deterministic timeout`s** — on terms and statements that elaborate with no
error:

* `((match).trans (comp_congr_right _ identification)).symm` and the same with the orientations of
  the identification and of the conclusion exchanged, in all four combinations;
* the same with the match re-elaborated right-hand side first in its own declaration, so that the
  two sides' implicit arguments come from the same elaboration;
* `refine (comp_congr_right _ identification).trans ?_` closed by `exact (match).symm`, which
  elaborates — the elaborator accepts the identification of the two sides — and then fails in the
  kernel; and by `convert (match).symm using 2` and `using 3`, which leave an unsolved goal as
  well.

So the obstruction is not the orientation discipline, not the association, and not a missing
mathematical step.

*The obstruction located, and the four further routes that refute the reading above.* The reading
above — that the cost is the kernel's `Eq.trans` whose middle term is the match's five-factor
right-hand side, so that a match re-proved directly in these factors would move it — is **wrong**,
and four more observations say where the cost really is. Write `a` for the leading factor
`openSubschemeTopSections V` of the comparison of the two indexings at `f ∣_ V` inverted, and `L`,
`R` for the two sides of `schemeHigherDirectImageRestrictIso_hom_app_comp_tail_eq`.

* **The match re-proved directly in these factors is the same timeout.** A statement
  `(01E5 on sections).hom = a ≫ R` proved by a term-level segment lemma from
  `…rightDerivedPlusRestrictSectionsIso_hom_eq`, the split of the sheaf-level comparison and
  `…SectionsRestrictMatch.openSectionsModuleIso_hom_eq` — so that the five-factor composite is
  never the middle term of any `Eq.trans` — is a `(kernel) deterministic timeout`. So is the same
  with `…SectionsRestrictMatch.rightDerivedPlusRestrictSectionsIso_hom_eq_cast_comp` in place of
  the last two, which is the second prescription above (one further unfolding of the comparison
  before the chase) carried out: that declaration itself checks in seconds, and the weld built on
  it does not.
* **Nor is the cost the statement.** `a ≫ R = a ≫ L`, `a ≫ L = a ≫ L` and `(R = L) = (R = L)` all
  **check**, the three of them together in 23 s — so the kernel forms either headed composite, and
  the proposition that equates them, without difficulty.
* **Nor is it the match.** `L = R` restated in a fresh declaration and proved from the existing one
  **checks**, the whole module in 24 s.
* **It is the head.** `a ≫ R = a ≫ L` is a timeout under each of these proofs:
  `comp_congr_right _ identification` at either orientation of the identification and of the
  conclusion; a five-factor term segment lemma `comp_congr_right a (comp₄_split_head_absorb …)`
  fed the identification's own two ingredients, at either orientation, so that the identification
  is rebuilt inline rather than compared with a stored statement; and the same with `a` written in
  the whiskered spelling `(Functor.isoWhiskerLeft _ (rightDerivedIso _ p).symm).hom.app M`, which
  makes the junction `target a = source R` syntactic (the uncomposed `.obj` of
  `CategoryTheory.Functor.comp` against the composite one) and changes nothing.

So the wall is precisely: **precomposing this identification with one further factor**, where
neither composite, nor the equation between them, nor the identification itself is expensive on its
own. A route that is to move it must therefore avoid ever holding `a ≫ L` and `a ≫ R` in one
proof term — not merely avoid the five-factor middle term, which is what the four routes above
all did.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 01E5] and [Stacks, Tag 01XK] carry their own
where their comparisons are built, and conclusion (c) of [Stacks, Tag 0EX3] is **not** proved
anywhere in the tree. The tail identity the reduction still owes is untouched here.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The segment rewrites, at a variable category -/

section Segments

variable {C : Type*} [Category C]

/-- **A composite postcomposed with a fixed morphism**, as a term. -/
theorem comp_congr_left {A B D : C} {u v : A ⟶ B} (h : u = v) (w : B ⟶ D) : u ≫ w = v ≫ w :=
  congrArg (fun t => t ≫ w) h

/-- **A composite precomposed with a fixed morphism**, as a term. -/
theorem comp_congr_right {A B D : C} (u : A ⟶ B) {v w : B ⟶ D} (h : v = w) : u ≫ v = u ≫ w :=
  congrArg (fun t => u ≫ t) h

/-- **A four-fold composite whose head splits into three, with the last of the three absorbed into
what follows it.** Given a splitting `b = b₁ ≫ b₂ ≫ b₃` and an identification `ht` of
`b₃ ≫ c ≫ d ≫ e` with `q ≫ s`, the composite `b ≫ c ≫ d ≫ e` is `b₁ ≫ b₂ ≫ q ≫ s`.

Proved as a term rather than by `rw`: see this module's implementation notes. -/
theorem comp₄_split_head_absorb {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ : C}
    {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄} {e : A₄ ⟶ A₅}
    {b₁ : A₁ ⟶ B₁} {b₂ : B₁ ⟶ B₂} {b₃ : B₂ ⟶ A₂} {q : B₂ ⟶ B₃} {s : B₃ ⟶ A₅}
    (hb : b = b₁ ≫ b₂ ≫ b₃) (ht : b₃ ≫ c ≫ d ≫ e = q ≫ s) :
    b ≫ c ≫ d ≫ e = b₁ ≫ b₂ ≫ q ≫ s :=
  (comp_congr_left hb (c ≫ d ≫ e)).trans
    ((Category.assoc _ _ _).trans
      (comp_congr_right b₁ ((Category.assoc _ _ _).trans (comp_congr_right b₂ ht))))

end Segments

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ)

/-! ### Moving `restrictCompSectionsIso` to the front -/

/-- **The step that moves `…TopDegreeBaseChange.restrictCompSectionsIso` to the front of the
crossing's right-hand side.** A morphism `ψ` of modules on the open subscheme `V`, conjugated by
`κ` and `κ'` into the ringed-space restriction of `φ`, read under the `ψ` side's outer functor and
followed by `restrictCompSectionsIso` at the target, is `restrictCompSectionsIso` at the source
followed by the sections over `V` of `φ`.

This is the naturality of `restrictCompSectionsIso`, whose source functor is the ringed-space
restriction followed by the outer functor. The conjugating morphisms are **variables** with their
identification as a hypothesis, which is what keeps the one `congrArg` under the outer functor at
variables; see this module's implementation notes. Nothing is assumed. -/
theorem restrictCompSectionsIso_hom_app_naturality_of_eq {N N' : Y.Modules}
    {A B : (V : Scheme).Modules} (κ : (moduleRestriction Y.toSheafedSpace V).obj N ⟶ A)
    (ψ : A ⟶ B) (κ' : B ⟶ (moduleRestriction Y.toSheafedSpace V).obj N') (φ : N ⟶ N')
    (h : κ ≫ ψ ≫ κ' = (moduleRestriction Y.toSheafedSpace V).map φ) :
    (openSubschemeTopSections V).map κ ≫ (openSubschemeTopSections V).map ψ ≫
        (openSubschemeTopSections V).map κ' ≫ (restrictCompSectionsIso (Y := Y) V).hom.app N' =
      (restrictCompSectionsIso (Y := Y) V).hom.app N ≫
        (sectionsOverOpen Y.toSheafedSpace V).map φ :=
  have hm : (openSubschemeTopSections V).map κ ≫ (openSubschemeTopSections V).map ψ ≫
      (openSubschemeTopSections V).map κ' =
      (openSubschemeTopSections V).map ((moduleRestriction Y.toSheafedSpace V).map φ) :=
    (comp_congr_right _ ((openSubschemeTopSections V).map_comp ψ κ').symm).trans
      (((openSubschemeTopSections V).map_comp κ (ψ ≫ κ')).symm.trans
        (congrArg (fun t => (openSubschemeTopSections V).map t) h))
  ((Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    (comp_congr_left hm _))).trans
      ((restrictCompSectionsIso (Y := Y) V).hom.naturality φ)

/-- **The ringed-space restriction to `V` acting on a morphism is the scheme one, conjugated by the
two casts.** This is `CategoryTheory.Functor.congr_hom` at
`…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` and nothing else. -/
theorem moduleRestriction_map_eq_restrictFunctor_map {N N' : Y.Modules} (φ : N ⟶ N') :
    (moduleRestriction Y.toRingedSpace V).map φ =
      eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V N) ≫
        (Scheme.Modules.restrictFunctor V.ι).map φ ≫
          eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V N').symm :=
  Functor.congr_hom (restrictFunctor_eq_moduleRestriction Y V).symm φ

/-- **The second cast of the scheme-level [Stacks, Tag 01E5], at a module.** The transport along
`…SchemeHigherDirectImage.higherDirectImageRestrictIso_target` inverted, read at `M`, is the
module-level cast `…TopDegreeBaseChange.moduleRestriction_obj_eq_restrictFunctor_obj` at the
degree-`p` higher direct image: the two `eqToHom`s are the same term, the two equalities being the
same proposition up to unfolding `CategoryTheory.Functor.comp`. -/
theorem eqToIso_higherDirectImageRestrictIso_target_hom_app (M : X.Modules) :
    (eqToIso (higherDirectImageRestrictIso_target f V p).symm).hom.app M =
      eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V
        (((Scheme.Modules.pushforward f).rightDerived p).obj M)) :=
  (congrArg (fun t => NatTrans.app t M)
      (eqToIso.hom (higherDirectImageRestrictIso_target f V p).symm)).trans
    (eqToHom_app (higherDirectImageRestrictIso_target f V p).symm M)

/-- **The naturality step's hypothesis, at the comparison of the two indexings at `f`.** The second
cast of the scheme-level [Stacks, Tag 01E5], then the scheme-level restriction to `V` of the
comparison of the two indexings, then the cast back, is the **ringed-space** restriction to `V` of
that comparison. Nothing is assumed. -/
theorem higherDirectImageRestrictIso_target_app_comp_restrictFunctor_map (M : X.Modules) :
    (eqToIso (higherDirectImageRestrictIso_target f V p).symm).hom.app M ≫
        (Scheme.Modules.restrictFunctor V.ι).map
            ((Stacks.DerivedIndexing.rightDerivedIso
              (Scheme.Modules.pushforward f) p).hom.app M) ≫
          eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V
            (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M)).symm =
      (moduleRestriction Y.toSheafedSpace V).map
        ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) p).hom.app M) :=
  (comp_congr_left (eqToIso_higherDirectImageRestrictIso_target_hom_app f V p M) _).trans
    (moduleRestriction_map_eq_restrictFunctor_map V
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) p).hom.app M)).symm

/-- **The naturality step, at the three factors the match carries after the ringed-space 01E5.**
The second cast of the scheme-level [Stacks, Tag 01E5], the scheme-level restriction to `V` of the
comparison of the two indexings at `f`, and the cast back, all read under the `ψ` side's outer
functor and followed by `…TopDegreeBaseChange.restrictCompSectionsIso`, are
`restrictCompSectionsIso` at the degree-`p` higher direct image followed by the sections over `V`
of the comparison of the two indexings.

This is `restrictCompSectionsIso_hom_app_naturality_of_eq` at those morphisms. It is declared, and
not written inline where the identification consumes it, because the unifier then has to solve for
the lemma's six implicit arguments at the same time as the gluing's nine, which is a kernel timeout;
with the instantiation named, both check in seconds. Nothing is assumed. -/
theorem restrictCompSectionsIso_hom_app_naturality_rightDerivedIso (M : X.Modules) :
    (openSubschemeTopSections V).map
          ((eqToIso (higherDirectImageRestrictIso_target f V p).symm).hom.app M) ≫
        (openSubschemeTopSections V).map
            ((Scheme.Modules.restrictFunctor V.ι).map
              ((Stacks.DerivedIndexing.rightDerivedIso
                (Scheme.Modules.pushforward f) p).hom.app M)) ≫
          (openSubschemeTopSections V).map
              (eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V
                (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M)).symm) ≫
            (restrictCompSectionsIso V).hom.app
              (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M) =
      (restrictCompSectionsIso V).hom.app
          (((Scheme.Modules.pushforward f).rightDerived p).obj M) ≫
        (sectionsOverOpen Y.toSheafedSpace V).map
          ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) p).hom.app M) :=
  restrictCompSectionsIso_hom_app_naturality_of_eq V _ _ _ _
    (higherDirectImageRestrictIso_target_app_comp_restrictFunctor_map f V p M)

/-! ### The scheme-level 01E5 split under the outer functor -/

/-- **The cast entry of the match, whiskered by the `ψ` side's outer functor.** The scheme-level
[Stacks, Tag 01E5] read under `…TopDegreeBaseChange.openSubschemeTopSections V` is the ringed-space
comparison read under it, conjugated by the two casts read under it.

This is `…TopDegreeBaseChange.higherDirectImageRestrictIso_hom_eq` whiskered, and it is performed
at the level of natural transformations because no module-level route to it is affordable; see this
module's implementation notes. -/
theorem whiskerRight_higherDirectImageRestrictIso_hom_eq :
    Functor.whiskerRight (SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom
        (openSubschemeTopSections V) =
      Functor.whiskerRight (eqToIso (higherDirectImageRestrictIso_source f V p)).hom
          (openSubschemeTopSections V) ≫
        Functor.whiskerRight (Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
            f.toLRSHom.toShHom V p).hom (openSubschemeTopSections V) ≫
          Functor.whiskerRight (eqToIso (higherDirectImageRestrictIso_target f V p).symm).hom
            (openSubschemeTopSections V) :=
  (congrArg (fun α => Functor.whiskerRight α (openSubschemeTopSections V))
        (higherDirectImageRestrictIso_hom_eq f V p)).trans
    ((Functor.whiskerRight_comp _ _ _).trans
      (comp_congr_right _ (Functor.whiskerRight_comp _ _ _)))

/-- **The same read at a module**: the three factors of the previous lemma at `M`, which is where
the identification consumes them. The component of a whiskering is the functor's image of the
component, so nothing is identified underneath the outer functor here. -/
theorem openSubschemeTopSections_map_higherDirectImageRestrictIso_hom_app (M : X.Modules) :
    (openSubschemeTopSections V).map
        ((SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom.app M) =
      (openSubschemeTopSections V).map
          ((eqToIso (higherDirectImageRestrictIso_source f V p)).hom.app M) ≫
        (openSubschemeTopSections V).map
            ((Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
              f.toLRSHom.toShHom V p).hom.app M) ≫
          (openSubschemeTopSections V).map
            ((eqToIso (higherDirectImageRestrictIso_target f V p).symm).hom.app M) :=
  (congrArg (fun α => NatTrans.app α M)
        (whiskerRight_higherDirectImageRestrictIso_hom_eq f V p)).trans
    ((NatTrans.comp_app _ _ _).trans
      (comp_congr_right _ (NatTrans.comp_app _ _ _)))

/-! ### The identification the join is made of -/

/-- **The crossing's leading factors against the match's trailing factors.** The source cast of the
scheme-level [Stacks, Tag 01E5] and the **ringed-space** 01E5 — both read under the `ψ` side's
outer functor `…TopDegreeBaseChange.openSubschemeTopSections V` — then
`…TopDegreeBaseChange.restrictCompSectionsIso` at the degree-`p` higher direct image and the
sections over `V` of the comparison of the two indexings at `f`, are the **scheme-level** 01E5 read
under the outer functor followed by the three factors
`…rightDerivedPlusRestrictSectionsIso_hom_eq_restrictCompSectionsIso` carries after it.

The second and third factors on the left are exactly the two that the right-hand side of
`…TopDegreeBaseChange.collapse_crossing_restrictedMorphism` begins with, so this is the
identification the join of conclusion (c) of [Stacks, Tag 0EX3] is made of. **The orientation is
not cosmetic**: written the other way round the same term is a kernel timeout; see
this module's implementation notes, and `schemeHigherDirectImageRestrictIso_hom_app_comp_tail_eq`
for the other orientation. Nothing is assumed of `f`, of `V`, of `M` or of `p`. -/
theorem higherDirectImageRestrictIso_hom_app_comp_restrictCompSectionsIso_eq (M : X.Modules) :
    (openSubschemeTopSections V).map
          ((eqToIso (higherDirectImageRestrictIso_source f V p)).hom.app M) ≫
        (openSubschemeTopSections V).map
            ((Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
              f.toLRSHom.toShHom V p).hom.app M) ≫
          (restrictCompSectionsIso V).hom.app
              (((Scheme.Modules.pushforward f).rightDerived p).obj M) ≫
            (sectionsOverOpen Y.toSheafedSpace V).map
              ((Stacks.DerivedIndexing.rightDerivedIso
                (Scheme.Modules.pushforward f) p).hom.app M) =
      (openSubschemeTopSections V).map
          ((SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom.app M) ≫
        (openSubschemeTopSections V).map
            ((Scheme.Modules.restrictFunctor V.ι).map
              ((Stacks.DerivedIndexing.rightDerivedIso
                (Scheme.Modules.pushforward f) p).hom.app M)) ≫
          (openSubschemeTopSections V).map
              (eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V
                (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M)).symm) ≫
            (restrictCompSectionsIso V).hom.app
              (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M) :=
  (comp₄_split_head_absorb
    (openSubschemeTopSections_map_higherDirectImageRestrictIso_hom_app f V p M)
    (restrictCompSectionsIso_hom_app_naturality_rightDerivedIso f V p M)).symm

/-- **The same identification with the match's factors first**, which is the orientation a chase
starting from `…rightDerivedPlusRestrictSectionsIso_hom_eq_restrictCompSectionsIso` meets it in.

It is `higherDirectImageRestrictIso_hom_app_comp_restrictCompSectionsIso_eq` inverted, and it is
**declared** rather than taken with `Eq.symm` at the point of use: the orientation crossing is
affordable in a declaration of its own and is a kernel timeout inside a larger term. -/
theorem schemeHigherDirectImageRestrictIso_hom_app_comp_tail_eq (M : X.Modules) :
    (openSubschemeTopSections V).map
          ((SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom.app M) ≫
        (openSubschemeTopSections V).map
            ((Scheme.Modules.restrictFunctor V.ι).map
              ((Stacks.DerivedIndexing.rightDerivedIso
                (Scheme.Modules.pushforward f) p).hom.app M)) ≫
          (openSubschemeTopSections V).map
              (eqToHom (moduleRestriction_obj_eq_restrictFunctor_obj V
                (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M)).symm) ≫
            (restrictCompSectionsIso V).hom.app
              (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj M) =
      (openSubschemeTopSections V).map
          ((eqToIso (higherDirectImageRestrictIso_source f V p)).hom.app M) ≫
        (openSubschemeTopSections V).map
            ((Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
              f.toLRSHom.toShHom V p).hom.app M) ≫
          (restrictCompSectionsIso V).hom.app
              (((Scheme.Modules.pushforward f).rightDerived p).obj M) ≫
            (sectionsOverOpen Y.toSheafedSpace V).map
              ((Stacks.DerivedIndexing.rightDerivedIso
                (Scheme.Modules.pushforward f) p).hom.app M) :=
  (higherDirectImageRestrictIso_hom_app_comp_restrictCompSectionsIso_eq f V p M).symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
