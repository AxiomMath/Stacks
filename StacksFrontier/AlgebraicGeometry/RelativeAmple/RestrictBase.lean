module

public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 01VJ, clause (2): relative ampleness over an arbitrary open covering of the base

Let `f : X ⟶ S` be a quasi-compact morphism of schemes and `L` an invertible `𝒪_X`-module.
Clause (2) of [Stacks, Tag 01VJ] is the condition

> there is an open covering `S = ⋃ V_i` such that `L|_{f⁻¹V_i}` is ample relative to the
> restricted morphism `f⁻¹V_i ⟶ V_i`,

and this file proves that it is equivalent to clause (1), relative ampleness of `L` for `f`
itself. The members `V_i` are arbitrary opens of `S`, not affine ones, and the condition over
each of them is *relative* ampleness, not absolute ampleness — that is what separates clause (2)
from clause (3), which is already proved in
`StacksFrontier/AlgebraicGeometry/RelativeAmple/LocalOnBase.lean`.

## Main results

* `Stacks.RelativeAmpleRestrictBase.isRelativelyAmple_morphismRestrict`:
  **Tag 01VJ, (1) implies (2)** — a relatively ample module stays relatively ample after the base
  is restricted to an arbitrary open, so the one-member covering `{S}` (indeed every open
  covering) witnesses clause (2). This also fills the gap recorded in
  `StacksFrontier/AlgebraicGeometry/RelativeAmpleComposition/Basic.lean` under
  "`Stacks.RelativeAmple.IsRelativelyAmple` is not shown to restrict to an open of the base".
* `Stacks.RelativeAmpleRestrictBase.isRelativelyAmple_of_forall_exists_isRelativelyAmple`:
  **Tag 01VJ, (2) implies (1)**.
* `Stacks.RelativeAmpleRestrictBase.isRelativelyAmple_iff_exists_isRelativelyAmple_cover`: the
  resulting equivalence of clauses (1) and (2).

## The route

No relative `Proj` and no new ampleness input: clause (2) is reduced to the already-proved
equivalence of clauses (1) and (3) by a comparison of open subschemes.

The whole content is the *bridge*
`Stacks.RelativeAmpleRestrictBase.isAmple_preimage_morphismRestrict_iff`. For an open
`A ⊆ V` of the open subscheme `V` of `S`, the two schemes

* `(f ∣_ V)⁻¹A`, an open subscheme of the open subscheme `f⁻¹V` of `X`, carrying the restriction
  of `L|_{f⁻¹V}`, and
* `f⁻¹W` for `W = V.ι ''ᵁ A` the same open seen inside `S`, carrying the restriction of `L`,

are two open subschemes of `X` with the same underlying open, so ampleness on one is ampleness
on the other. Pseudofunctoriality of the module pullback
(`Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso`) turns the iterated restriction into a
single restriction along `((f ∣_ V)⁻¹A).ι ≫ (f⁻¹V).ι`, and that morphism has the same range as
`(f⁻¹W).ι`: the identity `(f⁻¹V).ι⁻¹(f⁻¹W) = (f ∣_ V)⁻¹(V.ι⁻¹W)` is
`AlgebraicGeometry.morphismRestrict_ι` read through
`AlgebraicGeometry.Scheme.Hom.comp_preimage`, and `f⁻¹W ≤ f⁻¹V` because `W ≤ V`.

Given the bridge, both implications are short.

* **(1) ⟹ (2).** Quasi-compactness is local on the target, so `f ∣_ V` is quasi-compact. An
  affine open `A` of `V` has affine image `W = V.ι ''ᵁ A` in `S`, where clause (1) supplies
  ampleness of `L|_{f⁻¹W}`; the bridge moves it onto `(f ∣_ V)⁻¹A`.
* **(2) ⟹ (1).** Given `x ∈ S`, choose a member `V` of the covering around `x` and then, the
  affine opens being a basis, an affine open `W` with `x ∈ W ⊆ V`. Then `V.ι⁻¹W` is an affine
  open of `V`, relative ampleness over `V` gives ampleness on `(f ∣_ V)⁻¹(V.ι⁻¹W)`, and the
  bridge turns it into ampleness of `L|_{f⁻¹W}`. That is exactly the affine covering that
  `Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple` — clause (3)
  implies clause (1) — consumes.

## Implementation notes

**Comparing two open subschemes with the same image.** `AlgebraicGeometry.Scheme.Opens.toScheme`
produces a *different* scheme for each open, so the comparison is an isomorphism and not an
equality: `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` builds it from the equality of ranges
and `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac` records that it commutes with the
two immersions into `X`. Ampleness crosses it by
`Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso`.
`Stacks.RelativeAmpleRestrictBase.isAmple_pullbackModule_congr_range` packages the two
directions.

**Why the hypothesis `QuasiCompact f` is kept.** It is a standing hypothesis of
[Stacks, Tag 01VJ] and of the definition [Stacks, Tag 01VH], and it is the first conjunct of
`Stacks.RelativeAmple.IsRelativelyAmple`; the proof that clause (3) implies clause (1) asks for it
too. Nothing else is assumed: the covering hypothesis of clause (2) is the clause itself.

## What is not done

Clauses (4) and (6) of [Stacks, Tag 01VJ] remain unstated — they speak about the relative `Proj`
of a quasi-coherent graded algebra, which this repository does not construct — and clause (5) is
only partly proved; see
`StacksFrontier/AlgebraicGeometry/RelativeAmple/GradedDirectImage.lean` for the four named
obstructions there.

Two notes in other files are superseded by this file for clause (2) only: the
"What is not done" paragraph of `StacksFrontier/AlgebraicGeometry/RelativeAmple/LocalOnBase.lean`,
which lists clause (2) as unproved and names its missing ingredient as relative ampleness of a
restricted morphism, and the closing paragraph of
`StacksFrontier/AlgebraicGeometry/RelativeAmpleComposition/Basic.lean`, which records that
`Stacks.RelativeAmple.IsRelativelyAmple` is not shown to restrict to an open of the base. The
rest of both paragraphs stands: in particular the Beck–Chevalley comparison that Stacks Tag 0C4K
needs over a general base — the identification of the restriction of `L ⊗ f^* M ^⊗ a` with
`L| ⊗ (f|)^* (M|) ^⊗ a` — is a statement about a *tensor-and-pullback* module and is untouched
here, where the module is `L` itself.

## References

* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [EGA II, Proposition 4.6.3]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.RelativeAmpleBaseChange (pullbackModuleCompIso pullbackModuleCongr)

universe u

namespace Stacks.RelativeAmpleRestrictBase

/-! ### Ampleness on an open subscheme depends only on the open -/

/-- **An iterated restriction of a module is a restriction along the composite.** Ampleness of
the pullback of `L` along `a ≫ b` is ampleness of the pullback along `a` of the pullback along
`b`, by pseudofunctoriality of the module pullback
(`Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso`). -/
theorem isAmple_pullbackModule_comp_iff {A B X : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ X)
    (L : X.Modules) [IsInvertibleModule X L] :
    IsAmple A (pullbackModule a (pullbackModule b L)) ↔ IsAmple A (pullbackModule (a ≫ b) L) :=
  Stacks.RelativeVeryAmple.isAmple_congr _ _ (pullbackModuleCompIso a b L).symm

/-- **Two open immersions with the same range restrict `L` to the same ampleness condition.**
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` identifies the two sources, and
`Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso` carries ampleness along it. -/
theorem isAmple_pullbackModule_of_range_eq {X A B : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] (hr : Set.range a.base = Set.range b.base)
    (L : X.Modules) [IsInvertibleModule X L] (h : IsAmple A (pullbackModule a L)) :
    IsAmple B (pullbackModule b L) := by
  have key := (isAmple_pullbackModule_comp_iff _ a L).mp
    (Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso
      (IsOpenImmersion.isoOfRangeEq b a hr.symm).hom (pullbackModule a L) h)
  rwa [IsOpenImmersion.isoOfRangeEq_hom_fac] at key

/-- **Ampleness of a restriction of `L` depends only on the range of the open immersion.** The
symmetric form of `Stacks.RelativeAmpleRestrictBase.isAmple_pullbackModule_of_range_eq`. -/
theorem isAmple_pullbackModule_congr_range {X A B : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] (hr : Set.range a.base = Set.range b.base)
    (L : X.Modules) [IsInvertibleModule X L] :
    IsAmple A (pullbackModule a L) ↔ IsAmple B (pullbackModule b L) :=
  ⟨isAmple_pullbackModule_of_range_eq a b hr L,
    isAmple_pullbackModule_of_range_eq b a hr.symm L⟩

/-! ### The bridge between the restricted morphism and the morphism itself -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]

/-- **The preimage under the restricted morphism, seen inside `X`.** For an open `A` of the open
subscheme `V` of `S`, the preimage of `A` under `f ∣_ V` is the part of `f⁻¹(V.ι ''ᵁ A)` lying in
`f⁻¹V`. This is `AlgebraicGeometry.morphismRestrict_ι` read through
`AlgebraicGeometry.Scheme.Hom.comp_preimage`. -/
theorem preimage_morphismRestrict_eq {V : S.Opens} (A : V.toScheme.Opens) :
    (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ (V.ι ''ᵁ A)) = (f ∣_ V) ⁻¹ᵁ A := by
  have h : (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ (V.ι ''ᵁ A)) = (f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ (V.ι ''ᵁ A)) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  rw [h]
  simp

/-- **The preimage under the restricted morphism, as an open of `X`.** Its image under the open
immersion of `f⁻¹V` is `f⁻¹(V.ι ''ᵁ A)` on the nose, because that open already lies inside
`f⁻¹V`. -/
theorem image_preimage_morphismRestrict {V : S.Opens} (A : V.toScheme.Opens) :
    (f ⁻¹ᵁ V).ι ''ᵁ ((f ∣_ V) ⁻¹ᵁ A) = f ⁻¹ᵁ (V.ι ''ᵁ A) := by
  exact image_morphismRestrict_preimage f V A

/-- **The bridge of clause (2) of [Stacks, Tag 01VJ].** For an open `A` of an open subscheme `V`
of the base, ampleness of the restriction of `L|_{f⁻¹V}` to the preimage of `A` under the
restricted morphism `f ∣_ V` is the same condition as ampleness of the restriction of `L` to
`f⁻¹W`, where `W = V.ι ''ᵁ A` is `A` seen as an open of `S`.

Both sides are ampleness of a restriction of `L` along an open immersion into `X`, and the two
immersions have the same range by
`Stacks.RelativeAmpleRestrictBase.image_preimage_morphismRestrict`. -/
theorem isAmple_preimage_morphismRestrict_iff {V : S.Opens} (A : V.toScheme.Opens) :
    IsAmple ((f ∣_ V) ⁻¹ᵁ A).toScheme
        (pullbackModule ((f ∣_ V) ⁻¹ᵁ A).ι (pullbackModule (f ⁻¹ᵁ V).ι L)) ↔
      IsAmple (f ⁻¹ᵁ (V.ι ''ᵁ A)).toScheme (pullbackModule (f ⁻¹ᵁ (V.ι ''ᵁ A)).ι L) := by
  refine Iff.trans (isAmple_pullbackModule_comp_iff ((f ∣_ V) ⁻¹ᵁ A).ι (f ⁻¹ᵁ V).ι L) ?_
  refine isAmple_pullbackModule_congr_range _ _ ?_ L
  have himg : ((((f ⁻¹ᵁ V).ι ''ᵁ ((f ∣_ V) ⁻¹ᵁ A) : X.Opens)) : Set X)
      = ((f ⁻¹ᵁ (V.ι ''ᵁ A) : X.Opens) : Set X) :=
    congrArg _ (image_preimage_morphismRestrict f A)
  rw [Scheme.Opens.range_ι, ← himg]
  simp [Set.range_comp, Scheme.Opens.range_ι]

/-! ### Stacks Tag 01VJ, clause (2) -/

/-- **Stacks Tag 01VJ, clause (1) implies clause (2).** If `L` is ample relative to `f : X ⟶ S`
then, for *every* open `V ⊆ S`, the restriction `L|_{f⁻¹V}` is ample relative to the restricted
morphism `f ∣_ V : f⁻¹V ⟶ V`. In particular every open covering of `S` — for instance the
one-member covering `{S}` — witnesses clause (2) of [Stacks, Tag 01VJ].

Quasi-compactness of `f ∣_ V` holds because quasi-compactness of a morphism is local on the
target. For an affine open `A ⊆ V` the image `W = V.ι ''ᵁ A` is an affine open of `S`, where
clause (1) gives ampleness of `L|_{f⁻¹W}`, and
`Stacks.RelativeAmpleRestrictBase.isAmple_preimage_morphismRestrict_iff` moves it onto
`(f ∣_ V)⁻¹A`.

This also records that `Stacks.RelativeAmple.IsRelativelyAmple` restricts to an open of the
base. -/
@[stacks 01VJ "(1) implies (2): relative ampleness is inherited by the restriction of the \
morphism over an arbitrary open of the base, so every open covering witnesses clause (2)",
  ega "II 4.6.4" "Necessity"]
theorem isRelativelyAmple_morphismRestrict
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (V : S.Opens) :
    Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L) := by
  have hf : QuasiCompact f := hL.1
  refine ⟨inferInstance, fun A hA => ?_⟩
  refine (isAmple_preimage_morphismRestrict_iff f L A).mpr ?_
  exact hL.2 (V.ι ''ᵁ A) ((V.ι.isAffineOpen_iff_of_isOpenImmersion).mpr hA)

/-- **Stacks Tag 01VJ, clause (2) implies clause (1).** Let `f : X ⟶ S` be quasi-compact and `L`
invertible. If every point of `S` has an open neighbourhood `V` such that `L|_{f⁻¹V}` is ample
relative to `f ∣_ V : f⁻¹V ⟶ V`, then `L` is ample relative to `f`.

The affine opens of `S` are a basis, so each `V` contains an affine open `W` around the given
point, and `V.ι⁻¹W` is then an affine open of `V`. Relative ampleness over `V` gives ampleness
on `(f ∣_ V)⁻¹(V.ι⁻¹W)`, which
`Stacks.RelativeAmpleRestrictBase.isAmple_preimage_morphismRestrict_iff` turns into ampleness of
`L|_{f⁻¹W}`. That is an affine open covering of the kind
`Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple` — clause (3) implies
clause (1) — consumes. -/
@[stacks 01VJ "(2) implies (1): relative ampleness over the members of an arbitrary open \
covering of the base implies relative ampleness"]
theorem isRelativelyAmple_of_forall_exists_isRelativelyAmple (hf : QuasiCompact f)
    (hcov : ∀ x : S, ∃ V : S.Opens, x ∈ V ∧ Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V)
      (pullbackModule (f ⁻¹ᵁ V).ι L)) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L hf
    fun x => ?_
  obtain ⟨V, hxV, hV⟩ := hcov x
  obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hWV' : W ≤ V := hWV
  have himg : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hWV'
  have hAaff : IsAffineOpen (V.ι ⁻¹ᵁ W) := by
    refine (V.ι.isAffineOpen_iff_of_isOpenImmersion).mp ?_
    rw [himg]
    exact hW
  refine ⟨W, hW, hxW, ?_⟩
  have key := (isAmple_preimage_morphismRestrict_iff f L (V.ι ⁻¹ᵁ W)).mp
    (hV.2 (V.ι ⁻¹ᵁ W) hAaff)
  rwa [himg] at key

/-- **Stacks Tag 01VJ, clause (1) if and only if clause (2).** For a quasi-compact `f`, relative
ampleness of `L` is equivalent to the existence of an open covering of the base over whose
members the restriction of `L` is relatively ample. -/
theorem isRelativelyAmple_iff_exists_isRelativelyAmple_cover (hf : QuasiCompact f) :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔
      ∀ x : S, ∃ V : S.Opens, x ∈ V ∧ Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V)
        (pullbackModule (f ⁻¹ᵁ V).ι L) :=
  ⟨fun hL _ => ⟨⊤, trivial, isRelativelyAmple_morphismRestrict f L hL ⊤⟩,
    isRelativelyAmple_of_forall_exists_isRelativelyAmple f L hf⟩

end Stacks.RelativeAmpleRestrictBase

end
