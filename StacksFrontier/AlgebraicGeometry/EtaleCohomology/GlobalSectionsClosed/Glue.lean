module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Shrink

/-!
# Gluing a compatible family of étale-local sections over a covering of the base

Let `i : Z ⟶ X` be a morphism of schemes and `F` a sheaf of sets on the small étale site of `X`.
`Stacks.EtaleCohomology.exists_smallEtaleCover_sectionPullback_of_inverseImageSection` presents a
global section `t` of `i^{-1}F` by a family of objects `W j` of the small étale site of `X` whose
images cover `X`, together with sections `s j` of `F` over `W j` whose pullbacks `i⁻¹(s j)` are the
restrictions of `t`. What it does *not* say is that the `s j` agree with each other.

This file supplies the step that follows once they do. A family of objects of the small étale site
of `X` whose images cover `X` generates a covering sieve of the final object, so a family of
sections over them which is compatible on the pairwise fibre products has a unique amalgamation:
a global section `a` of `F` restricting to `s j` over each `W j`. The base changes `W j ×_X Z` then
cover `Z`, and the restriction of `i⁻¹a` to `W j ×_X Z` is `i⁻¹(s j)`, which is the restriction of
`t`; separatedness of `i^{-1}F` for that covering gives `i⁻¹a = t`.

So the surjectivity half of [Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF) comes
down to *compatibility*: every global section of `i^{-1}F` must admit a presenting family whose
sections agree on the pairwise fibre products. That is a hypothesis about the family, not a
restatement of the conclusion, and it is exactly what the source obtains — not on `X`, where it can
fail, but after passing to a finite surjective `X' → X` which Zariski-locally factors through the
family ([Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0)) and descending again
([Stacks, Tag 09Z3](https://stacks.math.columbia.edu/tag/09Z3)); see the implementation notes.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleCompatible` — a family of sections over objects of the small
  étale site of `X` is compatible when any two of them agree on the fibre product of their domains.
* `Stacks.EtaleCohomology.smallEtalePairLift` — the morphism into a fibre product of the small
  étale site determined by two morphisms out of a common object.

## Main results

* `Stacks.EtaleCohomology.isIso_terminalEtale_hom` and
  `Stacks.EtaleCohomology.injective_terminalEtale_hom` — the structure morphism of the final object
  of a small étale site is an isomorphism.
* `Stacks.EtaleCohomology.ofArrows_terminalFrom_mem_smallEtaleTopology` — a family of objects of
  the small étale site of `X` whose images cover `X` generates a covering sieve of the final
  object.
* `Stacks.EtaleCohomology.ofArrows_smallEtaleBaseChange_mem_smallEtaleTopology` — the base changes
  along `i` of such a family generate a covering sieve of the final object of the site of `Z`.
* `Stacks.EtaleCohomology.smallEtaleCompatible_map_terminalFrom` — the restrictions of a single
  global section form a compatible family.
* `Stacks.EtaleCohomology.eq_map_of_smallEtaleCompatible` — a compatible family agrees after
  restriction along any two morphisms out of a common object.
* `Stacks.EtaleCohomology.exists_globalSection_map_terminalFrom_eq` — a compatible family of
  sections over a covering family of objects glues to a global section.
* `Stacks.EtaleCohomology.map_terminalFrom_smallEtaleGlobalSectionPullback` — the pullback of a
  global section restricts, over the base change of `W`, to the pullback of its restriction to `W`.
* `Stacks.EtaleCohomology.exists_smallEtaleGlobalSectionPullback_eq_of_compatible` — a compatible
  presenting family for `t` exhibits `t` as the pullback of a global section.
* `Stacks.EtaleCohomology.surjective_smallEtaleGlobalSectionPullback_of_exists_compatible` and
  `Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImageComparison_of_compatible` —
  the bijectivity half of Tag 09ZF, reduced to the existence of compatible presenting families.
* `Stacks.EtaleCohomology.surjective_smallEtaleGlobalSectionPullback_of_compatible_cover` — for a
  closed immersion satisfying hypothesis (1) of the tag, surjectivity follows once every family
  presenting a global section of `i^{-1}F` is compatible.

## Implementation notes

Families of elements for a presieve of the shape `CategoryTheory.Presieve.ofArrows` cannot be
defined by pattern matching: that presieve is an inductive *proposition*, so it admits no large
elimination. The family below is therefore built on the generated sieve, using
`CategoryTheory.Sieve.ofArrows.i` and `CategoryTheory.Sieve.ofArrows.h`, whose choice of
factorization is irrelevant precisely because the family is compatible.

Compatibility in the sense of `CategoryTheory.Presieve.FamilyOfElements.Compatible` quantifies over
*all* pairs of morphisms out of a common object, not only over the fibre products; the two agree
here because the fibre product of two objects of the small étale site receives a morphism from any
object mapping to both, namely `Stacks.EtaleCohomology.smallEtalePairLift`. The condition
`g₁ ≫ f₁ = g₂ ≫ f₂` of that definition is vacuous for the sieve used here, the arrows all having
the final object as codomain.

What is *not* proved, and is not provable from the hypotheses of Tag 09ZF on `X` alone, is that the
family produced by
`Stacks.EtaleCohomology.exists_smallEtaleCover_sectionPullback_of_inverseImageSection` is
compatible. Agreement of `s j` and `s j'` on `W j ×_X W j'` would follow from injectivity of
restriction to `(W j ×_X W j') ×_X Z`, and that needs hypothesis (1) of the tag for the *étale*
scheme `W j ×_X W j'`, which hypothesis (2) — a statement about *finite* morphisms — does not
supply. This is the reason the source refines the étale covering by a finite surjective one before
comparing sections, and it is why the two external results cited in the module docstring are
unavoidable there.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe u v w

namespace Stacks.EtaleCohomology

section Terminal

/-- **The final object of a small étale site is the base.** Its structure morphism is an
isomorphism: the final object is isomorphic to the base with its identity morphism, and the
isomorphism is carried to the structure morphism by the forgetful functor. -/
public theorem isIso_terminalEtale_hom (S : Scheme.{u}) :
    IsIso ((terminal S.Etale).hom : (terminal S.Etale).left ⟶ S) := by
  have : IsIso ((Scheme.Etale.mk (𝟙 S)).hom : S ⟶ S) := inferInstanceAs (IsIso (𝟙 S))
  let e : terminal S.Etale ≅ Scheme.Etale.mk (𝟙 S) :=
    terminalIsTerminal.uniqueUpToIso (isTerminalOfIsIsoHom _)
  have hw : e.hom.left ≫ ((Scheme.Etale.mk (𝟙 S)).hom : S ⟶ S) =
      ((terminal S.Etale).hom : (terminal S.Etale).left ⟶ S) :=
    MorphismProperty.Over.w e.hom
  have heq : ((terminal S.Etale).hom : (terminal S.Etale).left ⟶ S) = e.hom.left := by
    rw [← hw]
    exact Category.comp_id _
  rw [heq]
  exact inferInstanceAs (IsIso ((Scheme.Etale.forget S ⋙ CategoryTheory.Over.forget S).map e.hom))

/-- The underlying map of the structure morphism of the final object of a small étale site is
injective, being the map of an isomorphism of schemes. -/
public theorem injective_terminalEtale_hom (S : Scheme.{u}) :
    Function.Injective ((terminal S.Etale).hom : (terminal S.Etale).left ⟶ S).base := by
  have := isIso_terminalEtale_hom S
  exact (Scheme.Hom.homeomorph
    ((terminal S.Etale).hom : (terminal S.Etale).left ⟶ S)).injective

/-- A point of an object `V` of a small étale site lying over `y` is carried to `y` by the map to
the final object, since the structure morphism of the final object is injective. -/
private theorem terminalFrom_left_base_eq_of_hom_base_eq {S : Scheme.{u}} (V : S.Etale)
    (y : (terminal S.Etale).left) (c : V.left)
    (hc : (V.hom : V.left ⟶ S).base c =
      ((terminal S.Etale).hom : (terminal S.Etale).left ⟶ S).base y) :
    (terminal.from V).left.base c = y := by
  refine injective_terminalEtale_hom S ?_
  have hw : (terminal.from V).left ≫ ((terminal S.Etale).hom : (terminal S.Etale).left ⟶ S) =
      (V.hom : V.left ⟶ S) := MorphismProperty.Over.w (terminal.from V)
  exact ((Scheme.Hom.comp_apply _ _ c).symm.trans
    (congrArg (fun f : V.left ⟶ S ↦ f.base c) hw)).trans hc

variable {X : Scheme.{u}}

/-- **A family covering `X` covers the final object.** If the images in `X` of a family of objects
of the small étale site of `X` cover `X`, then the morphisms from those objects to the final object
of the site generate a covering sieve.

A point of the final object is carried by its structure morphism — an isomorphism — to a point of
`X`, which is hit by one member of the family; the morphism of the site over that member then hits
the original point, because the structure morphism is injective. -/
public theorem ofArrows_terminalFrom_mem_smallEtaleTopology {α : Type*} (W : α → X.Etale)
    (hcov : (⨆ j, smallEtaleImage (W j)) = ⊤) :
    Sieve.ofArrows W (fun j ↦ terminal.from (W j)) ∈
      Scheme.smallEtaleTopology X (terminal X.Etale) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext y
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  have hx : ((terminal X.Etale).hom : (terminal X.Etale).left ⟶ X).base y ∈
      (⨆ j, smallEtaleImage (W j) : X.Opens) := by
    rw [hcov]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  obtain ⟨c, hc⟩ := (mem_smallEtaleImage_iff (W j) _).mp hj
  exact ⟨j, c, terminalFrom_left_base_eq_of_hom_base_eq _ _ c hc⟩

variable {Z : Scheme.{u}} (i : Z ⟶ X)

/-- **The base change of a family covering `X` covers the final object of the site of `Z`.** The
base change along `i` of a family of objects of the small étale site of `X` whose images cover `X`
generates a covering sieve of the final object of the small étale site of `Z`.

A point of `Z` is carried by `i` into the image of some member of the family, so it lies in the
image of the base change of that member by
`AlgebraicGeometry.Scheme.Pullback.range_snd`. -/
public theorem ofArrows_smallEtaleBaseChange_mem_smallEtaleTopology {α : Type*}
    (W : α → X.Etale) (hcov : (⨆ j, smallEtaleImage (W j)) = ⊤) :
    Sieve.ofArrows (fun j ↦ (smallEtaleBaseChange i).obj (W j))
        (fun j ↦ terminal.from ((smallEtaleBaseChange i).obj (W j))) ∈
      Scheme.smallEtaleTopology Z (terminal Z.Etale) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext y
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  set z := ((terminal Z.Etale).hom : (terminal Z.Etale).left ⟶ Z).base y
  have hx : i.base z ∈ (⨆ j, smallEtaleImage (W j) : X.Opens) := by
    rw [hcov]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  obtain ⟨c, hc⟩ : z ∈ Set.range (pullback.snd ((W j).hom : (W j).left ⟶ X) i).base := by
    rw [Scheme.Pullback.range_snd]
    exact (mem_smallEtaleImage_iff (W j) _).mp hj
  exact ⟨j, c, terminalFrom_left_base_eq_of_hom_base_eq ((smallEtaleBaseChange i).obj (W j)) _ c hc⟩

end Terminal

section Lift

variable {X : Scheme.{u}}

/-- The morphism into the fibre product `W ×_X V` of two objects of the small étale site of `X`
determined by two morphisms of the site out of a common object. -/
public def smallEtalePairLift {W V Y : X.Etale} (g₁ : Y ⟶ W) (g₂ : Y ⟶ V) :
    Y ⟶ smallEtalePair W V :=
  MorphismProperty.Over.homMk
    (pullback.lift g₁.left g₂.left
      ((MorphismProperty.Over.w g₁).trans (MorphismProperty.Over.w g₂).symm))
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ((W.hom : W.left ⟶ X))) (pullback.lift_fst _ _ _)).trans
        (MorphismProperty.Over.w g₁)))
    trivial

/-- The first projection of the fibre product, composed with
`Stacks.EtaleCohomology.smallEtalePairLift g₁ g₂`, is `g₁`. -/
@[simp]
public theorem smallEtalePairLift_fst {W V Y : X.Etale} (g₁ : Y ⟶ W) (g₂ : Y ⟶ V) :
    smallEtalePairLift g₁ g₂ ≫ smallEtalePairFst W V = g₁ :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

/-- The second projection of the fibre product, composed with
`Stacks.EtaleCohomology.smallEtalePairLift g₁ g₂`, is `g₂`. -/
@[simp]
public theorem smallEtalePairLift_snd {W V Y : X.Etale} (g₁ : Y ⟶ W) (g₂ : Y ⟶ V) :
    smallEtalePairLift g₁ g₂ ≫ smallEtalePairSnd W V = g₂ :=
  MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)

variable (F : Sheaf (Scheme.smallEtaleTopology X) (Type w))

/-- A family of sections of `F` over objects `W j` of the small étale site of `X` is **compatible**
when, for every two indices, the two restrictions to the fibre product `W j ×_X W j'` agree. This
is the cocycle condition for the family, stated on the fibre products of the site. -/
public def SmallEtaleCompatible {α : Type*} (W : α → X.Etale)
    (s : ∀ j, F.obj.obj (op (W j))) : Prop :=
  ∀ j j', F.obj.map (smallEtalePairFst (W j) (W j')).op (s j)
    = F.obj.map (smallEtalePairSnd (W j) (W j')).op (s j')

/-- The restrictions of a single global section to a family of objects of the small étale site form
a compatible family: the two sides of the condition are restrictions of that section along two
morphisms to the final object, and such a morphism is unique. -/
public theorem smallEtaleCompatible_map_terminalFrom {α : Type*} (W : α → X.Etale)
    (a : F.obj.obj (op (terminal X.Etale))) :
    SmallEtaleCompatible F W fun j ↦ F.obj.map (terminal.from (W j)).op a := by
  intro j j'
  rw [← types_comp_apply (F.obj.map (terminal.from (W j)).op) (F.obj.map _),
    ← types_comp_apply (F.obj.map (terminal.from (W j')).op) (F.obj.map _),
    ← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp,
    Subsingleton.elim (smallEtalePairFst (W j) (W j') ≫ terminal.from (W j))
      (smallEtalePairSnd (W j) (W j') ≫ terminal.from (W j'))]

/-- **A compatible family agrees along arbitrary pairs of morphisms.** For a compatible family of
sections and any two morphisms of the small étale site out of a common object into two members of
the family, the two restrictions agree.

The common object maps to the fibre product of the two members by
`Stacks.EtaleCohomology.smallEtalePairLift`, and the two restrictions are the restrictions along
that morphism of the two sides of the compatibility condition. -/
public theorem eq_map_of_smallEtaleCompatible {α : Type*} {W : α → X.Etale}
    {s : ∀ j, F.obj.obj (op (W j))} (hs : SmallEtaleCompatible F W s)
    {j j' : α} {Y : X.Etale} (g₁ : Y ⟶ W j) (g₂ : Y ⟶ W j') :
    F.obj.map g₁.op (s j) = F.obj.map g₂.op (s j') := by
  have h := congrArg (F.obj.map (smallEtalePairLift g₁ g₂).op) (hs j j')
  rwa [← types_comp_apply (F.obj.map _) (F.obj.map _),
    ← types_comp_apply (F.obj.map (smallEtalePairSnd (W j) (W j')).op) (F.obj.map _),
    ← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp,
    smallEtalePairLift_fst, smallEtalePairLift_snd] at h

/-- **A compatible family over a covering family glues.** Let `W j` be objects of the small étale
site of `X` whose images cover `X` and `s j` a compatible family of sections of `F` over them.
Then there is a global section of `F` — a section over the final object — restricting to `s j` over
each `W j`.

The morphisms from the `W j` to the final object generate a covering sieve by
`Stacks.EtaleCohomology.ofArrows_terminalFrom_mem_smallEtaleTopology`, and the family of elements
on that sieve obtained by restricting along a chosen factorization is compatible by
`Stacks.EtaleCohomology.eq_map_of_smallEtaleCompatible`; its amalgamation is the global section. -/
public theorem exists_globalSection_map_terminalFrom_eq {α : Type*} (W : α → X.Etale)
    (s : ∀ j, F.obj.obj (op (W j))) (hcov : (⨆ j, smallEtaleImage (W j)) = ⊤)
    (hs : SmallEtaleCompatible F W s) :
    ∃ a : F.obj.obj (op (terminal X.Etale)),
      ∀ j, F.obj.map (terminal.from (W j)).op a = s j := by
  set S := Sieve.ofArrows W fun j ↦ terminal.from (W j)
  have hsheaf : Presieve.IsSheafFor F.obj (S : Presieve (terminal X.Etale)) :=
    ((isSheaf_iff_isSheaf_of_type _ _).1 F.property) _
      (ofArrows_terminalFrom_mem_smallEtaleTopology W hcov)
  set x : Presieve.FamilyOfElements F.obj (S : Presieve (terminal X.Etale)) :=
    fun _ _ hf ↦ F.obj.map (Sieve.ofArrows.h hf).op (s (Sieve.ofArrows.i hf)) with hx
  have hxcompat : x.Compatible := by
    intro Y₁ Y₂ T k₁ k₂ f₁ f₂ h₁ h₂ _
    rw [hx, ← types_comp_apply (F.obj.map _) (F.obj.map k₁.op),
      ← types_comp_apply (F.obj.map _) (F.obj.map k₂.op), ← F.obj.map_comp, ← F.obj.map_comp,
      ← op_comp, ← op_comp]
    exact eq_map_of_smallEtaleCompatible F hs _ _
  obtain ⟨a, ha, -⟩ := hsheaf x hxcompat
  refine ⟨a, fun j ↦ ?_⟩
  have hin : S (terminal.from (W j)) := Sieve.ofArrows_mk W (fun j ↦ terminal.from (W j)) j
  rw [ha (terminal.from (W j)) hin, hx]
  exact eq_map_of_smallEtaleCompatible F hs _ (𝟙 (W j)) |>.trans
    (by rw [op_id, F.obj.map_id, types_id_apply])

end Lift

section Pullback

variable {X Z : Scheme.{u}} (i : Z ⟶ X)
  (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale))
  (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))

/-- The pullback of a global section is the restriction along `g` of the pullback of that section
regarded as a section over the final object. -/
public theorem smallEtaleGlobalSectionPullback_eq_map_smallEtaleSectionPullback
    (a : F.obj.obj (op (terminal X.Etale))) :
    smallEtaleGlobalSectionPullback.{u, v} i g F a
      = ((smallEtaleInverseImage.{u, v} i).obj F).obj.map g.op
          (smallEtaleSectionPullback.{u, v} i F (terminal X.Etale) a) :=
  (map_smallEtaleSectionPullback.{u, v} i F g a).symm

/-- **The pullback of a global section, restricted to a base change.** Over the base change along
`i` of an object `W` of the small étale site of `X`, the pullback of a global section `a` of `F` is
the pullback of the restriction of `a` to `W`.

The two morphisms `(smallEtaleBaseChange i).obj W ⟶ (smallEtaleBaseChange i).obj (⊤_ X.Etale)`
available here are equal, the target being a final object; the statement is then naturality of the
Kan extension unit and of the sheafification map, i.e.
`Stacks.EtaleCohomology.smallEtaleSectionPullback_map`. -/
public theorem map_terminalFrom_smallEtaleGlobalSectionPullback
    (a : F.obj.obj (op (terminal X.Etale))) (W : X.Etale) :
    ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
          (terminal.from ((smallEtaleBaseChange i).obj W)).op
          (smallEtaleGlobalSectionPullback.{u, v} i g F a)
      = smallEtaleSectionPullback.{u, v} i F W (F.obj.map (terminal.from W).op a) := by
  have hterm : terminal.from ((smallEtaleBaseChange i).obj W) ≫ g
      = (smallEtaleBaseChange i).map (terminal.from W) :=
    (isTerminalSmallEtaleBaseChangeObj i terminalIsTerminal).hom_ext _ _
  rw [smallEtaleGlobalSectionPullback_eq_map_smallEtaleSectionPullback,
    ← CategoryTheory.Functor.map_comp_apply, ← op_comp, hterm,
    smallEtaleSectionPullback_map.{u, v} i F (terminal.from W) a]

/-- **A compatible presenting family exhibits `t` as a pullback.** Let `W j` be objects of the
small étale site of `X` whose images cover `X`, and `s j` a compatible family of sections of `F`
over them whose pullbacks `i⁻¹(s j)` are the restrictions of a global section `t` of `i^{-1}F` to
the base changes `W j ×_X Z`. Then `t` is the pullback of a global section of `F`.

The `s j` glue to a global section `a` of `F` by
`Stacks.EtaleCohomology.exists_globalSection_map_terminalFrom_eq`. The base changes cover `Z`, and
over each of them the pullback of `a` agrees with `t`; separatedness of `i^{-1}F` for that covering
finishes. -/
public theorem exists_smallEtaleGlobalSectionPullback_eq_of_compatible {α : Type*}
    (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j)))
    (hcov : (⨆ j, smallEtaleImage (W j)) = ⊤) (hs : SmallEtaleCompatible F W s)
    (t : ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op (terminal Z.Etale)))
    (ht : ∀ j, ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
            (terminal.from ((smallEtaleBaseChange i).obj (W j))).op t
          = smallEtaleSectionPullback.{u, v} i F (W j) (s j)) :
    ∃ a, smallEtaleGlobalSectionPullback.{u, v} i g F a = t := by
  obtain ⟨a, ha⟩ := exists_globalSection_map_terminalFrom_eq F W s hcov hs
  refine ⟨a, ?_⟩
  refine (((isSheaf_iff_isSheaf_of_type _ _).1
    ((smallEtaleInverseImage.{u, v} i).obj F).property) _
      (ofArrows_smallEtaleBaseChange_mem_smallEtaleTopology i W hcov)).isSeparatedFor.ext
    fun Y f hf ↦ ?_
  obtain ⟨j, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  rw [op_comp, CategoryTheory.Functor.map_comp_apply, CategoryTheory.Functor.map_comp_apply,
    map_terminalFrom_smallEtaleGlobalSectionPullback, ha j, ht j]

/-- **The surjectivity half of Tag 09ZF, reduced to compatibility.** If every global section `t` of
`i^{-1}F` admits a *compatible* presenting family — objects of the small étale site of `X` whose
images cover `X`, with sections of `F` over them agreeing on the pairwise fibre products and
pulling back to the restrictions of `t` — then the presheaf-level pullback of global sections is
surjective.

`Stacks.EtaleCohomology.exists_smallEtaleCover_sectionPullback_of_inverseImageSection` supplies a
presenting family for every `t`, covering and with the right pullbacks; compatibility is the only
part of the hypothesis it does not supply, and the implementation notes explain why it cannot. -/
public theorem surjective_smallEtaleGlobalSectionPullback_of_exists_compatible
    (hc : ∀ t : ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op (terminal Z.Etale)),
      ∃ (α : Type (u + 1)) (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j))),
        (⨆ j, smallEtaleImage (W j)) = ⊤ ∧ SmallEtaleCompatible F W s ∧
          ∀ j, ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
                (terminal.from ((smallEtaleBaseChange i).obj (W j))).op t
              = smallEtaleSectionPullback.{u, v} i F (W j) (s j)) :
    Function.Surjective (smallEtaleGlobalSectionPullback.{u, v} i g F) := fun t ↦
  let ⟨_, W, s, hcov, hs, ht⟩ := hc t
  exists_smallEtaleGlobalSectionPullback_eq_of_compatible.{u, v} i g F W s hcov hs t ht

/-- **The surjectivity half of Tag 09ZF, for compatible presenting families.** If `i` is a closed
immersion satisfying hypothesis (1) of the tag, and *every* family presenting a global section of
`i^{-1}F` in the sense of
`Stacks.EtaleCohomology.exists_smallEtaleCover_sectionPullback_of_inverseImageSection` is
compatible, then the presheaf-level pullback of global sections is surjective. -/
public theorem surjective_smallEtaleGlobalSectionPullback_of_compatible_cover
    [IsClosedImmersion i]
    (hZar : ∀ G : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)),
      Function.Surjective (zariskiGlobalSectionsMap.{u, v} i G))
    (hcompat : ∀ (α : Type (u + 1)) (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j))),
      (⨆ j, smallEtaleImage (W j)) = ⊤ →
      ∀ t : ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op (terminal Z.Etale)),
        (∀ j, ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
              (terminal.from ((smallEtaleBaseChange i).obj (W j))).op t
            = smallEtaleSectionPullback.{u, v} i F (W j) (s j)) →
        SmallEtaleCompatible F W s) :
    Function.Surjective (smallEtaleGlobalSectionPullback.{u, v} i g F) :=
  surjective_smallEtaleGlobalSectionPullback_of_exists_compatible.{u, v} i g F fun t ↦
    let ⟨α, W, s, hcov, ht⟩ :=
      exists_smallEtaleCover_sectionPullback_of_inverseImageSection.{u, v} i F hZar t
    ⟨α, W, s, hcov, hcompat α W s hcov t ht, ht⟩

end Pullback

/-- **The bijectivity half of Tag 09ZF, reduced to compatibility.** Let `i : Z ⟶ X` be a closed
immersion into a quasi-compact quasi-separated scheme such that restriction of global sections
along `i` is bijective for every sheaf of sets on the Zariski site of `X`. If every global section
of the étale inverse image of every sheaf of sets on the small étale site of `X` admits a
compatible presenting family, then the comparison map
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageComparison` is an isomorphism.

The injectivity half is already available from hypothesis (1); the surjectivity half is
`Stacks.EtaleCohomology.surjective_smallEtaleGlobalSectionPullback_of_exists_compatible`. -/
public theorem isIso_globalSectionsSmallEtaleInverseImageComparison_of_compatible
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hZar : ∀ G : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)),
      Function.Bijective (zariskiGlobalSectionsMap.{u, v} i G))
    (hc : ∀ (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
      (t : ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op (terminal Z.Etale))),
      ∃ (α : Type (u + 1)) (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j))),
        (⨆ j, smallEtaleImage (W j)) = ⊤ ∧ SmallEtaleCompatible F W s ∧
          ∀ j, ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
                (terminal.from ((smallEtaleBaseChange i).obj (W j))).op t
              = smallEtaleSectionPullback.{u, v} i F (W j) (s j)) :
    IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, v} i).val :=
  isIso_globalSectionsSmallEtaleInverseImageComparison_of_surjective.{u, v} i hZar
    fun F g ↦ surjective_smallEtaleGlobalSectionPullback_of_exists_compatible.{u, v} i g F (hc F)

end Stacks.EtaleCohomology

end
