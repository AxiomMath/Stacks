module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Assembly.Relativize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineIntersections

/-!
# Quasi-separatedness of a formal algebraic space, tested on its reduction

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`. **Stacks 0AJ5** says that the following are equivalent: the reduction of `X` is a
quasi-separated algebraic space; the fibre product `U ×_X V` is quasi-compact for every pair of
quasi-compact schemes `U`, `V` over `X`; and the same for every pair of affine schemes over
`X`.

The argument is the one of the source. Writing `U_red` and `V_red` for the reductions of the
two test objects, the morphism `U_red ×_{X_red} V_red = U_red ×_X V_red ⟶ U ×_X V` is a
thickening of schemes, being a composition of two base changes of the thickenings `U_red ⟶ U`
and `V_red ⟶ V`; the identification of the two fibre products is the inclusion of the reduction
being a monomorphism. A thickening is a homeomorphism on points, so it does not change
quasi-compactness, and quasi-separatedness of the reduction is the intersection condition for
the reduction by **Stacks 0AHR**, the reduction being an algebraic space.

That comparison gives the implication from quasi-separatedness of the reduction to the
intersection condition for `X` with quasi-compact test objects. The condition with affine test
objects follows from it because an affine scheme is quasi-compact, and it gives back
quasi-separatedness of the reduction because a fibre product over the reduction is a fibre
product over `X`, the inclusion of the reduction being a monomorphism.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasQuasiCompactIntersectionsULift`: the intersection condition
  of Stacks 0AJ5 for a presheaf in the value universe of the formal algebraic spaces, uniform
  in the condition imposed on the two test objects. Clause (2) of Stacks 0AJ5 is this with
  quasi-compactness and clause (3) is this with affineness.

## Main results

* `AlgebraicGeometry.FormalSpace.isAbsolutelyQuasiSeparated_reduction_tfae`: **Stacks 0AJ5**.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactIntersectionsULift_of_isReduction`: the
  intersection condition passes from the reduction of a formal algebraic space to the space
  itself, which is the content of the source's argument.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactIntersectionsULift_of_mono`: the intersection
  condition passes along a monomorphism into a presheaf, which gives the converse.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactIntersectionsULift_comp_uliftFunctor_iff`: the
  intersection condition for the universe lift of a presheaf of `Type u` is the intersection
  condition of Stacks 0AHR for that presheaf.
* `AlgebraicGeometry.FormalSpace.exists_comp_uliftFunctor_iso_of_isReduction`: every reduction
  is the universe lift of an algebraic space with values in the value universe of the site, so
  the presentation that clause (1) of Stacks 0AJ5 is read against always exists.

## Implementation notes

The reduction is a given here, in the form of a morphism satisfying
`AlgebraicGeometry.FormalSpace.IsReduction`, exactly as in Stacks 0GB8 in
`StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction`. One always exists, by Stacks 0AIN,
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`; reading the
statement against an arbitrary reduction is more general than the statement about a chosen
one, which it implies, and it needs no choice.

Clause (1) of Stacks 0AJ5 is quasi-separatedness of the reduction *as an algebraic space*, and
an algebraic space over `S` is in this library a presheaf with values in `Type u`, the value
universe of the site, whereas a formal algebraic space is a sheaf of `Type (u + 1)`. The
reduction is therefore presented by a presheaf of `Type u` together with an isomorphism from
its universe lift, and clause (1) is `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` of
that presheaf. Such a presentation exists for every reduction, since an algebraic space with
values in `Type (u + 1)` is pointwise `u`-small; that is
`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`, and
`AlgebraicGeometry.FormalSpace.exists_comp_uliftFunctor_iso_of_isReduction` is the statement
for a reduction.

The fibre product of the two test objects is not named by a construction but specified by a
cartesian square over the universe-lifted Yoneda embedding together with an object of the site
representing it, as in `AlgebraicGeometry.Space.HasQuasiCompactIntersections`, so its
quasi-compactness does not depend on the choice of a representing object. Neither intersection
condition asserts that the fibre product *is* representable: that is Stacks 0AIP, proved in
this library only for an affine formal algebraic space (see
`StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal`), and the source's proof of 0AJ5
appeals to it only to know that the object whose quasi-compactness is at stake is a scheme. The
two carriers of Stacks 0AHR read the identical clauses the same way.

The two intersection conditions of Stacks 0AJ5 are the two instances of
`AlgebraicGeometry.FormalSpace.HasQuasiCompactIntersectionsULift` at the two conditions on the
test objects, which keeps the comparison with the reduction uniform in that condition: it needs
only that the condition passes to the reduction of an object of the site.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
* [Stacks Project, Tag 0AHR](https://stacks.math.columbia.edu/tag/0AHR)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AJ5](https://stacks.math.columbia.edu/tag/0AJ5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The intersection condition in the value universe of the formal algebraic spaces -/

/-- The universe lift of presheaves on the big fppf site of `S` from the value universe of the
site to the value universe of the formal algebraic spaces. -/
private abbrev upFunctor : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤
    ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}

/-- **The intersection condition of Stacks 0AJ5.** For every pair of objects `U`, `V` of the
big fppf site of `S` whose underlying schemes satisfy `P` and every pair of morphisms
`h_U ⟶ X`, `h_V ⟶ X` out of their universe-lifted Yoneda presheaves, every object of the site
representing the fibre product `U ×_X V` has quasi-compact underlying scheme.

Clause (2) of Stacks 0AJ5 is this with `P` quasi-compactness of the underlying scheme and
clause (3) is this with `P` affineness of it. -/
abbrev HasQuasiCompactIntersectionsULift (P : Scheme.{u} → Prop)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∀ (U V Q : BigFppfOver B S hS)
    (a : (uliftYoneda.{u + 1}).obj U ⟶ X) (b : (uliftYoneda.{u + 1}).obj V ⟶ X)
    (p : Q ⟶ U) (q : Q ⟶ V),
    P ((BigFppfOver.toScheme B S hS).obj U) →
    P ((BigFppfOver.toScheme B S hS).obj V) →
    IsPullback ((uliftYoneda.{u + 1}).map p) ((uliftYoneda.{u + 1}).map q) a b →
    CompactSpace ((BigFppfOver.toScheme B S hS).obj Q)

/-- The intersection condition passes along a monomorphism: a cartesian square over a cospan
stays cartesian after composing both its legs with a monomorphism, so a representing object of
a fibre product over the source of the monomorphism represents the fibre product over its
target. -/
theorem hasQuasiCompactIntersectionsULift_of_mono (P : Scheme.{u} → Prop)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (m : F ⟶ G) [Mono m]
    (h : HasQuasiCompactIntersectionsULift B S hS P G) :
    HasQuasiCompactIntersectionsULift B S hS P F := fun U V Q a b p q hU hV sq ↦
  h U V Q (a ≫ m) (b ≫ m) p q hU hV ((isPullback_comp_mono_iff m).mpr sq)

/-- Every morphism from a universe-lifted Yoneda presheaf into the universe lift of a presheaf
of `Type u` is the universe lift of a morphism of presheaves of `Type u`: the universe lift of
presheaves is full, and it carries the Yoneda presheaf of an object of the site to the
universe-lifted one. -/
private theorem exists_map_upFunctor_eq (T : BigFppfOver B S hS)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (c : (uliftYoneda.{u + 1}).obj T ⟶ F ⋙ uliftFunctor.{u + 1}) :
    ∃ c₀ : yoneda.obj T ⟶ F,
      ((upFunctor B S hS).map c₀ :
        (uliftYoneda.{u + 1}).obj T ⟶ F ⋙ uliftFunctor.{u + 1}) = c :=
  (upFunctor B S hS).map_surjective (X := yoneda.obj T) (Y := F) c

/-- The intersection condition for the universe lift of a presheaf of `Type u` on the big fppf
site of `S` is the intersection condition of Stacks 0AHR for that presheaf: the universe lift
of presheaves is fully faithful and preserves fibre products, and it carries the Yoneda
embedding to the universe-lifted one, so the cartesian squares the two conditions quantify over
correspond. -/
theorem hasQuasiCompactIntersectionsULift_comp_uliftFunctor_iff (P : Scheme.{u} → Prop)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasQuasiCompactIntersectionsULift B S hS P (F ⋙ uliftFunctor.{u + 1}) ↔
      Space.HasQuasiCompactIntersections B S hS P F := by
  refine ⟨fun h U V Q a b p q hU hV sq ↦
    h U V Q ((upFunctor B S hS).map a) ((upFunctor B S hS).map b) p q hU hV
      (sq.map (upFunctor B S hS)), fun h U V Q a b p q hU hV sq ↦ ?_⟩
  obtain ⟨a₀, rfl⟩ := exists_map_upFunctor_eq B S hS U F a
  obtain ⟨b₀, rfl⟩ := exists_map_upFunctor_eq B S hS V F b
  refine h U V Q a₀ b₀ p q hU hV (IsPullback.of_map (upFunctor B S hS) ?_ sq)
  refine (upFunctor B S hS).map_injective ?_
  simp only [Functor.map_comp]
  exact sq.w

/-! ### The comparison with the reduction -/

/-- A base change of the inclusion of the reduction of an object of the big fppf site of `S` is
a thickening of the underlying schemes. -/
theorem isThickening_toScheme_map_pullback_snd_siteReductionMap (T : BigFppfOver B S hS)
    {W : BigFppfOver B S hS} (f : W ⟶ T) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (siteReductionMap B S hS T) f)) := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  exact Stacks.Thickenings.isThickening_isStableUnderBaseChange.of_isPullback
    ((IsPullback.of_hasPullback (siteReductionMap B S hS T) f).map
      (BigFppfOver.toScheme B S hS))
    (isThickening_toScheme_map_siteReductionMap B S hS T)

/-- **The intersection condition passes from the reduction of a formal algebraic space to the
space itself.** This is the argument of Stacks 0AJ5: the two test objects are replaced by their
reductions, which map to the reduction of the space by the universal property, the fibre product
of the reductions over the reduction of the space is the fibre product over the space itself
because the inclusion of a reduction is a monomorphism, and that fibre product maps to the
original one by a composition of two base changes of the thickenings `U_red ⟶ U` and
`V_red ⟶ V`, hence by a thickening, which does not change quasi-compactness. -/
theorem hasQuasiCompactIntersectionsULift_of_isReduction (P : Scheme.{u} → Prop)
    (hPred : ∀ T : BigFppfOver B S hS, P ((BigFppfOver.toScheme B S hS).obj T) →
      P ((BigFppfOver.toScheme B S hS).obj (siteReduction B S hS T)))
    {X Xr : FppfSheaf B S hS} {i : Xr ⟶ X} (hi : IsReduction B S hS X Xr i)
    (h : HasQuasiCompactIntersectionsULift B S hS P Xr.obj) :
    HasQuasiCompactIntersectionsULift B S hS P X.obj := by
  have _ : Mono i.hom :=
    mono_of_isRepresentableThickeningULift B S hS hi.isRepresentableThickening
  intro U V Q a b p q hU hV sq
  have lift : ∀ (T : BigFppfOver B S hS) (c : (uliftYoneda.{u + 1}).obj T ⟶ X.obj),
      ∃ t, t ≫ i.hom = (uliftYoneda.{u + 1}).map (siteReductionMap B S hS T) ≫ c := fun T c ↦
    (hi.existsUnique_comp_eq (siteReduction B S hS T)
      (isReduced_toScheme_obj_siteReduction B S hS T)
      (uliftYonedaEquiv.{u + 1}
        ((uliftYoneda.{u + 1}).map (siteReductionMap B S hS T) ≫ c))).exists.imp
      fun _ ht ↦ by simpa using ht
  obtain ⟨a₁, ha₁⟩ := lift U a
  obtain ⟨b₁, hb₁⟩ := lift V b
  have sq₁ := IsPullback.of_hasPullback (siteReductionMap B S hS U) p
  have sqY₂ := (IsPullback.of_hasPullback (siteReductionMap B S hS V)
    (pullback.snd (siteReductionMap B S hS U) p ≫ q)).map (uliftYoneda.{u + 1})
  rw [Functor.map_comp] at sqY₂
  have paste := sqY₂.paste_vert ((sq₁.map (uliftYoneda.{u + 1})).paste_vert sq).flip
  rw [← ha₁, ← hb₁, ← Functor.map_comp] at paste
  have hcompact := h (siteReduction B S hS V) (siteReduction B S hS U) _ b₁ a₁ _ _
    (hPred V hV) (hPred U hU) ((isPullback_comp_mono_iff i.hom).mp paste)
  have hcomp : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (siteReductionMap B S hS V)
        (pullback.snd (siteReductionMap B S hS U) p ≫ q) ≫
        pullback.snd (siteReductionMap B S hS U) p)) := by
    rw [Functor.map_comp]
    exact Stacks.Thickenings.isThickening_comp
      (isThickening_toScheme_map_pullback_snd_siteReductionMap B S hS V _)
      (isThickening_toScheme_map_pullback_snd_siteReductionMap B S hS U p)
  exact hcomp.compactSpace

/-! ### Stacks 0AJ5 -/

/-- **A reduction of an fppf sheaf on the big fppf site of `S` is presented by a presheaf with
values in the value universe of the site.** A reduction is an algebraic space, and an algebraic
space with values in the value universe of the formal algebraic spaces is the universe lift of
an algebraic space with values in the value universe of the site. -/
theorem exists_comp_uliftFunctor_iso_of_isReduction {X Xr : FppfSheaf B S hS} {i : Xr ⟶ X}
    (hi : IsReduction B S hS X Xr i) :
    ∃ Xred : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B S hS Xred ∧ Nonempty (Xred ⋙ uliftFunctor.{u + 1} ≅ Xr.obj) :=
  Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hi.algebraic

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The reduction of a quasi-compact object of the big fppf site of `S` is quasi-compact: a
closed immersion is a quasi-compact morphism. -/
theorem compactSpace_toScheme_obj_siteReduction (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T : Type u)) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (siteReduction B S hS T) : Type u) := by
  have _ : IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS T)) :=
    (isThickening_toScheme_map_siteReductionMap B S hS T).1
  exact QuasiCompact.compactSpace_of_compactSpace
    ((BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS T))

/-- **Stacks 0AJ5.** Let `X` be a formal algebraic space over `S` and let `i : X_red ⟶ X` be a
reduction of `X`, presented by a presheaf `Xred` of `Type u` together with an isomorphism from
its universe lift. The following are equivalent: `Xred` is a quasi-separated algebraic space;
for every pair of objects of the big fppf site of `S` with quasi-compact underlying scheme and
every pair of morphisms from their universe-lifted Yoneda presheaves into `X`, every object of
the site representing the fibre product has quasi-compact underlying scheme; and the same for
every pair of objects with affine underlying scheme.

Condition (1) is equivalent to the intersection condition for `Xred`, with quasi-compact or
with affine test objects, by Stacks 0AHR. The intersection condition for `X` implies the one
for `Xred` because the inclusion of a reduction is a monomorphism, and conversely it follows
from the one for `Xred` by the thickening comparison of
`AlgebraicGeometry.FormalSpace.hasQuasiCompactIntersectionsULift_of_isReduction`. -/
@[stacks 0AJ5 "the reduction of X is a given, in the sense of \
AlgebraicGeometry.FormalSpace.IsReduction and supplied by Stacks 0AIN, and is presented by a \
presheaf of Type u together with \
an isomorphism from its universe lift, since an algebraic space over S is a presheaf of \
Type u while a formal algebraic space is a sheaf of Type (u + 1); clauses (2) and (3) \
quantify over the objects of the site representing the fibre product, as the carriers of \
Stacks 0AHR do for the identical clauses, rather than asserting that it is representable, \
which is Stacks 0AIP"]
theorem isAbsolutelyQuasiSeparated_reduction_tfae
    {X Xr : FppfSheaf B S hS} (_hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xr ⟶ X} (hi : IsReduction B S hS X Xr i)
    {Xred : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : Xred ⋙ uliftFunctor.{u + 1} ≅ Xr.obj) :
    List.TFAE
      [ Space.IsAbsolutelyQuasiSeparated B S hS hZ Xred,
        HasQuasiCompactIntersectionsULift B S hS
          (fun Z : Scheme.{u} ↦ CompactSpace (Z : Type u)) X.obj,
        HasQuasiCompactIntersectionsULift B S hS (fun Z : Scheme.{u} ↦ IsAffine Z) X.obj ] := by
  have _ : Mono i.hom :=
    mono_of_isRepresentableThickeningULift B S hS hi.isRepresentableThickening
  have halg : IsAlgebraicSpace B S hS Xred :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Xred).mp
      (Space.isAlgebraicSpaceULift_of_iso B S hS e.symm hi.algebraic)
  have h0AHR := Space.isAbsolutelyQuasiSeparated_tfae B S hS hZ Xred halg
  tfae_have 1 → 2 := fun hqs ↦
    hasQuasiCompactIntersectionsULift_of_isReduction B S hS _
      (compactSpace_toScheme_obj_siteReduction B S hS) hi
      (hasQuasiCompactIntersectionsULift_of_mono B S hS _ e.inv
        ((hasQuasiCompactIntersectionsULift_comp_uliftFunctor_iff B S hS _ Xred).mpr
          ((h0AHR.out 1 2).mp hqs)))
  tfae_have 2 → 3 := fun h U V Q a b p q _ _ sq ↦
    h U V Q a b p q (Scheme.compactSpace_of_isAffine _) (Scheme.compactSpace_of_isAffine _) sq
  tfae_have 3 → 1 := fun h ↦
    (h0AHR.out 1 3).mpr
      ((hasQuasiCompactIntersectionsULift_comp_uliftFunctor_iff B S hS _ Xred).mp
        (hasQuasiCompactIntersectionsULift_of_mono B S hS _ e.hom
          (hasQuasiCompactIntersectionsULift_of_mono B S hS _ i.hom h)))
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
