module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianInverseImageExact
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the direct image on abelian sheaves

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi. The direct image of abelian sheaves is always
left exact, being a right adjoint; Stacks 04DB says that it is *exact* as soon as one of four
conditions holds, each of which says that the direct image is in some way compatible with
colimits:

1. `f_*` transforms surjections of sheaves of sets into surjections,
2. `f_*` transforms surjections of abelian sheaves into surjections,
3. `f_*` commutes with coequalizers of sheaves of sets,
4. `f_*` commutes with pushouts of sheaves of sets.

A surjection of sheaves is an epimorphism, so (1) and (2) are preservation of epimorphisms by
the direct image on sheaves of sets and on abelian sheaves respectively, and (3) and (4) are
preservation of colimits of shape `WalkingParallelPair` and of shape `WalkingSpan`.

## Main definitions

* `Stacks.Topos.AbelianPushforward.abelianPushforward`: the direct image of ordinary abelian
  sheaves along a morphism of topoi, obtained by internalizing the group operations, pushing
  them forward, and reading them off on sections again — the construction of
  `CategoryTheory.Sites.abelianInverseImage` with the inverse image replaced by the direct
  image.
* `Stacks.Topos.AbelianPushforward.abelianPushforward_forgetIso`: forgetting the group
  operations after taking the direct image is taking the direct image of the underlying sheaf
  of sets.
* `Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward`: the inverse image of
  abelian sheaves is left adjoint to the direct image.

## Main results

* `CategoryTheory.Functor.preservesEpimorphisms_of_preservesColimitsOfShape_walkingParallelPair`
  and `...walkingSpan`: a functor out of a category in which every epimorphism is regular which
  commutes with coequalizers preserves epimorphisms, and so does any functor commuting with
  pushouts. These are the reductions of alternatives (3) and (4) to alternative (1).
* `Stacks.Topos.AbelianPushforward.preservesEpimorphisms_abelianPushforward`: alternative (1)
  implies alternative (2) — if the direct image of sheaves of sets preserves epimorphisms then
  so does the direct image of abelian sheaves.
* `Stacks.Topos.AbelianPushforward.abelianPushforward_exact_of_preservesEpimorphisms`: given
  alternative (2), the direct image of abelian sheaves is exact.
* `Stacks.Topos.AbelianPushforward.abelianPushforward_exact`: **Stacks 04DB**, the four-fold
  disjunction.

## Implementation notes

The identification of abelian sheaves with the commutative group objects of the topos of
sheaves of sets, and the functor and adjunction it induces on commutative group objects, are
`CategoryTheory.Sites.AbelianSheaf.equivalence`,
`Stacks.Topos.AbelianInverseImage.commGrpPushforward` and
`Stacks.Topos.AbelianInverseImage.commGrpAdjunction`; nothing of that machinery is repeated
here.
Because the direct image is built in exactly the same shape as the inverse image there, the
underlying-sheaf comparison `abelianPushforward_forgetIso` is again `Iso.refl`, which is what
makes the epimorphism transfer between alternatives (1) and (2) a one-line defeq rather than a
transport along a natural isomorphism.

**Hypotheses.** Left exactness needs nothing: the direct image is a right adjoint. Right
exactness is a statement about colimits, so both categories of abelian sheaves have to be
abelian, which is `HasSheafify` for each of the two topologies; the passage from an
epimorphism of abelian sheaves to an epimorphism of the underlying sheaves of sets needs in
addition `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` on the source
topology, and alternative (3) needs sheaves of sets on `C` to have a sheafification, since
that is what makes every epimorphism of sheaves of sets regular. All of these hold in the
setting of the source, where the sites are small categories and the sheaves take values in the
site's own universe; the `UnivLE` forms that discharge the first two at any sheaf universe
dominating the site are `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`.wEqualsLocallyBijective_addCommGrpCat`. The two sites and their two sheaf universes stay
independent throughout.

**Why epimorphisms and not cokernels.** The passage from "preserves epimorphisms" to "right
exact" is `CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels`: a functor
between abelian categories preserving kernels and epimorphisms preserves homology, hence finite
colimits. Kernels are preserved because the functor is left exact.

## References

* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] (F : A ⥤ B)

/-- A functor out of a category in which every epimorphism is regular which commutes with
coequalizers preserves epimorphisms: an epimorphism is the coequalizer of a pair, and its image
is then the coequalizer of the image of that pair, hence an epimorphism. -/
theorem preservesEpimorphisms_of_preservesColimitsOfShape_walkingParallelPair
    [IsRegularEpiCategory A] [PreservesColimitsOfShape WalkingParallelPair F] :
    F.PreservesEpimorphisms where
  preserves {X Y} f hf := by
    let : Epi f := hf
    let r : RegularEpi f := regularEpiOfEpi f
    exact Cofork.IsColimit.epi
      (isColimitCoforkMapOfIsColimit F r.w r.isColimit :
        IsColimit (Cofork.ofπ (F.map f) (by simp only [← F.map_comp, r.w])))

/-- A functor commuting with pushouts preserves epimorphisms: `f` is an epimorphism exactly when
the square with both legs `f` and both coprojections the identity is a pushout square, and that
description is preserved. -/
theorem preservesEpimorphisms_of_preservesColimitsOfShape_walkingSpan
    [PreservesColimitsOfShape WalkingSpan F] : F.PreservesEpimorphisms where
  preserves {X Y} f hf := by
    let : Epi f := hf
    have hc : IsColimit (PushoutCocone.mk (𝟙 Y) (𝟙 Y) (by simp) : PushoutCocone f f) := by
      refine PushoutCocone.IsColimit.mk _ (fun s => s.inl) (fun s => by simp) (fun s => ?_)
        (fun s m hm₁ _ => by simpa using hm₁)
      exact (cancel_epi f).1 (by simpa using s.condition)
    exact PushoutCocone.epi_of_isColimitMkIdId (F.map f)
      (by simpa using isColimitPushoutCoconeMapOfIsColimit F (by simp) hc)

end CategoryTheory.Functor

namespace Stacks.Topos.AbelianPushforward

open Stacks.Topos.AbelianInverseImage

universe v u v' u' w w'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- The direct image of ordinary abelian sheaves along a morphism of topoi: internalize the
group operations, apply the geometric direct image, and read the resulting operations off on
sections again. -/
noncomputable def abelianPushforward :
    Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w'} :=
  Sites.AbelianSheaf.internalSheaf J ⋙ commGrpPushforward J f ⋙ Sites.AbelianSheaf.externalSheaf K

/-- **Stacks 00YR for abelian sheaves, direct-image form.** Forgetting the abelian-group
operations recovers the geometric direct image, naturally in the sheaf. As for the inverse
image, the underlying sheaves and their maps agree definitionally. -/
noncomputable def abelianPushforward_forgetIso :
    abelianPushforward J f ⋙ sheafCompose K (forget AddCommGrpCat.{w'}) ≅
      sheafCompose J (forget AddCommGrpCat.{w}) ⋙ f.pushforward := Iso.refl _

/-- The inverse image of abelian sheaves is left adjoint to the direct image: both are the
functors induced on commutative group objects by the geometric adjunction `f⁻¹ ⊣ f_*`, read
through the identification of abelian sheaves with commutative group objects. -/
noncomputable def abelianInverseImageAdjPushforward :
    Sites.abelianInverseImage f ⊣ abelianPushforward J f :=
  ((Sites.AbelianSheaf.equivalence K).toAdjunction.comp (commGrpAdjunction J f)).comp
    (Sites.AbelianSheaf.equivalence J).symm.toAdjunction

/-- The direct image of abelian sheaves preserves all limits, being a right adjoint; in
particular it is left exact. This needs none of the four alternatives of Stacks 04DB. -/
@[sga "4 IV 3.1.2" "special case"]
theorem preservesLimitsOfSize_abelianPushforward :
    PreservesLimitsOfSize.{0, 0} (abelianPushforward J f) :=
  (abelianInverseImageAdjPushforward J f).rightAdjoint_preservesLimits

/-- The direct image of abelian sheaves is left exact, with no hypothesis on the morphism of
topoi, because it is a right adjoint. -/
noncomputable instance abelianPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (abelianPushforward J f) :=
  have := preservesLimitsOfSize_abelianPushforward J f
  inferInstance

/-- The direct image of abelian sheaves is additive, with no hypothesis on the morphism of
topoi, because it is left exact. -/
instance abelianPushforward_additive [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w'}] : (abelianPushforward J f).Additive :=
  leftExactFunctor_le_additiveFunctor _ _ (abelianPushforward J f)
    (by rw [leftExactFunctor_iff]; infer_instance)

section Exactness

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- An epimorphism of abelian sheaves is an epimorphism on underlying sheaves of sets: it is
locally surjective, local surjectivity passes to the underlying morphism of sheaves of sets,
and a locally surjective morphism of sheaves of sets is an epimorphism. -/
theorem epi_sheafCompose_forget_map {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) [Epi φ] :
    Epi ((sheafCompose J (forget AddCommGrpCat.{w})).map φ) := by
  let : Abelian (Sheaf J AddCommGrpCat.{w}) := CategoryTheory.sheafIsAbelian
  let : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w} φ).2 ‹_›
  infer_instance

/-- **Alternative (1) implies alternative (2) of Stacks 04DB.** If the direct image of sheaves
of sets preserves epimorphisms, so does the direct image of abelian sheaves: the underlying
sheaf of sets of the direct image of a morphism of abelian sheaves *is* the direct image of its
underlying morphism, and forgetting the group operations is faithful, hence reflects
epimorphisms. -/
theorem preservesEpimorphisms_abelianPushforward
    (hf : f.pushforward.PreservesEpimorphisms) :
    (abelianPushforward J f).PreservesEpimorphisms where
  preserves {F G} φ hφ := by
    let : Epi φ := hφ
    let : Epi ((sheafCompose J (forget AddCommGrpCat.{w})).map φ) :=
      epi_sheafCompose_forget_map J φ
    let : Epi ((sheafCompose K (forget AddCommGrpCat.{w'})).map
        ((abelianPushforward J f).map φ)) :=
      hf.preserves ((sheafCompose J (forget AddCommGrpCat.{w})).map φ)
    let : (sheafCompose K (forget AddCommGrpCat.{w'})).ReflectsEpimorphisms :=
      Functor.reflectsEpimorphisms_of_faithful _
    exact (sheafCompose K (forget AddCommGrpCat.{w'})).epi_of_epi_map ‹_›

variable [HasSheafify K AddCommGrpCat.{w'}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Stacks 04DB given alternative (2).** If the direct image of abelian sheaves preserves
epimorphisms then it is exact: it is left exact because it is a right adjoint, so it preserves
kernels, and a functor between abelian categories preserving kernels and epimorphisms preserves
homology and is therefore also right exact. -/
theorem abelianPushforward_exact_of_preservesEpimorphisms
    (h : (abelianPushforward J f).PreservesEpimorphisms) :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w'})
      (abelianPushforward J f) := by
  let : Abelian (Sheaf J AddCommGrpCat.{w}) := CategoryTheory.sheafIsAbelian
  let : Abelian (Sheaf K AddCommGrpCat.{w'}) := CategoryTheory.sheafIsAbelian
  let := preservesLimitsOfSize_abelianPushforward J f
  let : PreservesFiniteLimits (abelianPushforward J f) := inferInstance
  let : (abelianPushforward J f).Additive :=
    Functor.additive_of_preserves_binary_products _
  let := h
  let := Functor.preservesHomology_of_preservesEpis_and_kernels (abelianPushforward J f)
  rw [exactFunctor_iff]
  exact ⟨inferInstance, Functor.preservesFiniteColimits_of_preservesHomology _⟩

/-- **Stacks 04DB.** Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and assume at least one of

1. `f_*` takes surjections of sheaves of sets to surjections,
2. `f_*` takes surjections of abelian sheaves to surjections,
3. `f_*` commutes with coequalizers of sheaves of sets,
4. `f_*` commutes with pushouts of sheaves of sets.

Then `f_* : Ab(C) ⟶ Ab(D)` is exact.

Each of (1), (3) and (4) is reduced to (2): (3) and (4) give (1) because every epimorphism of
sheaves of sets is a regular epimorphism, and (1) gives (2) through the identification of the
underlying sheaf of sets of a direct image with the direct image of the underlying sheaf. -/
@[stacks 04DB]
theorem abelianPushforward_exact [HasSheafify J (Type w)]
    (h : f.pushforward.PreservesEpimorphisms ∨
      (abelianPushforward J f).PreservesEpimorphisms ∨
      PreservesColimitsOfShape WalkingParallelPair f.pushforward ∨
      PreservesColimitsOfShape WalkingSpan f.pushforward) :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w'})
      (abelianPushforward J f) := by
  refine abelianPushforward_exact_of_preservesEpimorphisms J f ?_
  rcases h with h | h | h | h
  · exact preservesEpimorphisms_abelianPushforward J f h
  · exact h
  all_goals refine preservesEpimorphisms_abelianPushforward J f ?_
  · exact Functor.preservesEpimorphisms_of_preservesColimitsOfShape_walkingParallelPair _
  · exact Functor.preservesEpimorphisms_of_preservesColimitsOfShape_walkingSpan _

end Exactness

end Stacks.Topos.AbelianPushforward

end
