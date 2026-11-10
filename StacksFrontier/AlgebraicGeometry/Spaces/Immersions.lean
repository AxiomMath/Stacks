module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover

/-!
# Local criteria for immersions of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is an open immersion, a closed immersion or an
immersion exactly when every one of its base changes to a representable presheaf is. Each of the
three properties is `(P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf`
for a property `P` of morphisms of schemes, and the results are proved for an arbitrary `P`.

## Main results

* `CategoryTheory.MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd`: a morphism
  of presheaves satisfies `P.presheaf` if and only if each of its base changes to a
  representable presheaf does.
* `CategoryTheory.MorphismProperty.presheaf_of_isIso`: an isomorphism of presheaves
  satisfies `P.presheaf`.
* `AlgebraicGeometry.IsAlgebraicSpace.of_iso`: being an algebraic space is invariant under
  isomorphism of presheaves.
* `AlgebraicGeometry.Space.isOpenSubspace_top` and
  `AlgebraicGeometry.Space.isZariskiCover_top`: an algebraic space is an open subspace of
  itself, and the one-member family consisting of itself is a Zariski covering of it.
* `AlgebraicGeometry.Space.exists_surjective_etale_chart_of_presheaf` and
  `AlgebraicGeometry.Space.exists_isZariskiCover_of_presheaf`: a morphism satisfying
  `P.presheaf` has a surjective étale chart, respectively a Zariski covering of its
  target, along which the base change again satisfies `P.presheaf`.
* `AlgebraicGeometry.Space.exists_etale_isPullback_presheaf_of_chart`: a surjective étale
  chart of the target along which the base change satisfies `P.presheaf` makes every
  representable base change satisfy `P.presheaf` after a surjective étale morphism of the
  site.
* `AlgebraicGeometry.Space.isOpenImmersion_iff_forall_pullback_snd`,
  `AlgebraicGeometry.Space.isClosedImmersion_iff_forall_pullback_snd` and
  `AlgebraicGeometry.Space.isImmersion_iff_forall_pullback_snd`: the base-change criterion for
  open immersions, closed immersions and immersions.
* `CategoryTheory.MorphismProperty.relative_isStableUnderComposition`: the relative property
  attached to a morphism property stable under composition is again stable under composition,
  so that `CategoryTheory.MorphismProperty.comp_mem` applies to it.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02YV](https://stacks.math.columbia.edu/tag/02YV)
* [Stacks Project, Tag 02YY](https://stacks.math.columbia.edu/tag/02YY)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C) {F G : Cᵒᵖ ⥤ Type v}

/-- An isomorphism of presheaves satisfies `P.presheaf` as soon as `P` contains the
identities and respects isomorphisms. -/
theorem presheaf_of_isIso [P.ContainsIdentities] [P.RespectsIso] (f : F ⟶ G) [IsIso f] :
    P.presheaf f :=
  relative.of_exists fun a g ↦
    ⟨a, g ≫ inv f, 𝟙 a, IsPullback.of_vert_isIso ⟨by simp⟩, P.id_mem a⟩

/-- If every base change of `f` to a representable presheaf satisfies `P.presheaf`, then so
does `f`. -/
theorem presheaf_of_forall_presheaf_pullback_snd [P.RespectsIso] {f : F ⟶ G}
    (h : ∀ (Z : C) (g : yoneda.obj Z ⟶ G), P.presheaf (pullback.snd f g)) :
    P.presheaf f := by
  refine relative.of_exists fun a g ↦ ?_
  have hq := h a g
  refine ⟨hq.rep.pullback (𝟙 (yoneda.obj a)), hq.rep.fst (𝟙 _) ≫ pullback.fst f g,
    hq.rep.snd (𝟙 _), ?_, hq.property_snd (𝟙 _)⟩
  simpa using ((hq.rep.isPullback (𝟙 _)).flip.paste_vert (IsPullback.of_hasPullback f g).flip).flip

/-- A morphism of presheaves satisfies `P.presheaf` precisely when each of its base changes
to a representable presheaf does. -/
theorem presheaf_iff_forall_presheaf_pullback_snd [P.RespectsIso] (f : F ⟶ G) :
    P.presheaf f ↔ ∀ (Z : C) (g : yoneda.obj Z ⟶ G), P.presheaf (pullback.snd f g) := by
  have := relative_isStableUnderBaseChange (F := yoneda) P
  exact ⟨fun hf _ g ↦ pullback_snd f g hf, presheaf_of_forall_presheaf_pullback_snd P⟩

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

/-- A presheaf isomorphic to an algebraic space over `S` is an algebraic space over `S`. -/
theorem IsAlgebraicSpace.of_iso {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : IsAlgebraicSpace B S hS F) (e : F ≅ F') :
    IsAlgebraicSpace B S hS F' where
  isSheaf := (Presheaf.isSheaf_of_iso_iff e).1 h.isSheaf
  diagonal_representable := by
    refine (MorphismProperty.arrow_mk_iso_iff yoneda.relativelyRepresentable
      (Arrow.isoMk e (Limits.prod.mapIso e e) ?_)).1 h.diagonal_representable
    simp [diag]
  exists_atlas := by
    obtain ⟨U, a, h₁, h₂⟩ := h.exists_atlas
    exact ⟨U, a ≫ e.hom, MorphismProperty.RespectsIso.postcomp _ e.hom a h₁,
      MorphismProperty.RespectsIso.postcomp _ e.hom a h₂⟩

namespace Space

section Top

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The top subfunctor of an algebraic space is an open subspace of it: its inclusion is an
isomorphism. -/
theorem isOpenSubspace_top (hF : IsAlgebraicSpace B S hS F) :
    IsOpenSubspace B S hS (⊤ : Subfunctor F) :=
  ⟨hF.of_iso (asIso (Subfunctor.ι (⊤ : Subfunctor F))).symm,
    MorphismProperty.presheaf_of_isIso _ _⟩

/-- An algebraic space over `S` is Zariski covered by the one-member family consisting of its top
subfunctor. -/
theorem isZariskiCover_top (hF : IsAlgebraicSpace B S hS F) :
    IsZariskiCover B S hS PUnit.{u + 1} (fun _ ↦ (⊤ : Subfunctor F)) :=
  ⟨fun _ ↦ isOpenSubspace_top hF,
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (Sigma.ι_comp_desc (fun _ : PUnit.{u + 1} ↦ (⊤ : Subfunctor F).ι) PUnit.unit)⟩

end Top

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of presheaves on the big fppf site of `S` which satisfies the presheaf
property attached to `P` has a surjective étale chart of its target along which its base
change again satisfies that property, as soon as its target is an algebraic space. -/
theorem exists_surjective_etale_chart_of_presheaf [P.RespectsIso]
    (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G}
    (hf : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ G),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) := by
  obtain ⟨V, g, h₁, h₂⟩ := hG.exists_atlas
  exact ⟨V, g, h₁, h₂,
    ((MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ f).1 hf) V g⟩

/-- A morphism of presheaves on the big fppf site of `S` which satisfies the presheaf
property attached to `P` has a Zariski covering of its target along which its base change
again satisfies that property, as soon as its target is an algebraic space. -/
theorem exists_isZariskiCover_of_presheaf (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G}
    (hf : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) :
    ∃ (I : Type u) (U : I → Subfunctor G), IsZariskiCover B S hS I U ∧
      ∀ i, (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd f (U i).ι) := by
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P.inverseImage (BigFppfOver.toScheme B S hS))
  exact ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hG,
    fun _ ↦ MorphismProperty.pullback_snd _ _ hf⟩

/-- A surjective étale chart `g` of the target along which the base change of `f` satisfies
the presheaf property attached to `P` produces, over every representable base change of `f`,
a surjective étale morphism of the site after which that base change again satisfies the
property. -/
theorem exists_etale_isPullback_presheaf_of_chart [P.RespectsIso] {f : F ⟶ G}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ G}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hq : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g))
    (a : BigFppfOver B S hS) (h : yoneda.obj a ⟶ G) :
    ∃ (c : BigFppfOver B S hS) (q : c ⟶ a) (A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (m : A ⟶ F) (r : A ⟶ yoneda.obj c),
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      IsPullback m r f (yoneda.map q ≫ h) ∧
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r := by
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P.inverseImage (BigFppfOver.toScheme B S hS))
  have sq := hs.rep.isPullback h
  refine ⟨hs.rep.pullback h, hs.rep.snd h, pullback (pullback.snd f g) (hs.rep.fst h),
    pullback.fst (pullback.snd f g) (hs.rep.fst h) ≫ pullback.fst f g,
    pullback.snd (pullback.snd f g) (hs.rep.fst h),
    hs.property h _ _ sq, he.property h _ _ sq, ?_,
    MorphismProperty.pullback_snd _ _ hq⟩
  rw [← sq.w]
  exact (IsPullback.of_hasPullback (pullback.snd f g) (hs.rep.fst h)).paste_horiz
    (IsPullback.of_hasPullback f g)

/-- The base-change criterion for the presheaf property attached to `P`. -/
private theorem presheaf_inverseImage_iff_forall_pullback_snd [P.RespectsIso] (f : F ⟶ G) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f ↔
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) :=
  have := MorphismProperty.RespectsIso.inverseImage P (BigFppfOver.toScheme B S hS)
  MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ f

/-- An open immersion of algebraic spaces over `S` is exactly a morphism all of whose base
changes to a representable presheaf are open immersions of algebraic spaces over `S`. -/
theorem isOpenImmersion_iff_forall_pullback_snd (f : F ⟶ G) :
    IsOpenImmersion B S hS f ↔ ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
      IsOpenImmersion B S hS (pullback.snd f g) := by
  exact presheaf_inverseImage_iff_forall_pullback_snd B S hS _ f

/-- A closed immersion of algebraic spaces over `S` is exactly a morphism all of whose base
changes to a representable presheaf are closed immersions of algebraic spaces over `S`. -/
theorem isClosedImmersion_iff_forall_pullback_snd (f : F ⟶ G) :
    IsClosedImmersion B S hS f ↔ ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
      IsClosedImmersion B S hS (pullback.snd f g) := by
  exact presheaf_inverseImage_iff_forall_pullback_snd B S hS _ f

/-- An immersion of algebraic spaces over `S` is exactly a morphism all of whose base
changes to a representable presheaf are immersions of algebraic spaces over `S`. -/
theorem isImmersion_iff_forall_pullback_snd (f : F ⟶ G) :
    IsImmersion B S hS f ↔ ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
      IsImmersion B S hS (pullback.snd f g) := by
  have : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := @_root_.AlgebraicGeometry.IsImmersion.{u})
  exact presheaf_inverseImage_iff_forall_pullback_snd B S hS _ f

end Space

end AlgebraicGeometry

add_to_stacks 02YV "parts (1)-(3), in the generality of a relatively representable morphism \
property: the relative property of a property stable under composition is again stable under \
composition" CategoryTheory.MorphismProperty.relative_isStableUnderComposition
add_to_stacks 02YV "parts (1)-(3), the conclusion read off from that stability: a composite of \
two morphisms with a property stable under composition again has it"
  CategoryTheory.MorphismProperty.comp_mem

end
