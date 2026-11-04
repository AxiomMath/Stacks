module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubschemeLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedRefinable

/-!
# A full subcategory cut out by an open locus is an open immersion

Let `𝒟` be a category over the big fppf site of a scheme `S` and let `G : 𝒞 ⟶ 𝒟` be a
1-morphism over that site whose underlying functor is fully faithful — the case of interest
being the inclusion of a full subcategory `Q ⊆ 𝒟`.  Suppose that every scheme-valued point `y`
of `𝒟` over an object `U` of the big fppf site cuts out an *open subscheme* `V ⊆ U` through which
an object `T` of the big fppf site of `U` maps exactly when `y(T)` is in the image of `G` — for a
full subcategory, exactly when `y(T)` has the property `Q`.  Then `G` is representable by
algebraic spaces and an open immersion, and the representing algebraic space of each base change
is that open subscheme.

This is the mechanism of the proof of **Stacks 06CL** separated from the finite Hilbert stack.
It is the only machinery in this library that delivers *both* conjuncts of Stacks 04YL (1) —
representability by algebraic spaces and the open-immersion condition of Stacks 04XB — from an
open-subscheme datum, and nothing in it is about local complete intersections: it is used by
`StacksFrontier/AlgebraicGeometry/Stacks/FiniteHilbert/LciLocusOpen.lean` for Stacks 06CL and is
available for any other open substack cut out by a property of the objects.

## Main definitions

* `AlgebraicGeometry.Stack.HasOpenLocus`: the one geometric input — the open subscheme cut out on
  the base of a scheme-valued point by the image of `G`.
* `AlgebraicGeometry.Stack.objectPropertySubcategory` and
  `AlgebraicGeometry.Stack.objectPropertyInclusion`: the full subcategory of a category over the
  big fppf site cut out by a property of its objects, as a category over that site, and its
  inclusion.
* `AlgebraicGeometry.Stack.HasOpenObjectPropertyLocus`: the same input read at a property of the
  objects.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_hasOpenLocus`: **Stacks 02ZW**
  for a fully faithful 1-morphism with an open locus.
* `AlgebraicGeometry.Stack.isOpenImmersion_of_hasOpenLocus`: the open-immersion condition of
  Stacks 04XB for it, written out — which is `AlgebraicGeometry.Stack.IsOpenImmersion` for a
  1-morphism of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_objectPropertyInclusion` and
  `AlgebraicGeometry.Stack.isOpenImmersion_objectPropertyInclusion`: the two conclusions for the
  inclusion of a full subcategory closed under isomorphisms.
* `AlgebraicGeometry.Stack.exists_isOpenImmersion_equivalenceOver_of_hasOpenLocus` and
  `AlgebraicGeometry.Stack.exists_iso_yoneda_of_equivalenceOver_of_hasOpenLocus`: the two
  comparisons the conclusions rest on — the 2-fibre product *is* the open subscheme, and *every*
  algebraic space representing it is.

## Implementation notes

Representability is the comparison of two categories over the big fppf site of the base: the
first projection of the 2-fibre product of `G` with a scheme-valued point of `𝒟`, which is fully
faithful because `G` is, and the category of elements of the sheaf of points of the open
subscheme `V`, whose projection is fully faithful because there is at most one morphism to `V`
over `U`.  Two fully faithful categories over a base with the same image on objects are
equivalent over it, and `AlgebraicGeometry.Stack.HasOpenLocus` says exactly that these two
images agree.  The same comparison identifies *every* algebraic space representing the 2-fibre
product with `V`, which is what the open-immersion condition of Stacks 04XB quantifies over:
both presheaves take subsingleton values and have the same support, so they are isomorphic.

The open-immersion conclusion is `AlgebraicGeometry.Stack.IsOpenImmersion` written out.  That
predicate takes a 1-morphism of the 2-category of categories fibred in groupoids, and this
module deliberately stays at the level of categories over the site: a consumer which does know
that both sides are fibred in groupoids obtains the packaged predicate by `exact`, since it is
an abbreviation for the condition below at `CategoryTheory.CatFiberedInGroupoids.homFunctor`,
and a consumer for which the fibred-in-groupoids structure of the subcategory is itself part of
what is being proved — as it is for Stacks 06CL — uses the written-out form.  Keeping
`StacksFrontier/AlgebraicGeometry/Stacks/ImmersionAlgebraicStack.lean` out of the imports also
keeps the import closure of this module, and so of Stacks 06CL, small.

Fullness and faithfulness of the underlying functor are explicit arguments rather than instance
hypotheses: the two are properties of `G.toFunctor`, and instance search does not see through
the projection at an application where `G` is itself the result of unfolding a definition, as it
is for the inclusion of a full subcategory of a named category over the site.

The structural morphism the open-immersion condition tests is the one of Stacks 04SG, replaced
by `CategoryTheory.OverShriek.relocalizeToYoneda` through
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`, which is the form in which the
identification of the representing presheaf with `V` can be used.

## References

* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w v₁ u₁ v₂ u₂

namespace AlgebraicGeometry.Stack

/-! ### Comparison of two categories over a base -/

section Comparison

universe v

variable {C A D E : Type*} [Category C] [Category A] [Category D] [Category E]

/-- **The first projection of a 2-fibre product over the base is fully faithful as soon as the
second leg is.**  A morphism of the 2-fibre product is determined by its first component, the
comparison isomorphisms fixing the second; and a morphism of first components lifts, its second
component being the preimage under the second leg of the conjugate of the first. -/
noncomputable def fullyFaithfulTwoFibreProductFst (p : A ⥤ C) (q : D ⥤ C) (r : E ⥤ C)
    (G₁ : A ⥤ E) (G₂ : D ⥤ E) (hG₁ : G₁ ⋙ r = p) (hG₂ : G₂ ⋙ r = q)
    (h₂ : G₂.FullyFaithful) : (TwoFibreProductOver.fst p q r G₁ G₂).FullyFaithful :=
  haveI := h₂.full
  haveI := h₂.faithful
  haveI : (TwoFibreProductOver.fst p q r G₁ G₂).Faithful :=
    ⟨fun {X Y} f g h => by
      apply TwoFibreProductOver.Hom.ext' h
      apply G₂.map_injective
      apply (cancel_epi X.iso.hom).mp
      rw [← f.w, ← g.w]
      exact congrArg (fun a => G₁.map a ≫ Y.iso.hom) h⟩
  haveI : (TwoFibreProductOver.fst p q r G₁ G₂).Full :=
    ⟨fun {X Y} a => by
      subst p q
      change X.x ⟶ Y.x at a
      let b := G₂.preimage (X.iso.inv ≫ G₁.map a ≫ Y.iso.hom)
      have hbase : eqToHom X.hy.symm ≫ (G₂ ⋙ r).map b ≫ eqToHom Y.hy =
          eqToHom X.hx.symm ≫ (G₁ ⋙ r).map a ≫ eqToHom Y.hx := by
        have hXhom : r.IsHomLift (𝟙 X.base) X.iso.hom := X.vertical
        have hYhom : r.IsHomLift (𝟙 Y.base) Y.iso.hom := Y.vertical
        have hXinv : r.IsHomLift (𝟙 X.base) X.iso.inv := inferInstance
        have hXm := IsHomLift.fac' r (𝟙 X.base) X.iso.inv
        have hYm := IsHomLift.fac' r (𝟙 Y.base) Y.iso.hom
        change eqToHom X.hy.symm ≫ r.map (G₂.map b) ≫ eqToHom Y.hy = _
        dsimp [b]
        rw [G₂.map_preimage, r.map_comp, r.map_comp, hXm, hYm]
        simp
      refine ⟨TwoFibreProductOver.Hom.mk' a b hbase ?_, rfl⟩
      dsimp [b]
      simp⟩
  Functor.FullyFaithful.ofFullyFaithful _

/-- A fully faithful functor over the base whose image on objects contains that of another one
receives a 1-morphism over the base from it: choose preimages of objects and transport morphisms
through the fully faithful structure. -/
theorem nonempty_morphismOver_of_range_obj_subset (p : A ⥤ C) (q : D ⥤ C)
    (hq : q.FullyFaithful) (h : Set.range p.obj ⊆ Set.range q.obj) :
    Nonempty (StacksRepresentableCFG.MorphismOver p q) := by
  classical
  have := hq.full
  have := hq.faithful
  have hh : ∀ a, ∃ e, q.obj e = p.obj a := fun a => h ⟨a, rfl⟩
  choose obj ho using hh
  let G : A ⥤ D :=
    { obj := obj
      map := fun {a b} f => q.preimage (eqToHom (ho a) ≫ p.map f ≫ eqToHom (ho b).symm)
      map_id := by intro a; apply q.map_injective; simp
      map_comp := by intro a b c f g; apply q.map_injective; simp }
  refine ⟨G, CategoryTheory.Functor.ext ho ?_⟩
  intro a b f
  show q.map (q.preimage _) = _
  simp

/-- Two functors into the source of a fully faithful functor `p` whose composites with `p` agree
are isomorphic by an isomorphism that `p` sends to the identity. -/
private theorem exists_iso_whiskerRight_eq_eqToHom {E' : Type*} [Category E'] (p : D ⥤ C)
    (hp : p.FullyFaithful) (F G : E' ⥤ D) (h : F ⋙ p = G ⋙ p) :
    ∃ η : F ≅ G, Functor.whiskerRight η.hom p = eqToHom h :=
  have := hp.full
  have := hp.faithful
  have hw := Functor.FullyFaithful.ofFullyFaithful ((Functor.whiskeringRight E' D C).obj p)
  ⟨hw.preimageIso (eqToIso h), hw.map_preimage _⟩

/-- **Two fully faithful functors over the base with the same image on objects are equivalent
over the base.**  Each factors through the other by
`AlgebraicGeometry.Stack.nonempty_morphismOver_of_range_obj_subset`, and the two composites are
the identities up to the unique isomorphisms over the base. -/
theorem nonempty_equivalenceOver_of_range_obj_eq (p : A ⥤ C) (q : D ⥤ C)
    (hp : p.FullyFaithful) (hq : q.FullyFaithful) (h : Set.range p.obj = Set.range q.obj) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver p q) := by
  obtain ⟨G₁⟩ := nonempty_morphismOver_of_range_obj_subset p q hq h.subset
  obtain ⟨G₂⟩ := nonempty_morphismOver_of_range_obj_subset q p hp h.symm.subset
  have hu : (G₁.functor ⋙ G₂.functor) ⋙ p = p := by rw [Functor.assoc, G₂.w, G₁.w]
  have hc : (G₂.functor ⋙ G₁.functor) ⋙ q = q := by rw [Functor.assoc, G₁.w, G₂.w]
  obtain ⟨η, hη⟩ := exists_iso_whiskerRight_eq_eqToHom p hp (𝟭 A) (G₁.functor ⋙ G₂.functor)
    (by rw [Functor.id_comp, hu])
  obtain ⟨ε, hε⟩ := exists_iso_whiskerRight_eq_eqToHom q hq (G₂.functor ⋙ G₁.functor) (𝟭 D)
    (by rw [Functor.id_comp, hc])
  exact ⟨G₁, G₂, η, ε, hη, hε⟩

attribute [local implicit_reducible] Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc

/-- **The projection from the category of elements of a subsingleton-valued presheaf of sets is
fully faithful**: a morphism of elements is its base morphism together with a proof that the
sections match, and the latter is automatic for a subsingleton-valued presheaf. -/
noncomputable def fullyFaithfulElementsProjection (P : Cᵒᵖ ⥤ Type*)
    (hP : ∀ X, Subsingleton (P.obj X)) :
    (presheafOfCategories (P ⋙ typeToCat)).p.FullyFaithful :=
  haveI : (presheafOfCategories (P ⋙ typeToCat)).p.Faithful :=
    ⟨fun {X Y} f g h => by
      apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ h
      exact @Subsingleton.elim (Discrete.mk X.fiber.as ⟶
        Discrete.mk (P.map f.base.op Y.fiber.as)) inferInstance _ _⟩
  haveI : (presheafOfCategories (P ⋙ typeToCat)).p.Full :=
    ⟨fun {X Y} f => by
      refine ⟨⟨f, ?_⟩, rfl⟩
      exact eqToHom (by
        apply Discrete.ext
        exact (hP _).elim _ _)⟩
  Functor.FullyFaithful.ofFullyFaithful _

/-- The objects of the base in the image of the projection from the category of elements of a
presheaf are those over which the presheaf has a section. -/
theorem range_elementsProjection_obj (P : Cᵒᵖ ⥤ Type*) :
    Set.range (presheafOfCategories (P ⋙ typeToCat)).p.obj =
      {X | Nonempty (P.obj (Opposite.op X))} := by
  ext X
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.fiber.as⟩
  · rintro ⟨a⟩
    exact ⟨⟨X, Discrete.mk a⟩, rfl⟩

/-- **An equivalence over the base preserves fullness and the image on objects.**  The image of
the source and target functors on objects agree, the two functors commuting with the
equivalence; and the target functor is full whenever the source functor is. -/
theorem range_obj_eq_and_full_of_equivalenceOver {p : A ⥤ C} {q : D ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver p q) (hp : p.Full) :
    Set.range p.obj = Set.range q.obj ∧ q.Full := by
  refine ⟨Set.ext fun c => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨a, rfl⟩
    exact ⟨e.hom.functor.obj a, congrArg (fun G => G.obj a) e.hom.w⟩
  · rintro ⟨b, rfl⟩
    exact ⟨e.inv.functor.obj b, congrArg (fun G => G.obj b) e.inv.w⟩
  · have : e.inv.functor.Full := by
      show e.toEquivalence.inverse.Full
      infer_instance
    rw [← e.inv.w]
    infer_instance

end Comparison

/-! ### The open-locus mechanism -/

section OpenLocus

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The one geometric input of the open-locus mechanism.**  A 1-morphism `G : 𝒞 ⟶ 𝒟` of
categories over the big fppf site of `S` *has an open locus* when, for every scheme-valued point
`y` of `𝒟` over an object `U` of the big fppf site, there is an open subscheme `V` of `U`
through which an object `T` of the big fppf site of `U` maps exactly when `T` is in the image of
the first projection of the 2-fibre product `(Sch/U)_{fppf} ×_{y, 𝒟} 𝒞`. -/
def HasOpenLocus {𝒞 : BasedCategory.{v₁, u₁} (BigFppfOver B S hS)}
    {𝒟 : BasedCategory.{v₂, u₂} (BigFppfOver B S hS)} (G : 𝒞 ⥤ᵇ 𝒟) : Prop :=
  ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj),
    y ⋙ 𝒟.p = Over.map U.hom →
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        Nonempty (T ⟶ V) ↔
          ∃ a, (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor).obj a = T

variable {𝒞 : BasedCategory.{v₁, u₁} (BigFppfOver B S hS)}
  {𝒟 : BasedCategory.{v₂, u₂} (BigFppfOver B S hS)}

/-- **Every 2-fibre product of a fully faithful 1-morphism with an open locus is the open
subscheme the locus cuts out.**  The first projection of the 2-fibre product is fully faithful
because `G` is, and the category of elements of the sheaf of points of that open subscheme has
fully faithful projection because there is at most one morphism to an open subscheme; the two
have the same image on objects, so they are equivalent over the big fppf site of the base. -/
theorem exists_isOpenImmersion_equivalenceOver_of_hasOpenLocus (G : 𝒞 ⥤ᵇ 𝒟)
    (hfull : G.toFunctor.Full) (hfaithful : G.toFunctor.Faithful)
    (hopen : HasOpenLocus B S hS G) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj)
    (hy : y ⋙ 𝒟.p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor)
        (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p) := by
  obtain ⟨V, hV, hVlocus⟩ := hopen U y hy
  refine ⟨V, hV, nonempty_equivalenceOver_of_range_obj_eq _ _
    (fullyFaithfulTwoFibreProductFst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor hy G.w
      (Functor.FullyFaithful.ofFullyFaithful G.toFunctor))
    (fullyFaithfulElementsProjection (yoneda.obj V)
      (fun T ↦ subsingleton_hom_of_isOpenImmersion B S hS U V hV T.unop)) ?_⟩
  rw [range_elementsProjection_obj]
  ext T
  exact (hVlocus T).symm

/-- **A fully faithful 1-morphism with an open locus is representable by algebraic spaces**, the
representing algebraic space of a base change being the open subscheme of the base the locus cuts
out.  This is the first conjunct of the conclusion of Stacks 04YL (1). -/
theorem isRepresentableByAlgebraicSpaces_of_hasOpenLocus (G : 𝒞 ⥤ᵇ 𝒟)
    (hfull : G.toFunctor.Full) (hfaithful : G.toFunctor.Faithful)
    (hopen : HasOpenLocus B S hS G) :
    IsRepresentableByAlgebraicSpaces B S hS G := by
  intro U
  dsimp only
  intro y hy
  obtain ⟨V, _, he⟩ :=
    exists_isOpenImmersion_equivalenceOver_of_hasOpenLocus B S hS G hfull hfaithful hopen U y hy
  exact ⟨yoneda.obj V, isAlgebraicSpace_yoneda B U.left.1 U.left.2 V, he⟩

/-- **Every algebraic space representing a base change of a fully faithful 1-morphism with an
open locus is the open subscheme the locus cuts out**: both presheaves take subsingleton values
and have the same support. -/
theorem exists_iso_yoneda_of_equivalenceOver_of_hasOpenLocus (G : 𝒞 ⥤ᵇ 𝒟)
    (hfull : G.toFunctor.Full) (hfaithful : G.toFunctor.Faithful)
    (hopen : HasOpenLocus B S hS G) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj)
    (hy : y ⋙ 𝒟.p = Over.map U.hom)
    (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor)
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      Nonempty (P ≅ yoneda.obj V) := by
  obtain ⟨V, hV, hVlocus⟩ := hopen U y hy
  have hfst := (fullyFaithfulTwoFibreProductFst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor hy G.w
    (Functor.FullyFaithful.ofFullyFaithful G.toFunctor)).full
  obtain ⟨hrange, hfullP⟩ := range_obj_eq_and_full_of_equivalenceOver e hfst
  have hsubP : ∀ X, Subsingleton (P.obj X) := by
    intro X
    constructor
    intro a b
    let A' : (presheafOfCategories (P ⋙ typeToCat)).obj := ⟨X.unop, Discrete.mk a⟩
    let D' : (presheafOfCategories (P ⋙ typeToCat)).obj := ⟨X.unop, Discrete.mk b⟩
    obtain ⟨m, hm⟩ := (presheafOfCategories (P ⋙ typeToCat)).p.map_surjective
      (X := A') (Y := D') (𝟙 X.unop)
    have he : a = P.map m.base.op b := Discrete.eq_of_hom m.fiber
    change m.base = 𝟙 X.unop at hm
    rw [hm] at he
    change a = P.map (𝟙 X) b at he
    simpa only [P.map_id, types_id_apply] using he
  refine ⟨V, hV, nonempty_iso_of_subsingleton P (yoneda.obj V) hsubP
    (fun T ↦ subsingleton_hom_of_isOpenImmersion B S hS U V hV T.unop) ?_⟩
  intro T
  have h1 := congrArg (T.unop ∈ ·) (range_elementsProjection_obj P)
  have h2 := congrArg (T.unop ∈ ·) hrange
  simp only [eq_iff_iff] at h1 h2
  exact h1.symm.trans (h2.symm.trans (hVlocus T.unop).symm)

/-- **A fully faithful 1-morphism with an open locus is an open immersion**: every algebraic
space representing a base change of it along a scheme-valued point of the target has open
immersion structural morphism, read as a morphism of algebraic spaces over `S`.

This is the condition of Stacks 04XB at `AlgebraicGeometry.Space.IsOpenImmersion` written out,
which is `AlgebraicGeometry.Stack.IsOpenImmersion` for a 1-morphism of categories fibred in
groupoids; it is written out here so that this module does not have to know about the
2-category of categories fibred in groupoids. -/
theorem isOpenImmersion_of_hasOpenLocus (G : 𝒞 ⥤ᵇ 𝒟)
    (hfull : G.toFunctor.Full) (hfaithful : G.toFunctor.Faithful)
    (hopen : HasOpenLocus B S hS G) :
    ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj),
      y ⋙ 𝒟.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor)
          (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsOpenImmersion B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom := by
  intro U y hy P hP he
  obtain ⟨V, hV, ⟨i⟩⟩ := exists_iso_yoneda_of_equivalenceOver_of_hasOpenLocus B S hS G hfull
    hfaithful hopen U y hy P he.some
  exact isOpenImmersion_algebraicSpaceMap_of_iso_yoneda B S hS U P hP V i hV

end OpenLocus

/-! ### The mechanism at a property of the objects -/

section ObjectProperty

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒟 : BasedCategory.{v₂, u₂} (BigFppfOver B S hS)) (Q : ObjectProperty 𝒟.obj)

/-- The full subcategory of a category over the big fppf site cut out by a property of its
objects, as a category over the big fppf site. -/
def objectPropertySubcategory : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (Q.ι ⋙ 𝒟.p)

/-- The inclusion of that full subcategory, as a 1-morphism of categories over the big fppf
site. -/
def objectPropertyInclusion : objectPropertySubcategory B S hS 𝒟 Q ⥤ᵇ 𝒟 where
  toFunctor := Q.ι
  w := rfl

/-- The inclusion of a full subcategory is full. -/
instance full_objectPropertyInclusion :
    (objectPropertyInclusion B S hS 𝒟 Q).toFunctor.Full :=
  ObjectProperty.full_ι _

/-- The inclusion of a full subcategory is faithful. -/
instance faithful_objectPropertyInclusion :
    (objectPropertyInclusion B S hS 𝒟 Q).toFunctor.Faithful :=
  ObjectProperty.faithful_ι _

/-- An object `T` of the big fppf site of `U` is in the image of the first projection of the
2-fibre product of the inclusion of a full subcategory with a scheme-valued point `y` of `𝒟`
exactly when `y(T)` has the property.  Closure of the property under isomorphisms is what makes
the forward direction work. -/
theorem image_twoFibreProductFst_objectPropertyInclusion
    (hiso : Q.IsClosedUnderIsomorphisms) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj) (hy : y ⋙ 𝒟.p = Over.map U.hom)
    (T : BigFppfOver B U.left.1 U.left.2) :
    (∃ a, (TwoFibreProductOver.fst (Over.map U.hom)
        (objectPropertySubcategory B S hS 𝒟 Q).p 𝒟.p y
        (objectPropertyInclusion B S hS 𝒟 Q).toFunctor).obj a = T) ↔ Q (y.obj T) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact hiso.of_iso a.iso.symm a.y.property
  · intro hT
    exact ⟨{ base := 𝒟.p.obj (y.obj T)
             x := T
             y := ⟨y.obj T, hT⟩
             hx := (congrArg (fun G => G.obj T) hy).symm
             hy := rfl
             iso := Iso.refl _
             vertical := IsHomLift.id rfl }, rfl⟩

/-- **The input of the mechanism, read at a property of the objects.**  Every scheme-valued
point `y` of `𝒟` over an object `U` of the big fppf site cuts out an open subscheme `V` of `U`
through which an object `T` of the big fppf site of `U` maps exactly when `y(T)` has the
property. -/
def HasOpenObjectPropertyLocus : Prop :=
  ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj),
    y ⋙ 𝒟.p = Over.map U.hom →
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ Q (y.obj T)

/-- An open locus for a property of the objects is an open locus for the inclusion of the full
subcategory it cuts out. -/
theorem hasOpenLocus_objectPropertyInclusion (hiso : Q.IsClosedUnderIsomorphisms)
    (hopen : HasOpenObjectPropertyLocus B S hS 𝒟 Q) :
    HasOpenLocus B S hS (objectPropertyInclusion B S hS 𝒟 Q) := by
  intro U y hy
  obtain ⟨V, hV, hVlocus⟩ := hopen U y hy
  exact ⟨V, hV, fun T => (hVlocus T).trans
    (image_twoFibreProductFst_objectPropertyInclusion B S hS 𝒟 Q hiso U y hy T).symm⟩

/-- **The inclusion of a full subcategory with an open locus is representable by algebraic
spaces.** -/
theorem isRepresentableByAlgebraicSpaces_objectPropertyInclusion
    (hiso : Q.IsClosedUnderIsomorphisms) (hopen : HasOpenObjectPropertyLocus B S hS 𝒟 Q) :
    IsRepresentableByAlgebraicSpaces B S hS (objectPropertyInclusion B S hS 𝒟 Q) :=
  isRepresentableByAlgebraicSpaces_of_hasOpenLocus B S hS _
    (full_objectPropertyInclusion B S hS 𝒟 Q) (faithful_objectPropertyInclusion B S hS 𝒟 Q)
    (hasOpenLocus_objectPropertyInclusion B S hS 𝒟 Q hiso hopen)

/-- **The inclusion of a full subcategory with an open locus is an open immersion**, in the
written-out form of the condition of Stacks 04XB. -/
theorem isOpenImmersion_objectPropertyInclusion
    (hiso : Q.IsClosedUnderIsomorphisms) (hopen : HasOpenObjectPropertyLocus B S hS 𝒟 Q) :
    ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj),
      y ⋙ 𝒟.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (objectPropertySubcategory B S hS 𝒟 Q).p 𝒟.p y
            (objectPropertyInclusion B S hS 𝒟 Q).toFunctor)
          (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsOpenImmersion B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom :=
  isOpenImmersion_of_hasOpenLocus B S hS _
    (full_objectPropertyInclusion B S hS 𝒟 Q) (faithful_objectPropertyInclusion B S hS 𝒟 Q)
    (hasOpenLocus_objectPropertyInclusion B S hS 𝒟 Q hiso hopen)

end ObjectProperty


end AlgebraicGeometry.Stack

end
