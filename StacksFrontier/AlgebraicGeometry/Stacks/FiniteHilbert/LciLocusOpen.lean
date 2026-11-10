module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubschemeLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedRefinable

/-!
# The local complete intersection locus is an open substack of the finite Hilbert stack

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
which is representable by algebraic spaces, flat and locally of finite presentation, and let `d`
be a natural number. **Stacks 06CL** says that the local complete intersection locus
`ℋ_{d,lci}(𝒳/𝒴)` of Stacks 06CJ is a stack in groupoids and that its inclusion into the relative
finite Hilbert category `ℋ_d(𝒳/𝒴)` is representable and an open immersion.

The source argues as follows. An object `Ξ = (U, Z, y, x, α)` of `ℋ_d(𝒳/𝒴)` has `Z ⟶ U` finite
locally free, hence flat, locally of finite presentation and universally closed, and `X_y ⟶ U`
flat and locally of finite presentation by the hypotheses on `F`; so Stacks 05X8 and Stacks 06CE
produce an open subscheme `W ⊆ U` through which a morphism `U' ⟶ U` factors exactly when the base
change of the relative map `x_α` of Stacks 06CK is unramified and a local complete intersection
morphism — that is, by the remark following Stacks 06CK, exactly when the pullback of `Ξ` lies in
the locus. The 2-fibre product `(Sch/U)_{fppf} ×_{Ξ, ℋ_d(𝒳/𝒴)} ℋ_{d,lci}(𝒳/𝒴)` is therefore
represented by `W`, which gives representability and the open-immersion property, and the
stack-in-groupoids assertion then follows from Stacks 05UN.

## The hypotheses this file carries

**Stacks 06CE**, the local-complete-intersection analogue of Stacks 05X8, is available, as
`AlgebraicGeometry.Space.exists_isOpenSubspace_factorsThrough_iff_isLocalCompleteIntersection` of
the module `KoszulLocusOnBaseUnconditional` of the directory
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection`;
what it produces is an open *subspace* of an algebraic space, whereas the source's third step
needs an open *subscheme* of `U` cutting out the conjunction of the two conditions on the
relative map of Stacks 06CK. That conjunction is carried as the explicit hypothesis
`AlgebraicGeometry.Stack.FiniteHilbert.HasOpenLciLocus`, which is exactly the output of the
source's steps 1-3. Invariance of membership of the locus under
isomorphism in `ℋ_d(𝒳/𝒴)` — the independence-of-choice remark following Stacks 06CK, which here
means transporting a `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData` across an
isomorphism of base objects of the site — is carried as
`CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms` of the locus. Finally **Stacks 05UN**,
that a 1-morphism representable by algebraic spaces into a stack in groupoids has source a stack
in groupoids, is carried for the full subcategories of `ℋ_d(𝒳/𝒴)`, together with the standing
fact that `ℋ_d(𝒳/𝒴)` is itself a stack in groupoids.

## Main definitions

* `AlgebraicGeometry.Stack.FiniteHilbert.HasOpenLciLocus`: the open locus cut out on the base of
  a scheme-valued point of `ℋ_d(𝒳/𝒴)` by membership of the local complete intersection locus.

## Main results

* `AlgebraicGeometry.Stack.exists_isOpenImmersion_representing_lciFiniteHilbertInclusion`:
  **Stacks 06CL**, the inclusion `ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)` is representable, by an open
  subscheme of the base.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_lciFiniteHilbertInclusion`:
  **Stacks 06CL**, that inclusion is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isOpenImmersion_lciFiniteHilbertInclusion`: **Stacks 06CL**, that
  inclusion is an open immersion.
* `AlgebraicGeometry.Stack.isStackInGroupoids_lciFiniteHilbertCategory`: **Stacks 06CL**,
  `ℋ_{d,lci}(𝒳/𝒴)` is a stack in groupoids.

## Implementation notes

Representability is the comparison of two categories over the big fppf site of the base: the
first projection of the 2-fibre product of the inclusion with a scheme-valued point of
`ℋ_d(𝒳/𝒴)`, which is fully faithful because the inclusion of a full subcategory is, and the
category of elements of the sheaf of points of the open subscheme `W`, whose projection is fully
faithful because there is at most one morphism to `W` over `U`. Two fully faithful categories
over a base with the same image on objects are equivalent over it, and the image of the first
projection is exactly the locus — this is where invariance under isomorphism enters. The same
comparison identifies *every* algebraic space representing the 2-fibre product with `W`, which is
what the open-immersion condition of Stacks 04XB quantifies over: both presheaves take
subsingleton values and have the same support, so they are isomorphic.

The open-immersion conclusion is `AlgebraicGeometry.Stack.IsOpenImmersion` written out, because
that predicate takes a 1-morphism of the 2-category of categories fibred in groupoids while the
fibred-in-groupoids structure of the locus is itself part of what is being proved here; the
inclusion is therefore handled as the `CategoryTheory.BasedFunctor`
`AlgebraicGeometry.Stack.lciFiniteHilbertInclusion` throughout. The structural morphism the
condition tests is the one of Stacks 04SG, replaced by
`CategoryTheory.OverShriek.relocalizeToYoneda` through
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`, which is the form in which the
identification of the representing presheaf with `W` can be used.

Flatness and local finite presentation of `F` are the standing hypotheses of the source's
section; they enter only through `AlgebraicGeometry.Stack.FiniteHilbert.HasOpenLciLocus`, where
Stacks 05X8 and Stacks 06CE are applied, and are therefore unused arguments below. They are
retained because the source imposes them, and are spelled in the written-out form of Stacks 03YK
at flatness and at local finite presentation of morphisms of algebraic spaces.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
* [Stacks Project, Tag 05X8](https://stacks.math.columbia.edu/tag/05X8)
* [Stacks Project, Tag 06CE](https://stacks.math.columbia.edu/tag/06CE)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

/-! ### Comparison of two categories over a base -/

section Comparison

universe v

variable {C A D E : Type*} [Category C] [Category A] [Category D] [Category E]

/-- The first projection of a 2-fibre product over the base is faithful as soon as the second
leg is: a morphism of the 2-fibre product is determined by its first component. -/
private theorem faithful_twoFibreProductFst (p : A ⥤ C) (q : D ⥤ C) (r : E ⥤ C)
    (G₁ : A ⥤ E) (G₂ : D ⥤ E) [G₂.Faithful] :
    (TwoFibreProductOver.fst p q r G₁ G₂).Faithful where
  map_injective {X Y} f g h := by
    apply TwoFibreProductOver.Hom.ext' h
    apply G₂.map_injective
    apply (cancel_epi X.iso.hom).mp
    rw [← f.w, ← g.w]
    exact congrArg (fun a => G₁.map a ≫ Y.iso.hom) h

/-- The first projection of a 2-fibre product over the base is full as soon as the second leg is
fully faithful. -/
private theorem full_twoFibreProductFst (p : A ⥤ C) (q : D ⥤ C) (r : E ⥤ C)
    (G₁ : A ⥤ E) (G₂ : D ⥤ E) (hG₁ : G₁ ⋙ r = p) (hG₂ : G₂ ⋙ r = q)
    [G₂.Full] [G₂.Faithful] : (TwoFibreProductOver.fst p q r G₁ G₂).Full where
  map_surjective {X Y} a := by
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
    simp

/-- A fully faithful functor over the base whose image contains the image of another one receives
a 1-morphism over the base from it. -/
private theorem nonempty_morphismOver_of_image_subset (p : A ⥤ C) (q : D ⥤ C) [q.Full]
    [q.Faithful] (h : ∀ a, ∃ e, q.obj e = p.obj a) :
    Nonempty (StacksRepresentableCFG.MorphismOver p q) := by
  classical
  choose obj ho using h
  let G : A ⥤ D :=
    { obj := obj
      map := fun {a b} f => q.preimage (eqToHom (ho a) ≫ p.map f ≫ eqToHom (ho b).symm)
      map_id := by intro a; apply q.map_injective; simp
      map_comp := by intro a b c f g; apply q.map_injective; simp }
  refine ⟨G, CategoryTheory.Functor.ext ho ?_⟩
  intro a b f
  change q.map (q.preimage _) = _
  simp

/-- Two fully faithful functors over the base with the same image are equivalent over the
base. -/
private theorem nonempty_equivalenceOver_of_image_eq (p : A ⥤ C) (q : D ⥤ C) [p.Full]
    [p.Faithful] [q.Full] [q.Faithful]
    (h : ∀ c, (∃ a, p.obj a = c) ↔ ∃ e, q.obj e = c) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver p q) := by
  obtain ⟨G₁⟩ := nonempty_morphismOver_of_image_subset p q (fun a => (h _).mp ⟨a, rfl⟩)
  obtain ⟨G₂⟩ := nonempty_morphismOver_of_image_subset q p (fun e => (h _).mpr ⟨e, rfl⟩)
  have hu : (G₁.functor ⋙ G₂.functor) ⋙ p = p := by rw [Functor.assoc, G₂.w, G₁.w]
  have hc : (G₂.functor ⋙ G₁.functor) ⋙ q = q := by rw [Functor.assoc, G₁.w, G₂.w]
  let η : 𝟭 A ≅ G₁.functor ⋙ G₂.functor :=
    (Functor.FullyFaithful.ofFullyFaithful ((Functor.whiskeringRight A A C).obj p)).preimageIso
      (eqToIso (by change 𝟭 A ⋙ p = (G₁.functor ⋙ G₂.functor) ⋙ p; rw [Functor.id_comp, hu]))
  let ε : G₂.functor ⋙ G₁.functor ≅ 𝟭 D :=
    (Functor.FullyFaithful.ofFullyFaithful ((Functor.whiskeringRight D D C).obj q)).preimageIso
      (eqToIso (by change (G₂.functor ⋙ G₁.functor) ⋙ q = 𝟭 D ⋙ q; rw [Functor.id_comp, hc]))
  refine ⟨G₁, G₂, η, ε, ?_, ?_⟩
  · exact (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringRight A A C).obj p)).map_preimage _
  · exact (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringRight D D C).obj q)).map_preimage _

attribute [local implicit_reducible] Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc

/-- The projection from the category of elements of a presheaf of sets is faithful. -/
private theorem faithful_elementsProjection (P : Cᵒᵖ ⥤ Type*) :
    (presheafOfCategories (P ⋙ typeToCat)).p.Faithful where
  map_injective {X Y} f g h := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ h
    exact @Subsingleton.elim (Discrete.mk X.fiber.as ⟶
      Discrete.mk (P.map f.base.op Y.fiber.as)) inferInstance _ _

/-- The projection from the category of elements of a subsingleton-valued presheaf is full. -/
private theorem full_elementsProjection (P : Cᵒᵖ ⥤ Type*)
    (hP : ∀ X, Subsingleton (P.obj X)) :
    (presheafOfCategories (P ⋙ typeToCat)).p.Full where
  map_surjective {X Y} f := by
    refine ⟨⟨f, ?_⟩, rfl⟩
    exact eqToHom (by
      apply Discrete.ext
      exact (hP _).elim _ _)

/-- An object of the base is in the image of the projection from the category of elements of a
presheaf exactly when the presheaf has a section over it. -/
private theorem image_elementsProjection (P : Cᵒᵖ ⥤ Type*) (X : C) :
    (∃ a, (presheafOfCategories (P ⋙ typeToCat)).p.obj a = X) ↔
      Nonempty (P.obj (Opposite.op X)) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.fiber.as⟩
  · rintro ⟨a⟩
    exact ⟨⟨X, Discrete.mk a⟩, rfl⟩

/-- A presheaf whose category of elements has full projection takes subsingleton values. -/
private theorem subsingleton_of_full_elementsProjection (P : Cᵒᵖ ⥤ Type*)
    [(presheafOfCategories (P ⋙ typeToCat)).p.Full] (X : Cᵒᵖ) : Subsingleton (P.obj X) := by
  constructor
  intro a b
  let A : (presheafOfCategories (P ⋙ typeToCat)).obj := ⟨X.unop, Discrete.mk a⟩
  let D : (presheafOfCategories (P ⋙ typeToCat)).obj := ⟨X.unop, Discrete.mk b⟩
  obtain ⟨m, hm⟩ := (presheafOfCategories (P ⋙ typeToCat)).p.map_surjective
    (X := A) (Y := D) (𝟙 X.unop)
  have he : a = P.map m.base.op b := Discrete.eq_of_hom m.fiber
  change m.base = 𝟙 X.unop at hm
  rw [hm] at he
  change a = P.map (𝟙 X) b at he
  simpa only [P.map_id, types_id_apply] using he

/-- An equivalence over the base has the same image on objects. -/
private theorem image_equivalenceOver {p : A ⥤ C} {q : D ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver p q) (c : C) :
    (∃ a, p.obj a = c) ↔ ∃ b, q.obj b = c := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e.hom.functor.obj a, congrArg (fun G => G.obj a) e.hom.w⟩
  · rintro ⟨b, rfl⟩
    exact ⟨e.inv.functor.obj b, congrArg (fun G => G.obj b) e.inv.w⟩

/-- Fullness transports along an equivalence over the base. -/
private theorem full_of_equivalenceOver {p : A ⥤ C} {q : D ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver p q) [p.Full] : q.Full := by
  have : e.inv.functor.Full := by
    change e.toEquivalence.inverse.Full
    infer_instance
  rw [← e.inv.w]
  infer_instance

end Comparison

/-! ### Stacks 06CL -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

/-- The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)` is full, being the inclusion of a full
subcategory. -/
private instance full_lciFiniteHilbertInclusion :
    (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).toFunctor.Full :=
  ObjectProperty.full_ι _

/-- The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)` is faithful, being the inclusion of a full
subcategory. -/
private instance faithful_lciFiniteHilbertInclusion :
    (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).toFunctor.Faithful :=
  ObjectProperty.faithful_ι _

namespace FiniteHilbert

/-- **The output of the first three steps of the proof of Stacks 06CL.** Every scheme-valued
point `y` of `ℋ_d(𝒳/𝒴)` over an object `U` of the big fppf site cuts out an open subscheme `V`
of `U` through which an object `T` of the big fppf site of `U` maps exactly when the object
`y(T)` of `ℋ_d(𝒳/𝒴)` lies in the local complete intersection locus.

For a 1-morphism `F` which is flat and locally of finite presentation this is Stacks 05X8 and
Stacks 06CE applied to the relative map of Stacks 06CK, read through the base-change criterion
following that tag. -/
def HasOpenLciLocus (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
      (BigFppfOver.topology B S hS))
    (F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory) (d : ℕ) : Prop :=
  ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ Object B S hS 𝒳 𝒴 F d),
    y ⋙ finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d) = Over.map U.hom →
      ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
        ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ lciLocus (y.obj T)

/-- For a scheme-valued point `y` of `ℋ_d(𝒳/𝒴)`, the first projection of the 2-fibre product of
the inclusion of the local complete intersection locus with `y` is full, and its image consists of
the objects `T` of the big fppf site of `U` mapping to the open subscheme `V` cut out by the
locus. -/
private theorem exists_isOpenImmersion_full_image_twoFibreProductFst
    (hiso : ObjectProperty.IsClosedUnderIsomorphisms
      (lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)))
    (hopen : HasOpenLciLocus B S hS 𝒳 𝒴 F d) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).obj)
    (hy : y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      (TwoFibreProductOver.fst (Over.map U.hom)
        (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).p
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).p y
        (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).toFunctor).Full ∧
      ∀ T, (∃ a, (TwoFibreProductOver.fst (Over.map U.hom)
        (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).p
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).p y
        (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).toFunctor).obj a = T) ↔ Nonempty (T ⟶ V) := by
  obtain ⟨V, hV, hVlocus⟩ := hopen U y hy
  refine ⟨V, hV, full_twoFibreProductFst (Over.map U.hom)
    (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p
    (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
    y (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).toFunctor hy rfl, fun T ↦ ?_⟩
  rw [hVlocus T]
  constructor
  · rintro ⟨a, rfl⟩
    exact hiso.of_iso a.iso.symm a.y.property
  · intro hT
    refine ⟨{ base := (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
                (F := F) (d := d)).p.obj (y.obj T)
              x := T
              y := ⟨y.obj T, hT⟩
              hx := (congrArg (fun G => G.obj T) hy).symm
              hy := rfl
              iso := Iso.refl _
              vertical := IsHomLift.id rfl }, rfl⟩

end FiniteHilbert

/-- The 2-fibre product of the inclusion of the local complete intersection locus with a
scheme-valued point of `ℋ_d(𝒳/𝒴)` is equivalent, over the big fppf site of the base, to the
category of elements of the sheaf of points of the open subscheme cut out by the locus.

The first projection of the 2-fibre product is fully faithful because the inclusion of a full
subcategory is, and the category of elements of the sheaf of points of that open subscheme has
fully faithful projection because there is at most one morphism to an open subscheme; the two
have the same image on objects, so they are equivalent over the big fppf site of the base. -/
private theorem exists_isOpenImmersion_equivalenceOver_lciFiniteHilbertInclusion
    (hiso : ObjectProperty.IsClosedUnderIsomorphisms
      (FiniteHilbert.lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)))
    (hopen : FiniteHilbert.HasOpenLciLocus B S hS 𝒳 𝒴 F d) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).obj)
    (hy : y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom)
          (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
            (d := d)).p
          (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
            (d := d)).p y
          (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
            (d := d)).toFunctor)
        (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p) := by
  obtain ⟨V, hV, _, himg⟩ :=
    FiniteHilbert.exists_isOpenImmersion_full_image_twoFibreProductFst hiso hopen U y hy
  have _ := faithful_twoFibreProductFst (Over.map U.hom)
    (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p
    (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
    y (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).toFunctor
  have _ := full_elementsProjection (yoneda.obj V)
    (fun T ↦ subsingleton_hom_of_isOpenImmersion B S hS U V hV T.unop)
  have _ := faithful_elementsProjection (yoneda.obj V)
  refine ⟨V, hV, nonempty_equivalenceOver_of_image_eq _ _ fun T ↦ ?_⟩
  rw [himg, image_elementsProjection]

/-- **Stacks 06CL.** The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of the local complete
intersection locus is representable: every 2-fibre product of it with a scheme-valued point of
`ℋ_d(𝒳/𝒴)` is represented by an object of the big fppf site of the base which is an open
subscheme of it, namely the open subscheme cut out by the locus. -/
@[stacks 06CL "the inclusion ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴) is representable by an open subscheme \
of the base, with the open locus of Stacks 05X8 and 06CE and isomorphism-invariance of the \
locus as explicit hypotheses"]
theorem exists_isOpenImmersion_representing_lciFiniteHilbertInclusion
    (_hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (_hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (_hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hiso : ObjectProperty.IsClosedUnderIsomorphisms
      (FiniteHilbert.lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)))
    (hopen : FiniteHilbert.HasOpenLciLocus B S hS 𝒳 𝒴 F d) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).obj),
      y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)).p = Over.map U.hom →
      ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p
            (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p y
            (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).toFunctor)
          (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p) :=
  exists_isOpenImmersion_equivalenceOver_lciFiniteHilbertInclusion hiso hopen

/-- **Stacks 06CL.** The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of the local complete
intersection locus is representable by algebraic spaces, the representing algebraic space of a
base change being the open subscheme of the base cut out by the locus. -/
@[stacks 06CL "the inclusion ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴) is representable by algebraic spaces, \
with the open locus of Stacks 05X8 and 06CE and isomorphism-invariance of the locus as explicit \
hypotheses"]
theorem isRepresentableByAlgebraicSpaces_lciFiniteHilbertInclusion
    (_hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (_hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (_hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hiso : ObjectProperty.IsClosedUnderIsomorphisms
      (FiniteHilbert.lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)))
    (hopen : FiniteHilbert.HasOpenLciLocus B S hS 𝒳 𝒴 F d) :
    IsRepresentableByAlgebraicSpaces B S hS
      (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)) := by
  intro U
  dsimp only
  intro y hy
  obtain ⟨V, _, he⟩ :=
    exists_isOpenImmersion_equivalenceOver_lciFiniteHilbertInclusion hiso hopen U y hy
  exact ⟨yoneda.obj V, isAlgebraicSpace_yoneda B U.left.1 U.left.2 V, he⟩

/-- Every algebraic space representing a base change of the inclusion of the local complete
intersection locus along a scheme-valued point of `ℋ_d(𝒳/𝒴)` is the open subscheme of the base
cut out by the locus: both presheaves take subsingleton values and have the same support. -/
private theorem exists_iso_yoneda_of_equivalenceOver_lciFiniteHilbertInclusion
    (hiso : ObjectProperty.IsClosedUnderIsomorphisms
      (FiniteHilbert.lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)))
    (hopen : FiniteHilbert.HasOpenLciLocus B S hS 𝒳 𝒴 F d) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).obj)
    (hy : y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p = Over.map U.hom)
    (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom)
        (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).p
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).p y
        (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).toFunctor)
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      Nonempty (P ≅ yoneda.obj V) := by
  obtain ⟨V, hV, _, himg⟩ :=
    FiniteHilbert.exists_isOpenImmersion_full_image_twoFibreProductFst hiso hopen U y hy
  have _ := full_of_equivalenceOver e
  refine ⟨V, hV, nonempty_iso_of_subsingleton P (yoneda.obj V)
    (subsingleton_of_full_elementsProjection P)
    (fun T ↦ subsingleton_hom_of_isOpenImmersion B S hS U V hV T.unop) ?_⟩
  intro T
  rw [← image_elementsProjection P T.unop, ← image_equivalenceOver e T.unop, himg]

/-- **Stacks 06CL.** The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of the local complete
intersection locus is an open immersion: every algebraic space representing a base change of it
along a scheme-valued point of `ℋ_d(𝒳/𝒴)` has open immersion structural morphism, read as a
morphism of algebraic spaces over `S`.

This is the condition of Stacks 04XB at `AlgebraicGeometry.Space.IsOpenImmersion`, written out,
and the representing algebraic space is the open subscheme of the base cut out by the locus. -/
@[stacks 06CL "the inclusion ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴) is an open immersion, with the open \
locus of Stacks 05X8 and 06CE and isomorphism-invariance of the locus as explicit hypotheses"]
theorem isOpenImmersion_lciFiniteHilbertInclusion
    (_hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (_hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (_hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hiso : ObjectProperty.IsClosedUnderIsomorphisms
      (FiniteHilbert.lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)))
    (hopen : FiniteHilbert.HasOpenLciLocus B S hS 𝒳 𝒴 F d) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).obj),
      y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)).p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p
            (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p y
            (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).toFunctor)
          (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsOpenImmersion B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom := by
  intro U y hy P hP he
  obtain ⟨V, hV, ⟨i⟩⟩ := exists_iso_yoneda_of_equivalenceOver_lciFiniteHilbertInclusion hiso
    hopen U y hy P he.some
  exact isOpenImmersion_algebraicSpaceMap_of_iso_yoneda B S hS U P hP V i hV

/-- **Stacks 06CL.** The local complete intersection locus `ℋ_{d,lci}(𝒳/𝒴)` is a stack in
groupoids over the big fppf site of `S`.

By Stacks 05UN this follows from the representability by algebraic spaces of the inclusion into
`ℋ_d(𝒳/𝒴)` together with `ℋ_d(𝒳/𝒴)` being a stack in groupoids. -/
@[stacks 06CL "ℋ_{d,lci}(𝒳/𝒴) is a stack in groupoids, with Stacks 05UN for the full \
subcategories of ℋ_d(𝒳/𝒴), that ℋ_d(𝒳/𝒴) is a stack in groupoids, the open locus of Stacks \
05X8 and 06CE and isomorphism-invariance of the locus as explicit hypotheses"]
theorem isStackInGroupoids_lciFiniteHilbertCategory
    (hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hiso : ObjectProperty.IsClosedUnderIsomorphisms
      (FiniteHilbert.lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)))
    (hopen : FiniteHilbert.HasOpenLciLocus B S hS 𝒳 𝒴 F d)
    (hHd : Functor.IsStackInGroupoids.{w}
      (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
      (BigFppfOver.topology B S hS))
    (h05UN : ∀ (Q : ObjectProperty (FiniteHilbert.Object B S hS 𝒳 𝒴 F d))
      (j : BasedCategory.ofFunctor (Q.ι ⋙ finiteHilbertProjection (B := B) (S := S) (hS := hS)
            (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) ⥤ᵇ
          finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
            (d := d)),
      IsRepresentableByAlgebraicSpaces B S hS j →
      Functor.IsStackInGroupoids.{w}
        (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)) (BigFppfOver.topology B S hS) →
      Functor.IsStackInGroupoids.{w}
        (Q.ι ⋙ finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)) (BigFppfOver.topology B S hS)) :
    Functor.IsStackInGroupoids.{w}
      (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)).p (BigFppfOver.topology B S hS) :=
  h05UN (FiniteHilbert.lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
    (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
    (isRepresentableByAlgebraicSpaces_lciFiniteHilbertInclusion hFrep hFflat hFlfp hiso hopen)
    hHd

end AlgebraicGeometry.Stack

end
