module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# A monoidal structure descending along a localization is unique

`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` builds a monoidal structure on a
functor `F : D ⥤ E` out of a monoidal structure on a functor `G : C ⥤ E` that `F` lifts along a
monoidal localization `L : C ⥤ D`. It is a construction and says nothing about uniqueness, so a
consumer that obtains a monoidal structure on one and the same functor by two different routes —
one application of `functorMonoidalOfComp`, or a composite of monoidal functors whose underlying
functors happen to be equal — has no way to identify the two. This file supplies the missing
uniqueness.

Two observations make it. First, a lax monoidal structure on `F : D ⥤ E` is determined by its
unit together with its tensorator **on the essential image of any essentially surjective
`L : C ⥤ D`**: the tensorator is natural in both arguments, so its value at an arbitrary pair of
objects is conjugate to its value at a pair in the image. Second, when `F` lifts `G` along `L`,
the requirement that the lifting isomorphism `L ⋙ F ≅ G` be a *monoidal* natural transformation
pins the unit of `F` and the tensorator of `F` at the image of `L` — because every other factor
in the two coherence equations is invertible. Together these say that at most one lax monoidal
structure on `F` makes the lifting isomorphism monoidal, and `Localization.Monoidal`
`.lifting_isMonoidal` says that the structure produced by `functorMonoidalOfComp` does.

## Main results

* `CategoryTheory.Functor.laxMonoidal_ext`: two lax monoidal structures on `F : D ⥤ E` whose
  units agree and whose tensorators agree on the essential image of an essentially surjective
  `L : C ⥤ D` are equal.
* `CategoryTheory.Localization.Monoidal.laxMonoidal_ext_of_isMonoidal`: **at most one lax
  monoidal structure on `F` makes the lifting isomorphism `L ⋙ F ≅ G` monoidal.**
* `CategoryTheory.Localization.Monoidal.laxMonoidal_eq_functorMonoidalOfComp` and
  `monoidal_eq_functorMonoidalOfComp`: **that structure is the one built by
  `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`**, which is the form in which the
  uniqueness is used: a monoidal structure obtained any other way, for which the lifting
  isomorphism is monoidal, is equal to it.

## Implementation notes

The oplax half of a monoidal structure carries no freedom beyond the lax half, by
`CategoryTheory.Functor.Monoidal.toLaxMonoidal_injective`, so only the lax statement is proved
in general and the monoidal one is obtained through that injectivity where it is needed.

The two structures being compared cannot both be instances, so they are bound as ordinary
hypotheses and the unit and the tensorator are addressed by `@CategoryTheory.Functor`
`.LaxMonoidal.ε` and `@CategoryTheory.Functor.LaxMonoidal.μ` with the structure supplied
explicitly. In the statements where only one of the two is abstract — everything downstream of
`laxMonoidal_ext_of_isMonoidal` — the hypothesis that the lifting isomorphism is monoidal is
written with `letI` in the statement, as Mathlib's `Localization.Monoidal.functorMonoidalOfComp_ε`
already does, so that the reader sees `(Lifting.iso L W G F).hom.IsMonoidal` and not a chain of
instance arguments.

`laxMonoidal_ext` asks only for `L.EssSurj`, not for `L.IsLocalization W`: essential
surjectivity is the whole of what the naturality argument uses, and a localization functor has
it (`CategoryTheory.Localization.essSurj`). Stating it at that strength is what lets the lemma be
used for a comparison functor that is not presented as a localization.

No monoidal coherence is reproved: `ε` and `μ` are the only fields of
`CategoryTheory.Functor.LaxMonoidal` carrying data, so the generated `ext` lemma reduces the
equality of two structures to those two, and the `Prop`-valued fields follow.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

omit [MonoidalCategory C] in
/-- **A lax monoidal structure is determined by its unit and by its tensorator on the essential
image of an essentially surjective functor.** The tensorator is natural in both arguments, so for
arbitrary objects `Y₁`, `Y₂` of `D` it is conjugate by `F.map` of the chosen isomorphisms
`L.obj (L.objPreimage Yᵢ) ≅ Yᵢ` to its value at a pair of objects in the image of `L`. -/
theorem Functor.laxMonoidal_ext (L : C ⥤ D) [L.EssSurj] {F : D ⥤ E} {h₁ h₂ : F.LaxMonoidal}
    (hε : @ε _ _ _ _ _ _ F h₁ = @ε _ _ _ _ _ _ F h₂)
    (hμ : ∀ X Y : C, @μ _ _ _ _ _ _ F h₁ (L.obj X) (L.obj Y)
      = @μ _ _ _ _ _ _ F h₂ (L.obj X) (L.obj Y)) : h₁ = h₂ := by
  ext
  · exact hε
  case _ Y₁ Y₂ =>
    have e₁ := L.objObjPreimageIso Y₁
    have e₂ := L.objObjPreimageIso Y₂
    refine (cancel_epi ((F.mapIso e₁) ⊗ᵢ (F.mapIso e₂)).hom).mp ?_
    exact (@μ_natural _ _ _ _ _ _ F h₁ _ _ _ _ e₁.hom e₂.hom).trans
      ((congrArg (· ≫ F.map (e₁.hom ⊗ₘ e₂.hom)) (hμ _ _)).trans
        (@μ_natural _ _ _ _ _ _ F h₂ _ _ _ _ e₁.hom e₂.hom).symm)


namespace Localization.Monoidal

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Monoidal]
  (F : D ⥤ E) (G : C ⥤ E) [G.Monoidal] [W.ContainsIdentities] [Lifting L W G F]

omit [W.ContainsIdentities] in
/-- **At most one lax monoidal structure on `F` makes the lifting isomorphism monoidal.** The
unit condition reads `ε F ≫ F.map (ε L) ≫ e.hom.app (𝟙_ C) = ε G` and the tensor condition reads
`μ F (L.obj X) (L.obj Y) ≫ F.map (μ L X Y) ≫ e.hom.app (X ⊗ Y) = (e.hom.app X ⊗ₘ e.hom.app Y) ≫
μ G X Y`, where `e` is the lifting isomorphism; in each the factor to the right of the structure
being determined is invertible, `L` being monoidal, so the structure is pinned — at the unit and
at the essential image of `L`, which by `CategoryTheory.Functor.laxMonoidal_ext` is everywhere. -/
theorem laxMonoidal_ext_of_isMonoidal {h₁ h₂ : F.LaxMonoidal}
    (hm₁ : letI := h₁; (Lifting.iso L W G F).hom.IsMonoidal)
    (hm₂ : letI := h₂; (Lifting.iso L W G F).hom.IsMonoidal) : h₁ = h₂ := by
  have := Localization.essSurj L W
  refine Functor.laxMonoidal_ext L ?_ (fun X Y => ?_)
  · refine (cancel_mono (F.map (ε L) ≫ (Lifting.iso L W G F).hom.app (𝟙_ C))).mp ?_
    rw [← Category.assoc, ← Category.assoc]
    exact hm₁.unit.trans hm₂.unit.symm
  · refine (cancel_mono (F.map (μ L X Y) ≫ (Lifting.iso L W G F).hom.app (X ⊗ Y))).mp ?_
    rw [← Category.assoc, ← Category.assoc]
    exact (hm₁.tensor X Y).trans (hm₂.tensor X Y).symm

/-- **A lax monoidal structure on `F` for which the lifting isomorphism is monoidal is the one
built by `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`.** -/
theorem laxMonoidal_eq_functorMonoidalOfComp {h : F.LaxMonoidal}
    (hm : letI := h; (Lifting.iso L W G F).hom.IsMonoidal) :
    h = (functorMonoidalOfComp L W F G).toLaxMonoidal :=
  laxMonoidal_ext_of_isMonoidal L W F G hm (lifting_isMonoidal L W F G)

/-- **Uniqueness of a monoidal lift along a monoidal localization:** a monoidal structure on `F`
for which the lifting isomorphism `L ⋙ F ≅ G` is monoidal is
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`. This is the form the uniqueness is
used in: a monoidal structure on `F` reached by some other construction is compared with the
lifted one by checking the two coherence equations of the lifting isomorphism, which mention no
monoidal structure on `F` beyond its unit and tensorator. -/
theorem monoidal_eq_functorMonoidalOfComp {h : F.Monoidal}
    (hm : letI := h; (Lifting.iso L W G F).hom.IsMonoidal) :
    h = functorMonoidalOfComp L W F G :=
  Functor.Monoidal.toLaxMonoidal_injective F
    (laxMonoidal_eq_functorMonoidalOfComp L W F G hm)

end Localization.Monoidal

end CategoryTheory
