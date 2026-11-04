module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Basic

/-!
# The diagram of finite Hilbert stacks

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. Specialising the relative finite Hilbert category `ℋ_d(𝒳/𝒴)`
of `AlgebraicGeometry.Stack.FiniteHilbert.Object` along `𝒴 = S` and along `𝒳 = 𝒴 = S` produces
two further categories over the site: the *absolute finite Hilbert category* `ℋ_d(𝒳)`, whose
objects are a degree-`d` finite locally free cover `Z ⟶ U` together with an object of `𝒳` over
`Z`, and the category `ℋ_d` of degree-`d` finite locally free covers alone.

Forgetting the data that distinguishes the three categories gives the commutative diagram of
Stacks 05WD: the relative finite Hilbert category maps to the target stack `𝒴` and to the
absolute finite Hilbert category, the latter maps to `ℋ_d`, and the resulting composite
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d` is the arrow that reads off the underlying cover.

## Main definitions

* `AlgebraicGeometry.Stack.FiniteCover`: a degree-`d` finite locally free cover, an object of
  `ℋ_d`.
* `AlgebraicGeometry.Stack.finiteCoverCategory`: `ℋ_d` as a category over the big fppf site.
* `AlgebraicGeometry.Stack.AbsoluteHilbert.Object`: such a cover together with an object of `𝒳`
  over it, an object of `ℋ_d(𝒳)`.
* `AlgebraicGeometry.Stack.absoluteHilbertCategory`: `ℋ_d(𝒳)` as a category over the big fppf
  site.
* `AlgebraicGeometry.Stack.forgetRelativeStructure`, `AlgebraicGeometry.Stack.forgetTarget`,
  `AlgebraicGeometry.Stack.forgetAbsoluteStructure` and
  `AlgebraicGeometry.Stack.forgetRelativeToFiniteCover`: **Stacks 05WD**, the four 1-morphisms of
  the diagram.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInGroupoids_finiteCoverProjection` and
  `AlgebraicGeometry.Stack.isFiberedInGroupoids_absoluteHilbertProjection`: both categories are
  fibred in groupoids over the big fppf site.
* `AlgebraicGeometry.Stack.forgetRelativeToFiniteCover_eq_comp`: the triangle of Stacks 05WD
  commutes.

## Implementation notes

Taking `𝒴 = S` in the relative finite Hilbert category leaves the object `y` over `U` and the
identification of `F x` with its restriction determined up to unique isomorphism, so the
remaining data is a cover together with an object of `𝒳` over it; taking `𝒳 = 𝒴 = S` leaves the
cover alone. The two categories are therefore defined directly, by the data that survives,
rather than through the category over the site represented by `S`.

A morphism of either category carries the condition that its cover component present the source
cover as the fibre product of the target cover with the source base, and — in the absolute case
— a morphism of the objects of `𝒳` lying over that cover component. As in
`AlgebraicGeometry.Stack.FiniteHilbert.Hom`, no isomorphism condition is imposed on that
morphism, because a morphism of a category fibred in groupoids lying over an isomorphism is
automatically one.

The fourth arrow is defined outright, by reading off the underlying cover, and
`AlgebraicGeometry.Stack.forgetRelativeToFiniteCover_eq_comp` then states that it agrees with
the composite of the first and the third; commutativity of the diagram is thus a proved
statement rather than a definition.

## References

* [Stacks Project, Tag 05WC](https://stacks.math.columbia.edu/tag/05WC)
* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ)
  (𝒳 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS))

/-- An object of the category `ℋ_d` of degree-`d` finite locally free covers in the big fppf
site of `S`: an object `U` of the site and an object `Z` of the site which is finite locally
free of degree `d` over `U`. -/
structure FiniteCover where
  /-- The base object of the big fppf site. -/
  U : BigFppfOver B S hS
  /-- The covering object of the big fppf site. -/
  Z : BigFppfOver B S hS
  /-- The structure morphism of the cover. -/
  q : Z ⟶ U
  /-- The cover is finite locally free of degree `d`. -/
  finiteLocallyFree : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
    ((BigFppfOver.toScheme B S hS).map q) d

/-- An object of the absolute finite Hilbert category `ℋ_d(𝒳)` of a stack in groupoids `𝒳`: a
degree-`d` finite locally free cover `Z ⟶ U` together with an object of `𝒳` over `Z`. -/
structure AbsoluteHilbert.Object extends FiniteCover B S hS d where
  /-- The object of `𝒳` lying over the cover. -/
  x : 𝒳.toBasedCategory.obj
  /-- The object `x` lies over `Z`. -/
  x_over : 𝒳.toBasedCategory.p.obj x = Z

variable {B S hS d 𝒳}

/-! ### The category of finite locally free covers -/

/-- A morphism of degree-`d` finite locally free covers: a morphism of base objects together
with a morphism of covers presenting the source cover as the fibre product of the target cover
with the source base. -/
structure FiniteCover.Hom (P Q : FiniteCover B S hS d) where
  /-- The morphism of base objects. -/
  f : P.U ⟶ Q.U
  /-- The morphism of covers. -/
  g : P.Z ⟶ Q.Z
  /-- The morphism of covers presents `P.Z` as `Q.Z ×_{Q.U} P.U`. -/
  square : IsPullback g P.q Q.q f

namespace FiniteCover

/-- Two morphisms of finite locally free covers agree as soon as their two components do. -/
@[ext]
theorem Hom.ext {P Q : FiniteCover B S hS d} {φ ψ : Hom P Q} (hf : φ.f = ψ.f)
    (hg : φ.g = ψ.g) : φ = ψ := by
  cases φ; cases ψ; cases hf; cases hg; rfl

/-- Composition of morphisms of finite locally free covers is componentwise. -/
instance categoryStruct : CategoryStruct (FiniteCover B S hS d) where
  Hom := Hom
  id P := ⟨𝟙 P.U, 𝟙 P.Z, IsPullback.id_horiz P.q⟩
  comp φ ψ := ⟨φ.f ≫ ψ.f, φ.g ≫ ψ.g, φ.square.paste_horiz ψ.square⟩

/-- The category `ℋ_d` of degree-`d` finite locally free covers. -/
instance category : Category (FiniteCover B S hS d) where
  toCategoryStruct := categoryStruct
  id_comp _ := Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

end FiniteCover

/-- The canonical functor from the category of degree-`d` finite locally free covers to the big
fppf site, remembering only the base object and the base component of a morphism. -/
def finiteCoverProjection : FiniteCover B S hS d ⥤ BigFppfOver B S hS where
  obj P := P.U
  map φ := φ.f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category `ℋ_d` of degree-`d` finite locally free covers, regarded as a category over the
big fppf site through its canonical projection. -/
def finiteCoverCategory : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))

/-- The base change of a finite locally free cover along a morphism `f : V ⟶ P.U` of the site. -/
private noncomputable abbrev FiniteCover.pullbackCover (P : FiniteCover B S hS d)
    {V : BigFppfOver B S hS} (f : V ⟶ P.U) : FiniteCover B S hS d :=
  haveI : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map P.q) d := P.finiteLocallyFree
  ⟨V, pullback P.q f, pullback.snd P.q f,
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      ((IsPullback.of_hasPullback P.q f).map (BigFppfOver.toScheme B S hS))⟩

/-- Every morphism `f : V ⟶ U` of the big fppf site lifts to the category of degree-`d` finite
locally free covers, by pulling the cover back along `f`. -/
theorem FiniteCover.exists_lift {V U : BigFppfOver B S hS} (f : V ⟶ U)
    (P : FiniteCover B S hS d) (hP : P.U = U) :
    ∃ (Q : FiniteCover B S hS d) (φ : Q ⟶ P),
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift f φ := by
  cases hP
  exact ⟨P.pullbackCover f, ⟨f, pullback.fst P.q f, IsPullback.of_hasPullback P.q f⟩,
    IsHomLift.of_fac' _ f _ rfl rfl rfl⟩

/-- Gap-filling for morphisms of covers: a base morphism `f` through which `ψ` factors over `φ`
lifts to a unique morphism of covers. -/
private theorem FiniteCover.exists_unique_hom {P Q R : FiniteCover B S hS d} (φ : P ⟶ Q)
    (ψ : R ⟶ Q) (f : R.U ⟶ P.U) (hf : f ≫ φ.f = ψ.f) :
    ∃ χ : R ⟶ P, χ.f = f ∧ χ.g ≫ φ.g = ψ.g ∧ ∀ χ' : R ⟶ P, χ'.f = f → χ'.g ≫ φ.g = ψ.g →
      χ' = χ := by
  let g : R.Z ⟶ P.Z := φ.square.lift ψ.g (R.q ≫ f) (by rw [ψ.square.w, Category.assoc, hf])
  have hg : g ≫ φ.g = ψ.g := φ.square.lift_fst _ _ _
  have hq : g ≫ P.q = R.q ≫ f := φ.square.lift_snd _ _ _
  refine ⟨⟨f, g, (hf ▸ ψ.square).of_right' φ.square⟩, rfl, hg, fun χ hχf hχ ↦ ?_⟩
  refine FiniteCover.Hom.ext hχf (φ.square.hom_ext (hχ.trans hg.symm) ?_)
  rw [χ.square.w, hχf, hq]

/-- **The category of degree-`d` finite locally free covers is fibred in groupoids** over the big
fppf site. A lift of a base morphism is a base change of the cover, and the unique gap-filler
over a base morphism is its cover component, supplied by the universal property of a cartesian
square. -/
theorem isFiberedInGroupoids_finiteCoverProjection :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsFiberedInGroupoids := by
  refine ⟨FiniteCover.exists_lift, ?_⟩
  intro P Q R φ ψ f hf
  change R.U ⟶ Q.U at f
  change f ≫ φ.f = ψ.f at hf
  obtain ⟨χ, hχf, hχ, huniq⟩ := FiniteCover.exists_unique_hom φ ψ f hf
  exact ⟨χ, ⟨hχf, FiniteCover.Hom.ext (by change χ.f ≫ φ.f = ψ.f; rw [hχf, hf]) hχ⟩,
    fun χ' h ↦
    huniq χ' h.1 (congrArg FiniteCover.Hom.g h.2)⟩

/-! ### The absolute finite Hilbert category -/

/-- A morphism of the absolute finite Hilbert category: a morphism of the underlying covers
together with a morphism of the objects of `𝒳` lying over its cover component. -/
structure AbsoluteHilbert.Hom (P Q : AbsoluteHilbert.Object B S hS d 𝒳) where
  /-- The morphism of the underlying finite locally free covers. -/
  cover : FiniteCover.Hom P.toFiniteCover Q.toFiniteCover
  /-- The morphism of the objects of `𝒳`. -/
  a : P.x ⟶ Q.x
  /-- The morphism `a` lies over the cover component. -/
  a_over : 𝒳.toBasedCategory.p.IsHomLift cover.g a

namespace AbsoluteHilbert

/-- Two morphisms of the absolute finite Hilbert category agree as soon as their cover component
and their stack component do. -/
@[ext]
theorem Hom.ext {P Q : Object B S hS d 𝒳} {φ ψ : Hom P Q} (hc : φ.cover = ψ.cover)
    (ha : φ.a = ψ.a) : φ = ψ := by
  cases φ; cases ψ; cases hc; cases ha; rfl

/-- Composition in the absolute finite Hilbert category is componentwise. -/
instance categoryStruct : CategoryStruct (Object B S hS d 𝒳) where
  Hom := Hom
  id P :=
    { cover := 𝟙 P.toFiniteCover
      a := 𝟙 P.x
      a_over := IsHomLift.id P.x_over }
  comp φ ψ :=
    { cover := ⟨φ.cover.f ≫ ψ.cover.f, φ.cover.g ≫ ψ.cover.g,
        φ.cover.square.paste_horiz ψ.cover.square⟩
      a := φ.a ≫ ψ.a
      a_over := by
        change 𝒳.toBasedCategory.p.IsHomLift (φ.cover.g ≫ ψ.cover.g) (φ.a ≫ ψ.a)
        have := φ.a_over
        have := ψ.a_over
        infer_instance }

/-- The absolute finite Hilbert category `ℋ_d(𝒳)` of a stack in groupoids `𝒳`. -/
instance category : Category (Object B S hS d 𝒳) where
  toCategoryStruct := categoryStruct
  id_comp _ := Hom.ext
    (FiniteCover.Hom.ext (Category.id_comp _) (Category.id_comp _)) (Category.id_comp _)
  comp_id _ := Hom.ext
    (FiniteCover.Hom.ext (Category.comp_id _) (Category.comp_id _)) (Category.comp_id _)
  assoc _ _ _ := Hom.ext
    (FiniteCover.Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)) (Category.assoc _ _ _)

end AbsoluteHilbert

/-- The canonical functor from the absolute finite Hilbert category to the big fppf site,
remembering only the base object and the base component of a morphism. -/
def absoluteHilbertProjection :
    AbsoluteHilbert.Object B S hS d 𝒳 ⥤ BigFppfOver B S hS where
  obj P := P.U
  map φ := φ.cover.f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The absolute finite Hilbert category `ℋ_d(𝒳)`, regarded as a category over the big fppf site
through its canonical projection. -/
def absoluteHilbertCategory : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor
    (absoluteHilbertProjection (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳))

/-- Every morphism `f : V ⟶ U` of the big fppf site lifts to the absolute finite Hilbert
category: pull the cover back along `f` and lift the object of `𝒳` along the fibredness of
`𝒳`. -/
theorem AbsoluteHilbert.exists_lift {V U : BigFppfOver B S hS} (f : V ⟶ U)
    (P : AbsoluteHilbert.Object B S hS d 𝒳) (hP : P.U = U) :
    ∃ (Q : AbsoluteHilbert.Object B S hS d 𝒳) (φ : Q ⟶ P),
      (absoluteHilbertProjection (B := B) (S := S) (hS := hS)
        (d := d) (𝒳 := 𝒳)).IsHomLift f φ := by
  cases hP
  obtain ⟨x', a, ha⟩ :=
    𝒳.isStackInGroupoids.isFiberedInGroupoids.exists_lift (pullback.fst P.q f) P.x P.x_over
  refine ⟨{ toFiniteCover := P.toFiniteCover.pullbackCover f
            x := x'
            x_over := IsHomLift.domain_eq 𝒳.toBasedCategory.p (pullback.fst P.q f) a },
    { cover := ⟨f, pullback.fst P.q f, IsPullback.of_hasPullback P.q f⟩
      a := a
      a_over := ha }, ?_⟩
  exact IsHomLift.of_fac' _ f _ rfl rfl rfl

/-- **The absolute finite Hilbert category is fibred in groupoids** over the big fppf site. A
lift of a base morphism base-changes the cover and lifts the object of `𝒳`; the unique
gap-filler over a base morphism has its cover component supplied by the universal property of a
cartesian square and its stack component by the universal property of a strongly cartesian
morphism. -/
theorem isFiberedInGroupoids_absoluteHilbertProjection :
    (absoluteHilbertProjection (B := B) (S := S) (hS := hS)
      (d := d) (𝒳 := 𝒳)).IsFiberedInGroupoids := by
  refine ⟨AbsoluteHilbert.exists_lift, ?_⟩
  intro P Q R φ ψ f hf
  change R.U ⟶ Q.U at f
  change f ≫ φ.cover.f = ψ.cover.f at hf
  obtain ⟨c, hcf, hg, huniq⟩ := FiniteCover.exists_unique_hom φ.cover ψ.cover f hf
  have := φ.a_over
  have := ψ.a_over
  have := 𝒳.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift φ.cover.g φ.a
  obtain ⟨a, ⟨ha, hafac⟩, hauniq⟩ :=
    Functor.IsStronglyCartesian.universal_property 𝒳.toBasedCategory.p φ.cover.g φ.a c.g
      ψ.cover.g hg.symm ψ.a
  refine ⟨⟨c, a, ha⟩, ⟨hcf, AbsoluteHilbert.Hom.ext
    (FiniteCover.Hom.ext (by change c.f ≫ φ.cover.f = ψ.cover.f; rw [hcf, hf]) hg) hafac⟩, ?_⟩
  rintro χ ⟨hχf, hχ⟩
  have hχg : χ.cover = c :=
    huniq _ hχf (congrArg FiniteCover.Hom.g (congrArg AbsoluteHilbert.Hom.cover hχ))
  refine AbsoluteHilbert.Hom.ext hχg (hauniq _ ⟨?_, ?_⟩)
  · rw [← hχg]
    exact χ.a_over
  · exact congrArg AbsoluteHilbert.Hom.a hχ

/-! ### The diagram of Stacks 05WD -/

variable {𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- **Stacks 05WD.** The 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` from the relative to the absolute
finite Hilbert category: forget the object of `𝒴` and the identification, keeping the cover and
the object of `𝒳`. -/
@[stacks 05WD "relative Hilbert stack to absolute Hilbert stack"]
def forgetRelativeStructure :
    finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) ⥤ᵇ
      absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) where
  toFunctor :=
    { obj := fun P ↦
        { toFiniteCover := ⟨P.U, P.Z, P.q, P.finiteLocallyFree⟩
          x := P.x
          x_over := P.x_over }
      map := fun φ ↦ { cover := ⟨φ.f, φ.g, φ.square⟩, a := φ.a, a_over := φ.a_over }
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  w := rfl

/-- **Stacks 05WD.** The 1-morphism `ℋ_d(𝒳/𝒴) ⟶ 𝒴` to the target stack: forget the cover and
the object of `𝒳`, keeping the object of `𝒴`. -/
@[stacks 05WD "relative Hilbert stack to the target stack"]
def forgetTarget :
    finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) ⥤ᵇ
      𝒴.toBasedCategory where
  toFunctor :=
    { obj := fun P ↦ P.y
      map := fun φ ↦ φ.b
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  w := by
    refine CategoryTheory.Functor.ext
      (fun P : FiniteHilbert.Object B S hS 𝒳 𝒴 F d ↦ P.y_over) ?_
    intro P Q φ
    have := φ.b_over
    exact IsHomLift.fac' 𝒴.toBasedCategory.p φ.f φ.b

/-- **Stacks 05WD.** The 1-morphism `ℋ_d(𝒳) ⟶ ℋ_d` from the absolute finite Hilbert category to
the category of finite locally free covers: forget the object of `𝒳`. -/
@[stacks 05WD "absolute Hilbert stack to finite covers"]
def forgetAbsoluteStructure :
    absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) ⥤ᵇ
      finiteCoverCategory (B := B) (S := S) (hS := hS) (d := d) where
  toFunctor :=
    { obj := fun P ↦ P.toFiniteCover
      map := fun φ ↦ φ.cover
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  w := rfl

/-- **Stacks 05WD.** The 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d` from the relative finite Hilbert category
to the category of finite locally free covers: forget both stack objects and the
identification, keeping the cover. -/
@[stacks 05WD "relative Hilbert stack to finite covers"]
def forgetRelativeToFiniteCover :
    finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) ⥤ᵇ
      finiteCoverCategory (B := B) (S := S) (hS := hS) (d := d) where
  toFunctor :=
    { obj := fun P ↦ ⟨P.U, P.Z, P.q, P.finiteLocallyFree⟩
      map := fun φ ↦ ⟨φ.f, φ.g, φ.square⟩
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  w := rfl

/-- **The triangle of Stacks 05WD commutes**: the 1-morphism from the relative finite Hilbert
category to the category of finite locally free covers is the composite of the 1-morphism to the
absolute finite Hilbert category with the 1-morphism from it. -/
theorem forgetRelativeToFiniteCover_eq_comp :
    forgetRelativeToFiniteCover (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F) =
      BasedFunctor.comp
        (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
          (F := F))
        (forgetAbsoluteStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)) :=
  rfl

end AlgebraicGeometry.Stack

end
