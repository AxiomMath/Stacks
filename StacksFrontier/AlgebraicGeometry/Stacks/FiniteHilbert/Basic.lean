module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Stack.Groupoid

/-!
# The relative finite Hilbert stack

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. The *relative finite Hilbert category* `ℋ_d(𝒳/𝒴)` has as
objects the quintuples `(U, Z, y, x, α)` consisting of an object `U` of the site, an object `Z`
of the site which is finite locally free of degree `d` over `U`, an object `y` of `𝒴` over `U`,
an object `x` of `𝒳` over `Z`, and an identification `α` of `F x` with the restriction of `y`
to `Z`. A morphism `(U, Z, y, x, α) ⟶ (U', Z', y', x', α')` consists of `f : U ⟶ U'` and
`g : Z ⟶ Z'` presenting `Z` as the fibre product `Z' ×_{U'} U`, together with morphisms of `y`
and of `x` lying over `f` and over `g` which are compatible with `α` and `α'`.

Forgetting everything but `U` gives a functor to the site, and the relative finite Hilbert
category is fibred in groupoids over it: a lift of `f : U' ⟶ U` is obtained by pulling back the
cover `Z ⟶ U` along `f`, which stays finite locally free of degree `d`, lifting `y` and `x`
along the fibredness of `𝒴` and of `𝒳`, and transporting `α` by the universal property of a
strongly cartesian morphism.

## Main definitions

* `AlgebraicGeometry.Stack.FiniteHilbert.Object`: the quintuple `(U, Z, y, x, α)`.
* `AlgebraicGeometry.Stack.FiniteHilbert.Hom`: the cartesian quadruple `(f, g, b, a)`.
* `AlgebraicGeometry.Stack.finiteHilbertProjection`: the forgetful functor `(U, Z, y, x, α) ↦ U`.
* `AlgebraicGeometry.Stack.finiteHilbertCategory`: the relative finite Hilbert category as a
  category over the big fppf site.
* `AlgebraicGeometry.Stack.FiniteHilbert.sourceFunctor`: the forgetful functor
  `(U, Z, y, x, α) ↦ Z`, which is not a functor over the site.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInGroupoids_finiteHilbertProjection`: the relative finite
  Hilbert category is fibred in groupoids over the big fppf site.

## Implementation notes

The source takes `α` to be an isomorphism `y|_Z ≅ F x` from a chosen restriction of `y`, and
likewise asks for isomorphisms from `y` and from `x` to chosen restrictions of `y'` and of `x'`.
Here `α` is instead a plain morphism `F x ⟶ y` of `𝒴` lying over `q : Z ⟶ U`, and the morphism
fields `b` and `a` are plain morphisms lying over `f` and over `g`. This is not a weakening: in
a category fibred in groupoids every morphism lying over a base morphism is strongly cartesian,
so a morphism lying over an isomorphism is itself an isomorphism, and a morphism lying over `q`
exhibits its source as a restriction of its target along `q`. Encoding the data this way removes
every choice of cleavage, and makes the identity and the composition of the category
componentwise.

The condition that `g : Z ⟶ Z'` identify `Z` with `Z' ×_{U'} U` is recorded as the statement
that the square formed by `g`, `q`, `q'` and `f` is cartesian.

Finite local freeness of degree `d` is a condition on the underlying morphism of schemes, so it
is stated for the image of `q` under the canonical functor from the big fppf site to schemes.
Its stability under base change is
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback`, applied to the image of a cartesian
square of the site, which is again cartesian because that functor preserves fibre products.

## References

* [Stacks Project, Tag 05WA](https://stacks.math.columbia.edu/tag/05WA)
* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS))
  (F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory) (d : ℕ)

/-- An object of the relative finite Hilbert category `ℋ_d(𝒳/𝒴)` of a 1-morphism
`F : 𝒳 ⟶ 𝒴` of stacks in groupoids: an object `U` of the big fppf site, a degree-`d` finite
locally free cover `q : Z ⟶ U`, an object `y` of `𝒴` over `U`, an object `x` of `𝒳` over `Z`,
and an identification `α` of `F x` with the restriction of `y` to `Z`. -/
structure FiniteHilbert.Object where
  /-- The base object of the big fppf site. -/
  U : BigFppfOver B S hS
  /-- The covering object of the big fppf site. -/
  Z : BigFppfOver B S hS
  /-- The structure morphism of the cover. -/
  q : Z ⟶ U
  /-- The cover is finite locally free of degree `d`. -/
  finiteLocallyFree : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
    ((BigFppfOver.toScheme B S hS).map q) d
  /-- The object of `𝒴` lying over the base. -/
  y : 𝒴.toBasedCategory.obj
  /-- The object `y` lies over `U`. -/
  y_over : 𝒴.toBasedCategory.p.obj y = U
  /-- The object of `𝒳` lying over the cover. -/
  x : 𝒳.toBasedCategory.obj
  /-- The object `x` lies over `Z`. -/
  x_over : 𝒳.toBasedCategory.p.obj x = Z
  /-- The identification of `F x` with the restriction of `y` to `Z`. -/
  α : F.obj x ⟶ y
  /-- The identification `α` lies over the structure morphism of the cover. -/
  α_over : 𝒴.toBasedCategory.p.IsHomLift q α

variable {B S hS 𝒳 𝒴 F d}

/-- A morphism of the relative finite Hilbert category: a morphism `f` of base objects and a
morphism `g` of covers presenting the source cover as the fibre product of the target cover with
the source base, together with morphisms `b` of `𝒴` over `f` and `a` of `𝒳` over `g` which are
compatible with the two identifications. -/
structure FiniteHilbert.Hom (P Q : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) where
  /-- The morphism of base objects. -/
  f : P.U ⟶ Q.U
  /-- The morphism of covers. -/
  g : P.Z ⟶ Q.Z
  /-- The morphism of covers presents `P.Z` as `Q.Z ×_{Q.U} P.U`. -/
  square : IsPullback g P.q Q.q f
  /-- The morphism of the objects of `𝒴`. -/
  b : P.y ⟶ Q.y
  /-- The morphism `b` lies over `f`. -/
  b_over : 𝒴.toBasedCategory.p.IsHomLift f b
  /-- The morphism of the objects of `𝒳`. -/
  a : P.x ⟶ Q.x
  /-- The morphism `a` lies over `g`. -/
  a_over : 𝒳.toBasedCategory.p.IsHomLift g a
  /-- The two identifications are compatible with `a` and `b`. -/
  compatible : F.map a ≫ Q.α = P.α ≫ b

namespace FiniteHilbert

/-- Two morphisms of the relative finite Hilbert category agree as soon as their four
components do. -/
@[ext]
theorem Hom.ext {P Q : Object B S hS 𝒳 𝒴 F d} {φ ψ : Hom P Q} (hf : φ.f = ψ.f)
    (hg : φ.g = ψ.g) (hb : φ.b = ψ.b) (ha : φ.a = ψ.a) : φ = ψ := by
  cases φ; cases ψ; cases hf; cases hg; cases hb; cases ha; rfl

/-- Composition in the relative finite Hilbert category is componentwise. -/
instance categoryStruct : CategoryStruct (Object B S hS 𝒳 𝒴 F d) where
  Hom := Hom
  id P :=
    { f := 𝟙 P.U
      g := 𝟙 P.Z
      square := IsPullback.id_horiz P.q
      b := 𝟙 P.y
      b_over := IsHomLift.id P.y_over
      a := 𝟙 P.x
      a_over := IsHomLift.id P.x_over
      compatible := by simp }
  comp φ ψ :=
    { f := φ.f ≫ ψ.f
      g := φ.g ≫ ψ.g
      square := φ.square.paste_horiz ψ.square
      b := φ.b ≫ ψ.b
      b_over := by
        have := φ.b_over
        have := ψ.b_over
        infer_instance
      a := φ.a ≫ ψ.a
      a_over := by
        have := φ.a_over
        have := ψ.a_over
        infer_instance
      compatible := by
        rw [Functor.map_comp, Category.assoc, ψ.compatible, ← Category.assoc,
          φ.compatible, Category.assoc] }

/-- The relative finite Hilbert category of a 1-morphism of stacks in groupoids. -/
instance category : Category (Object B S hS 𝒳 𝒴 F d) where
  toCategoryStruct := categoryStruct
  id_comp _ := Hom.ext (Category.id_comp _) (Category.id_comp _) (Category.id_comp _)
    (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _) (Category.comp_id _) (Category.comp_id _)
    (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _) (Category.assoc _ _ _)
    (Category.assoc _ _ _)

end FiniteHilbert

/-- The canonical functor from the relative finite Hilbert category to the big fppf site,
remembering only the base object of a quintuple and the base component of a morphism. -/
def finiteHilbertProjection :
    FiniteHilbert.Object B S hS 𝒳 𝒴 F d ⥤ BigFppfOver B S hS where
  obj P := P.U
  map φ := φ.f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The relative finite Hilbert category, regarded as a category over the big fppf site through
its canonical projection. -/
noncomputable def finiteHilbertCategory : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))

namespace FiniteHilbert

/-- The functor from the relative finite Hilbert category to the big fppf site remembering only
the *cover* of a quintuple and the cover component of a morphism. Unlike
`AlgebraicGeometry.Stack.finiteHilbertProjection` this is not a functor *over* the site; it is
used to read the cover component off an isomorphism and off a commuting diagram. -/
def sourceFunctor {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
    {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
    {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} :
    Object B S hS 𝒳 𝒴 F d ⥤ BigFppfOver B S hS where
  obj P := P.Z
  map φ := φ.g
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every morphism `f : V ⟶ U` of the big fppf site lifts to the relative finite Hilbert
category: pull the cover back along `f`, which preserves degree-`d` finite local freeness, lift
the objects of `𝒴` and of `𝒳` by fibredness of `𝒳` and `𝒴`, and transport the identification by
the universal property of the lift in `𝒴`. -/
theorem exists_lift {V U : BigFppfOver B S hS} (f : V ⟶ U)
    (P : Object B S hS 𝒳 𝒴 F d) (hP : P.U = U) :
    ∃ (Q : Object B S hS 𝒳 𝒴 F d) (φ : Q ⟶ P),
      (finiteHilbertProjection (B := B) (S := S) (hS := hS)
        (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).IsHomLift f φ := by
  cases hP
  let g := pullback.fst P.q f
  let q' := pullback.snd P.q f
  have sq : IsPullback g q' P.q f := IsPullback.of_hasPullback P.q f
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map P.q) d := P.finiteLocallyFree
  have hfinite : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map q') d :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (sq.map (BigFppfOver.toScheme B S hS))
  obtain ⟨y', b, hb⟩ := 𝒴.isStackInGroupoids.isFiberedInGroupoids.exists_lift f P.y P.y_over
  obtain ⟨x', a, ha⟩ := 𝒳.isStackInGroupoids.isFiberedInGroupoids.exists_lift g P.x P.x_over
  have := P.α_over
  have : 𝒴.toBasedCategory.p.IsStronglyCartesian f b :=
    𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift f b
  let α := Functor.IsStronglyCartesian.map 𝒴.toBasedCategory.p f b sq.w (F.map a ≫ P.α)
  refine ⟨{ U := V
            Z := pullback P.q f
            q := q'
            finiteLocallyFree := hfinite
            y := y'
            y_over := IsHomLift.domain_eq 𝒴.toBasedCategory.p f b
            x := x'
            x_over := IsHomLift.domain_eq 𝒳.toBasedCategory.p g a
            α := α
            α_over := inferInstance },
    { f := f
      g := g
      square := sq
      b := b
      b_over := hb
      a := a
      a_over := ha
      compatible :=
        (Functor.IsStronglyCartesian.fac 𝒴.toBasedCategory.p f b sq.w (F.map a ≫ P.α)).symm },
    ?_⟩
  exact IsHomLift.of_fac' _ f _ rfl rfl rfl

end FiniteHilbert

/-- **The relative finite Hilbert category is fibred in groupoids** over the big fppf site.
Existence of lifts is `AlgebraicGeometry.Stack.FiniteHilbert.exists_lift`; the unique gap-filler
over a base morphism is assembled componentwise, its cover component from the universal property
of a cartesian square and its two stack components from the universal property of a strongly
cartesian morphism. -/
theorem isFiberedInGroupoids_finiteHilbertProjection :
    (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).IsFiberedInGroupoids := by
  refine ⟨FiniteHilbert.exists_lift, ?_⟩
  intro P Q R φ ψ f hf
  change R.U ⟶ Q.U at f
  change f ≫ φ.f = ψ.f at hf
  let g : R.Z ⟶ Q.Z := φ.square.lift ψ.g (R.q ≫ f) (by rw [ψ.square.w, Category.assoc, hf])
  have hg : g ≫ φ.g = ψ.g := φ.square.lift_fst _ _ _
  have hq : g ≫ Q.q = R.q ≫ f := φ.square.lift_snd _ _ _
  have hsq : IsPullback g R.q Q.q f := (hf ▸ ψ.square).of_right' φ.square
  have := φ.b_over
  have := ψ.b_over
  have := φ.a_over
  have := ψ.a_over
  have := Q.α_over
  have := R.α_over
  have := 𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift φ.f φ.b
  have := 𝒳.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift φ.g φ.a
  obtain ⟨b, ⟨hb, hbfac⟩, hbuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property 𝒴.toBasedCategory.p φ.f φ.b f ψ.f hf.symm ψ.b
  obtain ⟨a, ⟨ha, hafac⟩, hauniq⟩ :=
    Functor.IsStronglyCartesian.universal_property 𝒳.toBasedCategory.p φ.g φ.a g ψ.g hg.symm ψ.a
  have hcompat : F.map a ≫ Q.α = R.α ≫ b := by
    have : 𝒴.toBasedCategory.p.IsHomLift (g ≫ Q.q) (R.α ≫ b) := by rw [hq]; infer_instance
    refine Functor.IsStronglyCartesian.ext 𝒴.toBasedCategory.p φ.f φ.b (g ≫ Q.q) ?_
    calc (F.map a ≫ Q.α) ≫ φ.b = F.map a ≫ F.map φ.a ≫ P.α := by
            rw [Category.assoc, ← φ.compatible]
      _ = F.map ψ.a ≫ P.α := by rw [← Category.assoc, ← F.map_comp, hafac]
      _ = R.α ≫ ψ.b := ψ.compatible
      _ = (R.α ≫ b) ≫ φ.b := by rw [Category.assoc, hbfac]
  refine ⟨⟨f, g, hsq, b, hb, a, ha, hcompat⟩, ⟨rfl, FiniteHilbert.Hom.ext hf hg hbfac hafac⟩, ?_⟩
  rintro χ ⟨hχf, hχ⟩
  change χ.f = f at hχf
  have hχg : χ.g = g := by
    refine φ.square.hom_ext ?_ ?_
    · exact (congrArg FiniteHilbert.Hom.g hχ).trans hg.symm
    · rw [χ.square.w, hχf, hq]
  refine FiniteHilbert.Hom.ext hχf hχg ?_ ?_
  · refine hbuniq _ ⟨?_, congrArg FiniteHilbert.Hom.b hχ⟩
    rw [← hχf]
    exact χ.b_over
  · refine hauniq _ ⟨?_, congrArg FiniteHilbert.Hom.a hχ⟩
    rw [← hχg]
    exact χ.a_over



end AlgebraicGeometry.Stack

namespace CategoryTheory.Functor.Restriction

/-- **The base component of the canonical comparison of two restrictions is the first of the two
morphisms.** Stated for an arbitrary functor, since `CategoryTheory.Functor.Restriction` records
no base component of its own: the component is read off through `p.map`, which each fibration's
own `Hom` projection equals by definition. -/
theorem compTo_map {𝒞 : Type*} [Category 𝒞] {𝒮 : Type*} [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U) {h : W ⟶ U} (hh : h = g ≫ f)
    {x : 𝒮} {hx : p.obj x = U}
    (xr : Functor.Restriction p f x hx) (xrW : Functor.Restriction p h x hx) :
    p.map (Functor.Restriction.compTo p g f hh xr xrW) =
      eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm := by
  have : p.IsHomLift (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm)
      (Functor.Restriction.compTo p g f hh xr xrW) := by
    unfold Functor.Restriction.compTo
    infer_instance
  have h := CategoryTheory.IsHomLift.fac' p
    (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm)
    (Functor.Restriction.compTo p g f hh xr xrW)
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

end CategoryTheory.Functor.Restriction

end
