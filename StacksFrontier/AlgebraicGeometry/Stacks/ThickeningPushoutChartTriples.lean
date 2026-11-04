module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutPointIso
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

/-!
# Sections of the base change of an atlas along a point, as triples

Let `p : 𝒳 ⥤ 𝒞` be a category fibred in groupoids, let `f₀ : 𝒞/U₀ ⥤ 𝒳` be a 1-morphism out of
the category represented by an object `U₀` and let `w` be an object of `𝒳` over `A`, with
2-Yoneda point `𝒞/A ⥤ 𝒳` its functor of chosen lifts. The 2-fibre product `𝒞/A ×_𝒳 𝒞/U₀`
of the point and `f₀` has, over an object `T`, the objects
`(t : T ⟶ A, s : T ⟶ U₀, γ : t^* w ≅ f₀(s))` with `γ` vertical; and two such objects are
isomorphic over `T` only when they are equal, the fibres of the two slices being discrete.

So if the 2-fibre product is equivalent over `𝒞` to the category of elements of a presheaf `F`,
the sections of `F` over `T` are exactly these triples, and restriction of sections is
restriction of triples.

## Main definitions

* `AlgebraicGeometry.Stack.ThickeningPushout.Trip`: the triples over `T`.
* `AlgebraicGeometry.Stack.ThickeningPushout.Trip.restrict`: their restriction along `g : T' ⟶ T`.
* `AlgebraicGeometry.Stack.ThickeningPushout.tripSection`: the section a triple names.
* `AlgebraicGeometry.Stack.ThickeningPushout.tripEquiv`: the bijection between triples over `T`
  and sections of `F` over `T`.

## Main results

* `AlgebraicGeometry.Stack.ThickeningPushout.map_tripSection`: restricting the section named by a
  triple gives the section named by the restricted triple.

## References

* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.Stack.ThickeningPushout

universe a

variable {𝒞 : Type*} [Category 𝒞] {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ 𝒞)
  (hp : p.IsFiberedInGroupoids) {U₀ : 𝒞} (f₀ : Over U₀ ⥤ 𝒳)
  {A : 𝒞} (P : Over A ⥤ 𝒳)

/-- The 2-fibre product of the point named by `w` and of `f₀`. -/
abbrev ChartProduct :=
  TwoFibreProductOver (Over.forget A) (Over.forget U₀) p P f₀

/-- A triple over `T`: morphisms `t : T ⟶ A`, `s : T ⟶ U₀` and a vertical isomorphism
`t^* w ≅ f₀(s)`. -/
abbrev Trip (T : 𝒞) : Type _ :=
  Σ (t : T ⟶ A) (s : T ⟶ U₀),
    {γ : P.obj (Over.mk t) ≅ f₀.obj (Over.mk s) //
      p.IsHomLift (𝟙 T) γ.hom}

variable {p f₀ P}

/-- The object of the 2-fibre product named by a triple. -/
abbrev Trip.obj {T : 𝒞} (τ : Trip p f₀ P T) : ChartProduct p f₀ P where
  base := T
  x := Over.mk τ.1
  y := Over.mk τ.2.1
  hx := rfl
  hy := rfl
  iso := τ.2.2.1
  vertical := τ.2.2.2

/-- Two triples with the same morphisms and the same isomorphism are equal. -/
lemma Trip.ext {T : 𝒞} {τ τ' : Trip p f₀ P T} (ht : τ.1 = τ'.1) (hs : τ.2.1 = τ'.2.1)
    (hγ : τ.2.2.1.hom ≫ eqToHom (by rw [hs]) =
      eqToHom (by rw [ht]) ≫ τ'.2.2.1.hom) : τ = τ' := by
  obtain ⟨t, s, γ, hγv⟩ := τ
  obtain ⟨t', s', γ', hγv'⟩ := τ'
  dsimp only at ht hs hγ
  subst ht hs
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hγ
  obtain rfl : γ = γ' := Iso.ext hγ
  rfl

/-- Composing `P`'s image of `Over.homMk g` with the comparison of a triple lies over `g`. -/
private lemma isHomLift_P_homMk_comp (hP : P ⋙ p = Over.forget A) {T T' : 𝒞} (g : T' ⟶ T)
    (τ : Trip p f₀ P T) :
    p.IsHomLift g (P.map
      (Over.homMk g rfl : Over.mk (g ≫ τ.1) ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom) :=
  have : (Over.forget A).IsHomLift g (Over.homMk g rfl : Over.mk (g ≫ τ.1) ⟶ Over.mk τ.1) :=
    IsHomLift.of_fac' _ g _ rfl rfl (by simp)
  have := isHomLift_map_of_comp_eq hP g (Over.homMk g rfl : Over.mk (g ≫ τ.1) ⟶ Over.mk τ.1)
  have : p.IsHomLift (𝟙 T) τ.2.2.1.hom := τ.2.2.2
  IsHomLift.comp_lift_id_right' p g _ T _

section Restrict

variable (hf₀ : f₀ ⋙ p = Over.forget U₀) (hP : P ⋙ p = Over.forget A)
include hp hf₀ hP

omit hp hP in
/-- `f₀` carries a morphism of the slice over `U₀` to a morphism lying over its underlying
morphism. -/
lemma isHomLift_f₀_map {a b : Over U₀} (m : a ⟶ b) : p.IsHomLift m.left (f₀.map m) :=
  have : (Over.forget U₀).IsHomLift m.left m := IsHomLift.map (Over.forget U₀) m
  isHomLift_map_of_comp_eq hf₀ m.left m

omit hP in
/-- `f₀` carries a morphism of the slice over `U₀` to a strongly cartesian morphism. -/
lemma isStronglyCartesian_f₀_map {a b : Over U₀} (m : a ⟶ b) :
    p.IsStronglyCartesian m.left (f₀.map m) :=
  have := isHomLift_f₀_map hf₀ m
  hp.isStronglyCartesian_homLift m.left (f₀.map m)

omit hp hf₀ hP in
/-- `Over.homMk g` lies over `g`. -/
lemma isHomLift_forget_homMk {B T T' : 𝒞} (g : T' ⟶ T) (t : T ⟶ B) :
    (Over.forget B).IsHomLift g (Over.homMk g rfl : Over.mk (g ≫ t) ⟶ Over.mk t) :=
  IsHomLift.of_fac' _ g _ rfl rfl (by simp)

omit hp hP in
/-- `f₀` carries `Over.homMk g : Over.mk (g ≫ s) ⟶ Over.mk s` to a morphism lying over `g`. -/
lemma isHomLift_f₀_homMk {T T' : 𝒞} (g : T' ⟶ T) (s : T ⟶ U₀) :
    p.IsHomLift g (f₀.map (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s)) :=
  have := isHomLift_forget_homMk g s
  isHomLift_map_of_comp_eq hf₀ g _

omit hP in
/-- `f₀` carries `Over.homMk g : Over.mk (g ≫ s) ⟶ Over.mk s` to a strongly cartesian morphism
over `g`. -/
lemma isStronglyCartesian_f₀_homMk {T T' : 𝒞} (g : T' ⟶ T) (s : T ⟶ U₀) :
    p.IsStronglyCartesian g (f₀.map (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s)) :=
  have := isHomLift_f₀_homMk hf₀ g s
  hp.isStronglyCartesian_homLift g _

omit hp hf₀ in
/-- `P` carries `Over.homMk g : Over.mk (g ≫ t) ⟶ Over.mk t` to a morphism lying over `g`. -/
lemma isHomLift_P_homMk {T T' : 𝒞} (g : T' ⟶ T) (t : T ⟶ A) :
    p.IsHomLift g (P.map
      (Over.homMk g rfl : Over.mk (g ≫ t) ⟶ Over.mk t)) :=
  have := isHomLift_forget_homMk g t
  isHomLift_map_of_comp_eq (hP) g _

/-- The comparison of a triple, restricted along `g`: the unique vertical morphism compatible
with the images of `g` under the point and under `f₀`. -/
noncomputable def Trip.restrictHom {T T' : 𝒞} (g : T' ⟶ T) (τ : Trip p f₀ P T) :
    P.obj (Over.mk (g ≫ τ.1)) ⟶ f₀.obj (Over.mk (g ≫ τ.2.1)) :=
  have := isStronglyCartesian_f₀_homMk hp hf₀ g τ.2.1
  have := isHomLift_P_homMk hP g τ.1
  have : p.IsHomLift (𝟙 T) τ.2.2.1.hom := τ.2.2.2
  have : p.IsHomLift g (P.map
      (Over.homMk g rfl : Over.mk (g ≫ τ.1) ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom) :=
    IsHomLift.comp_lift_id_right' p g _ T _
  IsStronglyCartesian.map p g (f₀.map (Over.homMk g rfl : Over.mk (g ≫ τ.2.1) ⟶ Over.mk τ.2.1))
    (f' := g) (g := 𝟙 T') (Category.id_comp g).symm
    (P.map
      (Over.homMk g rfl : Over.mk (g ≫ τ.1) ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom)

/-- The restricted comparison `Trip.restrictHom` is vertical. -/
lemma Trip.isHomLift_restrictHom {T T' : 𝒞} (g : T' ⟶ T) (τ : Trip p f₀ P T) :
    p.IsHomLift (𝟙 T') (Trip.restrictHom hp hf₀ hP g τ) := by
  have := isStronglyCartesian_f₀_homMk hp hf₀ g τ.2.1
  have := isHomLift_P_homMk hP g τ.1
  have : p.IsHomLift (𝟙 T) τ.2.2.1.hom := τ.2.2.2
  have : p.IsHomLift g (P.map
      (Over.homMk g rfl : Over.mk (g ≫ τ.1) ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom) :=
    IsHomLift.comp_lift_id_right' p g _ T _
  unfold Trip.restrictHom
  infer_instance

/-- The restricted comparison followed by the image of `g` under `f₀` is the image of `g` under
the point followed by the comparison of the triple. -/
@[reassoc]
lemma Trip.restrictHom_fac {T T' : 𝒞} (g : T' ⟶ T) (τ : Trip p f₀ P T) :
    Trip.restrictHom hp hf₀ hP g τ ≫
        f₀.map (Over.homMk g rfl : Over.mk (g ≫ τ.2.1) ⟶ Over.mk τ.2.1) =
      P.map
        (Over.homMk g rfl : Over.mk (g ≫ τ.1) ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom := by
  have := isStronglyCartesian_f₀_homMk hp hf₀ g τ.2.1
  have := isHomLift_P_homMk_comp hP g τ
  exact IsStronglyCartesian.fac p g _ (f' := g) (g := 𝟙 T') (Category.id_comp g).symm _

/-- The restriction of a triple along `g : T' ⟶ T`. -/
noncomputable abbrev Trip.restrict {T T' : 𝒞} (g : T' ⟶ T) (τ : Trip p f₀ P T) :
    Trip p f₀ P T' :=
  have := Trip.isHomLift_restrictHom hp hf₀ hP g τ
  have := hp.isStronglyCartesian_homLift (𝟙 T') (Trip.restrictHom hp hf₀ hP g τ)
  have := IsStronglyCartesian.isIso_of_base_isIso p (𝟙 T') (Trip.restrictHom hp hf₀ hP g τ)
  ⟨g ≫ τ.1, g ≫ τ.2.1, asIso (Trip.restrictHom hp hf₀ hP g τ),
    Trip.isHomLift_restrictHom hp hf₀ hP g τ⟩

/-- The first morphism of the restriction of `τ` along `g` is `g ≫ τ.1`. -/
@[simp] lemma Trip.restrict_fst {T T' : 𝒞} (g : T' ⟶ T) (τ : Trip p f₀ P T) :
    (Trip.restrict hp hf₀ hP g τ).1 = g ≫ τ.1 := rfl

/-- The second morphism of the restriction of `τ` along `g` is `g ≫ τ.2.1`. -/
@[simp] lemma Trip.restrict_snd_fst {T T' : 𝒞} (g : T' ⟶ T) (τ : Trip p f₀ P T) :
    (Trip.restrict hp hf₀ hP g τ).2.1 = g ≫ τ.2.1 := rfl

/-- The comparison of the restriction of `τ` along `g` is `Trip.restrictHom`. -/
@[simp] lemma Trip.restrict_iso_hom {T T' : 𝒞} (g : T' ⟶ T) (τ : Trip p f₀ P T) :
    (Trip.restrict hp hf₀ hP g τ).2.2.1.hom = Trip.restrictHom hp hf₀ hP g τ := rfl

/-- The morphism of the 2-fibre product from the object named by the restriction of a triple to
the object named by the triple; it lies over `g`. -/
noncomputable def Trip.objHom {T T' : 𝒞} (g : T' ⟶ T) (τ : Trip p f₀ P T) :
    (Trip.restrict hp hf₀ hP g τ).obj ⟶ τ.obj where
  hbase := g
  a := Over.homMk g rfl
  b := Over.homMk g rfl
  ha := isHomLift_forget_homMk g τ.1
  hb := isHomLift_forget_homMk g τ.2.1
  w := (Trip.restrictHom_fac hp hf₀ hP g τ).symm

end Restrict

/-! ### Sections of a representing presheaf -/

section Sections

variable (hf₀ : f₀ ⋙ p = Over.forget U₀) (hP : P ⋙ p = Over.forget A) {F : 𝒞ᵒᵖ ⥤ Type a}
  (e : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.structureFunctor (Over.forget A) (Over.forget U₀) p
      P f₀)
    (presheafOfCategories (F ⋙ typeToCat)).p)

/-- The section of the representing presheaf named by a triple. -/
noncomputable def tripSection {T : 𝒞} (τ : Trip p f₀ P T) : F.obj (op T) :=
  PresheafOfCategories.sectionOfObj e τ.obj rfl

/-- Restricting the section named by a triple is naming the restricted triple. -/
lemma map_tripSection {T T' : 𝒞} (g : T' ⟶ T) (τ : Trip p f₀ P T) :
    F.map g.op (tripSection e τ) = tripSection e (Trip.restrict hp hf₀ hP g τ) :=
  (PresheafOfCategories.sectionOfObj_map e (z := τ.obj)
    (z' := (Trip.restrict hp hf₀ hP g τ).obj) (W := T) (W' := T') rfl rfl g _
    (IsHomLift.map _ (Trip.objHom hp hf₀ hP g τ))).symm

/-- **Equal sections come from triples related by a vertical compatibility.** The converse of
`AlgebraicGeometry.Stack.ThickeningPushout.tripSection_eq_of_hom`. -/
lemma exists_hom_of_tripSection_eq {T : 𝒞} (τ τ' : Trip p f₀ P T)
    (hs : tripSection e τ' = tripSection e τ) :
    ∃ (ht : τ.1 = τ'.1) (hs : τ.2.1 = τ'.2.1),
      P.map (Over.homMk (𝟙 T) (by simp [ht]) : Over.mk τ'.1 ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom =
        τ'.2.2.1.hom ≫ f₀.map (Over.homMk (𝟙 T) (by simp [hs]) :
          Over.mk τ'.2.1 ⟶ Over.mk τ.2.1) := by
  obtain ⟨φ, hφ⟩ := PresheafOfCategories.exists_hom_of_sectionOfObj_map e (z := τ.obj)
    (z' := τ'.obj) (W := T) (W' := T) rfl rfl (𝟙 T) (by
      show tripSection e τ' = F.map (𝟙 T).op (tripSection e τ)
      rw [hs, op_id, F.map_id]
      rfl)
  have hb : φ.hbase = 𝟙 T :=
    (IsHomLift.fac' (TwoFibreProductOver.structureFunctor (Over.forget A) (Over.forget U₀) p
      P f₀) (𝟙 T) φ).trans
      (by rw [Category.id_comp, eqToHom_trans]; exact eqToHom_refl _ _)
  have ha : (Over.forget A).IsHomLift (𝟙 T) φ.a := hb ▸ φ.ha
  have hbb : (Over.forget U₀).IsHomLift (𝟙 T) φ.b := hb ▸ φ.hb
  have hal : φ.a.left = 𝟙 T := (IsHomLift.eq_of_isHomLift (Over.forget A) _ φ.a).symm
  have hbl : φ.b.left = 𝟙 T := (IsHomLift.eq_of_isHomLift (Over.forget U₀) _ φ.b).symm
  have ht : τ.1 = τ'.1 := by simpa [hal] using Over.w φ.a
  have hs' : τ.2.1 = τ'.2.1 := by simpa [hbl] using Over.w φ.b
  refine ⟨ht, hs', ?_⟩
  have ha1 : φ.a = (Over.homMk (𝟙 T) (by simp [ht]) : Over.mk τ'.1 ⟶ Over.mk τ.1) :=
    Over.OverMorphism.ext hal
  have hb1 : φ.b = (Over.homMk (𝟙 T) (by simp [hs']) : Over.mk τ'.2.1 ⟶ Over.mk τ.2.1) :=
    Over.OverMorphism.ext hbl
  have hw : P.map φ.a ≫ τ.2.2.1.hom = τ'.2.2.1.hom ≫ f₀.map φ.b := φ.w
  rwa [ha1, hb1] at hw

/-- Distinct triples name distinct sections: the fibres of the two slices are discrete. -/
lemma tripSection_injective (T : 𝒞) :
    Function.Injective (tripSection (T := T) e) := by
  intro τ τ' h
  obtain ⟨ht, hs, hw⟩ := exists_hom_of_tripSection_eq e τ' τ h
  obtain ⟨t, s, γ, _⟩ := τ
  obtain ⟨t', s', γ', _⟩ := τ'
  dsimp only at ht hs hw
  subst ht hs
  have h₁ : (Over.homMk (𝟙 T) (by simp) : Over.mk t' ⟶ Over.mk t') = 𝟙 _ :=
    Over.OverMorphism.ext rfl
  have h₂ : (Over.homMk (𝟙 T) (by simp) : Over.mk s' ⟶ Over.mk s') = 𝟙 _ :=
    Over.OverMorphism.ext rfl
  simp only [h₁, h₂, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at hw
  obtain rfl : γ = γ' := Iso.ext hw.symm
  rfl

/-- Every section is named by a triple. -/
lemma tripSection_surjective (T : 𝒞) :
    Function.Surjective (tripSection (T := T) e) := by
  intro σ
  obtain ⟨z, hz, rfl⟩ := PresheafOfCategories.exists_sectionOfObj e σ
  obtain ⟨base, ⟨xl, xr, xh⟩, ⟨yl, yr, yh⟩, hx, hy, iso, vert⟩ := z
  change base = T at hz
  change xl = base at hx
  change yl = base at hy
  subst hz hx hy
  exact ⟨⟨xh, yh, iso, vert⟩, rfl⟩

/-- **The sections of the representing presheaf over `T` are the triples over `T`.** -/
noncomputable def tripEquiv (T : 𝒞) : Trip p f₀ P T ≃ F.obj (op T) :=
  Equiv.ofBijective _ ⟨tripSection_injective e T, tripSection_surjective e T⟩

/-- `tripEquiv` sends a triple to the section it names. -/
@[simp] lemma tripEquiv_apply {T : 𝒞} (τ : Trip p f₀ P T) :
    tripEquiv e T τ = tripSection e τ := rfl

/-- A triple from a vertical morphism, which is invertible because the fibres of `p` are
groupoids. -/
noncomputable abbrev Trip.mk' {T : 𝒞} (t : T ⟶ A) (s : T ⟶ U₀)
    (γ : P.obj (Over.mk t) ⟶ f₀.obj (Over.mk s)) (hγ : p.IsHomLift (𝟙 T) γ) : Trip p f₀ P T :=
  have := hp.isStronglyCartesian_homLift (𝟙 T) γ
  have := IsStronglyCartesian.isIso_of_base_isIso p (𝟙 T) γ
  ⟨t, s, asIso γ, hγ⟩

/-- The first morphism of `Trip.mk' hp t s γ hγ` is `t`. -/
@[simp] lemma Trip.mk'_fst {T : 𝒞} (t : T ⟶ A) (s : T ⟶ U₀)
    (γ : P.obj (Over.mk t) ⟶ f₀.obj (Over.mk s)) (hγ : p.IsHomLift (𝟙 T) γ) :
    (Trip.mk' hp t s γ hγ).1 = t := rfl

/-- The second morphism of `Trip.mk' hp t s γ hγ` is `s`. -/
@[simp] lemma Trip.mk'_snd_fst {T : 𝒞} (t : T ⟶ A) (s : T ⟶ U₀)
    (γ : P.obj (Over.mk t) ⟶ f₀.obj (Over.mk s)) (hγ : p.IsHomLift (𝟙 T) γ) :
    (Trip.mk' hp t s γ hγ).2.1 = s := rfl

/-- The comparison of `Trip.mk' hp t s γ hγ` has forward morphism `γ`. -/
@[simp] lemma Trip.mk'_iso_hom {T : 𝒞} (t : T ⟶ A) (s : T ⟶ U₀)
    (γ : P.obj (Over.mk t) ⟶ f₀.obj (Over.mk s)) (hγ : p.IsHomLift (𝟙 T) γ) :
    (Trip.mk' hp t s γ hγ).2.2.1.hom = γ := rfl

/-- **Restriction of sections, from a morphism of triples.** If `g : T' ⟶ T` carries the two
morphisms of `τ'` to those of `τ` and the comparisons are compatible with the images of `g`, the
section named by `τ'` is the restriction along `g` of the section named by `τ`. -/
lemma tripSection_eq_map_of_hom {T T' : 𝒞} (g : T' ⟶ T) (τ : Trip p f₀ P T)
    (τ' : Trip p f₀ P T') (ht : g ≫ τ.1 = τ'.1) (hs : g ≫ τ.2.1 = τ'.2.1)
    (hw : P.map (Over.homMk g ht : Over.mk τ'.1 ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom =
      τ'.2.2.1.hom ≫ f₀.map (Over.homMk g hs : Over.mk τ'.2.1 ⟶ Over.mk τ.2.1)) :
    tripSection e τ' = F.map g.op (tripSection e τ) := by
  let φ : τ'.obj ⟶ τ.obj :=
    { hbase := g
      a := Over.homMk g ht
      b := Over.homMk g hs
      ha := IsHomLift.of_fac' _ g _ rfl rfl (by simp)
      hb := IsHomLift.of_fac' _ g _ rfl rfl (by simp)
      w := hw }
  exact PresheafOfCategories.sectionOfObj_map e (z := τ.obj) (z' := τ'.obj) (W := T) (W' := T')
    rfl rfl g φ (IsHomLift.map _ φ)

/-- Two triples over `T` related by a vertical compatibility name the same section. -/
lemma tripSection_eq_of_hom {T : 𝒞} (τ τ' : Trip p f₀ P T) (ht : τ.1 = τ'.1)
    (hs : τ.2.1 = τ'.2.1)
    (hw : P.map (Over.homMk (𝟙 T) (by simp [ht]) : Over.mk τ'.1 ⟶ Over.mk τ.1) ≫ τ.2.2.1.hom =
      τ'.2.2.1.hom ≫ f₀.map (Over.homMk (𝟙 T) (by simp [hs]) : Over.mk τ'.2.1 ⟶ Over.mk τ.2.1)) :
    tripSection e τ' = tripSection e τ := by
  rw [tripSection_eq_map_of_hom e (𝟙 T) τ τ' (by simp [ht]) (by simp [hs]) hw, op_id,
    F.map_id]
  rfl

end Sections

end AlgebraicGeometry.Stack.ThickeningPushout

end
