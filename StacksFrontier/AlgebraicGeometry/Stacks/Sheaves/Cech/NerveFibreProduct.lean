module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.Complex
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksCore.Tactic.StacksAttribute

/-!
# The Čech nerve of a covering is an iterated 2-fibre product

Let `f : U ⥤ X` be a functor over a base category `C`, viewed as a covering of `X`, and let
`U_n` be the degree `n` piece of its Čech nerve: the category of `n + 1` objects of `U` lying
over a common object of `X`, with vertical comparison isomorphisms. Then `U_0` is `U` itself,
and `U_{n + 1}` is the 2-fibre product `U ×_X U_n` of categories over `C`, the first factor
mapping to `X` by `f` and the second by the projection of the nerve. Iterating, `U_n` is the
`(n + 1)`-fold 2-fibre product `U ×_X ⋯ ×_X U`.

## Main definitions

* `Stacks.RelativeCech.Tuple.coordinate`: the functor `U_n ⥤ U` reading off one coordinate.
* `Stacks.RelativeCech.nerveFibreProduct`: the 2-fibre product `U ×_X U_n` over `C`.
* `Stacks.RelativeCech.fibreProductToNerve`: the canonical functor `U ×_X U_n ⥤ U_{n + 1}`,
  prepending a coordinate to a tuple.

## Main results

* `Stacks.RelativeCech.isEquivalence_coordinate_zero`: `U_0` is `U`.
* `Stacks.RelativeCech.isEquivalence_fibreProductToNerve`: `U_{n + 1}` is `U ×_X U_n`.
* `Stacks.RelativeCech.isIso_limit_pre_fibreProductToNerve`: consequently the sections of a
  presheaf over `U_{n + 1}` are its sections over `U ×_X U_n`.
* `Stacks.RelativeCech.fibreProductToNerve_comp_coordinate_zero` and
  `Stacks.RelativeCech.fibreProductToNerve_comp_reindex`: that identification carries the two
  projections of the 2-fibre product to the first coordinate and to the remaining coordinates
  of a tuple, so it is an identification over `U` and over `U_n`, hence over `X`.

## Implementation notes

The 2-fibre product used is `CategoryTheory.TwoFibreProductOver`, the 2-fibre product of
categories *over* `C`, whose comparison isomorphisms are required to be vertical, as are the
comparison isomorphisms of a Čech tuple. The canonical functor goes *from* the 2-fibre product,
where prepending a coordinate is strict on objects and morphisms. It is not bijective on
objects, since a tuple determines its base object of `C` only through its target.

## References

* [Stacks Project, Tag 06X3](https://stacks.math.columbia.edu/tag/06X3)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.RelativeCech

universe vA vC vU vX uA uC uU uX

variable {C : Type uC} [Category.{vC} C] {U : Type uU} [Category.{vU} U]
  {X : Type uX} [Category.{vX} X] (p : X ⥤ C) (f : U ⥤ X)

/-- The functor reading off the `i`-th coordinate of a Čech tuple. -/
public def Tuple.coordinate {n : ℕ} (i : Fin (n + 1)) : Tuple p f n ⥤ U where
  obj a := a.source i
  map g := Tuple.Hom.source g i
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The 2-fibre product `U ×_X U_n` over `C` of the covering `f : U ⥤ X` with the degree `n`
piece of its Čech nerve, taken along `f` and along the projection of the nerve. -/
public abbrev nerveFibreProduct (n : ℕ) : Type (max uC uU uX vX) :=
  TwoFibreProductOver (f ⋙ p) (Tuple.projection p f n ⋙ p) p f (Tuple.projection p f n)

/-- The canonical functor `U ×_X U_n ⥤ U_{n + 1}`: an object of `U` and a tuple of length
`n + 1`, together with a vertical isomorphism of their images in `X`, form a tuple of length
`n + 2` whose first coordinate is the given object. -/
public def fibreProductToNerve (n : ℕ) : nerveFibreProduct p f n ⥤ Tuple p f (n + 1) where
  obj P :=
    { target := P.y.target
      source := Fin.cons P.x P.y.source
      comparison := Fin.cons P.iso P.y.comparison
      comparison_lift := Fin.cons (by
        have h : p.obj P.y.target = P.base := P.hy
        rw [h]; exact P.vertical) P.y.comparison_lift }
  map {P Q} k :=
    { target := Tuple.Hom.target (a := P.y) (b := Q.y) k.b
      source := Fin.cons k.a (Tuple.Hom.source (a := P.y) (b := Q.y) k.b)
      comparison_naturality :=
        Fin.cons (by exact k.w) (Tuple.Hom.comparison_naturality (a := P.y) (b := Q.y) k.b) }
  map_id P := by
    refine Stacks.Cech.tupleHom_ext rfl (funext fun i => ?_)
    cases i using Fin.cases <;> rfl
  map_comp k l := by
    refine Stacks.Cech.tupleHom_ext rfl (funext fun i => ?_)
    cases i using Fin.cases <;> rfl

/-- The tuple obtained by prepending a coordinate lies over the same object of `X`. -/
@[simp] public theorem fibreProductToNerve_obj_target (n : ℕ) (P : nerveFibreProduct p f n) :
    ((fibreProductToNerve p f n).obj P).target = P.y.target := rfl

/-- The coordinates of the tuple obtained by prepending a coordinate. -/
@[simp] public theorem fibreProductToNerve_obj_source (n : ℕ) (P : nerveFibreProduct p f n) :
    ((fibreProductToNerve p f n).obj P).source = Fin.cons P.x P.y.source := rfl

/-- The comparison isomorphisms of the tuple obtained by prepending a coordinate; the new one
is the comparison isomorphism of the 2-fibre product. -/
@[simp] public theorem fibreProductToNerve_obj_comparison (n : ℕ) (P : nerveFibreProduct p f n) :
    ((fibreProductToNerve p f n).obj P).comparison = Fin.cons P.iso P.y.comparison := rfl

/-- Prepending a coordinate and then dropping it again is the second projection of the 2-fibre
product. -/
public theorem fibreProductToNerve_comp_reindex (n : ℕ) :
    fibreProductToNerve p f n ⋙ Tuple.reindex p f (Fin.succ : Fin (n + 1) → Fin (n + 2)) =
      TwoFibreProductOver.snd (f ⋙ p) (Tuple.projection p f n ⋙ p) p f
        (Tuple.projection p f n) :=
  rfl

/-- The first coordinate of the tuple obtained by prepending a coordinate is the first
projection of the 2-fibre product. -/
public theorem fibreProductToNerve_comp_coordinate_zero (n : ℕ) :
    fibreProductToNerve p f n ⋙ Tuple.coordinate p f (0 : Fin (n + 2)) =
      TwoFibreProductOver.fst (f ⋙ p) (Tuple.projection p f n ⋙ p) p f
        (Tuple.projection p f n) :=
  rfl

/-- Prepending a coordinate is faithful: a morphism of the 2-fibre product is recovered from
the first coordinate and the target and coordinates of the second component. -/
private lemma faithful_fibreProductToNerve (n : ℕ) : (fibreProductToNerve p f n).Faithful where
  map_injective {P Q} k l h := by
    have hs : ∀ i, Tuple.Hom.source ((fibreProductToNerve p f n).map k) i
        = Tuple.Hom.source ((fibreProductToNerve p f n).map l) i := fun i => by rw [h]
    have ht : Tuple.Hom.target ((fibreProductToNerve p f n).map k)
        = Tuple.Hom.target ((fibreProductToNerve p f n).map l) := by rw [h]
    exact TwoFibreProductOver.Hom.ext' (hs 0)
      (Stacks.Cech.tupleHom_ext ht (funext fun i => hs i.succ))

/-- Let `i₁ : x₁ ⟶ y₁` and `i₂ : x₂ ⟶ y₂` be vertical isomorphisms over `c₁` and `c₂`. A
morphism `a : x₁ ⟶ x₂` and a morphism `t : y₁ ⟶ y₂` that agree through them lie over one and
the same morphism `c₁ ⟶ c₂`. -/
private lemma base_eq_of_verticalComparisons {c₁ c₂ : C} {x₁ y₁ x₂ y₂ : X}
    (hx₁ : p.obj x₁ = c₁) (hy₁ : p.obj y₁ = c₁) (hx₂ : p.obj x₂ = c₂) (hy₂ : p.obj y₂ = c₂)
    {i₁ : x₁ ⟶ y₁} {i₂ : x₂ ⟶ y₂} {a : x₁ ⟶ x₂} {t : y₁ ⟶ y₂}
    (h₁ : p.map i₁ = eqToHom hx₁ ≫ eqToHom hy₁.symm)
    (h₂ : p.map i₂ = eqToHom hx₂ ≫ eqToHom hy₂.symm)
    (hw : a ≫ i₂ = i₁ ≫ t) :
    eqToHom hy₁.symm ≫ p.map t ≫ eqToHom hy₂
      = eqToHom hx₁.symm ≫ p.map a ≫ eqToHom hx₂ := by
  have key : p.map a ≫ (eqToHom hx₂ ≫ eqToHom hy₂.symm)
      = (eqToHom hx₁ ≫ eqToHom hy₁.symm) ≫ p.map t := by
    rw [← h₁, ← h₂, ← p.map_comp, ← p.map_comp, hw]
  rw [← cancel_epi (eqToHom hx₁), ← cancel_mono (eqToHom hy₂.symm)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.comp_id] at key ⊢
  exact key.symm

/-- Prepending a coordinate is full: the base morphism of a morphism of the 2-fibre product is
forced by the first coordinate, because the comparison isomorphisms are vertical. -/
private lemma full_fibreProductToNerve (n : ℕ) : (fibreProductToNerve p f n).Full where
  map_surjective {P Q} φ := by
    obtain ⟨t, s, w⟩ := φ
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : P.x ⟶ Q.x, a₀ = s 0 := ⟨s 0, rfl⟩
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : (Tuple.projection p f n).obj P.y ⟶
        (Tuple.projection p f n).obj Q.y, t₀ = t := ⟨t, rfl⟩
    have hv : ∀ R : nerveFibreProduct p f n,
        p.map R.iso.hom = eqToHom R.hx ≫ eqToHom R.hy.symm := fun R => by
      have := R.vertical
      rw [IsHomLift.fac' p (𝟙 R.base) R.iso.hom]; simp
    have w₀ : f.map a₀ ≫ Q.iso.hom = P.iso.hom ≫ t₀ := by
      subst ha₀ ht₀; exact w 0
    refine ⟨TwoFibreProductOver.Hom.mk' a₀
      { target := t₀
        source := fun i => s i.succ
        comparison_naturality := fun i => by subst ht₀; exact w i.succ }
      (base_eq_of_verticalComparisons p P.hx P.hy Q.hx Q.hy (hv P) (hv Q) w₀)
      (by subst ha₀ ht₀; exact w 0), ?_⟩
    refine Stacks.Cech.tupleHom_ext ht₀ (funext fun i => ?_)
    cases i using Fin.cases
    · exact ha₀
    · rfl

/-- Prepending a coordinate is essentially surjective: a tuple of length `n + 2` is its first
coordinate together with the tuple of its remaining coordinates, compared by the first of its
comparison isomorphisms. -/
private lemma essSurj_fibreProductToNerve (n : ℕ) : (fibreProductToNerve p f n).EssSurj where
  mem_essImage A := by
    have := A.comparison_lift 0
    refine ⟨{ base := p.obj A.target
              x := A.source 0
              y := { target := A.target
                     source := fun i => A.source i.succ
                     comparison := fun i => A.comparison i.succ
                     comparison_lift := fun i => A.comparison_lift i.succ }
              hx := IsHomLift.domain_eq p (𝟙 (p.obj A.target)) (A.comparison 0).hom
              hy := rfl
              iso := A.comparison 0
              vertical := A.comparison_lift 0 },
      ⟨Stacks.Cech.tupleIso (Iso.refl A.target)
        (Fin.cons (Iso.refl _) fun _ => Iso.refl _) ?_⟩⟩
    have key : ∀ i, f.map (𝟙 (A.source i)) ≫ (A.comparison i).hom
        = (A.comparison i).hom ≫ 𝟙 A.target := fun i => by simp
    exact Fin.cons (key 0) fun j => key j.succ

/-- The degree `n + 1` piece of the Čech nerve of a covering `f : U ⥤ X` is the 2-fibre product
`U ×_X U_n` of the covering with the degree `n` piece: prepending a coordinate is an equivalence
of categories. -/
@[stacks 06X3 "the nerve in degree n + 1 is the 2-fibre product of the covering with degree n"]
public theorem isEquivalence_fibreProductToNerve (n : ℕ) :
    (fibreProductToNerve p f n).IsEquivalence where
  faithful := faithful_fibreProductToNerve p f n
  full := full_fibreProductToNerve p f n
  essSurj := essSurj_fibreProductToNerve p f n

/-- Sections of a presheaf over the degree `n + 1` piece of the Čech nerve are its sections
over the 2-fibre product `U ×_X U_n`: the comparison of limits along the identification is an
isomorphism. -/
public theorem isIso_limit_pre_fibreProductToNerve {A : Type uA} [Category.{vA} A] (n : ℕ)
    (F : (Tuple p f (n + 1))ᵒᵖ ⥤ A) [Limits.HasLimit F]
    [Limits.HasLimit ((fibreProductToNerve p f n).op ⋙ F)] :
    IsIso (Limits.limit.pre F (fibreProductToNerve p f n).op) := by
  have := isEquivalence_fibreProductToNerve p f n
  infer_instance

/-- The degree `0` piece of the Čech nerve of a covering `f : U ⥤ X` is the covering `U` itself:
reading off the single coordinate of a tuple is an equivalence of categories. -/
@[stacks 06X3 "the nerve in degree zero is the covering"]
public theorem isEquivalence_coordinate_zero :
    (Tuple.coordinate p f (0 : Fin 1)).IsEquivalence where
  faithful :=
    { map_injective := fun {a b} g h hgh => by
        have hs : ∀ i : Fin 1, Tuple.Hom.source g i = Tuple.Hom.source h i := fun i => by
          rw [Fin.fin_one_eq_zero i]
          exact hgh
        refine Stacks.Cech.tupleHom_ext ?_ (funext hs)
        have hg := Tuple.Hom.comparison_naturality g 0
        have hh := Tuple.Hom.comparison_naturality h 0
        rw [hs 0] at hg
        rw [← cancel_epi (a.comparison 0).hom, ← hg, ← hh] }
  full :=
    { map_surjective := fun {a b} g =>
        ⟨{ target := (a.comparison 0).inv ≫ f.map g ≫ (b.comparison 0).hom
           source := Fin.cons g fun i => i.elim0
           comparison_naturality :=
             Fin.cons (Iso.hom_inv_id_assoc (a.comparison 0)
               (f.map g ≫ (b.comparison 0).hom)).symm fun i => i.elim0 }, rfl⟩ }
  essSurj :=
    { mem_essImage := fun u =>
        ⟨{ target := f.obj u
           source := fun _ => u
           comparison := fun _ => Iso.refl _
           comparison_lift := fun _ => IsHomLift.id rfl }, ⟨Iso.refl u⟩⟩ }

end Stacks.RelativeCech

end
