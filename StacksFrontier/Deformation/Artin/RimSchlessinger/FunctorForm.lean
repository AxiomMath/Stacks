module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreservingNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.Deformation.Artin.RimSchlessinger
import StacksFrontier.Deformation.Artin.RimSchlessinger.FibreProductLift

/-!
# Condition (RS) for a functor

Let `S` be a scheme contained in a big fppf site `B`. Condition (RS) of Stacks 07WP is stated in
`Deformation.Artin.SatisfiesRS` for a category fibred in groupoids over the big fppf site of
`S`. Section 07XZ, and for the locally Noetherian site Section 0GE6 (axiom [2]), read it for a
*functor* `F`: given a pushout `Y' = Y ⨿_X X'` of spectra of Artinian local rings of finite type
over `S` along a closed immersion `X ⟶ X'`, the map
`F(Y') ⟶ F(Y) ×_{F(X)} F(X')` is a bijection. This file records that reading, in the form
"every compatible pair over `Y` and `X'` comes from exactly one element over `Y'`", for a
presheaf on the big fppf site and for a presheaf on the locally Noetherian site of Stacks 0GE4,
and compares it with Stacks 07WP.

## Main definitions

* `Deformation.Artin.SatisfiesRSFunctor`: condition (RS) for a presheaf on the big fppf site.
* `AlgebraicGeometry.LocallyNoetherianOver.SatisfiesRS`: condition (RS), axiom [2] of Section
  0GE6, for a presheaf on the locally Noetherian site.

## Main results

* `AlgebraicGeometry.LocallyNoetherianOver.satisfiesRS_of_satisfiesRSFunctor`: (RS) passes to
  the restriction of a presheaf to the locally Noetherian site.
* `Deformation.Artin.satisfiesRSFunctor_of_satisfiesRS`: a presheaf of sets whose category
  fibred in groupoids `AlgebraicGeometry.Stack.fibredCategory` satisfies (RS) in the sense of
  Stacks 07WP satisfies (RS) in the functor form.

## Implementation notes

The fibres of `AlgebraicGeometry.Stack.fibredCategory` are discrete: an object of the fibre over
`V` is an element of `F(V)`, two objects are isomorphic exactly when the elements are equal, and
there is at most one morphism between them. The chosen pullback of the element `t` along
`f : V ⟶ U` is therefore the element `F(f)(t)`, so the comparison functor of Stacks 07WP is, up
to these identifications, the map `F(Y') ⟶ F(Y) ×_{F(X)} F(X')`: essential surjectivity gives
existence and full faithfulness gives uniqueness.

## References

* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
* [Stacks Project, Tag 0GE6](https://stacks.math.columbia.edu/tag/0GE6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (RS) for a presheaf on the big fppf site of `S`.** For every pushout
`Y' = Y ⨿_X X'` of spectra of Artinian local rings of finite type over `S` along a closed
immersion `X ⟶ X'`, every pair of elements over `Y` and `X'` with the same restriction to `X`
is the pair of restrictions of exactly one element over `Y'`. -/
abbrev SatisfiesRSFunctor (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y') (j' : Y ⟶ Y'),
    i ≫ i' = j ≫ j' →
    IsArtinianLocal B S hS X → IsArtinianLocal B S hS X' →
      IsArtinianLocal B S hS Y → IsArtinianLocal B S hS Y' →
      IsFiniteTypeOver B S hS X → IsFiniteTypeOver B S hS X' →
      IsFiniteTypeOver B S hS Y → IsFiniteTypeOver B S hS Y' →
    IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
      IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map j)
        ((BigFppfOver.toScheme B S hS).map i') ((BigFppfOver.toScheme B S hS).map j') →
    ∀ (a : F.obj (op Y)) (b : F.obj (op X')), F.map j.op a = F.map i.op b →
      ∃! t : F.obj (op Y'), F.map j'.op t = a ∧ F.map i'.op t = b

end Deformation.Artin

namespace AlgebraicGeometry.LocallyNoetherianOver

open Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Axiom [2] of Section 0GE6: condition (RS) for a presheaf on the locally Noetherian site
of `S`.** For every pushout `Y' = Y ⨿_X X'` of spectra of Artinian local rings of finite type
over `S` along a closed immersion `X ⟶ X'`, every pair of elements over `Y` and `X'` with the
same restriction to `X` is the pair of restrictions of exactly one element over `Y'`. -/
abbrev SatisfiesRS (F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {X X' Y Y' : LocallyNoetherianOver B S hS} (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y')
    (j' : Y ⟶ Y'), i ≫ i' = j ≫ j' →
    IsArtinianLocal B S hS X.obj → IsArtinianLocal B S hS X'.obj →
      IsArtinianLocal B S hS Y.obj → IsArtinianLocal B S hS Y'.obj →
      IsFiniteTypeOver B S hS X.obj → IsFiniteTypeOver B S hS X'.obj →
      IsFiniteTypeOver B S hS Y.obj → IsFiniteTypeOver B S hS Y'.obj →
    IsClosedImmersion ((LocallyNoetherianOver.toScheme B S hS).map i) →
      IsPushout ((LocallyNoetherianOver.toScheme B S hS).map i)
        ((LocallyNoetherianOver.toScheme B S hS).map j)
        ((LocallyNoetherianOver.toScheme B S hS).map i')
        ((LocallyNoetherianOver.toScheme B S hS).map j') →
    ∀ (a : F.obj (op Y)) (b : F.obj (op X')), F.map j.op a = F.map i.op b →
      ∃! t : F.obj (op Y'), F.map j'.op t = a ∧ F.map i'.op t = b

/-- Condition (RS) passes from a presheaf on the big fppf site to its restriction to the locally
Noetherian site: the squares (RS) quantifies over on the smaller site are among those it
quantifies over on the bigger one. -/
theorem satisfiesRS_of_satisfiesRSFunctor (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v)
    (hF : SatisfiesRSFunctor B S hS F) :
    SatisfiesRS B S hS ((ObjectProperty.ι _).op ⋙ F) :=
  fun i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo a b hab =>
    hF i.hom j.hom i'.hom j'.hom (congrArg InducedCategory.Hom.hom w)
      hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo a b hab

end AlgebraicGeometry.LocallyNoetherianOver

/-! ### Comparison with Stacks 07WP -/

namespace Deformation.Artin

open Functor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The object of the fibre over `V` of the category fibred in groupoids of `F` given by an
element `t` of `F(V)`. -/
abbrev fibredCategoryFiberMk {V : BigFppfOver B S hS} (t : F.obj (op V)) :
    (Stack.fibredCategory B S hS F).val.p.Fiber V :=
  Fiber.mk (p := (Stack.fibredCategory B S hS F).val.p)
    (a := (⟨V, Discrete.mk t⟩ : (Stack.fibredCategory B S hS F).val.obj)) rfl

/-- A morphism of the category fibred in groupoids of `F` sends the element of its target to the
element of its source. -/
theorem fiber_as_eq_of_hom {x y : (Stack.fibredCategory B S hS F).val.obj} (φ : x ⟶ y) :
    x.fiber.as = F.map φ.base.op y.fiber.as :=
  Discrete.eq_of_hom φ.fiber

/-- A morphism of the category fibred in groupoids of `F` is determined by its base. -/
theorem fibredCategory_hom_ext {x y : (Stack.fibredCategory B S hS F).val.obj} (φ ψ : x ⟶ y)
    (h : φ.base = ψ.base) : φ = ψ :=
  Pseudofunctor.CoGrothendieck.Hom.ext φ ψ h (by apply Discrete.hom_eq)

/-- Every object of a fibre of the category fibred in groupoids of `F` is the object given by an
element. -/
theorem exists_eq_fibredCategoryFiberMk {V : BigFppfOver B S hS}
    (z : (Stack.fibredCategory B S hS F).val.p.Fiber V) :
    ∃ t : F.obj (op V), z = fibredCategoryFiberMk t := by
  obtain ⟨⟨V', ⟨t⟩⟩, h⟩ := z
  change V' = V at h
  subst h
  exact ⟨t, rfl⟩

/-- A morphism of the category fibred in groupoids of `F` from an object over `V` to the object
given by `t`, lying over `f`, exhibits that object as the one given by `F(f)(t)`. -/
theorem fiberMk_eq_of_isHomLift {V U : BigFppfOver B S hS} (f : V ⟶ U) (t : F.obj (op U))
    {x : (Stack.fibredCategory B S hS F).val.obj}
    (hx : (Stack.fibredCategory B S hS F).val.p.obj x = V)
    (m : x ⟶ (⟨U, Discrete.mk t⟩ : (Stack.fibredCategory B S hS F).val.obj))
    (hm : (Stack.fibredCategory B S hS F).val.p.IsHomLift f m) :
    (Fiber.mk hx : (Stack.fibredCategory B S hS F).val.p.Fiber V) =
      fibredCategoryFiberMk (F.map f.op t) := by
  obtain ⟨V', ⟨s⟩⟩ := x
  change V' = V at hx
  subst hx
  have hm : (Stack.fibredCategory B S hS F).val.p.IsHomLift
      (show (Stack.fibredCategory B S hS F).val.p.obj ⟨V', ⟨s⟩⟩ ⟶
        (Stack.fibredCategory B S hS F).val.p.obj ⟨U, ⟨t⟩⟩ from f) m := hm
  have hb : f = m.base := IsHomLift.eq_of_isHomLift (p := (Stack.fibredCategory B S hS F).val.p)
    (a := ⟨V', ⟨s⟩⟩) (b := ⟨U, ⟨t⟩⟩) f m
  have h := fiber_as_eq_of_hom m
  rw [← hb] at h
  change s = F.map f.op t at h
  subst h
  rfl

/-- A morphism of the fibre over `V` lies over the identity of `V`. -/
theorem base_fiberInclusion_map {V : BigFppfOver B S hS} {t t' : F.obj (op V)}
    (φ : fibredCategoryFiberMk t ⟶ fibredCategoryFiberMk t') :
    (Fiber.fiberInclusion.map φ).base = 𝟙 V := by
  have h := IsHomLift.fac' (Stack.fibredCategory B S hS F).val.p (𝟙 V)
    (Fiber.fiberInclusion.map φ)
  exact h.trans (eqToHom_refl V rfl)

/-- Two objects of the fibre over `V` given by elements are related by a morphism exactly when
the elements are equal. -/
theorem eq_of_fiber_hom {V : BigFppfOver B S hS} {t t' : F.obj (op V)}
    (φ : fibredCategoryFiberMk t ⟶ fibredCategoryFiberMk t') : t = t' := by
  have h := fiber_as_eq_of_hom (Fiber.fiberInclusion.map φ)
  rw [base_fiberInclusion_map φ] at h
  change t = F.map (𝟙 V).op t' at h
  simpa using h

/-- Between two objects of a fibre of the category fibred in groupoids of `F` there is at most
one morphism. -/
instance subsingleton_fiber_hom {V : BigFppfOver B S hS}
    (z z' : (Stack.fibredCategory B S hS F).val.p.Fiber V) : Subsingleton (z ⟶ z') := by
  obtain ⟨t, rfl⟩ := exists_eq_fibredCategoryFiberMk z
  obtain ⟨t', rfl⟩ := exists_eq_fibredCategoryFiberMk z'
  refine ⟨fun φ ψ => Fiber.hom_ext (fibredCategory_hom_ext _ _ ?_)⟩
  rw [base_fiberInclusion_map φ, base_fiberInclusion_map ψ]

/-- A choice of pullbacks of the category fibred in groupoids of `F` pulls the element `t` back to
`F(f)(t)`. -/
theorem pullbackFunctor_obj_eq (c : (Stack.fibredCategory B S hS F).val.p.ChoiceOfPullbacks)
    {V U : BigFppfOver B S hS} (f : V ⟶ U) (t : F.obj (op U)) :
    (c.pullbackFunctor f).obj (fibredCategoryFiberMk t) =
      fibredCategoryFiberMk (F.map f.op t) :=
  fiberMk_eq_of_isHomLift f t ((c.pullbackFunctor f).obj (fibredCategoryFiberMk t)).2
    (c.map f (fibredCategoryFiberMk t))
    (c.isStronglyCartesian f (fibredCategoryFiberMk t)).toIsHomLift

/-- **Condition (RS) of Stacks 07WP gives condition (RS) in the functor form.** If the category
fibred in groupoids of a presheaf of sets `F` on the big fppf site of `S` satisfies (RS), then
for every pushout `Y' = Y ⨿_X X'` of spectra of Artinian local rings of finite type over `S`
along a closed immersion, every compatible pair of elements of `F` over `Y` and `X'` is the pair
of restrictions of exactly one element over `Y'`.

Essential surjectivity of the comparison functor gives the element, full faithfulness its
uniqueness; the fibres being discrete, isomorphisms in them are equalities of elements. -/
theorem satisfiesRSFunctor_of_satisfiesRS
    (h : SatisfiesRS B S hS (Stack.fibredCategory B S hS F).val.p
      (Stack.fibredCategory B S hS F).isFiberedInGroupoids) :
    SatisfiesRSFunctor B S hS F := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo a b hab
  let : (Stack.fibredCategory B S hS F).val.p.IsFibered :=
    (Stack.fibredCategory B S hS F).isFiberedInGroupoids.isFibered
  have hE := h i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo
  let p := (Stack.fibredCategory B S hS F).val.p
  let c := p.chosenPullbacks
  let G := fiberSquareComparison p c j i j' i' w.symm
  have e : (c.pullbackFunctor j).obj (fibredCategoryFiberMk a) ≅
      (c.pullbackFunctor i).obj (fibredCategoryFiberMk b) :=
    eqToIso (by rw [pullbackFunctor_obj_eq, pullbackFunctor_obj_eq, hab])
  obtain ⟨z, ex, ey, -⟩ :=
    exists_fiber_of_fiberSquareComparison_essSurj p c j i j' i' w.symm _ _ e
  obtain ⟨t, rfl⟩ := exists_eq_fibredCategoryFiberMk z
  rw [pullbackFunctor_obj_eq] at ex ey
  refine ⟨t, ⟨eq_of_fiber_hom ex.hom, eq_of_fiber_hom ey.hom⟩, ?_⟩
  rintro t' ⟨h₁, h₂⟩
  have key : ∀ {W : BigFppfOver B S hS} (g : W ⟶ Y') (s : F.obj (op W)),
      F.map g.op t' = s → F.map g.op t = s →
      (c.pullbackFunctor g).obj (fibredCategoryFiberMk t') =
        (c.pullbackFunctor g).obj (fibredCategoryFiberMk t) := by
    rintro W g s rfl h
    rw [pullbackFunctor_obj_eq, pullbackFunctor_obj_eq, h]
  have κ : G.obj (fibredCategoryFiberMk t') ≅ G.obj (fibredCategoryFiberMk t) :=
    CategoricalPullback.mkIso (eqToIso (key j' _ h₁ (eq_of_fiber_hom ex.hom)))
      (eqToIso (key i' _ h₂ (eq_of_fiber_hom ey.hom))) (Subsingleton.elim _ _)
  exact eq_of_fiber_hom ((Functor.FullyFaithful.ofFullyFaithful G).preimageIso κ).hom

end Deformation.Artin
