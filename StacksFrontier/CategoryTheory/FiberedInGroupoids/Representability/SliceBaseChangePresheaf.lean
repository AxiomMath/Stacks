module

public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePointOfSection
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeFibre

/-!
# The base change of a representable 1-morphism along a point of the base, as a fibre product

Let `C` be a category, let `a : A ⟶ X` be a morphism of `C`, let `Hp` and `Gp` be presheaves of
sets on the slice `C/X` and let `θ : El Hp ⥤ El Gp` be a 1-morphism over `C/X` between their
categories of elements, i.e. a morphism of presheaves `Hp ⟶ Gp`. A 1-morphism
`σ : C/A ⥤ El Gp` over `C/X` — a *point of `El Gp` with values in `A`* — produces two things,
and this file identifies them with each other.

1. The 2-fibre product `C/A ×_{σ, El Gp, θ} El Hp` over `C/X`, whose first projection is the
   base change of `θ` along the point `σ`. By
   `CategoryTheory.PresheafOfCategories.isEquivalence_toTwoFibreProduct` it is the category of
   elements of the presheaf `CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf` on
   `C/A`, and here that is upgraded to an equivalence *over* `C/A`
   (`StacksRepresentableCFG.EquivalenceOver`).
2. The fibre of `Hp ⟶ Gp` over the section of `Gp` over `A → X` that `σ` restricts from. By
   `CategoryTheory.OverShriek.isPullback_relocalizeFibreOfSectionMap` the relocalization along
   `a` of that fibre is the fibre product `Hp ×_{Gp} h_{A → X}` of presheaves on `C/X`.

Together: the base change of `θ` along a point of `Gp` with values in `A` is represented by a
presheaf on `C/A` whose relocalization to `C/X` is the fibre product of `Hp` with the
representable presheaf of `A → X` over `Gp`.

## Main results

* `CategoryTheory.PresheafOfCategories.isFiberedInGroupoids_fst_overMap`: the base change
  projection is fibred in groupoids over `C/A`.
* `CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_twoFibreProductPresheaf`: the
  base change is equivalent over `C/A` to the category of elements of
  `CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf`.
* `CategoryTheory.PresheafOfCategories.fibreOfSection_eq_twoFibreProductPresheaf`: that presheaf
  is the fibre of `Hp ⟶ Gp` over a section `β` of `Gp` over `A → X`, as soon as `β` restricts to
  the family of sections that `σ` names.
* `CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf`: its
  relocalization along `a` is the fibre product `Hp ×_{Gp} h_{A → X}`.
* `CategoryTheory.PresheafOfCategories.exists_pointOverMap_sectionOfBasedFunctor_eq`: that
  hypothesis holds for the point 2-Yoneda produces from a section `β` of `Gp` over `A → X`.
* `CategoryTheory.PresheafOfCategories.sectionFamily_eq_of_eq_at_id`: a compatible family of
  sections over the objects `(Over.map a).obj τ` is determined by its value at the terminal
  object of `C/A`.

## Implementation notes

The subpresheaf `CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf` and the fibre
`CategoryTheory.OverShriek.fibreOfSection` are *definitionally* the same presheaf once their
families of sections agree, because both are the subpresheaf of the restriction of `Hp` along
`CategoryTheory.Over.map a` cut out by an equation with a prescribed right-hand side.

The comparison morphism of the fibre product is existentially quantified: only the cartesian
square matters for a property of morphisms stable under base change.

The universes of the category `𝒟` in the 2-Yoneda section are independent of those of `C`.

The object `A → X` of `C/X` is spelled `CategoryTheory.Over.mk a` throughout, rather than as an
abstract `T` with `T.left`, `T.hom`: only then are `Over.mk T.hom` and `T` the same term, which
the rewriting of the naturality of `β` at the tautological object needs. The tautological object
of `C/A` has image `A → (𝟙 A ≫ a) → X` rather than `A → a → X`; this mismatch is handled in
`CategoryTheory.PresheafOfCategories.elementOf_eq_map_overMapTautHom_of_iso`.

## References

* [Stacks Project, Tag 0041](https://stacks.math.columbia.edu/tag/0041)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits CategoryTheory.OverShriek

namespace CategoryTheory.PresheafOfCategories

universe v u v' u'

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X)
  {Hp Gp : (Over X)ᵒᵖ ⥤ Type v}

/-- A family of sections of `Gp` over the objects `(Over.map a).obj τ`, compatible with
restriction, is determined by its value at the terminal object `A → A` of `C/A`: every object of
`C/A` has a unique morphism to it. -/
theorem sectionFamily_eq_of_eq_at_id
    (s s' : ∀ τ : Over A, Gp.obj (op ((Over.map a).obj τ)))
    (hs : ∀ {τ τ' : Over A} (g : τ ⟶ τ'), Gp.map ((Over.map a).map g).op (s τ') = s τ)
    (hs' : ∀ {τ τ' : Over A} (g : τ ⟶ τ'), Gp.map ((Over.map a).map g).op (s' τ') = s' τ)
    (h : s (Over.mk (𝟙 A)) = s' (Over.mk (𝟙 A))) : s = s' := by
  funext τ
  rw [← hs (Over.mkIdTerminal.from τ), ← hs' (Over.mkIdTerminal.from τ), h]

/-- The value at `f : V ⟶ W` of a morphism out of a representable presheaf is the restriction
along `f` of its value at the identity. -/
private theorem app_yoneda_eq_map {W V : Over X} (β : yoneda.obj W ⟶ Gp) (f : V ⟶ W) :
    β.app (op V) f = Gp.map f.op (β.app (op W) (𝟙 W)) := by
  rw [← NatTrans.naturality_apply β f.op (𝟙 W)]
  exact congrArg (fun z => β.app (op V) z) (Category.comp_id f).symm

/-- The family of restrictions of a section `β` of `Gp` over `A → X` along the tautological
morphisms is compatible with restriction: it is the naturality of `β`. -/
theorem app_overMapTautHom_map (β : yoneda.obj (Over.mk a) ⟶ Gp) {τ τ' : Over A} (g : τ ⟶ τ') :
    Gp.map ((Over.map a).map g).op (β.app (op ((Over.map a).obj τ')) (overMapTautHom a τ')) =
      β.app (op ((Over.map a).obj τ)) (overMapTautHom a τ) := by
  rw [app_yoneda_eq_map β (overMapTautHom a τ'), app_yoneda_eq_map β (overMapTautHom a τ),
    ← Gp.map_comp_apply, ← op_comp, overMap_map_comp_overMapTautHom]

variable
  (θ : (presheafOfCategories (Hp ⋙ typeToCat)).obj ⥤
    (presheafOfCategories (Gp ⋙ typeToCat)).obj)
  (hθ : θ ⋙ discreteProjection Gp = discreteProjection Hp)
  (σ : Over A ⥤ (presheafOfCategories (Gp ⋙ typeToCat)).obj)
  (hσ : σ ⋙ discreteProjection Gp = Over.map a)

include hθ hσ in
/-- The base change of `θ` along a point of `El Gp` with values in `A` is fibred in groupoids
over `C/A`. -/
theorem isFiberedInGroupoids_fst_overMap :
    (TwoFibreProductOver.fst (Over.map a) (discreteProjection Hp) (discreteProjection Gp)
      σ θ).IsFiberedInGroupoids := by
  refine (Functor.isFiberedInGroupoids_comp_overMap_iff a _).1 ?_
  rw [TwoFibreProductOver.fst_comp_eq]
  exact TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (Functor.IsFiberedInGroupoids.over_map a)
    (isFiberedInSetoids_discreteProjection Hp).isFiberedInGroupoids
    (isFiberedInSetoids_discreteProjection Gp).isFiberedInGroupoids hσ hθ

/-- The base change of `θ` along a point of `El Gp` with values in `A` is represented by
`CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf`, as an equivalence of categories
over `C/A`. -/
theorem nonempty_equivalenceOver_twoFibreProductPresheaf :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map a) (discreteProjection Hp) (discreteProjection Gp) σ θ)
      (discreteProjection (twoFibreProductPresheaf σ hσ θ hθ))) :=
  (StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (isFiberedInSetoids_discreteProjection
      (twoFibreProductPresheaf σ hσ θ hθ)).isFiberedInGroupoids
    (isFiberedInGroupoids_fst_overMap a θ hθ σ hσ)
    (toTwoFibreProduct σ hσ θ hθ) (toTwoFibreProduct_comp_fst σ hσ θ hθ)
    (isEquivalence_toTwoFibreProduct σ hσ θ hθ)).map
    StacksRepresentableCFG.EquivalenceOver.symm

/-- The representing presheaf of the base change is the fibre of `Hp ⟶ Gp` over a section:
if a section `β` of `Gp` over `A → X` restricts, along the tautological morphisms, to the family
of sections that the point `σ` names, then the presheaf representing the base change of `θ`
along `σ` is the fibre of the morphism of presheaves underlying `θ` over `β`. -/
theorem fibreOfSection_eq_twoFibreProductPresheaf (β : yoneda.obj (Over.mk a) ⟶ Gp)
    (hβ : ∀ τ : Over A, β.app (op ((Over.map a).obj τ)) (overMapTautHom a τ) =
      sectionOfBasedFunctor σ hσ τ) :
    fibreOfSection a (natTransOfBasedFunctor θ hθ) β = twoFibreProductPresheaf σ hσ θ hθ := by
  have key : ∀ (s : ∀ τ : Over A, Gp.obj (op ((Over.map a).obj τ)))
      (hs : ∀ {τ τ' : Over A} (g : τ ⟶ τ'), Gp.map ((Over.map a).map g).op (s τ') = s τ),
      s = sectionOfBasedFunctor σ hσ →
      fibrePresheaf (Functor.whiskerLeft (Over.map a).op (natTransOfBasedFunctor θ hθ)) s hs =
        twoFibreProductPresheaf σ hσ θ hθ := by
    intro s hs hfam
    subst hfam
    rfl
  exact key (fun τ => β.app (op ((Over.map a).obj τ)) (overMapTautHom a τ))
    (fun g => app_overMapTautHom_map a β g) (funext hβ)

/-- The relocalization of the representing presheaf of the base change is a fibre product:
under the hypothesis of
`CategoryTheory.PresheafOfCategories.fibreOfSection_eq_twoFibreProductPresheaf`, the
relocalization along `a` of the presheaf representing the base change of `θ` along `σ`, together
with its structural morphism to the representable presheaf of `A → X`, is the fibre product of
`Hp` and that representable presheaf over `Gp`. -/
theorem exists_isPullback_relocalize_twoFibreProductPresheaf (β : yoneda.obj (Over.mk a) ⟶ Gp)
    (hβ : ∀ τ : Over A, β.app (op ((Over.map a).obj τ)) (overMapTautHom a τ) =
      sectionOfBasedFunctor σ hσ τ) :
    ∃ c : (relocalizePresheafFunctor a).obj (twoFibreProductPresheaf σ hσ θ hθ) ⟶ Hp,
      IsPullback c (relocalizeToYoneda a (twoFibreProductPresheaf σ hσ θ hθ))
        (natTransOfBasedFunctor θ hθ) β := by
  rw [← fibreOfSection_eq_twoFibreProductPresheaf a θ hθ σ hσ β hβ]
  exact ⟨_, isPullback_relocalizeFibreOfSectionMap a (natTransOfBasedFunctor θ hθ) β⟩

section TwoYoneda

variable {𝒟 : Type u'} [Category.{v'} 𝒟]

/-- The value at the terminal object of `C/A` of the family of sections named by a point.
Let `q : 𝒟 ⥤ C/A` be equivalent over `C/X` to the category of elements of `Gp`, let `s₀` be a
section of `Gp` over `A → X`, and let `D` be an object of `𝒟` lying — after transport through
the equivalence — over `(Over.map a).obj (A → A)`, together with a *vertical* isomorphism of `D`
with the object of `𝒟` that `s₀` names. Then the element of `Gp` that `D` names is the
restriction of `s₀` along the tautological morphism. -/
theorem elementOf_eq_map_overMapTautHom_of_iso (q : 𝒟 ⥤ Over X)
    (e : StacksRepresentableCFG.EquivalenceOver q (discreteProjection Gp))
    (s₀ : Gp.obj (op (Over.mk a))) (D : 𝒟)
    (hD : (e.hom.functor.obj D).base = (Over.map a).obj (Over.mk (𝟙 A)))
    (ξ : D ≅ e.inv.functor.obj (⟨Over.mk a, Discrete.mk s₀⟩ :
      (presheafOfCategories (Gp ⋙ typeToCat)).obj))
    (hξ : q.IsHomLift (𝟙 (Over.mk a)) ξ.hom) :
    elementOf Gp hD = Gp.map (overMapTautHom a (Over.mk (𝟙 A))).op s₀ := by
  obtain ⟨κ, hκ⟩ : ∃ κ : e.hom.functor.obj (e.inv.functor.obj
      (⟨Over.mk a, Discrete.mk s₀⟩ : (presheafOfCategories (Gp ⋙ typeToCat)).obj)) ⟶
        (⟨Over.mk a, Discrete.mk s₀⟩ : (presheafOfCategories (Gp ⋙ typeToCat)).obj),
      κ = e.counitIso.hom.app (⟨Over.mk a, Discrete.mk s₀⟩ :
        (presheafOfCategories (Gp ⋙ typeToCat)).obj) := ⟨_, rfl⟩
  have hζ₁ : (discreteProjection Gp).IsHomLift (𝟙 (Over.mk a)) (e.hom.functor.map ξ.hom) :=
    Functor.isHomLift_map_of_comp_eq e.hom.w (𝟙 (Over.mk a)) ξ.hom
  have hζ₂ : (discreteProjection Gp).IsHomLift (𝟙 (Over.mk a)) κ := by
    rw [hκ]
    exact e.isHomLift_counitIso_hom_app (⟨Over.mk a, Discrete.mk s₀⟩ :
      (presheafOfCategories (Gp ⋙ typeToCat)).obj)
  have hζ : (discreteProjection Gp).IsHomLift (𝟙 (Over.mk a))
      (e.hom.functor.map ξ.hom ≫ κ) := by
    simpa using IsHomLift.comp (discreteProjection Gp) (𝟙 (Over.mk a)) (𝟙 (Over.mk a))
      (e.hom.functor.map ξ.hom) κ
  have hu : (discreteProjection Gp).IsHomLift (overMapTautHom a (Over.mk (𝟙 A)))
      (e.hom.functor.map ξ.hom ≫ κ) := by
    have htaut : overMapTautHom a (Over.mk (𝟙 A)) =
        eqToHom (show (Over.map a).obj (Over.mk (𝟙 A)) = Over.mk a from
          congrArg Over.mk (Category.id_comp a)) :=
      Over.OverMorphism.ext (by simp)
    refine IsHomLift.of_fac' (discreteProjection Gp) _ _ hD rfl ?_
    rw [IsHomLift.fac' (discreteProjection Gp) (𝟙 (Over.mk a))
      (e.hom.functor.map ξ.hom ≫ κ), htaut]
    simp only [Category.id_comp, eqToHom_trans]
    exact (eqToHom_trans _ _).symm
  rw [elementOf_eq_map (P := Gp) (V := (Over.map a).obj (Over.mk (𝟙 A))) (W := Over.mk a)
      (Y := (⟨Over.mk a, Discrete.mk s₀⟩ : (presheafOfCategories (Gp ⋙ typeToCat)).obj))
      hD rfl (overMapTautHom a (Over.mk (𝟙 A))) (e.hom.functor.map ξ.hom ≫ κ) hu,
    elementOf_mk]

/-- The hypothesis of
`CategoryTheory.PresheafOfCategories.fibreOfSection_eq_twoFibreProductPresheaf` holds for the
point that 2-Yoneda produces. Let `q : 𝒟 ⥤ C/X` be a category fibred in groupoids over the
slice at `X`, equivalent over that slice to the category of elements of a presheaf `Gp`, and let
`β : h_{A → X} ⟶ Gp` be a section of `Gp` over `A → X`. Then the 1-morphism `C/A ⥤ 𝒟` over
`Over.map a` of `StacksRepresentableCFG.exists_pointOverMap_of_section`, carried into the
category of elements, names exactly the family of restrictions of `β` along the tautological
morphisms. -/
theorem exists_pointOverMap_sectionOfBasedFunctor_eq (q : 𝒟 ⥤ Over X)
    (hq : q.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver q (discreteProjection Gp))
    (β : yoneda.obj (Over.mk a) ⟶ Gp) :
    ∃ (y : Over A ⥤ 𝒟) (_ : y ⋙ q = Over.map a)
      (hσ : (y ⋙ e.hom.functor) ⋙ discreteProjection Gp = Over.map a),
      ∀ τ : Over A,
        β.app (op ((Over.map a).obj τ)) (overMapTautHom a τ) =
          sectionOfBasedFunctor (y ⋙ e.hom.functor) hσ τ := by
  obtain ⟨y, hy, ξ, hξ⟩ :=
    StacksRepresentableCFG.exists_pointOverMap_of_section q hq e (Over.mk a) β
  have hσ : (y ⋙ e.hom.functor) ⋙ discreteProjection Gp = Over.map a := by
    rw [Functor.assoc, e.hom.w]
    exact hy
  refine ⟨y, hy, hσ, ?_⟩
  refine congrFun (sectionFamily_eq_of_eq_at_id a _ _
    (fun g => app_overMapTautHom_map a β g)
    (fun g => sectionOfBasedFunctor_map (y ⋙ e.hom.functor) hσ g) ?_)
  rw [app_yoneda_eq_map β (overMapTautHom a (Over.mk (𝟙 A)))]
  exact (elementOf_eq_map_overMapTautHom_of_iso a q e
    (β.app (op (Over.mk a)) (𝟙 (Over.mk a))) (y.obj (Over.mk (𝟙 A)))
    (Functor.congr_obj hσ (Over.mk (𝟙 A))) ξ hξ).symm

end TwoYoneda

end CategoryTheory.PresheafOfCategories

end
