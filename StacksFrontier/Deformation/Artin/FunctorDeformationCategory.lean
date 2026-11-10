module

public import StacksFrontier.Deformation.Artin.LocallyNoetherianAlgebraicSpaceCriterion

/-!
# The predeformation categories of a functor satisfying (RS) are deformation categories

Let `F` be a set-valued functor on the locally Noetherian site of `S` (Stacks 0GE4) satisfying
condition (RS) in the form of axiom `[2]` of Section 0GE6. For every field `k` of finite type over
`S` and every `x₀ ∈ F(Spec k)`, the predeformation category `𝓕_{F,k,x₀}` is a deformation
category (Stacks 07WU). In particular it is a predeformation category and its functor of
isomorphism classes satisfies Schlessinger's condition (S2) (Stacks 07WV), so its tangent space
carries the canonical vector-space structure of Stacks 06IH.

## Main definitions

* `AlgebraicGeometry.LocallyNoetherianOver.bigSiteRan`: the right Kan extension of `F` along the
  inclusion of the locally Noetherian site into the big fppf site of `S`, given by compatible
  families of elements of `F` over the locally Noetherian objects mapping to a given object.
* `AlgebraicGeometry.LocallyNoetherianOver.elementsToBigSiteRan`: the comparison of the category
  fibred in sets of `F` with that of its extension.

## Main results

* `CategoryTheory.Functor.isFiberedInGroupoids_elements_leftOp`: the opposite of the category of
  elements of a presheaf of sets is fibred in groupoids over the base.
* `Deformation.Artin.satisfiesRS_elements_of_satisfiesRSFunctor`: condition (RS) in the functor
  form gives condition (RS) of Stacks 07WP for the category of elements, in any universe.
* `LocallyNoetherianOver.isDeformationCategory_predeformationCategory_of_satisfiesRS`: the
  predeformation categories of a functor on the locally Noetherian site satisfying (RS) are
  deformation categories.

## Implementation notes

Stacks 07WU is stated for a category fibred in groupoids over the big fppf site, while the
category fibred in sets of `F` lives over the locally Noetherian objects only and is not fibred
over the big site. The functor `F` is therefore first extended to the big site; any extension
would do, since the test objects of (RS) and of the predeformation categories are spectra of
Artinian local rings, and the right Kan extension is the one available without any hypothesis on
`F`. Its values lie in the universe `max w (u + 1)`, which is why the elements category, and not
the Grothendieck construction `AlgebraicGeometry.Stack.fibredCategory` of a `Type u`-valued
presheaf, is used as the fibred category. The predeformation categories of `F` and of the
extension are then compared by `Deformation.isDeformationCategory_comp_of_surjective`.

## References

* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07WU](https://stacks.math.columbia.edu/tag/07WU)
* [Stacks Project, Tag 07WV](https://stacks.math.columbia.edu/tag/07WV)
* [Stacks Project, Tag 0GE6](https://stacks.math.columbia.edu/tag/0GE6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u₁ v₁ u

/-! ### The category of elements of a presheaf is fibred in groupoids -/

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]

/-- Morphisms of the opposite of the category of elements with the same base map are equal. -/
private theorem elements_op_hom_ext {G : Cᵒᵖ ⥤ Type w} {x y : G.Elementsᵒᵖ} {f g : x ⟶ y}
    (h : f.unop.1 = g.unop.1) : f = g :=
  Quiver.Hom.unop_inj (Functor.Elements.hom_ext h)

/-- **The opposite of the category of elements of a presheaf of sets is fibred in groupoids**
over the base: the restriction of `t ∈ G(U)` along `f : V ⟶ U` is a lift of `f`, and a morphism
of elements is determined by its image in the base. -/
theorem isFiberedInGroupoids_elements_leftOp (G : Cᵒᵖ ⥤ Type w) :
    (Functor.Elements.π G).leftOp.IsFiberedInGroupoids where
  exists_lift {V U} f x hx := by
    obtain ⟨@⟨⟨U'⟩, t⟩⟩ := x
    change U' = U at hx
    subst hx
    exact ⟨op (G.elementsMk (op V) (G.map f.op t)),
      (Functor.Elements.homMk (x := G.elementsMk (op U') t)
        (y := G.elementsMk (op V) (G.map f.op t)) f.op rfl).op,
      IsHomLift.map (p := (Functor.Elements.π G).leftOp)
        (Functor.Elements.homMk (x := G.elementsMk (op U') t)
          (y := G.elementsMk (op V) (G.map f.op t)) f.op rfl).op⟩
  unique_lift {x y z} φ ψ f hf := by
    have hz : G.map f.op y.unop.2 = z.unop.2 := by
      rw [← φ.unop.2, ← ψ.unop.2]
      change G.map f.op (G.map φ.unop.1 x.unop.2) = G.map ψ.unop.1 x.unop.2
      have e : φ.unop.1 ≫ f.op = ψ.unop.1 := Quiver.Hom.unop_inj hf
      rw [← Functor.map_comp_apply, e]
    refine ⟨(Functor.Elements.homMk (x := y.unop) (y := z.unop) f.op hz).op, ⟨rfl, ?_⟩, ?_⟩
    · exact elements_op_hom_ext (Quiver.Hom.unop_inj hf)
    · rintro χ ⟨hχ, -⟩
      exact elements_op_hom_ext (Quiver.Hom.unop_inj hχ)

end CategoryTheory.Functor

/-! ### Condition (RS) for the category of elements -/

namespace Deformation.Artin

open AlgebraicGeometry Functor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}

/-- The object of the fibre over `V` of the category of elements of `G` given by an element
`t` of `G(V)`. -/
abbrev elementsFiberMk {V : BigFppfOver B S hS} (t : G.obj (op V)) :
    (Functor.Elements.π G).leftOp.Fiber V :=
  ⟨op (G.elementsMk (op V) t), rfl⟩

/-- Every object of a fibre of the category of elements of `G` is given by an element. -/
theorem exists_eq_elementsFiberMk {V : BigFppfOver B S hS}
    (z : (Functor.Elements.π G).leftOp.Fiber V) : ∃ t : G.obj (op V), z = elementsFiberMk t := by
  obtain ⟨⟨@⟨⟨V'⟩, t⟩⟩, h⟩ := z
  change V' = V at h
  subst h
  exact ⟨t, rfl⟩

/-- A morphism of the category of elements lying over `f` into the object given by `t` exhibits
its source as the object given by `G(f)(t)`. -/
theorem elementsFiberMk_eq_of_isHomLift {V U : BigFppfOver B S hS} (f : V ⟶ U)
    (t : G.obj (op U)) {x : G.Elementsᵒᵖ} (hx : (Functor.Elements.π G).leftOp.obj x = V)
    (m : x ⟶ op (G.elementsMk (op U) t)) (hm : (Functor.Elements.π G).leftOp.IsHomLift f m) :
    (⟨x, hx⟩ : (Functor.Elements.π G).leftOp.Fiber V) = elementsFiberMk (G.map f.op t) := by
  obtain ⟨@⟨⟨V'⟩, s⟩⟩ := x
  change V' = V at hx
  subst hx
  have hb : m.unop.1 = f.op := by
    have h := IsHomLift.fac' (Functor.Elements.π G).leftOp f m
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
    exact Quiver.Hom.unop_inj h
  obtain rfl : G.map f.op t = s := by
    rw [← hb]
    exact m.unop.2
  rfl

/-- A morphism of a fibre of the category of elements of `G` lies over the identity. -/
theorem val_unop_fiberInclusion_map {V : BigFppfOver B S hS}
    {z z' : (Functor.Elements.π G).leftOp.Fiber V} (φ : z ⟶ z') :
    (Fiber.fiberInclusion.map φ).unop.1 =
      (eqToHom z.2 ≫ eqToHom z'.2.symm).op := by
  have h := IsHomLift.fac' (Functor.Elements.π G).leftOp (𝟙 V) (Fiber.fiberInclusion.map φ)
  rw [Category.id_comp] at h
  exact Quiver.Hom.unop_inj h

/-- Two objects of a fibre of the category of elements given by elements are related by a
morphism exactly when the elements are equal. -/
theorem eq_of_elementsFiber_hom {V : BigFppfOver B S hS} {t t' : G.obj (op V)}
    (φ : elementsFiberMk t ⟶ elementsFiberMk t') : t = t' := by
  have hm : G.map (Fiber.fiberInclusion.map φ).unop.1 t' = t := (Fiber.fiberInclusion.map φ).unop.2
  have h₁ : (Fiber.fiberInclusion.map φ).unop.1 = (𝟙 (op V) : op V ⟶ op V) := by
    rw [val_unop_fiberInclusion_map φ]
    simp only [eqToHom_refl, Category.comp_id, op_id]
    rfl
  rw [h₁] at hm
  have key : ∀ s : G.obj (op V), G.map (𝟙 (op V)) s = s := fun s => by simp
  exact hm.symm.trans (key t')

/-- Between two objects of a fibre of the category of elements there is at most one morphism. -/
instance subsingleton_elementsFiber_hom {V : BigFppfOver B S hS}
    (z z' : (Functor.Elements.π G).leftOp.Fiber V) : Subsingleton (z ⟶ z') :=
  ⟨fun φ ψ => Fiber.hom_ext (Quiver.Hom.unop_inj (Functor.Elements.hom_ext
    ((val_unop_fiberInclusion_map φ).trans (val_unop_fiberInclusion_map ψ).symm)))⟩

/-- A choice of pullbacks of the category of elements of `G` pulls the element `t` back to
`G(f)(t)`. -/
theorem elements_pullbackFunctor_obj_eq
    (c : (Functor.Elements.π G).leftOp.ChoiceOfPullbacks)
    {V U : BigFppfOver B S hS} (f : V ⟶ U) (t : G.obj (op U)) :
    (c.pullbackFunctor f).obj (elementsFiberMk t) = elementsFiberMk (G.map f.op t) :=
  elementsFiberMk_eq_of_isHomLift f t ((c.pullbackFunctor f).obj (elementsFiberMk t)).2
    (c.map f (elementsFiberMk t)) (c.isStronglyCartesian f (elementsFiberMk t)).toIsHomLift

/-- A morphism between pullbacks of elements in a fibre of the category of elements of `G`
identifies the restricted elements. -/
theorem map_eq_of_pullbackFunctor_hom
    (c : (Functor.Elements.π G).leftOp.ChoiceOfPullbacks)
    {V U U' : BigFppfOver B S hS} (f : V ⟶ U) (f' : V ⟶ U') {t : G.obj (op U)}
    {t' : G.obj (op U')}
    (φ : (c.pullbackFunctor f).obj (elementsFiberMk t) ⟶
      (c.pullbackFunctor f').obj (elementsFiberMk t')) :
    G.map f.op t = G.map f'.op t' := by
  rw [elements_pullbackFunctor_obj_eq, elements_pullbackFunctor_obj_eq] at φ
  exact eq_of_elementsFiber_hom φ

/-- **Condition (RS) in the functor form gives condition (RS) of Stacks 07WP for the category of
elements.** The fibres of the category of elements are discrete, so the comparison functor of
Stacks 07WP is, up to the identification of the objects of a fibre with elements of `G`, the map
`G(Y') ⟶ G(Y) ×_{G(X)} G(X')`. -/
theorem satisfiesRS_elements_of_satisfiesRSFunctor (h : SatisfiesRSFunctor B S hS G) :
    SatisfiesRS B S hS (Functor.Elements.π G).leftOp
      (isFiberedInGroupoids_elements_leftOp G) := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo
  let : (Functor.Elements.π G).leftOp.IsFibered :=
    (isFiberedInGroupoids_elements_leftOp G).isFibered
  let p := (Functor.Elements.π G).leftOp
  let c := p.chosenPullbacks
  let K := fiberSquareComparison p c j i j' i' w.symm
  have hRS := h i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo
  have hcomp : ∀ t : G.obj (op Y'), G.map j.op (G.map j'.op t) = G.map i.op (G.map i'.op t) := by
    intro t
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      w]
  have : K.Faithful := ⟨fun {_ _} _ _ _ => Subsingleton.elim _ _⟩
  have : K.Full := by
    refine ⟨fun {z₁ z₂} φ => ?_⟩
    obtain ⟨t₁, rfl⟩ := exists_eq_elementsFiberMk z₁
    obtain ⟨t₂, rfl⟩ := exists_eq_elementsFiberMk z₂
    have h₁ : G.map j'.op t₁ = G.map j'.op t₂ := map_eq_of_pullbackFunctor_hom c j' j' φ.fst
    have h₂ : G.map i'.op t₁ = G.map i'.op t₂ := map_eq_of_pullbackFunctor_hom c i' i' φ.snd
    obtain ⟨t, -, ht⟩ := hRS (G.map j'.op t₁) (G.map i'.op t₁) (hcomp t₁)
    have e : t₁ = t₂ := (ht t₁ ⟨rfl, rfl⟩).trans (ht t₂ ⟨h₁.symm, h₂.symm⟩).symm
    subst e
    refine ⟨𝟙 _, ?_⟩
    apply CategoricalPullback.hom_ext <;> exact Subsingleton.elim _ _
  have : K.EssSurj := by
    refine ⟨fun P => ?_⟩
    obtain ⟨x, y, e⟩ := P
    obtain ⟨a, rfl⟩ := exists_eq_elementsFiberMk x
    obtain ⟨b, rfl⟩ := exists_eq_elementsFiberMk y
    have hab : G.map j.op a = G.map i.op b := map_eq_of_pullbackFunctor_hom c j i e.hom
    obtain ⟨t, ⟨ht₁, ht₂⟩, -⟩ := hRS a b hab
    refine ⟨elementsFiberMk t, ⟨CategoricalPullback.mkIso
      (eqToIso (by
        change (c.pullbackFunctor j').obj _ = _
        rw [elements_pullbackFunctor_obj_eq, ht₁]))
      (eqToIso (by
        change (c.pullbackFunctor i').obj _ = _
        rw [elements_pullbackFunctor_obj_eq, ht₂]))
      (Subsingleton.elim _ _)⟩⟩
  exact { }

end Deformation.Artin

/-! ### The right Kan extension to the big fppf site -/

namespace AlgebraicGeometry.LocallyNoetherianOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w)

/-- The compatible families of elements of `F` over the locally Noetherian objects mapping to
`V`: the value at `V` of the right Kan extension of `F` to the big fppf site. -/
abbrev RanSections (V : BigFppfOver B S hS) : Type (max w (u + 1)) :=
  { s : ∀ (U : LocallyNoetherianOver B S hS), (U.obj ⟶ V) → F.obj (op U) //
    ∀ (U U' : LocallyNoetherianOver B S hS) (g : U' ⟶ U) (f : U.obj ⟶ V),
      F.map g.op (s U f) = s U' (g.hom ≫ f) }

/-- **The right Kan extension of `F` to the big fppf site of `S`.** Its value at `V` is the set
of compatible families of elements of `F` over the locally Noetherian objects mapping to `V`. -/
def bigSiteRan : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1)) where
  obj V := RanSections F V.unop
  map {V V'} h := ↾fun s => ⟨fun U f => s.1 U (f ≫ h.unop), fun U U' g f => by
    rw [s.2]
    exact congrArg (s.1 U') (Category.assoc _ _ _).symm⟩
  map_id V := by
    ext s U f
    change s.1 U (f ≫ 𝟙 _) = s.1 U f
    rw [Category.comp_id]
  map_comp h h' := by
    ext s U f
    change s.1 U (f ≫ (h ≫ h').unop) = s.1 U ((f ≫ h'.unop) ≫ h.unop)
    rw [unop_comp, Category.assoc]

variable {F}

/-- The family attached to an element of `F` over a locally Noetherian object. -/
def ranSectionOf {U₀ : LocallyNoetherianOver B S hS} (t : F.obj (op U₀)) :
    (bigSiteRan F).obj (op U₀.obj) :=
  ⟨fun U f => F.map (ObjectProperty.homMk f : U ⟶ U₀).op t, fun U U' g f => by
    rw [← Functor.map_comp_apply, ← op_comp]
    rfl⟩

/-- The family attached to `t ∈ F(U₀)` takes the value `t` at the identity of `U₀`. -/
theorem ranSectionOf_val_id {U₀ : LocallyNoetherianOver B S hS} (t : F.obj (op U₀)) :
    (ranSectionOf t).1 U₀ (𝟙 _) = t := by
  change F.map (𝟙 U₀).op t = t
  simp

/-- A compatible family over a locally Noetherian object is the family of its value at the
identity. -/
theorem ranSectionOf_val_id_eq {U₀ : LocallyNoetherianOver B S hS}
    (s : (bigSiteRan F).obj (op U₀.obj)) : ranSectionOf (s.1 U₀ (𝟙 _)) = s := by
  apply Subtype.ext
  funext U f
  change F.map (ObjectProperty.homMk f : U ⟶ U₀).op (s.1 U₀ (𝟙 _)) = s.1 U f
  rw [s.2]
  change s.1 U (f ≫ 𝟙 _) = s.1 U f
  rw [Category.comp_id]

/-- The family attached to an element is compatible with restriction along a morphism of
locally Noetherian objects: restricting the family of `t` along `g` gives the family of
`F(g)(t)`. -/
theorem ranSectionOf_map {U₀ U₁ : LocallyNoetherianOver B S hS} (g : U₁ ⟶ U₀)
    (t : F.obj (op U₀)) :
    (bigSiteRan F).map g.hom.op (ranSectionOf t) = ranSectionOf (F.map g.op t) := by
  apply Subtype.ext
  funext U f
  change F.map (ObjectProperty.homMk (f ≫ g.hom) : U ⟶ U₀).op t =
    F.map (ObjectProperty.homMk f : U ⟶ U₁).op (F.map g.op t)
  rw [← Functor.map_comp_apply, ← op_comp]
  rfl

/-- Distinct elements of `F` over a locally Noetherian object give distinct families. -/
theorem ranSectionOf_injective {U₀ : LocallyNoetherianOver B S hS} :
    Function.Injective (ranSectionOf (F := F) (U₀ := U₀)) := fun t t' h => by
  rw [← ranSectionOf_val_id t, ← ranSectionOf_val_id t', h]

/-- Restricting the family of `t` along `g` gives the family of `t'` iff `F(g)(t) = t'`. -/
private theorem ranSectionOf_map_eq_iff {U₀ U₁ : LocallyNoetherianOver B S hS} (g : U₁ ⟶ U₀)
    {t : F.obj (op U₀)} {t' : F.obj (op U₁)} :
    (bigSiteRan F).map g.hom.op (ranSectionOf t) = ranSectionOf t' ↔ F.map g.op t = t' := by
  rw [ranSectionOf_map, ranSectionOf_injective.eq_iff]

/-- Every compatible family over a locally Noetherian object is the family of an element. -/
private theorem exists_ranSectionOf_eq {U₀ : LocallyNoetherianOver B S hS}
    (s : (bigSiteRan F).obj (op U₀.obj)) : ∃ t : F.obj (op U₀), ranSectionOf t = s :=
  ⟨_, ranSectionOf_val_id_eq s⟩

/-- **Condition (RS) passes from `F` to its right Kan extension.** The pushout squares of
Artinian local schemes that condition (RS) quantifies over lie in the locally Noetherian site,
where the extension is `F`. -/
theorem satisfiesRSFunctor_bigSiteRan (hF : SatisfiesRS B S hS F) :
    Deformation.Artin.SatisfiesRSFunctor B S hS (bigSiteRan F) := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo a b hab
  let X₀ : LocallyNoetherianOver B S hS := ⟨X, isLocallyNoetherian_of_isArtinianLocal hX⟩
  let X'₀ : LocallyNoetherianOver B S hS := ⟨X', isLocallyNoetherian_of_isArtinianLocal hX'⟩
  let Y₀ : LocallyNoetherianOver B S hS := ⟨Y, isLocallyNoetherian_of_isArtinianLocal hY⟩
  let Y'₀ : LocallyNoetherianOver B S hS := ⟨Y', isLocallyNoetherian_of_isArtinianLocal hY'⟩
  let i₀ : X₀ ⟶ X'₀ := ObjectProperty.homMk i
  let j₀ : X₀ ⟶ Y₀ := ObjectProperty.homMk j
  let i'₀ : X'₀ ⟶ Y'₀ := ObjectProperty.homMk i'
  let j'₀ : Y₀ ⟶ Y'₀ := ObjectProperty.homMk j'
  obtain ⟨a₀, rfl⟩ := exists_ranSectionOf_eq (U₀ := Y₀) a
  obtain ⟨b₀, rfl⟩ := exists_ranSectionOf_eq (U₀ := X'₀) b
  have hab' : F.map j₀.op a₀ = F.map i₀.op b₀ := (ranSectionOf_map_eq_iff j₀).1
    (hab.trans (ranSectionOf_map i₀ b₀))
  obtain ⟨t, ⟨ht₁, ht₂⟩, hu⟩ := hF i₀ j₀ i'₀ j'₀ (ObjectProperty.hom_ext _ w) hX hX' hY hY'
    hX₁ hX'₁ hY₁ hY'₁ hci hpo _ _ hab'
  refine ⟨ranSectionOf t, ⟨(ranSectionOf_map_eq_iff j'₀).2 ht₁,
    (ranSectionOf_map_eq_iff i'₀).2 ht₂⟩, fun t' ht' => ?_⟩
  obtain ⟨t'₀, rfl⟩ := exists_ranSectionOf_eq (U₀ := Y'₀) t'
  exact congrArg ranSectionOf (hu t'₀ ⟨(ranSectionOf_map_eq_iff j'₀).1 ht'.1,
    (ranSectionOf_map_eq_iff i'₀).1 ht'.2⟩)

variable (F)

/-- **The comparison of the category fibred in sets of `F` with that of its right Kan
extension.** -/
def elementsToBigSiteRan : F.Elementsᵒᵖ ⥤ (bigSiteRan F).Elementsᵒᵖ :=
  (show F.Elements ⥤ (bigSiteRan F).Elements from
    { obj := fun x => (bigSiteRan F).elementsMk (op x.1.unop.obj) (ranSectionOf x.2)
      map := fun {x _} f => ⟨f.1.unop.hom.op,
        (ranSectionOf_map f.1.unop x.2).trans (congrArg ranSectionOf f.2)⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }).op

/-- The comparison lies over the identity of `Sch/S`. -/
theorem elementsToBigSiteRan_comp_bigElementsToOver :
    elementsToBigSiteRan F ⋙ bigElementsToOver (bigSiteRan F) = elementsToOver B S hS F :=
  rfl

/-- The comparison `elementsToBigSiteRan F` is faithful. -/
instance : (elementsToBigSiteRan F).Faithful :=
  ⟨fun {x y} f g h => by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact congrArg (fun k => k.unop.1.unop) h⟩

/-- The comparison `elementsToBigSiteRan F` is full: a morphism of the extension between objects
of the image comes from a morphism of the category of elements of `F`. -/
instance : (elementsToBigSiteRan F).Full :=
  ⟨fun {x y} g => by
    obtain ⟨@⟨⟨X₀⟩, x₀⟩⟩ := x
    obtain ⟨@⟨⟨Y₀⟩, y₀⟩⟩ := y
    let g₀ : X₀ ⟶ Y₀ := ObjectProperty.homMk g.unop.1.unop
    exact ⟨Quiver.Hom.op ⟨g₀.op,
      ranSectionOf_injective ((ranSectionOf_map g₀ y₀).symm.trans g.unop.2)⟩, rfl⟩⟩

/-- **The comparison reaches every object over a locally Noetherian scheme.** -/
theorem elementsToBigSiteRan_surjective (y' : (bigSiteRan F).Elementsᵒᵖ)
    (hy' : IsLocallyNoetherian ((bigElementsToOver (bigSiteRan F)).obj y').left) :
    ∃ y : F.Elementsᵒᵖ, (elementsToBigSiteRan F).obj y = y' := by
  obtain ⟨@⟨⟨T⟩, s⟩⟩ := y'
  refine ⟨op (F.elementsMk (op ⟨T, hy'⟩) (s.1 ⟨T, hy'⟩ (𝟙 _))), ?_⟩
  change op ((bigSiteRan F).elementsMk (op T) (ranSectionOf (s.1 ⟨T, hy'⟩ (𝟙 _)))) =
    op ((bigSiteRan F).elementsMk (op T) s)
  rw [ranSectionOf_val_id_eq (U₀ := ⟨T, hy'⟩) s]

/-! ### Predeformation categories -/

open Deformation Deformation.Artin

variable {F}

/-- **The predeformation categories of a functor on the locally Noetherian site satisfying (RS)
are deformation categories** (Stacks 07WU, for `F` in the form of axiom `[2]` of Section 0GE6):
for a field `k` of finite type over `S`, a factorization of `Spec k ⟶ S` through `Spec Λ`, and
`x₀ ∈ F(Spec k)`, the category `𝓕_{F,k,x₀}` is a deformation category over `𝒞_Λ`. -/
theorem isDeformationCategory_predeformationCategory_of_satisfiesRS (hF : SatisfiesRS B S hS F)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : F.Elementsᵒᵖ)
    (hx₀ : (elementsToOver B S hS F).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI := (predeformationCategory iΛ (elementsToOver B S hS F) x₀ hx₀).category
    IsDeformationCategory
      (predeformationCategory iΛ (elementsToOver B S hS F) x₀ hx₀).projection := by
  have hD' := Deformation.Artin.isDeformationCategory_predeformationCategory B S hS
    (Functor.Elements.π (bigSiteRan F)).leftOp
    (Functor.isFiberedInGroupoids_elements_leftOp (bigSiteRan F))
    (satisfiesRS_elements_of_satisfiesRSFunctor (satisfiesRSFunctor_bigSiteRan hF))
    iΛ ((elementsToBigSiteRan F).obj x₀) hx₀ hfinite hqc
  let := (predeformationCategory iΛ
    (elementsToBigSiteRan F ⋙ bigElementsToOver (bigSiteRan F)) x₀ hx₀).category
  let := (predeformationCategory iΛ (bigElementsToOver (bigSiteRan F))
    ((elementsToBigSiteRan F).obj x₀) hx₀).category
  have := predeformationComp_full iΛ (bigElementsToOver (bigSiteRan F)) (elementsToBigSiteRan F)
    x₀ hx₀
  have := predeformationComp_faithful iΛ (bigElementsToOver (bigSiteRan F))
    (elementsToBigSiteRan F) x₀ hx₀
  exact isDeformationCategory_comp_of_surjective
    (predeformationComp iΛ (bigElementsToOver (bigSiteRan F)) (elementsToBigSiteRan F) x₀ hx₀)
    (predeformationComp_surjective iΛ (bigElementsToOver (bigSiteRan F)) (elementsToBigSiteRan F)
      x₀ hx₀ (elementsToBigSiteRan_surjective F)) hD'

/-- The finite-type hypotheses of `isDeformationCategory_predeformationCategory_of_satisfiesRS` in
the convention of Artin's axiom `[3]`: `Spec Λ ⊆ S` an open subscheme and `Λ → k` finite. -/
theorem locallyOfFiniteType_quasiCompact_of_isOpenImmersion
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : IsOpenImmersion iΛ) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) := by
  have : (algebraMap Λ k).Finite := RingHom.finite_algebraMap.mpr inferInstance
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Λ k))) :=
    (IsFinite.SpecMap_iff _).mpr this
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.LocallyNoetherianOver

end
