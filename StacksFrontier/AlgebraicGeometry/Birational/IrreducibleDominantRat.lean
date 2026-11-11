module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Composition
public import StacksCore.Tactic.StacksAttribute

/-!
# The category of irreducible schemes and dominant rational maps

Composition of dominant rational maps between irreducible schemes is associative and unital, so
irreducible schemes and dominant rational maps form a category, and similarly over a base scheme
`S` with dominant `S`-rational maps. Two irreducible schemes are *birational* (resp.
*`S`-birational*) if they are isomorphic in this category.

## Main definitions

* `AlgebraicGeometry.IrreducibleDominantRat`: the category of irreducible schemes and dominant
  rational maps.
* `AlgebraicGeometry.IrreducibleDominantRatOver S`: the category of irreducible schemes over `S`
  and dominant `S`-rational maps.
* `AlgebraicGeometry.IrreducibleDominantRat.Birational`: two irreducible schemes are birational
  if they are isomorphic in `IrreducibleDominantRat`.
* `AlgebraicGeometry.IrreducibleDominantRatOver.BirationalOver`: two irreducible schemes over `S`
  are `S`-birational if they are isomorphic in `IrreducibleDominantRatOver S`.

## Main results

* `AlgebraicGeometry.IrreducibleDominantRat.birational_iff_birational`: birationality in the
  category of dominant rational maps is equivalent to the existence of a partial isomorphism,
  that is to `AlgebraicGeometry.Scheme.Birational`.
* `AlgebraicGeometry.IrreducibleDominantRatOver.birationalOver_iff_birationalOver`: the same
  over a base scheme, with `AlgebraicGeometry.Scheme.BirationalOver`.

## Implementation notes

The key step is `AlgebraicGeometry.Scheme.PartialMap.exists_partialIso_of_comp_equiv_id`: if
`f : U → Y` and `g : V → X` represent mutually inverse dominant rational maps, then `g ∘ f` is the
inclusion on a nonempty open `W ⊆ U` and `f ∘ g` is the inclusion on a nonempty open `V' ⊆ V`.
On `W₀ = W ∩ f⁻¹(V')` and `T = V' ∩ g⁻¹(W₀)` the maps `f` and `g` restrict to mutually inverse
morphisms `W₀ ⟶ T` and `T ⟶ W₀`, and nonempty opens of irreducible schemes are dense.

## References

* [Stacks Project, Tag 0A20](https://stacks.math.columbia.edu/tag/0A20)
* [Stacks Project, Tag 0BAA](https://stacks.math.columbia.edu/tag/0BAA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}}

namespace PartialMap

/-- If the composite `f.comp g` of partial maps agrees with the identity as a rational map, then
on some dense open `W` of the domain of `f`, the map `f` factors through the domain of `g` and
`g ∘ f` is the inclusion of `W`. -/
lemma exists_factor_of_comp_equiv_id [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap X)
    (h : (f.comp g).equiv (PartialMap.id X)) :
    ∃ (W : X.Opens) (_ : Dense (W : Set X)) (hW : W ≤ f.domain)
      (k : W.toScheme ⟶ g.domain.toScheme),
      k ≫ g.domain.ι = X.homOfLE hW ≫ f.hom ∧ k ≫ g.hom = W.ι := by
  obtain ⟨W, hW, hWl, hWr, e⟩ := h
  have hle : f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain ≤ f.domain := f.domain.ι_image_le _
  have hWl' : W ≤ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain := hWl
  refine ⟨W, hW, hWl'.trans hle,
    X.homOfLE hWl' ≫ (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain, ?_, ?_⟩
  · have h₁ : (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ (f.hom ⁻¹ᵁ g.domain).ι =
        X.homOfLE hle := by
      rw [← cancel_mono f.domain.ι, Category.assoc, Hom.isoImage_inv_ι, Scheme.homOfLE_ι]
    simp only [Category.assoc, morphismRestrict_ι]
    rw [reassoc_of% h₁, ← Category.assoc, Scheme.homOfLE_homOfLE]
  · simp only [restrict_hom, comp_hom, Hom.toPartialMap_hom, Category.comp_id] at e
    exact (Category.assoc _ _ _).trans (e.trans (X.homOfLE_ι hWr))

/-- If dominant partial maps `f : X.PartialMap Y` and `g : Y.PartialMap X` between irreducible
schemes are mutually inverse as rational maps, then a restriction of `f` is an isomorphism
between dense open subschemes. -/
lemma exists_partialIso_of_comp_equiv_id [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap X) [IsDominant g.hom]
    (hfg : (f.comp g).equiv (PartialMap.id X)) (hgf : (g.comp f).equiv (PartialMap.id Y)) :
    ∃ (e : X.PartialIso Y) (h : e.source ≤ f.domain),
      e.iso.hom ≫ e.target.ι = X.homOfLE h ≫ f.hom := by
  obtain ⟨W, hWd, hWU, k, hk₁, hk₂⟩ := f.exists_factor_of_comp_equiv_id g hfg
  obtain ⟨V', hV'd, hV'V, k', hk₁', hk₂'⟩ := g.exists_factor_of_comp_equiv_id f hgf
  obtain ⟨W₀, hW₀def⟩ : ∃ W₀ : X.Opens, W₀ = W ⊓ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ V' := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Y.Opens, T = V' ⊓ g.domain.ι ''ᵁ g.hom ⁻¹ᵁ W₀ := ⟨_, rfl⟩
  have hW₀W : W₀ ≤ W := hW₀def ▸ inf_le_left
  have hW₀U : W₀ ≤ f.domain := hW₀W.trans hWU
  have hTV' : T ≤ V' := hTdef ▸ inf_le_left
  have hTV : T ≤ g.domain := hTV'.trans hV'V
  have hW₀ : (W₀ : Set X).Nonempty := by
    rw [hW₀def]
    refine nonempty_preirreducible_inter W.2 (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ V').2 hWd.nonempty ?_
    simpa [← Set.nonempty_preimage_iff] using
      f.hom.denseRange.inter_open_nonempty _ V'.2 hV'd.nonempty
  have hT : (T : Set Y).Nonempty := by
    rw [hTdef]
    refine nonempty_preirreducible_inter V'.2 (g.domain.ι ''ᵁ g.hom ⁻¹ᵁ W₀).2 hV'd.nonempty ?_
    simpa [← Set.nonempty_preimage_iff] using
      g.hom.denseRange.inter_open_nonempty _ W₀.2 hW₀
  have hmem₁ (x : W₀.toScheme) : f.hom (X.homOfLE hW₀U x) ∈ T := by
    have hx : x.1 ∈ W ⊓ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ V' := hW₀def ▸ x.2
    obtain ⟨-, u', hu', hu'x⟩ := hx
    have e₁ : u' = X.homOfLE hW₀U x := Subtype.ext (hu'x.trans (Scheme.homOfLE_apply _ _).symm)
    have e₂ : X.homOfLE hW₀U x = X.homOfLE hWU (X.homOfLE hW₀W x) := by
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_homOfLE]
    have h₁ := congr($hk₁ (X.homOfLE hW₀W x))
    have h₂ := congr($hk₂ (X.homOfLE hW₀W x))
    simp only [Scheme.Hom.comp_apply] at h₁ h₂
    rw [hTdef]
    refine ⟨e₁ ▸ hu', k (X.homOfLE hW₀W x), ?_, ?_⟩
    · change g.hom (k (X.homOfLE hW₀W x)) ∈ W₀
      have h₃ := congr($(X.homOfLE_ι hW₀W) x)
      simp only [Scheme.Hom.comp_apply] at h₃
      rw [h₂, h₃]
      exact x.2
    · exact h₁.trans (congrArg f.hom e₂.symm)
  have hmem₂ (y : T.toScheme) : g.hom (Y.homOfLE hTV y) ∈ W₀ := by
    have hy : y.1 ∈ V' ⊓ g.domain.ι ''ᵁ g.hom ⁻¹ᵁ W₀ := hTdef ▸ y.2
    obtain ⟨-, v', hv', hv'y⟩ := hy
    have e₁ : v' = Y.homOfLE hTV y := Subtype.ext (hv'y.trans (Scheme.homOfLE_apply _ _).symm)
    exact e₁ ▸ hv'
  let α : W₀.toScheme ⟶ T.toScheme := IsOpenImmersion.lift T.ι (X.homOfLE hW₀U ≫ f.hom) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact hmem₁ x)
  let β : T.toScheme ⟶ W₀.toScheme := IsOpenImmersion.lift W₀.ι (Y.homOfLE hTV ≫ g.hom) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact hmem₂ y)
  have hα : α ≫ T.ι = X.homOfLE hW₀U ≫ f.hom := IsOpenImmersion.lift_fac _ _ _
  have hβ : β ≫ W₀.ι = Y.homOfLE hTV ≫ g.hom := IsOpenImmersion.lift_fac _ _ _
  have hαV : α ≫ Y.homOfLE hTV = X.homOfLE hW₀W ≫ k := by
    rw [← cancel_mono g.domain.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, hα, hk₁]
    rw [← Category.assoc, Scheme.homOfLE_homOfLE]
  have hβU : β ≫ X.homOfLE hW₀U = Y.homOfLE hTV' ≫ k' := by
    rw [← cancel_mono f.domain.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, hβ, hk₁']
    rw [← Category.assoc, Scheme.homOfLE_homOfLE]
  have hαβ : α ≫ β = 𝟙 _ := by
    rw [← cancel_mono W₀.ι, Category.assoc, hβ, ← Category.assoc, hαV, Category.assoc, hk₂,
      Scheme.homOfLE_ι, Category.id_comp]
  have hβα : β ≫ α = 𝟙 _ := by
    rw [← cancel_mono T.ι, Category.assoc, hα, ← Category.assoc, hβU, Category.assoc, hk₂',
      Scheme.homOfLE_ι, Category.id_comp]
  exact ⟨⟨W₀, W₀.2.dense hW₀, T, T.2.dense hT, ⟨α, β, hαβ, hβα⟩⟩, hW₀U, hα⟩

end PartialMap

namespace PartialIso

instance (e : X.PartialIso Y) : IsDominant e.toPartialMap.hom := by
  have : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  exact ⟨e.target.ι.denseRange.comp e.iso.hom.denseRange e.target.ι.continuous⟩

/-- A partial isomorphism followed by its inverse is the identity as a rational map. -/
lemma toPartialMap_comp_symm_equiv [IrreducibleSpace X] [Nonempty Y] (e : X.PartialIso Y) :
    (e.toPartialMap.comp e.symm.toPartialMap).equiv (PartialMap.id X) := by
  have hdom : e.source.ι ''ᵁ (e.iso.hom ≫ e.target.ι) ⁻¹ᵁ e.target = e.source := by
    rw [Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Hom.preimage_top,
      Scheme.Opens.ι_image_top]
  refine ⟨e.source, e.dense_source, hdom.ge, le_top, ?_⟩
  have h₁ : (e.iso.hom ≫ e.target.ι) ∣_ e.target =
      ((e.iso.hom ≫ e.target.ι) ⁻¹ᵁ e.target).ι ≫ e.iso.hom := by
    rw [← cancel_mono e.target.ι, morphismRestrict_ι, Category.assoc]
  change X.homOfLE hdom.ge ≫
      (e.source.ι.isoImage ((e.iso.hom ≫ e.target.ι) ⁻¹ᵁ e.target)).inv ≫
        (e.iso.hom ≫ e.target.ι) ∣_ e.target ≫ e.iso.inv ≫ e.source.ι =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ 𝟙 X
  rw [h₁]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Hom.isoImage_inv_ι, Scheme.homOfLE_ι,
    Category.comp_id, Scheme.topIso_hom]

end PartialIso

end Scheme

open Scheme

/-- The category of irreducible schemes whose morphisms are dominant rational maps. -/
structure IrreducibleDominantRat : Type (u + 1) where
  /-- The irreducible scheme `X` as an object of `IrreducibleDominantRat`. -/
  of ::
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  [irreducibleSpace : IrreducibleSpace toScheme]

attribute [instance] IrreducibleDominantRat.irreducibleSpace

namespace IrreducibleDominantRat

/-- A morphism in `IrreducibleDominantRat` is a dominant rational map. -/
@[ext]
structure Hom (X Y : IrreducibleDominantRat.{u}) where
  /-- The underlying rational map. -/
  toRationalMap : X.toScheme ⤏ Y.toScheme
  [isDominant : toRationalMap.IsDominant]

attribute [instance] Hom.isDominant

noncomputable instance : Category IrreducibleDominantRat.{u} where
  Hom := Hom
  id X := ⟨RationalMap.id X.toScheme⟩
  comp f g := ⟨f.toRationalMap.comp g.toRationalMap⟩
  id_comp _ := Hom.ext (RationalMap.id_comp _)
  comp_id _ := Hom.ext (RationalMap.comp_id _)
  assoc _ _ _ := Hom.ext (RationalMap.comp_assoc _ _ _)

/-- **Stacks 0A20 (1).** Irreducible schemes `X` and `Y` are *birational* if they are isomorphic
in the category of irreducible schemes and dominant rational maps. -/
@[stacks 0A20 "(1): isomorphic in the category `IrreducibleDominantRat` of irreducible schemes
and dominant rational maps; `birational_iff_birational` identifies it with Mathlib's
`Scheme.Birational` (a partial isomorphism between dense opens)."]
def Birational (X Y : Scheme.{u}) [IrreducibleSpace X] [IrreducibleSpace Y] : Prop :=
  Nonempty (of X ≅ of Y)

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- Birationality unfolded: mutually inverse dominant rational maps. -/
theorem birational_iff_exists_comp_eq_id :
    Birational X Y ↔ ∃ (f : X ⤏ Y) (_ : f.IsDominant) (g : Y ⤏ X) (_ : g.IsDominant),
      f.comp g = RationalMap.id X ∧ g.comp f = RationalMap.id Y := by
  constructor
  · rintro ⟨e⟩
    exact ⟨Hom.toRationalMap e.hom, inferInstance, Hom.toRationalMap e.inv, inferInstance,
      congr_arg Hom.toRationalMap e.hom_inv_id, congr_arg Hom.toRationalMap e.inv_hom_id⟩
  · rintro ⟨f, hf, g, hg, h₁, h₂⟩
    exact ⟨⟨(⟨f⟩ : Hom (of X) (of Y)), (⟨g⟩ : Hom (of Y) (of X)), Hom.ext h₁, Hom.ext h₂⟩⟩

/-- Birationality in the category of irreducible schemes and dominant rational maps
(Stacks 0A20 (1)) is equivalent to the existence of a partial isomorphism, Mathlib's
`Scheme.Birational`. -/
@[stacks 0A20 "(1): the definition by isomorphism in the category of dominant rational maps
is equivalent to Mathlib's `Scheme.Birational`."]
theorem birational_iff_birational : Birational X Y ↔ Scheme.Birational X Y := by
  rw [birational_iff_exists_comp_eq_id]
  constructor
  · rintro ⟨f, hf, g, hg, h₁, h₂⟩
    obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective f
    obtain ⟨g, rfl⟩ := PartialMap.toRationalMap_surjective g
    have : IsDominant f.hom := f.isDominant_toRationalMap_iff.1 hf
    have : IsDominant g.hom := g.isDominant_toRationalMap_iff.1 hg
    rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff] at h₁ h₂
    obtain ⟨e, -, -⟩ := f.exists_partialIso_of_comp_equiv_id g h₁ h₂
    exact ⟨e⟩
  · rintro ⟨e⟩
    refine ⟨e.toRationalMap, inferInstance, e.symm.toRationalMap, inferInstance, ?_, ?_⟩
    · rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff]
      exact e.toPartialMap_comp_symm_equiv
    · rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff]
      exact e.symm.toPartialMap_comp_symm_equiv

end IrreducibleDominantRat

/-- The category of irreducible schemes over `S` whose morphisms are dominant `S`-rational
maps. -/
structure IrreducibleDominantRatOver (S : Scheme.{u}) : Type (u + 1) where
  /-- The irreducible `S`-scheme `X` as an object of `IrreducibleDominantRatOver S`. -/
  of ::
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  [over : toScheme.Over S]
  [irreducibleSpace : IrreducibleSpace toScheme]

attribute [instance] IrreducibleDominantRatOver.over IrreducibleDominantRatOver.irreducibleSpace

namespace IrreducibleDominantRatOver

variable {S : Scheme.{u}}

/-- A morphism in `IrreducibleDominantRatOver S` is a dominant `S`-rational map. -/
@[ext]
structure Hom (X Y : IrreducibleDominantRatOver.{u} S) where
  /-- The underlying rational map. -/
  toRationalMap : X.toScheme ⤏ Y.toScheme
  [isDominant : toRationalMap.IsDominant]
  [isOver : toRationalMap.IsOver S]

attribute [instance] Hom.isDominant Hom.isOver

noncomputable instance : Category (IrreducibleDominantRatOver.{u} S) where
  Hom := Hom
  id X := ⟨RationalMap.id X.toScheme⟩
  comp f g := ⟨f.toRationalMap.comp g.toRationalMap⟩
  id_comp _ := Hom.ext (RationalMap.id_comp _)
  comp_id _ := Hom.ext (RationalMap.comp_id _)
  assoc _ _ _ := Hom.ext (RationalMap.comp_assoc _ _ _)

/-- **Stacks 0A20 (2).** Irreducible schemes `X` and `Y` over `S` are *`S`-birational* if they
are isomorphic in the category of irreducible schemes over `S` and dominant `S`-rational maps. -/
@[stacks 0A20 "(2): isomorphic in the category `IrreducibleDominantRatOver S` of irreducible
schemes over `S` and dominant `S`-rational maps; `birationalOver_iff_birationalOver` identifies
it with Mathlib's `Scheme.BirationalOver`."]
def BirationalOver (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] [IrreducibleSpace X]
    [IrreducibleSpace Y] : Prop :=
  Nonempty ((of X : IrreducibleDominantRatOver S) ≅ of Y)

variable {X Y : Scheme.{u}} [X.Over S] [Y.Over S] [IrreducibleSpace X] [IrreducibleSpace Y]

/-- `S`-birationality unfolded: mutually inverse dominant `S`-rational maps. -/
theorem birationalOver_iff_exists_comp_eq_id :
    BirationalOver S X Y ↔
      ∃ (f : X ⤏ Y) (_ : f.IsDominant) (_ : f.IsOver S) (g : Y ⤏ X) (_ : g.IsDominant)
        (_ : g.IsOver S), f.comp g = RationalMap.id X ∧ g.comp f = RationalMap.id Y := by
  constructor
  · rintro ⟨e⟩
    exact ⟨Hom.toRationalMap e.hom, inferInstance, inferInstance, Hom.toRationalMap e.inv,
      inferInstance, inferInstance, congr_arg Hom.toRationalMap e.hom_inv_id,
      congr_arg Hom.toRationalMap e.inv_hom_id⟩
  · rintro ⟨f, hf, hf', g, hg, hg', h₁, h₂⟩
    exact ⟨⟨(⟨f⟩ : Hom (of X : IrreducibleDominantRatOver S) (of Y)),
      (⟨g⟩ : Hom (of Y : IrreducibleDominantRatOver S) (of X)), Hom.ext h₁, Hom.ext h₂⟩⟩

/-- `S`-birationality in the category of irreducible `S`-schemes and dominant `S`-rational maps
(Stacks 0A20 (2)) is equivalent to the existence of a partial isomorphism over `S`, Mathlib's
`Scheme.BirationalOver`. -/
@[stacks 0A20 "(2): the definition by isomorphism in the category of dominant `S`-rational
maps is equivalent to Mathlib's `Scheme.BirationalOver`."]
theorem birationalOver_iff_birationalOver :
    BirationalOver S X Y ↔ Scheme.BirationalOver (X ↘ S) (Y ↘ S) := by
  rw [birationalOver_iff_exists_comp_eq_id]
  constructor
  · rintro ⟨f, hf, hf', g, hg, hg', h₁, h₂⟩
    obtain ⟨f, hfS, rfl⟩ := f.exists_partialMap_over S
    obtain ⟨g, -, rfl⟩ := g.exists_partialMap_over S
    have : IsDominant f.hom := f.isDominant_toRationalMap_iff.1 hf
    have : IsDominant g.hom := g.isDominant_toRationalMap_iff.1 hg
    rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff] at h₁ h₂
    obtain ⟨e, h, he⟩ := f.exists_partialIso_of_comp_equiv_id g h₁ h₂
    have hfS' : f.hom ≫ Y ↘ S = f.domain.ι ≫ X ↘ S := by
      simp
    refine ⟨e, ?_⟩
    change e.iso.hom ≫ e.target.ι ≫ Y ↘ S = e.source.ι ≫ X ↘ S
    rw [← Category.assoc, he, Category.assoc, hfS', ← Category.assoc, Scheme.homOfLE_ι]
  · rintro ⟨e, he⟩
    have : e.toPartialMap.IsOver S := PartialMap.isOver_iff.2 (by
      simp only [PartialMap.compHom_hom, PartialIso.toPartialMap_hom]
      exact he)
    have : e.symm.toPartialMap.IsOver S := PartialMap.isOver_iff.2 (by
      simp only [PartialMap.compHom_hom, PartialIso.toPartialMap_hom]
      exact PartialIso.IsOver.symm he)
    refine ⟨e.toRationalMap, inferInstance, inferInstance, e.symm.toRationalMap, inferInstance,
      inferInstance, ?_, ?_⟩
    · rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff]
      exact e.toPartialMap_comp_symm_equiv
    · rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff]
      exact e.symm.toPartialMap_comp_symm_equiv

end IrreducibleDominantRatOver

end AlgebraicGeometry
