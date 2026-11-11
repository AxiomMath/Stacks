module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Composition
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.BirationalOpenIso

/-!
# Birationality through dominant rational maps

Irreducible schemes form a category whose morphisms are the dominant rational maps, and, over a
base scheme `S`, irreducible schemes over `S` form a category whose morphisms are the dominant
`S`-rational maps. Two irreducible schemes are *birational* (respectively *`S`-birational*) when
they are isomorphic in that category, that is, when there are mutually inverse dominant
(`S`-)rational maps between them. This is the definition of [Stacks, Tag 0A20].

We show that this holds exactly when the schemes have (`S`-)isomorphic nonempty open
subschemes, which is [Stacks, Tag 0BAA], and deduce that the notion agrees with
`AlgebraicGeometry.Scheme.Birational` and `AlgebraicGeometry.Scheme.BirationalOver`, which are
defined through isomorphisms of dense open subschemes.

## Main definitions

* `AlgebraicGeometry.IrreducibleScheme`: the category of irreducible schemes and dominant
  rational maps.
* `AlgebraicGeometry.IrreducibleOverScheme`: the category of irreducible schemes over `S` and
  dominant `S`-rational maps.
* `AlgebraicGeometry.Scheme.DominantBirational`: birationality in the sense of Tag 0A20 (1).
* `AlgebraicGeometry.Scheme.DominantBirationalOver`: `S`-birationality in the sense of
  Tag 0A20 (2).

## Main results

* `AlgebraicGeometry.Scheme.dominantBirational_iff_exists_nonempty_open_iso`: Tag 0BAA (1).
* `AlgebraicGeometry.Scheme.dominantBirationalOver_iff_exists_nonempty_open_iso`: Tag 0BAA (2).
* `AlgebraicGeometry.Scheme.dominantBirational_iff_birational` and
  `AlgebraicGeometry.Scheme.dominantBirationalOver_iff_birationalOver`: the comparison with the
  library's notions.
* `AlgebraicGeometry.Scheme.dominantBirationalOver_of_isBirational`: the final assertion of
  Tag 0BAC, a birational morphism over `S` of finite type with reduced target, or of finite
  presentation, between irreducible schemes makes them `S`-birational.

## Implementation notes

In the category of irreducible schemes, the composite of `f : X ⟶ Y` and `g : Y ⟶ Z` is the
rational map `f.comp g` (first `f`, then `g`) of `AlgebraicGeometry.Scheme.RationalMap.comp`.

## References

* [Stacks Project, Tag 0A20](https://stacks.math.columbia.edu/tag/0A20)
* [Stacks Project, Tag 0BAA](https://stacks.math.columbia.edu/tag/0BAA)
* [Stacks Project, Tag 0BAC](https://stacks.math.columbia.edu/tag/0BAC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An irreducible scheme, regarded as an object of the category of irreducible schemes and
dominant rational maps. -/
structure IrreducibleScheme where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  /-- The underlying scheme is irreducible. -/
  [irreducibleSpace : IrreducibleSpace toScheme]

attribute [instance] IrreducibleScheme.irreducibleSpace

/-- A dominant rational map between irreducible schemes. -/
structure IrreducibleScheme.Hom (X Y : IrreducibleScheme.{u}) where
  /-- The underlying rational map. -/
  toRationalMap : X.toScheme ⤏ Y.toScheme
  /-- The rational map is dominant. -/
  [isDominant : toRationalMap.IsDominant]

attribute [instance] IrreducibleScheme.Hom.isDominant

/-- Two dominant rational maps are equal if their underlying rational maps are equal. -/
@[ext]
lemma IrreducibleScheme.Hom.ext {X Y : IrreducibleScheme.{u}} (f g : X.Hom Y)
    (h : f.toRationalMap = g.toRationalMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Irreducible schemes form a category whose morphisms are the dominant rational maps, with
composition of rational maps. -/
noncomputable instance IrreducibleScheme.instCategory : Category IrreducibleScheme.{u} where
  Hom := IrreducibleScheme.Hom
  id X := ⟨Scheme.RationalMap.id X.toScheme⟩
  comp f g := ⟨f.toRationalMap.comp g.toRationalMap⟩
  id_comp f := IrreducibleScheme.Hom.ext _ _ (Scheme.RationalMap.id_comp f.toRationalMap)
  comp_id f := IrreducibleScheme.Hom.ext _ _ (Scheme.RationalMap.comp_id f.toRationalMap)
  assoc f g h := IrreducibleScheme.Hom.ext _ _
    (Scheme.RationalMap.comp_assoc f.toRationalMap g.toRationalMap h.toRationalMap)

/-- An irreducible scheme over `S`, regarded as an object of the category of irreducible
schemes over `S` and dominant `S`-rational maps. -/
structure IrreducibleOverScheme (S : Scheme.{u}) where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  /-- The structure morphism to `S`. -/
  [over : toScheme.Over S]
  /-- The underlying scheme is irreducible. -/
  [irreducibleSpace : IrreducibleSpace toScheme]

attribute [instance] IrreducibleOverScheme.over IrreducibleOverScheme.irreducibleSpace

/-- A dominant `S`-rational map between irreducible schemes over `S`. -/
structure IrreducibleOverScheme.Hom {S : Scheme.{u}} (X Y : IrreducibleOverScheme S) where
  /-- The underlying rational map. -/
  toRationalMap : X.toScheme ⤏ Y.toScheme
  /-- The rational map is dominant. -/
  [isDominant : toRationalMap.IsDominant]
  /-- The rational map is an `S`-rational map. -/
  [isOver : toRationalMap.IsOver S]

attribute [instance] IrreducibleOverScheme.Hom.isDominant IrreducibleOverScheme.Hom.isOver

/-- Two dominant `S`-rational maps are equal if their underlying rational maps are equal. -/
@[ext]
lemma IrreducibleOverScheme.Hom.ext {S : Scheme.{u}} {X Y : IrreducibleOverScheme S}
    (f g : X.Hom Y) (h : f.toRationalMap = g.toRationalMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Irreducible schemes over `S` form a category whose morphisms are the dominant `S`-rational
maps, with composition of rational maps. -/
noncomputable instance IrreducibleOverScheme.instCategory (S : Scheme.{u}) :
    Category (IrreducibleOverScheme S) where
  Hom := IrreducibleOverScheme.Hom
  id X := ⟨Scheme.RationalMap.id X.toScheme⟩
  comp f g := ⟨f.toRationalMap.comp g.toRationalMap⟩
  id_comp f := IrreducibleOverScheme.Hom.ext _ _ (Scheme.RationalMap.id_comp f.toRationalMap)
  comp_id f := IrreducibleOverScheme.Hom.ext _ _ (Scheme.RationalMap.comp_id f.toRationalMap)
  assoc f g h := IrreducibleOverScheme.Hom.ext _ _
    (Scheme.RationalMap.comp_assoc f.toRationalMap g.toRationalMap h.toRationalMap)

namespace Scheme

/-- Two irreducible schemes are **birational** if they are isomorphic in the category of
irreducible schemes and dominant rational maps. -/
def DominantBirational (X Y : Scheme.{u}) [IrreducibleSpace X] [IrreducibleSpace Y] : Prop :=
  Nonempty (IrreducibleScheme.mk X ≅ IrreducibleScheme.mk Y)

/-- Two irreducible schemes over `S` are **`S`-birational** if they are isomorphic in the
category of irreducible schemes over `S` and dominant `S`-rational maps. -/
def DominantBirationalOver (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] [IrreducibleSpace X]
    [IrreducibleSpace Y] : Prop :=
  Nonempty (IrreducibleOverScheme.mk (S := S) X ≅ IrreducibleOverScheme.mk Y)

variable {S X Y : Scheme.{u}}

/-- Birationality of irreducible schemes is the existence of mutually inverse dominant rational
maps. -/
theorem dominantBirational_iff [IrreducibleSpace X] [IrreducibleSpace Y] :
    DominantBirational X Y ↔
      ∃ (f : X ⤏ Y) (g : Y ⤏ X) (_ : f.IsDominant) (_ : g.IsDominant),
        f.comp g = RationalMap.id X ∧ g.comp f = RationalMap.id Y := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.hom.toRationalMap, e.inv.toRationalMap, inferInstance, inferInstance,
      congrArg IrreducibleScheme.Hom.toRationalMap e.hom_inv_id,
      congrArg IrreducibleScheme.Hom.toRationalMap e.inv_hom_id⟩
  · rintro ⟨f, g, _, _, h₁, h₂⟩
    refine ⟨⟨(⟨f⟩ : IrreducibleScheme.Hom _ _), (⟨g⟩ : IrreducibleScheme.Hom _ _), ?_, ?_⟩⟩
    · exact IrreducibleScheme.Hom.ext _ _ h₁
    · exact IrreducibleScheme.Hom.ext _ _ h₂

/-- `S`-birationality of irreducible schemes over `S` is the existence of mutually inverse
dominant `S`-rational maps. -/
theorem dominantBirationalOver_iff [X.Over S] [Y.Over S] [IrreducibleSpace X]
    [IrreducibleSpace Y] :
    DominantBirationalOver S X Y ↔
      ∃ (f : X ⤏ Y) (g : Y ⤏ X) (_ : f.IsDominant) (_ : g.IsDominant) (_ : f.IsOver S)
        (_ : g.IsOver S), f.comp g = RationalMap.id X ∧ g.comp f = RationalMap.id Y := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.hom.toRationalMap, e.inv.toRationalMap, inferInstance, inferInstance,
      inferInstance, inferInstance,
      congrArg IrreducibleOverScheme.Hom.toRationalMap e.hom_inv_id,
      congrArg IrreducibleOverScheme.Hom.toRationalMap e.inv_hom_id⟩
  · rintro ⟨f, g, _, _, _, _, h₁, h₂⟩
    refine ⟨⟨(⟨f⟩ : IrreducibleOverScheme.Hom _ _), (⟨g⟩ : IrreducibleOverScheme.Hom _ _), ?_,
      ?_⟩⟩
    · exact IrreducibleOverScheme.Hom.ext _ _ h₁
    · exact IrreducibleOverScheme.Hom.ext _ _ h₂

/-- The underlying partial map of a partial isomorphism is dominant. -/
theorem PartialIso.isDominant_toPartialMap_hom (p : X.PartialIso Y) :
    IsDominant p.toPartialMap.hom := by
  have := Opens.isDominant_ι p.dense_target
  change IsDominant (p.iso.hom ≫ p.target.ι)
  infer_instance

/-- Following a partial isomorphism by its inverse is the identity rational map. -/
theorem PartialIso.toRationalMap_comp_symm [IrreducibleSpace X] [IrreducibleSpace Y]
    (p : X.PartialIso Y) :
    haveI := p.isDominant_toPartialMap_hom
    p.toRationalMap.comp p.symm.toRationalMap = RationalMap.id X := by
  have := p.isDominant_toPartialMap_hom
  have h' : (p.toPartialMap.hom ∣_ p.target) ≫ p.iso.inv =
      (p.toPartialMap.hom ⁻¹ᵁ p.target).ι := by
    refine (Iso.comp_inv_eq _).2 ((cancel_mono p.target.ι).1 ?_)
    exact (morphismRestrict_ι _ _).trans (Category.assoc _ _ _).symm
  have key : (p.toPartialMap.comp p.symm.toPartialMap).hom =
      (p.toPartialMap.comp p.symm.toPartialMap).domain.ι := by
    refine (Iso.inv_comp_eq _).2 (Eq.trans ?_ (Hom.isoImage_hom_ι _ _).symm)
    exact (Category.assoc _ _ _).symm.trans (h' =≫ p.source.ι)
  rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff]
  refine ⟨_, (p.toPartialMap.comp p.symm.toPartialMap).dense_domain, le_rfl, le_top, ?_⟩
  refine (congrArg (X.homOfLE le_rfl ≫ ·) key).trans ((X.homOfLE_ι _).trans ?_)
  change _ = X.homOfLE _ ≫ X.topIso.hom ≫ 𝟙 X
  simp

/-- A partial isomorphism between irreducible schemes gives an isomorphism in the category of
irreducible schemes and dominant rational maps. -/
theorem dominantBirational_of_partialIso [IrreducibleSpace X] [IrreducibleSpace Y]
    (p : X.PartialIso Y) : DominantBirational X Y := by
  have := p.isDominant_toPartialMap_hom
  have := p.symm.isDominant_toPartialMap_hom
  exact dominantBirational_iff.2 ⟨p.toRationalMap, p.symm.toRationalMap, inferInstance,
    inferInstance, p.toRationalMap_comp_symm, p.symm.toRationalMap_comp_symm⟩

/-- An `S`-partial isomorphism between irreducible schemes over `S` gives an isomorphism in the
category of irreducible schemes over `S` and dominant `S`-rational maps. -/
theorem dominantBirationalOver_of_partialIso [X.Over S] [Y.Over S] [IrreducibleSpace X]
    [IrreducibleSpace Y] (p : X.PartialIso Y) (hp : p.IsOver (X ↘ S) (Y ↘ S)) :
    DominantBirationalOver S X Y := by
  have := p.isDominant_toPartialMap_hom
  have := p.symm.isDominant_toPartialMap_hom
  have : p.toPartialMap.IsOver S :=
    ⟨show (p.iso.hom ≫ p.target.ι) ≫ Y ↘ S = p.source.toScheme ↘ S by
      simpa [PartialIso.IsOver] using hp⟩
  have : p.symm.toPartialMap.IsOver S :=
    ⟨show (p.iso.inv ≫ p.source.ι) ≫ X ↘ S = p.target.toScheme ↘ S by
      have hp' : p.iso.hom ≫ p.target.ι ≫ Y ↘ S = p.source.ι ≫ X ↘ S := hp
      have h : p.iso.inv ≫ p.source.ι ≫ X ↘ S = p.target.ι ≫ Y ↘ S := by
        rw [← hp', Iso.inv_hom_id_assoc]
      simpa using h⟩
  exact dominantBirationalOver_iff.2 ⟨p.toRationalMap, p.symm.toRationalMap, inferInstance,
    inferInstance, inferInstance, inferInstance, p.toRationalMap_comp_symm,
    p.symm.toRationalMap_comp_symm⟩

/-- **Stacks 0BAC**, the final assertion: a birational morphism `f : X ⟶ Y` over `S` between
irreducible schemes, locally of finite type with `Y` reduced or locally of finite presentation,
makes `X` and `Y` `S`-birational in the sense of [Stacks, Tag 0A20] (2), i.e. isomorphic in the
category of irreducible schemes over `S` and dominant `S`-rational maps. -/
@[stacks 0BAC "in particular: irreducible X, Y are S-birational in the sense of 0A20"]
theorem dominantBirationalOver_of_isBirational [X.Over S] [Y.Over S] (f : X ⟶ Y) [f.IsOver S]
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    [IrreducibleSpace X] [IrreducibleSpace Y] (hf : IsBirational f)
    (hfin : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    DominantBirationalOver S X Y := by
  obtain ⟨p, hp⟩ := birationalOver_of_isBirational (X ↘ S) (Y ↘ S) f hf (comp_over f S) hfin
  exact dominantBirationalOver_of_partialIso p hp

/-- If following a dominant partial map `F` by `G` agrees with the identity on a dense open,
then on a dense open `W` inside the domain of `F`, the map `F` lands in the domain of `G` and is
followed by `G` to the inclusion of `W`. -/
private theorem exists_retraction_of_comp_equiv_id [IrreducibleSpace X] [Nonempty Y]
    (F : X.PartialMap Y) [IsDominant F.hom] (G : Y.PartialMap X)
    (h : (F.comp G).equiv (PartialMap.id X)) :
    ∃ (W : X.Opens) (_ : Dense (W : Set X)) (h₁ : W ≤ F.domain)
      (a : W.toScheme ⟶ G.domain.toScheme),
      a ≫ G.domain.ι = X.homOfLE h₁ ≫ F.hom ∧ a ≫ G.hom = W.ι := by
  obtain ⟨W, hW, hWl, hWr, e⟩ := h
  refine ⟨W, hW, hWl.trans (F.domain.ι_image_le _),
    X.homOfLE (V := F.domain.ι ''ᵁ F.hom ⁻¹ᵁ G.domain) hWl ≫
      (F.domain.ι.isoImage _).inv ≫ F.hom ∣_ G.domain, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, morphismRestrict_ι, Opens.isoImage_ι_inv_ι_assoc]
    exact X.homOfLE_homOfLE_assoc _ _ _
  · simp only [Category.assoc]
    exact e.trans (X.homOfLE_ι hWr)

/-- The point-free core of Tag 0BAA: maps `φ` and `ψ` defined on opens `A` and `B`, which are
inverse to each other on opens `W₁ ≤ A` and `W₂ ≤ B`, restrict to an isomorphism of the open
`W₁ ⊓ A.ι ''ᵁ φ ⁻¹ᵁ W₂` of `X` with an open of `Y`. -/
private theorem exists_iso_of_retractions {A : X.Opens} {B : Y.Opens}
    (φ : A.toScheme ⟶ Y) (ψ : B.toScheme ⟶ X)
    {W₁ : X.Opens} (h₁ : W₁ ≤ A) (a : W₁.toScheme ⟶ B.toScheme)
    (ha : a ≫ B.ι = X.homOfLE h₁ ≫ φ) (ha' : a ≫ ψ = W₁.ι)
    {W₂ : Y.Opens} (h₂ : W₂ ≤ B) (b : W₂.toScheme ⟶ A.toScheme)
    (hb : b ≫ A.ι = Y.homOfLE h₂ ≫ ψ) (hb' : b ≫ φ = W₂.ι) :
    ∃ (V : Y.Opens) (hU : W₁ ⊓ A.ι ''ᵁ φ ⁻¹ᵁ W₂ ≤ A)
      (e : (W₁ ⊓ A.ι ''ᵁ φ ⁻¹ᵁ W₂).toScheme ≅ V.toScheme),
      e.hom ≫ V.ι = X.homOfLE hU ≫ φ := by
  have pa : ∀ w, B.ι (a w) = φ (X.homOfLE h₁ w) := fun w => by
    simpa using congr($ha w)
  have pa' : ∀ w, ψ (a w) = W₁.ι w := fun w => by
    simpa using congr($ha' w)
  have pb : ∀ w, A.ι (b w) = ψ (Y.homOfLE h₂ w) := fun w => by
    simpa using congr($hb w)
  have pb' : ∀ w, φ (b w) = W₂.ι w := fun w => by
    simpa using congr($hb' w)
  set U : X.Opens := W₁ ⊓ A.ι ''ᵁ φ ⁻¹ᵁ W₂ with hUdef
  set V : Y.Opens := W₂ ⊓ B.ι ''ᵁ ψ ⁻¹ᵁ W₁ with hVdef
  have hUW : U ≤ W₁ := inf_le_left
  have hVW : V ≤ W₂ := inf_le_left
  have hU : U ≤ A := hUW.trans h₁
  have hV : V ≤ B := hVW.trans h₂
  have rα : Set.range (X.homOfLE hUW ≫ a ≫ B.ι) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [V.range_ι]
    obtain ⟨z, hz, hzx⟩ := x.2.2
    have e1 : (X.homOfLE hU ≫ A.ι) x = U.ι x := by rw [homOfLE_ι]
    have hz' : X.homOfLE hU x = z := A.ι.isOpenEmbedding.injective
      ((Scheme.Hom.comp_apply _ _ _).symm.trans (e1.trans hzx.symm))
    have hc : X.homOfLE hUW ≫ a ≫ B.ι = X.homOfLE hU ≫ φ := by
      rw [ha, homOfLE_homOfLE_assoc]
    refine ⟨?_, ?_⟩
    · rw [hc, Scheme.Hom.comp_apply, hz']
      exact hz
    · refine ⟨a (X.homOfLE hUW x), ?_, by simp⟩
      change ψ (a _) ∈ W₁
      rw [pa']
      exact (X.homOfLE hUW x).2
  have rβ : Set.range (Y.homOfLE hVW ≫ b ≫ A.ι) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [U.range_ι]
    obtain ⟨z, hz, hzy⟩ := y.2.2
    have e1 : (Y.homOfLE hV ≫ B.ι) y = V.ι y := by rw [homOfLE_ι]
    have hz' : Y.homOfLE hV y = z := B.ι.isOpenEmbedding.injective
      ((Scheme.Hom.comp_apply _ _ _).symm.trans (e1.trans hzy.symm))
    have hc : Y.homOfLE hVW ≫ b ≫ A.ι = Y.homOfLE hV ≫ ψ := by
      rw [hb, homOfLE_homOfLE_assoc]
    refine ⟨?_, ?_⟩
    · rw [hc, Scheme.Hom.comp_apply, hz']
      exact hz
    · refine ⟨b (Y.homOfLE hVW y), ?_, by simp⟩
      change φ (b _) ∈ W₂
      rw [pb']
      exact (Y.homOfLE hVW y).2
  set α := IsOpenImmersion.lift V.ι _ rα
  set β := IsOpenImmersion.lift U.ι _ rβ
  have hα : α ≫ V.ι = X.homOfLE hUW ≫ a ≫ B.ι := IsOpenImmersion.lift_fac _ _ _
  have hβ : β ≫ U.ι = Y.homOfLE hVW ≫ b ≫ A.ι := IsOpenImmersion.lift_fac _ _ _
  have hαB : α ≫ Y.homOfLE (hVW.trans h₂) = X.homOfLE hUW ≫ a := by
    rw [← cancel_mono B.ι, Category.assoc, homOfLE_ι, hα, Category.assoc]
  have hβA : β ≫ X.homOfLE hU = Y.homOfLE hVW ≫ b := by
    rw [← cancel_mono A.ι, Category.assoc, homOfLE_ι, hβ, Category.assoc]
  refine ⟨V, hU, { hom := α, inv := β, hom_inv_id := ?_, inv_hom_id := ?_ }, ?_⟩
  · rw [← cancel_mono U.ι, Category.assoc, hβ, Category.id_comp, hb, homOfLE_homOfLE_assoc,
      ← Category.assoc, hαB, Category.assoc, ha', homOfLE_ι]
  · rw [← cancel_mono V.ι, Category.assoc, hα, Category.id_comp, ha, homOfLE_homOfLE_assoc,
      ← Category.assoc, hβA, Category.assoc, hb', homOfLE_ι]
  · rw [hα, ha, homOfLE_homOfLE_assoc]

/-- Mutually inverse dominant rational maps between irreducible schemes restrict to an
isomorphism of dense open subschemes, given on its source by a representative of the first
map. -/
private theorem exists_partialIso_of_comp_eq_id [IrreducibleSpace X] [IrreducibleSpace Y]
    (F : X.PartialMap Y) (G : Y.PartialMap X) [F.toRationalMap.IsDominant]
    [G.toRationalMap.IsDominant]
    (h₁ : F.toRationalMap.comp G.toRationalMap = RationalMap.id X)
    (h₂ : G.toRationalMap.comp F.toRationalMap = RationalMap.id Y) :
    ∃ (p : X.PartialIso Y) (hp : p.source ≤ F.domain),
      p.iso.hom ≫ p.target.ι = X.homOfLE hp ≫ F.hom := by
  have : IsDominant F.hom := (PartialMap.isDominant_toRationalMap_iff F).1 inferInstance
  have : IsDominant G.hom := (PartialMap.isDominant_toRationalMap_iff G).1 inferInstance
  rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff] at h₁ h₂
  obtain ⟨W₁, hW₁, k₁, a, ha, ha'⟩ := exists_retraction_of_comp_equiv_id F G h₁
  obtain ⟨W₂, hW₂, k₂, b, hb, hb'⟩ := exists_retraction_of_comp_equiv_id G F h₂
  obtain ⟨V, hU, e, he⟩ := exists_iso_of_retractions F.hom G.hom k₁ a ha ha' k₂ b hb hb'
  have hpre : ((F.hom ⁻¹ᵁ W₂ : F.domain.toScheme.Opens) : Set F.domain.toScheme).Nonempty := by
    obtain ⟨_, hz, ⟨z, rfl⟩⟩ :=
      F.hom.denseRange.inter_open_nonempty _ W₂.2 hW₂.nonempty
    exact ⟨z, hz⟩
  have hUne : ((W₁ ⊓ F.domain.ι ''ᵁ F.hom ⁻¹ᵁ W₂ : X.Opens) : Set X).Nonempty := by
    obtain ⟨x, hx₁, hx₂⟩ := hW₁.inter_open_nonempty _ (F.domain.ι ''ᵁ F.hom ⁻¹ᵁ W₂).2
      (hpre.image _)
    exact ⟨x, hx₂, hx₁⟩
  obtain ⟨x, hx⟩ := hUne
  have hVne : (V : Set Y).Nonempty := ⟨_, (e.hom ⟨x, hx⟩).2⟩
  exact ⟨⟨_, (TopologicalSpace.Opens.isOpen _).dense ⟨x, hx⟩, V, V.2.dense hVne, e⟩, hU, he⟩

/-- For irreducible schemes, birationality in the sense of mutually inverse dominant rational
maps agrees with the existence of an isomorphism of dense open subschemes. -/
theorem dominantBirational_iff_birational [IrreducibleSpace X] [IrreducibleSpace Y] :
    DominantBirational X Y ↔ Birational X Y := by
  refine ⟨fun h => ?_, fun ⟨p⟩ => dominantBirational_of_partialIso p⟩
  obtain ⟨f, g, _, _, h₁, h₂⟩ := dominantBirational_iff.1 h
  obtain ⟨F, rfl⟩ := PartialMap.toRationalMap_surjective f
  obtain ⟨G, rfl⟩ := PartialMap.toRationalMap_surjective g
  obtain ⟨p, -, -⟩ := exists_partialIso_of_comp_eq_id F G h₁ h₂
  exact ⟨p⟩

/-- For irreducible schemes over `S`, `S`-birationality in the sense of mutually inverse
dominant `S`-rational maps agrees with the existence of an `S`-isomorphism of dense open
subschemes. -/
theorem dominantBirationalOver_iff_birationalOver [X.Over S] [Y.Over S] [IrreducibleSpace X]
    [IrreducibleSpace Y] :
    DominantBirationalOver S X Y ↔ BirationalOver (X ↘ S) (Y ↘ S) := by
  refine ⟨fun h => ?_, fun ⟨p, hp⟩ => dominantBirationalOver_of_partialIso p hp⟩
  obtain ⟨f, g, _, _, _, _, h₁, h₂⟩ := dominantBirationalOver_iff.1 h
  obtain ⟨F, hF, rfl⟩ := f.exists_partialMap_over S
  obtain ⟨G, rfl⟩ := PartialMap.toRationalMap_surjective g
  obtain ⟨p, hp, hpF⟩ := exists_partialIso_of_comp_eq_id F G h₁ h₂
  have hF' : F.hom ≫ Y ↘ S = F.domain.ι ≫ X ↘ S := PartialMap.isOver_iff.1 hF
  refine ⟨p, ?_⟩
  change p.iso.hom ≫ p.target.ι ≫ Y ↘ S = p.source.ι ≫ X ↘ S
  rw [← Category.assoc, hpF, Category.assoc, hF', ← Category.assoc, homOfLE_ι]

/-- Two irreducible schemes are birational, in the sense of being isomorphic in the category of
irreducible schemes and dominant rational maps, if and only if they have isomorphic nonempty
open subschemes. -/
@[stacks 0BAA "(1)"]
theorem dominantBirational_iff_exists_nonempty_open_iso [IrreducibleSpace X]
    [IrreducibleSpace Y] :
    DominantBirational X Y ↔
      ∃ (U : X.Opens) (V : Y.Opens),
        (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧ Nonempty (U.toScheme ≅ V.toScheme) :=
  dominantBirational_iff_birational.trans birational_iff_exists_nonempty_open_iso

/-- Two irreducible schemes over `S` are `S`-birational, in the sense of being isomorphic in the
category of irreducible schemes over `S` and dominant `S`-rational maps, if and only if there are
nonempty opens `U ⊆ X` and `V ⊆ Y` which are isomorphic over `S`. -/
@[stacks 0BAA "(2)"]
theorem dominantBirationalOver_iff_exists_nonempty_open_iso [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    DominantBirationalOver S X Y ↔
      ∃ (U : X.Opens) (V : Y.Opens),
        (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧
          ∃ e : U.toScheme ≅ V.toScheme, e.hom ≫ V.ι ≫ Y ↘ S = U.ι ≫ X ↘ S :=
  dominantBirationalOver_iff_birationalOver.trans
    (birationalOver_iff_exists_nonempty_open_iso _ _)

end Scheme

end AlgebraicGeometry

end
