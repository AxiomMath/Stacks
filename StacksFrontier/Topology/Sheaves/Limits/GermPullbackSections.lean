module

public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Topology.Sheaves.Limits.GermPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The germ model is the inverse image, for sheaves of sets

`StacksFrontier.Topology.Sheaves.Limits.GermPullback` builds the inverse image `g⁻¹𝒢` of a presheaf
of types along a continuous map `g : Z → Y` as a *germ model*: a section over `W` is a function
`W → Σ y, 𝒢.stalkOfSize y` which is locally the family of germs of a single section of `𝒢`.

This file proves the universal property of the germ model for presheaves of sets: there is a unit
`𝒢 ⟶ g _* (g⁻¹𝒢)`, and for every sheaf of sets `H` on `Z` and every `φ : 𝒢 ⟶ g _* H` there is a
unique morphism `g⁻¹𝒢 ⟶ H` whose composite with the unit is `φ`. Consequently, for a sheaf of sets
the germ model is Mathlib's `TopCat.Sheaf.pullback` (`GermPullback.sheafPullbackIso`).

## Main definitions

* `GermPullback.toPushforwardPresheafOfSets`: the unit `𝒢 ⟶ g _* (g⁻¹𝒢)` on presheaves of sets.
* `GermPullback.toPushforwardOfSets`: the unit as a morphism of sheaves of sets.
* `GermPullback.Sets.localValue`: the only possible value of a mapping-out morphism at a germwise
  pullback `ofSection hV s`, namely the restriction of `φ_V s`.
* `GermPullback.Sets.appValue` and `GermPullback.Sets.mapOut`: the mapping-out morphism
  `g⁻¹𝒢 ⟶ H` determined by `φ : 𝒢 ⟶ g _* H`.
* `GermPullback.sheafPullbackIso`: the germ model is Mathlib's sheaf pullback.

## Main results

* `GermPullback.Sets.existsUnique_isAppValue`: the value of a mapping-out morphism at a section
  exists and is unique.
* `GermPullback.Sets.existsUnique_mapOut`: **the mapping-out half of the adjunction**, for
  presheaves of sets.
* `GermPullback.existsUnique_mapOutSheafOfSets`: the same, read in the category of sheaves of
  sets and with Mathlib's `TopCat.Sheaf.pushforward`.
* `GermPullback.unit_comp_map_sheafPullbackComparison`: the identification of the germ model
  with the sheaf pullback carries the unit to the unit.
* `GermPullback.bijective_comap_of_homeomorph`: pulling germ-model sections back along a
  homeomorphism is a bijection, with inverse the pullback along the inverse homeomorphism.

## References

* [Stacks Project, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u t

namespace GermPullback

variable {Y Z : TopCat.{u}} (g : Z ⟶ Y) (𝒢 : Y.Presheaf (Type (max u t)))

/-- **The unit of the germ model on presheaves of sets**: a presheaf of types maps to the
pushforward of its germ-model inverse image. Over an open `V` of `Y` the component sends a
section `s ∈ 𝒢(V)` to the germ-model section `z ↦ ⟨g z, germ_{g z} s⟩` of `g⁻¹𝒢` over `g⁻¹V`,
which is `GermPullback.ofSection`. -/
def toPushforwardPresheafOfSets :
    𝒢 ⟶ (TopCat.Presheaf.pushforward (Type (max u t)) g).obj
      (sheaf (ConcreteCategory.hom g) 𝒢).presheaf
    where
  app V := TypeCat.ofHom fun s ↦
    ofSection (g := ConcreteCategory.hom g) (𝒢 := 𝒢)
      (W := (Opens.map g).obj V.unop) (V := V.unop) (fun z ↦ z.2) s
  naturality {V V'} i := by
    refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
    refine GermPullback.ext fun z ↦ ?_
    exact congrArg (fun t ↦ (⟨ConcreteCategory.hom g z.1, t⟩ : Germs 𝒢))
      (𝒢.germOfSize_res_apply i.unop _ z.2 s)

/-- The unit sends `s ∈ 𝒢(V)` to its family of germs, i.e. to `GermPullback.ofSection`. -/
lemma toPushforwardPresheafOfSets_app_apply (V : Opens Y) (s : 𝒢.obj (op V)) :
    (toPushforwardPresheafOfSets g 𝒢).app (op V) s =
      ofSection (g := ConcreteCategory.hom g) (𝒢 := 𝒢)
        (W := (Opens.map g).obj V) (V := V) (fun z ↦ z.2) s :=
  rfl

/-- **The unit of the germ model, for sheaves of sets.** A sheaf of sets on `Y` maps to the
pushforward along `g` of its germ-model inverse image. -/
def toPushforwardOfSets (F : Y.Sheaf (Type (max u t))) :
    F ⟶ (TopCat.Sheaf.pushforward (Type (max u t)) g).obj
      (sheaf (ConcreteCategory.hom g) F.presheaf) :=
  ⟨toPushforwardPresheafOfSets g F.presheaf⟩

namespace Sets

variable {g 𝒢} {H : Z.Presheaf (Type (max u t))}
  (φ : 𝒢 ⟶ (TopCat.Presheaf.pushforward (Type (max u t)) g).obj H)

/-- Two germs of `𝒢` based at the same point which are equal as points of the total space of
germs are equal. -/
lemma snd_eq_of_mk_eq {y : Y} {a b : 𝒢.stalkOfSize y} (h : (⟨y, a⟩ : Germs 𝒢) = ⟨y, b⟩) : a = b :=
  eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp h).2

/-- Restriction of a germwise pullback is the germwise pullback of the same section. -/
lemma map_ofSection {A B : Opens Z} (j : B ⟶ A) {V : Opens Y}
    (hV : ∀ z : A, (ConcreteCategory.hom g) z.1 ∈ V) (s : 𝒢.obj (op V)) :
    (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.map j.op (ofSection hV s) =
      ofSection (fun z ↦ hV (j z)) s :=
  ext fun _ ↦ rfl

/-- **Two germwise pullbacks that agree have the same generating germs.** If the restrictions of
a germ-model section `σ` to `W₁` and `W₂` are the germwise pullbacks of `s₁` and `s₂`, then `s₁`
and `s₂` have the same germ at `g x` for every `x ∈ W₁ ∩ W₂`. -/
lemma germ_eq_of_restrict_eq {W : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.obj (op W))
    {W₁ W₂ : Opens Z} (i₁ : W₁ ⟶ W) (i₂ : W₂ ⟶ W) {V₁ V₂ : Opens Y}
    (h₁ : ∀ z : W₁, (ConcreteCategory.hom g) z.1 ∈ V₁)
    (h₂ : ∀ z : W₂, (ConcreteCategory.hom g) z.1 ∈ V₂)
    (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂))
    (e₁ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.map i₁.op σ = ofSection h₁ s₁)
    (e₂ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.map i₂.op σ = ofSection h₂ s₂)
    {x : Z} (hx₁ : x ∈ W₁) (hx₂ : x ∈ W₂) :
    𝒢.germOfSize V₁ ((ConcreteCategory.hom g) x) (h₁ ⟨x, hx₁⟩) s₁ =
      𝒢.germOfSize V₂ ((ConcreteCategory.hom g) x) (h₂ ⟨x, hx₂⟩) s₂ := by
  have k₁ : σ.1 (i₁ ⟨x, hx₁⟩) =
      ⟨(ConcreteCategory.hom g) x, 𝒢.germOfSize V₁ ((ConcreteCategory.hom g) x) (h₁ ⟨x, hx₁⟩) s₁⟩ :=
    congrArg (fun τ ↦ τ.1 ⟨x, hx₁⟩) e₁
  have k₂ : σ.1 (i₂ ⟨x, hx₂⟩) =
      ⟨(ConcreteCategory.hom g) x, 𝒢.germOfSize V₂ ((ConcreteCategory.hom g) x) (h₂ ⟨x, hx₂⟩) s₂⟩ :=
    congrArg (fun τ ↦ τ.1 ⟨x, hx₂⟩) e₂
  have hi : i₁ ⟨x, hx₁⟩ = i₂ ⟨x, hx₂⟩ := Subtype.ext rfl
  exact snd_eq_of_mk_eq ((k₁.symm.trans (congrArg σ.1 hi)).trans k₂)

/-- Naturality of `φ`, read on elements. -/
lemma app_map_apply {V V' : Opens Y} (k : V' ⟶ V) (s : 𝒢.obj (op V)) :
    φ.app (op V') (𝒢.map k.op s) = H.map ((Opens.map g).map k).op (φ.app (op V) s) := by
  exact ConcreteCategory.congr_hom (φ.naturality k.op) s

/-- **The local value attached to a section of `𝒢`.** If `g` carries the open `W` of `Z` into the
open `V` of `Y`, then `φ` sends `s ∈ 𝒢(V)` into `H(g⁻¹V)`, and restriction gives an element of
`H(W)`. -/
def localValue {W : Opens Z} {V : Opens Y}
    (hV : ∀ z : W, (ConcreteCategory.hom g) z.1 ∈ V) (s : 𝒢.obj (op V)) : H.obj (op W) :=
  H.map (homOfLE (fun z hz ↦ hV ⟨z, hz⟩) : W ⟶ (Opens.map g).obj V).op (φ.app (op V) s)

/-- Restricting twice along maps of opens is restricting along the composite, whatever the map. -/
private lemma map_map_apply_of_comp_eq {X : TopCat.{u}} (P : X.Presheaf (Type (max u t)))
    {A B C : Opens X} (f : B ⟶ A) (j : C ⟶ B) (k : C ⟶ A) (x : P.obj (op A)) :
    P.map j.op (P.map f.op x) = P.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, Subsingleton.elim (j ≫ f) k]

/-- The local value is compatible with restriction of the open of `Z`. -/
lemma localValue_map {W W' : Opens Z} (j : W' ⟶ W) {V : Opens Y}
    (hV : ∀ z : W, (ConcreteCategory.hom g) z.1 ∈ V) (s : 𝒢.obj (op V)) :
    H.map j.op (localValue φ hV s) = localValue φ (fun z ↦ hV (j z)) s := by
  exact map_map_apply_of_comp_eq H _ _ _ _

/-- Over the full inverse image `g⁻¹V`, the local value of `s` is `φ s` itself. -/
lemma localValue_self {V : Opens Y} (s : 𝒢.obj (op V)) :
    localValue φ (fun z : (Opens.map g).obj V ↦ z.2) s = φ.app (op V) s := by
  simp only [localValue]
  rw [show (homOfLE (fun z hz ↦ (fun z : (Opens.map g).obj V ↦ z.2) ⟨z, hz⟩) :
      (Opens.map g).obj V ⟶ (Opens.map g).obj V) = 𝟙 _ from Subsingleton.elim _ _,
    op_id, H.map_id, ConcreteCategory.id_apply]

/-- Restricting the generating section of `𝒢` does not change the local value. -/
lemma localValue_map_section {W : Opens Z} {V V' : Opens Y} (k : V' ⟶ V)
    (hV' : ∀ z : W, (ConcreteCategory.hom g) z.1 ∈ V')
    (hV : ∀ z : W, (ConcreteCategory.hom g) z.1 ∈ V) (s : 𝒢.obj (op V)) :
    localValue φ hV' (𝒢.map k.op s) = localValue φ hV s := by
  rw [localValue, localValue, app_map_apply φ k s]
  exact map_map_apply_of_comp_eq H _ _ _ _

/-- The germ of a local value at a point is the germ there of the `φ`-image of the generating
section, taken over the full inverse image `g⁻¹V`. -/
lemma germ_localValue {W : Opens Z} {V : Opens Y}
    (hV : ∀ z : W, (ConcreteCategory.hom g) z.1 ∈ V) (s : 𝒢.obj (op V)) {x : Z} (hx : x ∈ W) :
    H.germOfSize W x hx (localValue φ hV s) =
      H.germOfSize ((Opens.map g).obj V) x (hV ⟨x, hx⟩) (φ.app (op V) s) :=
  H.germOfSize_res_apply _ x hx _

/-- **Local values with the same generating germ have the same germ.** If `s₁ ∈ 𝒢(V₁)` and
`s₂ ∈ 𝒢(V₂)` have the same germ at `g x`, then their local values have the same germ at `x`. -/
lemma germ_localValue_eq {W₁ W₂ : Opens Z} {V₁ V₂ : Opens Y}
    (h₁ : ∀ z : W₁, (ConcreteCategory.hom g) z.1 ∈ V₁)
    (h₂ : ∀ z : W₂, (ConcreteCategory.hom g) z.1 ∈ V₂)
    (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂)) {x : Z} (hx₁ : x ∈ W₁) (hx₂ : x ∈ W₂)
    (he : 𝒢.germOfSize V₁ ((ConcreteCategory.hom g) x) (h₁ ⟨x, hx₁⟩) s₁ =
      𝒢.germOfSize V₂ ((ConcreteCategory.hom g) x) (h₂ ⟨x, hx₂⟩) s₂) :
    H.germOfSize W₁ x hx₁ (localValue φ h₁ s₁) = H.germOfSize W₂ x hx₂ (localValue φ h₂ s₂) := by
  obtain ⟨V₃, hxV₃, k₁, k₂, hk⟩ :=
    𝒢.germOfSize_eq ((ConcreteCategory.hom g) x) (h₁ ⟨x, hx₁⟩) (h₂ ⟨x, hx₂⟩) s₁ s₂ he
  have hx₃ : x ∈ (Opens.map g).obj V₃ := hxV₃
  have key : ∀ {V V' : Opens Y} (k : V' ⟶ V) (hxV' : x ∈ (Opens.map g).obj V')
      (s : 𝒢.obj (op V)),
      H.germOfSize ((Opens.map g).obj V) x (k.le hxV') (φ.app (op V) s) =
        H.germOfSize ((Opens.map g).obj V') x hxV' (φ.app (op V') (𝒢.map k.op s)) := by
    intro V V' k hxV' s
    rw [app_map_apply φ k s]
    exact (H.germOfSize_res_apply ((Opens.map g).map k) x hxV' _).symm
  rw [germ_localValue, germ_localValue, key k₁ hx₃ s₁, key k₂ hx₃ s₂]
  exact congrArg (fun t ↦ H.germOfSize ((Opens.map g).obj V₃) x hx₃ (φ.app (op V₃) t)) hk

/-- Local values generated by equal germwise pullbacks over the same open are equal. -/
lemma localValue_eq_of_ofSection_eq (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    {V₁ V₂ : Opens Y}
    (h₁ : ∀ z : W, (ConcreteCategory.hom g) z.1 ∈ V₁)
    (h₂ : ∀ z : W, (ConcreteCategory.hom g) z.1 ∈ V₂)
    (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂)) (e : ofSection h₁ s₁ = ofSection h₂ s₂) :
    localValue φ h₁ s₁ = localValue φ h₂ s₂ := by
  refine TopCat.Presheaf.sectionOfSize_ext (⟨H, hH⟩ : Z.Sheaf (Type (max u t))) W _ _ fun x hx ↦ ?_
  refine germ_localValue_eq φ h₁ h₂ s₁ s₂ hx hx ?_
  exact snd_eq_of_mk_eq (congrArg (fun τ ↦ τ.1 ⟨x, hx⟩) e)

/-- **The defining property of the value of the mapping-out morphism at a section `σ`.** An element
`t ∈ H(W)` *is* the value at `σ` when, on every open `W₀ ≤ W` where `σ` is the germwise pullback of
a section `s` of `𝒢`, the restriction of `t` is the local value of `s`. -/
def IsAppValue {W : Opens Z} (σ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.obj (op W))
    (t : H.obj (op W)) : Prop :=
  ∀ ⦃W₀ : Opens Z⦄ (i : W₀ ⟶ W) ⦃V : Opens Y⦄
    (hV : ∀ z : W₀, (ConcreteCategory.hom g) z.1 ∈ V) (s : 𝒢.obj (op V)),
    (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.map i.op σ = ofSection hV s →
      H.map i.op t = localValue φ hV s

/-- **The mapping-out value exists and is unique.** If `H` is a sheaf, then for every section
`σ` of the germ model over `W` there is a unique `t ∈ H(W)` with `IsAppValue φ σ t`. -/
theorem existsUnique_isAppValue (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.obj (op W)) :
    ∃! t : H.obj (op W), IsAppValue φ σ t := by
  classical
  choose A hmem ii V hV s hs using fun z : W ↦ exists_repr σ z.2
  have hres : ∀ z : W,
      (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.map (ii z).op σ = ofSection (hV z) (s z) :=
    fun z ↦ ext fun x ↦ hs z x
  have hcover : W ≤ iSup A := fun x hx ↦ Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  have huniq : ∀ t t' : H.obj (op W), IsAppValue φ σ t → IsAppValue φ σ t' → t = t' := by
    intro t t' ht ht'
    refine TopCat.Sheaf.eq_of_locally_eq' (⟨H, hH⟩ : Z.Sheaf (Type (max u t))) A W ii hcover
      t t' fun z ↦ ?_
    rw [ht (ii z) (hV z) (s z) (hres z), ht' (ii z) (hV z) (s z) (hres z)]
  have hcompat : TopCat.Presheaf.IsCompatible H A (fun z ↦ localValue φ (hV z) (s z)) := by
    intro z z'
    rw [localValue_map, localValue_map]
    refine TopCat.Presheaf.sectionOfSize_ext (⟨H, hH⟩ : Z.Sheaf (Type (max u t))) _ _ _
      fun x hx ↦ ?_
    exact germ_localValue_eq φ _ _ (s z) (s z') hx hx
      (germ_eq_of_restrict_eq σ (ii z) (ii z') (hV z) (hV z') (s z) (s z')
        (hres z) (hres z') hx.1 hx.2)
  obtain ⟨t, hts, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨H, hH⟩ : Z.Sheaf (Type (max u t)))
    A W ii hcover (fun z ↦ localValue φ (hV z) (s z)) hcompat
  have hIs : IsAppValue φ σ t := by
    intro W₁ i₁ V₁ hV₁ s₁ he₁
    refine TopCat.Presheaf.sectionOfSize_ext (⟨H, hH⟩ : Z.Sheaf (Type (max u t))) W₁ _ _
      fun x hx ↦ ?_
    have hxW : x ∈ W := i₁.le hx
    rw [H.germOfSize_res_apply i₁ x hx t,
      ← H.germOfSize_res_apply (ii ⟨x, hxW⟩) x (hmem ⟨x, hxW⟩) t, hts ⟨x, hxW⟩]
    exact germ_localValue_eq φ (hV ⟨x, hxW⟩) hV₁ (s ⟨x, hxW⟩) s₁ (hmem ⟨x, hxW⟩) hx
      (germ_eq_of_restrict_eq σ (ii ⟨x, hxW⟩) i₁ (hV ⟨x, hxW⟩) hV₁ (s ⟨x, hxW⟩) s₁
        (hres ⟨x, hxW⟩) he₁ (hmem ⟨x, hxW⟩) hx)
  exact ⟨t, hIs, fun t' ht' ↦ huniq t' t ht' hIs⟩

/-- The value of the mapping-out morphism at a section of the germ model. -/
def appValue (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.obj (op W)) : H.obj (op W) :=
  (existsUnique_isAppValue φ hH σ).choose

/-- `appValue` has the defining property. -/
lemma appValue_spec (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.obj (op W)) :
    IsAppValue φ σ (appValue φ hH σ) :=
  (existsUnique_isAppValue φ hH σ).choose_spec.1

/-- `appValue` is the only element with the defining property. -/
lemma appValue_unique (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    {σ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.obj (op W)} {t : H.obj (op W)}
    (ht : IsAppValue φ σ t) : t = appValue φ hH σ :=
  (existsUnique_isAppValue φ hH σ).choose_spec.2 t ht

/-- **`appValue` at a germwise pullback is the local value.** -/
lemma appValue_ofSection (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z} {V : Opens Y}
    (hV : ∀ z : W, (ConcreteCategory.hom g) z.1 ∈ V) (s : 𝒢.obj (op V)) :
    appValue φ hH (ofSection hV s) = localValue φ hV s := by
  refine (appValue_unique φ hH ?_).symm
  intro W₀ i V₀ hV₀ s₀ he
  rw [localValue_map]
  refine localValue_eq_of_ofSection_eq φ hH _ _ _ _ ?_
  rw [← map_ofSection i hV s]
  exact he

/-- **`appValue` commutes with restriction.** -/
lemma appValue_map (hH : TopCat.Presheaf.IsSheaf H) {W W' : Opens Z} (j : W' ⟶ W)
    (σ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.obj (op W)) :
    H.map j.op (appValue φ hH σ) =
      appValue φ hH ((sheaf (ConcreteCategory.hom g) 𝒢).presheaf.map j.op σ) := by
  refine appValue_unique φ hH ?_
  intro W₀ i V₀ hV₀ s₀ he
  have he' : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.map (i ≫ j).op σ = ofSection hV₀ s₀ := by
    rw [op_comp, (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.map_comp,
      ConcreteCategory.comp_apply]
    exact he
  calc H.map i.op (H.map j.op (appValue φ hH σ))
      = H.map (i ≫ j).op (appValue φ hH σ) := map_map_apply_of_comp_eq H _ _ _ _
    _ = localValue φ hV₀ s₀ := appValue_spec φ hH σ (i ≫ j) hV₀ s₀ he'

/-- **The mapping-out morphism of the germ model, for presheaves of sets.** Given a sheaf of sets
`H` on `Z` and a map `φ : 𝒢 ⟶ g _* H`, this is the morphism `g⁻¹𝒢 ⟶ H` whose value at a section `σ`
is `appValue`. -/
def mapOut (hH : TopCat.Presheaf.IsSheaf H) :
    (sheaf (ConcreteCategory.hom g) 𝒢).presheaf ⟶ H where
  app W := TypeCat.ofHom fun σ ↦ appValue φ hH σ
  naturality {W W'} j := by
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
    exact (appValue_map φ hH j.unop σ).symm

/-- The components of `mapOut` are `appValue`. -/
lemma mapOut_app_apply (hH : TopCat.Presheaf.IsSheaf H) (W : Opens Z)
    (σ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf.obj (op W)) :
    (mapOut φ hH).app (op W) σ = appValue φ hH σ :=
  rfl

/-- **A morphism out of the germ model is determined by its effect on germwise pullbacks.** The
composite of the unit with `ψ` is `φ` exactly when `ψ` sends the germwise pullback of each
`s ∈ 𝒢(V)` over the whole of `g⁻¹V` to `φ_V s`. -/
lemma toPushforwardPresheafOfSets_comp_eq_iff
    (ψ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf ⟶ H) :
    (toPushforwardPresheafOfSets g 𝒢 ≫
        (TopCat.Presheaf.pushforward (Type (max u t)) g).map ψ = φ) ↔
      ∀ (V : Opens Y) (s : 𝒢.obj (op V)),
        ψ.app (op ((Opens.map g).obj V))
            (ofSection (g := ConcreteCategory.hom g) (𝒢 := 𝒢)
              (W := (Opens.map g).obj V) (V := V) (fun z ↦ z.2) s) =
          φ.app (op V) s := by
  refine ⟨by rintro rfl V s; rfl, fun h ↦ ?_⟩
  ext V s
  exact h V s

/-- **`mapOut` solves the mapping-out problem**: its composite with the unit is `φ`. -/
lemma toPushforwardPresheafOfSets_comp_mapOut (hH : TopCat.Presheaf.IsSheaf H) :
    toPushforwardPresheafOfSets g 𝒢 ≫
      (TopCat.Presheaf.pushforward (Type (max u t)) g).map (mapOut φ hH) = φ :=
  (toPushforwardPresheafOfSets_comp_eq_iff φ _).2 fun V s ↦
    (appValue_ofSection φ hH (W := (Opens.map g).obj V)
      (fun z : (Opens.map g).obj V ↦ z.2) s).trans (localValue_self φ s)

/-- **`mapOut` is the only solution of the mapping-out problem**: a morphism whose composite with
the unit is `φ` is `mapOut φ hH`. -/
lemma mapOut_unique (hH : TopCat.Presheaf.IsSheaf H)
    {ψ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf ⟶ H}
    (hψ : toPushforwardPresheafOfSets g 𝒢 ≫
      (TopCat.Presheaf.pushforward (Type (max u t)) g).map ψ = φ) :
    ψ = mapOut φ hH := by
  refine NatTrans.ext (funext fun ⟨W⟩ ↦ ConcreteCategory.hom_ext _ _ fun σ ↦ ?_)
  refine appValue_unique φ hH fun W₀ i V₀ hV₀ s₀ he ↦ ?_
  rw [← NatTrans.naturality_apply, he, localValue,
    ← (toPushforwardPresheafOfSets_comp_eq_iff φ ψ).1 hψ V₀ s₀, ← NatTrans.naturality_apply]
  rfl

/-- **The mapping-out half of the germ-model adjunction, for presheaves of sets.** For every
sheaf of sets `H` on `Z` and every map `φ : 𝒢 ⟶ g _* H` there is a *unique* morphism
`ψ : g⁻¹𝒢 ⟶ H` of presheaves of sets whose composite with the unit is `φ`. -/
@[ega "0 3.5.3" "partial, special case"]
theorem existsUnique_mapOut (hH : TopCat.Presheaf.IsSheaf H) :
    ∃! ψ : (sheaf (ConcreteCategory.hom g) 𝒢).presheaf ⟶ H,
      toPushforwardPresheafOfSets g 𝒢 ≫
        (TopCat.Presheaf.pushforward (Type (max u t)) g).map ψ = φ :=
  ⟨mapOut φ hH, toPushforwardPresheafOfSets_comp_mapOut φ hH, fun _ hψ ↦ mapOut_unique φ hH hψ⟩

end Sets

/-- **The mapping-out half of the germ-model adjunction, in the category of sheaves of sets.**
For every sheaf of sets `H` on `Z` and every morphism `φ : F ⟶ g_*H` there is a unique morphism
`ψ : g⁻¹F ⟶ H` of sheaves whose composite with the unit `toPushforwardOfSets` is `φ`. -/
theorem existsUnique_mapOutSheafOfSets (F : Y.Sheaf (Type (max u t))) (H : Z.Sheaf (Type (max u t)))
    (φ : F ⟶ (TopCat.Sheaf.pushforward (Type (max u t)) g).obj H) :
    ∃! ψ : sheaf (⇑g) F.presheaf ⟶ H,
      toPushforwardOfSets g F ≫ (TopCat.Sheaf.pushforward (Type (max u t)) g).map ψ = φ := by
  obtain ⟨ψ, hψ, huniq⟩ := Sets.existsUnique_mapOut (g := g) (𝒢 := F.presheaf)
    (H := H.presheaf) φ.1 H.2
  refine ⟨⟨ψ⟩, Sheaf.hom_ext hψ, fun ρ hρ ↦ ?_⟩
  exact Sheaf.hom_ext (huniq ρ.1 (congrArg (fun k ↦ k.1) hρ))

/-- **The comparison of the germ model with Mathlib's sheaf pullback**: the transpose of the
germ-model unit `toPushforwardOfSets` across the pullback–pushforward adjunction. It is an
isomorphism, `GermPullback.sheafPullbackIso`. -/
def sheafPullbackComparison (F : Y.Sheaf (Type u)) :
    (TopCat.Sheaf.pullback (Type u) g).obj F ⟶ sheaf (⇑g) F.presheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).homEquiv F _).symm
    (toPushforwardOfSets g F)

/-- The comparison transposes back to the germ-model unit. -/
lemma unit_comp_map_sheafPullbackComparison (F : Y.Sheaf (Type u)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F ≫
        (TopCat.Sheaf.pushforward (Type u) g).map (sheafPullbackComparison g F) =
      toPushforwardOfSets g F :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).homEquiv F
    (sheaf (⇑g) F.presheaf)).apply_symm_apply (toPushforwardOfSets g F)

/-- The morphism in the other direction, supplied by the universal property of the germ model
applied to the unit of the pullback–pushforward adjunction. -/
def sheafPullbackComparisonInv (F : Y.Sheaf (Type u)) :
    sheaf (⇑g) F.presheaf ⟶ (TopCat.Sheaf.pullback (Type u) g).obj F :=
  (existsUnique_mapOutSheafOfSets g F ((TopCat.Sheaf.pullback (Type u) g).obj F)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F)).choose

/-- The defining property of `sheafPullbackComparisonInv`. -/
lemma toPushforwardOfSets_comp_map_sheafPullbackComparisonInv (F : Y.Sheaf (Type u)) :
    toPushforwardOfSets g F ≫
        (TopCat.Sheaf.pushforward (Type u) g).map (sheafPullbackComparisonInv g F) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F :=
  (existsUnique_mapOutSheafOfSets g F ((TopCat.Sheaf.pullback (Type u) g).obj F)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F)).choose_spec.1

/-- **The germ model is Mathlib's sheaf pullback.** For a continuous map `g : Z ⟶ Y` and a sheaf of
sets `F` on `Y`, the comparison of the germ-model inverse image `g⁻¹F` with
`TopCat.Sheaf.pullback`, the sheafification of the presheaf pullback, is an isomorphism. -/
@[ega "0 3.7.1" "special case"]
instance isIso_sheafPullbackComparison (F : Y.Sheaf (Type u)) :
    IsIso (sheafPullbackComparison g F) := by
  obtain ⟨ρ, -, huniq⟩ := existsUnique_mapOutSheafOfSets g F (sheaf (⇑g) F.presheaf)
    (toPushforwardOfSets g F)
  have h1 : toPushforwardOfSets g F ≫ (TopCat.Sheaf.pushforward (Type u) g).map
      (sheafPullbackComparisonInv g F ≫ sheafPullbackComparison g F) =
      toPushforwardOfSets g F := by
    rw [Functor.map_comp, ← Category.assoc,
      toPushforwardOfSets_comp_map_sheafPullbackComparisonInv,
      unit_comp_map_sheafPullbackComparison]
  have h2 : toPushforwardOfSets g F ≫ (TopCat.Sheaf.pushforward (Type u) g).map
      (𝟙 (sheaf (⇑g) F.presheaf)) = toPushforwardOfSets g F := by
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  refine ⟨sheafPullbackComparisonInv g F, ?_, (huniq _ h1).trans (huniq _ h2).symm⟩
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).homEquiv F _).injective ?_
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    unit_comp_map_sheafPullbackComparison,
    toPushforwardOfSets_comp_map_sheafPullbackComparisonInv]
  simp

/-- **The germ model is Mathlib's sheaf pullback**, as an isomorphism. -/
def sheafPullbackIso (F : Y.Sheaf (Type u)) :
    (TopCat.Sheaf.pullback (Type u) g).obj F ≅ sheaf (⇑g) F.presheaf :=
  asIso (sheafPullbackComparison g F)

/-- **Pulling germ-model sections back along a homeomorphism is a bijection.** If `e` is a
homeomorphism carrying `W'` into `W` and `W` into `W'` the other way, and the two structure maps to
`Y` agree under `e`, then `GermPullback.comap` along `e` is a bijection, with inverse `comap` along
`e.symm`. -/
lemma bijective_comap_of_homeomorph {T T' : TopCat.{u}} {ℋ : Y.Presheaf (Type (max u t))}
    {p : ↥T → ↥Y} {p' : ↥T' → ↥Y} (e : ↥T' ≃ₜ ↥T) (hcomp : ∀ z, p' z = p (e z))
    {W : Opens T} {W' : Opens T'} (hW : ∀ z : W', e z.1 ∈ W) (hW' : ∀ z : W, e.symm z.1 ∈ W') :
    Function.Bijective
      (fun σ : (sheaf p ℋ).presheaf.obj (op W) => comap (𝒢 := ℋ) e.continuous hcomp hW σ) := by
  have hcomp' : ∀ z, p z = p' (e.symm z) := fun z => by
    rw [hcomp (e.symm z), e.apply_symm_apply]
  refine Function.bijective_iff_has_inverse.2
    ⟨fun τ => comap (𝒢 := ℋ) e.symm.continuous hcomp' hW' τ, fun σ => ?_, fun τ => ?_⟩
  · exact ext fun z => congrArg σ.1 (Subtype.ext (e.apply_symm_apply z.1))
  · exact ext fun z => congrArg τ.1 (Subtype.ext (e.symm_apply_apply z.1))

end GermPullback

end
