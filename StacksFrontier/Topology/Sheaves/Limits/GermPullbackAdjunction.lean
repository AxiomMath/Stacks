module

public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Topology.Sheaves.Limits.GermPullbackAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The universal property of the germ model: it is the inverse image

`StacksFrontier.Topology.Sheaves.Limits.GermPullback` builds the inverse image `g⁻¹𝒢` of a presheaf
along a map `g : Z → Y` as a *germ model*: a section over `W` is a function `W → Σ y, 𝒢.stalk y`
which is locally the family of germs of a single section of `𝒢`.  The model is deliberately
concrete — restriction and pullback along a further map are literally precomposition, so it is
strictly functorial and needs no coherence isomorphisms — and the price is that it carries no
categorical universal property of its own: nothing relates it to Mathlib's
`TopCat.Sheaf.pullback`, and nothing exhibits it as a left adjoint of pushforward.

That gap is what blocked the two colimit-comparison clauses of Stacks 0A37 from consuming
`Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit.existsUnique_pull_eq`.  That theorem
characterizes the sheaf on the vertex of a limiting cone of sheafed spaces in *corepresented*
form, and its input is a family of maps `𝒢 ⟶ g _* H` phrased with **Mathlib's** pushforward;
the germ model offered no map of that shape at all, so the characterization could not be applied
to the germ-model pullback system of
`StacksFrontier.Topology.Sheaves.Limits.DescendOpensAbelian`.

This file supplies both halves of the universal property that the germ model previously lacked.

* The **unit** `𝒢 ⟶ g _* (g⁻¹𝒢)`, sending a section `s ∈ 𝒢(V)` to its family of germs over
  `g⁻¹V`.  This is the arrow whose shape `existsUnique_pull_eq` consumes, and the one needed to
  *write down* the comparison map out of the corepresented characterization.
* The **mapping-out** half: for every sheaf `H` on `Z` and every `φ : 𝒢 ⟶ g _* H` there is a
  unique `ψ : g⁻¹𝒢 ⟶ H` with `unit ≫ g _* ψ = φ`.  Together with the unit this says that the
  germ model *is* the inverse image, corepresented on sheaves — with no comparison to Mathlib's
  `TopCat.Sheaf.pullback` needed, and no adjunction functor constructed.

## Main definitions

* `GermPullback.toPushforwardPresheaf`: the unit at the level of presheaves of abelian groups,
  `𝒢 ⟶ f _* (GermPullback.abelianPresheaf f 𝒢)`.
* `GermPullback.toPushforward`: the same as a morphism of abelian **sheaves**,
  `ℱ ⟶ f _* (GermPullback.abelianSheaf f ℱ.presheaf)`.
* `GermPullback.localValue`: the only possible value of a mapping-out morphism at a germwise
  pullback `ofSection hV s`, namely the restriction of `φ_V s`.
* `GermPullback.appValue` and `GermPullback.mapOut`: the mapping-out morphism `g⁻¹𝒢 ⟶ H`
  determined by `φ : 𝒢 ⟶ g _* H`.

## Main results

* `GermPullback.toPushforwardPresheaf_app_apply`: the unit sends `s ∈ 𝒢(V)` to the germ-model
  section `z ↦ ⟨f z, germ_{f z} s⟩` over `f⁻¹V`, i.e. to `GermPullback.ofSection`.
* `GermPullback.existsUnique_isAppValue`: the value of a mapping-out morphism at a section
  exists and is unique.
* `GermPullback.existsUnique_mapOut`: **the mapping-out half of the adjunction.**

## Implementation notes

Naturality of the unit is `TopCat.Presheaf.germ_res_apply`: the germ of a restricted section is
the germ of the section.  Nothing else is involved, because `GermPullback.ofSection` is defined
by the germ formula and restriction in the model is precomposition.

The mapping-out morphism is built from what the germ model already proves.
`GermPullback.exists_repr` writes a section locally as `ofSection hV s`, so `ψ` must send it to
`localValue`, the restriction of `φ_V s`; that forces `ψ`.  The local values are compatible
because two sections of `𝒢` with the same germ at a point agree on a neighbourhood
(`TopCat.Presheaf.germ_eq`), and naturality of `φ` carries that to equality of germs in `H`
(`germ_localValue_eq`); so they glue, by `TopCat.Sheaf.existsUnique_gluing'`.  Separatedness of
`H` — `TopCat.Presheaf.section_ext` and `TopCat.Sheaf.eq_of_locally_eq'` — is what upgrades the
germwise statements to equalities, and it is also what makes the glued element satisfy the
defining property on *every* open where the section is a germwise pullback, not only on the
chosen covering.

Additivity of `ψ` is the one place where the group structure enters: near a point the two
sections are germwise pullbacks of `s₁ ∈ 𝒢(V₁)` and `s₂ ∈ 𝒢(V₂)`, their sum is the germwise
pullback of `resAdd 𝒢 s₁ s₂ ∈ 𝒢(V₁ ⊓ V₂)` (`ofSection_add_eq`), and the local value of a
`resAdd` is the sum of the local values (`localValue_resAdd`).

## References

* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace GermPullback

variable {Y Z : TopCat.{u}} (f : Z ⟶ Y) (𝒢 : Y.Presheaf AddCommGrpCat.{u})

/-- **The unit of the germ model**: a presheaf of abelian groups maps to the pushforward of its
germ-model inverse image.  Over an open `V` of `Y` the component sends a section `s ∈ 𝒢(V)` to
the germ-model section `z ↦ ⟨f z, germ_{f z} s⟩` of `f⁻¹𝒢` over `f⁻¹V`, which is
`GermPullback.ofSection`; it is additive by `GermPullback.ofSection_add`.

This is the arrow whose shape `SheafedSpaceLimit.existsUnique_pull_eq` consumes, and which the
germ model did not previously offer. -/
def toPushforwardPresheaf :
    𝒢 ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj
      (abelianPresheaf (ConcreteCategory.hom f) 𝒢) where
  app V := AddCommGrpCat.ofHom
    (ofSectionAddHom (g := ConcreteCategory.hom f) 𝒢
      (W := (Opens.map f).obj V.unop) (V := V.unop) (fun z => z.2))
  naturality {V V'} i := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    refine GermPullback.ext fun z => ?_
    exact congrArg (fun t => (⟨ConcreteCategory.hom f z.1, t⟩ : Germs (typePresheaf 𝒢)))
      ((typePresheaf 𝒢).germ_res_apply i.unop _ z.2 s)

/-- The unit sends a section to its family of germs, i.e. to `GermPullback.ofSection`. -/
lemma toPushforwardPresheaf_app_apply (V : Opens Y) (s : 𝒢.obj (op V)) :
    ConcreteCategory.hom ((toPushforwardPresheaf f 𝒢).app (op V)) s =
      ofSection (g := ConcreteCategory.hom f) (𝒢 := typePresheaf 𝒢)
        (W := (Opens.map f).obj V) (V := V) (fun z => z.2) s :=
  rfl

/-- The unit sends `s ∈ 𝒢(V)` to the germ-model section whose value at `z ∈ f⁻¹V` is the germ of
`s` at `f z`. -/
lemma toPushforwardPresheaf_app_apply_val (V : Opens Y) (s : 𝒢.obj (op V))
    (z : (Opens.map f).obj V) :
    (ConcreteCategory.hom ((toPushforwardPresheaf f 𝒢).app (op V)) s).1 z =
      ⟨ConcreteCategory.hom f z.1,
        (typePresheaf 𝒢).germ V (ConcreteCategory.hom f z.1) z.2 s⟩ :=
  rfl

/-- **The unit of the germ model, for sheaves of abelian groups.**  An abelian sheaf on `Y` maps
to the pushforward along `f` of its germ-model inverse image, by `toPushforwardPresheaf`. -/
def toPushforward (ℱ : Y.Sheaf AddCommGrpCat.{u}) :
    ℱ ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
      (abelianSheaf (ConcreteCategory.hom f) ℱ.presheaf) :=
  ⟨toPushforwardPresheaf f ℱ.presheaf⟩

/-- The sheaf-level unit is the presheaf-level one. -/
lemma toPushforward_hom (ℱ : Y.Sheaf AddCommGrpCat.{u}) :
    (toPushforward f ℱ).hom = toPushforwardPresheaf f ℱ.presheaf :=
  rfl

/-! ### The mapping-out half of the adjunction -/

section MappingOut

variable {𝒢} {H : Z.Presheaf AddCommGrpCat.{u}}
  (φ : 𝒢 ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj H)

/-! #### Germwise pullbacks: restriction, addition, and the zero section -/

/-- Restriction of a germwise pullback is the germwise pullback of the same section. -/
lemma map_ofSection {A B : Opens Z} (j : B ⟶ A) {V : Opens Y}
    (hV : ∀ z : A, (ConcreteCategory.hom f) z.1 ∈ V) (s : 𝒢.obj (op V)) :
    (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map j.op
        (ofSection.{u, u} (𝒢 := typePresheaf 𝒢) hV s) =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) (fun z ↦ hV (j z)) s :=
  ext fun _ ↦ rfl

/-- **The sum of two germwise pullbacks is a germwise pullback.**  Over an open `C` mapping into
both `V₁` and `V₂`, the sum of the germwise pullbacks of `s₁ ∈ 𝒢(V₁)` and `s₂ ∈ 𝒢(V₂)` is the
germwise pullback of `resAdd 𝒢 s₁ s₂ ∈ 𝒢(V₁ ⊓ V₂)`, because the germ maps of `𝒢` are additive
(`germ_resAdd`). -/
lemma ofSection_add_eq {C : Opens Z} {V₁ V₂ : Opens Y}
    (h₁ : ∀ z : C, (ConcreteCategory.hom f) z.1 ∈ V₁)
    (h₂ : ∀ z : C, (ConcreteCategory.hom f) z.1 ∈ V₂)
    (h₁₂ : ∀ z : C, (ConcreteCategory.hom f) z.1 ∈ V₁ ⊓ V₂)
    (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂)) :
    ofSection.{u, u} (𝒢 := typePresheaf 𝒢) h₁ s₁ + ofSection.{u, u} (𝒢 := typePresheaf 𝒢) h₂ s₂ =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) h₁₂ (resAdd 𝒢 s₁ s₂) := by
  refine ext fun z ↦ ?_
  rw [add_val, ofSection_val, stalkVal_ofSection, stalkVal_ofSection]
  exact congrArg (Sigma.mk _) (germ_resAdd 𝒢 s₁ s₂ (h₁ z) (h₂ z)).symm

/-- The zero section of the germ model is the germwise pullback of the zero section of `𝒢` over
the whole of `Y`. -/
lemma zero_eq_ofSection {W : Opens Z} (hT : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ (⊤ : Opens Y)) :
    (0 : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W)) =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) hT (0 : 𝒢.obj (op (⊤ : Opens Y))) := by
  refine ext fun z ↦ ?_
  rw [zero_val, ofSection_val]
  exact congrArg (Sigma.mk _) (germ_zero 𝒢 ⊤ (hT z)).symm

/-- **Two germwise pullbacks that agree have the same generating germs.**  The value of a
germ-model section at a point *is* its germ, so equality of two germwise pullbacks over opens
meeting at `x` forces equality of the germs at `f x` of the two generating sections. -/
lemma germ_eq_of_restrict_eq {W : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W))
    {W₁ W₂ : Opens Z} (i₁ : W₁ ⟶ W) (i₂ : W₂ ⟶ W) {V₁ V₂ : Opens Y}
    (h₁ : ∀ z : W₁, (ConcreteCategory.hom f) z.1 ∈ V₁)
    (h₂ : ∀ z : W₂, (ConcreteCategory.hom f) z.1 ∈ V₂)
    (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂))
    (e₁ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map i₁.op σ =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) h₁ s₁)
    (e₂ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map i₂.op σ =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) h₂ s₂)
    {x : Z} (hx₁ : x ∈ W₁) (hx₂ : x ∈ W₂) :
    (typePresheaf 𝒢).germ V₁ ((ConcreteCategory.hom f) x) (h₁ ⟨x, hx₁⟩) s₁ =
      (typePresheaf 𝒢).germ V₂ ((ConcreteCategory.hom f) x) (h₂ ⟨x, hx₂⟩) s₂ := by
  have k₁ : σ.1 (i₁ ⟨x, hx₁⟩) =
      ⟨(ConcreteCategory.hom f) x,
        (typePresheaf 𝒢).germ V₁ ((ConcreteCategory.hom f) x) (h₁ ⟨x, hx₁⟩) s₁⟩ :=
    congrArg (fun τ ↦ τ.1 ⟨x, hx₁⟩) e₁
  have k₂ : σ.1 (i₂ ⟨x, hx₂⟩) =
      ⟨(ConcreteCategory.hom f) x,
        (typePresheaf 𝒢).germ V₂ ((ConcreteCategory.hom f) x) (h₂ ⟨x, hx₂⟩) s₂⟩ :=
    congrArg (fun τ ↦ τ.1 ⟨x, hx₂⟩) e₂
  have hi : i₁ ⟨x, hx₁⟩ = i₂ ⟨x, hx₂⟩ := Subtype.ext rfl
  exact snd_eq_of_mk_eq 𝒢 ((k₁.symm.trans (congrArg σ.1 hi)).trans k₂)

/-- Restricting twice along `a` then `b` is restricting along any `c : C ⟶ A`. -/
private theorem map_op_map_op_apply {D : Type*} [Category D] {FD : D → D → Type*}
    {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    (P : Z.Presheaf D) {A B C : Opens Z} (a : B ⟶ A) (b : C ⟶ B) (c : C ⟶ A)
    (x : ToType (P.obj (op A))) :
    P.map b.op (P.map a.op x) = P.map c.op x := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp]
  exact congrArg (fun m ↦ ConcreteCategory.hom (P.map (Opposite.op m)) x) (Subsingleton.elim _ _)

/-- If `σ` restricts to a germwise pullback along `i`, it restricts to the same germwise pullback
over any open mapping into the source of `i`. -/
private theorem map_comp_ofSection {W W₁ W₂ : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W))
    (i : W₁ ⟶ W) (j : W₂ ⟶ W₁) (c : W₂ ⟶ W) {V : Opens Y}
    {h : ∀ z : W₁, (ConcreteCategory.hom f) z.1 ∈ V} {s : 𝒢.obj (op V)}
    (e : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map i.op σ =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) h s) :
    (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map c.op σ =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) (fun z ↦ h (j z)) s :=
  (map_op_map_op_apply (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf i j c
    σ).symm.trans ((congrArg _ e).trans (map_ofSection f j h s))

/-- Every section of the germ model is, near each point, the restriction-to-an-open of a germwise
pullback. -/
private theorem exists_map_eq_ofSection {W : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W)) {z : Z}
    (hz : z ∈ W) :
    ∃ (A : Opens Z) (_ : z ∈ A) (i : A ⟶ W) (V : Opens Y)
      (hV : ∀ x : A, (ConcreteCategory.hom f) x.1 ∈ V) (s : 𝒢.obj (op V)),
      (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map i.op σ =
        ofSection.{u, u} (𝒢 := typePresheaf 𝒢) hV s := by
  obtain ⟨A, hA, i, V, hV, s, hs⟩ := exists_repr σ hz
  exact ⟨A, hA, i, V, hV, s, ext hs⟩

/-! #### The local value of a section of `𝒢` -/

/-- Naturality of `φ`, read on elements. -/
lemma app_map_apply {V V' : Opens Y} (k : V' ⟶ V) (s : 𝒢.obj (op V)) :
    φ.app (op V') (𝒢.map k.op s) = H.map ((Opens.map f).map k).op (φ.app (op V) s) := by
  have h := ConcreteCategory.congr_hom (φ.naturality k.op) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- **The local value attached to a section of `𝒢`.**  If `f` carries the open `W` of `Z` into the
open `V` of `Y`, then `φ` sends `s ∈ 𝒢(V)` into `H(f⁻¹V)`, and restriction gives an element of
`H(W)`.  This is the only possible value of a mapping-out morphism at the germwise pullback
`ofSection hV s`, which is what forces uniqueness. -/
def localValue {W : Opens Z} {V : Opens Y}
    (hV : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ V) (s : 𝒢.obj (op V)) : H.obj (op W) :=
  H.map (homOfLE (fun z hz ↦ hV ⟨z, hz⟩) : W ⟶ (Opens.map f).obj V).op (φ.app (op V) s)

/-- The local value is compatible with restriction of the open of `Z`. -/
lemma localValue_map {W W' : Opens Z} (j : W' ⟶ W) {V : Opens Y}
    (hV : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ V) (s : 𝒢.obj (op V)) :
    H.map j.op (localValue f φ hV s) = localValue f φ (fun z ↦ hV (j z)) s := by
  rw [localValue, localValue]
  exact map_op_map_op_apply H _ _ _ _

/-- The local value is additive in the section of `𝒢`. -/
lemma localValue_add {W : Opens Z} {V : Opens Y}
    (hV : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ V) (s t : 𝒢.obj (op V)) :
    localValue f φ hV (s + t) = localValue f φ hV s + localValue f φ hV t := by
  simp only [localValue, map_add]

/-- The local value of the zero section is zero. -/
lemma localValue_zero {W : Opens Z} {V : Opens Y}
    (hV : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ V) :
    localValue f φ hV (0 : 𝒢.obj (op V)) = 0 := by
  simp only [localValue, map_zero]

/-- Over the full inverse image `f⁻¹V`, the local value of `s` is `φ s` itself. -/
lemma localValue_self {V : Opens Y} (s : 𝒢.obj (op V)) :
    localValue f φ (fun z : (Opens.map f).obj V ↦ z.2) s = φ.app (op V) s := by
  simp only [localValue]
  rw [show (homOfLE (fun z hz ↦ (fun z : (Opens.map f).obj V ↦ z.2) ⟨z, hz⟩) :
      (Opens.map f).obj V ⟶ (Opens.map f).obj V) = 𝟙 _ from Subsingleton.elim _ _,
    op_id, H.map_id, ConcreteCategory.id_apply]

/-- Restricting the generating section of `𝒢` does not change the local value. -/
lemma localValue_map_section {W : Opens Z} {V V' : Opens Y} (k : V' ⟶ V)
    (hV' : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ V')
    (hV : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ V) (s : 𝒢.obj (op V)) :
    localValue f φ hV' (𝒢.map k.op s) = localValue f φ hV s := by
  rw [localValue, localValue, app_map_apply f φ k s]
  exact map_op_map_op_apply H _ _ _ _

/-- **The local value of a sum.**  Over an open mapping into both `V₁` and `V₂`, the local value of
`resAdd 𝒢 s₁ s₂` is the sum of the local values of `s₁` and `s₂`. -/
lemma localValue_resAdd {C : Opens Z} {V₁ V₂ : Opens Y}
    (h₁ : ∀ z : C, (ConcreteCategory.hom f) z.1 ∈ V₁)
    (h₂ : ∀ z : C, (ConcreteCategory.hom f) z.1 ∈ V₂)
    (h₁₂ : ∀ z : C, (ConcreteCategory.hom f) z.1 ∈ V₁ ⊓ V₂)
    (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂)) :
    localValue f φ h₁₂ (resAdd 𝒢 s₁ s₂) = localValue f φ h₁ s₁ + localValue f φ h₂ s₂ := by
  rw [resAdd, localValue_add,
    localValue_map_section f φ (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)) h₁₂ h₁ s₁,
    localValue_map_section f φ (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)) h₁₂ h₂ s₂]

/-- The germ of a local value at a point is the germ there of the `φ`-image of the generating
section, taken over the full inverse image `f⁻¹V`. -/
lemma germ_localValue {W : Opens Z} {V : Opens Y}
    (hV : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ V) (s : 𝒢.obj (op V))
    {x : Z} (hx : x ∈ W) :
    H.germ W x hx (localValue f φ hV s) =
      H.germ ((Opens.map f).obj V) x (hV ⟨x, hx⟩) (φ.app (op V) s) :=
  H.germ_res_apply _ x hx _

/-- **Local values with the same generating germ have the same germ.**  If `s₁ ∈ 𝒢(V₁)` and
`s₂ ∈ 𝒢(V₂)` have the same germ at `f x`, then they agree on a smaller open `V₃ ∋ f x`
(`TopCat.Presheaf.germ_eq`), so their `φ`-images agree on `f⁻¹V₃` by naturality of `φ`, hence have
the same germ at `x`.

The sheaf condition on `H` is not used here: the statement is about germs, and it is `section_ext`
that turns germwise agreement into equality. -/
lemma germ_localValue_eq {W₁ W₂ : Opens Z} {V₁ V₂ : Opens Y}
    (h₁ : ∀ z : W₁, (ConcreteCategory.hom f) z.1 ∈ V₁)
    (h₂ : ∀ z : W₂, (ConcreteCategory.hom f) z.1 ∈ V₂)
    (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂))
    {x : Z} (hx₁ : x ∈ W₁) (hx₂ : x ∈ W₂)
    (he : (typePresheaf 𝒢).germ V₁ ((ConcreteCategory.hom f) x) (h₁ ⟨x, hx₁⟩) s₁ =
      (typePresheaf 𝒢).germ V₂ ((ConcreteCategory.hom f) x) (h₂ ⟨x, hx₂⟩) s₂) :
    H.germ W₁ x hx₁ (localValue f φ h₁ s₁) = H.germ W₂ x hx₂ (localValue f φ h₂ s₂) := by
  obtain ⟨V₃, hxV₃, k₁, k₂, hk⟩ := (typePresheaf 𝒢).germ_eq ((ConcreteCategory.hom f) x)
    (h₁ ⟨x, hx₁⟩) (h₂ ⟨x, hx₂⟩) s₁ s₂ he
  have hx₃ : x ∈ (Opens.map f).obj V₃ := hxV₃
  have key : ∀ {V V' : Opens Y} (k : V' ⟶ V) (hxV' : x ∈ (Opens.map f).obj V')
      (s : 𝒢.obj (op V)),
      H.germ ((Opens.map f).obj V) x (k.le hxV') (φ.app (op V) s) =
        H.germ ((Opens.map f).obj V') x hxV' (φ.app (op V') (𝒢.map k.op s)) := by
    intro V V' k hxV' s
    rw [app_map_apply f φ k s]
    exact (H.germ_res_apply ((Opens.map f).map k) x hxV' _).symm
  rw [germ_localValue, germ_localValue, key k₁ hx₃ s₁, key k₂ hx₃ s₂]
  exact congrArg (fun t ↦ H.germ ((Opens.map f).obj V₃) x hx₃ (φ.app (op V₃) t)) hk

/-- Local values generated by equal germwise pullbacks over the same open are equal. -/
lemma localValue_eq_of_ofSection_eq (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    {V₁ V₂ : Opens Y}
    (h₁ : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ V₁)
    (h₂ : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ V₂)
    (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂))
    (e : ofSection.{u, u} (𝒢 := typePresheaf 𝒢) h₁ s₁ =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) h₂ s₂) :
    localValue f φ h₁ s₁ = localValue f φ h₂ s₂ := by
  refine TopCat.Presheaf.section_ext (⟨H, hH⟩ : Z.Sheaf AddCommGrpCat.{u}) W _ _ fun x hx ↦ ?_
  refine germ_localValue_eq f φ h₁ h₂ s₁ s₂ hx hx ?_
  exact snd_eq_of_mk_eq 𝒢 (congrArg (fun τ ↦ τ.1 ⟨x, hx⟩) e)

/-! #### The value of the mapping-out morphism -/

/-- **The defining property of the value of the mapping-out morphism at a section `σ`.**  An
element `t ∈ H(W)` *is* the value at `σ` when, on every open `W₀ ≤ W` where `σ` is the germwise
pullback of a section `s` of `𝒢`, the restriction of `t` is the local value of `s`.  By
`exists_repr` such opens cover `W`, so a `t` with this property is unique; the construction below
glues the local values to produce one. -/
def IsAppValue {W : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W))
    (t : H.obj (op W)) : Prop :=
  ∀ ⦃W₀ : Opens Z⦄ (i : W₀ ⟶ W) ⦃V : Opens Y⦄
    (hV : ∀ z : W₀, (ConcreteCategory.hom f) z.1 ∈ V) (s : 𝒢.obj (op V)),
    (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map i.op σ =
        ofSection.{u, u} (𝒢 := typePresheaf 𝒢) hV s →
      H.map i.op t = localValue f φ hV s

/-- **The mapping-out value exists and is unique.**  Uniqueness is `eq_of_locally_eq'` on the
covering of `W` by the opens supplied by `exists_repr`.  Existence is `existsUnique_gluing'` for
that covering: the local values are compatible because two generating sections of `𝒢` whose germs
agree at a point have `φ`-images with the same germ there (`germ_localValue_eq`), and a sheaf is
separated.  That the glued element satisfies the property on *every* such open, not only on the
chosen covering, is again `section_ext`. -/
theorem existsUnique_isAppValue (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W)) :
    ∃! t : H.obj (op W), IsAppValue f φ σ t := by
  classical
  choose A hmem ii V hV s hres using fun z : W ↦ exists_map_eq_ofSection f σ z.2
  have hcover : W ≤ iSup A := fun x hx ↦ Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  have huniq : ∀ t t' : H.obj (op W), IsAppValue f φ σ t → IsAppValue f φ σ t' → t = t' := by
    intro t t' ht ht'
    refine TopCat.Sheaf.eq_of_locally_eq' (⟨H, hH⟩ : Z.Sheaf AddCommGrpCat.{u}) A W ii hcover
      t t' fun z ↦ ?_
    rw [ht (ii z) (hV z) (s z) (hres z), ht' (ii z) (hV z) (s z) (hres z)]
  have hcompat : TopCat.Presheaf.IsCompatible H A (fun z ↦ localValue f φ (hV z) (s z)) := by
    intro z z'
    rw [localValue_map, localValue_map]
    refine TopCat.Presheaf.section_ext (⟨H, hH⟩ : Z.Sheaf AddCommGrpCat.{u}) _ _ _ fun x hx ↦ ?_
    exact germ_localValue_eq f φ _ _ (s z) (s z') hx hx
      (germ_eq_of_restrict_eq f σ (ii z) (ii z') (hV z) (hV z') (s z) (s z')
        (hres z) (hres z') hx.1 hx.2)
  obtain ⟨t, hts, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨H, hH⟩ : Z.Sheaf AddCommGrpCat.{u})
    A W ii hcover (fun z ↦ localValue f φ (hV z) (s z)) hcompat
  have hIs : IsAppValue f φ σ t := by
    intro W₁ i₁ V₁ hV₁ s₁ he₁
    refine TopCat.Presheaf.section_ext (⟨H, hH⟩ : Z.Sheaf AddCommGrpCat.{u}) W₁ _ _ fun x hx ↦ ?_
    have hxW : x ∈ W := i₁.le hx
    rw [H.germ_res_apply i₁ x hx t,
      ← H.germ_res_apply (ii ⟨x, hxW⟩) x (hmem ⟨x, hxW⟩) t, hts ⟨x, hxW⟩]
    exact germ_localValue_eq f φ (hV ⟨x, hxW⟩) hV₁ (s ⟨x, hxW⟩) s₁ (hmem ⟨x, hxW⟩) hx
      (germ_eq_of_restrict_eq f σ (ii ⟨x, hxW⟩) i₁ (hV ⟨x, hxW⟩) hV₁ (s ⟨x, hxW⟩) s₁
        (hres ⟨x, hxW⟩) he₁ (hmem ⟨x, hxW⟩) hx)
  exact ⟨t, hIs, fun t' ht' ↦ huniq t' t ht' hIs⟩

/-- The value of the mapping-out morphism at a section of the germ model. -/
def appValue (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W)) : H.obj (op W) :=
  (existsUnique_isAppValue f φ hH σ).choose

/-- `appValue` has the defining property. -/
lemma appValue_spec (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    (σ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W)) :
    IsAppValue f φ σ (appValue f φ hH σ) :=
  (existsUnique_isAppValue f φ hH σ).choose_spec.1

/-- `appValue` is the only element with the defining property. -/
lemma appValue_unique (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    {σ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W)}
    {t : H.obj (op W)} (ht : IsAppValue f φ σ t) : t = appValue f φ hH σ :=
  (existsUnique_isAppValue f φ hH σ).choose_spec.2 t ht

/-- **`appValue` at a germwise pullback is the local value.** -/
lemma appValue_ofSection (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z} {V : Opens Y}
    (hV : ∀ z : W, (ConcreteCategory.hom f) z.1 ∈ V) (s : 𝒢.obj (op V)) :
    appValue f φ hH (ofSection.{u, u} (𝒢 := typePresheaf 𝒢) hV s) = localValue f φ hV s := by
  refine (appValue_unique f φ hH ?_).symm
  intro W₀ i V₀ hV₀ s₀ he
  rw [localValue_map]
  refine localValue_eq_of_ofSection_eq f φ hH _ _ _ _ ?_
  rw [← map_ofSection f i hV s]
  exact he

/-- **`appValue` commutes with restriction.**  The restriction of the value at `σ` has the
defining property of the value at the restriction of `σ`, so the two agree. -/
lemma appValue_map (hH : TopCat.Presheaf.IsSheaf H) {W W' : Opens Z} (j : W' ⟶ W)
    (σ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W)) :
    H.map j.op (appValue f φ hH σ) =
      appValue f φ hH ((sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map j.op σ) := by
  refine appValue_unique f φ hH ?_
  intro W₀ i V₀ hV₀ s₀ he
  have he' : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map (i ≫ j).op σ =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) hV₀ s₀ := by
    exact (map_op_map_op_apply (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf j i _
      σ).symm.trans he
  calc H.map i.op (H.map j.op (appValue f φ hH σ))
      = H.map (i ≫ j).op (appValue f φ hH σ) := by
        exact map_op_map_op_apply H _ _ _ _
    _ = localValue f φ hV₀ s₀ := appValue_spec f φ hH σ (i ≫ j) hV₀ s₀ he'

/-- `appValue` sends the zero section to zero. -/
lemma appValue_zero (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z} :
    appValue f φ hH
        (0 : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W)) = 0 := by
  rw [zero_eq_ofSection f (fun _ ↦ Set.mem_univ _), appValue_ofSection, localValue_zero]

/-- **`appValue` is additive.**  Near any point both sections are germwise pullbacks, their sum is
the germwise pullback of `resAdd` of the two generating sections (`ofSection_add_eq`), and the
local value of a `resAdd` is the sum of the local values (`localValue_resAdd`).  The three values
therefore agree after restriction to a covering of `W`, and `H` is a sheaf. -/
lemma appValue_add (hH : TopCat.Presheaf.IsSheaf H) {W : Opens Z}
    (σ τ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W)) :
    appValue f φ hH (σ + τ) = appValue f φ hH σ + appValue f φ hH τ := by
  classical
  choose A hmemA iA VA hVA sA hresA using fun z : W ↦ exists_map_eq_ofSection f σ z.2
  choose B hmemB iB VB hVB sB hresB using fun z : W ↦ exists_map_eq_ofSection f τ z.2
  set C : W → Opens Z := fun z ↦ A z ⊓ B z with hC
  have hjA : ∀ z : W, C z ⟶ A z := fun z ↦ homOfLE inf_le_left
  have hjB : ∀ z : W, C z ⟶ B z := fun z ↦ homOfLE inf_le_right
  have hiC : ∀ z : W, C z ⟶ W := fun z ↦ hjA z ≫ iA z
  have hcover : W ≤ iSup C := fun x hx ↦ Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmemA ⟨x, hx⟩, hmemB ⟨x, hx⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨H, hH⟩ : Z.Sheaf AddCommGrpCat.{u}) C W hiC hcover
    _ _ fun z ↦ ?_
  have hrA : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map (hiC z).op σ =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) (fun x ↦ hVA z (hjA z x)) (sA z) := by
    exact map_comp_ofSection f σ (iA z) (hjA z) _ (hresA z)
  have hrB : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map (hiC z).op τ =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢) (fun x ↦ hVB z (hjB z x)) (sB z) := by
    exact map_comp_ofSection f τ (iB z) (hjB z) _ (hresB z)
  have hsum : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map (hiC z).op (σ + τ) =
      ofSection.{u, u} (𝒢 := typePresheaf 𝒢)
        (fun x ↦ (⟨hVA z (hjA z x), hVB z (hjB z x)⟩ :
          (ConcreteCategory.hom f) x.1 ∈ VA z ⊓ VB z)) (resAdd 𝒢 (sA z) (sB z)) := by
    rw [presheafMap_add, hrA, hrB]
    exact ofSection_add_eq f (fun x ↦ hVA z (hjA z x)) (fun x ↦ hVB z (hjB z x)) _
      (sA z) (sB z)
  show H.map (hiC z).op (appValue f φ hH (σ + τ)) =
    H.map (hiC z).op (appValue f φ hH σ + appValue f φ hH τ)
  have eA : H.map (hiC z).op (appValue f φ hH σ) =
      localValue f φ (fun x ↦ hVA z (hjA z x)) (sA z) :=
    appValue_spec f φ hH σ (hiC z) _ (sA z) hrA
  have eB : H.map (hiC z).op (appValue f φ hH τ) =
      localValue f φ (fun x ↦ hVB z (hjB z x)) (sB z) :=
    appValue_spec f φ hH τ (hiC z) _ (sB z) hrB
  have eS : H.map (hiC z).op (appValue f φ hH (σ + τ)) =
      localValue f φ (fun x ↦ (⟨hVA z (hjA z x), hVB z (hjB z x)⟩ :
        (ConcreteCategory.hom f) x.1 ∈ VA z ⊓ VB z)) (resAdd 𝒢 (sA z) (sB z)) :=
    appValue_spec f φ hH (σ + τ) (hiC z) _ (resAdd 𝒢 (sA z) (sB z)) hsum
  rw [map_add, eA, eB, eS]
  exact localValue_resAdd f φ (fun x ↦ hVA z (hjA z x)) (fun x ↦ hVB z (hjB z x)) _
    (sA z) (sB z)

/-! #### The mapping-out morphism, and the universal property -/

/-- **The mapping-out morphism of the germ model.**  Given a sheaf `H` on `Z` and a map
`φ : 𝒢 ⟶ f _* H`, this is the morphism `f⁻¹𝒢 ⟶ H` of presheaves of abelian groups whose value at
a section `σ` is `appValue`: locally `σ` is the germwise pullback of a section `s` of `𝒢`, and
there the morphism must send it to the restriction of `φ s`. -/
def mapOut (hH : TopCat.Presheaf.IsSheaf H) :
    abelianPresheaf (ConcreteCategory.hom f) 𝒢 ⟶ H where
  app W := AddCommGrpCat.ofHom
    { toFun := fun σ ↦ appValue f φ hH σ
      map_zero' := appValue_zero f φ hH
      map_add' := appValue_add f φ hH }
  naturality {W W'} j := by
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
    exact (appValue_map f φ hH j.unop σ).symm

/-- The components of `mapOut` are `appValue`. -/
lemma mapOut_app_apply (hH : TopCat.Presheaf.IsSheaf H) (W : Opens Z)
    (σ : (sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.obj (op W)) :
    (mapOut f φ hH).app (op W) σ = appValue f φ hH σ :=
  rfl

/-- **A morphism out of the germ model is determined by its effect on germwise pullbacks.**  The
composite of the unit with `ψ` is `φ` exactly when `ψ` sends the germwise pullback of each
`s ∈ 𝒢(V)` over the whole of `f⁻¹V` to `φ_V s`. -/
lemma toPushforwardPresheaf_comp_eq_iff
    (ψ : abelianPresheaf (ConcreteCategory.hom f) 𝒢 ⟶ H) :
    (toPushforwardPresheaf f 𝒢 ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map ψ = φ) ↔
      ∀ (V : Opens Y) (s : 𝒢.obj (op V)),
        ψ.app (op ((Opens.map f).obj V))
            (ofSection (g := ConcreteCategory.hom f) (𝒢 := typePresheaf 𝒢)
              (W := (Opens.map f).obj V) (V := V) (fun z ↦ z.2) s) =
          φ.app (op V) s := by
  refine ⟨fun h V s ↦ ?_, fun h ↦ NatTrans.ext (funext fun V ↦
    ConcreteCategory.hom_ext _ _ fun s ↦ ?_)⟩
  · have := ConcreteCategory.congr_hom (NatTrans.congr_app h (op V)) s
    rwa [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  · induction V with
    | op V =>
      rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
      exact h V s

/-- **`mapOut` solves the mapping-out problem**: its composite with the unit is `φ`. -/
lemma toPushforwardPresheaf_comp_mapOut (hH : TopCat.Presheaf.IsSheaf H) :
    toPushforwardPresheaf f 𝒢 ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map (mapOut f φ hH) = φ :=
  (toPushforwardPresheaf_comp_eq_iff f φ _).2 fun V s ↦
    (appValue_ofSection f φ hH (W := (Opens.map f).obj V)
      (fun z : (Opens.map f).obj V ↦ z.2) s).trans (localValue_self f φ s)

/-- **`mapOut` is the only solution of the mapping-out problem.**  A morphism whose composite with
the unit is `φ` sends every germwise pullback to the corresponding local value, and by
`appValue_unique` that pins it down. -/
lemma mapOut_unique (hH : TopCat.Presheaf.IsSheaf H)
    {ψ : abelianPresheaf (ConcreteCategory.hom f) 𝒢 ⟶ H}
    (hψ : toPushforwardPresheaf f 𝒢 ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map ψ = φ) :
    ψ = mapOut f φ hH := by
  refine NatTrans.ext (funext fun W ↦ ConcreteCategory.hom_ext _ _ fun σ ↦ ?_)
  induction W with
  | op W =>
    refine appValue_unique f φ hH ?_
    intro W₀ i V₀ hV₀ s₀ he
    let k : W₀ ⟶ (Opens.map f).obj V₀ := homOfLE fun z hz ↦ hV₀ ⟨z, hz⟩
    calc H.map i.op (ψ.app (op W) σ)
        = ψ.app (op W₀) ((sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map i.op σ) :=
          (NatTrans.naturality_apply ψ i.op σ).symm
      _ = ψ.app (op W₀) ((sheaf (ConcreteCategory.hom f) (typePresheaf 𝒢)).presheaf.map k.op
            (ofSection.{u, u} (𝒢 := typePresheaf 𝒢) (fun z : (Opens.map f).obj V₀ ↦ z.2) s₀)) := by
          rw [he]
          exact congrArg _ (map_ofSection f k _ s₀).symm
      _ = H.map k.op (ψ.app (op ((Opens.map f).obj V₀))
            (ofSection.{u, u} (𝒢 := typePresheaf 𝒢) (fun z : (Opens.map f).obj V₀ ↦ z.2) s₀)) :=
          NatTrans.naturality_apply ψ k.op _
      _ = localValue f φ hV₀ s₀ := by
          rw [(toPushforwardPresheaf_comp_eq_iff f φ ψ).1 hψ V₀ s₀]
          rfl

/-- **The mapping-out half of the germ-model adjunction.**  For every sheaf of abelian groups `H`
on `Z` and every map `φ : 𝒢 ⟶ f _* H` there is a *unique* morphism `ψ : f⁻¹𝒢 ⟶ H` of presheaves
of abelian groups whose composite with the unit `toPushforwardPresheaf` is `φ`.

Together with `toPushforwardPresheaf` this is the universal property of the germ model: `f⁻¹𝒢` is
the inverse image of `𝒢`, corepresented on sheaves.  It is what makes
`SheafedSpaceLimit.existsUnique_pull_eq` consumable for the germ-model pullback system of
`DescendOpensAbelian`, whose arrows are phrased with Mathlib's pushforward.

Existence needs `H` to be a sheaf: the value at a section is *glued* from the local values. -/
@[ega "0 3.5.3" "partial, special case"]
theorem existsUnique_mapOut (hH : TopCat.Presheaf.IsSheaf H) :
    ∃! ψ : abelianPresheaf (ConcreteCategory.hom f) 𝒢 ⟶ H,
      toPushforwardPresheaf f 𝒢 ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map ψ = φ :=
  ⟨mapOut f φ hH, toPushforwardPresheaf_comp_mapOut f φ hH,
    fun _ hψ ↦ mapOut_unique f φ hH hψ⟩

end MappingOut

end GermPullback

end
