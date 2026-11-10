module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproductSheaf
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

/-!
# Coproducts of sheaves of sets are disjoint

Let `(C, J)` be a site and let a family of sheaves of sets `F i` have a coproduct `P` in
`Sheaf J (Type v)`, presented by a colimit cocone `ι i : F i ⟶ P`. This file proves, for a
site carrying a *clopen classifier*, that the legs `ι i` are monomorphisms and that legs with
distinct indices have disjoint images; it also proves, for an arbitrary site, that the legs
are jointly locally surjective.

A clopen classifier is an object `U` together with a morphism `l : L ⟶ U` and two global
sections `a : ⊤ ⟶ L` and `r : ⊤ ⟶ U` such that the fibre of the constant morphism
`W ⟶ ⊤ ⟶ U` given by `r` along `l` is covered by the empty sieve for every `W`. On the big
fppf site of a scheme one takes `U = ⊤ ⊔ ⊤`, `L = ⊤`, `l = coprod.inl`, `a = 𝟙` and
`r = coprod.inr`; the fibre in question is then the empty scheme. Sections of `U` over `W`
are the decompositions of `W` into two complementary clopen pieces, whence the name.

## Main definitions

* `CategoryTheory.Presheaf.adjoinPoint`: the presheaf `A` with a disjoint point adjoined,
  relative to `l : L ⟶ U`, namely `Z ↦ Σ (c : Z ⟶ U), A (Z ×_U L)`. For the clopen classifier
  `⊤ ⊔ ⊤` this is the sheaf `A ⊔ ⊤`. It is defined as
  `CategoryTheory.OverShriek.presheaf` of the restriction of `A` along the fibre functor
  `Over U ⥤ C`, so that its restriction maps come for free.
* `CategoryTheory.Presheaf.toAdjoinPoint`: the inclusion `A ⟶ adjoinPoint l A`.
* `CategoryTheory.Presheaf.constToYoneda`: the constant morphism from a presheaf to a
  representable presheaf given by a global section of the representing object.
* `CategoryTheory.OverShriek.transportSection`: a section of a presheaf on `Over U` over
  `Over.mk φ`, read as a section over an object whose structure morphism is `φ`.

## Main results

* `CategoryTheory.Presheaf.isSheaf_adjoinPoint`,
  `CategoryTheory.Presheaf.injective_toAdjoinPoint_app` and
  `CategoryTheory.Presheaf.nonempty_hom_adjoinPoint`: `adjoinPoint l A` is a sheaf, contains
  `A` as a subobject, and receives a morphism from every presheaf.
* `CategoryTheory.Sheaf.mono_cofan_inj`: **the legs of a coproduct cocone of sheaves of sets
  are monomorphisms**, for a site with a clopen classifier.
* `CategoryTheory.Sheaf.isColimitCofanOfCompUliftFunctor`: a cofan of sheaves of `Type t` whose
  universe lift is a coproduct cocone of sheaves of `Type (max w t)` is itself a coproduct
  cocone. This is how a statement about sheaves of a value universe above the site's own is
  deduced from the statement about sheaves of `Type t` when the latter category is not known to
  have coproducts.
* `CategoryTheory.Sheaf.terminal_comp_eq_of_ne`: legs with distinct indices have disjoint
  images.
* `CategoryTheory.Sheaf.sheafify_iSup_range_eq_top`,
  `CategoryTheory.Sheaf.sieveOfSection_iSup_range_mem`,
  `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_of_range_le` and
  `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_hom`: the legs are jointly locally
  surjective, on an arbitrary site.
* `CategoryTheory.Limits.mono_cofan_inj_of_mono` and
  `CategoryTheory.Limits.isIso_of_isColimit_cofan_fac`: the two formal consequences of a
  colimit cofan that the above arguments run on, valid in any category.

## Implementation notes

The usual proof that a coproduct of sheaves is disjoint sheafifies the pointwise coproduct of
presheaves and uses left exactness of sheafification. That is unavailable here: the intended
application is the big fppf site of a scheme, whose objects live one universe above its
morphisms, so the plus construction does not act on its category of `Type v`-valued
presheaves and the category of sheaves is not known to be a Grothendieck topos. Only the
abstract colimit cocone is available.

What replaces it is the topos-theoretic argument run by hand. To see that `ι i₀` is a
monomorphism it is enough to exhibit *some* cocone on the family whose `i₀`-th leg is a
monomorphism, by `CategoryTheory.Limits.mono_cofan_inj_of_mono`; the vertex of that cocone
must then be a sheaf containing `F i₀` as a subobject and carrying a global section, and the
smallest such is `F i₀ ⊔ ⊤`. That sheaf is `adjoinPoint`, built explicitly rather than as a
coproduct, so that its inclusion of `F i₀` is visibly injective. Its restriction maps are
inherited from the coproduct presheaf of Stacks 03CD already in the repository, which is what
makes the dependent sum over `c : Z ⟶ U` manageable; the sheaf condition for it is
`CategoryTheory.OverShriek.isSheaf_presheaf`, which glues the morphisms `c` in the
representable sheaf `h_U` and then the sections in `G` over the corresponding covering sieve
of `Over.mk c`.

The section-transport lemmas `CategoryTheory.OverShriek.transportSection` and
`CategoryTheory.OverShriek.map_op_transportSection` express a section of `G` over `Over.mk φ`
as a section over any object of `C/U` whose structure morphism is `φ`, which is the
bookkeeping that comparing the restriction maps of the coproduct presheaf with those of `G`
requires.

Joint local surjectivity needs no classifier and no sheafification either: the subsheaf of
the vertex generated by the images of the legs is formed by `CategoryTheory.Subfunctor.sheafify`,
which is the local closure of a subpresheaf inside a sheaf, and the universal property of the
coproduct splits its inclusion.

## References

* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 0F15](https://stacks.math.columbia.edu/tag/0F15)
* [Stacks Project, Tag 03CD](https://stacks.math.columbia.edu/tag/03CD)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe w t s v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U : C} (G : (Over U)ᵒᵖ ⥤ Type v)

/-- The morphism `Z ⟶ Over.mk φ` of `C/U` with identity underlying morphism, available
whenever `φ` is the structure morphism of `Z`. -/
def transportHom {Z : Over U} {φ : Z.left ⟶ U} (h : φ = Z.hom) : Z ⟶ Over.mk φ :=
  Over.homMk (𝟙 Z.left) (by simpa using h)

/-- The underlying morphism in `C` of `transportHom h` is the identity of `Z.left`. -/
@[simp]
lemma transportHom_left {Z : Over U} {φ : Z.left ⟶ U} (h : φ = Z.hom) :
    (transportHom (U := U) h).left = 𝟙 Z.left := rfl

/-- A section of `G` over `Over.mk φ`, read as a section over `Z` when `φ` is the structure
morphism of `Z`. -/
def transportSection {Z : Over U} {φ : Z.left ⟶ U} (h : φ = Z.hom)
    (s : G.obj (op (Over.mk φ))) : G.obj (op Z) :=
  G.map (transportHom h).op s

/-- Transporting along the identity does nothing. -/
lemma transportSection_mk {Y : C} {φ : Y ⟶ U} (h : φ = (Over.mk φ).hom)
    (s : G.obj (op (Over.mk φ))) : transportSection G h s = s := by
  change G.map (transportHom h).op s = s
  rw [show transportHom (U := U) h = 𝟙 (Over.mk φ) from Over.OverMorphism.ext (by simp)]
  simp

/-- The restriction maps of the coproduct presheaf, in applied form. -/
lemma presheaf_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (p : (presheaf G).obj X) :
    (presheaf G).map f p
      = ⟨f.unop ≫ p.1, G.map (Over.homMk f.unop rfl :
          Over.mk (f.unop ≫ p.1) ⟶ Over.mk p.1).op p.2⟩ :=
  rfl

/-- Two sections of `G` obtained by restricting the two components of one equality of pairs
along two morphisms with the same underlying morphism of `C` agree. -/
lemma map_op_eq_of_sigma_eq {Z : Over U}
    {p q : Σ φ : Z.left ⟶ U, G.obj (op (Over.mk φ))} (h : p = q)
    (e : Z ⟶ Over.mk p.1) (e' : Z ⟶ Over.mk q.1) (he : e.left = e'.left) :
    G.map e.op p.2 = G.map e'.op q.2 := by
  subst h
  rw [Over.OverMorphism.ext he]

/-- Transported sections of `G` depend only on the pair, not on its presentation. -/
lemma transportSection_congr {Z : Over U}
    {p q : Σ φ : Z.left ⟶ U, G.obj (op (Over.mk φ))} (h : p = q)
    (hp : p.1 = Z.hom) (hq : q.1 = Z.hom) :
    transportSection G hp p.2 = transportSection G hq q.2 :=
  map_op_eq_of_sigma_eq G h _ _ (by simp)

/-- Restriction along a morphism of `C/U` commutes with transport of sections. -/
lemma map_op_transportSection {Z Z' : Over U} (g : Z ⟶ Z') {φ : Z'.left ⟶ U} (h : φ = Z'.hom)
    (s : G.obj (op (Over.mk φ))) :
    G.map g.op (transportSection G h s)
      = transportSection G (show g.left ≫ φ = Z.hom by rw [h]; exact Over.w g)
          (G.map (Over.homMk g.left rfl : Over.mk (g.left ≫ φ) ⟶ Over.mk φ).op s) := by
  change G.map g.op (G.map (transportHom h).op s) = G.map (transportHom _).op _
  rw [map_op_comp, map_op_comp]
  exact congrArg (fun e : Z ⟶ Over.mk φ => G.map e.op s) (Over.OverMorphism.ext (by simp))

end CategoryTheory.OverShriek

namespace CategoryTheory

/-! ### Two formal consequences of a colimit cofan -/

section Formal

variable {D : Type*} [Category* D] {I : Type*} {F : I → D} {P : D} {ι : ∀ i, F i ⟶ P}

/-- The defining factorization of the morphism induced by a colimit cofan, with the cofan
spelled as `Cofan.mk`. -/
lemma Limits.comp_cofan_isColimit_desc (hP : Limits.IsColimit (Limits.Cofan.mk P ι))
    {Y : D} (κ : ∀ i, F i ⟶ Y) (i : I) :
    ι i ≫ Limits.Cofan.IsColimit.desc hP κ = κ i := by
  have h := Limits.Cofan.IsColimit.fac hP κ i
  rwa [Limits.cofan_mk_inj] at h

/-- If a colimit cofan admits *any* cocone whose `i₀`-th leg is a monomorphism, then the
`i₀`-th leg of the cofan is itself a monomorphism. -/
lemma Limits.mono_cofan_inj_of_mono (hP : Limits.IsColimit (Limits.Cofan.mk P ι))
    {Y : D} (κ : ∀ i, F i ⟶ Y) (i₀ : I) [Mono (κ i₀)] : Mono (ι i₀) :=
  mono_of_mono_fac (Limits.comp_cofan_isColimit_desc hP κ i₀)

/-- A subobject of the vertex of a colimit cofan through which every leg of the cofan factors
is the whole vertex. This is the usable form of "the legs of a coproduct cocone are jointly
epimorphic". -/
lemma Limits.isIso_of_isColimit_cofan_fac (hP : Limits.IsColimit (Limits.Cofan.mk P ι))
    {Z : D} (m : Z ⟶ P) [Mono m] (κ : ∀ i, F i ⟶ Z) (hκ : ∀ i, κ i ≫ m = ι i) : IsIso m := by
  have hfac : ∀ i, ι i ≫ Limits.Cofan.IsColimit.desc hP κ = κ i :=
    Limits.comp_cofan_isColimit_desc hP κ
  have hdm : Limits.Cofan.IsColimit.desc hP κ ≫ m = 𝟙 P := by
    refine Limits.Cofan.IsColimit.hom_ext hP _ _ fun i => ?_
    rw [Limits.cofan_mk_inj, ← Category.assoc, hfac, hκ, Category.comp_id (ι i)]
  refine ⟨Limits.Cofan.IsColimit.desc hP κ, ?_, hdm⟩
  rw [← cancel_mono m, Category.assoc, hdm, Category.comp_id, Category.id_comp]

end Formal

/-! ### A sheaf is a singleton on an object covered by the empty sieve -/

section Empty

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {A : Cᵒᵖ ⥤ Type v}

/-- The empty family of elements over the empty sieve. -/
private def botFamily (Z : C) : Presieve.FamilyOfElements A (⊥ : Sieve Z).arrows :=
  fun _ _ hf => hf.elim

private lemma botFamily_compatible (Z : C) : (botFamily (A := A) Z).Compatible := by
  intro _ _ _ _ _ _ _ h₁ _ _
  exact h₁.elim

private lemma botFamily_isAmalgamation {Z : C} (t : A.obj (op Z)) :
    (botFamily (A := A) Z).IsAmalgamation t := by
  intro _ _ hf
  exact hf.elim

/-- A sheaf is nonempty on any object whose empty sieve is covering. -/
lemma Presieve.IsSheaf.nonempty_obj_of_bot_mem (hA : Presieve.IsSheaf J A) {Z : C}
    (hZ : (⊥ : Sieve Z) ∈ J Z) : Nonempty (A.obj (op Z)) :=
  ⟨(hA ⊥ hZ (botFamily Z) (botFamily_compatible Z)).choose⟩

/-- A sheaf is a subsingleton on any object whose empty sieve is covering. Together with
`CategoryTheory.Presieve.IsSheaf.nonempty_obj_of_bot_mem`, a sheaf is a singleton there. -/
lemma Presieve.IsSheaf.subsingleton_obj_of_bot_mem (hA : Presieve.IsSheaf J A) {Z : C}
    (hZ : (⊥ : Sieve Z) ∈ J Z) : Subsingleton (A.obj (op Z)) := by
  obtain ⟨t, -, hu⟩ := hA ⊥ hZ (botFamily Z) (botFamily_compatible Z)
  exact ⟨fun p q => (hu p (botFamily_isAmalgamation p)).trans
    (hu q (botFamily_isAmalgamation q)).symm⟩

end Empty

/-! ### The legs of a coproduct cocone of sheaves are jointly locally surjective -/

section JointlySurjective

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **The legs of a coproduct cocone of sheaves of sets are jointly locally surjective.**
The subsheaf of the vertex generated by the images of the legs is the whole vertex: it is a
sheaf through which every leg factors, so the universal property of the coproduct splits its
inclusion, which is therefore an isomorphism. -/
theorem Sheaf.sheafify_iSup_range_eq_top {I : Type*} {F : I → Sheaf J (Type v)}
    {P : Sheaf J (Type v)} (ι : ∀ i, F i ⟶ P)
    (hP : Limits.IsColimit (Limits.Cofan.mk P ι)) :
    (⨆ i, Subfunctor.range (ι i).hom).sheafify J = ⊤ := by
  have hP' : Presieve.IsSheaf J P.obj := (isSheaf_iff_isSheaf_of_type J _).1 P.property
  let R : Subfunctor P.obj := ⨆ i, Subfunctor.range (ι i).hom
  let Z : Sheaf J (Type v) := ⟨(R.sheafify J).toFunctor,
    (isSheaf_iff_isSheaf_of_type J _).2 (Subfunctor.sheafify_isSheaf (G := R) hP')⟩
  let m : Z ⟶ P := ObjectProperty.homMk (R.sheafify J).ι
  have hm : Mono m := Sheaf.mono_of_injective m fun _ => Subtype.val_injective
  let κ : ∀ i, F i ⟶ Z := fun i => ObjectProperty.homMk
    (Subfunctor.lift (ι i).hom ((le_iSup _ i).trans (Subfunctor.le_sheafify J R)))
  have hκ : ∀ i, κ i ≫ m = ι i := fun _ => rfl
  have : IsIso m := Limits.isIso_of_isColimit_cofan_fac hP m κ hκ
  rw [Subfunctor.eq_top_iff_isIso]
  exact Functor.map_isIso (ObjectProperty.ι _) m

/-- Joint local surjectivity in the form a consumer uses: every section of the vertex lies,
after restriction along a covering sieve, in the image of one of the legs. -/
theorem Sheaf.sieveOfSection_iSup_range_mem {I : Type*} {F : I → Sheaf J (Type v)}
    {P : Sheaf J (Type v)} (ι : ∀ i, F i ⟶ P)
    (hP : Limits.IsColimit (Limits.Cofan.mk P ι)) (W : Cᵒᵖ) (x : P.obj.obj W) :
    (⨆ i, Subfunctor.range (ι i).hom).sieveOfSection x ∈ J W.unop := by
  have h := Sheaf.sheafify_iSup_range_eq_top J ι hP
  have hx : x ∈ ((⨆ i, Subfunctor.range (ι i).hom).sheafify J).obj W := by
    rw [h]; trivial
  exact hx

end JointlySurjective

/-! ### Joint local surjectivity through the presheaf coproduct -/

section SigmaDesc

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **The legs of a coproduct cocone of sheaves of sets are jointly locally surjective**, in
the form of local surjectivity of the morphism out of a *presheaf* coproduct of presheaves
whose ranges contain the ranges of the legs.

The range of that morphism contains the range of every leg, so its sheafification contains the
sheafification of the supremum of those ranges, which is everything by
`CategoryTheory.Sheaf.sheafify_iSup_range_eq_top`. -/
theorem Sheaf.isLocallySurjective_sigmaDesc_of_range_le {I : Type*} {F : I → Sheaf J (Type v)}
    {P : Sheaf J (Type v)} (ι : ∀ i, F i ⟶ P)
    (hP : Limits.IsColimit (Limits.Cofan.mk P ι)) {H : I → Cᵒᵖ ⥤ Type v}
    [Limits.HasCoproduct H] (g : ∀ i, H i ⟶ P.obj)
    (hg : ∀ i, Subfunctor.range (ι i).hom ≤ Subfunctor.range (g i)) :
    Presheaf.IsLocallySurjective J (Limits.Sigma.desc g) := by
  have hle : (⨆ i, Subfunctor.range (ι i).hom) ≤
      Subfunctor.range (Limits.Sigma.desc g) := by
    refine iSup_le fun i U x hx ↦ ?_
    obtain ⟨y, hy⟩ := hg i U hx
    refine ⟨(Limits.Sigma.ι H i).app U y, ?_⟩
    rw [show ((Limits.Sigma.desc g).app U) ((Limits.Sigma.ι H i).app U y) =
      ((Limits.Sigma.ι H i ≫ Limits.Sigma.desc g).app U) y from rfl, Limits.Sigma.ι_comp_desc]
    exact hy
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  refine top_le_iff.mp ?_
  rw [← Sheaf.sheafify_iSup_range_eq_top J ι hP]
  exact fun _ _ hx ↦ J.superset_covering (fun _ _ hf ↦ hle _ hf) hx

/-- **The legs of a coproduct cocone of sheaves of sets are jointly locally surjective**, in
the form of local surjectivity of the induced morphism out of the *presheaf* coproduct of the
summands. -/
theorem Sheaf.isLocallySurjective_sigmaDesc_hom {I : Type*} {F : I → Sheaf J (Type v)}
    {P : Sheaf J (Type v)} (ι : ∀ i, F i ⟶ P)
    [Limits.HasCoproduct fun i ↦ (F i).obj]
    (hP : Limits.IsColimit (Limits.Cofan.mk P ι)) :
    Presheaf.IsLocallySurjective J (Limits.Sigma.desc fun i ↦ (ι i).hom) :=
  Sheaf.isLocallySurjective_sigmaDesc_of_range_le J ι hP _ fun _ ↦ le_rfl

end SigmaDesc

/-! ### Adjoining a disjoint point to a sheaf -/

namespace Presheaf

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]

/-- The presheaf `A` with a disjoint point adjoined, relative to a subobject `l : L ⟶ U` of
a "clopen classifier" `U`: its sections over `Z` are pairs consisting of a morphism
`c : Z ⟶ U` and a section of `A` over the fibre `Z ×_U L`.

When `l` is one of the two inclusions of `U = ⊤ ⊔ ⊤` this is the sheaf `A ⊔ ⊤`, whose
sections over `Z` are a decomposition of `Z` into two complementary pieces together with a
section of `A` on the first piece. It is the smallest sheaf which contains `A` as a
subobject and has a global section, which is why it is formed here. -/
noncomputable def adjoinPoint {U L : C} (l : L ⟶ U) (A : Cᵒᵖ ⥤ Type v) : Cᵒᵖ ⥤ Type v :=
  OverShriek.presheaf ((Over.pullback l ⋙ Over.forget L).op ⋙ A)

variable {U L : C} (l : L ⟶ U) (A : Cᵒᵖ ⥤ Type v)

/-- A section of `adjoinPoint l A` over `Z` is a morphism `c : Z ⟶ U` together with a section
of `A` over the pullback `Z ×_U L` of `l` along `c`. -/
lemma adjoinPoint_obj (Z : Cᵒᵖ) :
    (adjoinPoint l A).obj Z = Σ c : Z.unop ⟶ U, A.obj (op (Limits.pullback c l)) :=
  rfl

/-- `adjoinPoint l A` is a sheaf as soon as `A` is one and the representable presheaf `h_U`
is one; the latter holds whenever `J` is subcanonical. -/
theorem isSheaf_adjoinPoint (J : GrothendieckTopology C)
    (hU : Presieve.IsSheaf J (yoneda.obj U)) (hA : Presieve.IsSheaf J A) :
    Presieve.IsSheaf J (adjoinPoint l A) := by
  have : (Over.pullback l ⋙ Over.forget L).IsContinuous (J.over U) J :=
    Functor.isContinuous_comp _ _ (J.over U) (J.over L) J
  exact OverShriek.isSheaf_presheaf J _ hU
    (Functor.op_comp_isSheaf_of_isSheaf_type _ (J.over U) hA)

section Aux

/-- Equality of two sections of a dependent sum whose first components agree. -/
private lemma sigma_snd_eq {α : Type*} {β : α → Type*} {c : α} {s t : β c}
    (h : (⟨c, s⟩ : Σ c, β c) = ⟨c, t⟩) : s = t := by simpa using h

/-- Equality of two sections of a dependent sum whose values lie in a subsingleton. -/
private lemma sigma_eq_of_subsingleton {α : Type*} {β : α → Type*} {c d : α} (h : c = d)
    (s : β c) (t : β d) (hsub : Subsingleton (β d)) :
    (⟨c, s⟩ : Σ c, β c) = ⟨d, t⟩ := by
  subst h
  exact congrArg (Sigma.mk c) (hsub.elim s t)

end Aux

section Terminal

variable [Limits.HasTerminal C]

/-- The inclusion of `A` into `adjoinPoint l A`, given a global section `a` of `L`: a section
of `A` over `Z` is sent to the pair consisting of the constant decomposition
`Z ⟶ ⊤ ⟶ L ⟶ U` and the section read on the corresponding fibre, which is all of `Z`. -/
noncomputable def toAdjoinPoint (a : ⊤_ C ⟶ L) : A ⟶ adjoinPoint l A where
  app Z := ↾fun s => ⟨Limits.terminal.from Z.unop ≫ a ≫ l,
    A.map (Limits.pullback.fst (Limits.terminal.from Z.unop ≫ a ≫ l) l).op s⟩
  naturality {Z Z'} g := by
    ext s
    have h2 : (⟨Limits.terminal.from Z'.unop ≫ a ≫ l,
          A.map (Limits.pullback.fst (Limits.terminal.from Z'.unop ≫ a ≫ l) l).op
            (A.map g s)⟩ :
        Σ c : Z'.unop ⟶ U,
          ((Over.pullback l ⋙ Over.forget L).op ⋙ A).obj (op (Over.mk c)))
        = ⟨Limits.terminal.from Z'.unop ≫ a ≫ l,
            ((Over.pullback l ⋙ Over.forget L).op ⋙ A).map
              (Over.homMk g.unop (by simp) :
                Over.mk (Limits.terminal.from Z'.unop ≫ a ≫ l) ⟶
                  Over.mk (Limits.terminal.from Z.unop ≫ a ≫ l)).op
              (A.map (Limits.pullback.fst
                (Limits.terminal.from Z.unop ≫ a ≫ l) l).op s)⟩ := by
      refine congrArg (Sigma.mk (Limits.terminal.from Z'.unop ≫ a ≫ l)) ?_
      change A.map _ (A.map _ s) = A.map _ (A.map _ s)
      simp only [← Functor.map_comp_apply]
      refine congrArg (fun f => A.map (Quiver.Hom.op f) s) ?_
      exact (Limits.pullback.lift_fst _ _ _).symm
    exact h2.trans (OverShriek.sigmaMk_eq ((Over.pullback l ⋙ Over.forget L).op ⋙ A)
      (A.map (Limits.pullback.fst (Limits.terminal.from Z.unop ≫ a ≫ l) l).op s)
      (Over.homMk g.unop rfl :
        Over.mk (g.unop ≫ (Limits.terminal.from Z.unop ≫ a ≫ l)) ⟶
          Over.mk (Limits.terminal.from Z.unop ≫ a ≫ l))
      (Over.homMk g.unop (by simp) :
        Over.mk (Limits.terminal.from Z'.unop ≫ a ≫ l) ⟶
          Over.mk (Limits.terminal.from Z.unop ≫ a ≫ l)) rfl).symm

/-- The component of `toAdjoinPoint l A a` at `Z` sends `s` to the constant morphism
`Z ⟶ ⊤_ C ⟶ L ⟶ U`, paired with the restriction of `s` along the first projection of the
pullback. -/
lemma toAdjoinPoint_app_apply (a : ⊤_ C ⟶ L) (Z : Cᵒᵖ) (s : A.obj Z) :
    (toAdjoinPoint l A a).app Z s
      = ⟨Limits.terminal.from Z.unop ≫ a ≫ l,
          A.map (Limits.pullback.fst (Limits.terminal.from Z.unop ≫ a ≫ l) l).op s⟩ :=
  rfl

/-- Every component of `toAdjoinPoint` is injective: the fibre of the constant decomposition
is the whole object, so restricting a section to it loses no information. -/
lemma injective_toAdjoinPoint_app (a : ⊤_ C ⟶ L) (Z : Cᵒᵖ) :
    Function.Injective (ConcreteCategory.hom ((toAdjoinPoint l A a).app Z)) := by
  have hsec : (Limits.pullback.lift (𝟙 Z.unop) (Limits.terminal.from Z.unop ≫ a)
        (by simp) : Z.unop ⟶ Limits.pullback (Limits.terminal.from Z.unop ≫ a ≫ l) l) ≫
      Limits.pullback.fst (Limits.terminal.from Z.unop ≫ a ≫ l) l = 𝟙 Z.unop :=
    Limits.pullback.lift_fst _ _ _
  have key : ∀ x : A.obj Z, A.map (Limits.pullback.lift (𝟙 Z.unop)
      (Limits.terminal.from Z.unop ≫ a) (by simp)).op
      (A.map (Limits.pullback.fst (Limits.terminal.from Z.unop ≫ a ≫ l) l).op x) = x := by
    intro x
    rw [← A.map_comp_apply, ← op_comp, hsec, op_id, A.map_id_apply]
  intro s t hst
  have h2 : (⟨Limits.terminal.from Z.unop ≫ a ≫ l,
        A.map (Limits.pullback.fst (Limits.terminal.from Z.unop ≫ a ≫ l) l).op s⟩ :
      Σ c : Z.unop ⟶ U, A.obj (op (Limits.pullback c l)))
      = ⟨Limits.terminal.from Z.unop ≫ a ≫ l,
          A.map (Limits.pullback.fst (Limits.terminal.from Z.unop ≫ a ≫ l) l).op t⟩ := hst
  rw [← key s, ← key t, sigma_snd_eq h2]

/-- Any presheaf maps to `adjoinPoint l A`, by the constant "point" map, as soon as `A` takes
a singleton value on the fibre of the constant decomposition `Z ⟶ ⊤ ⟶ U` for every `Z`.

This is the reason `adjoinPoint` is formed: it provides the leg of a cocone out of every
member of a family, so that the universal property of a coproduct can be applied. -/
lemma nonempty_hom_adjoinPoint (r : ⊤_ C ⟶ U)
    (hne : ∀ W : C, Nonempty (A.obj (op (Limits.pullback (Limits.terminal.from W ≫ r) l))))
    (hsub : ∀ W : C, Subsingleton (A.obj (op (Limits.pullback
      (Limits.terminal.from W ≫ r) l))))
    (B : Cᵒᵖ ⥤ Type v) : Nonempty (B ⟶ adjoinPoint l A) := by
  refine ⟨{ app := fun Z => ↾fun _ => ⟨Limits.terminal.from Z.unop ≫ r,
    (hne Z.unop).some⟩, naturality := ?_ }⟩
  intro Z Z' g
  ext b
  refine Eq.trans ?_ (OverShriek.sigmaMk_eq ((Over.pullback l ⋙ Over.forget L).op ⋙ A)
    (hne Z.unop).some
    (Over.homMk g.unop rfl :
      Over.mk (g.unop ≫ (Limits.terminal.from Z.unop ≫ r)) ⟶
        Over.mk (Limits.terminal.from Z.unop ≫ r))
    (Over.homMk g.unop (by simp) :
      Over.mk (Limits.terminal.from Z'.unop ≫ r) ⟶
        Over.mk (Limits.terminal.from Z.unop ≫ r)) rfl).symm
  exact congrArg (Sigma.mk (Limits.terminal.from Z'.unop ≫ r))
    ((hsub Z'.unop).elim _ _)

end Terminal

end Presheaf

/-! ### Distinct legs of a coproduct of sheaves have disjoint images -/

section Disjoint

variable {C : Type u} [Category.{v} C] [Limits.HasTerminal C] (J : GrothendieckTopology C)

/-- The constant morphism from a presheaf to a representable presheaf determined by a global
section of the representing object. -/
noncomputable def Presheaf.constToYoneda (B : Cᵒᵖ ⥤ Type v) {U : C} (c : ⊤_ C ⟶ U) :
    B ⟶ yoneda.obj U where
  app Z := ↾fun _ => Limits.terminal.from Z.unop ≫ c
  naturality {Z Z'} g := by
    ext b
    simp

/-- The component of `Presheaf.constToYoneda B c` at `Z` sends every section to the composite
of the unique morphism `Z ⟶ ⊤_ C` with `c`. -/
@[simp]
lemma Presheaf.constToYoneda_app_apply (B : Cᵒᵖ ⥤ Type v) {U : C} (c : ⊤_ C ⟶ U) (Z : Cᵒᵖ)
    (b : B.obj Z) :
    (Presheaf.constToYoneda B c).app Z b = Limits.terminal.from Z.unop ≫ c :=
  rfl

/-- **Distinct legs of a coproduct cocone of sheaves of sets have disjoint images.** If a
section of `F i` and a section of `F j` over the same object `W` have the same image in the
vertex, and `i ≠ j`, then the two global sections `a ≫ l` and `r` of `U` already become equal
after pullback to `W`.

On the big fppf site over `S`, with `U = ⊤ ⊔ ⊤`, `a ≫ l = coprod.inl` and `r = coprod.inr`,
this says that `W` has no points, which is the disjointness half of Stacks 02WO. -/
theorem Sheaf.terminal_comp_eq_of_ne {U L : C} (l : L ⟶ U) (a : ⊤_ C ⟶ L) (r : ⊤_ C ⟶ U)
    (hU : Presieve.IsSheaf J (yoneda.obj U))
    {I : Type*} {F : I → Sheaf J (Type v)} {P : Sheaf J (Type v)} (ι : ∀ i, F i ⟶ P)
    (hP : Limits.IsColimit (Limits.Cofan.mk P ι)) {i j : I} (hij : i ≠ j) {W : C}
    (x : (F i).obj.obj (op W)) (y : (F j).obj.obj (op W))
    (h : (ι i).hom.app (op W) x = (ι j).hom.app (op W) y) :
    Limits.terminal.from W ≫ a ≫ l = Limits.terminal.from W ≫ r := by
  classical
  let Y : Sheaf J (Type v) := ⟨yoneda.obj U, (isSheaf_iff_isSheaf_of_type J _).2 hU⟩
  let κ : ∀ k, F k ⟶ Y := fun k => ObjectProperty.homMk
    (Presheaf.constToYoneda (F k).obj (if k = j then r else a ≫ l))
  have key : ∀ (k : I) (z : (F k).obj.obj (op W)),
      (Limits.Cofan.IsColimit.desc hP κ).hom.app (op W) ((ι k).hom.app (op W) z)
        = Limits.terminal.from W ≫ (if k = j then r else a ≫ l) :=
    fun k z => congrArg (fun m : F k ⟶ Y => m.hom.app (op W) z)
      (Limits.comp_cofan_isColimit_desc hP κ k)
  have hi := key i x
  have hj := key j y
  rw [show (if i = j then r else a ≫ l) = a ≫ l from by simp [hij]] at hi
  rw [show (if j = j then r else a ≫ l) = r from by simp] at hj
  rw [← hi, h, hj]

end Disjoint

/-! ### Disjointness of coproducts of sheaves of sets -/

section Coproduct

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C] [Limits.HasTerminal C]
  (J : GrothendieckTopology C)

/-- **The legs of a coproduct cocone of sheaves of sets are monomorphisms**, provided the
site carries a *clopen classifier*: an
object `U` with a morphism `l : L ⟶ U`, a global section `a : ⊤ ⟶ L`, and a second global
section `r : ⊤ ⟶ U` disjoint from `l`, in the sense that the fibre of the constant morphism
`W ⟶ ⊤ ⟶ U` given by `r` along `l` is covered by the empty sieve for every `W`. The
representable presheaf on `U` must also be a sheaf, which holds whenever `J` is subcanonical.

On the big fppf site over `S` one takes `U = ⊤ ⊔ ⊤`, `L = ⊤`, `l = coprod.inl`,
`a = 𝟙`, `r = coprod.inr`; the fibre in question is then the empty scheme.

The proof is the standard topos-theoretic one, made available by the explicit construction
`CategoryTheory.Presheaf.adjoinPoint`: the sheaf `A ⊔ ⊤` obtained from `A = F i₀` by
adjoining a disjoint point receives `F i₀` by a monomorphism and receives every other
member of the family through its point, so it is the vertex of a cocone whose `i₀`-th leg is
a monomorphism; the universal property of the coproduct then forces `ι i₀` to be one. -/
@[sga "4 II 4.5.1" "partial"]
theorem Sheaf.mono_cofan_inj {U L : C} (l : L ⟶ U) (a : ⊤_ C ⟶ L) (r : ⊤_ C ⟶ U)
    (hU : Presieve.IsSheaf J (yoneda.obj U))
    (hbot : ∀ W : C, (⊥ : Sieve (Limits.pullback (Limits.terminal.from W ≫ r) l))
      ∈ J (Limits.pullback (Limits.terminal.from W ≫ r) l))
    {I : Type*} {F : I → Sheaf J (Type v)} {P : Sheaf J (Type v)} (ι : ∀ i, F i ⟶ P)
    (hP : Limits.IsColimit (Limits.Cofan.mk P ι)) (i₀ : I) : Mono (ι i₀) := by
  classical
  have hA : Presieve.IsSheaf J (F i₀).obj :=
    (isSheaf_iff_isSheaf_of_type J _).1 (F i₀).property
  let Y : Sheaf J (Type v) := ⟨Presheaf.adjoinPoint l (F i₀).obj,
    (isSheaf_iff_isSheaf_of_type J _).2 (Presheaf.isSheaf_adjoinPoint l _ J hU hA)⟩
  let m : F i₀ ⟶ Y := ObjectProperty.homMk (Presheaf.toAdjoinPoint l (F i₀).obj a)
  have hm : Mono m := Sheaf.mono_of_injective m
    (fun X => Presheaf.injective_toAdjoinPoint_app l (F i₀).obj a X)
  have hleg : ∀ i, Nonempty (F i ⟶ Y) := fun i =>
    (Presheaf.nonempty_hom_adjoinPoint l (F i₀).obj r
      (fun W => hA.nonempty_obj_of_bot_mem J (hbot W))
      (fun W => hA.subsingleton_obj_of_bot_mem J (hbot W)) (F i).obj).map ObjectProperty.homMk
  have hκ : Function.update (fun i => (hleg i).some) i₀ m i₀ = m :=
    Function.update_self (β := fun i => F i ⟶ Y) i₀ m _
  have : Mono (Function.update (fun i => (hleg i).some) i₀ m i₀) := by rw [hκ]; exact hm
  exact Limits.mono_cofan_inj_of_mono hP (Function.update (fun i => (hleg i).some) i₀ m) i₀

end Coproduct

/-! ### Descent of a coproduct cocone along the universe lift of the values -/

section CompUliftFunctor

/-- **A cofan of sheaves of sets whose universe lift is a coproduct cocone is a coproduct
cocone.** The hypothesis is that the legs `ι' i` become, after composing with the universe lift
of the values and transporting along isomorphisms `eF i` and `eP` identifying those lifts with
given sheaves of `Type (max w t)`, the legs `ι i` of a coproduct cocone.

This is a transport of a universal property along the fully faithful functor
`CategoryTheory.uliftFunctor` whiskered into the presheaf category. It is what a statement about
sheaves of a value universe above the site's own is deduced from the corresponding statement
about sheaves of `Type t` with, when the category of sheaves of `Type t` is not known to have
coproducts at all -- as happens one universe below the objects of a big site, where the plus
construction is unavailable. No coproduct of sheaves of `Type t` is formed. -/
noncomputable def Sheaf.isColimitCofanOfCompUliftFunctor
    {C : Type*} [Category* C] {J : GrothendieckTopology C} {I : Type s}
    {F' : I → Sheaf J (Type t)} {P' : Sheaf J (Type t)} (ι' : ∀ i, F' i ⟶ P')
    {F : I → Sheaf J (Type (max w t))} {P : Sheaf J (Type (max w t))} (ι : ∀ i, F i ⟶ P)
    (hP : Limits.IsColimit (Limits.Cofan.mk P ι))
    (eF : ∀ i, (F' i).obj ⋙ uliftFunctor.{w} ≅ (F i).obj)
    (eP : P'.obj ⋙ uliftFunctor.{w} ≅ P.obj)
    (hcompat : ∀ (i : I) (T : Cᵒᵖ) (z : (F' i).obj.obj T),
      (ι i).hom.app T ((eF i).hom.app T (ULift.up z))
        = eP.hom.app T (ULift.up ((ι' i).hom.app T z))) :
    Limits.IsColimit (Limits.Cofan.mk P' ι') := by
  let H := (Functor.whiskeringRight Cᵒᵖ (Type t) (Type (max w t))).obj uliftFunctor.{w}
  have hmapι₀ : ∀ i, H.map (ι' i).hom ≫ eP.hom = (eF i).hom ≫ (ι i).hom := by
    intro i
    ext T z
    exact (hcompat i T z.down).symm
  have hmapι : ∀ i, H.map (ι' i).hom = (eF i).hom ≫ (ι i).hom ≫ eP.inv := fun i => by
    rw [← Category.assoc, ← hmapι₀ i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let lift : Sheaf J (Type t) → Sheaf J (Type (max w t)) := fun K =>
    ⟨H.obj K.obj, by
      rw [isSheaf_iff_isSheaf_of_type]
      exact (Presieve.isSheaf_comp_uliftFunctor_iff _).mpr
        ((isSheaf_iff_isSheaf_of_type J _).1 K.property)⟩
  let big : ∀ (c : Limits.Cofan F') (i : I), F i ⟶ lift c.pt := fun c i =>
    ObjectProperty.homMk ((eF i).inv ≫ H.map (c.inj i).hom)
  let desc : ∀ c : Limits.Cofan F', P' ⟶ c.pt := fun c =>
    ObjectProperty.homMk (H.preimage (eP.hom ≫ (Limits.Cofan.IsColimit.desc hP (big c)).hom))
  have hdescmap : ∀ c : Limits.Cofan F',
      H.map (desc c).hom = eP.hom ≫ (Limits.Cofan.IsColimit.desc hP (big c)).hom := fun c =>
    H.map_preimage _
  have hbig : ∀ (c : Limits.Cofan F') (i : I),
      (ι i).hom ≫ (Limits.Cofan.IsColimit.desc hP (big c)).hom =
        (eF i).inv ≫ H.map (c.inj i).hom := fun c i =>
    congrArg (fun k : F i ⟶ lift c.pt => k.hom) (Limits.Cofan.IsColimit.fac hP (big c) i)
  refine Limits.Cofan.IsColimit.mk _ desc (fun c i => ?_) (fun c m hm => ?_)
  · refine Sheaf.hom_ext ?_
    change (ι' i).hom ≫ (desc c).hom = (c.inj i).hom
    apply H.map_injective
    rw [Functor.map_comp, hmapι, hdescmap]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [hbig]
    simp
  · have hmi : ∀ i, (ι' i).hom ≫ m.hom = (c.inj i).hom := fun i =>
      congrArg (fun k : F' i ⟶ c.pt => k.hom) (hm i)
    have hψ : (ObjectProperty.homMk (eP.inv ≫ H.map m.hom) : P ⟶ lift c.pt)
        = Limits.Cofan.IsColimit.desc hP (big c) := by
      refine Limits.Cofan.IsColimit.hom_ext hP _ _ fun i => ?_
      refine Sheaf.hom_ext ?_
      change (ι i).hom ≫ eP.inv ≫ H.map m.hom =
        (ι i).hom ≫ (Limits.Cofan.IsColimit.desc hP (big c)).hom
      have h3 : (eF i).hom ≫ (ι i).hom ≫ eP.inv ≫ H.map m.hom =
          H.map (c.inj i).hom := by
        have h4 := congrArg H.map (hmi i)
        rw [Functor.map_comp, hmapι] at h4
        simpa only [Category.assoc] using h4
      rw [hbig, ← h3, Iso.inv_hom_id_assoc]
    refine Sheaf.hom_ext ?_
    change m.hom = (desc c).hom
    apply H.map_injective
    rw [hdescmap, ← congrArg (fun k : P ⟶ lift c.pt => k.hom) hψ]
    change _ = eP.hom ≫ eP.inv ≫ H.map m.hom
    rw [Iso.hom_inv_id_assoc]

end CompUliftFunctor

end CategoryTheory

end
