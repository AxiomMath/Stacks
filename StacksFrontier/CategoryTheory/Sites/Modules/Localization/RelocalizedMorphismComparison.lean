module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableMorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableRelocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.StructureSheafComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.RelocalizedMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Relocalizing a morphism of ringed sites and relocalizing its morphism of ringed topoi

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites given by a continuous functor
`u : D ⥤ C`, let `V` be an object of `D`, `U` an object of `C` and `c : U ⟶ u(V)` a morphism of
`C`. There are two relocalized morphisms over this data:

* Stacks 04J1 relocalizes the morphism of ringed *sites*, giving
  `(f_c, f_c♯) : (Sh(C/U), O_U) ⟶ (Sh(D/V), O'_V)` in a square with `j_U` and `j_V`;
* Stacks 04J8 relocalizes the morphism of ringed *topoi* at the sheaves `G = h_V^#` and
  `F = h_U^#`, along the map `s : h_U^# ⟶ f^{-1}h_V^#` that `c` induces, giving
  `(f_s, f_s♯) : (Sh(C)/F, O_F) ⟶ (Sh(D)/G, O'_G)` in a square with `j_F` and `j_G`.

Stacks 04J9 says that these two squares agree via the identifications of Stacks 04J3 of the
localization of a ringed site at an object with the localization of its ringed topos at the
associated sheaf. This file supplies the identification of the horizontal edges as a
2-isomorphism of ringed topoi, the map of sheaves `s` that `c` induces, and the assertion of
Stacks 04J9 about the two structure maps.

## Main definitions

* `AlgebraicGeometry.RingedSite.localizationTwoIso`: the identification of Stacks 04J3, read as
  a 2-isomorphism of ringed topoi `j_{h_U^#} ∘ ι_U ≅ j_U` between the two localization
  morphisms. This is the identification along which Stacks 04J9 compares the two squares.
* `AlgebraicGeometry.RingedSite.Hom.relocalizationSheafMap`: the morphism of sheaves
  `s : h_U^# ⟶ f^{-1}h_V^#` that `c : U ⟶ u(V)` induces, which is the datum Stacks 04J9 feeds
  to Stacks 04J8.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.relocalized_fSharpInverseImage_forget`: **Stacks 04J9** on
  structure maps. Each of the two relocalized morphisms has, in inverse-image form and on
  underlying sheaves of sets, the structure map of its own localized morphism `f'` restricted
  along its own relocalization; the relocalization itself contributes the identity on both
  sides. So the assertion of Stacks 04J9 about the structure maps is the assertion of Stacks
  04J7 about the structure maps of the two `f'`, which is
  `AlgebraicGeometry.RingedSite.Hom.localizedRepresentable_forgetFSharp`.

## Implementation notes

The identification of Stacks 04J3 is formalized as three separate comparisons — of the two topoi,
of their inverse images and of their structure maps. `localizationTwoIso` assembles them into
the single 2-isomorphism of ringed topoi that a statement about commuting squares of ringed
topoi needs: `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` turns the comparison
of inverse images `AlgebraicGeometry.RingedSite.representableLocalizationInverseImageIso`,
together with the compatibility of the structure maps
`AlgebraicGeometry.RingedSite.representableLocalizationMorphism_compare`, into a 2-isomorphism
of the direct images. The two presentations of the localization morphism of a ringed site —
`localizationRingedToposHom` of Stacks 04IY's file and `localizationCommRingedToposHom` of
Stacks 04J3's file — are the same record, so the 2-isomorphism may be read at either.

**The relocalization contributes nothing to the structure map.** On underlying sheaves of sets
and in inverse-image form, the structure map of a relocalization is the identity — of the
ringed site by
`AlgebraicGeometry.RingedSite.forgetRing_relocalizationRingedToposHom_fSharpInverseImage`, of
the ringed topos by
`AlgebraicGeometry.RingedToposHom.forgetRing_relocalizationMorphism_fSharpInverseImage` — and
the structure map of a composite is the restriction of the first factor's followed by the
second factor's. That is the whole proof of
`Hom.relocalized_fSharpInverseImage_forget`, and it is the reason Stacks 04J9's assertion about
structure maps is Stacks 04J7's.

**What is not carried, and why.** Stacks 04J9 also asserts that the two commuting *squares*
agree, which is a 2-isomorphism `ι_V ∘ f_c ≅ f_s ∘ ι_U` compatible with the square of Stacks
04J1 and the square of Stacks 04J8. Two things stand between the formalized forms of the cited
lemmas and that statement.

* Stacks 04J5 is formalized
  (`AlgebraicGeometry.RingedSite.representableRelocalizationInverseImageIso`) against the
  localization of `(Sh(C)/h_{u(V)}^#, O_{h_{u(V)}^#})` at the *object* `h_U^#/h_{u(V)}^#`,
  whereas Stacks 04J8 relocalizes along the *morphism of sheaves* `h_U^# ⟶ h_{u(V)}^#` using
  Stacks 04J4's `AlgebraicGeometry.RingedTopos.relocalizationMorphism`. Identifying the two
  presentations is the half of Stacks 04J4 that this repository does not carry: the inverse
  image of a relocalization along `a : H ⟶ K`, read through Stacks 04IE's identifications of
  the two localizations with their slice topoi, is base change along `a`, i.e. an isomorphism
  `(RingedTopos.localizationEquivalence X K).functor ⋙ Over.pullback a ≅
  (X.relocalizationMorphismOfTopoi a).inverseImage ⋙ (RingedTopos.localizationEquivalence X
  H).functor`. See the implementation notes of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RelocalizationRingedTopos.lean`.
* Stacks 04J5 and Stacks 04J7 are formalized as isomorphisms of inverse-image functors transported
  across the equivalences of Stacks 04J3, not as 2-isomorphisms of morphisms of ringed topoi;
  the pasting that Stacks 04J9's proof performs is a pasting of 2-cells.

Universes follow Stacks 04J3 and Stacks 04J8: site objects, site morphisms and sections of the
structure sheaves are all taken in one universe `u`, which is what Stacks 0791 needs in order to
return a sheaf equivalence.

## References

* [Stacks Project, Tag 04J9](https://stacks.math.columbia.edu/tag/04J9)
* [Stacks Project, Tag 04J1](https://stacks.math.columbia.edu/tag/04J1)
* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
* [Stacks Project, Tag 04J5](https://stacks.math.columbia.edu/tag/04J5)
* [Stacks Project, Tag 04J7](https://stacks.math.columbia.edu/tag/04J7)
* [Stacks Project, Tag 04J8](https://stacks.math.columbia.edu/tag/04J8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ v₅ u₅ v₆ u₆ v₇ u₇

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- The conjugate of the inverse associator of three left adjoints is the inverse associator of
the three right adjoints. -/
theorem conjugateEquiv_associator_inv
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B} {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C}
    (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
        (Functor.associator L₀₁ L₁₂ L₂₃).inv =
      (Functor.associator R₃₂ R₂₁ R₁₀).inv := by
  apply (cancel_epi (Functor.associator R₃₂ R₂₁ R₁₀).hom).1
  rw [← conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃, conjugateEquiv_comp,
    Iso.inv_hom_id, conjugateEquiv_id, conjugateEquiv_associator_hom, Iso.hom_inv_id]

/-- Vertical composition of three conjugates. -/
theorem conjugateEquiv_comp₃ {L₁ L₂ L₃ L₄ : A ⥤ B} {R₁ R₂ R₃ R₄ : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (α : L₂ ⟶ L₁) (β : L₃ ⟶ L₂) (γ : L₄ ⟶ L₃) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β ≫ conjugateEquiv adj₃ adj₄ γ =
      conjugateEquiv adj₁ adj₄ (γ ≫ β ≫ α) := by
  rw [conjugateEquiv_comp adj₂ adj₃ adj₄, conjugateEquiv_comp adj₁ adj₂ adj₄, Category.assoc]

/-- The conjugate of an inverse associator preceded by a left whiskering: the inverse associator
of the right adjoints, followed by the right whiskering of the conjugate of the whiskered
transformation. The hypothesis `hα` lets the transformation be given in any spelling
definitionally equal to that composite. -/
theorem conjugateEquiv_assoc_inv_whisker
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B} {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C}
    {L' : B ⥤ D} {R' : D ⥤ B}
    (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) (adj' : L' ⊣ R')
    (τ : L' ⟶ L₁₂ ⋙ L₂₃) (α : L₀₁ ⋙ L' ⟶ (L₀₁ ⋙ L₁₂) ⋙ L₂₃)
    (hα : α = Functor.whiskerLeft L₀₁ τ ≫ (Functor.associator L₀₁ L₁₂ L₂₃).inv) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp adj') α =
      (Functor.associator R₃₂ R₂₁ R₁₀).inv ≫
        Functor.whiskerRight (conjugateEquiv (adj₁₂.comp adj₂₃) adj' τ) R₁₀ := by
  subst hα
  rw [← conjugateEquiv_comp ((adj₀₁.comp adj₁₂).comp adj₂₃)
      (adj₀₁.comp (adj₁₂.comp adj₂₃)) (adj₀₁.comp adj'),
    conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft]

/-- Vertical composition of three conjugates, with each factor identified. -/
theorem conjugateEquiv_comp₃_eq {L₁ L₂ L₃ L₄ : A ⥤ B} {R₁ R₂ R₃ R₄ : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (α : L₂ ⟶ L₁) (β : L₃ ⟶ L₂) (γ : L₄ ⟶ L₃) {u : R₁ ⟶ R₂} {v : R₂ ⟶ R₃} {w : R₃ ⟶ R₄}
    (hu : conjugateEquiv adj₁ adj₂ α = u) (hv : conjugateEquiv adj₂ adj₃ β = v)
    (hw : conjugateEquiv adj₃ adj₄ γ = w) :
    conjugateEquiv adj₁ adj₄ (γ ≫ β ≫ α) = u ≫ v ≫ w := by
  rw [← conjugateEquiv_comp₃ adj₁ adj₂ adj₃ adj₄, hu, hv, hw]


/-- Rearranging a pentagon of isomorphisms. -/
theorem pentagon_rearrange {C : Type u₅} [Category.{v₅} C] {o₁ o₂ o₃ o₄ o₅ : C}
    (u : o₁ ≅ o₂) (v : o₃ ≅ o₂) (p : o₁ ≅ o₄) (q : o₃ ≅ o₅) (t : o₄ ≅ o₅)
    (h : p.hom ≫ t.hom = u.hom ≫ v.inv ≫ q.hom) :
    v.hom ≫ u.inv ≫ p.hom = q.hom ≫ t.inv := by
  rw [← cancel_mono t.hom, Category.assoc, Category.assoc, h]
  simp

/-- The algebraic core of the pasting comparison: the two pasted squares agree, given the
decomposition of the one square, the naturality of its middle cell, the comparison of the other
square, and the rearranged pentagon. -/
theorem paste_chase {C : Type u₅} [Category.{v₅} C] {D : Type u₆} [Category.{v₆} D]
    {E : Type u₇} [Category.{v₇} E] (Gf : D ⥤ C) (Kf : E ⥤ C)
    {XJ : C} {y₀ y₁ y₂ : E} {wJ wQ wQ' wP wJ' : D}
    (kapR : Kf.obj y₀ ≅ XJ) (sqS : XJ ⟶ Gf.obj wJ) (b₁ : y₀ ⟶ y₁) (b₂ : y₁ ⟶ y₂)
    (sqq : Kf.obj y₂ ⟶ Gf.obj wP)
    (sqT' : Kf.obj y₂ ⟶ Gf.obj wQ') (sqT'' : Kf.obj y₁ ⟶ Gf.obj wQ)
    (alq : wQ ⟶ wQ') (triTinv : wQ' ⟶ wP) (kapPhom : wP ⟶ wJ') (kapQhom : wQ ⟶ wJ)
    (triSinv : wJ ⟶ wJ')
    (hD : sqq = sqT' ≫ Gf.map triTinv)
    (hA : Kf.map b₂ ≫ sqT' = sqT'' ≫ Gf.map alq)
    (hB : kapR.hom ≫ sqS = Kf.map b₁ ≫ sqT'' ≫ Gf.map kapQhom)
    (hC : alq ≫ triTinv ≫ kapPhom = kapQhom ≫ triSinv) :
    sqS ≫ Gf.map triSinv =
      kapR.inv ≫ Kf.map (b₁ ≫ b₂) ≫ sqq ≫ Gf.map kapPhom := by
  subst hD
  rw [Functor.map_comp, Category.assoc, Category.assoc, ← Category.assoc (Kf.map b₂), hA,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hC, Functor.map_comp,
    ← Category.assoc sqT'', ← Category.assoc (Kf.map b₁), ← hB]
  simp

end Stacks.CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

section Components

variable {A B C : RingedTopos.{u, u, u}}
  [A.J.HasSheafCompose (forget RingCat.{u})] [B.J.HasSheafCompose (forget RingCat.{u})]
  [C.J.HasSheafCompose (forget RingCat.{u})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Components of a vertical composite of 2-isomorphisms. -/
@[simp]
theorem TwoIso.trans_e_hom_app {p q r : RingedToposHom A B} (s : TwoIso p q) (t : TwoIso q r)
    (Ω : A.Topos) : (s.trans t).e.hom.app Ω = s.e.hom.app Ω ≫ t.e.hom.app Ω :=
  rfl

/-- Components of the inverse of a 2-isomorphism. -/
@[simp]
theorem TwoIso.symm_e_hom_app {p q : RingedToposHom A B} (s : TwoIso p q) (Ω : A.Topos) :
    s.symm.e.hom.app Ω = s.e.inv.app Ω :=
  rfl

/-- Components of a right whiskering. -/
@[simp]
theorem TwoIso.whiskerRight_e_hom_app {p q : RingedToposHom A B} (s : TwoIso p q)
    (g : RingedToposHom B C) (Ω : A.Topos) :
    (s.whiskerRight g).e.hom.app Ω = g.toToposHom.pushforward.map (s.e.hom.app Ω) :=
  rfl

/-- Components of a left whiskering. -/
@[simp]
theorem TwoIso.whiskerLeft_e_hom_app (f : RingedToposHom A B) {p q : RingedToposHom B C}
    (s : TwoIso p q) (Ω : A.Topos) :
    (TwoIso.whiskerLeft f s).e.hom.app Ω = s.e.hom.app (f.toToposHom.pushforward.obj Ω) :=
  rfl

/-- Components of the inverse of a vertical composite. -/
@[simp]
theorem TwoIso.trans_e_inv_app {p q r : RingedToposHom A B} (s : TwoIso p q) (t : TwoIso q r)
    (Ω : A.Topos) : (s.trans t).e.inv.app Ω = t.e.inv.app Ω ≫ s.e.inv.app Ω :=
  rfl

/-- Components of the inverse of an inverted 2-isomorphism. -/
@[simp]
theorem TwoIso.symm_e_inv_app {p q : RingedToposHom A B} (s : TwoIso p q) (Ω : A.Topos) :
    s.symm.e.inv.app Ω = s.e.hom.app Ω :=
  rfl

/-- Components of the inverse of a right whiskering. -/
@[simp]
theorem TwoIso.whiskerRight_e_inv_app {p q : RingedToposHom A B} (s : TwoIso p q)
    (g : RingedToposHom B C) (Ω : A.Topos) :
    (s.whiskerRight g).e.inv.app Ω = g.toToposHom.pushforward.map (s.e.inv.app Ω) :=
  rfl

/-- Components of the inverse of a left whiskering. -/
@[simp]
theorem TwoIso.whiskerLeft_e_inv_app (f : RingedToposHom A B) {p q : RingedToposHom B C}
    (s : TwoIso p q) (Ω : A.Topos) :
    (TwoIso.whiskerLeft f s).e.inv.app Ω = s.e.inv.app (f.toToposHom.pushforward.obj Ω) :=
  rfl

/-- A vertical composite whose first factor is a left whiskering. -/
theorem TwoIso.whiskerLeft_trans_e_hom_app (f : RingedToposHom A B)
    {p q : RingedToposHom B C} {E : RingedToposHom A C} (s : TwoIso p q)
    (t : TwoIso (q.comp f) E) (Ω : A.Topos) :
    ((TwoIso.whiskerLeft f s).trans t).e.hom.app Ω =
      s.e.hom.app (f.toToposHom.pushforward.obj Ω) ≫ t.e.hom.app Ω :=
  rfl

/-- A vertical composite whose first factor is an inverted left whiskering. -/
theorem TwoIso.whiskerLeft_symm_trans_e_hom_app (f : RingedToposHom A B)
    {p q : RingedToposHom B C} {E : RingedToposHom A C} (s : TwoIso p q)
    (t : TwoIso (p.comp f) E) (Ω : A.Topos) :
    ((TwoIso.whiskerLeft f s).symm.trans t).e.hom.app Ω =
      s.e.inv.app (f.toToposHom.pushforward.obj Ω) ≫ t.e.hom.app Ω :=
  rfl

/-- A vertical composite whose first factor is a right whiskering. -/
theorem TwoIso.whiskerRight_trans_e_hom_app {p q : RingedToposHom A B}
    {E : RingedToposHom A C} (s : TwoIso p q) (g : RingedToposHom B C)
    (t : TwoIso (g.comp q) E) (Ω : A.Topos) :
    ((s.whiskerRight g).trans t).e.hom.app Ω =
      g.toToposHom.pushforward.map (s.e.hom.app Ω) ≫ t.e.hom.app Ω :=
  rfl


end Components

section Associator

variable {A B C D : RingedTopos.{u, u, u}}
  [A.J.HasSheafCompose (forget RingCat.{u})] [B.J.HasSheafCompose (forget RingCat.{u})]
  [C.J.HasSheafCompose (forget RingCat.{u})] [D.J.HasSheafCompose (forget RingCat.{u})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The associator of ringed topoi has identity components. -/
@[simp]
theorem TwoIso.associator_e_hom_app (f : RingedToposHom A B) (g : RingedToposHom B C)
    (h : RingedToposHom C D) (Ω : A.Topos) :
    (TwoIso.associator f g h).e.hom.app Ω = 𝟙 _ :=
  rfl

/-- The inverse associator of ringed topoi has identity components. -/
@[simp]
theorem TwoIso.associator_e_inv_app (f : RingedToposHom A B) (g : RingedToposHom B C)
    (h : RingedToposHom C D) (Ω : A.Topos) :
    (TwoIso.associator f g h).e.inv.app Ω = 𝟙 _ :=
  rfl

/-- A vertical composite whose first factor is an associator. -/
theorem TwoIso.associator_trans_e_hom_app {E : RingedToposHom A D} (f : RingedToposHom A B)
    (g : RingedToposHom B C) (h : RingedToposHom C D)
    (t : TwoIso ((h.comp g).comp f) E) (Ω : A.Topos) :
    ((TwoIso.associator f g h).trans t).e.hom.app Ω = t.e.hom.app Ω :=
  Category.id_comp _

/-- A vertical composite whose first factor is an inverse associator. -/
theorem TwoIso.associator_symm_trans_e_hom_app {E : RingedToposHom A D}
    (f : RingedToposHom A B) (g : RingedToposHom B C) (h : RingedToposHom C D)
    (t : TwoIso (h.comp (g.comp f)) E) (Ω : A.Topos) :
    ((TwoIso.associator f g h).symm.trans t).e.hom.app Ω = t.e.hom.app Ω :=
  Category.id_comp _

/-- A vertical composite whose last factor is an associator. -/
theorem TwoIso.trans_associator_e_hom_app {E : RingedToposHom A D} (f : RingedToposHom A B)
    (g : RingedToposHom B C) (h : RingedToposHom C D)
    (t : TwoIso E (h.comp (g.comp f))) (Ω : A.Topos) :
    (t.trans (TwoIso.associator f g h)).e.hom.app Ω = t.e.hom.app Ω :=
  Category.comp_id _

/-- A vertical composite whose last factor is an inverse associator. -/
theorem TwoIso.trans_associator_symm_e_hom_app {E : RingedToposHom A D}
    (f : RingedToposHom A B) (g : RingedToposHom B C) (h : RingedToposHom C D)
    (t : TwoIso E ((h.comp g).comp f)) (Ω : A.Topos) :
    (t.trans (TwoIso.associator f g h).symm).e.hom.app Ω = t.e.hom.app Ω :=
  Category.comp_id _

end Associator

section Pasting

variable {P Q R P' Q' R' W Z : RingedTopos.{u, u, u}}
  [P.J.HasSheafCompose (forget RingCat.{u})] [Q.J.HasSheafCompose (forget RingCat.{u})]
  [R.J.HasSheafCompose (forget RingCat.{u})] [P'.J.HasSheafCompose (forget RingCat.{u})]
  [Q'.J.HasSheafCompose (forget RingCat.{u})] [R'.J.HasSheafCompose (forget RingCat.{u})]
  [W.J.HasSheafCompose (forget RingCat.{u})] [Z.J.HasSheafCompose (forget RingCat.{u})]
  [P.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Q.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [R.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [P'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Q'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [R'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (rs : RingedToposHom P Q) (ls : RingedToposHom Q R)
  (rt : RingedToposHom P' Q') (lt : RingedToposHom Q' R')
  (cP : RingedToposHom P P') (cQ : RingedToposHom Q Q') (cR : RingedToposHom R R')
  (jP : RingedToposHom P W) (jQ : RingedToposHom Q W) (jR : RingedToposHom R Z)
  (kP : RingedToposHom P' W) (kQ : RingedToposHom Q' W) (kR : RingedToposHom R' Z)
  (g : RingedToposHom W Z)
  (kapP : TwoIso (comp kP cP) jP) (kapQ : TwoIso (comp kQ cQ) jQ)
  (kapR : TwoIso (comp kR cR) jR)
  (triS : TwoIso jP (comp jQ rs)) (triT : TwoIso kP (comp kQ rt))
  (sqS : TwoIso (comp jR ls) (comp g jQ)) (sqT : TwoIso (comp kR lt) (comp g kQ))
  (al : TwoIso (comp cQ rs) (comp rt cP)) (bl : TwoIso (comp cR ls) (comp lt cQ))

/-- The comparison 2-isomorphism pasted out of the comparison of the relocalizations and the
comparison of the localized morphisms. -/
noncomputable def pastedComparison :
    TwoIso (comp cR (comp ls rs)) (comp (comp lt rt) cP) :=
  (TwoIso.associator rs ls cR).trans
    ((TwoIso.whiskerLeft rs bl).trans
      ((TwoIso.associator rs cQ lt).symm.trans
        ((al.whiskerRight lt).trans (TwoIso.associator cP rt lt))))

/-- **The formal pasting step.** Given the comparison of the two relocalization triangles and
the comparison of the two localization squares, the square pasted from the first pair agrees
with the square pasted from the second pair, under the comparison `pastedComparison`. -/
theorem exists_pastedComparison
    (sq : TwoIso (comp kR (comp lt rt)) (comp g kP))
    (hsq : sq.e.hom =
      ((TwoIso.associator rt lt kR).trans
        ((TwoIso.whiskerLeft rt sqT).trans
          ((TwoIso.associator rt kQ g).symm.trans (triT.whiskerRight g).symm))).e.hom)
    (hal : kapP.trans triS =
      (TwoIso.whiskerLeft cP triT).trans
        ((TwoIso.associator cP rt kQ).symm.trans
          ((al.symm.whiskerRight kQ).trans
            ((TwoIso.associator rs cQ kQ).trans (TwoIso.whiskerLeft rs kapQ)))))
    (hbl : (TwoIso.associator ls cR kR).trans
        ((TwoIso.whiskerLeft ls kapR).trans sqS) =
      (bl.whiskerRight kR).trans
        ((TwoIso.associator cQ lt kR).trans
          ((TwoIso.whiskerLeft cQ sqT).trans
            ((TwoIso.associator cQ kQ g).symm.trans (kapQ.whiskerRight g))))) :
    ∃ β : TwoIso (comp cR (comp ls rs)) (comp (comp lt rt) cP),
      ((TwoIso.associator rs ls jR).trans
          ((TwoIso.whiskerLeft rs sqS).trans
            ((TwoIso.associator rs jQ g).symm.trans (triS.whiskerRight g).symm))).e.hom =
        (((TwoIso.whiskerLeft (comp ls rs) kapR).symm).trans
          ((TwoIso.associator (comp ls rs) cR kR).symm.trans
            ((β.whiskerRight kR).trans
              ((TwoIso.associator cP (comp lt rt) kR).trans
                ((TwoIso.whiskerLeft cP sq).trans
                  ((TwoIso.associator cP kP g).symm.trans
                    (kapP.whiskerRight g))))))).e.hom := by
  refine ⟨pastedComparison rs ls rt lt cP cQ cR al bl, ?_⟩
  refine NatTrans.ext (funext fun Ω ↦ ?_)
  have hsqΩ := congrArg (fun t ↦ NatTrans.app t (cP.toToposHom.pushforward.obj Ω)) hsq
  have halΩ : kapP.e.hom.app Ω ≫ triS.e.hom.app Ω =
      ((TwoIso.whiskerLeft cP triT).trans
        ((TwoIso.associator cP rt kQ).symm.trans
          ((al.symm.whiskerRight kQ).trans
            ((TwoIso.associator rs cQ kQ).trans
              (TwoIso.whiskerLeft rs kapQ))))).e.hom.app Ω :=
    congrArg (fun t ↦ NatTrans.app t.e.hom Ω) hal
  have hblΩ := congrArg (fun t ↦ NatTrans.app t.e.hom (rs.toToposHom.pushforward.obj Ω)) hbl
  simp only [pastedComparison, TwoIso.associator_trans_e_hom_app,
    TwoIso.associator_symm_trans_e_hom_app, TwoIso.trans_associator_e_hom_app,
    TwoIso.whiskerLeft_trans_e_hom_app,
    TwoIso.whiskerLeft_symm_trans_e_hom_app, TwoIso.whiskerRight_trans_e_hom_app,
    TwoIso.symm_e_hom_app,
    TwoIso.whiskerRight_e_hom_app, TwoIso.whiskerLeft_e_hom_app,
    TwoIso.whiskerRight_e_inv_app] at hsqΩ halΩ hblΩ ⊢
  have nat : kR.toToposHom.pushforward.map
        (lt.toToposHom.pushforward.map (al.e.hom.app Ω)) ≫
          sqT.e.hom.app (rt.toToposHom.pushforward.obj (cP.toToposHom.pushforward.obj Ω)) =
      sqT.e.hom.app (cQ.toToposHom.pushforward.obj (rs.toToposHom.pushforward.obj Ω)) ≫
        g.toToposHom.pushforward.map
          (kQ.toToposHom.pushforward.map (al.e.hom.app Ω)) :=
    sqT.e.hom.naturality (al.e.hom.app Ω)
  have key := Stacks.CategoryTheory.pentagon_rearrange
    (triT.e.app (cP.toToposHom.pushforward.obj Ω))
    (kQ.toToposHom.pushforward.mapIso (al.e.app Ω)) (kapP.e.app Ω)
    (kapQ.e.app (rs.toToposHom.pushforward.obj Ω)) (triS.e.app Ω) halΩ
  exact Stacks.CategoryTheory.paste_chase g.toToposHom.pushforward kR.toToposHom.pushforward
    (kapR.e.app (ls.toToposHom.pushforward.obj (rs.toToposHom.pushforward.obj Ω))) _ _ _ _ _
    _ _ _ _ _ _ hsqΩ nat hblΩ key

end Pasting

/-- **Stacks 04J4**, commutativity of the relocalization triangle as a triangle of ringed topoi:
`(j_G, j_G♯)` is `(j_F, j_F♯)` composed with the relocalization `(j, j♯)` along `s`.

The two inverse images are equal on the nose — restriction along postcomposition followed by
restriction along the projection from the site of elements of `F` is restriction along the
projection from the site of elements of `G` — and all three structure maps are identities on
underlying sheaves of sets, so there is nothing left to check. -/
@[stacks 04J4 "the relocalization triangle commutes as a triangle of ringed topoi"]
noncomputable def toposRelocalizationTriangle (W : RingedTopos.{u, u, u}) {H K : W.Topos}
    (a : H ⟶ K) :
    TwoIso (A := W.localizedRingedTopos H) (B := W)
      (W.localizationMorphism H)
      (comp (X := W.localizedRingedTopos H) (Y := W.localizedRingedTopos K) (Z := W)
        (W.localizationMorphism K) (W.relocalizationMorphism a)) :=
  TwoIso.ofInverseImageIso (A := W.localizedRingedTopos H) (B := W)
    (p := W.localizationMorphism H)
    (q := comp (X := W.localizedRingedTopos H) (Y := W.localizedRingedTopos K) (Z := W)
      (W.localizationMorphism K) (W.relocalizationMorphism a))
    (Iso.refl _) (by
      have hH := forgetRing_localizationMorphism_fSharpInverseImage W H
      have hK := forgetRing_localizationMorphism_fSharpInverseImage W K
      have ha := forgetRing_relocalizationMorphism_fSharpInverseImage W a
      have hq : (W.localizedRingedTopos H).forgetRing.map
          (comp (X := W.localizedRingedTopos H) (Y := W.localizedRingedTopos K) (Z := W)
            (W.localizationMorphism K)
            (W.relocalizationMorphism a)).fSharpInverseImage =
          𝟙 ((W.localizedRingedTopos H).forgetRing.obj (W.localizedRingedTopos H).O) :=
        (comp_fSharpInverseImage_forget
            (X := W.localizedRingedTopos H) (Y := W.localizedRingedTopos K) (Z := W)
            (W.localizationMorphism K) (W.relocalizationMorphism a)).trans
          ((congrArg (fun z ↦ (W.relocalizationMorphism a).toToposHom.inverseImage.map
              ((W.localizedRingedTopos K).forgetRing.map
                (W.localizationMorphism K).fSharpInverseImage) ≫ z) ha).trans
            ((Category.comp_id _).trans
              ((congrArg (fun z ↦ (W.relocalizationMorphism a).toToposHom.inverseImage.map z)
                  hK).trans
                ((W.relocalizationMorphism a).toToposHom.inverseImage.map_id _))))
      exact (Category.id_comp _).trans (hH.trans hq.symm))

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y) {G : Y.Topos} {F : X.Topos}
  (s : F ⟶ f.toToposHom.inverseImage.obj G)

/-- **Stacks 04IF**: the square of Stacks 04IF as a 2-isomorphism of ringed topoi.

The comparison of inverse images is `inverseImageCompLocalizationIso`, and the compatibility of
the three structure maps that it needs is `localized_fSharpInverseImage_forget`; the structure
maps of the two localization morphisms are identities on underlying sheaves of sets, so they
drop out of the two composites. -/
@[stacks 04IF "the square of 04IF as a 2-isomorphism of ringed topoi"]
noncomputable def localizedRingedToposSquare (G : Y.Topos) :
    TwoIso (A := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)) (B := Y)
      (comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
        (Y := Y.localizedRingedTopos G) (Z := Y)
        (Y.localizationMorphism G) (f.localized G))
      (comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)) (Y := X) (Z := Y)
        f (X.localizationMorphism (f.toToposHom.inverseImage.obj G))) :=
  TwoIso.ofInverseImageIso
    (A := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)) (B := Y)
    (p := comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
      (Y := Y.localizedRingedTopos G) (Z := Y) (Y.localizationMorphism G) (f.localized G))
    (q := comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)) (Y := X) (Z := Y)
      f (X.localizationMorphism (f.toToposHom.inverseImage.obj G)))
    (f.inverseImageCompLocalizationIso G) (by
      have hjG := forgetRing_localizationMorphism_fSharpInverseImage Y G
      have hjGp := forgetRing_localizationMorphism_fSharpInverseImage X
        (f.toToposHom.inverseImage.obj G)
      have hP : (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
            (comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
              (Y := Y.localizedRingedTopos G) (Z := Y)
              (Y.localizationMorphism G) (f.localized G)).fSharpInverseImage =
          (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
            (f.localized G).fSharpInverseImage :=
        (comp_fSharpInverseImage_forget
            (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
            (Y := Y.localizedRingedTopos G) (Z := Y)
            (Y.localizationMorphism G) (f.localized G)).trans
          ((congrArg (fun z ↦ z ≫ (X.localizedRingedTopos
              (f.toToposHom.inverseImage.obj G)).forgetRing.map
                (f.localized G).fSharpInverseImage)
            ((congrArg (fun z ↦ (f.localized G).toToposHom.inverseImage.map z) hjG).trans
              ((f.localized G).toToposHom.inverseImage.map_id _))).trans (Category.id_comp _))
      have hQ : (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
            (comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)) (Y := X)
              (Z := Y) f
              (X.localizationMorphism
                (f.toToposHom.inverseImage.obj G))).fSharpInverseImage =
          (X.localizationMorphism
              (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
            (X.forgetRing.map f.fSharpInverseImage) :=
        (comp_fSharpInverseImage_forget
            (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)) (Y := X) (Z := Y)
            f (X.localizationMorphism (f.toToposHom.inverseImage.obj G))).trans
          ((congrArg (fun z ↦ (X.localizationMorphism
              (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
                (X.forgetRing.map f.fSharpInverseImage) ≫ z) hjGp).trans
            (Category.comp_id _))
      exact (congrArg (fun z ↦ (f.inverseImageCompLocalizationIso G).hom.app
        (Y.forgetRing.obj Y.O) ≫ z) hP).trans
        ((f.localized_fSharpInverseImage_forget G).trans hQ.symm))

/-! ### The 04J8 square is the pasting of 04IF's square with the 04J4 triangle -/

section Paste

/-- The pasting of 04IF's square with the 04J4 relocalization triangle. -/
noncomputable def relocalizedPastedSquare :
    TwoIso (A := X.localizedRingedTopos F) (B := Y)
      (comp (X := X.localizedRingedTopos F) (Y := Y.localizedRingedTopos G) (Z := Y)
        (Y.localizationMorphism G) (f.relocalized s))
      (comp (X := X.localizedRingedTopos F) (Y := X) (Z := Y) f
        (X.localizationMorphism F)) :=
  (TwoIso.associator (X.relocalizationMorphism s) (f.localized G)
        (Y.localizationMorphism G)).trans
    ((TwoIso.whiskerLeft (X.relocalizationMorphism s)
        (f.localizedRingedToposSquare G)).trans
      ((TwoIso.associator (X.relocalizationMorphism s)
          (X.localizationMorphism (f.toToposHom.inverseImage.obj G)) f).symm.trans
        ((toposRelocalizationTriangle X s).whiskerRight f).symm))

/-- Step (i): the 04J8 square's transformation, spelled as a conjugate. -/
theorem relocalizedRingedSquare_e_hom_eq :
    (f.relocalizedRingedSquare s).e.hom =
      conjugateEquiv
        ((Y.localizationMorphism G).toToposHom.adj.comp
          ((f.localized G).toToposHom.adj.comp (X.relocalizationMorphism s).toToposHom.adj))
        (f.toToposHom.adj.comp (X.localizationMorphism F).toToposHom.adj)
        ((Functor.associator f.toToposHom.inverseImage
              (X.localizationMorphism
                (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
              (X.relocalizationMorphism s).toToposHom.inverseImage).inv ≫
          Functor.whiskerRight (f.inverseImageCompLocalizationIso G).hom
              (X.relocalizationMorphism s).toToposHom.inverseImage ≫
            (Functor.associator (Y.localizationMorphism G).toToposHom.inverseImage
              (f.localized G).toToposHom.inverseImage
              (X.relocalizationMorphism s).toToposHom.inverseImage).hom) :=
  rfl

/-- Step (ii): the pasted square's transformation, spelled explicitly. -/
theorem relocalizedPastedSquare_e_hom_eq :
    (f.relocalizedPastedSquare s).e.hom =
      (Functor.associator (X.relocalizationMorphism s).toToposHom.pushforward
          (f.localized G).toToposHom.pushforward
          (Y.localizationMorphism G).toToposHom.pushforward).hom ≫
        Functor.whiskerLeft (X.relocalizationMorphism s).toToposHom.pushforward
            (conjugateEquiv
              ((Y.localizationMorphism G).toToposHom.adj.comp
                (f.localized G).toToposHom.adj)
              (f.toToposHom.adj.comp
                (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.adj)
              (f.inverseImageCompLocalizationIso G).hom) ≫
          ((Functor.associator (X.relocalizationMorphism s).toToposHom.pushforward
              (X.localizationMorphism
                (f.toToposHom.inverseImage.obj G)).toToposHom.pushforward
              f.toToposHom.pushforward).inv ≫
            Functor.whiskerRight
              (conjugateEquiv
                ((X.localizationMorphism
                    (f.toToposHom.inverseImage.obj G)).toToposHom.adj.comp
                  (X.relocalizationMorphism s).toToposHom.adj)
                (X.localizationMorphism F).toToposHom.adj
                (𝟙 ((X.localizationMorphism
                    (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage ⋙
                  (X.relocalizationMorphism s).toToposHom.inverseImage)))
              f.toToposHom.pushforward) :=
  rfl

/-- Step (iii): the last factor of the three-term decomposition. -/
theorem conjugateEquiv_lastFactor :
    conjugateEquiv
        ((f.toToposHom.adj.comp
            (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.adj).comp
          (X.relocalizationMorphism s).toToposHom.adj)
        (f.toToposHom.adj.comp (X.localizationMorphism F).toToposHom.adj)
        (Functor.associator f.toToposHom.inverseImage
          (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
          (X.relocalizationMorphism s).toToposHom.inverseImage).inv =
      (Functor.associator (X.relocalizationMorphism s).toToposHom.pushforward
          (X.localizationMorphism
            (f.toToposHom.inverseImage.obj G)).toToposHom.pushforward
          f.toToposHom.pushforward).inv ≫
        Functor.whiskerRight
          (conjugateEquiv
            ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.adj.comp
              (X.relocalizationMorphism s).toToposHom.adj)
            (X.localizationMorphism F).toToposHom.adj
            (𝟙 ((X.localizationMorphism
                (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage ⋙
              (X.relocalizationMorphism s).toToposHom.inverseImage)))
          f.toToposHom.pushforward :=
  Stacks.CategoryTheory.conjugateEquiv_assoc_inv_whisker f.toToposHom.adj
    (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.adj
    (X.relocalizationMorphism s).toToposHom.adj
    (X.localizationMorphism F).toToposHom.adj _ _ (Category.id_comp _).symm

/-- **The 04J8 square is the pasting of 04IF's square with the 04J4 triangle.** -/
theorem relocalizedRingedSquare_eq_paste :
    (f.relocalizedRingedSquare s).e.hom = (f.relocalizedPastedSquare s).e.hom := by
  refine (relocalizedRingedSquare_e_hom_eq f s).trans
    (Eq.trans (Stacks.CategoryTheory.conjugateEquiv_comp₃_eq _
      (((Y.localizationMorphism G).toToposHom.adj.comp
        (f.localized G).toToposHom.adj).comp (X.relocalizationMorphism s).toToposHom.adj)
      ((f.toToposHom.adj.comp
        (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.adj).comp
        (X.relocalizationMorphism s).toToposHom.adj) _ _ _ _
      (conjugateEquiv_associator_hom _ _ _) (conjugateEquiv_whiskerRight _ _ _ _)
      (conjugateEquiv_lastFactor f s))
    (relocalizedPastedSquare_e_hom_eq f s).symm)


end Paste

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp
  CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

section Localization

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- **The identification of Stacks 04J3, as a 2-isomorphism of ringed topoi.** Localizing the
ringed topos at `h_U^#` and then reading the result on the slice site `C/U` is the localization
of the ringed site at `U`: the comparison of inverse images of Stacks 04J3 conjugates to a
comparison of direct images, and it carries the structure map of the one composite to the
structure map of the other. -/
noncomputable def localizationTwoIso :
    TwoIso (A := ringedTopos (X.over U)) (B := ringedTopos X)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := ringedTopos X)
        (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U))
        (representableLocalizationRingedMorphism X U))
      (X.localizationRingedToposHom U) :=
  TwoIso.ofInverseImageIso (A := ringedTopos (X.over U)) (B := ringedTopos X)
    (p := AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
      (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
      (Z := ringedTopos X)
      (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U))
      (representableLocalizationRingedMorphism X U))
    (q := X.localizationCommRingedToposHom U)
    (representableLocalizationInverseImageIso X U).symm (by
      have h1 : (ringedTopos (X.over U)).forgetRing.map
          (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
            (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
            (Z := ringedTopos X)
            (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U))
            (representableLocalizationRingedMorphism X U)).fSharpInverseImage =
          (ringInverseImageComparisonApp X U).hom :=
        comp_representableLocalizationRingedMorphism_fSharpInverseImage_forget X U
      have h2 : (ringedTopos (X.over U)).forgetRing.map
          (X.localizationCommRingedToposHom U).fSharpInverseImage = 𝟙 _ :=
        localizationCommRingedToposHom_fSharpInverseImage_forget X U
      rw [h1, h2]
      exact (ringInverseImageComparisonApp X U).inv_hom_id)

end Localization

section Middle

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- **The identification of Stacks 04J3 at the middle corner.** Stacks 04J8 localizes the source
at `f^{-1}h_V^#`, while Stacks 04J3 identifies `Sh(C/u(V))` with the localization at
`h_{u(V)}^#`; composing that identification with the relocalization of Stacks 04J4 along the
inverse of Stacks 04D3's isomorphism `f^{-1}h_V^# ≅ h_{u(V)}^#` identifies `Sh(C/u(V))` with the
localization at `f^{-1}h_V^#`. -/
noncomputable def Hom.compareMid :
    AlgebraicGeometry.RingedToposHom (ringedTopos (X.over (f.u.obj V)))
      (RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V)) :=
  AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
    (Y := RingedTopos.localizedRingedTopos X.ringedTopos
      (representableSheaf X (f.u.obj V)))
    (Z := RingedTopos.localizedRingedTopos X.ringedTopos
      (f.inverseImageRepresentableSheaf V))
    (X.ringedTopos.relocalizationMorphism (f.inverseImageRepresentableSheafIso V).inv)
    (representableLocalizationRingedMorphism X (f.u.obj V))

/-- **The middle identification is compatible with the two localizations.** Localizing the ringed
topos at `f^{-1}h_V^#` and reading the result on `Sh(C/u(V))` through `Hom.compareMid` is the
localization of the ringed site at `u(V)`: the relocalization triangle of Stacks 04J4 for
Stacks 04D3's isomorphism reduces the claim to the identification of Stacks 04J3 at `u(V)`. -/
noncomputable def Hom.kapMid :
    TwoIso (A := ringedTopos (X.over (f.u.obj V))) (B := ringedTopos X)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (Z := ringedTopos X)
        (RingedTopos.localizationMorphism X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (f.compareMid V))
      (X.localizationRingedToposHom (f.u.obj V)) :=
  (TwoIso.associator (representableLocalizationRingedMorphism X (f.u.obj V))
      (X.ringedTopos.relocalizationMorphism (f.inverseImageRepresentableSheafIso V).inv)
      (RingedTopos.localizationMorphism X.ringedTopos
        (f.inverseImageRepresentableSheaf V))).trans
    ((TwoIso.whiskerLeft (representableLocalizationRingedMorphism X (f.u.obj V))
        (AlgebraicGeometry.RingedToposHom.toposRelocalizationTriangle X.ringedTopos
          (f.inverseImageRepresentableSheafIso V).inv).symm).trans
      (localizationTwoIso X (f.u.obj V)))

end Middle

section Squares

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)
  [HasFiniteLimits Y.C] [HasFiniteLimits X.C] [PreservesFiniteLimits f.u]

/-- **The localization square of Stacks 04J0, read from the localization of the ringed topos at
`h_V^#`.** This is the square of Stacks 04J0 preceded by the identification of Stacks 04J3 at
`V`; it is the left-hand side of the compatibility that Stacks 04J7 is used through. -/
noncomputable def Hom.locSquareCompareSite :
    TwoIso (A := ringedTopos (X.over (f.u.obj V))) (B := ringedTopos Y)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (Z := ringedTopos Y)
        (RingedTopos.localizationMorphism Y.ringedTopos (representableSheaf Y V))
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
          (Y := ringedTopos (Y.over V))
          (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
          (representableLocalizationRingedMorphism Y V) (f.localizedRingedToposHom V)))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := ringedTopos X) (Z := ringedTopos Y) f.ringedToposHom
        (X.localizationRingedToposHom (f.u.obj V))) :=
  (TwoIso.associator (f.localizedRingedToposHom V)
        (representableLocalizationRingedMorphism Y V)
        (RingedTopos.localizationMorphism Y.ringedTopos (representableSheaf Y V))).trans
    ((TwoIso.whiskerLeft (f.localizedRingedToposHom V)
      (localizationTwoIso Y V)).trans (f.localizedRingedSquare V))

/-- **The localization square of Stacks 04IF, read through the comparison of the two localized
morphisms.** This is the square of Stacks 04IF preceded by the comparison `locComparison` of
Stacks 04J7 and followed by the identification of Stacks 04J3 at the middle corner; it is the
right-hand side of the compatibility that Stacks 04J7 is used through. -/
noncomputable def Hom.locSquareCompareTopos
    (locComparison : TwoIso (A := ringedTopos (X.over (f.u.obj V)))
      (B := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := ringedTopos (Y.over V))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (representableLocalizationRingedMorphism Y V) (f.localizedRingedToposHom V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (f.ringedToposHom.localized (representableSheaf Y V)) (f.compareMid V))) :
    TwoIso (A := ringedTopos (X.over (f.u.obj V))) (B := ringedTopos Y)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (Z := ringedTopos Y)
        (RingedTopos.localizationMorphism Y.ringedTopos (representableSheaf Y V))
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
          (Y := ringedTopos (Y.over V))
          (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
          (representableLocalizationRingedMorphism Y V) (f.localizedRingedToposHom V)))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := ringedTopos X) (Z := ringedTopos Y) f.ringedToposHom
        (X.localizationRingedToposHom (f.u.obj V))) :=
  (locComparison.whiskerRight (RingedTopos.localizationMorphism Y.ringedTopos
        (representableSheaf Y V))).trans
    ((TwoIso.associator (f.compareMid V)
        (f.ringedToposHom.localized (representableSheaf Y V))
        (RingedTopos.localizationMorphism Y.ringedTopos (representableSheaf Y V))).trans
      ((TwoIso.whiskerLeft (f.compareMid V)
          (f.ringedToposHom.localizedRingedToposSquare
            (representableSheaf Y V))).trans
        ((TwoIso.associator (f.compareMid V)
            (RingedTopos.localizationMorphism X.ringedTopos
              (f.inverseImageRepresentableSheaf V))
            f.ringedToposHom).symm.trans
          ((f.kapMid V).whiskerRight f.ringedToposHom))))

end Squares

section Main

/-! The statements below carry the structure-map compatibility of Stacks 04IF's square as a
hypothesis, an equation whose two sides are built from Stacks 04IF's comparison of inverse
images. That comparison is a composite of four whiskered isomorphisms of functors between sheaf
categories, and nothing here needs to see inside it: the equation is only ever passed from one
statement to the next, never unfolded. Making it opaque keeps those hypotheses from being
compared by unfolding both sides to the underlying natural transformations. -/
attribute [local irreducible]
  AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) {V : Y.C} {U : X.C}
  (c : U ⟶ f.u.obj V)

/-- **The morphism of sheaves that Stacks 04J9 feeds to Stacks 04J8.** A morphism
`c : U ⟶ u(V)` of the source site induces `h_c^# : h_U^# ⟶ h_{u(V)}^#` on associated sheaves,
and Stacks 04D3 identifies `h_{u(V)}^#` with `f^{-1}h_V^#`; the composite is the morphism
`s : h_U^# ⟶ f^{-1}h_V^#` at which Stacks 04J8 relocalizes. -/
noncomputable abbrev Hom.relocalizationSheafMap :
    representableSheaf X U ⟶ f.toposHom.inverseImage.obj (representableSheaf Y V) :=
  representableSheafMap X c ≫ (f.inverseImageRepresentableSheafIso V).inv

variable [HasFiniteLimits Y.C] [HasFiniteLimits X.C] [PreservesFiniteLimits f.u]

omit [HasFiniteLimits Y.C] [HasFiniteLimits X.C] [PreservesFiniteLimits f.u] in
/-- **Stacks 04J9**, on structure maps: the two relocalized morphisms have the same structure
map, each being the structure map of its own localized morphism `f'` restricted along its own
relocalization.

Read in inverse-image form and on underlying sheaves of sets, the structure map of `f_c` is
`j_c^{-1}` applied to the structure map of the morphism of Stacks 04J0, and the structure map of
`f_s` is `j_s^{-1}` applied to the structure map of the morphism of Stacks 04IF; the structure
maps of the two relocalizations themselves are identities and drop out. Stacks 04J7
(`AlgebraicGeometry.RingedSite.Hom.localizedRepresentable_forgetFSharp`) says that the two
structure maps so restricted are the same formula, namely the structure map of `f` restricted
along the localization morphism. -/
@[stacks 04J9 "the relocalized morphism of 04J1 and the relocalized morphism of 04J8 have the
  same structure map: each is the structure map of its own `f'` restricted along its own
  relocalization, the relocalization contributing the identity, so that the assertion reduces
  to the one of 04J7"]
theorem Hom.relocalized_fSharpInverseImage_forget :
    (ringedTopos (X.over U)).forgetRing.map (f.relocalized c).fSharpInverseImage =
      (X.relocalizationRingedToposHom c).toToposHom.inverseImage.map
        ((ringedTopos (X.over (f.u.obj V))).forgetRing.map
          (f.localizedRingedToposHom V).fSharpInverseImage) ∧
    (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)).forgetRing.map
        (f.ringedToposHom.relocalized (f.relocalizationSheafMap c)).fSharpInverseImage =
      (X.ringedTopos.relocalizationMorphismOfTopoi (f.relocalizationSheafMap c)).inverseImage.map
        ((RingedTopos.localizedRingedTopos X.ringedTopos
            (f.ringedToposHom.toToposHom.inverseImage.obj
              (representableSheaf Y V))).forgetRing.map
          (f.ringedToposHom.localized (representableSheaf Y V)).fSharpInverseImage) := by
  constructor
  · refine (comp_fSharpInverseImage_forget
      (X := ringedTopos (X.over U)) (Y := ringedTopos (X.over (f.u.obj V)))
      (Z := ringedTopos (Y.over V))
      (f.localizedRingedToposHom V) (X.relocalizationRingedToposHom c)).trans ?_
    rw [X.forgetRing_relocalizationRingedToposHom_fSharpInverseImage c]
    exact Category.comp_id _
  · refine (comp_fSharpInverseImage_forget
      (X := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
      (Y := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.ringedToposHom.toToposHom.inverseImage.obj (representableSheaf Y V)))
      (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (f.ringedToposHom.localized (representableSheaf Y V))
      (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))).trans ?_
    exact (congrArg (_ ≫ ·) (forgetRing_relocalizationMorphism_fSharpInverseImage X.ringedTopos
      (f.relocalizationSheafMap c))).trans (Category.comp_id _)

/-- **The relocalization triangle of Stacks 04IY, read from the localization of the ringed topos
at `h_U^#`.** This is the triangle of Stacks 04IY preceded by the identification of Stacks 04J3
at `U`; it is the left-hand side of the compatibility that Stacks 04J5 is used through. -/
noncomputable def Hom.relocTriangleCompareSite :
    TwoIso (A := ringedTopos (X.over U)) (B := ringedTopos X)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := ringedTopos X)
        (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U))
        (representableLocalizationRingedMorphism X U))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (X.over (f.u.obj V))) (Z := ringedTopos X)
        (X.localizationRingedToposHom (f.u.obj V)) (X.relocalizationRingedToposHom c)) :=
  (localizationTwoIso X U).trans (relocalizationTriangle X c)

/-- **The relocalization triangle of Stacks 04J4, read through the comparison of the two
relocalizations.** This is the triangle of Stacks 04J4 followed by the comparison
`relocComparison` of Stacks 04J5 and the identification of Stacks 04J3 at the middle corner; it
is the right-hand side of the compatibility that Stacks 04J5 is used through. -/
noncomputable def Hom.relocTriangleCompareTopos
    (relocComparison : TwoIso (A := ringedTopos (X.over U))
      (B := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (X.over (f.u.obj V)))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (f.compareMid V) (X.relocalizationRingedToposHom c))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
        (representableLocalizationRingedMorphism X U))) :
    TwoIso (A := ringedTopos (X.over U)) (B := ringedTopos X)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := ringedTopos X)
        (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U))
        (representableLocalizationRingedMorphism X U))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (X.over (f.u.obj V))) (Z := ringedTopos X)
        (X.localizationRingedToposHom (f.u.obj V)) (X.relocalizationRingedToposHom c)) :=
  (TwoIso.whiskerLeft (representableLocalizationRingedMorphism X U)
      (AlgebraicGeometry.RingedToposHom.toposRelocalizationTriangle X.ringedTopos
        (f.relocalizationSheafMap c))).trans
    ((TwoIso.associator (representableLocalizationRingedMorphism X U)
        (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
        (RingedTopos.localizationMorphism X.ringedTopos
          (f.inverseImageRepresentableSheaf V))).symm.trans
      ((relocComparison.symm.whiskerRight
          (RingedTopos.localizationMorphism X.ringedTopos
            (f.inverseImageRepresentableSheaf V))).trans
        ((TwoIso.associator (X.relocalizationRingedToposHom c) (f.compareMid V)
            (RingedTopos.localizationMorphism X.ringedTopos
              (f.inverseImageRepresentableSheaf V))).trans
          (TwoIso.whiskerLeft (C := ringedTopos X)
            (X.relocalizationRingedToposHom c) (f.kapMid V)))))

/-- **The localization square of Stacks 04J8, read through the identifications of Stacks 04J3.**
Given a comparison `β` of the two relocalized morphisms, this is the square of Stacks 04J8
conjugated by the identification of Stacks 04J3 at `U` and at `V`; Stacks 04J9 says that it is
the localization square of Stacks 04J1. -/
noncomputable def Hom.relocalizedPastedComparisonSquare
    (β : TwoIso (A := ringedTopos (X.over U))
      (B := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (Y.over V))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (representableLocalizationRingedMorphism Y V) (f.relocalized c))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (f.ringedToposHom.relocalized (f.relocalizationSheafMap c))
        (representableLocalizationRingedMorphism X U))) :
    TwoIso (A := ringedTopos (X.over U)) (B := ringedTopos Y)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (Y.over V)) (Z := ringedTopos Y)
        (Y.localizationRingedToposHom V) (f.relocalized c))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos X) (Z := ringedTopos Y) f.ringedToposHom
        (X.localizationRingedToposHom U)) :=
  (TwoIso.whiskerLeft (f.relocalized c) (localizationTwoIso Y V)).symm.trans
    ((TwoIso.associator (f.relocalized c) (representableLocalizationRingedMorphism Y V)
        (RingedTopos.localizationMorphism Y.ringedTopos
          (representableSheaf Y V))).symm.trans
      ((β.whiskerRight (RingedTopos.localizationMorphism Y.ringedTopos
          (representableSheaf Y V))).trans
        ((TwoIso.associator (representableLocalizationRingedMorphism X U)
            (f.ringedToposHom.relocalized (f.relocalizationSheafMap c))
            (RingedTopos.localizationMorphism Y.ringedTopos
              (representableSheaf Y V))).trans
          ((TwoIso.whiskerLeft (representableLocalizationRingedMorphism X U)
              (f.ringedToposHom.relocalizedRingedSquare
                (f.relocalizationSheafMap c))).trans
            ((TwoIso.associator (representableLocalizationRingedMorphism X U)
                (RingedTopos.localizationMorphism X.ringedTopos
                  (representableSheaf X U)) f.ringedToposHom).symm.trans
              ((localizationTwoIso X U).whiskerRight f.ringedToposHom))))))

/-- **The assertion of Stacks 04J9**, as a proposition: there is a 2-isomorphism
`β : ι_V ∘ f_c ≅ f_s ∘ ι_U` of morphisms of ringed topoi under which the localization square of
Stacks 04J1 is the localization square of Stacks 04J8, read through the identifications of
Stacks 04J3 at `U` and at `V`. -/
def Hom.RelocalizedComparisonStatement : Prop :=
  ∃ β, (f.relocalizedLocalizationSquare c).e.hom =
    (f.relocalizedPastedComparisonSquare c β).e.hom

omit [HasFiniteLimits Y.C] [HasFiniteLimits X.C] [PreservesFiniteLimits f.u] in
/-- **Stacks 04J9.** The commutative diagram of Stacks 04J1 and the commutative diagram of
Stacks 04J8 agree via the identifications of Stacks 04J3: there is a 2-isomorphism
`β : ι_V ∘ f_c ≅ f_s ∘ ι_U` of morphisms of ringed topoi under which the localization square of
Stacks 04J1 *is* the localization square of Stacks 04J8, the horizontal edges being identified
by `localizationTwoIso` at `U` and at `V`.

Two things are granted, and they are exactly the two lemmas the source's proof cites.

* `relocComparison` is Stacks 04J5 as a 2-isomorphism of ringed topoi — the two relocalizations
  agree — and `hRelocTriangles` is its compatibility with the relocalization triangle of
  Stacks 04IY and that of Stacks 04J4.
* `locComparison` is Stacks 04J7 as a 2-isomorphism of ringed topoi — the two localized
  morphisms `f'` agree — and `hLocSquares` is its compatibility with the localization square of
  Stacks 04J0 and that of Stacks 04IF.

Given those the conclusion is formal, which is exactly what the source's proof asserts: the
comparison is pasted from `locComparison` and `relocComparison`
(`AlgebraicGeometry.RingedToposHom.pastedComparison`), and the pasting identity is
`AlgebraicGeometry.RingedToposHom.exists_pastedComparison` fed with the decomposition
`AlgebraicGeometry.RingedToposHom.relocalizedRingedSquare_eq_paste` of 04J8's square into the
square of Stacks 04IF and the relocalization triangle of Stacks 04J4.

This statement carries no `@[stacks 04J9]` attribute, and deliberately so: its four arguments are
the content of the source's assertion rather than inputs the source grants, so a tag here would
record Stacks 04J9 as established when what is established is only the implication. What this
repository does carry of 04J9 unconditionally is the assertion on structure maps,
`AlgebraicGeometry.RingedSite.Hom.relocalized_fSharpInverseImage_forget` above, and the assertion
on inverse images,
`AlgebraicGeometry.RingedSite.Hom.relocalizedCompInverseImageIso` in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RelocalizedMorphismInverseImage.lean`,
which pastes the two comparisons below on inverse images, where both hold. What neither supplies
is the coherence between them that makes the paste a 2-isomorphism of ringed topoi. Discharging
`locComparison` with `hLocSquares` is Stacks 04J7 (whose one assertion is that the diagrams of
04J0 and 04IF agree via 04J3), and `relocComparison` with `hRelocTriangles` is the
sheaf-morphism description of Stacks 04J5; neither is proved here. -/
theorem Hom.exists_relocalizedComparison
    (relocComparison : TwoIso (A := ringedTopos (X.over U))
      (B := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (X.over (f.u.obj V)))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (f.compareMid V) (X.relocalizationRingedToposHom c))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
        (representableLocalizationRingedMorphism X U)))
    (locComparison : TwoIso (A := ringedTopos (X.over (f.u.obj V)))
      (B := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := ringedTopos (Y.over V))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (representableLocalizationRingedMorphism Y V) (f.localizedRingedToposHom V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (f.ringedToposHom.localized (representableSheaf Y V)) (f.compareMid V)))
    (hRelocTriangles :
      f.relocTriangleCompareSite c = f.relocTriangleCompareTopos c relocComparison)
    (hLocSquares :
      f.locSquareCompareSite V = f.locSquareCompareTopos V locComparison) :
    f.RelocalizedComparisonStatement c :=
  AlgebraicGeometry.RingedToposHom.exists_pastedComparison
    (X.relocalizationRingedToposHom c)
    (f.localizedRingedToposHom V)
    (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
    (f.ringedToposHom.localized (representableSheaf Y V))
    (representableLocalizationRingedMorphism X U)
    (f.compareMid V)
    (representableLocalizationRingedMorphism Y V)
    (X.localizationRingedToposHom U)
    (X.localizationRingedToposHom (f.u.obj V))
    (Y.localizationRingedToposHom V)
    (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U))
    (RingedTopos.localizationMorphism X.ringedTopos (f.inverseImageRepresentableSheaf V))
    (RingedTopos.localizationMorphism Y.ringedTopos (representableSheaf Y V))
    f.ringedToposHom
    (localizationTwoIso X U) (f.kapMid V) (localizationTwoIso Y V)
    (relocalizationTriangle X c)
    (AlgebraicGeometry.RingedToposHom.toposRelocalizationTriangle X.ringedTopos
      (f.relocalizationSheafMap c))
    (f.localizedRingedSquare V)
    (f.ringedToposHom.localizedRingedToposSquare (representableSheaf Y V))
    relocComparison locComparison
    (f.ringedToposHom.relocalizedRingedSquare (f.relocalizationSheafMap c))
    (f.ringedToposHom.relocalizedRingedSquare_eq_paste (f.relocalizationSheafMap c))
    hRelocTriangles hLocSquares

end Main

end AlgebraicGeometry.RingedSite

end
