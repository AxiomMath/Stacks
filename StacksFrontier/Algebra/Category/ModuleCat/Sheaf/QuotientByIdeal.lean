module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quotients of sheaves of modules by an ideal

Let `(C, J)` be a site, `Λ` a commutative ring and `I ⊆ Λ` an ideal. A sheaf of `Λ`-modules `G` is
*annihilated* by `I` when `a • s = 0` for every `a ∈ I` and every local section `s`; a morphism
`q : F ⟶ G` *is the quotient of `F` by `I`* when `G` is annihilated by `I` and `q` is initial
among morphisms out of `F` to sheaves annihilated by `I`. This characterizes the sheaf `F / IF`
together with its quotient map up to unique isomorphism, without choosing a construction of it.

## Main definitions

* `Stacks.ModuleSheaf.IsAnnihilatedBy`: an ideal kills every local section.
* `Stacks.ModuleSheaf.IsQuotientBy`: the universal property of the quotient by an ideal.
* `Stacks.ModuleSheaf.isQuotientByIso`: the comparison isomorphism of two quotients.

## Main results

* `Stacks.ModuleSheaf.isAnnihilatedBy_iff_smul_id`: annihilation by `I` is the vanishing of the
  endomorphisms `a • 𝟙` for `a ∈ I` of the `Λ`-linear category of sheaves.
* `Stacks.ModuleSheaf.IsQuotientBy.map`: a `Λ`-linear left adjoint between categories of sheaves
  of `Λ`-modules carries quotients by `I` to quotients by `I`; this applies in particular to
  restriction to a slice site.
* `Stacks.ModuleSheaf.isQuotientBy_map_of_tower`: in a tower of quotients `F / IⁿF`, each
  transition map is the quotient of its source by the smaller power.

## Implementation notes

Annihilation is stated sectionwise, which is what the clients use; the categorical form
`a • 𝟙 G = 0` is what makes it visibly preserved by `Λ`-linear functors and their right adjoints.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w r u' v'

namespace Stacks.ModuleSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type r) [CommRing Λ]

/-- An ideal annihilates every local section of a sheaf of modules. -/
abbrev IsAnnihilatedBy (I : Ideal Λ) (G : Sheaf J (ModuleCat.{w} Λ)) : Prop :=
  ∀ (U : C) (a : Λ), a ∈ I → ∀ x : G.obj.obj (op U), a • x = 0

/-- A morphism of sheaves of modules is *the* quotient by an ideal `I` when its target is
annihilated by `I` and it is initial among morphisms out of its source to sheaves annihilated
by `I`. -/
abbrev IsQuotientBy (I : Ideal Λ) (F G : Sheaf J (ModuleCat.{w} Λ)) (q : F ⟶ G) : Prop :=
  IsAnnihilatedBy J Λ I G ∧
    ∀ H : Sheaf J (ModuleCat.{w} Λ),
      IsAnnihilatedBy J Λ I H → ∀ f : F ⟶ H, ∃! g : G ⟶ H, q ≫ g = f

variable {J Λ}

/-- Annihilation by `I` is the vanishing of the endomorphisms `a • 𝟙 G`, `a ∈ I`. -/
theorem isAnnihilatedBy_iff_smul_id (I : Ideal Λ) (G : Sheaf J (ModuleCat.{w} Λ)) :
    IsAnnihilatedBy J Λ I G ↔ ∀ a ∈ I, a • 𝟙 G = 0 := by
  refine ⟨fun h a ha => ?_, fun h U a ha x => ?_⟩
  · ext U x
    exact h U.unop a ha x
  · change ((a • 𝟙 G).hom.app (op U)).hom x = 0
    rw [h a ha]
    rfl

/-- A sheaf annihilated by an ideal is annihilated by every smaller ideal. -/
theorem IsAnnihilatedBy.mono {I I' : Ideal Λ} (hI : I' ≤ I) {H : Sheaf J (ModuleCat.{w} Λ)}
    (hH : IsAnnihilatedBy J Λ I H) : IsAnnihilatedBy J Λ I' H :=
  fun U a ha x => hH U a (hI ha) x

section Functor

variable {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  (L : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J' (ModuleCat.{w} Λ)) [L.Additive] [L.Linear Λ]

/-- A `Λ`-linear functor carries sheaves annihilated by `I` to sheaves annihilated by `I`. -/
theorem IsAnnihilatedBy.map {I : Ideal Λ} {G : Sheaf J (ModuleCat.{w} Λ)}
    (hG : IsAnnihilatedBy J Λ I G) : IsAnnihilatedBy J' Λ I (L.obj G) := by
  rw [isAnnihilatedBy_iff_smul_id] at hG ⊢
  intro a ha
  rw [← L.map_id, ← L.map_smul, hG a ha, L.map_zero]

/-- The right adjoint of a `Λ`-linear functor carries sheaves annihilated by `I` to sheaves
annihilated by `I`: the inverse of the adjunction bijection is `Λ`-linear, and it carries
`a • 𝟙 (R H)` to `a •` the counit, which factors through `a • 𝟙 H`. -/
theorem IsAnnihilatedBy.of_adjunction {R : Sheaf J' (ModuleCat.{w} Λ) ⥤ Sheaf J (ModuleCat.{w} Λ)}
    (adj : L ⊣ R) {I : Ideal Λ} {H : Sheaf J' (ModuleCat.{w} Λ)}
    (hH : IsAnnihilatedBy J' Λ I H) : IsAnnihilatedBy J Λ I (R.obj H) := by
  rw [isAnnihilatedBy_iff_smul_id] at hH ⊢
  intro a ha
  apply (adj.homEquiv (R.obj H) H).symm.injective
  simp only [Adjunction.homEquiv_counit, L.map_smul, L.map_zero, Limits.zero_comp,
    Linear.smul_comp, L.map_id, Category.id_comp]
  rw [show a • adj.counit.app H = adj.counit.app H ≫ (a • 𝟙 H) by
    rw [Linear.comp_smul]; simp, hH a ha, Limits.comp_zero]

/-- A functor with a right adjoint preserving annihilation by `I` carries a quotient by `I` to a
quotient by `I`, as soon as it carries the target to a sheaf annihilated by `I`. -/
private theorem isQuotientBy_map_of_adjunction
    {L₀ : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J' (ModuleCat.{w} Λ)}
    {R₀ : Sheaf J' (ModuleCat.{w} Λ) ⥤ Sheaf J (ModuleCat.{w} Λ)} (adj : L₀ ⊣ R₀)
    {I : Ideal Λ} {F G : Sheaf J (ModuleCat.{w} Λ)} {q : F ⟶ G}
    (h : IsQuotientBy J Λ I F G q) (hG : IsAnnihilatedBy J' Λ I (L₀.obj G))
    (hR : ∀ H, IsAnnihilatedBy J' Λ I H → IsAnnihilatedBy J Λ I (R₀.obj H)) :
    IsQuotientBy J' Λ I (L₀.obj F) (L₀.obj G) (L₀.map q) := by
  refine ⟨hG, fun H hH f => ?_⟩
  obtain ⟨g, hg, huniq⟩ := h.2 (R₀.obj H) (hR H hH) (adj.homEquiv _ _ f)
  refine ⟨(adj.homEquiv _ _).symm g, ?_, fun y hy => ?_⟩
  · change L₀.map q ≫ (adj.homEquiv _ _).symm g = f
    rw [← Adjunction.homEquiv_naturality_left_symm, hg, Equiv.symm_apply_apply]
  · change L₀.map q ≫ y = f at hy
    have : q ≫ adj.homEquiv _ _ y = adj.homEquiv _ _ f := by
      rw [← Adjunction.homEquiv_naturality_left, hy]
    rw [← huniq (adj.homEquiv _ _ y) this, Equiv.symm_apply_apply]

/-- **A `Λ`-linear left adjoint preserves quotients by an ideal.** -/
theorem IsQuotientBy.map {R : Sheaf J' (ModuleCat.{w} Λ) ⥤ Sheaf J (ModuleCat.{w} Λ)}
    (adj : L ⊣ R) {I : Ideal Λ} {F G : Sheaf J (ModuleCat.{w} Λ)} {q : F ⟶ G}
    (h : IsQuotientBy J Λ I F G q) : IsQuotientBy J' Λ I (L.obj F) (L.obj G) (L.map q) :=
  isQuotientBy_map_of_adjunction adj h (h.1.map L) fun _ hH => hH.of_adjunction L adj

/-- The left adjoint of a `Λ`-linear functor carries sheaves annihilated by `I` to sheaves
annihilated by `I`: the adjunction bijection is `Λ`-linear, and it carries `a • 𝟙 (L G)` to
`a •` the unit, which factors through `a • 𝟙 G`. -/
theorem IsAnnihilatedBy.of_adjunction_left
    {R' : Sheaf J' (ModuleCat.{w} Λ) ⥤ Sheaf J (ModuleCat.{w} Λ)}
    [R'.Additive] [R'.Linear Λ] {L' : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J' (ModuleCat.{w} Λ)}
    (adj : L' ⊣ R') {I : Ideal Λ} {G : Sheaf J (ModuleCat.{w} Λ)}
    (hG : IsAnnihilatedBy J Λ I G) : IsAnnihilatedBy J' Λ I (L'.obj G) := by
  rw [isAnnihilatedBy_iff_smul_id] at hG ⊢
  intro a ha
  apply (adj.homEquiv G (L'.obj G)).injective
  simp only [Adjunction.homEquiv_unit, R'.map_smul, R'.map_id, R'.map_zero, Limits.comp_zero,
    Linear.comp_smul]
  rw [show a • (adj.unit.app G ≫ 𝟙 (R'.obj (L'.obj G))) = (a • 𝟙 G) ≫ adj.unit.app G by
    rw [Linear.smul_comp, Category.id_comp]; exact congrArg _ (Category.comp_id _),
    hG a ha, Limits.zero_comp]

/-- **A left adjoint of a `Λ`-linear functor preserves quotients by an ideal.** -/
theorem IsQuotientBy.map' {R' : Sheaf J' (ModuleCat.{w} Λ) ⥤ Sheaf J (ModuleCat.{w} Λ)}
    [R'.Additive] [R'.Linear Λ] {L' : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J' (ModuleCat.{w} Λ)}
    (adj : L' ⊣ R') {I : Ideal Λ} {F G : Sheaf J (ModuleCat.{w} Λ)} {q : F ⟶ G}
    (h : IsQuotientBy J Λ I F G q) : IsQuotientBy J' Λ I (L'.obj F) (L'.obj G) (L'.map q) :=
  isQuotientBy_map_of_adjunction adj h (h.1.of_adjunction_left adj) fun _ hH => hH.map R'

end Functor

section QuotientBy

/-- Two quotients of a sheaf of modules by the same ideal are isomorphic, by an isomorphism
carrying one quotient map to the other. -/
noncomputable def isQuotientByIso {I : Ideal Λ}
    {F G G' : Sheaf J (ModuleCat.{w} Λ)} {q : F ⟶ G} {q' : F ⟶ G'}
    (h : IsQuotientBy J Λ I F G q) (h' : IsQuotientBy J Λ I F G' q') : G ≅ G' where
  hom := (h.2 G' h'.1 q').choose
  inv := (h'.2 G h.1 q).choose
  hom_inv_id := ((h.2 G h.1 q).choose_spec.2 _ (by
      change q ≫ ((h.2 G' h'.1 q').choose ≫ (h'.2 G h.1 q).choose) = q
      rw [← Category.assoc, (h.2 G' h'.1 q').choose_spec.1,
        (h'.2 G h.1 q).choose_spec.1])).trans
    ((h.2 G h.1 q).choose_spec.2 (𝟙 G) (Category.comp_id q)).symm
  inv_hom_id := ((h'.2 G' h'.1 q').choose_spec.2 _ (by
      change q' ≫ ((h'.2 G h.1 q).choose ≫ (h.2 G' h'.1 q').choose) = q'
      rw [← Category.assoc, (h'.2 G h.1 q).choose_spec.1,
        (h.2 G' h'.1 q').choose_spec.1])).trans
    ((h'.2 G' h'.1 q').choose_spec.2 (𝟙 G') (Category.comp_id q')).symm

/-- The comparison isomorphism between two quotients by one ideal carries the first quotient
map to the second. -/
theorem isQuotientByIso_hom_comp {I : Ideal Λ}
    {F G G' : Sheaf J (ModuleCat.{w} Λ)} {q : F ⟶ G} {q' : F ⟶ G'}
    (h : IsQuotientBy J Λ I F G q) (h' : IsQuotientBy J Λ I F G' q') :
    q ≫ (isQuotientByIso h h').hom = q' :=
  (h.2 G' h'.1 q').choose_spec.1

/-- Being the quotient by an ideal is transported along an isomorphism of the source. -/
theorem isQuotientBy_of_iso {I : Ideal Λ}
    {F F' G : Sheaf J (ModuleCat.{w} Λ)} {q : F ⟶ G} (e : F' ≅ F)
    (h : IsQuotientBy J Λ I F G q) : IsQuotientBy J Λ I F' G (e.hom ≫ q) := by
  refine ⟨h.1, fun H hH f => ⟨(h.2 H hH (e.inv ≫ f)).choose, ?_, fun y hy => ?_⟩⟩
  · change (e.hom ≫ q) ≫ _ = f
    rw [Category.assoc, (h.2 H hH (e.inv ≫ f)).choose_spec.1, ← Category.assoc,
      e.hom_inv_id, Category.id_comp]
  · change (e.hom ≫ q) ≫ y = f at hy
    refine (h.2 H hH (e.inv ≫ f)).choose_spec.2 y ?_
    change q ≫ y = e.inv ≫ f
    rw [← hy, Category.assoc, ← Category.assoc e.inv e.hom, e.inv_hom_id, Category.id_comp]

/-- Being the quotient by an ideal is transported along an isomorphism of the target. -/
theorem isQuotientBy_of_iso_target {I : Ideal Λ}
    {F G G' : Sheaf J (ModuleCat.{w} Λ)} {q : F ⟶ G} (e : G ≅ G')
    (h : IsQuotientBy J Λ I F G q) : IsQuotientBy J Λ I F G' (q ≫ e.hom) := by
  refine ⟨?_, fun H hH f => ⟨e.inv ≫ (h.2 H hH f).choose, ?_, fun y hy => ?_⟩⟩
  · have h₁ := h.1
    rw [isAnnihilatedBy_iff_smul_id] at h₁ ⊢
    intro a ha
    rw [show a • 𝟙 G' = e.inv ≫ (a • 𝟙 G) ≫ e.hom by simp, h₁ a ha]
    simp
  · change (q ≫ e.hom) ≫ e.inv ≫ (h.2 H hH f).choose = f
    rw [Category.assoc, e.hom_inv_id_assoc, (h.2 H hH f).choose_spec.1]
  · change (q ≫ e.hom) ≫ y = f at hy
    rw [← (h.2 H hH f).choose_spec.2 (e.hom ≫ y) (show q ≫ e.hom ≫ y = f by
      rw [← Category.assoc, hy]), e.inv_hom_id_assoc]

variable (I : Ideal Λ) {F : Sheaf J (ModuleCat.{w} Λ)}
  {Q : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} Λ)} (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)

/-- The transition map `F / IⁿF ⟶ F / IᵐF` of the adic quotient tower, for `m ≤ n`, exhibits
its target as the quotient of its source by `Iᵐ`. -/
theorem isQuotientBy_map_of_tower
    (hq : ∀ n : ℕ, IsQuotientBy J Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    {m n : ℕ} (hmn : m ≤ n) :
    IsQuotientBy J Λ (I ^ m) (Q.obj (op n)) (Q.obj (op m)) (Q.map (homOfLE hmn).op) := by
  have hnat : q.app (op n) ≫ Q.map (homOfLE hmn).op = q.app (op m) := by
    simpa using (q.naturality (homOfLE hmn).op).symm
  refine ⟨(hq m).1, fun H hH g =>
    ⟨((hq m).2 H hH (q.app (op n) ≫ g)).choose, ?_, fun y hy => ?_⟩⟩
  · have hbig := (hq n).2 H
      (hH.mono (Ideal.pow_le_pow_right hmn)) (q.app (op n) ≫ g)
    change Q.map (homOfLE hmn).op ≫ _ = g
    refine (hbig.choose_spec.2 _ ?_).trans (hbig.choose_spec.2 g rfl).symm
    change q.app (op n) ≫ Q.map (homOfLE hmn).op ≫ _ = _
    rw [← Category.assoc, hnat]
    exact ((hq m).2 H hH (q.app (op n) ≫ g)).choose_spec.1
  · change Q.map (homOfLE hmn).op ≫ y = g at hy
    refine ((hq m).2 H hH (q.app (op n) ≫ g)).choose_spec.2 y ?_
    change q.app (op m) ≫ y = q.app (op n) ≫ g
    rw [← hnat, Category.assoc, hy]

end QuotientBy

section RestrictQuotient

variable (J Λ) [UnivLE.{max u v, w}] (I : Ideal Λ)

/-- Restriction of coefficients along `Λ → Λ ⧸ I`, as a functor between the categories of
sheaves of modules. The sheaf condition transfers because the forgetful functor to abelian groups
factors through restriction of scalars, so a presheaf of `Λ`-modules whose underlying presheaf of
abelian groups is a sheaf is a sheaf. -/
@[implicit_reducible]
noncomputable def restrictQuotientScalars :
    Sheaf J (ModuleCat.{w} (Λ ⧸ I)) ⥤ Sheaf J (ModuleCat.{w} Λ) := by
  haveI : J.HasSheafCompose (ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk I)) := by
    refine ⟨fun P hP ↦ ?_⟩
    apply Presheaf.isSheaf_of_isSheaf_comp _
      (P ⋙ ModuleCat.restrictScalars (Ideal.Quotient.mk I))
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
    change Presheaf.IsSheaf J (P ⋙ forget₂ (ModuleCat.{w} (Λ ⧸ I)) AddCommGrpCat.{w})
    exact GrothendieckTopology.HasSheafCompose.isSheaf P hP
  exact sheafCompose J (ModuleCat.restrictScalars (Ideal.Quotient.mk I))

/-- Restriction of coefficients along `Λ → Λ ⧸ I` commutes with restriction to a slice site, on
the nose. -/
noncomputable def overPullbackRestrictQuotientScalarsIso (U : C) :
    J.overPullback (ModuleCat.{w} (Λ ⧸ I)) U ⋙ restrictQuotientScalars (J.over U) Λ I ≅
      restrictQuotientScalars J Λ I ⋙ J.overPullback (ModuleCat.{w} Λ) U :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable [HasWeakSheafify J (ModuleCat.{w} (Λ ⧸ I))] [HasWeakSheafify J (ModuleCat.{w} Λ)]
  [J.PreservesSheafification (ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk I))]

/-- Restriction of coefficients along `Λ → Λ ⧸ I` of a constant sheaf is the constant sheaf on
the restriction of coefficients. -/
noncomputable def restrictQuotientScalarsConstantSheafIso :
    constantSheaf J (ModuleCat.{w} (Λ ⧸ I)) ⋙ restrictQuotientScalars J Λ I ≅
      ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk I) ⋙ constantSheaf J (ModuleCat.{w} Λ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
      (sheafComposeNatIso J (ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk I))
        (sheafificationAdjunction J _) (sheafificationAdjunction J _)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.compConstIso Cᵒᵖ
      (ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk I))).symm _ ≪≫
    Functor.associator _ _ _

end RestrictQuotient

/-- Restriction to a slice site is `Λ`-linear. -/
instance linear_overPullback (U : C) : (J.overPullback (ModuleCat.{w} Λ) U).Linear Λ where
  map_smul _ _ := rfl

end Stacks.ModuleSheaf
