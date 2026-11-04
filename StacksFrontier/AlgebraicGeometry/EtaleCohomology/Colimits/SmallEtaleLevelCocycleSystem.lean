module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelTransitionCoherence
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CocycleSystemsOfColimitOfFiniteSites

/-!
# The two cocycle laws of the level crossing of Stacks 09YQ

`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem` is abelian
sheaves on the levels of [Stacks, Tag 0EYL] together with **direct-image** transition data subject
to the cocycle law alone, and
`...AbelianCocycleSystem.isColimitPresentation_split` carries a colimit presentation of such data
to one for a genuine `...AbelianSheafSystem`. So the coefficient side of the passage of
[Stacks, Tag 09YQ] from Mathlib's small étale sites to those levels owes nothing further; what the
*site* side owes is cocycle data on the levels built out of an
`Stacks.EtaleCohomology.EtaleSheafSystem`, together with a presentation of it.

Building that datum needs two cocycle laws, and this file proves both. They are independent of each
other: one is about the transition of the **sheaves**, the other about the transition of the
**sites**.

* The datum an `EtaleSheafSystem` carries is a map `f_a^{-1}F_j ⟶ F_i` *out of an inverse image*,
  with the cocycle law stated at `Stacks.EtaleCohomology.systemPullbackComp`. Transposing it across
  the adjunction gives a map `F_j ⟶ f_{a, *}F_i` into a direct image, and the transposed cocycle
  law is stated at `Stacks.EtaleCohomology.systemPushforwardComp`. That is
  `systemDirTransition_comp`.
* A level of [Stacks, Tag 0EYL] is a category of *chosen* pullback models, so its transition
  functor is identified with base change along the transition morphism of schemes only up to
  `Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso`, an isomorphism and not an
  equality. The cocycle law of that identification —
  `levelTransitionIso_hom_app_comp` — is the level-transition counterpart of
  `Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition_hom_app`, which
  does the same for the projections of the cone.

## Main definitions

* `Stacks.EtaleCohomology.systemDirTransition` — **the transition datum of an
  `Stacks.EtaleCohomology.EtaleSheafSystem` in the direct-image form**, the transpose of the datum
  the structure carries.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelEtaleRestrictAb` — restriction of abelian
  sheaves from Mathlib's small étale site of `X_n` to the level `n`, which
  `Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionAb` says is an
  equivalence.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelDirTransition` — the direct-image transition
  datum of a system between two levels.

## Main results

* `Stacks.EtaleCohomology.systemDirTransition_comp` — **the cocycle law of a system of étale
  sheaves, in the direct-image form.**
* `Stacks.EtaleCohomology.systemDirTransition_comp'` — the same at an arrow presented as a
  composite, which is the form needed at an arrow of `Iᵒᵖ` that is the image of a composite: there
  the image of the composite and the composite of the images are equal arrows and not the same
  term, and the type of `systemDirTransition` depends on the term.
* `Stacks.EtaleCohomology.AffineLimitCohomology.transitionScheme_comp` — the transition morphisms
  of schemes compose.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso_hom_app_comp` — **the cocycle
  law of the level-transition identification.**
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelDirTransition_comp` — the cocycle law of the
  transition datum of a system, read at the levels.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleSystem` — a system of abelian étale
  sheaves read as an
  `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem` on the
  levels of [Stacks, Tag 0EYL], with `levelCocycleMap_comp` as its cocycle law.
* `Stacks.EtaleCohomology.compatible_iff_systemDirTransition` — **the compatibility of a family
  of maps out of the inverse images of an ARBITRARY system is the compatibility of the adjoint
  family of maps of direct images.**
* `Stacks.EtaleCohomology.existsUnique_desc_dir_of_isPullbackColimitPresentation` — **the
  presentation of an arbitrary system with the inverse images removed**.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v u

namespace Stacks.EtaleCohomology

open AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **The algebra of the level cocycle law.** The shape in which the cocycle law of the transition
datum on the levels is assembled from the two cocycle laws it rests on: an isomorphism and its
inverse cancel in the middle (`hid`), the naturality of the transition datum in the object of the
site moves the transport of the later level across it (`hnat`), and the two transports along the
strictness field of the system agree (`hXE`). Stated in an arbitrary category and applied by
`exact`, as `Stacks.EtaleCohomology.AffineLimitCohomology.comp_comp_eq_of_naturality` is. -/
theorem assoc_cancel_of_naturality {𝒜 : Type*} [Category* 𝒜]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : 𝒜} {f : A₀ ⟶ A₁} {g : A₁ ⟶ A₂} {e : A₂ ⟶ A₃} {e' : A₃ ⟶ A₂}
    {k : A₂ ⟶ A₄} {l : A₄ ⟶ A₅} {t : A₅ ⟶ A₆} {g' : A₁ ⟶ A₇} {k' : A₇ ⟶ A₄} {t' : A₅ ⟶ A₆}
    (hid : e ≫ e' = 𝟙 A₂) (hnat : g' ≫ k' = g ≫ k) (hXE : t = t') :
    (f ≫ g ≫ e) ≫ e' ≫ k ≫ l ≫ t = (f ≫ g') ≫ (k' ≫ l) ≫ t' := by
  simp only [Category.assoc]
  rw [← Category.assoc e e', hid, Category.id_comp, ← Category.assoc g k, ← hnat, hXE,
    Category.assoc]

/-- **Restriction of a presheaf along an identification of objects, read through a functor.**
The transport `CategoryTheory.eqToHom` of an equality of objects of the source category, pushed
through a functor and then through a presheaf, is the transport of the resulting equality of
sections. It is `rfl` once the equality is substituted, and it is stated with the target equality
as an argument because two transports with the same endpoints are definitionally equal. -/
theorem map_op_map_eqToHom {𝒞 : Type*} [Category* 𝒞] {𝒟 : Type*} [Category* 𝒟]
    {A : Type*} [Category* A] (G : 𝒞 ⥤ 𝒟) (P : 𝒟ᵒᵖ ⥤ A) {U V : 𝒞} (h : U = V)
    (h' : P.obj (op (G.obj V)) = P.obj (op (G.obj U))) :
    P.map ((G.map (eqToHom h)).op) = eqToHom h' := by
  subst h
  rw [eqToHom_refl, G.map_id, op_id, P.map_id]
  exact (eqToHom_refl _ h').symm

section DirTransition

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{u}) (A : Type w)
  [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint]

/-- **The transition datum of a system of étale sheaves, in the direct-image form.** The datum
`Stacks.EtaleCohomology.EtaleSheafSystem` carries is a map `f_a^{-1}F_j ⟶ F_i` out of an inverse
image; its transpose across `Stacks.EtaleCohomology.systemAdjunction` is a map
`F_j ⟶ f_{a, *}F_i` into a direct image, which is the form
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem` asks for. -/
def systemDirTransition (F : EtaleSheafSystem D A) {i j : Iᵒᵖ} (a : i ⟶ j) :
    F.obj j ⟶ (systemPushforward D A a).obj (F.obj i) :=
  (systemAdjunction D A a).homEquiv (F.obj j) (F.obj i) (F.map a)

/-- The transition datum of a system, recovered from its direct-image form. -/
theorem homEquiv_symm_systemDirTransition (F : EtaleSheafSystem D A) {i j : Iᵒᵖ} (a : i ⟶ j) :
    ((systemAdjunction D A a).homEquiv (F.obj j) (F.obj i)).symm
        (systemDirTransition D A F a) = F.map a :=
  ((systemAdjunction D A a).homEquiv (F.obj j) (F.obj i)).symm_apply_apply (F.map a)

/-- **The cocycle law of a system of étale sheaves, in the direct-image form.** The cocycle
condition `Stacks.EtaleCohomology.EtaleSheafSystem.map_comp` imposes on the inverse-image datum,
transposed: the transition along a composite is the composite of the transitions, read through
the comparison `Stacks.EtaleCohomology.systemPushforwardComp` of the direct images.

Here `Stacks.EtaleCohomology.systemPullbackComp` is the comparison of left adjoints induced by
`systemPushforwardComp`, so the two cocycle conditions are the same equation read on the two sides
of the adjunction. -/
theorem systemDirTransition_comp (F : EtaleSheafSystem D A) {i j k : Iᵒᵖ} (a : i ⟶ j)
    (b : j ⟶ k) :
    systemDirTransition D A F (a ≫ b) =
      systemDirTransition D A F b ≫
        (systemPushforward D A b).map (systemDirTransition D A F a) ≫
          (systemPushforwardComp D A a b).hom.app (F.obj i) := by
  have key := leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D A b)
    (systemAdjunction D A a) (systemAdjunction D A (a ≫ b)) (systemPushforwardComp D A a b)
    (systemDirTransition D A F b) (systemDirTransition D A F a)
  rw [homEquiv_symm_systemDirTransition, homEquiv_symm_systemDirTransition] at key
  have hmap : ((systemAdjunction D A b).leftAdjointCompIso (systemAdjunction D A a)
        (systemAdjunction D A (a ≫ b)) (systemPushforwardComp D A a b)).inv.app (F.obj k) ≫
      (systemPullback D A a).map (F.map b) ≫ F.map a = F.map (a ≫ b) := F.map_comp a b
  rw [hmap] at key
  rw [systemDirTransition, key, Equiv.apply_symm_apply]

/-- **The cocycle law of a system of étale sheaves at an arrow presented as a composite**, with
the comparison of the direct images written through the *named* composite morphism of schemes
`Stacks.EtaleCohomology.smallEtalePushforwardComp'`.

This is `Stacks.EtaleCohomology.systemDirTransition_comp` with the composite generalised, which is
what lets it be used at an arrow of the index that is the image of a composite under a functor:
there the composite of the images and the image of the composite are equal arrows but not the same
term, and the type of `systemDirTransition` depends on the term. -/
theorem systemDirTransition_comp' (F : EtaleSheafSystem D A) {i j k : Iᵒᵖ} (a : i ⟶ j)
    (b : j ⟶ k) (ab : i ⟶ k) (hab : a ≫ b = ab)
    (hmap : D.map ab = D.map a ≫ D.map b) :
    systemDirTransition D A F ab =
      systemDirTransition D A F b ≫
        (systemPushforward D A b).map (systemDirTransition D A F a) ≫
          (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map ab) hmap A).hom.app (F.obj i) := by
  subst hab
  exact systemDirTransition_comp D A F a b

end DirTransition

/-! ### The presentation of an arbitrary system, with the inverse images removed -/

section DirectImageForm

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{u}} (c : Cone D)

/-- **The compatibility of a family of maps out of the inverse images of an ARBITRARY system is
the compatibility of the adjoint family of maps of direct images.**

`Stacks.EtaleCohomology.LimitHigherDirectImage.compatible_iff` is this statement at the system of
direct images `Stacks.EtaleCohomology.directImageSystem`, where the transition datum is the
comparison `Stacks.EtaleCohomology.coneDirectImageComp` itself; at an arbitrary system the
transition datum is `Stacks.EtaleCohomology.systemDirTransition`, the transpose of the datum
`Stacks.EtaleCohomology.EtaleSheafSystem` carries, and the identity is the same hexagon
`Stacks.EtaleCohomology.leftAdjointCompIso_inv_homEquiv_symm` read at it. Nothing is assumed:
`Stacks.EtaleCohomology.conePullbackComp` *is* the comparison of left adjoints induced by
`Stacks.EtaleCohomology.coneDirectImageCompAb`, so the two compatibilities are one equation read
on the two sides of the adjunction.

**Why this lives here.** It is the general-system form of
`Stacks.EtaleCohomology.LimitHigherDirectImage.compatible_iff`, which the tree states at
`Stacks.EtaleCohomology.directImageSystem` — the canonical system of direct images — and there
only. The two are not the same statement: this one quantifies over an arbitrary system, an
arbitrary abelian sheaf on the limit and an arbitrary family, and its transition datum is
`systemDirTransition` rather than the comparison `Stacks.EtaleCohomology.coneDirectImageComp`
itself. It cannot be placed downstream of this module either:
`Stacks.EtaleCohomology.systemDirTransition` is defined here and occurs nowhere else, so a module
stating this iff would have to import this one and could not be cited back from it. -/
theorem compatible_iff_systemDirTransition (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (σ : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforwardAb (c.π.app i)).obj 𝒢) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    ((conePullbackComp c a).inv.app (F.obj j) ≫
          (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫
            ((smallEtaleAdjunctionAb (c.π.app i)).homEquiv (F.obj i) 𝒢).symm (σ i) =
        ((smallEtaleAdjunctionAb (c.π.app j)).homEquiv (F.obj j) 𝒢).symm (σ j)) ↔
      σ j = systemDirTransition D AddCommGrpCat.{u + 1} F a ≫
        (systemPushforward D AddCommGrpCat.{u + 1} a).map (σ i) ≫
          (coneDirectImageCompAb c a).hom.app 𝒢 := by
  rw [← homEquiv_symm_systemDirTransition D AddCommGrpCat.{u + 1} F a,
    show (conePullbackComp c a).inv.app (F.obj j) ≫
        (smallEtalePullbackAb (c.π.app i)).map
            (((systemAdjunction D AddCommGrpCat.{u + 1} a).homEquiv (F.obj j) (F.obj i)).symm
              (systemDirTransition D AddCommGrpCat.{u + 1} F a)) ≫
          ((smallEtaleAdjunctionAb (c.π.app i)).homEquiv (F.obj i) 𝒢).symm (σ i) = _ from
      leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D AddCommGrpCat.{u + 1} a)
        (smallEtaleAdjunctionAb (c.π.app i)) (smallEtaleAdjunctionAb (c.π.app j))
        (coneDirectImageCompAb c a) (systemDirTransition D AddCommGrpCat.{u + 1} F a) (σ i)]
  exact (Equiv.apply_eq_iff_eq _).trans eq_comm

/-- **The presentation of an arbitrary system, with the inverse images removed.** If the legs
`ι_i : f_i^{-1}F_i ⟶ 𝓕` exhibit `𝓕 = colim_i f_i^{-1}F_i` in the sense of
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation`, then every family
of maps of direct images `σ_i : F_i ⟶ f_{i, *}H` compatible with
`Stacks.EtaleCohomology.systemDirTransition` factors uniquely through the transposed legs.

Only direct images occur on the right: no inverse image, no left adjoint and no sheafification.
This is the arbitrary-system counterpart of
`Stacks.EtaleCohomology.LimitHigherDirectImage.isPullbackColimitPresentation_iff`, whose two
ingredients it reuses — `compatible_iff_systemDirTransition` for the compatibility and
`CategoryTheory.Adjunction.homEquiv_naturality_right` for the factorisation, which at the system
of direct images is `Stacks.EtaleCohomology.counit_comp_eq_iff`. The morphism `χ` is the same on
both sides. -/
theorem existsUnique_desc_dir_of_isPullbackColimitPresentation
    (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (𝓕 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (h : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι)
    (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (σ : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforwardAb (c.π.app i)).obj H)
    (hσ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      σ j = systemDirTransition D AddCommGrpCat.{u + 1} F a ≫
        (systemPushforward D AddCommGrpCat.{u + 1} a).map (σ i) ≫
          (coneDirectImageCompAb c a).hom.app H) :
    ∃! χ : 𝓕 ⟶ H, ∀ i : Iᵒᵖ,
      (smallEtaleAdjunctionAb (c.π.app i)).homEquiv (F.obj i) 𝓕 (ι i) ≫
        (smallEtalePushforwardAb (c.π.app i)).map χ = σ i := by
  obtain ⟨χ, hχ, hu⟩ := h H
    (fun i => ((smallEtaleAdjunctionAb (c.π.app i)).homEquiv (F.obj i) H).symm (σ i))
    (fun a => (compatible_iff_systemDirTransition c F H σ a).mpr (hσ a))
  refine ⟨χ, fun i => ?_, fun y hy => hu y fun i => ?_⟩
  · rw [← Adjunction.homEquiv_naturality_right, hχ i, Equiv.apply_symm_apply]
  · refine ((smallEtaleAdjunctionAb (c.π.app i)).homEquiv (F.obj i) H).injective ?_
    rw [Adjunction.homEquiv_naturality_right, hy i, Equiv.apply_symm_apply]

end DirectImageForm

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex levelToSmallEtale transitionScheme)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)]

/-- **The transition morphisms of schemes compose.** The transition between two levels is
`D.map` of the arrow `(affineEtaleSiteColimit …).indexEquiv` assigns to an arrow of the index, and
both are functorial. -/
theorem transitionScheme_comp {n m p : (sys D c B hD hX hc).I} (a : n ⟶ m) (b : m ⟶ p) :
    transitionScheme D c B hD hX hc (a ≫ b) =
      transitionScheme D c B hD hX hc a ≫ transitionScheme D c B hD hX hc b := by
  show D.map ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map (a ≫ b)) =
    D.map ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a) ≫
      D.map ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map b)
  rw [Functor.map_comp, D.map_comp]

/-- **The first projection of the left-hand side of the transition cocycle**, entirely inside
`AlgebraicGeometry.Scheme`: it is the stored projection of the composite transition. -/
theorem levelTransitionCocycle_lhs_fst {n m p : (sys D c B hD hX hc).I} (a : n ⟶ m) (b : m ⟶ p)
    (Y : (sys D c B hD hX hc).C p) :
    ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback (a ≫ b) Y).isoPullback.hom ≫
        pullback.fst (levelStruct D c B hD hX hc p Y)
          (transitionScheme D c B hD hX hc (a ≫ b)) =
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst (a ≫ b)).app Y :=
  IsPullback.isoPullback_hom_fst _

/-- **The first projection of the right-hand side of the transition cocycle**, entirely inside
`AlgebraicGeometry.Scheme`. The three comparison morphisms are taken as variables constrained only
by their first projections: the transport along the strictness field `comp` of the system by the
compatibility `heL` that
`Stacks.EtaleCohomology.AffineEtaleSiteColimit.transitionFst_comp` provides, the action of base
change on a morphism by `Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst`, and the
composite base-change comparison by
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_inv_fst`. -/
theorem levelTransitionCocycle_rhs_fst {n m p : (sys D c B hD hX hc).I} (a : n ⟶ m) (b : m ⟶ p)
    (Y : (sys D c B hD hX hc).C p)
    (eL : (levelToScheme D c B hD hX hc n).obj (((sys D c B hD hX hc).u (a ≫ b)).obj Y) ⟶
      (levelToScheme D c B hD hX hc n).obj
        (((sys D c B hD hX hc).u a).obj (((sys D c B hD hX hc).u b).obj Y)))
    (heL : eL ≫ ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app
          (((sys D c B hD hX hc).u b).obj Y) ≫
        ((affineEtaleSiteColimit D c B hD hX hc).transitionFst b).app Y =
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst (a ≫ b)).app Y)
    (m₁ : pullback (levelStruct D c B hD hX hc m (((sys D c B hD hX hc).u b).obj Y))
          (transitionScheme D c B hD hX hc a) ⟶
        pullback (pullback.snd (levelStruct D c B hD hX hc p Y)
            (transitionScheme D c B hD hX hc b))
          (transitionScheme D c B hD hX hc a))
    (m₂ : (levelToScheme D c B hD hX hc n).obj
          (((sys D c B hD hX hc).u a).obj (((sys D c B hD hX hc).u b).obj Y)) ⟶
        pullback (levelStruct D c B hD hX hc m (((sys D c B hD hX hc).u b).obj Y))
          (transitionScheme D c B hD hX hc a))
    (hm₂ : m₂ ≫ pullback.fst (levelStruct D c B hD hX hc m
            (((sys D c B hD hX hc).u b).obj Y)) (transitionScheme D c B hD hX hc a) =
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app
        (((sys D c B hD hX hc).u b).obj Y))
    (eb : (levelToScheme D c B hD hX hc m).obj (((sys D c B hD hX hc).u b).obj Y) ⟶
      pullback (levelStruct D c B hD hX hc p Y) (transitionScheme D c B hD hX hc b))
    (hm₁ : m₁ ≫ pullback.fst (pullback.snd (levelStruct D c B hD hX hc p Y)
            (transitionScheme D c B hD hX hc b)) (transitionScheme D c B hD hX hc a) =
      pullback.fst (levelStruct D c B hD hX hc m (((sys D c B hD hX hc).u b).obj Y))
          (transitionScheme D c B hD hX hc a) ≫ eb)
    (heb : eb ≫ pullback.fst (levelStruct D c B hD hX hc p Y)
          (transitionScheme D c B hD hX hc b) =
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst b).app Y)
    (m₃ : pullback (pullback.snd (levelStruct D c B hD hX hc p Y)
            (transitionScheme D c B hD hX hc b))
          (transitionScheme D c B hD hX hc a) ⟶
        pullback (levelStruct D c B hD hX hc p Y)
          (transitionScheme D c B hD hX hc (a ≫ b)))
    (hm₃ : m₃ ≫ pullback.fst (levelStruct D c B hD hX hc p Y)
            (transitionScheme D c B hD hX hc (a ≫ b)) =
      pullback.fst (pullback.snd (levelStruct D c B hD hX hc p Y)
          (transitionScheme D c B hD hX hc b)) (transitionScheme D c B hD hX hc a) ≫
        pullback.fst (levelStruct D c B hD hX hc p Y)
          (transitionScheme D c B hD hX hc b)) :
    (eL ≫ m₂ ≫ m₁ ≫ m₃) ≫ pullback.fst (levelStruct D c B hD hX hc p Y)
        (transitionScheme D c B hD hX hc (a ≫ b)) =
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst (a ≫ b)).app Y := by
  simp only [Category.assoc]
  rw [hm₃, ← Category.assoc m₁, hm₁]
  simp only [Category.assoc]
  rw [heb, ← Category.assoc m₂, hm₂]
  exact heL

/-- The component of the level-transition identification, read on underlying schemes. -/
theorem levelTransitionIso_hom_app_left {n m : (sys D c B hD hX hc).I} (a : n ⟶ m)
    (Y : (sys D c B hD hX hc).C m) :
    ((levelTransitionIso D c B hD hX hc a).hom.app Y).left =
      ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y).isoPullback.hom :=
  rfl

/-- **THE TRANSITION COCYCLE of the level-side identification.** For composable arrows
`a : n ⟶ m` and `b : m ⟶ p` of the index of the system of [Stacks, Tag 0EYL], the identification
`Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso` of the level transition with
base change along the transition morphism of schemes satisfies the cocycle condition: the
identification at `a ≫ b` is the transport along the strictness field
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.comp` of the system, followed by
the identification at `a`, the base change along the transition at `a` of the identification at
`b`, and the comparison `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'` of base change along
the composite transition with the composite of the two base changes.

This is the level-transition counterpart of
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition_hom_app`, which
does the same for the projections of the cone, and it is what makes the étale transition data of a
system satisfy the cocycle law of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem` once read on
the levels.

Nothing is assumed. Both sides are morphisms into a base change along the composite transition, so
`Stacks.EtaleCohomology.smallEtaleBaseChange_hom_ext` reduces the statement to one projection, and
there the left-hand side is the stored projection
`Stacks.EtaleCohomology.AffineEtaleSiteColimit.transitionFst` of the composite while the
right-hand side is its factorisation
`Stacks.EtaleCohomology.AffineEtaleSiteColimit.transitionFst_comp`, which [Stacks, Tag 0EYL]
supplies as data. -/
theorem levelTransitionIso_hom_app_comp {n m p : (sys D c B hD hX hc).I} (a : n ⟶ m) (b : m ⟶ p)
    (Y : (sys D c B hD hX hc).C p) :
    (levelTransitionIso D c B hD hX hc (a ≫ b)).hom.app Y =
      (levelEtaleSite D c B hD hX hc n).map
          (eqToHom (Functor.congr_obj ((sys D c B hD hX hc).comp a b) Y)) ≫
        (levelTransitionIso D c B hD hX hc a).hom.app (((sys D c B hD hX hc).u b).obj Y) ≫
          (Stacks.EtaleCohomology.smallEtaleBaseChange
                (transitionScheme D c B hD hX hc a)).map
              ((levelTransitionIso D c B hD hX hc b).hom.app Y) ≫
            (Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
                (transitionScheme D c B hD hX hc a) (transitionScheme D c B hD hX hc b)
                (transitionScheme D c B hD hX hc (a ≫ b))
                (transitionScheme_comp D c B hD hX hc a b)).inv.app
              ((levelEtaleSite D c B hD hX hc p).obj Y) := by
  refine Stacks.EtaleCohomology.smallEtaleBaseChange_hom_ext
    (transitionScheme D c B hD hX hc (a ≫ b)) ?_
  rw [levelTransitionIso_hom_app_left, comp_left_etale, comp_left_etale, comp_left_etale]
  refine (levelTransitionCocycle_lhs_fst D c B hD hX hc a b Y).trans
    (levelTransitionCocycle_rhs_fst D c B hD hX hc a b Y _
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst_comp a b Y).symm
      _ _ (IsPullback.isoPullback_hom_fst _) _
      (Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst
        (transitionScheme D c B hD hX hc a)
        ((levelTransitionIso D c B hD hX hc b).hom.app Y))
      (IsPullback.isoPullback_hom_fst _) _
      (Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_inv_fst
        (transitionScheme D c B hD hX hc a) (transitionScheme D c B hD hX hc b)
        (transitionScheme D c B hD hX hc (a ≫ b))
        (transitionScheme_comp D c B hD hX hc a b)
        ((levelEtaleSite D c B hD hX hc p).obj Y))).symm

/-! ### The transition datum of a system, at the levels -/

/-- **Restriction of abelian sheaves from Mathlib's small étale site of `X_n` to the level `n` of
[Stacks, Tag 0EYL].** This is the functor
`Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionAb` says is an
equivalence, named so that the continuity instance is introduced once. -/
abbrev levelEtaleRestrictAb (n : (sys D c B hD hX hc).I) :
    Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology
        (D.obj (levelIndex D c B hD hX hc n))) AddCommGrpCat.{max u v + 1} ⥤
      Sheaf ((sys D c B hD hX hc).J n) AddCommGrpCat.{max u v + 1} :=
  letI := isContinuous_levelToEtaleSite D c B hD hX hc n
  (levelEtaleSite D c B hD hX hc n).sheafPushforwardContinuous AddCommGrpCat.{max u v + 1}
    ((sys D c B hD hX hc).J n)
    (AlgebraicGeometry.Scheme.smallEtaleTopology (D.obj (levelIndex D c B hD hX hc n)))

/-- Reading an abelian sheaf of the small étale site of `X_n` on the level does not change its
sections: the underlying presheaf is restriction along the level crossing, on the nose. -/
theorem levelEtaleRestrictAb_obj (n : (sys D c B hD hX hc).I)
    (F : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology
      (D.obj (levelIndex D c B hD hX hc n))) AddCommGrpCat.{max u v + 1}) :
    ((levelEtaleRestrictAb D c B hD hX hc n).obj F).obj =
      (levelEtaleSite D c B hD hX hc n).op ⋙ F.obj :=
  rfl

variable (F : Stacks.EtaleCohomology.EtaleSheafSystem D AddCommGrpCat.{max u v + 1})

/-- **The transition datum of a system of étale sheaves between two levels of
[Stacks, Tag 0EYL], in the direct-image form.** For an arrow `a : n ⟶ m` of the index of the
system of sites, the map `F_m ⟶ t_{a, *}F_n` into the direct image along the transition morphism
of schemes between the two stages: it is
`Stacks.EtaleCohomology.systemDirTransition` at the arrow of `Iᵒᵖ` that
`(affineEtaleSiteColimit …).indexEquiv` assigns to `a`, the two being definitionally the same
datum, `Stacks.EtaleCohomology.QcSeparatedColimit.transitionScheme` being `D.map` of that
arrow. -/
def levelDirTransition {n m : (sys D c B hD hX hc).I} (a : n ⟶ m) :
    F.obj (levelIndex D c B hD hX hc m) ⟶
      (Stacks.EtaleCohomology.smallEtalePushforward (transitionScheme D c B hD hX hc a)
        AddCommGrpCat.{max u v + 1}).obj (F.obj (levelIndex D c B hD hX hc n)) :=
  Stacks.EtaleCohomology.systemDirTransition D AddCommGrpCat.{max u v + 1} F
    ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a)

/-- **The cocycle law of the transition datum of a system, at the levels.** The transition along a
composite arrow of the index is the composite of the transitions, read through the comparison
`Stacks.EtaleCohomology.smallEtalePushforwardComp'` of the direct images along the composite
transition morphism of schemes.

This is `Stacks.EtaleCohomology.systemDirTransition_comp'` at the arrow
`(affineEtaleSiteColimit …).indexEquiv.functor.map a`; the generalised form is what is needed,
because the functor's image of a composite and the composite of its images are equal arrows of
`Iᵒᵖ` and not the same term. Together with
`Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso_hom_app_comp` this is the whole
of the cocycle law that
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem` asks for on
the levels: that one identifies the two readings of the level transition, this one the two
readings of the sheaf transition. -/
theorem levelDirTransition_comp {n m p : (sys D c B hD hX hc).I} (a : n ⟶ m) (b : m ⟶ p) :
    levelDirTransition D c B hD hX hc F (a ≫ b) =
      levelDirTransition D c B hD hX hc F b ≫
        (Stacks.EtaleCohomology.smallEtalePushforward (transitionScheme D c B hD hX hc b)
            AddCommGrpCat.{max u v + 1}).map (levelDirTransition D c B hD hX hc F a) ≫
          (Stacks.EtaleCohomology.smallEtalePushforwardComp'
              (transitionScheme D c B hD hX hc a) (transitionScheme D c B hD hX hc b)
              (transitionScheme D c B hD hX hc (a ≫ b))
              (transitionScheme_comp D c B hD hX hc a b)
              AddCommGrpCat.{max u v + 1}).hom.app (F.obj (levelIndex D c B hD hX hc n)) :=
  Stacks.EtaleCohomology.systemDirTransition_comp' D AddCommGrpCat.{max u v + 1} F
    ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a)
    ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map b)
    ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map (a ≫ b))
    (Functor.map_comp _ a b).symm (transitionScheme_comp D c B hD hX hc a b)

/-! ### The cocycle system on the levels -/

/-- **The transition datum of the cocycle system a system of étale sheaves becomes on the levels
of [Stacks, Tag 0EYL].** The direct-image transition of the system, restricted along the level
crossing at the later level and transported along the identification
`Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso` of the level transition with
base change. -/
def levelCocycleMap {n m : (sys D c B hD hX hc).I} (a : n ⟶ m) :
    ((levelEtaleRestrictAb D c B hD hX hc m).obj
        (F.obj (levelIndex D c B hD hX hc m))).obj ⟶
      ((sys D c B hD hX hc).u a).op ⋙
        ((levelEtaleRestrictAb D c B hD hX hc n).obj
          (F.obj (levelIndex D c B hD hX hc n))).obj :=
  Functor.whiskerLeft (levelEtaleSite D c B hD hX hc m).op
      (levelDirTransition D c B hD hX hc F a).hom ≫
    Functor.whiskerRight (NatTrans.op (levelTransitionIso D c B hD hX hc a).hom)
      (F.obj (levelIndex D c B hD hX hc n)).obj

/-- The transition datum of the level cocycle system, over an object of the level. -/
theorem levelCocycleMap_app {n m : (sys D c B hD hX hc).I} (a : n ⟶ m)
    (Y : (sys D c B hD hX hc).C m) :
    (levelCocycleMap D c B hD hX hc F a).app (op Y) =
      (levelDirTransition D c B hD hX hc F a).hom.app
          (op ((levelEtaleSite D c B hD hX hc m).obj Y)) ≫
        (F.obj (levelIndex D c B hD hX hc n)).obj.map
          ((levelTransitionIso D c B hD hX hc a).hom.app Y).op :=
  rfl

/-- The level cocycle map along a composite is the composite of the level cocycle maps, up to the
identification of the composite transition functors. -/
theorem levelCocycleMap_comp {n m p : (sys D c B hD hX hc).I} (a : n ⟶ m) (b : m ⟶ p) :
    levelCocycleMap D c B hD hX hc F (a ≫ b) =
      (levelCocycleMap D c B hD hX hc F b ≫
          Functor.whiskerLeft ((sys D c B hD hX hc).u b).op
            (levelCocycleMap D c B hD hX hc F a)) ≫
        eqToHom (congrArg (fun H : (sys D c B hD hX hc).C p ⥤ (sys D c B hD hX hc).C n =>
            H.op ⋙ ((levelEtaleRestrictAb D c B hD hX hc n).obj
              (F.obj (levelIndex D c B hD hX hc n))).obj)
          ((sys D c B hD hX hc).comp a b).symm) := by
  refine NatTrans.ext (funext fun U => ?_)
  obtain ⟨Y⟩ := U
  have hcc : ((Stacks.EtaleCohomology.smallEtalePushforwardComp'
          (transitionScheme D c B hD hX hc a) (transitionScheme D c B hD hX hc b)
          (transitionScheme D c B hD hX hc (a ≫ b))
          (transitionScheme_comp D c B hD hX hc a b)
          AddCommGrpCat.{max u v + 1}).hom.app
        (F.obj (levelIndex D c B hD hX hc n))).hom.app
        (op ((levelEtaleSite D c B hD hX hc p).obj Y)) =
      (F.obj (levelIndex D c B hD hX hc n)).obj.map
        ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
            (transitionScheme D c B hD hX hc a) (transitionScheme D c B hD hX hc b)
            (transitionScheme D c B hD hX hc (a ≫ b))
            (transitionScheme_comp D c B hD hX hc a b)).hom.app
          ((levelEtaleSite D c B hD hX hc p).obj Y)).op :=
    Category.id_comp _
  have hpush : ((Stacks.EtaleCohomology.smallEtalePushforward
            (transitionScheme D c B hD hX hc b) AddCommGrpCat.{max u v + 1}).map
          (levelDirTransition D c B hD hX hc F a)).hom.app
        (op ((levelEtaleSite D c B hD hX hc p).obj Y)) =
      (levelDirTransition D c B hD hX hc F a).hom.app
        (op ((Stacks.EtaleCohomology.smallEtaleBaseChange
          (transitionScheme D c B hD hX hc b)).obj
          ((levelEtaleSite D c B hD hX hc p).obj Y))) :=
    rfl
  have hid : (F.obj (levelIndex D c B hD hX hc n)).obj.map
        ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
            (transitionScheme D c B hD hX hc a) (transitionScheme D c B hD hX hc b)
            (transitionScheme D c B hD hX hc (a ≫ b))
            (transitionScheme_comp D c B hD hX hc a b)).hom.app
          ((levelEtaleSite D c B hD hX hc p).obj Y)).op ≫
      (F.obj (levelIndex D c B hD hX hc n)).obj.map
        ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
            (transitionScheme D c B hD hX hc a) (transitionScheme D c B hD hX hc b)
            (transitionScheme D c B hD hX hc (a ≫ b))
            (transitionScheme_comp D c B hD hX hc a b)).inv.app
          ((levelEtaleSite D c B hD hX hc p).obj Y)).op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id]
    exact (F.obj (levelIndex D c B hD hX hc n)).obj.map_id _
  have hnat : (F.obj (levelIndex D c B hD hX hc m)).obj.map
          ((levelTransitionIso D c B hD hX hc b).hom.app Y).op ≫
        (levelDirTransition D c B hD hX hc F a).hom.app
          (op ((levelEtaleSite D c B hD hX hc m).obj (((sys D c B hD hX hc).u b).obj Y))) =
      (levelDirTransition D c B hD hX hc F a).hom.app
          (op ((Stacks.EtaleCohomology.smallEtaleBaseChange
            (transitionScheme D c B hD hX hc b)).obj
            ((levelEtaleSite D c B hD hX hc p).obj Y))) ≫
        (F.obj (levelIndex D c B hD hX hc n)).obj.map
          ((Stacks.EtaleCohomology.smallEtaleBaseChange
            (transitionScheme D c B hD hX hc a)).map
            ((levelTransitionIso D c B hD hX hc b).hom.app Y)).op :=
    (levelDirTransition D c B hD hX hc F a).hom.naturality
      ((levelTransitionIso D c B hD hX hc b).hom.app Y).op
  rw [levelCocycleMap_app, levelDirTransition_comp, levelTransitionIso_hom_app_comp]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.op_obj, unop_op, levelCocycleMap_app, op_comp,
    Functor.map_comp, Category.assoc, eqToHom_app, hcc, hpush]
  exact Stacks.EtaleCohomology.assoc_cancel_of_naturality hid hnat
    (Stacks.EtaleCohomology.map_op_map_eqToHom (levelEtaleSite D c B hD hX hc n)
      (F.obj (levelIndex D c B hD hX hc n)).obj
      (Functor.congr_obj ((sys D c B hD hX hc).comp a b) Y) _)

/-- **A system of abelian étale sheaves on an inverse system of schemes, read as cocycle data on
the levels of [Stacks, Tag 0EYL].** The sheaf at a level is the restriction of the system's sheaf
on Mathlib's small étale site of the level's own stage along the level crossing, and the transition
datum is `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleMap`. -/
def levelCocycleSystem :
    InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) where
  obj n := (levelEtaleRestrictAb D c B hD hX hc n).obj (F.obj (levelIndex D c B hD hX hc n))
  map a := levelCocycleMap D c B hD hX hc F a
  map_comp a b := levelCocycleMap_comp D c B hD hX hc F a b

/-- The sheaf of the level cocycle system at a level `n` is the restriction of the system's sheaf
at the index of `n`. -/
theorem levelCocycleSystem_obj (n : (sys D c B hD hX hc).I) :
    (levelCocycleSystem D c B hD hX hc F).obj n =
      (levelEtaleRestrictAb D c B hD hX hc n).obj (F.obj (levelIndex D c B hD hX hc n)) :=
  rfl

/-- The transition datum of the level cocycle system is `levelCocycleMap`. -/
theorem levelCocycleSystem_map {n m : (sys D c B hD hX hc).I} (a : n ⟶ m) :
    (levelCocycleSystem D c B hD hX hc F).map a = levelCocycleMap D c B hD hX hc F a :=
  rfl

end Stacks.EtaleCohomology.AffineLimitCohomology

end
