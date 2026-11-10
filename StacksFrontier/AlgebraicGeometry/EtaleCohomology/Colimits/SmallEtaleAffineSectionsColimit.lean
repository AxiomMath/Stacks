module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# A sheaf that is a filtered colimit on affine sections

Let `X` be a scheme, `(A_j)` a family of abelian sheaves on its small étale site indexed by a
directed category, with transition maps `A_j ⟶ A_k` for `k ⟶ j`, and `λ_j : A_j ⟶ P` maps
compatible with the transitions. Suppose that over every affine object `V` of the site the
`λ_j` exhibit `P(V)` as the filtered colimit of the `A_j(V)`: every section of `P` over `V` is
`λ_j` of a section of some `A_j`, and a section killed by `λ_j` is killed by a transition. Then
maps out of `P` are the compatible families of maps out of the `A_j`
(`existsUnique_desc_of_affineSections`).

The affine objects form a cover-dense subsite (`AlgebraicGeometry.Scheme.AffineEtale.Spec`), so a
map of sheaves is determined by, and can be glued from, its components over affine objects; over
each affine object the colimit description supplies them.

This is the shape in which the degree-zero case of [Stacks, Tag 0EYM] is proved: there `P` is the
direct image `f_{i, *}𝓕` and the `A_j` are the direct images of the `F_j`, and the colimit
description on affine sections is [Stacks, Tag 09YQ] in degree zero.

## Main results

* `Stacks.EtaleCohomology.sheafHom_ext_of_affineEtale` — maps of sheaves agreeing over the affine
  objects agree.
* `Stacks.EtaleCohomology.existsUnique_desc_of_affineSections` — **the universal property.**

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}}

/-- **Maps of abelian sheaves on the small étale site agreeing over the affine objects agree**:
the affine objects form a cover-dense subsite. -/
theorem sheafHom_ext_of_affineEtale {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    {σ₁ σ₂ : F ⟶ G}
    (h : ∀ W : X.AffineEtale, σ₁.hom.app (op ((AffineEtale.Spec X).obj W)) =
      σ₂.hom.app (op ((AffineEtale.Spec X).obj W))) : σ₁ = σ₂ := by
  refine (sheafToPresheaf (smallEtaleTopology X) Ab.{u + 1}).map_injective ?_
  have key := fun σ : F ⟶ G => Functor.IsCoverDense.sheafHom_eq (AffineEtale.Spec X)
    (K := smallEtaleTopology X) ((sheafToPresheaf (smallEtaleTopology X) Ab.{u + 1}).map σ)
  rw [← key σ₁, ← key σ₂]
  congr 1
  ext W : 2
  exact h W.unop

variable {J : Type w} [Category J] {A : J → Sheaf (smallEtaleTopology X) Ab.{u + 1}}
  {P Q : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
  (T : ∀ {j k : J}, (k ⟶ j) → (A j ⟶ A k)) (lg : ∀ j, A j ⟶ P)
  (hdir : ∀ j j' : J, ∃ (k : J) (_ : k ⟶ j) (_ : k ⟶ j'), True)
  (hlg : ∀ {j k : J} (a : k ⟶ j), T a ≫ lg k = lg j)
  (hsurj : ∀ (W : X.AffineEtale) (x : P.obj.obj (op ((AffineEtale.Spec X).obj W))),
    ∃ (j : J) (t : (A j).obj.obj (op ((AffineEtale.Spec X).obj W))),
      (lg j).hom.app (op ((AffineEtale.Spec X).obj W)) t = x)
  (hinj : ∀ (W : X.AffineEtale) (j : J) (t : (A j).obj.obj (op ((AffineEtale.Spec X).obj W))),
    (lg j).hom.app (op ((AffineEtale.Spec X).obj W)) t = 0 →
      ∃ (k : J) (a : k ⟶ j), (T a).hom.app (op ((AffineEtale.Spec X).obj W)) t = 0)
  (μ : ∀ j, A j ⟶ Q) (hμ : ∀ {j k : J} (a : k ⟶ j), T a ≫ μ k = μ j)

include hdir hlg hinj hμ in
/-- Two sections of the `A_j` over an affine object with the same image in `P` have the same
image in `Q`. -/
theorem desc_wellDefined (W : X.AffineEtale) {j j' : J}
    (t : (A j).obj.obj (op ((AffineEtale.Spec X).obj W)))
    (t' : (A j').obj.obj (op ((AffineEtale.Spec X).obj W)))
    (h : (lg j).hom.app (op ((AffineEtale.Spec X).obj W)) t =
      (lg j').hom.app (op ((AffineEtale.Spec X).obj W)) t') :
    (μ j).hom.app (op ((AffineEtale.Spec X).obj W)) t =
      (μ j').hom.app (op ((AffineEtale.Spec X).obj W)) t' := by
  let U := op ((AffineEtale.Spec X).obj W)
  have comp : ∀ {B C D : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (f : B ⟶ C) (g : C ⟶ D)
      (x : B.obj.obj U), (f ≫ g).hom.app U x = g.hom.app U (f.hom.app U x) := fun _ _ _ => rfl
  obtain ⟨k, a, a', -⟩ := hdir j j'
  have e : (lg k).hom.app U ((T a).hom.app U t - (T a').hom.app U t') = 0 := by
    rw [map_sub, ← comp, ← comp, hlg, hlg, h, sub_self]
  obtain ⟨m, b, hb⟩ := hinj W k _ e
  rw [map_sub, sub_eq_zero] at hb
  rw [← hμ a, comp, ← hμ b, comp, hb, ← comp, hμ b, ← comp, hμ a']

/-- The function on sections over an affine object underlying the map out of `P` that the `μ_j`
induce: a section of `P` is `λ_j` of a section of some `A_j`, which `μ_j` carries to `Q`. -/
def descFun (W : X.AffineEtale) (x : P.obj.obj (op ((AffineEtale.Spec X).obj W))) :
    Q.obj.obj (op ((AffineEtale.Spec X).obj W)) :=
  (μ (hsurj W x).choose).hom.app _ (hsurj W x).choose_spec.choose

include hdir hlg hinj hμ in
/-- `descFun` carries `λ_j t` to `μ_j t` for every section `t` of `A_j` over an affine object. -/
theorem descFun_spec (W : X.AffineEtale) (j : J)
    (t : (A j).obj.obj (op ((AffineEtale.Spec X).obj W))) :
    descFun lg hsurj μ W ((lg j).hom.app _ t) = (μ j).hom.app _ t :=
  desc_wellDefined T lg hdir hlg hinj μ hμ W _ t
    (hsurj W ((lg j).hom.app _ t)).choose_spec.choose_spec

include hdir hlg hinj hμ in
/-- The component over an affine object of the map out of `P` that the `μ_j` induce. -/
def descApp (W : X.AffineEtale) :
    P.obj.obj (op ((AffineEtale.Spec X).obj W)) ⟶ Q.obj.obj (op ((AffineEtale.Spec X).obj W)) :=
  AddCommGrpCat.ofHom
    { toFun := descFun lg hsurj μ W
      map_zero' := by
        obtain ⟨j, t, ht⟩ := hsurj W 0
        have h0 : (lg j).hom.app (op ((AffineEtale.Spec X).obj W)) 0 = 0 := map_zero _
        rw [← h0, descFun_spec T lg hdir hlg hsurj hinj μ hμ, map_zero]
      map_add' := by
        intro x y
        obtain ⟨j, t, rfl⟩ := hsurj W x
        obtain ⟨j', t', rfl⟩ := hsurj W y
        obtain ⟨k, a, a', -⟩ := hdir j j'
        have comp : ∀ {B C D : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (f : B ⟶ C) (g : C ⟶ D)
            (z : B.obj.obj (op ((AffineEtale.Spec X).obj W))),
            (f ≫ g).hom.app _ z = g.hom.app _ (f.hom.app _ z) := fun _ _ _ => rfl
        rw [← hlg a, ← hlg a', comp, comp, ← map_add, descFun_spec T lg hdir hlg hsurj hinj μ hμ,
          descFun_spec T lg hdir hlg hsurj hinj μ hμ, descFun_spec T lg hdir hlg hsurj hinj μ hμ,
          map_add, ← comp, ← comp, hμ, hμ] }

include hdir hlg hinj hμ in
/-- `descApp` carries `λ_j t` to `μ_j t` for every section `t` of `A_j` over an affine object. -/
theorem descApp_apply (W : X.AffineEtale) (j : J)
    (t : (A j).obj.obj (op ((AffineEtale.Spec X).obj W))) :
    descApp T lg hdir hlg hsurj hinj μ hμ W ((lg j).hom.app _ t) = (μ j).hom.app _ t :=
  descFun_spec T lg hdir hlg hsurj hinj μ hμ W j t

include hdir hlg hinj hμ in
/-- The components over the affine objects, as a natural transformation of the restrictions to
the affine subsite. -/
def descRestrict :
    (AffineEtale.Spec X).op ⋙ P.obj ⟶ (AffineEtale.Spec X).op ⋙ Q.obj where
  app W := descApp T lg hdir hlg hsurj hinj μ hμ W.unop
  naturality W₁ W₂ g := by
    ext x
    obtain ⟨j, t, rfl⟩ := hsurj W₁.unop x
    change descApp T lg hdir hlg hsurj hinj μ hμ W₂.unop
        (P.obj.map ((AffineEtale.Spec X).op.map g) ((lg j).hom.app _ t)) =
      Q.obj.map ((AffineEtale.Spec X).op.map g) (descApp T lg hdir hlg hsurj hinj μ hμ W₁.unop
        ((lg j).hom.app _ t))
    rw [← NatTrans.naturality_apply (lg j).hom, descApp_apply]
    exact (descApp_apply T lg hdir hlg hsurj hinj μ hμ W₂.unop j _).trans
      (NatTrans.naturality_apply (μ j).hom _ t)

/-- The map out of `P` that the `μ_j` induce: the gluing of its components over the affine
objects. -/
def desc : P ⟶ Q :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) Ab.{u + 1}).preimage
    (Functor.IsCoverDense.sheafHom (G := AffineEtale.Spec X) (K := smallEtaleTopology X)
      (descRestrict T lg hdir hlg hsurj hinj μ hμ))

/-- The component of `desc` over an affine object is `descApp`. -/
theorem desc_app (W : X.AffineEtale) :
    (desc T lg hdir hlg hsurj hinj μ hμ).hom.app (op ((AffineEtale.Spec X).obj W)) =
      descApp T lg hdir hlg hsurj hinj μ hμ W := by
  have h := NatTrans.congr_app (Functor.IsCoverDense.sheafHom_restrict_eq
    (G := AffineEtale.Spec X) (K := smallEtaleTopology X)
    (descRestrict T lg hdir hlg hsurj hinj μ hμ)) (op W)
  refine Eq.trans ?_ h
  simp [desc]

include hdir hlg hsurj hinj hμ in
/-- **A sheaf that is a filtered colimit on affine sections has the universal property of the
colimit.** If over every affine object the `λ_j` exhibit the sections of `P` as the filtered
colimit of those of the `A_j`, then every family of maps `μ_j : A_j ⟶ Q` compatible with the
transitions factors uniquely through the `λ_j`. -/
theorem existsUnique_desc_of_affineSections :
    ∃! σ : P ⟶ Q, ∀ j, lg j ≫ σ = μ j := by
  refine ⟨desc T lg hdir hlg hsurj hinj μ hμ, fun j => sheafHom_ext_of_affineEtale fun W => ?_,
    fun σ' hσ' => sheafHom_ext_of_affineEtale fun W => ?_⟩
  · ext t
    change (desc T lg hdir hlg hsurj hinj μ hμ).hom.app _ ((lg j).hom.app _ t) = _
    rw [desc_app, descApp_apply]
  · ext x
    obtain ⟨j, t, rfl⟩ := hsurj W x
    rw [desc_app, descApp_apply]
    change ((lg j) ≫ σ').hom.app _ t = _
    rw [hσ' j]

end Stacks.EtaleCohomology

end
