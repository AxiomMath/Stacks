module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# A sheaf of sets that is a filtered colimit on affine sections

Let `X` be a scheme, `(A_j)` a family of sheaves of sets on its small étale site indexed by a
directed category, with transition maps `A_j ⟶ A_k` for `k ⟶ j`, and `λ_j : A_j ⟶ P` maps
compatible with the transitions. Suppose that over every affine object `V` of the site the `λ_j`
exhibit `P(V)` as the filtered colimit of the `A_j(V)`: every section of `P` over `V` is `λ_j` of
a section of some `A_j`, and two sections of `A_j` with the same image under `λ_j` have the same
image under some transition. Then maps out of `P` are the compatible families of maps out of the
`A_j` (`Stacks.EtaleCohomology.existsUnique_desc_of_affineSetSections`).

This is `Stacks.EtaleCohomology.existsUnique_desc_of_affineSections` for sheaves of sets, with the
same proof: the affine objects form a cover-dense subsite
(`AlgebraicGeometry.Scheme.AffineEtale.Spec`), so a map of sheaves is determined by, and can be
glued from, its components over affine objects, and over each affine object the colimit
description supplies them.

## Main results

* `Stacks.EtaleCohomology.sheafHom_ext_of_affineEtale_set` — maps of sheaves of sets agreeing over
  the affine objects agree.
* `Stacks.EtaleCohomology.existsUnique_desc_of_affineSetSections` — **the universal property.**

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}}

/-- **Maps of sheaves of sets on the small étale site agreeing over the affine objects agree**:
the affine objects form a cover-dense subsite. -/
theorem sheafHom_ext_of_affineEtale_set {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))}
    {σ₁ σ₂ : F ⟶ G}
    (h : ∀ W : X.AffineEtale, σ₁.hom.app (op ((AffineEtale.Spec X).obj W)) =
      σ₂.hom.app (op ((AffineEtale.Spec X).obj W))) : σ₁ = σ₂ := by
  refine (sheafToPresheaf (smallEtaleTopology X) (Type (u + 1))).map_injective ?_
  rw [← Functor.IsCoverDense.sheafHom_eq (AffineEtale.Spec X) (K := smallEtaleTopology X)
      ((sheafToPresheaf (smallEtaleTopology X) (Type (u + 1))).map σ₁),
    ← Functor.IsCoverDense.sheafHom_eq (AffineEtale.Spec X) (K := smallEtaleTopology X)
      ((sheafToPresheaf (smallEtaleTopology X) (Type (u + 1))).map σ₂)]
  congr 1
  ext W : 2
  exact h W.unop

variable {J : Type w} [Category J] {A : J → Sheaf (smallEtaleTopology X) (Type (u + 1))}
  {P Q : Sheaf (smallEtaleTopology X) (Type (u + 1))}
  (T : ∀ {j k : J}, (k ⟶ j) → (A j ⟶ A k)) (lg : ∀ j, A j ⟶ P)
  (hdir : ∀ j j' : J, ∃ (k : J) (_ : k ⟶ j) (_ : k ⟶ j'), True)
  (hlg : ∀ {j k : J} (a : k ⟶ j), T a ≫ lg k = lg j)
  (hsurj : ∀ (W : X.AffineEtale) (x : P.obj.obj (op ((AffineEtale.Spec X).obj W))),
    ∃ (j : J) (t : (A j).obj.obj (op ((AffineEtale.Spec X).obj W))),
      (lg j).hom.app (op ((AffineEtale.Spec X).obj W)) t = x)
  (hinj : ∀ (W : X.AffineEtale) (j : J) (t t' : (A j).obj.obj (op ((AffineEtale.Spec X).obj W))),
    (lg j).hom.app (op ((AffineEtale.Spec X).obj W)) t =
        (lg j).hom.app (op ((AffineEtale.Spec X).obj W)) t' →
      ∃ (k : J) (a : k ⟶ j), (T a).hom.app (op ((AffineEtale.Spec X).obj W)) t =
        (T a).hom.app (op ((AffineEtale.Spec X).obj W)) t')
  (μ : ∀ j, A j ⟶ Q) (hμ : ∀ {j k : J} (a : k ⟶ j), T a ≫ μ k = μ j)

/-- The component over an affine object of the map out of `P` that the `μ_j` induce: a section of
`P` is `λ_j` of a section of some `A_j`, which `μ_j` carries to `Q`. -/
def descAppSet (W : X.AffineEtale) :
    P.obj.obj (op ((AffineEtale.Spec X).obj W)) ⟶ Q.obj.obj (op ((AffineEtale.Spec X).obj W)) :=
  TypeCat.ofHom fun x => (μ (hsurj W x).choose).hom.app _ (hsurj W x).choose_spec.choose

include hdir hlg hinj hμ in
/-- `Stacks.EtaleCohomology.descAppSet` is well defined: two sections of the `A_j` over an affine
object with the same image in `P` have the same image in `Q`. -/
theorem descAppSet_apply (W : X.AffineEtale) (j : J)
    (t : (A j).obj.obj (op ((AffineEtale.Spec X).obj W))) :
    descAppSet lg hsurj μ W ((lg j).hom.app _ t) = (μ j).hom.app _ t := by
  let U := op ((AffineEtale.Spec X).obj W)
  have comp : ∀ {B C D : Sheaf (smallEtaleTopology X) (Type (u + 1))} (f : B ⟶ C) (g : C ⟶ D)
      (x : B.obj.obj U), (f ≫ g).hom.app U x = g.hom.app U (f.hom.app U x) := fun _ _ _ => rfl
  have wd : ∀ {j j' : J} (t : (A j).obj.obj U) (t' : (A j').obj.obj U),
      (lg j).hom.app U t = (lg j').hom.app U t' → (μ j).hom.app U t = (μ j').hom.app U t' := by
    intro j j' t t' h
    obtain ⟨k, a, a', -⟩ := hdir j j'
    have e : (lg k).hom.app U ((T a).hom.app U t) = (lg k).hom.app U ((T a').hom.app U t') := by
      rw [← comp, ← comp, hlg, hlg, h]
    obtain ⟨m, b, hb⟩ := hinj W k _ _ e
    rw [← hμ a, comp, ← hμ b, comp, hb, ← comp, hμ b, ← comp, hμ a']
  exact wd _ t (hsurj W ((lg j).hom.app U t)).choose_spec.choose_spec

include hdir hlg hinj hμ in
/-- The components over the affine objects, as a natural transformation of the restrictions to
the affine subsite. -/
def descRestrictSet :
    (AffineEtale.Spec X).op ⋙ P.obj ⟶ (AffineEtale.Spec X).op ⋙ Q.obj where
  app W := descAppSet lg hsurj μ W.unop
  naturality W₁ W₂ g := by
    ext x
    obtain ⟨j, t, rfl⟩ := hsurj W₁.unop x
    have n₁ := ConcreteCategory.congr_hom ((lg j).hom.naturality ((AffineEtale.Spec X).op.map g)) t
    have n₂ := ConcreteCategory.congr_hom ((μ j).hom.naturality ((AffineEtale.Spec X).op.map g)) t
    change descAppSet lg hsurj μ W₂.unop
        (P.obj.map ((AffineEtale.Spec X).op.map g) ((lg j).hom.app _ t)) =
      Q.obj.map ((AffineEtale.Spec X).op.map g) (descAppSet lg hsurj μ W₁.unop
        ((lg j).hom.app _ t))
    simp only [ConcreteCategory.comp_apply] at n₁ n₂
    rw [← n₁, descAppSet_apply T lg hdir hlg hsurj hinj μ hμ]
    exact (descAppSet_apply T lg hdir hlg hsurj hinj μ hμ W₂.unop j _).trans n₂

/-- The map out of `P` that the `μ_j` induce: the gluing of its components over the affine
objects. -/
def descSet : P ⟶ Q :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) (Type (u + 1))).preimage
    (Functor.IsCoverDense.sheafHom (G := AffineEtale.Spec X) (K := smallEtaleTopology X)
      (descRestrictSet T lg hdir hlg hsurj hinj μ hμ))

/-- Over an affine object, the component of `Stacks.EtaleCohomology.descSet` is
`Stacks.EtaleCohomology.descAppSet`. -/
theorem descSet_app (W : X.AffineEtale) :
    (descSet T lg hdir hlg hsurj hinj μ hμ).hom.app (op ((AffineEtale.Spec X).obj W)) =
      descAppSet lg hsurj μ W := by
  refine .trans ?_ (NatTrans.congr_app (Functor.IsCoverDense.sheafHom_restrict_eq
    (G := AffineEtale.Spec X) (K := smallEtaleTopology X)
    (descRestrictSet T lg hdir hlg hsurj hinj μ hμ)) (op W))
  simp [descSet]

include hdir hlg hsurj hinj hμ in
/-- **A sheaf of sets that is a filtered colimit on affine sections has the universal property of
the colimit.** If over every affine object the `λ_j` exhibit the sections of `P` as the filtered
colimit of those of the `A_j`, then every family of maps `μ_j : A_j ⟶ Q` compatible with the
transitions factors uniquely through the `λ_j`. -/
theorem existsUnique_desc_of_affineSetSections :
    ∃! σ : P ⟶ Q, ∀ j : J, lg j ≫ σ = μ j := by
  refine ⟨descSet T lg hdir hlg hsurj hinj μ hμ,
    fun j => sheafHom_ext_of_affineEtale_set fun W => ?_,
    fun σ' hσ' => sheafHom_ext_of_affineEtale_set fun W => ?_⟩
  · ext t
    change (descSet T lg hdir hlg hsurj hinj μ hμ).hom.app _ ((lg j).hom.app _ t) = _
    rw [descSet_app, descAppSet_apply T lg hdir hlg hsurj hinj μ hμ]
    rfl
  · ext x
    obtain ⟨j, t, rfl⟩ := hsurj W x
    change σ'.hom.app _ ((lg j).hom.app _ t) =
      (descSet T lg hdir hlg hsurj hinj μ hμ).hom.app _ ((lg j).hom.app _ t)
    rw [descSet_app, descAppSet_apply T lg hdir hlg hsurj hinj μ hμ]
    change ((lg j) ≫ σ').hom.app _ t = _
    rw [hσ' j]

end Stacks.EtaleCohomology

end
