module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.Rings
public import StacksFrontier.Deformation.Examples.Geometric.Base
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization

/-!
# Recognising two deformations of the same algebra as isomorphic

The proof of **Stacks 0DZF** repeatedly compares two functors into the same deformation
category by writing down, for each deformation `X`, an isomorphism of the two flat algebras
produced from `X`. Such an isomorphism is nothing more than a ring isomorphism of the two
fibres which is linear over the common Artinian base and compatible with the reduction to the
special fibre: the pushout condition on a morphism of flat algebras is automatic once the
underlying map is invertible, and the morphism of Artinian bases is forced because the base of
`(k, P)` is terminal in `𝒞_Λ`.

This file isolates that recognition principle, together with the two transport-along-an-equality
gadgets the comparisons need: an equality of ideals gives a canonical isomorphism of the
corresponding adic completions, respectively henselizations, compatible with the structural
maps.

## Main definitions

* `Deformation.Examples.flatAlgebraWithBase`: a flat algebra whose base is rewritten along an
  equality of objects of `𝒞_Λ`.
* `Deformation.Examples.residueFieldBaseMap`: the unique morphism of `𝒞_Λ` from an object to
  the base of `(k, P)`.
* `Deformation.Examples.flatAlgebraIsoOfRingEquiv`: an isomorphism of flat algebras built from
  an isomorphism of bases and a compatible ring isomorphism of fibres.
* `Deformation.Examples.deformationIsoOfRingEquiv`: the same for two deformations of one
  algebra over one base.
* `Deformation.Examples.adicCompletionEquivOfIdealEq`,
  `Deformation.Examples.henselizationEquivOfIdealEq`: transport of the completion,
  respectively henselization, along an equality of ideals.

## Main results

* `Deformation.Examples.deformationBaseMap_unique`: any two morphisms of `𝒞_Λ` into the base of
  `(k, P)` agree, because that base is terminal.
* `Deformation.Examples.specialFiber_pushout_with_base` and
  `Deformation.Examples.flatAlgebraHom_cartesian_with_base`: the pushout squares of a
  deformation and of a morphism of deformations, read at a rewritten base.
* `Deformation.Examples.isPushout_of_base_eq`: a pushout square at rewritten bases is one at the
  original bases.

## Implementation notes

The isomorphism of fibres is taken as a `RingEquiv` together with the equation saying it
commutes with the two structural maps from the base, rather than as an `AlgEquiv`: every
application is to fibres of deformations, where the algebra instances are the ones carried by
the flat algebras, and matching those up to definitional equality is exactly what a caller
cannot do.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 0DY1](https://stacks.math.columbia.edu/tag/0DY1)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace Deformation.Examples

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Rewriting the base of a flat algebra -/

/-- A flat algebra whose base is rewritten along an equality of objects of `𝒞_Λ`: the fibre and
its flatness are unchanged. -/
public noncomputable def flatAlgebraWithBase
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (X : FlatAlgebraCategory.{u, w} Λ k) (h : X.base = A) :
    FlatAlgebraCategory.{u, w} Λ k where
  base := A
  fiber := X.fiber
  algebra := by subst A; exact X.algebra
  flat := by subst A; exact X.flat

/-- The structural map of a flat algebra with a rewritten base is the original one, read through
the rewriting. -/
public theorem flatAlgebraWithBase_algebraMap
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (X : FlatAlgebraCategory.{u, w} Λ k) (h : X.base = A) (a : A) :
    @algebraMap A X.fiber _ _ (flatAlgebraWithBase A X h).algebra a =
      algebraMap X.base X.fiber ((eqToHom h.symm).hom a) := by
  subst A
  rfl

/-! ### Morphisms into the base of the special fibre -/

/-- **Any two morphisms of `𝒞_Λ` into the base of `(k, P)` agree**: that base is the residue
field object, which is terminal. -/
public theorem deformationBaseMap_unique
    {R : Type w} [CommRing R] [Algebra k R]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f g : A ⟶ (residueFieldAlgebra (Λ := Λ) (k := k) R).base) : f = g :=
  (isTerminal_residueFieldBase (Λ := Λ) (k := k)).hom_ext f g

/-- The morphism of `𝒞_Λ` from an object to the base of `(k, P)`. -/
public noncomputable def residueFieldBaseMap
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (R : Type w) [CommRing R] [Algebra k R] :
    A ⟶ (residueFieldAlgebra (Λ := Λ) (k := k) R).base :=
  (isTerminal_residueFieldBase (Λ := Λ) (k := k)).from A

/-- **The pushout square of a deformation, read at a rewritten base.** The morphism of `𝒞_Λ` is
irrelevant by `Deformation.Examples.deformationBaseMap_unique`. -/
public theorem specialFiber_pushout_with_base
    {R : Type w} [CommRing R] [Algebra k R]
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (X : ringDeformationCategory (Λ := Λ) (k := k) R) (h : X.left.base = A)
    (f : A ⟶ (residueFieldAlgebra (Λ := Λ) (k := k) R).base) :
    IsPushout (FlatAlgebraCategory.structureMap (flatAlgebraWithBase A X.left h))
      (CommRingCat.ofHom f.hom.toRingHom) X.hom.map
      (FlatAlgebraCategory.structureMap (residueFieldAlgebra (Λ := Λ) (k := k) R)) := by
  subst A
  obtain rfl : f = X.hom.base := deformationBaseMap_unique _ _
  exact X.hom.cartesian

/-- **The pushout square of a morphism of flat algebras, read at rewritten bases.** -/
public theorem flatAlgebraHom_cartesian_with_base
    {A B : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {X Y : FlatAlgebraCategory.{u, w} Λ k}
    (hX : X.base = A) (hY : Y.base = B) (f : A ⟶ B) (g : X ⟶ Y)
    (hg : g.base = eqToHom hX ≫ f ≫ eqToHom hY.symm) :
    IsPushout (FlatAlgebraCategory.structureMap (flatAlgebraWithBase A X hX))
      (CommRingCat.ofHom f.hom.toRingHom) g.map
      (FlatAlgebraCategory.structureMap (flatAlgebraWithBase B Y hY)) := by
  subst A B
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg
  subst f
  exact g.cartesian

/-- **A pushout square at rewritten bases is one at the original bases.** -/
public theorem isPushout_of_base_eq
    {A B : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {X Y : FlatAlgebraCategory.{u, w} Λ k}
    (hX : X.base = A) (hY : Y.base = B) (f : A ⟶ B)
    (g : CommRingCat.of X.fiber ⟶ CommRingCat.of Y.fiber)
    (h : IsPushout (FlatAlgebraCategory.structureMap (flatAlgebraWithBase A X hX))
      (CommRingCat.ofHom f.hom.toRingHom) g
      (FlatAlgebraCategory.structureMap (flatAlgebraWithBase B Y hY))) :
    IsPushout (FlatAlgebraCategory.structureMap X)
      (FlatAlgebraCategory.baseMap (eqToHom hX ≫ f ≫ eqToHom hY.symm))
      g (FlatAlgebraCategory.structureMap Y) := by
  subst A B
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact h

/-! ### Isomorphisms of flat algebras and of deformations -/

/-- **An isomorphism of bases together with a compatible ring isomorphism of fibres is an
isomorphism of flat algebras.** Both pushout conditions hold because the vertical sides of the
squares are isomorphisms. -/
public noncomputable def flatAlgebraIsoOfRingEquiv
    (X Y : FlatAlgebraCategory.{u, w} Λ k) (b : X.base ≅ Y.base)
    (e : X.fiber ≃+* Y.fiber)
    (he : ∀ a, e (algebraMap X.base X.fiber a) =
      algebraMap Y.base Y.fiber (b.hom.hom a)) : X ≅ Y := by
  let c : CommRingCat.of X.fiber ≅ CommRingCat.of Y.fiber :=
    { hom := CommRingCat.ofHom e.toRingHom
      inv := CommRingCat.ofHom e.symm.toRingHom
      hom_inv_id := by ext x; exact e.symm_apply_apply x
      inv_hom_id := by ext x; exact e.apply_symm_apply x }
  let d : CommRingCat.of X.base ≅ CommRingCat.of Y.base :=
    { hom := CommRingCat.ofHom b.hom.hom.toRingHom
      inv := CommRingCat.ofHom b.inv.hom.toRingHom
      hom_inv_id := by
        ext a
        exact congrArg (fun f => f.hom a) b.hom_inv_id
      inv_hom_id := by
        ext a
        exact congrArg (fun f => f.hom a) b.inv_hom_id }
  have hf : IsPushout (FlatAlgebraCategory.structureMap X) d.hom c.hom
      (FlatAlgebraCategory.structureMap Y) :=
    (IsPushout.of_id_snd (f := FlatAlgebraCategory.structureMap X)).of_iso
      (Iso.refl _) (Iso.refl _) d c (by simp) (by simp) (by simp)
      (by ext a; exact he a)
  have hg : IsPushout (FlatAlgebraCategory.structureMap Y) d.inv c.inv
      (FlatAlgebraCategory.structureMap X) :=
    (IsPushout.of_id_snd (f := FlatAlgebraCategory.structureMap Y)).of_iso
      (Iso.refl _) (Iso.refl _) d.symm c.symm (by simp) (by simp) (by simp)
      (by
        ext a
        apply e.injective
        change e (e.symm (algebraMap Y.base Y.fiber a)) =
          e (algebraMap X.base X.fiber (b.inv.hom a))
        rw [e.apply_symm_apply, he]
        have h := congrArg (fun f => f.hom a) b.inv_hom_id
        change b.hom.hom (b.inv.hom a) = a at h
        rw [h])
  exact
    { hom := { base := b.hom, map := c.hom, cartesian := hf }
      inv := { base := b.inv, map := c.inv, cartesian := hg }
      hom_inv_id := FlatAlgebraCategory.Hom.ext b.hom_inv_id c.hom_inv_id
      inv_hom_id := FlatAlgebraCategory.Hom.ext b.inv_hom_id c.inv_hom_id }

/-- **Two deformations of the same algebra over the same base are isomorphic as soon as their
fibres are, compatibly.** The hypotheses are: the bases agree, the ring isomorphism of fibres is
linear over the base, and it commutes with the two reductions to the special fibre. -/
public noncomputable def deformationIsoOfRingEquiv
    {R : Type w} [CommRing R] [Algebra k R]
    (X Y : ringDeformationCategory (Λ := Λ) (k := k) R)
    (hbase : X.left.base = Y.left.base) (e : X.left.fiber ≃+* Y.left.fiber)
    (he : ∀ a, e (algebraMap X.left.base X.left.fiber a) =
      algebraMap Y.left.base Y.left.fiber ((eqToHom hbase).hom a))
    (hs : ∀ x, Y.hom.map.hom (e x) = X.hom.map.hom x) : X ≅ Y := by
  refine Over.isoMk (flatAlgebraIsoOfRingEquiv X.left Y.left (eqToIso hbase) e he) ?_
  exact FlatAlgebraCategory.Hom.ext (deformationBaseMap_unique _ _) (by ext x; exact hs x)

/-! ### Transport along an equality of ideals -/

/-- The canonical isomorphism of adic completions attached to an equality of ideals, together
with its compatibility with the structural maps. -/
public noncomputable def adicCompletionEquivOfIdealEq
    {R : Type w} [CommRing R] (I J : Ideal R) (h : I = J) :
    { e : AdicCompletion I R ≃+* AdicCompletion J R //
      ∀ r, e (algebraMap R (AdicCompletion I R) r) =
        algebraMap R (AdicCompletion J R) r } := by
  subst J
  exact ⟨RingEquiv.refl _, fun _ => rfl⟩

/-- The canonical isomorphism of henselizations attached to an equality of ideals, together with
its compatibility with the structural maps. -/
public noncomputable def henselizationEquivOfIdealEq
    {R : Type w} [CommRing R] (I J : Ideal R) (h : I = J) :
    { e : (henselization R I : Type w) ≃+* (henselization R J : Type w) //
      ∀ r, e (algebraMap R (henselization R I : Type w) r) =
        algebraMap R (henselization R J : Type w) r } := by
  subst J
  exact ⟨RingEquiv.refl _, fun _ => rfl⟩

end Deformation.Examples
