module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison

/-!
# The system of inverse images of a single sheaf

Let `D : Iᵒᵖ ⥤ Scheme` be an inverse system of schemes all of which carry a morphism to a fixed
scheme `S`, compatibly with the transitions — that is, let `d` be a cocone on `D` with vertex
`S` — and let `ℱ` be an abelian sheaf on the small étale site of `S`. The inverse images
`𝒢_i = (D_i ⟶ S)^{-1} ℱ` then form a *system of sheaves* on `D` in the sense of Stacks 0EZL: the
transition map `𝒢_j ⟶ 𝒢_i` along `a : i ⟶ j` is the comparison of the inverse image along the
composite `D_i ⟶ D_j ⟶ S` with the composite of the inverse images, and the cocycle condition is
the associativity pentagon of that comparison.

This is the shape in which Stacks 03Q6 takes its sheaves: there the system is not arbitrary but
is `𝒢_i = (Y_i ⟶ X)^{-1} ℱ` for one abelian sheaf `ℱ` on `X`, the `Y_i` being the base changes of
`X` and the cocone being the projections `Y_i ⟶ X`.

## Main definitions

* `Stacks.EtaleCohomology.coconeInverseImage` — the inverse image `(D_i ⟶ S)^{-1} ℱ`.
* `Stacks.EtaleCohomology.coconeInverseImageComp` — the comparison identifying the inverse image
  along `D_i ⟶ S` with the inverse image along `D_j ⟶ S` followed by the inverse image along the
  transition `D_i ⟶ D_j`.
* `Stacks.EtaleCohomology.inverseImageSystem` — **the system of inverse images of a single
  sheaf**, constructed.

## Main results

* `Stacks.EtaleCohomology.smallEtalePullbackAbComp'_eq_compIso'` — the two names the repository
  carries for the comparison of inverse images along a named composite agree.

## Implementation notes

The cocycle condition is not proved from scratch: it is
`Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'_assoc`, the associativity pentagon of the
inverse-image comparison, read at the three composites `D_i ⟶ D_j ⟶ D_k ⟶ S` and evaluated at
`ℱ`. The only bookkeeping is that the pentagon is stated for
`Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'` whereas
`Stacks.EtaleCohomology.EtaleSheafSystem` is stated through
`Stacks.EtaleCohomology.systemPullbackComp`; `systemPullbackComp_eq` and
`smallEtalePullbackAbComp'_eq_compIso'` close that gap, the two comparisons being the same
`CategoryTheory.Adjunction.leftAdjointCompIso` of the same comparison of direct images.

Coefficients are `Ab.{u + 1}` and the site is the small étale site of a scheme in the sense of
Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology`. That is the setting in which the inverse
image of abelian sheaves exists with no hypothesis: the site is essentially `(u + 1)`-small, so
the left Kan extensions computing the left adjoint of restriction are available, which is what
`Stacks.EtaleCohomology.smallEtalePullbackAb` relies on.

Nothing is assumed of the index: `I` is a preordered type and the transitions are arbitrary
morphisms of schemes, as in Stacks 0EZL. In particular the cocone is not assumed to be a colimit
and `S` is not one of the `D_i`.

## References

* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

/-- **The two names for the comparison of inverse images along a named composite agree.** Both
are `CategoryTheory.Adjunction.leftAdjointCompIso` of the comparison of direct images along the
same composite. -/
theorem smallEtalePullbackAbComp'_eq_compIso' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    smallEtalePullbackAbComp' f g fg hfg = smallEtalePullbackAbCompIso' f g fg hfg := by
  rw [smallEtalePullbackAbComp'_eq_leftAdjointCompIso, smallEtalePullbackAbCompIso'_def]
  rfl

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (d : Cocone D)
  (F : Sheaf (smallEtaleTopology d.pt) Ab.{u + 1})

/-- The inverse image `(D_i ⟶ S)^{-1} ℱ` of an abelian sheaf on the small étale site of the
vertex `S` of a cocone, along the leg at `i`. -/
abbrev coconeInverseImage (i : Iᵒᵖ) : Sheaf (smallEtaleTopology (D.obj i)) Ab.{u + 1} :=
  (smallEtalePullbackAb (d.ι.app i)).obj F

/-- The canonical identification `(D_i ⟶ S)^{-1} ≅ f_{ij}^{-1} (D_j ⟶ S)^{-1}` of inverse-image
functors, coming from the factorisation `(D_i ⟶ S) = f_{ij} ≫ (D_j ⟶ S)` of a leg of the cocone
through a transition morphism. -/
def coconeInverseImageComp {i j : Iᵒᵖ} (a : i ⟶ j) :
    smallEtalePullbackAb (d.ι.app j) ⋙ systemPullback D Ab.{u + 1} a ≅
      smallEtalePullbackAb (d.ι.app i) :=
  smallEtalePullbackAbCompIso' (D.map a) (d.ι.app j) (d.ι.app i) (d.w a).symm

/-- **The system of inverse images of a single sheaf, constructed.** Let `D` be an inverse system
of schemes, let `d` be a cocone on it with vertex `S` — so every `D_i` carries a morphism
`D_i ⟶ S` compatible with the transitions — and let `ℱ` be an abelian sheaf on the small étale
site of `S`. The inverse images `(D_i ⟶ S)^{-1} ℱ`, with the transition maps supplied by
`coconeInverseImageComp`, form a system of sheaves on `D` in the sense of Stacks 0EZL.

The cocycle condition is the associativity pentagon
`smallEtalePullbackAbCompIso'_assoc` of the inverse-image comparison, at the three morphisms
`D_i ⟶ D_j ⟶ D_k ⟶ S`. -/
@[stacks 0EZL "the system of INVERSE IMAGES of a single sheaf: for a cocone on the inverse \
system with vertex `S` and an abelian sheaf on the small etale site of `S`, the system \
`𝒢_i = (D_i ⟶ S)^{-1} ℱ` together with its cocycle condition, constructed and not assumed. \
Coefficients are `Ab.{u + 1}` on Mathlib's `Scheme.smallEtaleTopology`, which is where the \
inverse image of abelian sheaves exists unconditionally"]
def inverseImageSystem : EtaleSheafSystem D Ab.{u + 1} where
  obj i := coconeInverseImage D d F i
  map a := (coconeInverseImageComp D d a).hom.app F
  map_comp {i j k} a b := by
    have hpent := smallEtalePullbackAbCompIso'_assoc (d.ι.app k) (D.map b) (D.map a)
      (d.ι.app j) (d.w b).symm (D.map (a ≫ b)) (D.map_comp a b) (d.ι.app i)
      (d.w (a ≫ b)).symm (d.w a).symm
    have hp := congrArg (fun z : _ ≅ _ => NatTrans.app z.hom F) hpent
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.symm_hom, Functor.associator_inv_app, Category.id_comp] at hp
    rw [systemPullbackComp_eq, smallEtalePullbackAbComp'_eq_compIso']
    exact (Iso.inv_comp_eq (Iso.app (smallEtalePullbackAbCompIso' (D.map a) (D.map b)
      (D.map (a ≫ b)) (D.map_comp a b)) _)).2 hp.symm

end Stacks.EtaleCohomology

end
