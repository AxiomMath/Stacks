module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableSurjectiveInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheafEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image along an extension of separably closed fields, on spaces-étale sheaves

Let `K/k` be an extension of separably closed fields. Inverse image along `Spec K ⟶ Spec k` is an
equivalence of small étale topoi, the spectrum of a separably closed field having global sections
as an equivalence (`Stacks.EtaleCohomology.isEquivalence_sheafSections_final_of_isSepClosed`).
This file reads that statement on the spaces-étale sites of the represented algebraic spaces, for
abelian sheaves: the spaces-étale topos of a represented algebraic space is the bounded small
étale topos of the scheme, compatibly with inverse images
(`AlgebraicGeometry.Space.representedComparison`), the bounded small étale topos is Mathlib's,
compatibly with inverse images (`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChangeIso`),
and inverse image of abelian sheaves is inverse image of sheaves of sets on commutative group
objects.

## Main results

* `Stacks.EtaleCohomology.isEquivalence_smallEtaleInverseImage_of_isSepClosed`: inverse image of
  small étale sheaves of sets along `Spec K ⟶ Spec k` is an equivalence.
* `AlgebraicGeometry.Space.isEquivalence_representedSpacesInverseImage_of_isEquivalence`: inverse
  image of spaces-étale sheaves of sets along `h_m` is an equivalence as soon as inverse image of
  small étale sheaves of sets along the morphism of schemes underlying `m` is.
* `AlgebraicGeometry.BigEtaleSpaceSite.isEquivalence_abelianInverseImage_of_isSepClosed`: **for an
  extension `K/k` of separably closed fields, inverse image of abelian sheaves along
  `h_{Spec K} ⟶ h_{Spec k}` is an equivalence.**

## References

* [Stacks Project, Tag 0DG5](https://stacks.math.columbia.edu/tag/0DG5)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (k K : Type u) [Field k] [IsSepClosed k] [Field K] [IsSepClosed K] [Algebra k K]

/-- **For an extension `K/k` of separably closed fields, inverse image of small étale sheaves of
sets along `Spec K ⟶ Spec k` is an equivalence**, being left adjoint to the direct image, which
is one. -/
@[sga "4 VIII 2.5"]
public theorem isEquivalence_smallEtaleInverseImage_of_isSepClosed :
    (smallEtaleInverseImage.{u, 0}
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsEquivalence := by
  have := isEquivalence_sheafPushforwardContinuous_smallEtaleBaseChange_of_isSepClosed k K
    (Type (u + 1))
  exact (smallEtaleInverseImageAdjunction.{u, 0}
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isEquivalence_left_of_isEquivalence_right

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Inverse image of spaces-étale sheaves of sets along `h_m` is an equivalence** as soon as
inverse image of small étale sheaves of sets along the morphism of schemes underlying `m` is:
through the restrictions along the chart functors it is the inverse image of bounded small étale
sheaves (`AlgebraicGeometry.Space.representedComparison`), and that is Mathlib's small étale
inverse image through the restrictions along the embeddings of the bounded sites
(`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChangeIso`). All the restrictions are
equivalences. -/
theorem isEquivalence_representedSpacesInverseImage_of_isEquivalence {V W : BigFppfOver B S hS}
    (m : W ⟶ V)
    (hm : (Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0}
      ((BigFppfOver.toScheme B S hS).map m)).IsEquivalence) :
    ((representedSpacesPseudofunctor B S hS).map m.op.toLoc).toFunctor.IsEquivalence := by
  let B' := associatedBigEtaleSite B
  have e := SmallEtale.restrictionPullbackBaseChangeIso B' (Type (u + 1))
    (S := V.left) (T := W.left) m.left
    (Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction.{u, 0}
      ((BigFppfOver.toScheme B S hS).map m))
    (representedSchemesAdjunction m)
  let ρV := (_root_.AlgebraicGeometry.SmallEtale.toEtaleSite B' V.left.obj
    V.left.property).sheafPushforwardContinuous (Type (u + 1))
      (_root_.AlgebraicGeometry.SmallEtale.topology B' V.left.obj V.left.property)
      V.left.obj.smallEtaleTopology
  let ρW := (_root_.AlgebraicGeometry.SmallEtale.toEtaleSite B' W.left.obj
    W.left.property).sheafPushforwardContinuous (Type (u + 1))
      (_root_.AlgebraicGeometry.SmallEtale.topology B' W.left.obj W.left.property)
      W.left.obj.smallEtaleTopology
  have hV : ρV.IsEquivalence := (_root_.AlgebraicGeometry.SmallEtale.sheafEquiv B' V.left.obj
    V.left.property (Type (u + 1))).isEquivalence_inverse
  have hW : ρW.IsEquivalence := (_root_.AlgebraicGeometry.SmallEtale.sheafEquiv B' W.left.obj
    W.left.property (Type (u + 1))).isEquivalence_inverse
  have h₁ : (Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0}
      ((BigFppfOver.toScheme B S hS).map m) ⋙ ρW).IsEquivalence := inferInstance
  have h₂ := @Functor.isEquivalence_of_iso _ _ _ _ _ _ e.symm h₁
  have hS' := @Functor.isEquivalence_of_comp_left _ _ _ _ _ _ ρV _ hV h₂
  have e' := Cat.Hom.toNatIso
    ((representedComparison (B := B) (S := S) (hS := hS)).naturality m.op.toLoc)
  have h₃ := @Functor.isEquivalence_trans _ _ _ _ _ _ (representedRestriction V (Type (u + 1)))
    ((representedSchemesPseudofunctor B S hS).map m.op.toLoc).toFunctor
    (representedRestriction_isEquivalence V (Type (u + 1))) hS'
  have h₄ := @Functor.isEquivalence_of_iso _ _ _ _ _ _ e'.symm h₃
  exact @Functor.isEquivalence_of_comp_right _ _ _ _ _ _ _ (representedRestriction W (Type (u + 1)))
    (representedRestriction_isEquivalence W (Type (u + 1))) h₄

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-- **Inverse image of abelian sheaves along an extension of separably closed fields is an
equivalence, on the spaces-étale sites.** Let `K/k` be an extension of separably closed fields
whose spectra lie in the big fppf site of `S`, with `Spec k` over `S` by `s`. Then inverse image
of abelian sheaves along the morphism `h_{Spec K} ⟶ h_{Spec k}` of represented algebraic spaces
induced by `Spec K ⟶ Spec k` is an equivalence. -/
theorem isEquivalence_abelianInverseImage_of_isSepClosed
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [IsSepClosed K] [Algebra k K]
    (hk : T.fppfSite.Contains (Spec (.of k))) (hK : T.fppfSite.Contains (Spec (.of K)))
    (s : Spec (.of k) ⟶ S) :
    (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T (Space.yonedaSpaceHom
      (BigFppfOver.homMk T.fppfSite S T.fppf_mem hk s
        (T := BigFppfOver.mk T.fppfSite S T.fppf_mem hK
          (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ s))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl)))).IsEquivalence := by
  have := Space.isEquivalence_representedSpacesInverseImage_of_isEquivalence
    (BigFppfOver.homMk T.fppfSite S T.fppf_mem hk s
      (T := BigFppfOver.mk T.fppfSite S T.fppf_mem hK
        (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ s))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl)
    (Stacks.EtaleCohomology.isEquivalence_smallEtaleInverseImage_of_isSepClosed k K)
  have : (smallEtaleMorphism T (Space.yonedaSpaceHom
      (BigFppfOver.homMk T.fppfSite S T.fppf_mem hk s
        (T := BigFppfOver.mk T.fppfSite S T.fppf_mem hK
          (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ s))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl))).inverseImage.IsEquivalence := this
  exact CategoryTheory.Sites.isEquivalence_abelianInverseImage_of_isEquivalence _

end AlgebraicGeometry.BigEtaleSpaceSite

end
