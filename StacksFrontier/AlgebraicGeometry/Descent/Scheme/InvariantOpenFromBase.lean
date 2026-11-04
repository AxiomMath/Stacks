module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumSectionsPushout
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.EffectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.InvariantOpen
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.OpenSubDatum

/-!
# Invariant opens of a descent datum coming from the base

Let `f : X ⟶ S` be a morphism of schemes and let `(V, φ)` be a descent datum relative to
`X/S`. The preimage in `V` of an open `T ⊆ S` is an invariant open, and an open covering of `S`
pulls back to a covering of `V` by invariant opens. Restricting the datum to such an open preserves
étaleness of the scheme it carries.

## Main results

* `AlgebraicGeometry.DescentData.isInvariantOpens_preimage_base`: the preimages of an open of
  the base form an invariant family of opens of a descent datum for a family of morphisms with
  target `S`.
* `AlgebraicGeometry.DescentDatum.isTransitionInvariant_preimage_base`: the same statement for a
  descent datum relative to a single morphism.
* `AlgebraicGeometry.DescentDatum.iSup_preimage_base`: an open covering of `S` pulls back to
  a covering of `V` by invariant opens.
* `AlgebraicGeometry.DescentDatum.etale_restrictOpen`: the restriction of a descent datum with
  étale underlying scheme to an invariant open again has étale underlying scheme.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

namespace DescentData

variable {ι : Type v} {S : Scheme.{u}} {Y : ι → Scheme.{u}} {g : ∀ i, Y i ⟶ S}

/-- The preimages of an open of the base form an invariant family of opens. -/
lemma isInvariantOpens_preimage_base (D : DescentData g) (T : S.Opens) :
    D.IsInvariantOpens fun i ↦ ((D.obj i).hom ≫ g i) ⁻¹ᵁ T := by
  intro i j
  have key : (D.gluingPullbackIso i j).hom ≫ pullback.snd (g i) ((D.obj j).hom ≫ g j) ≫
      (D.obj j).hom ≫ g j =
      pullback.fst ((D.obj i).hom ≫ g i) (g j) ≫ (D.obj i).hom ≫ g i := by
    rw [← Category.assoc (pullback.snd (g i) ((D.obj j).hom ≫ g j)), ← Category.assoc,
      D.gluingPullbackIso_hom_snd i j, pullback.condition]
  simpa only [Scheme.Hom.comp_preimage] using
    congrArg (fun k : pullback ((D.obj i).hom ≫ g i) (g j) ⟶ S => k ⁻¹ᵁ T) key

end DescentData

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- The preimage in `V` of an open of `S` is an invariant open. -/
theorem isTransitionInvariant_preimage_base (T : S.Opens) :
    D.IsTransitionInvariant ((D.over.hom ≫ f) ⁻¹ᵁ T) := by
  have key : D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f ≫
      D.over.hom ≫ f = pullback.snd f (D.over.hom ≫ f) ≫ D.over.hom ≫ f := by
    rw [pullback.condition, ← Category.assoc,
      D.transitionPullbackIso_inv_comp_pullbackSnd, Category.assoc]
  have h := congrArg (fun k : pullback f (D.over.hom ≫ f) ⟶ S => k ⁻¹ᵁ T) key
  simp only [Scheme.Hom.comp_preimage, Scheme.Hom.inv_preimage] at h
  change D.transitionPullbackIso.hom ''ᵁ
      (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ ((D.over.hom ≫ f) ⁻¹ᵁ T)) =
    pullback.snd f (D.over.hom ≫ f) ⁻¹ᵁ ((D.over.hom ≫ f) ⁻¹ᵁ T)
  simpa only [Scheme.Hom.comp_preimage] using h

/-- An open covering of `S` pulls back to a covering of `V` by invariant opens. -/
lemma iSup_preimage_base {κ : Type*} (T : κ → S.Opens) (hT : ⨆ i, T i = ⊤) :
    ⨆ i, (D.over.hom ≫ f) ⁻¹ᵁ T i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hT, Scheme.Hom.preimage_top]

/-- The restriction of a descent datum whose scheme is étale over `X` to an invariant open
again has a scheme étale over `X`. -/
instance etale_restrictOpen {W : D.over.left.Opens} (hW : D.IsTransitionInvariant W)
    [Etale D.over.hom] : Etale (D.restrictOpen W hW).over.hom :=
  inferInstanceAs (Etale (W.ι ≫ D.over.hom))

end DescentDatum

end AlgebraicGeometry

end

end
