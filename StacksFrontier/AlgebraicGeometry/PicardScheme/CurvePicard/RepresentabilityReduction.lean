module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Normalized
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteOpenSubfunctorGluing
public import StacksFrontier.CategoryTheory.ShrinkSubfunctor

/-!
# Representability of the Picard functor of a curve from its normalized subfunctor

This is the gluing step of the proof of [Stacks, Tag 0B9Z], i.e. [Stacks, Tag 0B9Q] for the
Picard functor of a curve on the big fppf site. Let `X` be a proper scheme of dimension at most
one over `k` with a rational point, satisfying the hypothesis of [Stacks, Tag 0B9N]. If the
normalized subfunctor `F` (fibrewise `H¹ = 0`, `dim H⁰ = 1`) is represented by an object `W` of
the site, and every point of `Pic_{X/k}` is, locally around each point of its base, translated
into `F` by a `k`-rational point of `Pic_{X/k}`, then `Pic_{X/k}` is representable — granted a
cardinal bound placing the glued scheme in the site.

The values of the Picard functor lie in `Type (u + 1)`; they are `u`-small because they are
quotients of the Picard groups of the base changes, and the gluing is carried out on the shrunk
presheaf `CategoryTheory.FunctorToTypes.shrink`.

## Main results

* `Stacks.PicardFunctor.small_picardFunctor_obj`: the values of the Picard functor are small.
* `Stacks.PicardFunctor.isRepresentable_picardFunctor_of_normalized`: the reduction.

## References

* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Cardinal

universe u

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS) (σ : S ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 S)
  (hOiso : ∀ U : BigFppfOver B S hS, IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)

include σ hσ hOiso in
/-- **The values of the Picard functor are `u`-small**: they are quotients of the Picard groups
of the base changes (Tag 0B9N), which have a model in `Type u`. -/
theorem small_picardFunctor_obj (T : BigFppfOver B S hS) :
    Small.{u} ((picardFunctor B hX hS f).obj (op T)) :=
  have : Small.{u} (picardAt B hX hS f T) :=
    Small.mk' (Stacks.GluePicard.picardModelEquiv (baseChange B hX hS f T).toRingedSpace)
  small_of_surjective (surjective_toPicardFunctorHom B hX hS f σ hσ hOiso T)

end Stacks.PicardFunctor

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
    IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c)
  [IsProper (B.inclusion.map f)] [X.IsSeparated] [IsNoetherian X]
  (hdim : topologicalKrullDim X ≤ 1)

include hdim in
/-- **The gluing step of Tag 0B9Z (Tag 0B9Q for the Picard functor of a curve).** If the
normalized subfunctor is represented by an object `W` of the site and every point of the Picard
functor is, around each point of its base, translated into the normalized subfunctor by a
`k`-rational point of the Picard functor, then the Picard functor is representable, as soon as
the `k`-rational points and `W` are bounded by one cardinal below the cutoff of the site. -/
theorem isRepresentable_picardFunctor_of_normalized
    (W : BigFppfOver B (Spec (.of k)) hk)
    (e : (normalizedSubfunctor B hX hk f σ hσ hOiso).toFunctor.RepresentableBy W)
    (htrans : ∀ (T : BigFppfOver B (Spec (.of k)) hk)
      (ξ : (picardFunctor B hX hk f).obj (op T)) (t : (BigFppfOver.toScheme B _ hk).obj T),
      ∃ g, t ∈ normalizedLocus B hX hk f σ hσ hOiso hdim T
        ((translate B hX hk f g).hom.app (op T) ξ))
    (c : Cardinal.{u}) (hc : c < B.cutoff)
    (hpts : #((picardFunctor B hX hk f).obj (op (baseObj B hk))) ≤ Cardinal.lift.{u + 1} c)
    (hW : ((BigFppfOver.toScheme B _ hk).obj W).size ≤ c) :
    (picardFunctor B hX hk f).IsRepresentable := by
  have : FunctorToTypes.Small.{u} (picardFunctor B hX hk f) := fun T =>
    small_picardFunctor_obj B hX hk f σ hσ hOiso T.unop
  let P := picardFunctor B hX hk f
  let G' : Sheaf (BigFppfOver.topology B (Spec (.of k)) hk) (Type u) :=
    ⟨FunctorToTypes.shrink.{u} P, (isSheaf_iff_isSheaf_of_type _ _).2
      (FunctorToTypes.isSheaf_shrink P
        ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_picardFunctor B hX hk f)))⟩
  let ι := Shrink.{u} (P.obj (op (baseObj B hk)))
  let g (i : ι) : P.obj (op (baseObj B hk)) := (equivShrink _).symm i
  let F (i : ι) : Subfunctor G'.obj :=
    FunctorToTypes.shrinkSubfunctor.{u} P (translateSubfunctor B hX hk f σ hσ hOiso (g i))
  let R (i : ι) : (F i).toFunctor.RepresentableBy W :=
    FunctorToTypes.shrinkSubfunctorRepresentableBy P _
      (Subfunctor.preimageIsoRepresentableBy _ (translate B hX hk f (g i)) e)
  let Wo (i : ι) (T : BigFppfOver B (Spec (.of k)) hk) (ξ : G'.obj.obj (op T)) :
      T.left.obj.Opens :=
    normalizedLocus B hX hk f σ hσ hOiso hdim T
      ((translate B hX hk f (g i)).hom.app (op T) ((equivShrink _).symm ξ))
  have hWo : ∀ (i : ι) (T T' : BigFppfOver B (Spec (.of k)) hk) (ξ : G'.obj.obj (op T))
      (h : T' ⟶ T), G'.obj.map h.op ξ ∈ (F i).obj (op T') ↔
        ∀ t, (BigFppfOver.toScheme B _ hk).map h t ∈ Wo i T ξ := by
    intro i T T' ξ h
    rw [FunctorToTypes.mem_shrinkSubfunctor_iff, FunctorToTypes.shrink_map_apply,
      Equiv.symm_apply_apply]
    exact map_mem_translateSubfunctor_iff B hX hk f σ hσ hOiso hdim (g i) h _
  have hcov : ∀ (T : BigFppfOver B (Spec (.of k)) hk) (ξ : G'.obj.obj (op T))
      (t : T.left.obj), ∃ i, t ∈ Wo i T ξ := by
    intro T ξ t
    obtain ⟨g₀, hg₀⟩ := htrans T ((equivShrink _).symm ξ) t
    refine ⟨equivShrink _ g₀, ?_⟩
    change t ∈ normalizedLocus B hX hk f σ hσ hOiso hdim T
      ((translate B hX hk f ((equivShrink _).symm (equivShrink _ g₀))).hom.app (op T) _)
    rw [Equiv.symm_apply_apply]
    exact hg₀
  have hι : #ι ≤ c := by
    rw [← Cardinal.lift_le.{u + 1}]
    refine le_trans (le_of_eq ?_) hpts
    have h := Cardinal.lift_mk_eq'.2 ⟨(equivShrink (P.obj (op (baseObj B hk)))).symm⟩
    exact h.trans (Cardinal.lift_id'.{u, u + 1} _)
  have hrep : G'.obj.IsRepresentable :=
    Space.isRepresentable_of_openSubfunctors G' F (fun _ => W) R Wo hWo hcov c hc hι
      (fun _ => hW)
  obtain ⟨Y, ⟨eY⟩⟩ := hrep.has_representation
  exact (FunctorToTypes.representableByOfShrink P eY).isRepresentable

end Stacks.PicardFunctor
