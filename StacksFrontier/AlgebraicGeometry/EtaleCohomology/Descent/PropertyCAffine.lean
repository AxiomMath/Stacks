module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Property (C) with an affine dominating scheme

Stacks Project, Tag 04DW gives, for an integral morphism `f : X ⟶ Y` which is a homeomorphism onto
a closed subset of `Y` and a scheme `U` étale over `X`, a scheme `V` étale over `Y` and a
surjection `X ×_Y V ⟶ U` over `X`. Nothing is claimed about `V` beyond étaleness. The second proof
of Stacks Project, Tag 04DZ needs the same statement with `V` *affine*, and gets it from the
quasi-compactness of `U`: "As `U` is quasi-compact we may replace `W` by a disjoint union of
finitely many affine opens of `W`, hence we may assume that `W` is affine as well."

This file carries out that replacement. The dominating morphism `h : X ×_Y V ⟶ U` is a morphism
over `X` between schemes étale over `X`, hence itself étale and therefore open; so the images under
`h` of the preimages of the affine opens of `V` form an open covering of `U`, a finite subfamily of
which already covers `U` when `U` is quasi-compact. The coproduct of those finitely many affine
opens is affine, is étale over `Y`, and its fibre product with `f` still dominates `U`.

## Main definitions

* `Stacks.EtaleCohomology.pullbackBaseMap` — the comparison morphism `X ×_Y V' ⟶ X ×_Y V` induced
  by a morphism `V' ⟶ V` of schemes over `Y`.

## Main results

* `Stacks.EtaleCohomology.isPullback_pullbackBaseMap` — the comparison morphism exhibits
  `X ×_Y V'` as the fibre product of `X ×_Y V ⟶ V` with `V' ⟶ V`.
* `Stacks.EtaleCohomology.exists_pullbackBaseMap_eq` — consequently a point of `X ×_Y V` whose
  image in `V` comes from `V'` is itself in the image of the comparison morphism.
* `Stacks.EtaleCohomology.etale_of_etale_comp_etale` — a morphism over `X` between schemes étale
  over `X` is étale.
* `Stacks.EtaleCohomology.exists_affine_etale_surjective_pullback` — property (C) with an affine
  dominating scheme: the affine form of Stacks Project, Tag 04DW which the second proof of Stacks
  Project, Tag 04DZ uses.

## References

* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section BaseMap

variable {X Y V' V : Scheme.{u}} (f : X ⟶ Y) (α : V' ⟶ V) (v : V ⟶ Y)

/-- **The comparison morphism of a change of base scheme.** A morphism `α : V' ⟶ V` of schemes
over `Y` induces a morphism `X ×_Y V' ⟶ X ×_Y V` over `X`. -/
def pullbackBaseMap : pullback f (α ≫ v) ⟶ pullback f v :=
  pullback.lift (pullback.fst f (α ≫ v)) (pullback.snd f (α ≫ v) ≫ α)
    (by rw [pullback.condition, Category.assoc])

/-- The comparison morphism of `α`, followed by the projection `X ×_Y V ⟶ X`, is the projection
`X ×_Y V' ⟶ X`. -/
@[simp]
theorem pullbackBaseMap_fst :
    pullbackBaseMap f α v ≫ pullback.fst f v = pullback.fst f (α ≫ v) :=
  pullback.lift_fst _ _ _

/-- The comparison morphism of `α`, followed by the projection `X ×_Y V ⟶ V`, is the projection
`X ×_Y V' ⟶ V'` followed by `α`. -/
@[simp]
theorem pullbackBaseMap_snd :
    pullbackBaseMap f α v ≫ pullback.snd f v = pullback.snd f (α ≫ v) ≫ α :=
  pullback.lift_snd _ _ _

/-- **The comparison morphism is a base change.** The comparison morphism of `α`, together with
the projection to `V'`, exhibits `X ×_Y V'` as the fibre product of `X ×_Y V ⟶ V` with `α`.

This is the pasting of the defining square of `X ×_Y V'` onto that of `X ×_Y V`. -/
theorem isPullback_pullbackBaseMap :
    IsPullback (pullbackBaseMap f α v) (pullback.snd f (α ≫ v)) (pullback.snd f v) α := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f v) ?_ (pullbackBaseMap_snd f α v)
    (IsPullback.of_hasPullback f v)
  rw [pullbackBaseMap_fst]
  exact IsPullback.of_hasPullback f (α ≫ v)

/-- A point of `X ×_Y V` whose image in `V` lies in the image of `α` is itself in the image of the
comparison morphism of `α`. -/
theorem exists_pullbackBaseMap_eq (q : ↥(pullback f v)) (y : ↥V')
    (hy : α.base y = (pullback.snd f v).base q) :
    ∃ z, (pullbackBaseMap f α v).base z = q := by
  have sq := isPullback_pullbackBaseMap f α v
  obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd f v) (g := α) q y hy.symm
  have hmap : sq.isoPullback.inv ≫ pullbackBaseMap f α v =
      pullback.fst (pullback.snd f v) α := by
    calc
      sq.isoPullback.inv ≫ pullbackBaseMap f α v =
          sq.isoPullback.inv ≫
            (sq.isoPullback.hom ≫ pullback.fst (pullback.snd f v) α) := by
        rw [sq.isoPullback_hom_fst]
      _ = pullback.fst (pullback.snd f v) α := by simp
  refine ⟨sq.isoPullback.inv.base z, ?_⟩
  show (sq.isoPullback.inv ≫ pullbackBaseMap f α v).base z = q
  rw [hmap]
  exact hz₁

end BaseMap

/-- **A morphism over `X` between schemes étale over `X` is étale.** If `h ≫ p` is étale and `p`
is étale, then `h` is étale, étale morphisms being unramified. -/
@[sga "4 VII 1.2"]
theorem etale_of_etale_comp_etale {X U U' : Scheme.{u}} (h : U' ⟶ U) (p : U ⟶ X)
    (hp : Etale p) (hhp : Etale (h ≫ p)) : Etale h := by
  have _ : Etale p := hp
  have _ : Etale (h ≫ p) := hhp
  exact Etale.of_comp h p

/-- **Property (C) with an affine dominating scheme.** Let `f : X ⟶ Y` be an integral morphism
which is a homeomorphism onto a closed subset of `Y`, and let `p : U ⟶ X` be étale with `U`
quasi-compact. Then there is an *affine* scheme `W` étale over `Y` together with a surjection
`X ×_Y W ⟶ U` over `X`.

This is the form of Stacks Project, Tag 04DW used by the second proof of Stacks Project,
Tag 04DZ. Tag 04DW supplies some scheme `V` étale over `Y` dominating `U`; the dominating morphism
`h : X ×_Y V ⟶ U` is a morphism over `X` between schemes étale over `X`, hence étale and so open
by Stacks Project, Tag 01UA, so the images under `h` of the preimages of the affine opens of `V`
cover `U`. Quasi-compactness of `U` selects a finite subfamily, and the coproduct of the
corresponding affine opens is the required affine `W`. -/
theorem exists_affine_etale_surjective_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    (hf : Topology.IsClosedEmbedding f.base) {U : Scheme.{u}} (p : U ⟶ X) (hp : Etale p)
    [CompactSpace U] :
    ∃ (W : Scheme.{u}) (w : W ⟶ Y) (_ : Etale w) (_ : IsAffine W) (k : pullback f w ⟶ U),
      Surjective k ∧ k ≫ p = pullback.fst f w := by
  have _ : Etale p := hp
  obtain ⟨V, v, hv, h, hsurj, hcomp⟩ :=
    hasPropertyC_of_isIntegralHom_of_isClosedEmbedding f hf p hp
  have _ : Etale v := hv
  have hhp : Etale (h ≫ p) := by rw [hcomp]; infer_instance
  have hhe : Etale h := etale_of_etale_comp_etale h p hp hhp
  have hopen : IsOpenMap h.base := isOpenMap_of_etale h hhe
  -- an affine open neighbourhood of every point of `V`
  choose A hAaff hAmem _ using fun t : V =>
    exists_isAffineOpen_mem_and_subset (X := V) (x := t) (U := ⊤)
      (TopologicalSpace.Opens.mem_top t)
  -- the images under `h` of their preimages form an open covering of `U`
  set O : V → Set U := fun t => h.base '' ((pullback.snd f v).base ⁻¹' (A t).1) with hO
  have hOopen (t : V) : IsOpen (O t) :=
    hopen _ ((A t).2.preimage (pullback.snd f v).continuous)
  have hOcover : (Set.univ : Set U) ⊆ ⋃ t : V, O t := by
    intro u _
    obtain ⟨q, hq⟩ := hsurj.surj u
    exact Set.mem_iUnion.2
      ⟨(pullback.snd f v).base q, ⟨q, hAmem _, hq⟩⟩
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover O hOopen hOcover
  -- the coproduct of the chosen finitely many affine opens
  set σ : (∐ fun j : (J : Finset V) => (A j.1).toScheme) ⟶ V :=
    Sigma.desc (fun j => (A j.1).ι) with hσ
  have hσι (j : (J : Finset V)) (y : (A j.1).toScheme) :
      σ.base (Sigma.ι (fun j : (J : Finset V) => (A j.1).toScheme) j |>.base y)
        = (A j.1).ι.base y := by
    have : Sigma.ι (fun j : (J : Finset V) => (A j.1).toScheme) j ≫ σ = (A j.1).ι := by
      simp [hσ]
    exact congrArg (fun m : (A j.1).toScheme ⟶ V => m.base y) this |>.symm ▸ rfl
  have hAetale (j : (J : Finset V)) : Etale (A j.1).ι := inferInstance
  have _ : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have hσe : Etale σ := by
    rw [hσ]
    exact IsZariskiLocalAtSource.sigmaDesc fun j => hAetale j
  have hWaff : IsAffine (∐ fun j : (J : Finset V) => (A j.1).toScheme) := by
    have _ (j : (J : Finset V)) : IsAffine (A j.1).toScheme := (hAaff j.1)
    infer_instance
  refine ⟨∐ fun j : (J : Finset V) => (A j.1).toScheme, σ ≫ v, inferInstance, hWaff,
    pullbackBaseMap f σ v ≫ h, ⟨fun u => ?_⟩, ?_⟩
  · -- surjectivity
    obtain ⟨t, htJ, hu⟩ := Set.mem_iUnion₂.1 (hJ (Set.mem_univ u))
    obtain ⟨q, hqmem, hqu⟩ := hu
    have hmem : (pullback.snd f v).base q ∈ Set.range ((A t).ι).base := by
      rw [Scheme.Opens.range_ι]
      exact hqmem
    obtain ⟨y, hy⟩ := hmem
    obtain ⟨z, hz⟩ := exists_pullbackBaseMap_eq f σ v q
      ((Sigma.ι (fun j : (J : Finset V) => (A j.1).toScheme) ⟨t, htJ⟩).base y)
      (by rw [hσι]; exact hy)
    refine ⟨z, ?_⟩
    show h.base ((pullbackBaseMap f σ v).base z) = u
    rw [hz]
    exact hqu
  · rw [Category.assoc, hcomp, pullbackBaseMap_fst]

end Stacks.EtaleCohomology

end

end
