module

public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.DominationFromNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.ResolutionTransferAssembly

/-!
# Dominating a modification at closed points by normalized blowups, from the neighbourhoods

Let `X` be a normal, locally Noetherian algebraic space over a scheme `S` with pairwise
distinct closed points `x₁, …, xₙ` and chosen elementary étale neighbourhoods
`(Uᵢ, uᵢ) ⟶ (X, xᵢ)` (Stacks 0BH9), let `ν : X ⟶ X₀` be the proper normalization of an
algebraic space `X₀`, and let `l : Y ⟶ X` be an algebraic space over `X` which is an isomorphism
over `X ∖ {x₁, …, xₙ}`. Suppose that for each `i` there is a sequence of proper normalized
blowups of the scheme `Uᵢ` at closed points over `uᵢ` whose top dominates, over `Uᵢ`, a scheme
which in turn dominates the base change `Yᵢ = Y ×_X Uᵢ`. Then there is a sequence of normalized
blowups of `X₀` in the sense of Stacks 0BHX, starting with `ν`, whose top dominates `Y` over `X`.

This is the last paragraph of the proof of Stacks 0BHM: the local sequences lift to `X` by
Stacks 0BHL (one blowing up at a time, through
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_lift_reflTransGen`), and the top
dominates `Y` by the equivalence of categories of Stacks 0BHB
(`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_hom_of_forall_pullback_hom`).

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_normalizedBlowUpChain_dominating`:
  the statement above.

## References

* [Stacks Project, Tag 0BHM](https://stacks.math.columbia.edu/tag/0BHM)
* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- **Dominating `Y` from dominations over the neighbourhoods.** Let `ν : X ⟶ X₀` be the proper
normalization of `X₀`, with `X` normal and locally Noetherian, and let `l : Y ⟶ X` be an
isomorphism over `X ∖ {x₁, …, xₙ}`. If each chosen neighbourhood `Uᵢ` has a sequence of proper
normalized blowups centred over `uᵢ` whose top maps over `Uᵢ` to a scheme `Pᵢ` of the site
dominating `Y ×_X Uᵢ`, then `X₀` has a sequence of normalized blowups in the sense of
Stacks 0BHX, starting with `ν`, whose top dominates `Y` over `X`. -/
theorem exists_normalizedBlowUpChain_dominating
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] {X₀ Y : AlgebraicSpaces B S hS}
    (ν : D.space ⟶ X₀) (hν : IsProper B S hS ν.hom)
    (hνnorm : ∃ (Dn : NormalizationData B S hS X₀.obj) (e : D.space.obj ≅ Dn.space),
      ν.hom = e.hom ≫ Dn.hom)
    (hXn : Space.IsNormal B S hS D.space.obj)
    (hXln : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (l : Y ⟶ D.space) (hl : IsIso (pullback.snd l.hom D.openAwayFromPoints.ι))
    (hloc : ∀ i, ∃ (U : (D.neighborhoodScheme i).Opens) (Z : Over (D.neighborhoodScheme i)),
      (∀ y, y ∉ U → y = (D.neighborhood i).point) ∧
        Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U) (Over.mk (𝟙 _)) Z ∧
          ∃ (P : BigFppfOver B S hS) (qP : P ⟶ (D.neighborhood i).scheme)
            (hP : yoneda.obj P ⟶ pullback l.hom (D.toSpaceHom i).hom)
            (k : Z.left ⟶ (BigFppfOver.toScheme B S hS).obj P),
            hP ≫ pullback.snd l.hom (D.toSpaceHom i).hom = yoneda.map qP ∧
              k ≫ (BigFppfOver.toScheme B S hS).map qP = Z.hom) :
    ∃ (A : AlgebraicSpaces B S hS) (g : A ⟶ D.space) (h : A ⟶ Y),
      NormalizedBlowUpChain B S hS X₀ A (g ≫ ν) ∧ h ≫ l = g := by
  classical
  choose U Z hU hZ P qP hP k hhP hk using hloc
  have hidp : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : P ⟶ D.space.obj),
      IsIso (pullback.snd (𝟙 D.space : D.space ⟶ D.space).hom c) :=
    fun c => (IsPullback.of_hasPullback _ c).isIso_snd_of_isIso
  have hgood₀ : D.IsGoodStage ν (𝟙 D.space) := by
    refine ⟨?_, hXn, hXln, hidp _⟩
    rw [Category.id_comp]
    exact NormalizedBlowUpChain.normalization ν hνnorm hν
  have hrest₀ : ∀ k, IsProper B S hS
      (pullback.snd (𝟙 D.space : D.space ⟶ D.space).hom (D.toSpaceHom k).hom) :=
    fun k => have := hidp (D.toSpaceHom k).hom; isProper_of_isIso B S hS _
  have hrep₀ : ∀ k, D.StageRep k (𝟙 D.space) (Over.mk (𝟙 _)) := fun k =>
    ⟨(D.neighborhood k).scheme, 𝟙 _, @asIso _ _ _ _
      (pullback.snd (𝟙 D.space : D.space ⟶ D.space).hom (D.toSpaceHom k).hom) (hidp _),
      Iso.refl _, by simp only [CategoryTheory.Functor.map_id, Category.comp_id]; rfl, by simp⟩
  have claim : ∀ s : Finset (Fin n), ∃ (A : AlgebraicSpaces B S hS) (g : A ⟶ D.space),
      D.IsGoodStage ν g ∧ (∀ k, IsProper B S hS (pullback.snd g.hom (D.toSpaceHom k).hom)) ∧
        ∀ k, D.StageRep k g (if k ∈ s then Z k else Over.mk (𝟙 _)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨_, 𝟙 D.space, hgood₀, hrest₀, fun k => by simpa using hrep₀ k⟩
    | @insert i s hi ih =>
      obtain ⟨A₀, g₀, hgood, hrest, hrep⟩ := ih
      have hrepi : D.StageRep i g₀ (Over.mk (𝟙 _)) := by simpa [hi] using hrep i
      obtain ⟨A, g, hgood', hrest', hrepi', hpres⟩ :=
        D.exists_lift_reflTransGen ν hν hXln i (hU i) hgood hrest hrepi (hZ i)
      refine ⟨A, g, hgood', hrest', fun k => ?_⟩
      by_cases hk : k = i
      · subst hk
        simpa using hrepi'
      · obtain ⟨e, he⟩ := hpres (D.neighborhoodSpace k).property (D.toSpaceHom k).hom
          (D.neighborhood k).etale_toSpace (fun p hp => D.map_ne_point k i hk p hp)
        simpa [Finset.mem_insert, hk] using D.stageRep_of_iso k e he (hrep k)
  obtain ⟨A, g, hgood, -, hrep⟩ := claim Finset.univ
  simp only [Finset.mem_univ, ite_true] at hrep
  have hm : ∀ i, ∃ m : pullback g.hom (D.toSpaceHom i).hom ⟶ pullback l.hom (D.toSpaceHom i).hom,
      m ≫ pullback.snd l.hom (D.toSpaceHom i).hom = pullback.snd g.hom (D.toSpaceHom i).hom :=
    fun i => D.exists_pullback_hom_of_stageRep i l (hrep i) (qP i) (hP i) (hhP i) (k i) (hk i)
  choose m hm using hm
  obtain ⟨h, hh⟩ := D.exists_hom_of_forall_pullback_hom g l hgood.2.2.2 hl m hm
  exact ⟨A, g, h, hgood.1, hh⟩

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
