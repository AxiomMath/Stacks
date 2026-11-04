module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.LocalToGlobalStep

/-!
# Lifting sequences of normalized blowups from étale neighbourhoods to the whole space

Let `X` be a decent algebraic space over a scheme `S` with pairwise distinct closed points
`x₁, …, xₙ` and chosen elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` (Stacks 0BH9), and
let `ν : X ⟶ Y` be proper. A sequence of normalized blowups of the scheme `Uᵢ` at closed points
over `uᵢ` lifts, one blowing up at a time, to a sequence of normalized blowups at closed points
of algebraic spaces over `X`; the base change of the result to `Uᵢ` is the given sequence, and
the base change to every étale `P ⟶ X` missing `xᵢ` is unchanged. Along the way the composite
to `Y` stays a sequence of normalized blowups in the sense of Stacks 0BHX, each member being
proper over `Y` by Stacks 0BHC.

This is the local-to-global direction of Stacks 0BHL for normalized blowups over a normal base,
as used in the proof of (4) `⇒` (3) of Stacks 0BHY.

## Main definitions

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.IsGoodStage`: the invariant of the
  induction.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isProper_of_forall_isProper_pullback_snd`:
  Stacks 0BHC for the morphisms to `X` occurring here.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_lift_reflTransGen`: the lifting of
  a whole sequence over one neighbourhood.

## References

* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0BHC](https://stacks.math.columbia.edu/tag/0BHC)
* [Stacks Project, Tag 0BHX](https://stacks.math.columbia.edu/tag/0BHX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- **Stacks 0BHC for a morphism to `X` which is an isomorphism over `X ∖ {x₁, …, xₙ}`.** It is
proper as soon as each of its base changes to the chosen neighbourhoods is. -/
theorem isProper_of_forall_isProper_pullback_snd {A : AlgebraicSpaces B S hS} (g : A ⟶ D.space)
    (hiso : IsIso (pullback.snd g.hom D.openAwayFromPoints.ι))
    (h : ∀ i, IsProper B S hS (pullback.snd g.hom (D.toSpaceHom i).hom)) :
    IsProper B S hS g.hom :=
  (D.isProper_iff_forall_restrictionComponent ⟨Over.mk g.hom, A.property, hiso⟩).mpr h

/-- A base change represented by a scheme proper over the neighbourhood is proper. -/
theorem isProper_pullback_snd_of_stageRep (i : Fin n) {A : AlgebraicSpaces B S hS}
    {g : A ⟶ D.space} {Z : Over (D.neighborhoodScheme i)} (hZ : D.StageRep i g Z)
    (hZp : AlgebraicGeometry.IsProper Z.hom) :
    IsProper B S hS (pullback.snd g.hom (D.toSpaceHom i).hom) := by
  obtain ⟨W, q, Φ, θ, hΦ, hθ⟩ := hZ
  have hq : AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q) := by
    rw [← hθ]; infer_instance
  rw [← hΦ]
  exact isProper_comp B S hS
    (isAlgebraicSpace_pullback B S hS _ _ A.property (D.neighborhoodSpace i).property
      D.space.property)
    (isAlgebraicSpace_yoneda B S hS W) (D.neighborhoodSpace i).property _ _
    (isProper_of_isIso B S hS Φ.hom) (isProper_yoneda_map B S hS q hq)

/-- Properness of the second projection depends only on the isomorphism class of the base
change over the base. -/
theorem isProper_of_iso_over {P P' V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hP' : IsAlgebraicSpace B S hS P')
    (hV : IsAlgebraicSpace B S hS V) {s : P ⟶ V} {s' : P' ⟶ V} (e : P ≅ P')
    (he : e.hom ≫ s' = s) (hs' : IsProper B S hS s') : IsProper B S hS s := by
  rw [← he]
  exact isProper_comp B S hS hP hP' hV _ _ (isProper_of_isIso B S hS e.hom) hs'

variable {Y : AlgebraicSpaces B S hS} (ν : D.space ⟶ Y)

/-- **The invariant of the lifting.** `g : A ⟶ X` followed by `ν` is a sequence of normalized
blowups over `Y` in the sense of Stacks 0BHX, `A` is normal and locally Noetherian, and `g` is an
isomorphism over `X ∖ {x₁, …, xₙ}`. -/
def IsGoodStage {A : AlgebraicSpaces B S hS} (g : A ⟶ D.space) : Prop :=
  NormalizedBlowUpChain B S hS Y A (g ≫ ν) ∧ Space.IsNormal B S hS A.obj ∧
    HasEtaleLocalProperty B S hS A.obj (fun T : Scheme.{u} => IsLocallyNoetherian T) ∧
      IsIso (pullback.snd g.hom D.openAwayFromPoints.ι)

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The lifting of a sequence of normalized blowups of the `i`th neighbourhood at points over
`uᵢ`.** Starting from a good stage `g₀ : A₀ ⟶ X` whose base change to the `i`th neighbourhood is
the neighbourhood itself, a sequence of proper normalized blowups of the neighbourhood at closed
points over `uᵢ` ending in `Z` lifts to a good stage `g : A ⟶ X` whose base change to the `i`th
neighbourhood is `Z` and whose base change to every étale `P ⟶ X` missing `xᵢ` is that of
`g₀`. -/
theorem exists_lift_reflTransGen (hν : IsProper B S hS ν.hom)
    (hX : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Fin n) {U : (D.neighborhoodScheme i).Opens}
    (hU : ∀ y, y ∉ U → y = (D.neighborhood i).point)
    {A₀ : AlgebraicSpaces B S hS} {g₀ : A₀ ⟶ D.space} (hgood : D.IsGoodStage ν g₀)
    (hrest : ∀ k, IsProper B S hS (pullback.snd g₀.hom (D.toSpaceHom k).hom))
    (hrep : D.StageRep i g₀ (Over.mk (𝟙 _)))
    {Z : Over (D.neighborhoodScheme i)}
    (hchain : Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U) (Over.mk (𝟙 _)) Z) :
    ∃ (A : AlgebraicSpaces B S hS) (g : A ⟶ D.space), D.IsGoodStage ν g ∧
      (∀ k, IsProper B S hS (pullback.snd g.hom (D.toSpaceHom k).hom)) ∧ D.StageRep i g Z ∧
        ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
          (c : P ⟶ D.space.obj), IsEtale B S hS c →
            (∀ p, pointsMap B S hS P c p ≠ D.point i) →
            ∃ e : pullback g.hom c ≅ pullback g₀.hom c,
              e.hom ≫ pullback.snd g₀.hom c = pullback.snd g.hom c := by
  induction hchain with
  | refl =>
    exact ⟨A₀, g₀, hgood, hrest, hrep, fun _ c _ _ => ⟨Iso.refl _, Category.id_comp _⟩⟩
  | @tail Z₁ Z₂ _ hstep ih =>
    obtain ⟨A, g, ⟨hchainA, hAn, hAnoeth, hAiso⟩, hArest, hArep, hApres⟩ := ih
    obtain ⟨A', g₁, z, hz, hg₁, hrep', hpres'⟩ :=
      D.exists_lift_isNormalizedBlowUpOutside i g hAn hAnoeth hU hArep hstep.1
    -- base changes away from `xᵢ`
    have hpres : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
        (c : P ⟶ D.space.obj), IsEtale B S hS c →
          (∀ p, pointsMap B S hS P c p ≠ D.point i) →
          ∃ e : pullback (g₁.hom ≫ g.hom) c ≅ pullback g₀.hom c,
            e.hom ≫ pullback.snd g₀.hom c = pullback.snd (g₁.hom ≫ g.hom) c := by
      intro P hP c hc hcx
      obtain ⟨e₁, he₁⟩ := hpres' hP c hc hcx
      obtain ⟨e₂, he₂⟩ := hApres hP c hc hcx
      exact ⟨e₁ ≪≫ e₂, by rw [Iso.trans_hom, Category.assoc, he₂, he₁]⟩
    -- the open complement of the chosen points
    have hNo := D.isOpenSubspace_openAwayFromPoints
    have hiso' : IsIso (pullback.snd (g₁.hom ≫ g.hom) D.openAwayFromPoints.ι) := by
      obtain ⟨e, he⟩ := hpres hNo.1 D.openAwayFromPoints.ι (isEtale_ι_of_isOpenSubspace hNo)
        (by
          intro p hp
          have hmem : D.point i ∈ Set.range
              (pointsMap B S hS _ D.openAwayFromPoints.ι) := ⟨p, hp⟩
          rw [D.range_pointsMap_ι_openAwayFromPoints] at hmem
          exact hmem ⟨i, rfl⟩)
      have hiso₀ := hgood.2.2.2
      rw [← he]
      infer_instance
    -- properness over the neighbourhoods
    have hrest' : ∀ k, IsProper B S hS (pullback.snd (g₁.hom ≫ g.hom) (D.toSpaceHom k).hom) := by
      intro k
      by_cases hk : k = i
      · subst hk
        exact D.isProper_pullback_snd_of_stageRep k hrep' hstep.2
      · obtain ⟨e, he⟩ := hpres (D.neighborhoodSpace k).property (D.toSpaceHom k).hom
          (D.neighborhood k).etale_toSpace (fun p hp => D.map_ne_point k i hk p hp)
        exact isProper_of_iso_over (isAlgebraicSpace_pullback B S hS _ _
            (A'.property) (D.neighborhoodSpace k).property D.space.property)
          (isAlgebraicSpace_pullback B S hS _ _ A₀.property (D.neighborhoodSpace k).property
            D.space.property) (D.neighborhoodSpace k).property e he (hrest k)
    have hproperX : IsProper B S hS (g₁ ≫ g).hom :=
      D.isProper_of_forall_isProper_pullback_snd (g₁ ≫ g) hiso' hrest'
    have hproperY : IsProper B S hS ((g₁ ≫ g) ≫ ν).hom :=
      isProper_comp B S hS A'.property D.space.property Y.property _ _ hproperX hν
    refine ⟨A', g₁ ≫ g, ⟨?_, ?_, ?_, hiso'⟩, hrest', hrep', hpres⟩
    · have h := NormalizedBlowUpChain.normalizedBlowUp hchainA g₁ z hz hg₁
        (by rw [← Category.assoc]; exact hproperY)
      rwa [← Category.assoc] at h
    · obtain ⟨X', b, -, Dn, e, -⟩ := hg₁
      exact hasEtaleLocalProperty_of_isEtale B S hS A'.property Dn.isAlgebraicSpace
        (isEtale_of_iso B S hS e) (Dn.isNormal X'.property)
    · exact hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
        A'.property D.space.property _ hproperX.2.1.1 hX

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space
