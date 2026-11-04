module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic

/-!
# Domination of normal modifications read off the exceptional curves

## Main results

* `Stacks.ResolutionOfSurfaces.exists_finite_contracted_forall_exists_lift`: a normal modification
  `Y` of a Noetherian normal Nagata surface `S` contracts finitely many curves, and a normal
  modification `T` of `S` dominates `Y` as soon as no exceptional curve of `Y` has a closed
  centre on `T`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

attribute [local instance] isLocalHom_ringEquiv

/-! ### Domination read off the exceptional curves

A normal modification `q : Y ⟶ S` of a Noetherian normal Nagata surface contracts finitely many
curves, and another normal modification `T` of `S` dominates `Y` as soon as no exceptional curve
of `Y` has a closed centre on `T`. Indeed, on a normal common modification `W` of `T` and `Y`
finite over `T ×_S Y`, a curve contracted by `W ⟶ T` maps onto an exceptional curve of `Y`, whose
local ring is then that of `W` along the curve, centred on `T` at the closed image point. So
`W ⟶ T` contracts nothing and is an isomorphism.
-/

/-- The lift into the swapped pullback is finite when the original lift is. -/
theorem isFinite_pullback_lift_symm {X Y Z W : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) [IsFinite (Limits.pullback.lift a b h)] :
    IsFinite (Limits.pullback.lift b a h.symm) := by
  rw [show Limits.pullback.lift b a h.symm =
      Limits.pullback.lift a b h ≫ (Limits.pullbackSymmetry f g).hom by
    apply Limits.pullback.hom_ext <;>
      simp only [Category.assoc, Limits.pullbackSymmetry_hom_comp_fst,
        Limits.pullbackSymmetry_hom_comp_snd, Limits.pullback.lift_fst, Limits.pullback.lift_snd]]
  infer_instance

/-- In a commutative square `p ≫ l = q' ≫ q` with `q'` inducing an isomorphism on stalks at `w`,
the stalk maps of `l` and `q` are compatible with `p.stalkMap w ≫ inv (q'.stalkMap w)`. -/
theorem stalkMap_comp_inv_stalkMap_eq {W T Y S : Scheme.{u}} {p : W ⟶ T} {l : T ⟶ S}
    {q' : W ⟶ Y} {q : Y ⟶ S} (h : p ≫ l = q' ≫ q) (w : W) [IsIso (q'.stalkMap w)]
    (ht : l (p w) = q (q' w)) :
    l.stalkMap (p w) ≫ (p.stalkMap w ≫ inv (q'.stalkMap w)) =
      (S.presheaf.stalkCongr (.of_eq ht)).hom ≫ q.stalkMap (q' w) := by
  have h1 := Scheme.Hom.stalkMap_congr_hom (p ≫ l) (q' ≫ q) h w
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h1
  rw [← Category.assoc, h1]
  exact (IsIso.comp_inv_eq _).mpr (Category.assoc _ _ _).symm

/-- **A normal modification of a normal surface is dominated as soon as its exceptional curves
have non-closed centres.** Let `S` be a Noetherian integral normal Nagata scheme of dimension at
most two and `q : Y ⟶ S` a proper birational morphism with `Y` normal. The set `F` of non-closed
points of `Y` over closed points of `S` (the generic points of the exceptional curves) is finite;
at each of them the local ring is a discrete valuation ring whose residue field contains the
residue of an element `u` transcendental over the residue field below, and `u` is a ratio of
elements of the local ring of `S` below. And a normal `T` proper and birational over
`S` admits a morphism to `Y` over `S` as soon as, for every `y ∈ F`, no point `t` of `T` over the
image of `y` has a local homomorphism `𝒪_{T,t} ⟶ 𝒪_{Y,y}` over `S` while `κ(t)` is integral over
the residue field below: the local homomorphism would make `𝒪_{Y,y}` dominate `𝒪_{T,t}`, and a
closed centre has a residue field integral over the residue field below. -/
theorem exists_finite_contracted_forall_exists_lift
    {S Y : Scheme.{u}} [IsNoetherian S] [IsIntegral S] [IsNormal S] (hNagata : IsNagataScheme S)
    (hdim : topologicalKrullDim S ≤ 2) [IsIntegral Y] [IsNormal Y] (q : Y ⟶ S) [IsProper q]
    (hq : IsBirational q) :
    ∃ F : Set Y, F.Finite ∧
      (∀ y ∈ F, ¬ IsClosed ({y} : Set Y) ∧ IsClosed ({q y} : Set S) ∧
        IsDiscreteValuationRing (Y.presheaf.stalk y) ∧
        ∃ u : Y.presheaf.stalk y,
          @Transcendental (S.residueField (q y)) (Y.residueField y) _ _
            (q.residueFieldMap y).hom.toAlgebra (Y.residue y u) ∧
          ∃ a b : S.presheaf.stalk (q y), (q.stalkMap y).hom b ≠ 0 ∧
            (q.stalkMap y).hom a = u * (q.stalkMap y).hom b) ∧
      ∀ (T : Scheme.{u}) [IsNormal T] (l : T ⟶ S) [IsProper l], IsBirational l →
        (∀ y ∈ F, ∀ (t : T) (ψ : T.presheaf.stalk t ⟶ Y.presheaf.stalk y) (ht : l t = q y),
          IsLocalHom ψ.hom →
          l.stalkMap t ≫ ψ = (S.presheaf.stalkCongr (.of_eq ht)).hom ≫ q.stalkMap y →
          (l.residueFieldMap t).hom.IsIntegral → False) →
        ∃ g : T ⟶ Y, g ≫ q = l := by
  classical
  have : IsNoetherian Y := isNoetherian_of_isProper_over_noetherian q
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  have hlocS : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ IsIntegral U.toScheme := fun s =>
    have : Nonempty (⊤ : S.Opens) := ⟨⟨s, trivial⟩⟩
    ⟨⊤, trivial, isIntegral_of_isOpenImmersion (⊤ : S.Opens).ι⟩
  have hdimY : topologicalKrullDim Y ≤ 2 :=
    (topologicalKrullDim_le_of_birational_of_locally_integral q hq hlocS).trans hdim
  refine ⟨{y | ¬ IsClosed ({y} : Set Y) ∧ IsClosed ({q y} : Set S)},
    finite_contracted_nonclosed_points q hq hdimY, fun y hy => ⟨hy.1, hy.2, ?_, ?_⟩, ?_⟩
  · obtain ⟨_, h⟩ := isDiscreteValuationRing_stalk_of_codimension_eq_one y
      (codimension_eq_one_of_nonclosed_of_not_generic hdimY y hy.1
        (not_generic_of_contracted_nonclosed_point q hq y hy.1 hy.2))
    exact h
  · obtain ⟨u, hu⟩ := exists_transcendental_residue_of_nonclosed q y hy.1 hy.2
    exact ⟨u, hu, exists_stalk_numerator_denominator_of_birational q hq y u⟩
  intro T _ l _ hl hT
  have : IsNoetherian T := isNoetherian_of_isProper_over_noetherian l
  have : IsReduced T := isReduced_of_isReduced_stalk T
  have hdimT : topologicalKrullDim T ≤ 2 :=
    (topologicalKrullDim_le_of_birational_of_locally_integral l hl hlocS).trans hdim
  obtain ⟨W, p, q', h, hW, hp, hq'p, hfin, hpb, hq'b⟩ :=
    exists_common_normal_modification hNagata hdim l q hl hq
  have : IsNormal W := hW
  have : IsProper p := hp
  have : IsProper q' := hq'p
  have : IsNoetherian W := isNoetherian_of_isProper_over_noetherian p
  have : IsReduced W := isReduced_of_isReduced_stalk W
  have : IsFinite (Limits.pullback.lift p q' h) := hfin
  have := isFinite_pullback_lift_symm p q' h
  have : IsIso p := by
    refine isIso_of_no_contracted_nonclosed_points p hpb hdimT fun w hw => ?_
    by_contra hwc
    have hy : ¬ IsClosed ({q' w} : Set Y) :=
      nonclosed_image_of_finite_comparison q l q' p h.symm w hwc hw
    have ht : l (p w) = q (q' w) := congrArg (fun k : W ⟶ S => k w) h
    have hqy : IsClosed ({q (q' w)} : Set S) := by
      rw [← ht]
      simpa only [Set.image_singleton] using l.isClosedMap _ hw
    have : IsIso (q'.stalkMap w) := isIso_stalkMap_over_nonclosed_point q' hq'b hdimY w hy
    have : IsLocalHom (p.stalkMap w ≫ inv (q'.stalkMap w)).hom := by
      have := isLocalHom_of_isIso (inv (q'.stalkMap w))
      rw [CommRingCat.hom_comp]
      infer_instance
    exact hT (q' w) ⟨hy, hqy⟩ (p w) _ ht this (stalkMap_comp_inv_stalkMap_eq h w ht)
      (isIntegral_residueFieldMap_of_closedPoint l (p w) hw)
  exact ⟨inv p ≫ q', by rw [Category.assoc, ← h, IsIso.inv_hom_id_assoc]⟩

end Stacks.ResolutionOfSurfaces

end
