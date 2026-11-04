module

import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorAmplitude
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers

/-!
# Derived limits of towers that factor eventually through a constant

Let `D` be a pretriangulated category and `T : ℕᵒᵖ ⥤ D` a tower with a countable product. A
derived limit of `T` with projections `πₙ : L ⟶ Tₙ` is an object `L` sitting in a distinguished
triangle `L ⟶ ∏ₙ Tₙ ⟶ ∏ₙ Tₙ ⟶ L⟦1⟧` whose first map is the product of the projections and whose
middle map is the Milnor difference `1 - shift`. For an object `Y`, the long exact sequence of
`Hom(Y, -)` on this triangle gives the Milnor short exact sequence
`0 ⟶ R¹ lim Hom(Y, Tₙ⟦-1⟧) ⟶ Hom(Y, L) ⟶ lim Hom(Y, Tₙ) ⟶ 0` of [Stacks, Tag 0919]. In general
a map `Y ⟶ L` is therefore *not* determined by its composites with the projections: the
maps killed by all projections are the phantom maps, measured by the first derived limit. In
particular two derived-limit presentations of the same tower, related by a map `c` compatible
with the projections, need not be related by an isomorphism `c`.

This indeterminacy disappears when the tower factors eventually through a constant: suppose
given compatible maps `φₙ : V ⟶ Tₙ` such that every transition map `Tₘ ⟶ Tₙ`, for `m` large
enough relative to `n`, factors as `Tₘ ⟶ V ⟶ Tₙ` through `φₙ`. Then for every object `Z` the
tower of abelian groups `Hom(Z, Tₙ)` is Mittag-Leffler, since the image of `Hom(Z, Tₘ)` in
`Hom(Z, Tₙ)` is contained in the image of `φₙ ∘ -`, which is contained in the image of every
`Hom(Z, Tₖ)` with `k ≥ n`. So its first derived limit vanishes ([Stacks, Tag 07KW]): the Milnor
difference on `∏ₙ Hom(Z, Tₙ) = Hom(Z, ∏ₙ Tₙ)` is surjective. Taking `Z = Y⟦1⟧`, every map
`Y⟦1⟧ ⟶ ∏ₙ Tₙ` factors through the Milnor difference and hence composes to zero with the
connecting map of the triangle; this kills the phantom maps, so maps into `L` are determined by
their projections, and any map between two derived-limit presentations compatible with the
projections is an isomorphism.

The factorisation property transfers along a map of towers having eventual inverses, which is
how it is used for towers that are pro-isomorphic to one that is known to factor.

## Main results

* `NoetherianAdicCompletion.isMittagLeffler_homSystem_of_exists_factor`: if a tower factors
  eventually through compatible maps from a fixed object, its Hom-towers are Mittag-Leffler.
* `NoetherianAdicCompletion.exists_comp_milnorDifference_eq_of_exists_factor`: for such a tower,
  every map into the product factors through the Milnor difference map.
* `NoetherianAdicCompletion.eq_of_comp_proj_of_exists_factor`: for such a tower, maps into a
  derived limit are determined by their composites with the projections.
* `NoetherianAdicCompletion.isIso_of_comp_proj_of_exists_factor`: for such a tower, a map
  between two derived limits compatible with the projections is an isomorphism.
* `NoetherianAdicCompletion.exists_factor_of_comp_of_hasEventualInverses`: the factorisation
  property transfers along a map of towers having eventual inverses.

## References

* [Stacks Project, Tag 0919](https://stacks.math.columbia.edu/tag/0919)
* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace NoetherianAdicCompletion

/-! ### Transport of the factorisation property -/

section Transport

variable {C : Type u} [Category.{v} C]

/-- Composing a compatible family of maps into a tower with a map of towers gives a compatible
family of maps into the target tower. -/
theorem comp_app_map_homOfLE {F G : ℕᵒᵖ ⥤ C} (ψ : F ⟶ G) {V : C}
    {φ : ∀ n : ℕ, V ⟶ F.obj ⟨n⟩}
    (hφ : ∀ {m n : ℕ} (h : n ≤ m), φ m ≫ F.map (homOfLE h).op = φ n)
    {m n : ℕ} (h : n ≤ m) :
    (φ m ≫ ψ.app ⟨m⟩) ≫ G.map (homOfLE h).op = φ n ≫ ψ.app ⟨n⟩ := by
  rw [Category.assoc, ← ψ.naturality, ← Category.assoc, hφ]

/-- **Eventual factorisation through a constant transfers along a map with eventual inverses.**
If every transition map of `F` eventually factors through `φₙ : V ⟶ Fₙ`, and `ψ : F ⟶ G` has
eventual inverses, then every transition map of `G` eventually factors through `φₙ ≫ ψₙ`. -/
theorem exists_factor_of_comp_of_hasEventualInverses {F G : ℕᵒᵖ ⥤ C} {ψ : F ⟶ G}
    (hψ : HasEventualInverses ψ) {V : C} {φ : ∀ n : ℕ, V ⟶ F.obj ⟨n⟩}
    (hfac : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (t : F.obj ⟨m⟩ ⟶ V),
      t ≫ φ n = F.map (homOfLE h).op) (n : ℕ) :
    ∃ (m : ℕ) (h : n ≤ m) (t : G.obj ⟨m⟩ ⟶ V),
      t ≫ φ n ≫ ψ.app ⟨n⟩ = G.map (homOfLE h).op := by
  obtain ⟨n', hn', t', ht'⟩ := hfac n
  obtain ⟨m, hm, s, -, hs⟩ := hψ n'
  refine ⟨m, hn'.trans hm, s ≫ t', ?_⟩
  rw [Category.assoc, reassoc_of% ht', ψ.naturality, reassoc_of% hs, map_homOfLE_op_comp]

/-- A natural isomorphism of towers has eventual inverses, attained at the same stage. -/
theorem hasEventualInverses_of_isIso {F G : ℕᵒᵖ ⥤ C} (ψ : F ⟶ G) [IsIso ψ] :
    HasEventualInverses ψ := by
  intro n
  have h : (homOfLE (le_refl n)).op = 𝟙 (op n) := Subsingleton.elim _ _
  refine ⟨n, le_refl n, inv ψ |>.app (op n), ?_, ?_⟩
  · rw [h, F.map_id, ← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app]
  · rw [h, G.map_id, ← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]

end Transport

/-! ### Vanishing of the first derived limit of the Hom-towers -/

section MittagLeffler

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **The Hom-towers of a tower factoring eventually through a constant are Mittag-Leffler.**
If `φₙ : V ⟶ Tₙ` are compatible and every transition map `Tₘ ⟶ Tₙ` eventually factors through
`φₙ`, then for every object `Z` the image of `Hom(Z, Tₘ)` in `Hom(Z, Tₙ)` lies in the image of
every `Hom(Z, Tₖ)` with `k ≥ n`. -/
theorem isMittagLeffler_homSystem_of_exists_factor (T : ℕᵒᵖ ⥤ C) {V : C}
    (φ : ∀ n : ℕ, V ⟶ T.obj ⟨n⟩)
    (hφ : ∀ {m n : ℕ} (h : n ≤ m), φ m ≫ T.map (homOfLE h).op = φ n)
    (hfac : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (t : T.obj ⟨m⟩ ⟶ V),
      t ≫ φ n = T.map (homOfLE h).op) (Z : C) :
    ((T ⋙ preadditiveCoyoneda.obj (op Z)) ⋙ forget AddCommGrpCat.{v}).IsMittagLeffler := by
  intro j
  obtain ⟨m, h, t, ht⟩ := hfac j.unop
  refine ⟨op m, (homOfLE h).op, fun k g ↦ ?_⟩
  have hk : j.unop ≤ k.unop := leOfHom g.unop
  obtain rfl : g = (homOfLE hk).op := Subsingleton.elim _ _
  have key : ∀ x : Z ⟶ T.obj (op m), ∃ y : Z ⟶ T.obj k,
      y ≫ T.map (homOfLE hk).op = x ≫ T.map (homOfLE h).op := fun x ↦
    ⟨x ≫ t ≫ φ k.unop, by rw [Category.assoc, Category.assoc, hφ, ht]⟩
  rintro _ ⟨x, rfl⟩
  exact key x

/-- Applying `Hom(Z, -)` to the Milnor difference map of a tower gives, under the comparison
of `Hom(Z, ∏ₙ Tₙ)` with `∏ₙ Hom(Z, Tₙ)`, the Milnor difference map of the Hom-tower. -/
theorem map_milnorDifference_comp_piComparison (T : ℕᵒᵖ ⥤ C)
    [HasProduct fun n : ℕ ↦ T.obj ⟨n⟩] (Z : C) :
    (preadditiveCoyoneda.obj (op Z)).map
        (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op) ≫
        piComparison (preadditiveCoyoneda.obj (op Z)) (fun n : ℕ ↦ T.obj ⟨n⟩) =
      piComparison (preadditiveCoyoneda.obj (op Z)) (fun n : ℕ ↦ T.obj ⟨n⟩) ≫
        Rlim.delta (T ⋙ preadditiveCoyoneda.obj (op Z)) := by
  rw [Rlim.delta_eq_lift]
  apply Pi.hom_ext
  intro n
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [Category.assoc, piComparison_comp_π, Pi.lift_π, Preadditive.comp_sub,
    piComparison_comp_π_assoc, ← Functor.map_comp, Functor.map_sub]

/-- **For a tower factoring eventually through a constant, every map into the product factors
through the Milnor difference map.** This is the vanishing of the first derived limit of the
Mittag-Leffler tower `n ↦ Hom(Z, Tₙ)`, read on `Hom(Z, ∏ₙ Tₙ) = ∏ₙ Hom(Z, Tₙ)`. -/
theorem exists_comp_milnorDifference_eq_of_exists_factor (T : ℕᵒᵖ ⥤ C)
    [HasProduct fun n : ℕ ↦ T.obj ⟨n⟩] {V : C} (φ : ∀ n : ℕ, V ⟶ T.obj ⟨n⟩)
    (hφ : ∀ {m n : ℕ} (h : n ≤ m), φ m ≫ T.map (homOfLE h).op = φ n)
    (hfac : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (t : T.obj ⟨m⟩ ⟶ V),
      t ≫ φ n = T.map (homOfLE h).op) {Z : C} (y : Z ⟶ ∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩) :
    ∃ y' : Z ⟶ ∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩,
      y' ≫ (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op) = y := by
  let H := preadditiveCoyoneda.obj (op Z)
  set f : (∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩) ⟶ ∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩ :=
    Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op
  have hepi : Epi (Rlim.delta (T ⋙ H)) := Stacks.DerivedLimit.epi_delta_of_isMittagLeffler _
    (isMittagLeffler_homSystem_of_exists_factor T φ hφ hfac Z)
  have : PreservesLimitsOfSize.{0, 0} H := preservesSmallestLimits_of_preservesLimits _
  have hd : H.map f =
      (piComparison H (fun n : ℕ ↦ T.obj ⟨n⟩) ≫ Rlim.delta (T ⋙ H)) ≫
        inv (piComparison H (fun n : ℕ ↦ T.obj ⟨n⟩)) :=
    (IsIso.eq_comp_inv _).2 (map_milnorDifference_comp_piComparison T Z)
  have : Epi (H.map f) := by
    rw [hd]
    infer_instance
  exact (AddCommGrpCat.epi_iff_surjective _).1 this y

end MittagLeffler

/-! ### Maps into a derived limit -/

section DerivedLimit

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Maps into a derived limit of a tower factoring eventually through a constant are
determined by their projections.** If `φₙ : V ⟶ Tₙ` are compatible and every transition map of
`T` eventually factors through `φₙ`, then two maps `Y ⟶ L` into a derived limit of `T` agreeing
after every projection are equal: the phantom part, the first derived limit of the
Hom-tower `n ↦ Hom(Y⟦1⟧, Tₙ)`, vanishes. -/
theorem eq_of_comp_proj_of_exists_factor (T : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ ↦ T.obj ⟨n⟩]
    {L : D} {π : ∀ n : ℕ, L ⟶ T.obj ⟨n⟩} (hL : IsDerivedLimitWithProjections T L π)
    {V : D} (φ : ∀ n : ℕ, V ⟶ T.obj ⟨n⟩)
    (hφ : ∀ {m n : ℕ} (h : n ≤ m), φ m ≫ T.map (homOfLE h).op = φ n)
    (hfac : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (t : T.obj ⟨m⟩ ⟶ V),
      t ≫ φ n = T.map (homOfLE h).op)
    {Y : D} {d d' : Y ⟶ L} (h : ∀ n : ℕ, d ≫ π n = d' ≫ π n) : d = d' := by
  obtain ⟨δ, hT⟩ := hL
  rw [← sub_eq_zero]
  have h₀ : (d - d') ≫ Pi.lift π = 0 :=
    Pi.hom_ext _ _ fun n ↦ by simp [Preadditive.sub_comp, h n]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ _ hT ((shiftFunctor D (1 : ℤ)).map (d - d')) (by
    dsimp
    rw [← Functor.map_comp, h₀, Functor.map_zero])
  obtain ⟨g', rfl⟩ := exists_comp_milnorDifference_eq_of_exists_factor T φ hφ hfac g
  apply (shiftFunctor D (1 : ℤ)).map_injective
  rw [hg, Functor.map_zero, Category.assoc]
  exact (g' ≫= comp_distTriang_mor_zero₂₃ _ hT).trans comp_zero

/-- **Two derived limits of a tower factoring eventually through a constant are identified by
any map compatible with the projections.** If `φₙ : V ⟶ Tₙ` are compatible and every
transition map of `T` eventually factors through `φₙ`, then any map `c : M ⟶ L` between two
derived limits of `T` with `c ≫ πₙ = pₙ` is an isomorphism. Completing the identity of the
products to a morphism of the defining triangles gives an isomorphism `M ⟶ L` compatible with
the projections, and it equals `c` by `eq_of_comp_proj_of_exists_factor`. -/
theorem isIso_of_comp_proj_of_exists_factor (T : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ ↦ T.obj ⟨n⟩] {V : D} (φ : ∀ n : ℕ, V ⟶ T.obj ⟨n⟩)
    (hφ : ∀ {m n : ℕ} (h : n ≤ m), φ m ≫ T.map (homOfLE h).op = φ n)
    (hfac : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (t : T.obj ⟨m⟩ ⟶ V),
      t ≫ φ n = T.map (homOfLE h).op)
    {M L : D} {p : ∀ n : ℕ, M ⟶ T.obj ⟨n⟩} {π : ∀ n : ℕ, L ⟶ T.obj ⟨n⟩}
    (hM : IsDerivedLimitWithProjections T M p) (hL : IsDerivedLimitWithProjections T L π)
    (c : M ⟶ L) (hc : ∀ n : ℕ, c ≫ π n = p n) : IsIso c := by
  obtain ⟨δM, hTM⟩ := hM
  obtain ⟨δL, hTL⟩ := id hL
  obtain ⟨a, ha₁, ha₂⟩ := complete_distinguished_triangle_morphism₁ _ _ hTM hTL (𝟙 _) (𝟙 _)
    (by simp)
  have hap : ∀ n : ℕ, a ≫ π n = p n := fun n ↦ by
    simpa using (ha₁ =≫ Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n).symm
  have : IsIso a := isIso₁_of_isIso₂₃
    (Triangle.homMk _ _ a (𝟙 _) (𝟙 _) ha₁ (by simp) ha₂) hTM hTL (IsIso.id _) (IsIso.id _)
  obtain rfl : c = a :=
    eq_of_comp_proj_of_exists_factor T hL φ hφ hfac fun n ↦ by rw [hc, hap]
  infer_instance

end DerivedLimit

end NoetherianAdicCompletion
