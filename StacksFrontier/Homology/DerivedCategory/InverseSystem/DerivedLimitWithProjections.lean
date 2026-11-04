module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleShortExact
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumCompletedSections

/-!
# Derived limits with their projections

Let `D` be a pre-triangulated category and `F : ℕᵒᵖ ⥤ D` an inverse system whose objects have a
product. `NoetherianAdicCompletion.IsDerivedLimitWithProjections F K π` says that the maps
`π n : K ⟶ Kₙ` are the projections of a derived-limit presentation of `F` at `K`: their product
`Pi.lift π` is the first map of a distinguished triangle whose middle map is the Milnor
difference. This file collects the facts about that predicate which the bare existential
`CategoryTheory.Pretriangulated.IsDerivedLimit` cannot supply, because it pins no cone:

* the projections form a cone;
* every inverse system has such a presentation;
* a cone on `F` with any vertex factors through the projections;
* the comparison map `Hʳ(K) ⟶ lim Hʳ(Kₙ)` *characterized by the projections* is an isomorphism
  as soon as the inverse system one degree below is Mittag-Leffler.

The last item is the point. `Stacks.LocalCohomology.isIso_completedLocalCohomologyToLimit` proves
Tag 0DXJ for `Dualizing.completedLocalCohomologyToLimit`, a map cut out by `Classical.choose`
from a Milnor existential, so its composite with `limit.π` refers to the structural map of an
unpinned triangle. Here the map is quantified over instead: any `q` whose composites with the
limit projections are `Hʳ(π n)` is inverted, so a consumer that has built its own comparison map
out of canonical projections can use it.

## Main results

* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_map_succ` (in
  `StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers`) — the projections form a
  cone on `F`.
* `NoetherianAdicCompletion.exists_isDerivedLimitWithProjections_of_hasProduct` — every inverse
  system whose objects have a product admits a derived-limit presentation with projections.
* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.exists_lift` — a cone on `F` with
  vertex `Y` factors through the projections.
* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.isIso_of_comp_limit_π` — the pinned
  form of Tag 0DXJ described above.

## References

* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe w v u

namespace NoetherianAdicCompletion

section Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- Splitting a map into a product into its components and reassembling it changes nothing. -/
theorem pi_lift_comp_π {K : D} (a : K ⟶ ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) :
    (Pi.lift fun n : ℕ ↦ a ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) = a :=
  Pi.hom_ext _ _ fun n ↦ by rw [Pi.lift_π]

/-- **Every inverse system whose objects have a product has a derived-limit presentation with
projections.** Completing the Milnor difference map to a distinguished triangle gives a
structural map, and its components are the projections. -/
theorem exists_isDerivedLimitWithProjections_of_hasProduct (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] :
    ∃ (K : D) (π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩), IsDerivedLimitWithProjections F K π := by
  obtain ⟨K, hK⟩ := exists_isDerivedLimit F
  exact ⟨K, exists_isDerivedLimitWithProjections hK⟩

variable {K : D} {π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩}

/-- **A cone on the system factors through the projections.** If `(c n)` is a cone on `F` with
vertex `Y` then its product `Pi.lift c` is killed by the Milnor difference map, so the
presenting triangle factors it through the structural map: there is `v : Y ⟶ K` with
`v ≫ π n = c n` for every `n`. -/
theorem IsDerivedLimitWithProjections.exists_lift
    (h : IsDerivedLimitWithProjections F K π) {Y : D} (c : ∀ n : ℕ, Y ⟶ F.obj ⟨n⟩)
    (hc : ∀ n : ℕ, c (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = c n) :
    ∃ v : Y ⟶ K, ∀ n : ℕ, v ≫ π n = c n := by
  obtain ⟨δ, hT⟩ := h
  have hzero : (Pi.lift c) ≫ (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) = 0 := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, Pi.lift_π, Preadditive.comp_sub, Pi.lift_π, ← Category.assoc,
      Pi.lift_π, hc n, zero_comp, sub_self]
  obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ _ hT (Pi.lift c) hzero
  refine ⟨v, fun n ↦ ?_⟩
  simpa only [Triangle.mk_mor₁, Category.assoc, Pi.lift_π] using
    (congrArg (· ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) hv).symm

/-- **Transport of a derived-limit presentation along an isomorphism of the object.** If `π'`
are the projections of a presentation at `K'` and `e : K ≅ K'`, then `fun n ↦ e.hom ≫ π' n` are
the projections of a presentation at `K`. -/
theorem IsDerivedLimitWithProjections.of_iso {K' : D} {π' : ∀ n : ℕ, K' ⟶ F.obj ⟨n⟩}
    (h : IsDerivedLimitWithProjections F K' π') {K : D} (e : K ≅ K') :
    IsDerivedLimitWithProjections F K (fun n ↦ e.hom ≫ π' n) := by
  exact h.ofIso e.symm

end Pretriangulated

section ModuleCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- **Tag 0DXJ with the comparison map pinned by the projections.** Let `F` be an inverse system
in `D(A)` and let `π` be the projections of a derived-limit presentation at `K`. If the inverse
system of cohomology modules one degree below is Mittag-Leffler, then *every* map
`q : Hʳ(K) ⟶ lim Hʳ(Kₙ)` whose composite with the `n`-th limit projection is `Hʳ(π n)` is an
isomorphism.

The `R¹lim` term of the Milnor short exact sequence vanishes because the Mittag-Leffler
condition makes the difference map on the product of the terms an epimorphism, leaving the
comparison map both a monomorphism and an epimorphism. The sequence is taken at the triangle
supplied by the presentation rather than at an existentially quantified one, which is what makes
the hypothesis `hq` usable: with the structural map equal to `Pi.lift π`, the clause
characterizing the comparison reads `q ≫ limit.π _ (op n) = Hʳ(π n)`, so `q` is determined. -/
theorem IsDerivedLimitWithProjections.isIso_of_comp_limit_π
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (K : DerivedCategory (ModuleCat.{u} A)) (π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩)
    (hK : IsDerivedLimitWithProjections F K π) (r : ℤ)
    (hML : IsMittagLefflerCategorical
      (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1)))
    (q : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj K ⟶
      limit (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) r))
    (hq : ∀ n : ℕ, q ≫ limit.π (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) (op n) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map (π n)) :
    IsIso q := by
  obtain ⟨δ, hT⟩ := hK
  obtain ⟨e, i, q', w, -, -, hqn, hse⟩ :=
    DerivedCategory.exists_milnor_shortExact_of_distTriang F K (Pi.lift π) δ hT r
  obtain rfl : q = q' :=
    limit.hom_ext fun ⟨n⟩ ↦ by rw [hq n, hqn n, ← Functor.map_comp, Pi.lift_π]
  have : Mono q := hse.exact.mono_g (((Preadditive.epi_iff_isZero_cokernel _).1
    (Stacks.Algebraization.epi_milnorDifference_of_isMittagLefflerCategorical
      (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1)) hML)).eq_of_src _ _)
  have : Epi q := hse.epi_g
  exact isIso_of_mono_of_epi _

/-- **Tag 0DXJ with the comparison map built from the projections.** The existential form of
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.isIso_of_comp_limit_π`: the comparison
map exists, is invertible, and its composites with the limit projections are the `Hʳ(π n)`. A
consumer that wants the map rather than a criterion for a given one uses this. -/
theorem IsDerivedLimitWithProjections.exists_isIso_comp_limit_π
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (K : DerivedCategory (ModuleCat.{u} A)) (π : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩)
    (hK : IsDerivedLimitWithProjections F K π) (r : ℤ)
    (hML : IsMittagLefflerCategorical
      (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1))) :
    ∃ q : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj K ⟶
        limit (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) r),
      IsIso q ∧ ∀ n : ℕ,
        q ≫ limit.π (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) (op n) =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map (π n) := by
  obtain ⟨δ, hT⟩ := hK
  obtain ⟨e, i, q, w, -, -, hqn, -⟩ :=
    DerivedCategory.exists_milnor_shortExact_of_distTriang F K (Pi.lift π) δ hT r
  have hq : ∀ n : ℕ,
      q ≫ limit.π (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) (op n) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map (π n) :=
    fun n ↦ by rw [hqn n, ← Functor.map_comp, Pi.lift_π]
  exact ⟨q, IsDerivedLimitWithProjections.isIso_of_comp_limit_π A F K π ⟨δ, hT⟩ r hML q hq, hq⟩

end ModuleCat

end NoetherianAdicCompletion

end
