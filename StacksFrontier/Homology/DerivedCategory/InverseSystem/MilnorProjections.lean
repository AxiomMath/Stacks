module

public import StacksFrontier.CategoryTheory.Abelian.InverseSystemFourTermLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers

/-!
# The cohomology of a derived limit with given projections

Let `K` be a derived limit of an inverse system `F` of complexes of modules, presented by a
distinguished triangle `K ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ K[1]` whose first map has components `pₙ`
(`NoetherianAdicCompletion.IsDerivedLimitWithProjections`). If the inverse system
`{H^{r-1}(Fₙ)}` is Mittag-Leffler, then the cone on `{H^r(Fₙ)}` with point `H^r(K)` and legs
`H^r(pₙ)` is a limit cone: the `R¹lim` term of the Milnor sequence
(`DerivedCategory.homology_shortExact_of_distinguished`) vanishes, and the projection of that
sequence is the comparison map of the cone because the presenting triangle is the given one.

## Main results

* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.cone` — the cone of the projections.
* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.nonempty_isLimit_mapCone_homology` —
  the cone of the `H^r(pₙ)` is a limit cone when `{H^{r-1}(Fₙ)}` is Mittag-Leffler.

## References

* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace NoetherianAdicCompletion

variable {A : Type u} [Ring A] {F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)}
  [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] {K : DerivedCategory (ModuleCat.{u} A)}
  {p : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩}

/-- For `n ≤ m`, the projection `pₘ` followed by the transition map `Fₘ ⟶ Fₙ` is `pₙ`. -/
theorem IsDerivedLimitWithProjections.comp_map (h : IsDerivedLimitWithProjections F K p)
    {m n : ℕ} (hnm : n ≤ m) : p m ≫ F.map (homOfLE hnm).op = p n := by
  induction m, hnm using Nat.le_induction with
  | base => rw [show (homOfLE (le_refl n)).op = 𝟙 (op n) from rfl, F.map_id, Category.comp_id]
  | succ m hnm ih =>
    rw [show (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op from rfl, F.map_comp,
      ← Category.assoc, h.comp_map_succ, ih]

/-- The cone over `F` given by the projections of a derived limit. -/
def IsDerivedLimitWithProjections.cone (h : IsDerivedLimitWithProjections F K p) : Cone F where
  pt := K
  π :=
    { app n := p n.unop
      naturality m n g := by
        refine (Category.id_comp _).trans ?_
        exact (h.comp_map (leOfHom g.unop)).symm }

/-- **The Milnor comparison is an isomorphism for a Mittag-Leffler system.** If the system
`{H^{r-1}(Fₙ)}` is Mittag-Leffler, the cone on `{H^r(Fₙ)}` given by the cohomology of the
projections of a derived limit is a limit cone. -/
theorem IsDerivedLimitWithProjections.nonempty_isLimit_mapCone_homology
    (h : IsDerivedLimitWithProjections F K p) (r : ℤ)
    (hML : IsMittagLefflerCategorical (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A)
      (r - 1))) :
    Nonempty (IsLimit ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).mapCone h.cone)) := by
  obtain ⟨δ, hδ⟩ := id h
  obtain ⟨e, i, q, w, -, -, hq, hS⟩ :=
    DerivedCategory.homology_shortExact_of_distinguished F K (Pi.lift p) δ hδ r
  have hepi := Stacks.Algebraization.epi_milnorDifference_of_isMittagLefflerCategorical _ hML
  have hzero : IsZero (cokernel (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1)).obj
        (op n)) n -
        Pi.π (fun n : ℕ ↦ (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1)).obj
          (op n)) (n + 1) ≫
          (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1)).map
            (homOfLE (Nat.le_succ n)).op)) :=
    isZero_cokernel_of_epi _
  have : Mono q := hS.exact.mono_g (hzero.eq_of_src _ _)
  have : Epi q := hS.epi_g
  have : IsIso q := isIso_of_mono_of_epi q
  have hql : q = limit.lift _ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).mapCone
      h.cone) := by
    refine limit.hom_ext fun n => ?_
    induction n using Opposite.rec with
    | op n =>
      refine (hq n).trans (Eq.trans ?_ (limit.lift_π
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).mapCone h.cone) (op n)).symm)
      rw [← Functor.map_comp, Pi.lift_comp_π]
      rfl
  rw [hql] at this
  have : IsIso ((limit.isLimit (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) r)).lift
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).mapCone h.cone)) := this
  exact ⟨IsLimit.ofPointIso (limit.isLimit _)⟩

end NoetherianAdicCompletion

end
