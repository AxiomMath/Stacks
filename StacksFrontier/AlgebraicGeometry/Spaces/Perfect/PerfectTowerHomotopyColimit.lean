module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentHomotopyColimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExtConeOrthogonality

/-!
# Homotopy colimits of towers of perfect objects whose transition maps stabilise

Let `X` be an algebraic space and let `L₀ ⟶ L₁ ⟶ L₂ ⟶ ⋯` be a system in `D(𝒪_X)` whose transition
map `Lₙ ⟶ Lₙ₊₁` is an isomorphism on cohomology in degrees `> sₙ`, for a non-increasing sequence
of integers `sₙ`.  Then the homotopy colimit `L = hocolim Lₙ` (Stacks 090Z) exists, and each
coprojection `Lₙ ⟶ L` is an isomorphism on cohomology in degrees `> sₙ` (Stacks 0CRK: cohomology
commutes with the derived colimit).  Consequently

* `Ext^i(L, F) ⟶ Ext^i(Lₙ, F)` is bijective for `i + sₙ + 2 ≤ 0` and every `𝒪_X`-module `F`
  (`DerivedCategory.bijective_comp_shiftedHom_of_isIso_homologyFunctor_map`), and
* if the `Lₙ` are perfect and `sₙ ⟶ -∞`, then `L` is pseudo-coherent.

This is the last step of the proof of Stacks 08JR, part (B): "Thus `L = hocolim Lₙ` is
pseudo-coherent, see Lemma 0DKB.  The mapping property of homotopy colimits gives that
`Ext^i(L, F) = Ext^i(Lₙ, F)` for `i ≤ n + a - 3`."

## Main results

* `AlgebraicGeometry.Space.exists_isHomotopyColimitWith_isIso_homology_of_tower`: the homotopy
  colimit and the cohomology of its coprojections.
* `AlgebraicGeometry.Space.isPseudoCoherent_of_isIso_homology_of_isPerfect`: pseudo-coherence of
  the colimit, the argument of the direction `(2) ⟹ (1)` of Stacks 0DKB.

## Implementation notes

The model of `D(𝒪_X)` is arbitrary, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentHomotopyColimit`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 0DKB](https://stacks.math.columbia.edu/tag/0DKB)
* [Stacks Project, Tag 0CRK](https://stacks.math.columbia.edu/tag/0CRK)
* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] pointTopology smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
  [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]

/-- In a tower whose transition maps `Lₖ ⟶ Lₖ₊₁` are isomorphisms on `Hʲ` for `j > sₖ`, with `s`
non-increasing, every map `Lₙ ⟶ Lₘ`, `n ≤ m`, is an isomorphism on `Hʲ` for `j > sₙ`. -/
theorem isIso_homologyFunctor_map_of_tower
    (F : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS X hX)) (s : ℕ → ℤ)
    (hs : ∀ n, s (n + 1) ≤ s n)
    (hF : ∀ n : ℕ, ∀ j : ℤ, s n < j →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).map
        (F.map (homOfLE (Nat.le_succ n)))))
    (n : ℕ) (j : ℤ) (hj : s n < j) :
    ∀ (m : ℕ) (f : n ⟶ m),
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).map (F.map f)) := by
  have hs' : ∀ k, n ≤ k → s k ≤ s n := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact (hs k).trans ih
  intro m f
  have hnm : n ≤ m := leOfHom f
  rw [show f = homOfLE hnm from Subsingleton.elim _ _]
  induction m, hnm using Nat.le_induction with
  | base =>
    rw [show (homOfLE (le_refl n) : n ⟶ n) = 𝟙 n from Subsingleton.elim _ _, F.map_id,
      CategoryTheory.Functor.map_id]
    infer_instance
  | succ k hk ih =>
    have h₁ := ih (homOfLE hk)
    have h₂ := hF k j ((hs' k hk).trans_lt hj)
    rw [show (homOfLE (hk.trans (Nat.le_succ k)) : n ⟶ k + 1) =
      homOfLE hk ≫ homOfLE (Nat.le_succ k) from Subsingleton.elim _ _, F.map_comp,
      Functor.map_comp]
    infer_instance

/-- **The homotopy colimit of a stabilising tower**, at any model of `D(𝒪_X)`.  If the transition
maps `Lₙ ⟶ Lₙ₊₁` are isomorphisms on `Hʲ` for `j > sₙ`, `s` non-increasing, then a homotopy
colimit `L = hocolim Lₙ` exists and its coprojections `Lₙ ⟶ L` are isomorphisms on `Hʲ` for
`j > sₙ`: by Stacks 0CRK `Hʲ(L)` is the colimit of the system `Hʲ(Lₘ)`, which is constant from
`m = n` on. -/
theorem exists_isHomotopyColimitWith_isIso_homology_of_tower
    (F : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS X hX)) (s : ℕ → ℤ)
    (hs : ∀ n, s (n + 1) ≤ s n)
    (hF : ∀ n : ℕ, ∀ j : ℤ, s n < j →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).map
        (F.map (homOfLE (Nat.le_succ n))))) :
    haveI := hasColimitsOfShape_discrete_nat_derivedCategory_modules B S hS X hX
    ∃ (L : DerivedCategory (Modules.{u, u} B S hS X hX)) (c : ∀ n, F.obj n ⟶ L),
      IsHomotopyColimitWith F L c ∧
        ∀ n : ℕ, ∀ j : ℤ, s n < j →
          IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).map (c n)) := by
  have := hasColimitsOfShape_discrete_nat_derivedCategory_modules B S hS X hX
  have := isGrothendieckAbelian_modules B S hS X hX
  have : HasColimitsOfShape ℕ (Modules.{u, u} B S hS X hX) :=
    hasColimitsOfShape_of_equivalence (AsSmall.equiv.{0, 0, u}).symm
  have : HasExactColimitsOfShape ℕ (Modules.{u, u} B S hS X hX) :=
    HasExactColimitsOfShape.of_domain_equivalence (Modules.{u, u} B S hS X hX)
      (AsSmall.equiv.{0, 0, u}).symm
  obtain ⟨L, p, q, hT⟩ :=
    distinguished_cocone_triangle (Stacks.CountableCoproducts.oneSubShift F)
  refine ⟨L, fun n => Sigma.ι F.obj n ≫ p, ⟨p, q, hT, fun _ => rfl⟩, fun n j hj => ?_⟩
  let H := DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j
  have : PreservesColimitsOfShape (Discrete ℕ) H :=
    have := Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor
      (Modules.{u, u} B S hS X hX) (J := ULift.{u} ℕ) j
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  obtain ⟨e, he⟩ := exists_iso_colimit_of_isHomotopyColimit F H p q hT
  have hev : (F ⋙ H).IsEventuallyConstantFrom n := fun m f =>
    isIso_homologyFunctor_map_of_tower B S hS X hX F s hs hF n j hj m f
  have : IsIso (colimit.ι (F ⋙ H) n) := hev.isIso_ι_of_isColimit (colimit.isColimit _)
  rw [← he n]
  infer_instance

/-- **The homotopy colimit of a stabilising tower of perfect objects is pseudo-coherent**,
provided the thresholds `sₙ` tend to `-∞`.  For every `m` choose `n` with `sₙ < m`; the cone of
`Lₙ ⟶ L` has no cohomology in degrees `≥ m`, hence is `m`-pseudo-coherent, and `Lₙ` is perfect,
hence pseudo-coherent (Stacks 08G8); so `L` is `m`-pseudo-coherent.  This is the argument of the
direction `(2) ⟹ (1)` of Stacks 0DKB. -/
theorem isPseudoCoherent_of_isIso_homology_of_isPerfect
    {L : DerivedCategory (Modules.{u, u} B S hS X hX)}
    (P : ℕ → DerivedCategory (Modules.{u, u} B S hS X hX)) (c : ∀ n, P n ⟶ L) (s : ℕ → ℤ)
    (hP : ∀ n, (smallEtaleRingedSite B S hS X hX).IsPerfect (P n))
    (hc : ∀ n : ℕ, ∀ j : ℤ, s n < j →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).map (c n)))
    (hs : ∀ m : ℤ, ∃ n : ℕ, s n < m) :
    (smallEtaleRingedSite B S hS X hX).IsPseudoCoherent L := by
  refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ L).2 fun m => ?_
  obtain ⟨n, hn⟩ := hs m
  obtain ⟨C, v, w', hT⟩ := distinguished_cocone_triangle (c n)
  have hC : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom C m :=
    RingedSite.isPseudoCoherentFrom_of_forall_isZero_homology _ C m fun i hi =>
      CategoryTheory.isZero_homology_obj₃_of_distinguished (s n + 1) _ hT
        (fun j hj => hc n j (by omega)) (hc n (s n + 1) (by omega)).epi_of_iso
        i (by omega)
  exact RingedSite.isPseudoCoherentFrom_of_distinguished_two_general _ m _ hT
    ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1
      (RingedSite.isPseudoCoherent_of_isPerfect_general _ (hP n)) m) hC

end AlgebraicGeometry.Space

end
