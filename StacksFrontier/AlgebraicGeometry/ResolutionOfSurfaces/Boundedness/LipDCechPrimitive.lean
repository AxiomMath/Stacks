module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDPuncturedRestriction

/-!
# Gluing primitives of a cocycle along a Čech coboundary

Let `0 ⟶ M ⟶ I⁰ ⟶ I¹ ⟶ ⋯` be an injective resolution of a sheaf of modules on a ringed space,
let `z ∈ Γ(O, I¹)` and let `eⱼ ∈ Γ(Oⱼ, I⁰)` be primitives of `z` on the members of an open cover
of `O`. If the differences `eⱼ - eₖ`, which are sections of `M`, form the Čech coboundary of a
family `tⱼ ∈ Γ(Oⱼ, M)`, then the corrected primitives `eⱼ - tⱼ` glue to a primitive of `z` on
`O`.

## Main results

* `AlgebraicGeometry.PuncturedRestriction.exists_d_eq_of_cech`: the gluing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.PuncturedRestriction

variable {T : Type u} [TopologicalSpace T] {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]
  {M : SheafOfModules.{u} R} (I : InjectiveResolution M)

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)] in
/-- **Primitives glue along a Čech coboundary.** On an open `O` covered by opens `Oⱼ`, let
`eⱼ ∈ Γ(Oⱼ, I⁰)` be primitives of the restrictions of `z ∈ Γ(O, I¹)`, and let `tⱼ ∈ Γ(Oⱼ, M)` be
such that `tⱼ - tₖ` and `eⱼ - eₖ` agree on `Oⱼ ∩ Oₖ`. Then `z` has a primitive on `O`. -/
theorem exists_d_eq_of_cech {O : Opens T} {J : Type u} (Oj : J → Opens T) (hle : ∀ j, Oj j ≤ O)
    (hcov : O ≤ iSup Oj) (z : (secF R O).obj (I.cocomplex.X 1))
    (e : ∀ j, (secF R (Oj j)).obj (I.cocomplex.X 0))
    (he : ∀ j, (secF R (Oj j)).map (I.cocomplex.d 0 1) (e j) = (secRestrict R (hle j)).app _ z)
    (t : ∀ j, (secF R (Oj j)).obj M)
    (ht : ∀ j k, (secF R (Oj j ⊓ Oj k)).map (ι₀ I)
        ((secRestrict R inf_le_left).app _ (t j) - (secRestrict R inf_le_right).app _ (t k)) =
      (secRestrict R inf_le_left).app _ (e j) - (secRestrict R inf_le_right).app _ (e k)) :
    ∃ ε : (secF R O).obj (I.cocomplex.X 0), (secF R O).map (I.cocomplex.d 0 1) ε = z := by
  let ε' : ∀ j, (secF R (Oj j)).obj (I.cocomplex.X 0) :=
    fun j => e j - (secF R (Oj j)).map (ι₀ I) (t j)
  have hcompat : ∀ j k, (secRestrict R inf_le_left).app _ (ε' j) =
      (secRestrict R (inf_le_right : Oj j ⊓ Oj k ≤ Oj k)).app _ (ε' k) := by
    intro j k
    have h1 := ht j k
    rw [map_sub, ← secRestrict_app_map, ← secRestrict_app_map] at h1
    simp only [ε', map_sub]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h1.symm
  let G : ℕ → TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of T) := fun i =>
    ⟨((SheafOfModules.toSheaf R).obj (I.cocomplex.X i)).obj,
      ((SheafOfModules.toSheaf R).obj (I.cocomplex.X i)).property⟩
  obtain ⟨ε, hε, -⟩ := TopCat.Sheaf.existsUnique_gluing' (G 0) Oj O (fun j => homOfLE (hle j))
    hcov ε' hcompat
  refine ⟨ε, TopCat.Sheaf.eq_of_locally_eq' (G 1) Oj O (fun j => homOfLE (hle j)) hcov _ _
    (fun j => ?_)⟩
  change (secRestrict R (hle j)).app _ ((secF R O).map (I.cocomplex.d 0 1) ε) =
    (secRestrict R (hle j)).app _ z
  rw [secRestrict_app_map, show (secRestrict R (hle j)).app _ ε = ε' j from hε j]
  simp only [ε', map_sub, secF_map_ι₀_d_apply, sub_zero]
  exact he j

end AlgebraicGeometry.PuncturedRestriction

end
