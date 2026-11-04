module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# The stalk of `I𝒪_U` at a point of the open complement

For an algebraization situation, the stalk of the ideal `I𝒪_U` at a point `y` of `U` is the
image of `I` under the map `A → 𝒪_{U,y}`, and at a point lying over the closed subscheme it is a
proper ideal. Both facts are needed wherever the depth inequalities of chapter 52 are run, so
they are stated here once rather than in each development.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.Algebraization

/-- The stalk of `I𝒪_U` at `y` is the image of `I` under `A → 𝒪_{U,y}`. -/
public theorem stalk_idealOnOpen_eq_map (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) :
    IdealSheafData.stalk (idealOnOpen S) y = S.I.map (baseToPointStalk S y) := by
  have hT : (Scheme.IdealSheafData.ofIdealTop
        (S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom)).ideal ⟨⊤, isAffineOpen_top S.X⟩ =
      S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom := by
    simp [Scheme.IdealSheafData.ofIdealTop]
  rw [show idealOnOpen S = (Scheme.IdealSheafData.ofIdealTop
      (S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom)).comap S.U.ι from rfl,
    IdealSheafData.stalk_comap,
    IdealSheafData.stalk_eq_map_germ _ _ ⟨⊤, isAffineOpen_top S.X⟩ (Set.mem_univ _), hT,
    Ideal.map_map, Ideal.map_map]
  rfl

/-- At a point of `U ∩ Y` the stalk of `I𝒪_U` is a proper ideal. -/
public theorem stalk_idealOnOpen_le_maximalIdeal (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z) :
    IdealSheafData.stalk (idealOnOpen S) y ≤
      maximalIdeal (S.U.toScheme.presheaf.stalk y) := by
  let x : S.X := S.U.ι.base y
  let x₀ : PrimeSpectrum S.A := x
  let g : Γ(S.X, ⊤) →+* S.X.presheaf.stalk x := (S.X.presheaf.germ ⊤ x (Set.mem_univ x)).hom
  let f0 : S.A →+* S.X.presheaf.stalk x := g.comp (Scheme.ΓSpecIso (.of S.A)).inv.hom
  let f1 : S.X.presheaf.stalk x →+* S.U.toScheme.presheaf.stalk y := (S.U.ι.stalkMap y).hom
  have hIpx : S.I ≤ x₀.asIdeal := by
    have hx₀ : x₀ = S.Yι.base z := congrArg (fun t : S.X => (t : PrimeSpectrum S.A)) hyz
    rw [hx₀]
    intro a ha
    change Ideal.Quotient.mk S.I a ∈ (z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr ha) ▸ zero_mem _
  have hmaxX : Ideal.map f0 x₀.asIdeal = maximalIdeal (S.X.presheaf.stalk x) := by
    have htoStalk : f0 = (StructureSheaf.toStalk S.A x₀).hom := by
      dsimp only [f0, g, StructureSheaf.toStalk]
      rw [Scheme.ΓSpecIso_inv]
      rfl
    have : IsLocalRing ((structurePresheafInCommRingCat S.A).stalk x₀) :=
      inferInstanceAs (IsLocalRing (S.X.presheaf.stalk x))
    have hmapEq : algebraMap S.A ((structurePresheafInCommRingCat S.A).stalk x₀) =
        (StructureSheaf.toStalk S.A x₀).hom :=
      RingHom.ext (StructureSheaf.stalkAlgebra_map S.A x₀)
    have hbase : Ideal.map (StructureSheaf.toStalk S.A x₀).hom x₀.asIdeal =
        maximalIdeal ((structurePresheafInCommRingCat S.A).stalk x₀) := by
      simpa [hmapEq] using IsLocalization.AtPrime.map_eq_maximalIdeal x₀.asIdeal
        ((structurePresheafInCommRingCat S.A).stalk x₀)
    rw [htoStalk]
    exact hbase
  rw [stalk_idealOnOpen_eq_map,
    show baseToPointStalk S y = f1.comp f0 from rfl, ← Ideal.map_map]
  calc Ideal.map f1 (Ideal.map f0 S.I)
      ≤ Ideal.map f1 (maximalIdeal (S.X.presheaf.stalk x)) :=
        Ideal.map_mono ((Ideal.map_mono hIpx).trans hmaxX.le)
    _ = maximalIdeal (S.U.toScheme.presheaf.stalk y) :=
        IsLocalRing.map_maximalIdeal_of_surjective f1
          (ConcreteCategory.bijective_of_isIso (S.U.ι.stalkMap y)).2

end Stacks.Algebraization

end
