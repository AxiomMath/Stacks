module

public import StacksFrontier.AlgebraicGeometry.Cube.OpennessCover
public import StacksFrontier.AlgebraicGeometry.Cube.OpennessReduction
public import StacksFrontier.AlgebraicGeometry.Cube.OpennessFaces
public import StacksFrontier.AlgebraicGeometry.Cube.OpennessFibre

/-!
# The openness step of the theorem of the cube

Let `k` be a field, `X` and `Y` proper geometrically integral schemes over `k` with rational
points `x` and `y`, `R` a Noetherian `k`-algebra and `L` an invertible module on
`Q = (X ×_k Y) ×_k Spec R` which is trivial on the two faces `X_R = X × y × Spec R` and
`Y_R = x × Y × Spec R`. If `L` is trivial on the fibre of `Q` over a prime `𝔭` of `R`, then it is
trivial over a basic open neighbourhood of `𝔭` in `Spec R`. This is the openness step of the
theorem of the cube ([Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3), in the form
used by [Stacks, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)).

The proof takes finite affine covers of `X` and `Y` and applies
`AlgebraicGeometry.Cube.Openness.exists_basicOpen_of_fibre_inputs`, whose four fibrewise inputs
are `AlgebraicGeometry.Cube.Openness.h0_fibre`, `AlgebraicGeometry.Cube.Openness.h1_fibre`
(the Künneth input), `AlgebraicGeometry.Cube.Openness.exists_lift_DX` and
`AlgebraicGeometry.Cube.Openness.exists_lift_DY`.

## Main results

* `AlgebraicGeometry.Cube.exists_basicOpen_isTrivial_of_isTrivial_fiber`: the statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Cube

open Openness

/-- **The openness step of the theorem of the cube** ([Stacks, Tag 0BF3]): an invertible module
on `(X ×_k Y) ×_k Spec R`, trivial on the two faces, which is trivial on the fibre over a prime
`𝔭` of `R` is trivial over a basic open neighbourhood of `𝔭`. -/
theorem exists_basicOpen_isTrivial_of_isTrivial_fiber
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Algebra k R]
    (L : (pullback (pullback.fst f g ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible
      (pullback (pullback.fst f g ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k R)))).presheaf
      (pullback (pullback.fst f g ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))).ringCatIsSheaf L)
    (hfX : Nonempty ((Scheme.Modules.pullback (jX f g y hy R)).obj L ≅ SheafOfModules.unit _))
    (hfY : Nonempty ((Scheme.Modules.pullback (jY f g x hx R)).obj L ≅ SheafOfModules.unit _))
    (𝔭 : PrimeSpectrum R)
    (hfib : Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd
        (pullback.fst f g ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField))))).obj L ≅
          SheafOfModules.unit _)) :
    ∃ r : R, r ∉ 𝔭.asIdeal ∧ Nonempty ((Scheme.Modules.pullback
      ((pullback.snd (pullback.fst f g ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k R)))) ⁻¹ᵁ
        PrimeSpectrum.basicOpen (R := CommRingCat.of R) r).ι).obj L ≅
          SheafOfModules.unit _) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  obtain ⟨I, _, UX, hUXa, hUX⟩ := exists_finite_affine_cover X
  obtain ⟨J, _, UY, hUYa, hUY⟩ := exists_finite_affine_cover Y
  let : LinearOrder (I × J) :=
    LinearOrder.lift' (Fintype.equivFin (I × J)) (Fintype.equivFin (I × J)).injective
  have : L.IsQuasicoherent := by
    have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible (Q f g R).presheaf
        (Q f g R).ringCatSheaf.property L :=
      Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
    have := (coherent_flat_of_isInvertible (qR f g R) L hL').1
    exact (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent L).1
  exact exists_basicOpen_of_fibre_inputs f g x hx y hy R UX UY hUXa hUYa hUX hUY L hL 𝔭
    hfib.some
    (h0_fibre f g x hx y hy R UX UY hUXa hUYa hUX hUY L 𝔭 hfib)
    (h1_fibre f g x hx y hy R UX UY hUXa hUYa hUX hUY L 𝔭 hfib)
    (exists_lift_DX f g y hy UX UY hUXa hUX hUY L 𝔭 hfX)
    (exists_lift_DY f g x hx UX UY hUYa hUX hUY L 𝔭 hfY)

end AlgebraicGeometry.Cube

end
