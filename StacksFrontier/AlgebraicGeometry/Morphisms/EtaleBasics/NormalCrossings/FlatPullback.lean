module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.SmoothPullback

/-!
# Flat pullback of a strict normal crossings divisor

The scheme-theoretic inverse image of a strict normal crossings divisor along a flat morphism
with regular closed fibres is again a strict normal crossings divisor.

## Main results

* `Stacks.Divisors.isStrictNormalCrossingsDivisor_comap_of_flat`: pullback along a flat morphism
  with regular closed fibres preserves strict normal crossings divisors.

## Implementation notes

This generalizes `Stacks.Divisors.isStrictNormalCrossingsDivisor_comap`, where the morphism is
smooth: smoothness of `f : Y ⟶ X` enters that proof only through flatness of the stalk maps,
regularity of the closed fibres of the stalk maps, and local Noetherianness of `Y`. Here the
first is the `AlgebraicGeometry.Flat` instance, the second is the hypothesis `hfib`, and the
third is an instance hypothesis, since a flat morphism need not be locally of finite type.

## References

* [Stacks Project, Tag 0CBP](https://stacks.math.columbia.edu/tag/0CBP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-- At a point of the fibre product of a flat morphism with regular closed fibres with the
subscheme of a strict normal crossings divisor, the local ring of the source is regular and the
kernel of the stalk map of the first projection is cut out by an initial segment of a regular
system of parameters. -/
private theorem pullback_stalk_isSystemOfParameters_of_flat {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : Y ⟶ X) [AlgebraicGeometry.Flat f]
    (hfib : ∀ y : Y, IsRegularLocalRing ((Y.presheaf.stalk y) ⧸
      Ideal.map (f.stalkMap y).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (f y)))))
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossingsDivisor D)
    (z : (pullback f D.subschemeι).carrier) :
    let x := pullback.fst f D.subschemeι z
    IsRegularLocalRing (Y.presheaf.stalk x) ∧
      ∃ (rs : List (Y.presheaf.stalk x)) (r : ℕ),
        IsLocalRing.IsSystemOfParameters rs ∧
        Ideal.ofList rs = IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ∧
        1 ≤ r ∧ r ≤ rs.length ∧
        RingHom.ker ((pullback.fst f D.subschemeι).stalkMap z).hom =
          Ideal.span {(rs.take r).prod} := by
  classical
  let x := pullback.fst f D.subschemeι z
  let d := pullback.snd f D.subschemeι z
  have h : f x = D.subschemeι d :=
    congrArg (fun k : pullback f D.subschemeι ⟶ X => k z) pullback.condition
  let t := eqToHom (congrArg X.presheaf.stalk h) ≫ D.subschemeι.stalkMap d
  have hbase : IsRegularLocalRing (X.presheaf.stalk (f x)) ∧
      ∃ (rs : List (X.presheaf.stalk (f x))) (r : ℕ),
        IsLocalRing.IsSystemOfParameters rs ∧
        Ideal.ofList rs = IsLocalRing.maximalIdeal (X.presheaf.stalk (f x)) ∧
        1 ≤ r ∧ r ≤ rs.length ∧ RingHom.ker t.hom = Ideal.span {(rs.take r).prod} := by
    dsimp only [t]
    generalize hp : f x = p at h ⊢
    clear hp
    subst p
    simpa using hD.2 d
  obtain ⟨hA, rs, r, hrs, hgen, hr, hrle, hk⟩ := hbase
  let A := X.presheaf.stalk (f x)
  let B := Y.presheaf.stalk x
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat A B := AlgebraicGeometry.Flat.stalkMap f x
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have hF := hfib x
  have hB' := isRegularLocalRing_of_flat_of_regular_closedFibre A B hA hF
  obtain ⟨ts, hparams, hgens⟩ :=
    IsLocalRing.exists_isSystemOfParameters_append_of_flat (B := B) rs hrs hgen hF
  refine ⟨hB', rs.map (algebraMap A B) ++ ts, r, hparams, hgens, hr, ?_, ?_⟩
  · simpa only [List.length_append, List.length_map] using
      hrle.trans (Nat.le_add_right rs.length ts.length)
  · rw [ker_stalkMap_pullback_fst]
    change Ideal.map (algebraMap A B) (RingHom.ker t.hom) = _
    rw [hk, Ideal.map_span, Set.image_singleton]
    congr 1
    rw [List.take_append_of_le_length (by simpa using hrle), ← List.map_take, ← map_list_prod]

/-- The pullback of a strict normal crossings divisor along a flat morphism whose stalk maps have
regular closed fibres is a strict normal crossings divisor. This generalizes Stacks Project,
Tag 0CBP, where the morphism is smooth. -/
theorem isStrictNormalCrossingsDivisor_comap_of_flat
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [AlgebraicGeometry.Flat f]
    (hfib : ∀ y : Y, IsRegularLocalRing ((Y.presheaf.stalk y) ⧸
      Ideal.map (f.stalkMap y).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (f y)))))
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossingsDivisor D) :
    IsStrictNormalCrossingsDivisor (D.comap f) := by
  refine ⟨isPullbackDefined_of_flat f D hD.1, fun y ↦ ?_⟩
  set e := (D.comapIso f).hom with he'
  set g := pullback.fst f D.subschemeι with hg
  have H := pullback_stalk_isSystemOfParameters_of_flat f hfib D hD (e y)
  have H' : IsRegularLocalRing (Y.presheaf.stalk ((e ≫ g) y)) ∧
      ∃ (rs : List (Y.presheaf.stalk ((e ≫ g) y))) (r : ℕ),
        IsLocalRing.IsSystemOfParameters rs ∧
        Ideal.ofList rs = IsLocalRing.maximalIdeal (Y.presheaf.stalk ((e ≫ g) y)) ∧
        1 ≤ r ∧ r ≤ rs.length ∧
        RingHom.ker ((e ≫ g).stalkMap y).hom = Ideal.span {(rs.take r).prod} := by
    rw [ker_stalkMap_comp_of_isIso]
    exact H
  have he : e ≫ g = (D.comap f).subschemeι := D.comapIso_hom_fst f
  rw [he] at H'
  exact H'

end Stacks.Divisors

end
