module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Unconditional

/-!
# Smooth base change along a limit of smooth schemes holds

The proposition `Stacks.EtaleCohomology.SmoothLimitBaseChange`, the assertion of [Stacks, Tag 0F09]
with the torsion condition read as local annihilation of sections, is proved here outright. Its
reduction to the smooth base change theorem,
`Stacks.EtaleCohomology.smoothLimitBaseChange_of_smoothBaseChangeForSheaves`, is fed by [Stacks,
Theorem 0EYU], `Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth`.

The two state the torsion hypothesis differently. The reduction asks that every local section be
annihilated, on an étale covering, by a positive integer which is a unit in `Γ(S, 𝒪_S)`
(`Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn`); Theorem 0EYU asks that every element of
every stalk at a geometric point be annihilated by such an integer. The first implies the second:
an element of a stalk is the germ of a section over an étale neighbourhood of the geometric point,
the geometric point lifts along some member of the covering on which that section is annihilated,
and the germ is the germ of the restricted section. This is
`CategoryTheory.GrothendieckTopology.Point.exists_nsmul_eq_zero_sheafFiber_of_locallyAnnihilated`,
proved for any point of any site. The base scheme `S` of the integers' invertibility is the same
in both: in the reduction Theorem 0EYU is applied to the square `S_i ← S_i ×_S X` over `S ← X`,
whose smooth side `S_i ⟶ S` has target `S`.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.exists_nsmul_eq_zero_sheafFiber_of_locallyAnnihilated`
  — a locally annihilated abelian sheaf has annihilated fibres at every point of the site.
* `Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn.exists_nsmul_eq_zero_smallEtaleStalkAb` —
  the stalks of a sheaf with torsion of orders invertible on `S` are torsion of such orders.
* `Stacks.EtaleCohomology.smoothLimitBaseChange_holds` — the proposition
  `Stacks.EtaleCohomology.SmoothLimitBaseChange` holds.

## References

* [Stacks Project, Tag 0F09](https://stacks.math.columbia.edu/tag/0F09)
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w w' v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : J.Point.{w})
  [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} AddCommGrpCat.{w'}]
  [PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{w'})]

/-- **A locally annihilated abelian sheaf has annihilated fibres.** If every local section of an
abelian sheaf `F` is annihilated, along the arrows of some covering sieve, by integers satisfying
`P`, then every element of the fibre of `F` at a point of the site is annihilated by an integer
satisfying `P`: the element is the image of a section over some object, the point lifts along an
arrow of the covering sieve, and the element is the image of the restricted section. -/
theorem exists_nsmul_eq_zero_sheafFiber_of_locallyAnnihilated {P : ℕ → Prop}
    {F : Sheaf J AddCommGrpCat.{w'}} (hF : Stacks.EtaleCohomology.LocallyAnnihilated J P F)
    (a : ↑(Φ.sheafFiber.obj F)) : ∃ n : ℕ, P n ∧ n • a = 0 := by
  obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) a
  obtain ⟨R, hR, hk⟩ := hF X z
  obtain ⟨Y, f, hf, y, rfl⟩ := Φ.jointly_surjective R hR x
  obtain ⟨n, hn, hz⟩ := hk Y f hf
  refine ⟨n, hn, ?_⟩
  have h : n • Φ.toPresheafFiber Y y F.obj (F.obj.map f.op z) = 0 := by
    rw [← map_nsmul, hz, map_zero]
  rw [← Φ.toPresheafFiber_w_apply f y F.obj z]
  exact h

end CategoryTheory.GrothendieckTopology.Point

namespace Stacks.EtaleCohomology

/-- **The stalks of a sheaf with torsion of orders invertible on `S` are such torsion.** If every
local section of an abelian sheaf `F` on `X_étale` is annihilated, on an étale covering, by a
positive integer which is a unit in `Γ(S, 𝒪_S)`, then so is every element of the stalk of `F` at
every geometric point of `X`. -/
theorem HasTorsionOrdersInvertibleOn.exists_nsmul_eq_zero_smallEtaleStalkAb
    {S X : Scheme.{u}} {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (hF : HasTorsionOrdersInvertibleOn S F) (t : GeometricPoint X)
    (a : ↑((smallEtaleStalkAb t.hom).obj F)) :
    ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ n • a = 0 := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨n, ⟨hn, hu⟩, ha⟩ :=
    (pointSmallEtale t.hom).exists_nsmul_eq_zero_sheafFiber_of_locallyAnnihilated hF a
  exact ⟨n, hn, by rwa [Int.cast_natCast], ha⟩

/-- **Smooth base change along a limit of smooth schemes holds** ([Stacks, Tag 0F09], with the
torsion condition read as local annihilation of sections). Let `S' = lim S_i` be a directed
inverse limit of schemes `S_i` smooth over `S` with affine transition morphisms, let `f : X ⟶ S`
be quasi-compact and quasi-separated and `X' = X ×_S S'`. Then the base change map
`g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism for every `E ∈ D⁺(X_étale)` whose cohomology
sheaves have torsion of orders invertible on `S`.

This is `Stacks.EtaleCohomology.smoothLimitBaseChange_of_smoothBaseChangeForSheaves` fed by the
smooth base change theorem [Stacks, Theorem 0EYU], whose stalkwise torsion hypothesis is supplied
by `Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn.exists_nsmul_eq_zero_smallEtaleStalkAb`. -/
theorem smoothLimitBaseChange_holds : SmoothLimitBaseChange.{u} :=
  smoothLimitBaseChange_of_smoothBaseChangeForSheaves
    fun _ _ _ _ f g h e sq hf hg hg' q ℱ hℱ => by
      have := hf; have := hg; have := hg'
      exact SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth f h e g sq ℱ
        (fun t a => hℱ.exists_nsmul_eq_zero_smallEtaleStalkAb t a) q

end Stacks.EtaleCohomology

end
