module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RefinedTorsionSiteTransfer
public import StacksFrontier.AlgebraicGeometry.Etale.RefinedTorsionStalk

/-!
# Smooth base change along a limit of smooth schemes

[Stacks, Tag 0F09]: let `S` be a scheme, let `S' = lim S_i` be a directed inverse limit of schemes
`S_i` smooth over `S` with affine transition morphisms, let `f : X ⟶ S` be quasi-compact and
quasi-separated and let `X' = X ×_S S'`, with projections `f' : X' ⟶ S'` and `g' : X' ⟶ X`. Then
the base change map `g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism for every
`E ∈ D⁺(X_étale)` whose cohomology sheaves `H^q(E)` have stalks which are torsion of orders
invertible on `S`.

The torsion hypothesis is stated as in the source: every element of the stalk of every `H^q(E)`
at every geometric point of `X` is annihilated by a positive integer which is a unit on `S`. The
proof is `Stacks.EtaleCohomology.smoothLimitBaseChange_holds`, whose torsion hypothesis is the
local annihilation of sections, `Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn`. The two
conditions agree
(`Stacks.EtaleCohomology.hasTorsionOrdersInvertibleOn_iff_forall_smallEtaleStalkAb`): local
annihilation gives annihilated stalks by
`Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn.exists_nsmul_eq_zero_smallEtaleStalkAb`, and
the converse is the stalk criterion for local annihilation on the size-bounded small étale site,
`AlgebraicGeometry.SmallEtale.isLocallyAnnihilatedBy_of_forall_etaleStalk`, carried to the small
étale site of `X` by `Stacks.Torsion.isLocallyAnnihilatedBy_of_pushforward` along the dense
subsite inclusion, the stalks agreeing by `AlgebraicGeometry.smallEtaleStalkAb_sheafEquiv_obj_iso`.

## Main results

* `Stacks.EtaleCohomology.hasTorsionOrdersInvertibleOn_iff_forall_smallEtaleStalkAb` — an abelian
  sheaf on `X_étale` has torsion of orders invertible on `S` exactly when its stalks at all
  geometric points do.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_app_of_smoothLimit` —
  [Stacks, Tag 0F09].

## Implementation notes

The base change map is `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, which is
constructed under the standard model `HasDerivedCategory.standard`; that fixes the model of the
derived categories here.

## References

* [Stacks Project, Tag 0F09](https://stacks.math.columbia.edu/tag/0F09)
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- `smallEtaleDerivedBaseChangeAb` (BaseChangeHigher/BaseChangeCondition.lean:220) is built under
-- the standard model, so its components live in the standard bounded below derived categories.
attribute [local instance] HasDerivedCategory.standard

/-- **Torsion of orders invertible on `S` is detected on stalks.** An abelian sheaf `F` on
`X_étale` all of whose stalks at geometric points are torsion of orders invertible on `S` has
every local section annihilated, on an étale covering, by a positive integer which is a unit on
`S`. -/
theorem hasTorsionOrdersInvertibleOn_of_forall_smallEtaleStalkAb {S X : Scheme.{u}}
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (hF : ∀ (t : GeometricPoint X) (a : ↑((smallEtaleStalkAb t.hom).obj F)),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ n • a = 0) :
    HasTorsionOrdersInvertibleOn S F := by
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  let N : Set ℕ := {n | 0 < n ∧ IsUnit ((n : ℕ) : Γ(S, ⊤))}
  refine Stacks.Torsion.isLocallyAnnihilatedBy_of_pushforward (SmallEtale.topology B X hX)
    X.smallEtaleTopology (SmallEtale.toEtaleSite B X hX) N F ?_
  refine SmallEtale.isLocallyAnnihilatedBy_of_forall_etaleStalk.{u, 0} B X hX N _ fun t g => ?_
  let E := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  let e : (smallEtaleStalkAb t.hom).obj F ≅
      etaleStalk B X hX t (((SmallEtale.toEtaleSite B X hX).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (SmallEtale.topology B X hX) X.smallEtaleTopology).obj F).obj :=
    (smallEtaleStalkAb t.hom).mapIso (E.counitIso.app F).symm ≪≫
      smallEtaleStalkAb_sheafEquiv_obj_iso B ⟨X, hX⟩ t (E.inverse.obj F)
  obtain ⟨n, hn, hu, hz⟩ := hF t (e.inv g)
  refine ⟨n, ⟨hn, by rwa [Int.cast_natCast] at hu⟩, ?_⟩
  have hg : e.hom (e.inv g) = g := by simp
  rw [← hg, ← map_nsmul, hz, map_zero]

/-- **Torsion of orders invertible on `S`, locally and on stalks.** An abelian sheaf on `X_étale`
has every local section annihilated, on an étale covering, by a positive integer which is a unit
on `S` exactly when every element of every stalk at a geometric point is annihilated by such an
integer. -/
theorem hasTorsionOrdersInvertibleOn_iff_forall_smallEtaleStalkAb {S X : Scheme.{u}}
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    HasTorsionOrdersInvertibleOn S F ↔
      ∀ (t : GeometricPoint X) (a : ↑((smallEtaleStalkAb t.hom).obj F)),
        ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ n • a = 0 :=
  ⟨fun hF t a => hF.exists_nsmul_eq_zero_smallEtaleStalkAb t a,
    hasTorsionOrdersInvertibleOn_of_forall_smallEtaleStalkAb F⟩

/-- **Smooth base change along a limit of smooth schemes** ([Stacks, Tag 0F09]). Let `S` be a
scheme and let `S' = lim S_i` be a directed inverse limit of schemes `S_i` smooth over `S` with
affine transition morphisms: an inverse system `D` over a directed nonempty preorder `I`, with
structure morphisms `p_i : S_i ⟶ S` compatible with the transitions, a limit cone `c` with point
`S'`, and `g : S' ⟶ S` the composite of each leg of `c` with `p_i`. Let `f : X ⟶ S` be
quasi-compact and quasi-separated and let `X' = X ×_S S'` be a fibre product, with projections
`f' : X' ⟶ S'` and `g' : X' ⟶ X`. Then for every `E ∈ D⁺(X_étale)` whose cohomology sheaves
`H^q(E)` have stalks which are torsion of orders invertible on `S` (every element of the stalk at
every geometric point is killed by a positive integer which is a unit on `S`), the base change map
`g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism. -/
@[stacks 0F09]
theorem isIso_smallEtaleDerivedBaseChangeAb_app_of_smoothLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {S : Scheme.{u}}
    (D : Iᵒᵖ ⥤ Scheme.{u}) (p : D ⟶ (Functor.const Iᵒᵖ).obj S) (hp : ∀ i, Smooth (p.app i))
    (haff : ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j), IsAffineHom (D.map a)) (c : Cone D) (hc : IsLimit c)
    (g : c.pt ⟶ S) (hg : ∀ i, c.π.app i ≫ p.app i = g) {X X' : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (f' : X' ⟶ c.pt) (g' : X' ⟶ X)
    (sq : IsPullback f' g' g f) (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (hE : ∀ (q : ℤ) (t : GeometricPoint X)
      (a : ↑((smallEtaleStalkAb t.hom).obj
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology X) Ab.{u + 1}) q).obj E))),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ n • a = 0) :
    IsIso ((smallEtaleDerivedBaseChangeAb g f f' g' sq.w).app E) :=
  smoothLimitBaseChange_holds I S D p hp haff c hc g hg X X' f f' g' sq E fun q =>
    hasTorsionOrdersInvertibleOn_of_forall_smallEtaleStalkAb _ (hE q)

end Stacks.EtaleCohomology

end
