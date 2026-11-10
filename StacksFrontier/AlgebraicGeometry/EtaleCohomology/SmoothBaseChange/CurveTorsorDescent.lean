module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AlgebraicExtensionCohomologyColimit
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CurveFirstDegreeReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.TorsorCover

/-!
# A class over `\bar k` comes from a finite extension of `k`

Let `X` be a quasi-compact and quasi-separated scheme over a field `k`, `\bar k` an algebraic
extension, and `S` an abelian group. Every class in `H^q(X_{\bar k}, S)` with constant
coefficients is the restriction of a class in `H^q(X_E, S)` for a subextension `E` of finite
degree ([Stacks, Tag 03Q6]). This is the limit argument of the proof of [Stacks, Tag 0EYT],
performed on the cohomology class rather than on the cover it defines.

## Main results

* `Stacks.EtaleCohomology.sheafH_map_etaleCohomologyMapTo` — post-composition of the cohomology
  map of a morphism with a map of sheaves.
* `Stacks.EtaleCohomology.exists_finite_stage_class` — the descent of a constant-coefficient
  class to a finite stage.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

/-- For a morphism of schemes `k : X₂ ⟶ X₁`, a map `w : k⁻¹ A ⟶ B` and a map of sheaves
`φ : B ⟶ C`, the map `Sheaf.H.map φ p` composed with `etaleCohomologyMapTo k w p` is
`etaleCohomologyMapTo k (w ≫ φ) p`. -/
theorem sheafH_map_etaleCohomologyMapTo {X₁ X₂ : Scheme.{u}} (k : X₂ ⟶ X₁)
    {A : Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B C : Sheaf X₂.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ B) (φ : B ⟶ C) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} A p) :
    Sheaf.H.map φ p (etaleCohomologyMapTo k w p x) = etaleCohomologyMapTo k (w ≫ φ) p x := by
  rw [etaleCohomologyMapTo, etaleCohomologyMapTo, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, ← Sheaf.H.map_comp_apply]

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A constant-coefficient class over an algebraic extension comes from a finite stage.** Let `X`
be quasi-compact and quasi-separated over `k`, `L/k` algebraic and `S` an abelian group. Every
`ζ ∈ H^q(X_L, S)` is the image, under the cohomology map of the projection `X_L ⟶ X_E` and a map
of sheaves, of a class in `H^q(X_E, S)` for a subextension `E` of finite degree. -/
theorem exists_finite_stage_class [CompactSpace X] [QuasiSeparatedSpace X] (L : Type u)
    [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] (S : AddCommGrpCat.{u + 1}) {q : ℕ}
    (ζ : Sheaf.H.{u + 1, u + 1} ((constantSheaf (pullback (spectrumMap k L) f).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj S) q) :
    ∃ (E : FExt k L)
      (ζE : Sheaf.H.{u + 1, u + 1}
        ((constantSheaf (pullback (spectrumMap k E.1) f).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj S) q)
      (w : (etaleAbelianInverseImage.{u, u + 1}
          ((fextPullbackCone (k := k) (K := L) X f).π.app (op E))).obj
          ((constantSheaf _ AddCommGrpCat.{u + 1}).obj S) ⟶
            (constantSheaf _ AddCommGrpCat.{u + 1}).obj S),
      etaleCohomologyMapTo ((fextPullbackCone (k := k) (K := L) X f).π.app (op E)) w q ζE = ζ := by
  let cL := (etaleAbelianInverseImageConstantIso.{u, u + 1}
    (pullback.snd (spectrumMap k L) f)).app S
  obtain ⟨E, x, hx⟩ := exists_finiteDimensional_eq_etaleCohomologyMapTo_of_isAlgebraic f
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj S) q (Sheaf.H.map cL.inv q ζ)
  let cE := (etaleAbelianInverseImageConstantIso.{u, u + 1}
    (pullback.snd (spectrumMap k E.1) f)).app S
  let π : pullback (spectrumMap k L) f ⟶ pullback (spectrumMap k E.1) f :=
    (fextPullbackCone (k := k) (K := L) X f).π.app (op E)
  have hπ : pullback.snd (spectrumMap k L) f = π ≫ pullback.snd (spectrumMap k E.1) f :=
    (Over.w ((Over.pullback f).map ((fextOverCone (k := k) (K := L)).π.app (op E)))).symm
  let c := (etaleAbelianInverseImageCompIso'.{u, u + 1} π (pullback.snd (spectrumMap k E.1) f)
    (pullback.snd (spectrumMap k L) f) hπ).inv.app
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj S)
  have hx' : etaleCohomologyMapTo π c q x = Sheaf.H.map cL.inv q ζ := hx
  refine ⟨E, Sheaf.H.map cE.hom q x, (etaleAbelianInverseImage.{u, u + 1} π).map cE.inv ≫ c ≫
    cL.hom, ?_⟩
  change etaleCohomologyMapTo π ((etaleAbelianInverseImage.{u, u + 1} π).map cE.inv ≫ c ≫
    cL.hom) q (Sheaf.H.map cE.hom q x) = ζ
  rw [etaleCohomologyMapTo_sheafH_map, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, ← sheafH_map_etaleCohomologyMapTo, hx',
    ← Sheaf.H.map_comp_apply,
    Iso.inv_hom_id, Sheaf.H.map_id_apply]

end Stacks.EtaleCohomology

end
