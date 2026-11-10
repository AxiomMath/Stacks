module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.EffaceableRestriction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FilteredColimitClasses
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FiniteDirectImageEffacement

/-!
# Closure properties of effaceability on a closed subscheme

Let `i : Z ⟶ X` be a morphism of schemes and `P` a property of abelian sheaves on `X_étale`. Say
that an abelian sheaf `F` on `X_étale` is *effaceable along `i` in `P`* if every class
`ξ ∈ H^q(Z, i^{-1} F)` with `q > 0` dies along `i^{-1} φ` for some monomorphism `φ : F ⟶ F'` with
`F'` in `P`. This is the conclusion of [Stacks, Tag 09ZE] (with `P` the torsion sheaves), and the
shape of the hypotheses `heffY` of
`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_effaceable`.

The proof of Stacks 09ZE reduces the general case to the sheaves `f_* M` through three closure
properties, proved here:

* a subsheaf of an effaceable sheaf is effaceable;
* a finite direct sum of effaceable sheaves is effaceable, when `P` is stable under finite direct
  sums;
* a filtered colimit of effaceable sheaves is effaceable when `Z` is quasi-compact and
  quasi-separated and `P` is stable under the pushouts `G' ⊔_G F` with `G'` and `F` in `P`
  (Stacks 03Q5 on `Z`, and the pushout step of the source).

The case `F = f_* N` for a finite `f` is reduced to the vanishing of restrictions along finite
surjective covers of `Y ×_X Z` by
`Stacks.EtaleCohomology.isEffaceableAlong_directImage_of_isFinite`.

## Main definitions

* `Stacks.EtaleCohomology.IsEffaceableAlong` — effaceability of a sheaf along `i` in `P`.

## Main results

* `Stacks.EtaleCohomology.IsEffaceableAlong.of_mono`
* `Stacks.EtaleCohomology.IsEffaceableAlong.biproduct`
* `Stacks.EtaleCohomology.IsEffaceableAlong.of_isColimit`
* `Stacks.EtaleCohomology.isEffaceableAlong_directImage_of_isFinite`

## References

* [Stacks Project, Tag 09ZE](https://stacks.math.columbia.edu/tag/09ZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- Abelian sheaves on a small étale site have finite biproducts. -/
local instance {X : Scheme.{u}} :
    HasFiniteBiproducts (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {X Z : Scheme.{u}} (i : Z ⟶ X)
  (P : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))

/-- An abelian sheaf `F` on `X_étale` is *effaceable along `i : Z ⟶ X` in `P`* if every class of
positive degree in the cohomology of `i^{-1} F` dies along the inverse image of a monomorphism
`F ⟶ F'` into a sheaf `F'` with `P F'`. -/
def IsEffaceableAlong (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj F) q,
    ∃ (F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ F'),
      Mono φ ∧ P F' ∧ ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map φ)) (add_zero q) = 0

namespace IsEffaceableAlong

variable {i P}

/-- **A subsheaf of an effaceable sheaf is effaceable.** -/
theorem of_mono {G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (m : G ⟶ H) [Mono m]
    (hH : IsEffaceableAlong i P H) : IsEffaceableAlong i P G := by
  intro q hq ξ
  obtain ⟨H', ψ, hψ, hP, hkill⟩ :=
    hH q hq (ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map m)) (add_zero q))
  refine ⟨H', m ≫ ψ, mono_comp m ψ, hP, ?_⟩
  rw [Functor.map_comp, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero, hkill]

/-- **A finite direct sum of effaceable sheaves is effaceable**, when `P` is stable under finite
direct sums. -/
theorem biproduct {ι : Type} [Finite ι] (A : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hP : ∀ B : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}, (∀ k, P (B k)) →
      P (⨁ B))
    (hA : ∀ k, IsEffaceableAlong i P (A k)) : IsEffaceableAlong i P (⨁ A) := by
  have := Fintype.ofFinite ι
  intro q hq ξ
  let G := etaleAbelianInverseImage.{u, 0} i
  choose B φ hφ hPB hkill using fun k =>
    hA k q hq (ξ.comp (Ext.mk₀ (G.map (biproduct.π A k))) (add_zero q))
  refine ⟨⨁ B, biproduct.map φ, inferInstance, hP B hPB, ?_⟩
  -- write the identity of `⨁ A` as the sum of its projections followed by its inclusions
  have htot : G.map (biproduct.map φ) =
      ∑ k, G.map (biproduct.π A k) ≫ G.map (φ k) ≫ G.map (biproduct.ι B k) := by
    rw [← Category.id_comp (biproduct.map φ), ← biproduct.total, Preadditive.sum_comp,
      Functor.map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Category.assoc, biproduct.ι_map, Functor.map_comp, Functor.map_comp]
  have hsum : ∀ (s : Finset ι) (f : ι → (G.obj (⨁ A) ⟶ G.obj (⨁ B))),
      Ext.mk₀ (∑ k ∈ s, f k) = ∑ k ∈ s, Ext.mk₀ (f k) := fun s f =>
    map_sum (Ext.addEquiv₀ (X := G.obj (⨁ A)) (Y := G.obj (⨁ B))).symm f s
  rw [htot, hsum]
  have hlin : ξ.comp (∑ k, Ext.mk₀ (G.map (biproduct.π A k) ≫ G.map (φ k) ≫
      G.map (biproduct.ι B k))) (add_zero q) = ∑ k, ξ.comp (Ext.mk₀ (G.map (biproduct.π A k) ≫
        G.map (φ k) ≫ G.map (biproduct.ι B k))) (add_zero q) :=
    map_sum (Ext.bilinearComp _ _ _ q 0 q (add_zero q) ξ) _ _
  rw [hlin]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [← Category.assoc, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero, hkill k, Ext.zero_comp]
/-- **A filtered colimit of effaceable sheaves is effaceable** (the first reduction of the proof
of Stacks 09ZE). Let `Z` be quasi-compact and quasi-separated, `F = colim_j G_j` a filtered
colimit with every `G_j` effaceable along `i` in `P`, and suppose `P` contains `F` and is stable
under the pushouts `G' ⊔_{G_j} F` along monomorphisms `G_j ⟶ G'` with `P G'`. Then `F` is
effaceable along `i` in `P`: a class of `i^{-1} F` comes from some `i^{-1} G_j` (Stacks 03Q5 on
`Z`, inverse image commuting with colimits), it is effaced there by a monomorphism `G_j ⟶ G'`,
and the pushout `F ⟶ G' ⊔_{G_j} F` effaces it on `F`. -/
theorem of_isColimit [CompactSpace Z] [QuasiSeparatedSpace Z]
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (c : Cocone D) (hc : IsColimit c)
    (_hPF : P c.pt)
    (hpush : ∀ (j : J) {G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (ι : D.obj j ⟶ G'),
      Mono ι → P G' → P (pushout ι (c.ι.app j)))
    (hD : ∀ j, IsEffaceableAlong i P (D.obj j)) : IsEffaceableAlong i P c.pt := by
  intro q hq ξ
  let G := etaleAbelianInverseImage.{u, 0} i
  have : PreservesColimitsOfSize.{u + 1, u + 1} G :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} i).leftAdjoint_preservesColimits
  obtain ⟨j, ζ, hζ⟩ := exists_comp_mk₀_eq_of_isColimit Z (D ⋙ G) (G.mapCocone c)
    (isColimitOfPreserves G hc) q ξ
  obtain ⟨G', ι, hι, hPG', hkill⟩ := hD j q hq ζ
  obtain ⟨hmono, hzero⟩ := effaces_pushout_inr.{u, 0, u + 1} i (c.ι.app j) ι q ζ hkill
  refine ⟨pushout ι (c.ι.app j), pushout.inr ι (c.ι.app j), hmono, hpush j ι hι hPG', ?_⟩
  rw [← hζ]
  exact hzero

end IsEffaceableAlong

/-- **Effaceability of a finite direct image** (the `f_* M` step of the proof of Stacks 09ZE).
Let `f : Y ⟶ X` be finite with base change `f_Z : Y_Z ⟶ Z` along `i`, and `N` an abelian sheaf on
`Y_étale`. Suppose every positive-degree class of `N|_{Y_Z}` restricts to zero on `Y' ×_Y Y_Z`
for some finite surjective `π : Y' ⟶ Y` with `P (f_* π_* π^{-1} N)`. Then `f_* N` is effaceable
along `i` in `P`, by the monomorphisms `f_* N ⟶ f_* π_* π^{-1} N`. -/
theorem isEffaceableAlong_directImage_of_isFinite {Y YZ : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    (g : YZ ⟶ Y) (fZ : YZ ⟶ Z) (sq : IsPullback g fZ f i)
    (N : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hcov : ∀ (q : ℕ), 0 < q → ∀ η : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} g).obj N) q,
      ∃ (Y' : Scheme.{u}) (π : Y' ⟶ Y), IsFinite π ∧ Surjective π ∧
        P ((etaleAbelianDirectImage.{u, 0} f).obj ((etaleAbelianDirectImage.{u, 0} π).obj
          ((etaleAbelianInverseImage.{u, 0} π).obj N))) ∧
        etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π g) _ q η = 0) :
    IsEffaceableAlong i P ((etaleAbelianDirectImage.{u, 0} f).obj N) := by
  intro q hq ξ
  obtain ⟨Y', π, hπ, hsurj, hP, hres⟩ := hcov q hq (finiteDirectImageTransport f i g fZ sq N q ξ)
  have := mono_etaleAbelianUnit_of_surjective π N
  refine ⟨_, (etaleAbelianDirectImage.{u, 0} f).map
    ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app N), inferInstance, hP, ?_⟩
  exact comp_directImage_unit_eq_zero_of_restriction_eq_zero f i g fZ sq π (pullback.fst π g)
    (pullback.snd π g) (IsPullback.of_hasPullback π g) N q ξ hres

end Stacks.EtaleCohomology
