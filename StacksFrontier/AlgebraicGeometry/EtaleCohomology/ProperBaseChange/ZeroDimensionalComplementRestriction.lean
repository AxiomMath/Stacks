module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteDirectImageRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteOverFieldRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionDegreewise

/-!
# Restriction to a scalar extension across a complement finite over the base field

Let `k ⊆ k'` be separably closed fields, `π : X ⟶ Spec k` a scheme over `k`, `i : Z ⟶ X` a
closed immersion with `Z` finite over `k`, and `j : U ⟶ X` an open immersion onto the
complement. For an abelian sheaf `F` on `X_étale` the short exact sequence of Stacks Project Tag
095L,

`0 → j_! j^{-1} F → F → i_* i^{-1} F → 0`,

has a third term on which restriction to `X_{k'}` is bijective in every degree: by the transfer
along the finite morphism `i`
(`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_directImage_iff_of_isFinite`)
this is restriction on `Z`, and `Z` is finite over a separably closed field
(`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_isFinite_of_isSepClosed`).
So surjectivity of restriction in degree `q` passes between `F` and `j_! j^{-1} F`, which is the
part of Stacks Project Tag 0GJA that statement (7) of Situation 0A52 uses.

Everything below lives in the namespace `Stacks.EtaleCohomology`.

## Main results

* `isPullback_scalarExtension_closed`: the cartesian square comparing the scalar extension of
  `Z` with that of `X`.
* `etaleCohomologyRestrictionMap_bijective_directImage_of_isFinite_comp`: restriction to
  `X_{k'}` is bijective on the cohomology of `i_* H`, for `i` finite and `Z` finite over `k`.
* `surjective_etaleCohomologyRestrictionMap_of_openClosed_finite` and
  `surjective_etaleCohomologyRestrictionMap_extensionByZero_of_openClosed_finite`: the two
  directions of the transfer of surjectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']
  {X Z : Scheme.{u}} (π : X ⟶ Spec (.of k)) (i : Z ⟶ X)

/-- The morphism from the scalar extension of `Z` to that of `X` induced by `i`. -/
abbrev scalarExtensionCompMap : scalarExtension k k' (i ≫ π) ⟶ scalarExtension k k' π :=
  pullback.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

/-- **The scalar extension of `Z` is the base change of `i` along the scalar extension of `X`.**
-/
theorem isPullback_scalarExtension_closed :
    IsPullback (scalarExtensionFst k k' (i ≫ π)) (scalarExtensionCompMap k k' π i) i
      (scalarExtensionFst k k' π) := by
  have houter : IsPullback (scalarExtensionCompMap k k' π i ≫
      pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
      (scalarExtensionFst k k' (i ≫ π)) (Spec.map (CommRingCat.ofHom (algebraMap k k')))
      (i ≫ π) := by
    rw [pullback.lift_snd]
    exact (IsPullback.of_hasPullback (i ≫ π) _).flip
  exact (IsPullback.of_right houter (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback π _).flip).flip

variable [IsSepClosed k] [IsSepClosed k'] [IsFinite i] [IsFinite (i ≫ π)]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' (i ≫ π)).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Restriction is bijective on the direct image along a finite `i` with source finite over
`k`.** -/
theorem etaleCohomologyRestrictionMap_bijective_directImage_of_isFinite_comp
    (H : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' π)
      ((etaleAbelianDirectImage.{u, 0} i).obj H) q) :=
  (etaleCohomologyRestrictionMap_bijective_directImage_iff_of_isFinite.{u, w} i _ _ _
    (isPullback_scalarExtension_closed k k' π i) H q).mpr
    (etaleCohomologyRestrictionMap_bijective_of_isFinite_of_isSepClosed k k' (i ≫ π) H q)

variable {U : Scheme.{u}} [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)

include hij in
/-- **Surjectivity passes from `j_! j^{-1} F` to `F`.** If restriction to `X_{k'}` is surjective
in degree `q` and injective in degree `q + 1` on `j_! j^{-1} F`, it is surjective in degree `q`
on `F`. -/
theorem surjective_etaleCohomologyRestrictionMap_of_openClosed_finite
    (hsurj : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' π)
      ((extensionByZero.{u, 0} j).obj ((etaleRestriction.{u, 0} j).obj F)) q))
    (hinj : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' π)
      ((extensionByZero.{u, 0} j).obj ((etaleRestriction.{u, 0} j).obj F)) (q + 1))) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' π)
      F q) := by
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} i j hij F
  exact surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_injective.{u, 0, w} _ hS q
    hsurj (etaleCohomologyRestrictionMap_bijective_directImage_of_isFinite_comp k k' π i _ q).2
    hinj

include hij in
/-- **Surjectivity passes from `F` to `j_! j^{-1} F`.** If restriction to `X_{k'}` is surjective
in degree `q` on `F`, it is surjective in degree `q` on `j_! j^{-1} F`. -/
theorem surjective_etaleCohomologyRestrictionMap_extensionByZero_of_openClosed_finite
    (hsurj : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' π) F q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' π)
      ((extensionByZero.{u, 0} j).obj ((etaleRestriction.{u, 0} j).obj F)) q) := by
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} i j hij F
  exact surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_X₃.{u, 0, w} _ hS q hsurj
    (etaleCohomologyRestrictionMap_bijective_directImage_of_isFinite_comp k k' π i _ q).1
    (fun m _ ↦
      (etaleCohomologyRestrictionMap_bijective_directImage_of_isFinite_comp k k' π i _ m).2)

end Stacks.EtaleCohomology

end
