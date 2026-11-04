module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusAlgClosure
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionZModRank
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Injectivity
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections

/-!
# Extending the ground field does not decrease the `ℓ`-torsion bound

Let `k` be a field, let `X` be a proper scheme over `k` and let `ℓ` be a prime. Pullback along
`X_{k'} ⟶ X` is injective on Picard groups for every extension `k'/k`
([Stacks, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5)). Hence

`dim_{F_ℓ} Pic(X)[ℓ] ≤ dim_{F_ℓ} Pic(X_{k'})[ℓ]`.

Combined with the invariance of the genus ([Stacks, Tag 0BY9], the genus clause) and of the
geometric genus under passage to an algebraic closure, this is the first reduction step of
[Stacks, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6): the inequality

`dim_{F_ℓ} Pic(X)[ℓ] ≤ dim_k H¹(X, 𝒪_X) + g_geom(X/k)`

for `X` of dimension at most one follows from the same inequality for `X_{k̄}` over `k̄`.

## Main results

* `AlgebraicGeometry.injective_schemePullbackClass_of_isProper`: for a proper scheme over a
  field, `Pic(X) → Pic(X_{k'})` is injective.
* `AlgebraicGeometry.finrank_picardTorsion_le_baseChange_field`:
  `dim_{F_ℓ} Pic(X)[ℓ] ≤ dim_{F_ℓ} Pic(X_{k'})[ℓ]`.
* `AlgebraicGeometry.finiteDimensional_picardTorsion_of_baseChange_field`: the `ℓ`-torsion of
  `Pic(X)` is finite-dimensional as soon as that of `Pic(X_{k'})` is.
* `AlgebraicGeometry.picardTorsion_bound_of_baseChange_algebraicClosure`: **the first reduction
  step of [Stacks, Tag 0CE6]**: the bound for `X_{k̄}` over `k̄` gives the bound for `X` over `k`.

## References

* [Stacks Project, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6)
* [Stacks Project, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Picard (ofScheme schemePullbackClass schemePullbackClassHom zsmulTorsion)

universe u

namespace AlgebraicGeometry

attribute [local instance] AddSubgroup.torsionBy.zmodModule

/-! ### Tag 0CC5 for a proper scheme over a field -/

/-- **[Stacks, Tag 0CC5] for a proper scheme over a field.** For every extension of fields
`k'/k` and every proper scheme `X` over `k`, the pullback map `Pic(X) → Pic(X_{k'})` is
injective. -/
theorem injective_schemePullbackClass_of_isProper {k k' : Type u} [Field k] [Field k']
    (φ : k →+* k') {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g] :
    Function.Injective
      (schemePullbackClass (pullback.fst g (Spec.map (CommRingCat.ofHom φ)))) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated g
  exact Stacks.AlgebraicGeometry.PicardBaseChange.injective_picardPullback_of_finiteDimensional
    X φ g
    (Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k g)

/-! ### The `F_ℓ`-dimension of the `ℓ`-torsion under extension of the ground field -/

/-- **`dim_{F_ℓ} Pic(X)[ℓ] ≤ dim_{F_ℓ} Pic(X_{k'})[ℓ]`** for a proper scheme `X` over a field
`k`, an extension `k'/k` and a prime `ℓ`, the `ℓ`-torsion upstairs being finite-dimensional. -/
theorem finrank_picardTorsion_le_baseChange_field {k k' : Type u} [Field k] [Field k']
    (φ : k →+* k') {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hfin : FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy
      (ofScheme (pullback g (Spec.map (CommRingCat.ofHom φ)))) (ℓ : ℤ))) :
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ≤
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy
        (ofScheme (pullback g (Spec.map (CommRingCat.ofHom φ)))) (ℓ : ℤ)) :=
  Stacks.Picard.finrank_zmodTorsion_le_of_injOn ℓ
    (schemePullbackClassHom (pullback.fst g (Spec.map (CommRingCat.ofHom φ))))
    (injective_schemePullbackClass_of_isProper φ g).injOn hfin

/-- **Finite-dimensionality of the `ℓ`-torsion of the Picard group descends along extension of
the ground field** of a proper scheme. -/
theorem finiteDimensional_picardTorsion_of_baseChange_field {k k' : Type u} [Field k] [Field k']
    (φ : k →+* k') {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hfin : FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy
      (ofScheme (pullback g (Spec.map (CommRingCat.ofHom φ)))) (ℓ : ℤ))) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) :=
  Stacks.Picard.finiteDimensional_zmodTorsion_of_injOn ℓ
    (schemePullbackClassHom (pullback.fst g (Spec.map (CommRingCat.ofHom φ))))
    (injective_schemePullbackClass_of_isProper φ g).injOn hfin

/-! ### The first reduction step of Tag 0CE6 -/

/-- **The first reduction step of [Stacks, Tag 0CE6]: the bound passes from `X_{k̄}` to `X`.**
Let `k` be a field, let `X` be a proper scheme of dimension at most one over `k` and let `ℓ` be
a prime. If the `ℓ`-torsion of `Pic(X_{k̄})` is finite-dimensional over `F_ℓ` and bounded by the
genus of `X_{k̄}` plus its geometric genus over `k̄`, then the `ℓ`-torsion of `Pic(X)` is
finite-dimensional over `F_ℓ` and bounded by the genus of `X` plus its geometric genus over `k`. -/
theorem picardTorsion_bound_of_baseChange_algebraicClosure (k : Type u) [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (hfin : FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme (pullback g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) (ℓ : ℤ)))
    (hbound : Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme (pullback g
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) (ℓ : ℤ)) ≤
        genus (pullback.snd g
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) +
          geometricGenus (AlgebraicClosure k) (pullback.snd g
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ≤
        genus g + geometricGenus k g := by
  set a := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hgenus : genus (pullback.snd g a) = genus g :=
    genus_baseChange k (AlgebraicClosure k) (pullback.fst g a) (pullback.snd g a) g
      (IsPullback.of_hasPullback g a)
  have hgeom : geometricGenus k g =
      geometricGenus (AlgebraicClosure k) (pullback.snd g a) :=
    geometricGenus_eq_geometricGenus_pullback_snd k g hdim
  refine ⟨finiteDimensional_picardTorsion_of_baseChange_field
    (algebraMap k (AlgebraicClosure k)) g ℓ hfin, ?_⟩
  refine le_trans (finrank_picardTorsion_le_baseChange_field
    (algebraMap k (AlgebraicClosure k)) g ℓ hfin) ?_
  rwa [hgeom, ← hgenus]

end AlgebraicGeometry

end
