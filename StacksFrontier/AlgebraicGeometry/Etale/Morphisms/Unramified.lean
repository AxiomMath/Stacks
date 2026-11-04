module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Stalkwise unramifiedness of a morphism of schemes

For a morphism locally of finite type to a locally Noetherian scheme, unramifiedness at a point
can be read off the induced homomorphism of local rings: it is formal unramifiedness of that
homomorphism. A morphism is stalkwise unramified when it is stalkwise unramified at every point
of its source. This agrees with the affine-neighbourhood notion of unramifiedness.

## Main definitions

* `AlgebraicGeometry.StalkwiseUnramifiedAt` expresses unramifiedness at a point using the map
  on stalks.
* `AlgebraicGeometry.StalkwiseUnramified` expresses pointwise unramifiedness of a morphism.

## Main results

* `AlgebraicGeometry.unramifiedAt_iff_morphisms_unramifiedAt` compares the definition using the
  map on stalks with the definition using affine neighbourhoods.

## References

* [Stacks Project, Tag 024N](https://stacks.math.columbia.edu/tag/024N)
* [Stacks Project, Tag 039J](https://stacks.math.columbia.edu/tag/039J)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A locally finite type morphism to a locally Noetherian scheme is unramified at `x` if its
map on local rings at `x` is unramified. -/
@[stacks 024N "part (1)"]
abbrev StalkwiseUnramifiedAt {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] (x : X) : Prop :=
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- A locally finite type morphism to a locally Noetherian scheme is unramified if it is
unramified at every point of its source. -/
@[stacks 024N "part (2)"]
class StalkwiseUnramified {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] : Prop where
  /-- The morphism is stalkwise unramified at every point of its source. -/
  unramifiedAt (x : X) : StalkwiseUnramifiedAt f x

/-- Formal unramifiedness of the stalk map at `x` is membership of the corresponding prime in
the unramified locus of the algebra of sections on affine neighbourhoods. -/
private lemma formallyUnramified_stalkMap_iff
    {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X} (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyUnramified ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.unramifiedLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p := ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyUnramified_algebraMap]
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · refine ⟨fun _ => Algebra.FormallyUnramified.comp Γ(Y, U) (Localization.AtPrime p)
      (Localization.AtPrime q), fun h => ?_⟩
    have : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime q) := h
    exact Algebra.FormallyUnramified.of_restrictScalars Γ(Y, U) (Localization.AtPrime p)
      (Localization.AtPrime q)

/-- For a locally finite type morphism to a locally Noetherian scheme, the stalk-theoretic
definition of unramifiedness at a point agrees with the affine-neighbourhood definition. -/
@[stacks 039J]
lemma unramifiedAt_iff_morphisms_unramifiedAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] (x : X) :
    StalkwiseUnramifiedAt f x ↔ UnramifiedAt f x := by
  constructor
  · intro H
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
    have := f.finiteType_appLE hU hV hVU
    algebraize [(f.appLE U V hVU).hom]
    have : Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
      (formallyUnramified_stalkMap_iff U hU V hV hVU hxV).mp H
    obtain ⟨r, hr, hur⟩ := Algebra.exists_unramified_of_isUnramifiedAt (R := Γ(Y, U))
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
    let e : X.basicOpen r ≤ f ⁻¹ᵁ U := (X.basicOpen_le r).trans hVU
    refine ⟨X.basicOpen r, hV.basicOpen r, ?_, U, hU, e, ?_⟩
    · show (⟨x, hxV⟩ : V).1 ∈ X.basicOpen r
      rw [← hV.fromSpec_primeIdealOf ⟨x, hxV⟩]
      show hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen r
      rw [hV.fromSpec_preimage_basicOpen]
      show r ∉ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal; exact hr
    · have := hV.isLocalization_basicOpen r
      let : Algebra Γ(Y, U) Γ(X, X.basicOpen r) :=
        (f.appLE U (X.basicOpen r) e).hom.toAlgebra
      refine ⟨?_, f.finiteType_appLE hU (hV.basicOpen r) e⟩
      have hur' := hur.formallyUnramified
      rw [← RingHom.formallyUnramified_algebraMap] at hur'
      rw [← RingHom.formallyUnramified_algebraMap]
      convert! RingHom.FormallyUnramified.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hur'
      ext; dsimp
      rw [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).commutes]
      show (f.appLE U (X.basicOpen r) e).hom _ =
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom ((f.appLE U V hVU).hom _)
      have happ := f.appLE_map hVU (homOfLE (X.basicOpen_le r)).op
      exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp happ.symm) _
  · rintro ⟨V, hV, hxV, U, hU, hVU, H⟩
    algebraize [(f.appLE U V hVU).hom]
    have : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) := H.formallyUnramified
    exact (formallyUnramified_stalkMap_iff U hU V hV hVU hxV).mpr
      (Algebra.FormallyUnramified.comp Γ(Y, U) Γ(X, V) _)

end AlgebraicGeometry
