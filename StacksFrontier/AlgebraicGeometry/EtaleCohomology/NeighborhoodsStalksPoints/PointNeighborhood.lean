module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood

/-!
# Étale neighbourhoods of a point and of a geometric point over it

Let `s` be a point of a scheme `S` and let `σ` (written `s̄` in the Stacks project) be a geometric
point of `S` lying over `s`. An étale neighbourhood `(U, ū)` of `(S, σ)` gives the étale
neighbourhood `(U, u)` of `(S, s)`, where `u` is the unique point of `U` over which `ū` lies.
Conversely, every étale neighbourhood `(U, u)` of `(S, s)` arises in this way: the residue field
extension `κ(u)/κ(s)` is finite separable, so it embeds into `κ(σ)` over `κ(s)`, which gives a
geometric point `ū` of `U` lying over `u` such that `(U, ū)` is an étale neighbourhood of `(S, σ)`.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.geometricPoint` is the geometric point `ū`
  of `U` given by an étale neighbourhood `(U, ū)` of a geometric point.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.toEtaleNeighborhood` is the étale
  neighbourhood `(U, u)` of `(S, s)` attached to an étale neighbourhood `(U, ū)` of `(S, σ)`.

## Main results

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.geometricPoint_liesOver_iff`: the point
  `u` is the unique point of `U` over which `ū` lies.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.toEtaleNeighborhood_surjective`: every étale
  neighbourhood of `(S, s)` comes from an étale neighbourhood of `(S, σ)`.

## References

* [Stacks Project, Tag 04HT](https://stacks.math.columbia.edu/tag/04HT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GeometricPoint.EtaleNeighborhood

variable {S : Scheme.{u}} {s : S} {σ : GeometricPoint S}

/-- The geometric point `ū` of `U` given by an étale neighbourhood `(U, ū)` of a geometric
point. -/
def geometricPoint (U : σ.EtaleNeighborhood) : GeometricPoint U.scheme where
  residueField := σ.residueField
  hom := U.point

/-- The morphism of the geometric point `U.geometricPoint` is the point `U.point` of `U`. -/
@[simp]
lemma geometricPoint_hom (U : σ.EtaleNeighborhood) : U.geometricPoint.hom = U.point :=
  rfl

/-- An étale neighbourhood `(U, ū)` of a geometric point `σ` lying over `s` gives the étale
neighbourhood `(U, u)` of `(S, s)`, where `u` is the image of `ū`. -/
@[stacks 04HT "first direction"]
def toEtaleNeighborhood (U : σ.EtaleNeighborhood) (h : σ.LiesOver s) :
    AlgebraicGeometry.EtaleNeighborhood S s where
  scheme := U.scheme
  point := U.point default
  toBase := U.toBase
  map_point := by rw [← h, ← U.point_comp]; rfl

/-- The scheme of `U.toEtaleNeighborhood h` is the scheme of `U`. -/
@[simp]
lemma toEtaleNeighborhood_scheme (U : σ.EtaleNeighborhood) (h : σ.LiesOver s) :
    (U.toEtaleNeighborhood h).scheme = U.scheme :=
  rfl

/-- The distinguished point of `U.toEtaleNeighborhood h` is `U.point default`, the image of the
geometric point of `U`. -/
@[simp]
lemma toEtaleNeighborhood_point (U : σ.EtaleNeighborhood) (h : σ.LiesOver s) :
    (U.toEtaleNeighborhood h).point = U.point default :=
  rfl

/-- The structure morphism of `U.toEtaleNeighborhood h` is the structure morphism of `U`. -/
@[simp]
lemma toEtaleNeighborhood_toBase (U : σ.EtaleNeighborhood) (h : σ.LiesOver s) :
    (U.toEtaleNeighborhood h).toBase = U.toBase :=
  rfl

/-- The distinguished point `u` of the étale neighbourhood `(U, u)` attached to `(U, ū)` is the
unique point of `U` over which the geometric point `ū` lies. -/
@[stacks 04HT "first direction: u is the unique point under ū"]
theorem geometricPoint_liesOver_iff (U : σ.EtaleNeighborhood) (h : σ.LiesOver s)
    (x : U.scheme) : U.geometricPoint.LiesOver x ↔ x = (U.toEtaleNeighborhood h).point :=
  eq_comm

/-- Conversely, every étale neighbourhood `(U, u)` of `(S, s)` comes from an étale neighbourhood
of a geometric point `σ` lying over `s`: there is a geometric point `ū` of `U` lying over `u`
such that `(U, ū)` is an étale neighbourhood of `(S, σ)`. -/
@[stacks 04HT "converse direction"]
theorem toEtaleNeighborhood_surjective (h : σ.LiesOver s) :
    Function.Surjective fun U : σ.EtaleNeighborhood ↦ U.toEtaleNeighborhood h := by
  rintro ⟨X, x, f, hx⟩
  obtain ⟨l, hl, rfl⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f σ.hom x (hx.trans h.symm)
  exact ⟨{ scheme := X, toBase := f, point := l, point_comp := hl }, rfl⟩

end AlgebraicGeometry.GeometricPoint.EtaleNeighborhood

end
