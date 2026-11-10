module

public import StacksFrontier.Deformation.Examples.Geometric.SmoothingFitting
public import StacksFrontier.Examples.Deformations.Schemes.LocalRing
public import StacksFrontier.Examples.Deformations.Schemes.SpecialFibre

/-!
# The Fitting clause of a deformation at a smooth point

Let `X` be a scheme of dimension at most one, locally of finite type over a field `k`, and let `P`
be a deformation of `X` over an Artinian local `k`-algebra `A`. At a point `x` where `X` is smooth
over `k`, the first Fitting ideal of `Ω_{𝒪_{P,x}/A}` is the unit ideal. This is the smooth-point
case of the Fitting computation in the proof of [Stacks, Tag 0E7Y]: "if `p` corresponds to a
smooth point for `X → Spec(k)`, then `Ω_{X_n/S_n, p}` is free of rank `1` and the first Fitting
ideal is equal to the local ring".

The local ring of `X` at `x` is the base change of the local ring of `P` at `x` along `A → k`
(`Deformation.Examples.special_stalk_pushout_any`), Fitting ideals of differentials commute with
base change (`Deformation.Examples.Smoothing.fittingIdeal_kaehler_of_isPushout`), the first
Fitting ideal of the differentials of the local ring of `X` is the unit ideal
(`Deformation.Examples.Smoothing.fittingIdeal_kaehler_stalk_eq_top_of_mem_smoothLocus`), and an
ideal whose image under a local homomorphism is the unit ideal is the unit ideal.

## Main results

* `Deformation.Examples.Smoothing.fittingIdeal_stalk_eq_top_of_mem_smoothLocus`.

## References

* [The Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Examples.Smoothing

/-- The structure map of `Deformation.Examples.Smoothing.stalkAlgebra` is the stalk map of the
morphism to `Spec A` composed with the structure map of the local ring of `Spec A`. -/
theorem stalkAlgebra_eq_stalkMap_comp (A : Type u) [CommRing A] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) (y : Y) :
    stalkAlgebra A g y =
      letI : Algebra A ((Spec (.of A)).presheaf.stalk (g.base y)) :=
        StructureSheaf.stalkAlgebra A (g.base y)
      ((g.stalkMap y).hom.comp (algebraMap A _)).toAlgebra := by
  refine Algebra.algebra_ext _ _ fun a => ?_
  change (Y.presheaf.germ ⊤ y _) (g.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) =
    (g.stalkMap y) (StructureSheaf.toStalk A (g.base y) a)
  refine (Scheme.Hom.germ_stalkMap_apply g ⊤ y trivial
    ((Scheme.ΓSpecIso (.of A)).inv a)).symm.trans ?_
  rfl

/-- An ideal whose image under a local homomorphism of local rings is the unit ideal is the unit
ideal. -/
theorem eq_top_of_map_eq_top_of_isLocalHom {C D : Type*} [CommRing C] [CommRing D]
    [IsLocalRing C] [IsLocalRing D] (φ : C →+* D) [IsLocalHom φ] {J : Ideal C}
    (hJ : J.map φ = ⊤) : J = ⊤ := by
  by_contra hne
  have hle : J.map φ ≤ IsLocalRing.maximalIdeal D := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
    exact IsLocalRing.le_maximalIdeal hne
  exact (IsLocalRing.maximalIdeal.isMaximal D).ne_top (top_le_iff.mp (hJ ▸ hle))

variable {k : Type u} [Field k]

/-- **The Fitting clause of a deformation at a smooth point.** Let `X` be a scheme of dimension at
most one, locally of finite type over `k`, and let `P` be a deformation of `X` over an Artinian
local `k`-algebra. At a point `x` of the smooth locus of `X`, the first Fitting ideal of the
differentials of the local ring of the total space of `P` at `x`, over the base of `P`, is the
unit ideal. -/
theorem fittingIdeal_stalk_eq_top_of_mem_smoothLocus (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
    (P : SchemeDeformationCategory (Λ := k) (k := k) X) [LocallyOfFiniteType P.toBase]
    (x : X.left) (hx : x ∈ X.hom.smoothLocus) :
    letI := stalkAlgebra P.base P.toBase (P.specialMap x)
    letI := moduleFinite_kaehler_stalkAlgebra P.base P.toBase (P.specialMap x)
    fittingIdeal (R := P.scheme.presheaf.stalk (P.specialMap x))
      (M := Ω[P.scheme.presheaf.stalk (P.specialMap x)⁄P.base]) (1 : ℤ) = ⊤ := by
  let y := P.specialMap x
  -- generalize the algebra structure, so that it can be replaced by its structure-sheaf form
  suffices key : ∀ (inst : Algebra P.base (P.scheme.presheaf.stalk y)),
      inst = (let : Algebra P.base ((Spec (.of P.base)).presheaf.stalk (P.toBase.base y)) :=
        StructureSheaf.stalkAlgebra P.base (P.toBase.base y)
        ((P.toBase.stalkMap y).hom.comp (algebraMap P.base _)).toAlgebra) →
      ∀ (_ : Module.Finite (P.scheme.presheaf.stalk y) Ω[P.scheme.presheaf.stalk y⁄P.base]),
      fittingIdeal (R := P.scheme.presheaf.stalk y)
        (M := Ω[P.scheme.presheaf.stalk y⁄P.base]) (1 : ℤ) = ⊤ from
    key _ (stalkAlgebra_eq_stalkMap_comp P.base P.toBase y) _
  rintro _ rfl hfinP
  let : Algebra P.base ((Spec (.of P.base)).presheaf.stalk (P.toBase.base y)) :=
    StructureSheaf.stalkAlgebra P.base (P.toBase.base y)
  let : Algebra P.base (P.scheme.presheaf.stalk y) :=
    ((P.toBase.stalkMap y).hom.comp (algebraMap P.base _)).toAlgebra
  let : Algebra k (X.left.presheaf.stalk x) := stalkAlgebraOver (Over.mk X.hom) x
  have hsq := special_stalk_pushout_any X x P
  let : Algebra P.base k := (Deformation.Artin.residueMap P.base).toAlgebra
  let : Algebra (P.scheme.presheaf.stalk y) (X.left.presheaf.stalk x) :=
    (P.specialMap.stalkMap x).hom.toAlgebra
  let : Algebra P.base (X.left.presheaf.stalk x) :=
    ((algebraMap k (X.left.presheaf.stalk x)).comp (algebraMap P.base k)).toAlgebra
  have : IsScalarTower P.base k (X.left.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P.base (P.scheme.presheaf.stalk y) (X.left.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hsq.w).symm
  have : Algebra.IsPushout P.base k (P.scheme.presheaf.stalk y) (X.left.presheaf.stalk x) :=
    (CommRingCat.isPushout_iff_isPushout).mp hsq.flip
  have hF1 := fittingIdeal_kaehler_of_isPushout (R := P.base) (C := P.scheme.presheaf.stalk y)
    (R' := k) (C' := X.left.presheaf.stalk x) 1
  have hF5 := fittingIdeal_kaehler_stalk_eq_top_of_mem_smoothLocus X.hom hdim x hx
  rw [Nat.cast_one] at hF1
  rw [hF1] at hF5
  exact eq_top_of_map_eq_top_of_isLocalHom (P.specialMap.stalkMap x).hom hF5

end Deformation.Examples.Smoothing
