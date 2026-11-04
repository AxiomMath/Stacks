module

public import Mathlib.FieldTheory.Perfect
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.DirectedColimit
public import StacksFrontier.Cotangent.FilteredColimitVanishing
public import StacksFrontier.Cotangent.FrobeniusNullHomotopy
public import StacksFrontier.Cotangent.TensorProduct

/-!
# The cotangent complex of a map of perfect rings in positive characteristic

Let `p` be a prime, let `A → B` be a ring map with `p = 0` in `A`, and suppose both `A` and `B`
are perfect, that is, their Frobenius endomorphisms are bijective. Then `L_{B/A}` is zero in
`D(B)`.

## Main results

* `CommAlgCat.isIso_cotangentComplexAbMap_of_bijective`: the map of cotangent complexes of
  abelian groups induced by a commutative square whose two horizontal maps are bijective is an
  isomorphism.
* `CommAlgCat.nonempty_homotopy_cotangentComplexAbMap_frobeniusSquare`: the endomorphism of the
  complex of abelian groups underlying `L_{B/A}` induced by the Frobenius square is homotopic to
  zero.
* `CommAlgCat.isZero_cotangentComplexDerived_of_perfect`: for perfect `A` and `B` with `p = 0`
  in `A`, `L_{B/A}` is zero in `D(B)`.

## References

* [Stacks Project, Tag 0G60](https://stacks.math.columbia.edu/tag/0G60)
* [Stacks Project, Tag 0G5Z](https://stacks.math.columbia.edu/tag/0G5Z)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

/-! ### Invertibility of the functoriality map of a bijective square -/

/-- A bijection exhibits its target as the directed colimit of the constant system on its source. -/
private theorem isDirectedColimitOfTypes_of_bijective {X Y : Type*} {f : X → Y}
    (hf : Function.Bijective f) :
    IsDirectedColimitOfTypes (I := ℕ) (F := fun _ => X) (fun _ _ _ x => x) (fun _ x => f x) :=
  { map_id := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ _ => rfl
    comp := fun _ _ _ _ => rfl
    jointly_surjective := fun b => ⟨0, hf.surjective b⟩
    exists_eq := fun i _ _ hab => ⟨i, le_rfl, hf.injective hab⟩ }

/-- The map of cotangent complexes of abelian groups induced by an algebra square whose two
horizontal maps are bijective is an isomorphism. -/
theorem isIso_cotangentComplexAbMap_of_bijective {A : Type u} [CommRing A] {A' : Type u}
    [CommRing A'] {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'}
    (sq : AlgebraSquare.{u, u, u} A A' B B') (hbase : Function.Bijective sq.base)
    (hmap : Function.Bijective sq.map) :
    IsIso (cotangentComplexAbMap.{u, u, u} sq) := by
  have key := fun n : ℤ => isDirectedColimitOfTypes_cotangentComplexAb.{u, u, u, 0}
    (I := ℕ) (A := fun _ => A) (B := fun _ => B) (Ainf := A') (Binf := B')
    (fun _ _ _ => AlgebraSquare.id.{u, u} A B) (fun _ => sq)
    (isDirectedColimitOfTypes_of_bijective hbase)
    (isDirectedColimitOfTypes_of_bijective hmap) n
  have hbij : ∀ n : ℤ, Function.Bijective ((cotangentComplexAbMap.{u, u, u} sq).f n) := by
    intro n
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · obtain ⟨j, hij, hj⟩ := (key n).exists_eq 0 x y hxy
      exact ((key n).map_id 0 x).symm.trans (hj.trans ((key n).map_id 0 y))
    · obtain ⟨_, a, ha⟩ := (key n).jointly_surjective z
      exact ⟨a, ha⟩
  have hcomp : ∀ n : ℤ, IsIso ((cotangentComplexAbMap.{u, u, u} sq).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij n)
  exact @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _
    (cotangentComplexAbMap.{u, u, u} sq) hcomp

/-! ### The null homotopy on underlying abelian groups -/

variable (p : ℕ) (hp : p.Prime) (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
  (hA : (p : A) = 0)

include hp hA in
/-- The endomorphism of the complex of abelian groups underlying `L_{B/A}` induced by the
Frobenius square is homotopic to zero. -/
theorem nonempty_homotopy_cotangentComplexAbMap_frobeniusSquare :
    Nonempty (Homotopy (cotangentComplexAbMap.{u, u, u} (frobeniusSquare.{u, u} p hp A B hA)) 0) :=
  ⟨((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomotopy
      (nonempty_homotopy_squareCotangentComplexMap_frobeniusSquare.{u, u} p hp A B hA).some).trans
    (Homotopy.ofEq (Functor.map_zero _ _ _))⟩

/-! ### The vanishing -/

include hp hA in
/-- Let `p` be a prime number, let `A → B` be a ring homomorphism with `p = 0` in `A`, and assume
that `A` and `B` are perfect. Then `L_{B/A}` is zero in `D(B)`. -/
@[stacks 0G60]
theorem isZero_cotangentComplexDerived_of_perfect [PerfectRing A p]
    [PerfectRing (B : Type u) p] :
    IsZero (cotangentComplexDerived.{u, u} A B) := by
  set sq := frobeniusSquare.{u, u} p hp A B hA
  have hbase : Function.Bijective sq.base := PerfectRing.bijective_frobenius
  have hmap : Function.Bijective sq.map := PerfectRing.bijective_frobenius
  have hiso : IsIso (cotangentComplexAbMap.{u, u, u} sq) :=
    isIso_cotangentComplexAbMap_of_bijective.{u} sq hbase hmap
  obtain ⟨H⟩ := nonempty_homotopy_cotangentComplexAbMap_frobeniusSquare.{u} p hp A B hA
  have hzero : ∀ n : ℤ,
      HomologicalComplex.homologyMap (cotangentComplexAbMap.{u, u, u} sq) n = 0 := fun n => by
    rw [H.homologyMap_eq n]
    simp
  have hhom : ∀ n : ℤ, IsZero ((cotangentComplexAb.{u, u} A B).homology n) := fun n => by
    have : IsIso (0 : (cotangentComplexAb.{u, u} A B).homology n ⟶
        (cotangentComplexAb.{u, u} A B).homology n) := by
      rw [← hzero n]
      infer_instance
    exact IsZero.of_mono_zero _ ((cotangentComplexAb.{u, u} A B).homology n)
  refine CochainComplex.isZero_Q_obj_of_acyclic _ fun n =>
    (CochainComplex.exactAt_forget₂_addCommGrp_iff _ n).1 ?_
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ n).2 (hhom n)

end CommAlgCat

end
