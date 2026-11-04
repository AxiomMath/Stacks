module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Valuation.Extension.FundamentalInequality

/-!
# Extensions of valuation rings

An extension of valuation rings is an injective local homomorphism between valuation rings. It
induces a homomorphism on value groups and an extension of residue fields. The extension is
weakly unramified when the induced homomorphism of value groups is bijective, and its residue
degree is the degree of the induced residue-field extension.

## Main definitions

* `ValuationRing.IsExtension`: an injective local homomorphism of valuation rings.
* `ValuationRing.valueGroupMap`: the induced homomorphism of value groups.
* `ValuationRing.IsWeaklyUnramified`: the induced homomorphism of value groups is bijective.
* `ValuationRing.residueDegree`: the degree of the induced residue-field extension.

## Main results

* `ValuationRing.valueGroupMap_valuation`: the canonical value-group map commutes with the
  valuation on every nonzero element of the smaller valuation ring.
* `ValuationRing.valueGroupMap_range_eq_valueGroupHom_range`: the range of `valueGroupMap`
  coincides with the range of `ValuationRing.valueGroupHom`.

## References

* [Stacks, Tag 0ASG](https://stacks.math.columbia.edu/tag/0ASG)
-/

@[expose] public section

universe u v w x

open IsLocalRing ValuationRing

namespace ValuationRing

/-- An extension of valuation rings is an injective local ring homomorphism. -/
@[stacks 0ASG "extension of valuation rings"]
def IsExtension {A : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [ValuationRing B]
    (f : A →+* B) : Prop :=
  Function.Injective f ∧ IsLocalHom f

/-- The canonical homomorphism `Γ_A → Γ_B` induced by an extension of valuation
rings. Here `K` and `L` are arbitrary fraction fields of `A` and `B`, respectively. -/
@[stacks 0ASG "map on value groups"]
noncomputable def valueGroupMap {A : Type u} {B : Type v} {K : Type w} {L : Type x}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [ValuationRing B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    (f : A →+* B) (hf : IsExtension f) :
    (ValueGroup A K)ˣ →* (ValueGroup B L)ˣ := by
  let q : A →+* L := (algebraMap B L).comp f
  have hq : Function.Injective q := (IsFractionRing.injective B L).comp hf.1
  let g : K →+* L := IsFractionRing.lift (A := A) (K := K) hq
  let φ : ValueGroup A K →*₀ ValueGroup B L :=
    { toFun := Quotient.map' g fun a b hab => by
        obtain ⟨c, hc⟩ := hab
        refine ⟨Units.map f.toMonoidHom c, ?_⟩
        simp only [Units.smul_def, Algebra.smul_def]
        change q (c : A) * g b = g a
        rw [← IsFractionRing.lift_algebraMap (A := A) (K := K) (L := L) (g := q) hq,
          ← map_mul]
        exact congrArg g (by simpa [Algebra.smul_def, Units.smul_def] using hc)
      map_zero' := by
        change Quotient.mk'' (g 0) = Quotient.mk'' 0
        rw [map_zero]
      map_one' := by
        change Quotient.mk'' (g 1) = Quotient.mk'' 1
        rw [map_one]
      map_mul' := by
        rintro ⟨a⟩ ⟨b⟩
        change Quotient.mk'' (g (a * b)) = Quotient.mk'' (g a * g b)
        rw [map_mul] }
  exact Units.map φ.toMonoidHom

/-- An extension of valuation rings is weakly unramified when its canonical map on value
groups is bijective. -/
@[stacks 0ASG "weakly unramified"]
def IsWeaklyUnramified {A : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [ValuationRing B]
    (f : A →+* B) (hf : IsExtension f) : Prop :=
  Function.Bijective
    (valueGroupMap (K := FractionRing A) (L := FractionRing B) f hf)

/-- The residue degree of an extension of valuation rings, namely `[κ_B : κ_A]` for the
residue-field map induced by the local homomorphism, and zero when that extension is infinite. -/
@[stacks 0ASG "residue degree"]
noncomputable def residueDegree {A : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [ValuationRing B]
    (f : A →+* B) (hf : IsExtension f) : ℕ :=
  letI : IsLocalHom f := hf.2
  letI := (ResidueField.map f).toAlgebra
  Module.finrank (ResidueField A) (ResidueField B)

/-- The canonical map on value groups sends the valuation class of every nonzero element of
the smaller valuation ring to the valuation class of its image. This is the commutative square
in the definition of an extension of valuation rings. -/
@[stacks 0ASG "commutative value-group diagram"]
theorem valueGroupMap_valuation {A : Type u} {B : Type v} {K : Type w} {L : Type x}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [ValuationRing B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    (f : A →+* B) (hf : IsExtension f) (a : A) (ha : a ≠ 0) :
    ((valueGroupMap (K := K) (L := L) f hf)
      (Units.mk0 ((valuation A K) (algebraMap A K a)) (by simp [ha])) :
        ValueGroup B L) =
      (valuation B L) (algebraMap B L (f a)) := by
  let q : A →+* L := (algebraMap B L).comp f
  have hq : Function.Injective q := (IsFractionRing.injective B L).comp hf.1
  show Quotient.mk'' ((IsFractionRing.lift (A := A) (K := K) hq)
      (algebraMap A K a)) = Quotient.mk'' (algebraMap B L (f a))
  rw [IsFractionRing.lift_algebraMap]
  rfl

/-- Every unit of the value group of a valuation ring `A` with fraction field `K` is the
valuation of a unit of `K`. -/
lemma units_valuation_surjective
    (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] :
    Function.Surjective
      (Units.map ((valuation A K).toMonoidWithZeroHom.toMonoidHom) :
        Kˣ →* (ValueGroup A K)ˣ) := by
  intro x
  obtain ⟨a, ha⟩ := Quotient.exists_rep (x : ValueGroup A K)
  have hna : a ≠ 0 := by
    rintro rfl
    exact x.ne_zero ha.symm
  exact ⟨Units.mk0 a hna, Units.ext ha⟩

/-- For an extension `A → B` of valuation rings, the range of `valueGroupMap` is the range of
`valueGroupHom B (Frac A) (Frac B)`. -/
lemma valueGroupMap_range_eq_valueGroupHom_range
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [ValuationRing B]
    [Algebra A B] [FaithfulSMul A B]
    (h : IsExtension (algebraMap A B)) :
    letI : Algebra (FractionRing A) (FractionRing B) :=
      FractionRing.liftAlgebra A (FractionRing B)
    (valueGroupMap (K := FractionRing A) (L := FractionRing B)
      (algebraMap A B) h).range =
    (valueGroupHom B (FractionRing A) (FractionRing B)).range := by
  let : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  let f := valueGroupMap (K := FractionRing A) (L := FractionRing B)
    (algebraMap A B) h
  let v : (FractionRing A)ˣ →* (ValueGroup A (FractionRing A))ˣ :=
    Units.map ((valuation A (FractionRing A)).toMonoidWithZeroHom.toMonoidHom)
  have hv : Function.Surjective v := units_valuation_surjective A (FractionRing A)
  have hcomp : f.comp v = valueGroupHom B (FractionRing A) (FractionRing B) := by
    ext x
    rfl
  rw [← hcomp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hv, ← MonoidHom.range_eq_map]

end ValuationRing
