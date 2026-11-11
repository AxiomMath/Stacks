module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring

/-!
# The affine crystalline site

Fix a prime number `p`, a divided power ring `(A, I, γ)` whose underlying ring is an algebra
over `ℤ_(p)`, and an `A`-algebra `C` in which the distinguished ideal `I` acts trivially and
the image of `p` is nilpotent. This is the *affine crystalline situation*, the standing data
for the crystalline constructions over a divided power base.

Over such a situation one forms the big crystalline category `CRIS(C/A)`: an object is a
divided power ring `(B, J, δ)` together with a divided power map from `(A, I, γ)` and a
compatible ring map `C → B/J`, subject to the requirement that `p` be nilpotent in `B`; a
morphism is a divided power map over `A` whose induced map on quotients commutes with the
maps from `C`. The *little* crystalline category `Cris(C/A)` is the full subcategory on the
objects for which `C → B/J` is an isomorphism, i.e. on the honest divided power thickenings
of `C`.

The category `CRIS(C/A)` has finite products, computed as products of the underlying divided
power rings with the componentwise divided powers. Over an arbitrary index type, `CRIS(C/A)`
has the product of a family if and only if a single power of `p` kills every member of the
family; in particular it has all products when the base ring has characteristic `p`.

## Main definitions

* `Crystalline.AffineCrystallineSituation` — the standing affine data for crystalline
  constructions over a divided power ring.
* `Crystalline.DividedPowerThickening` — the big crystalline category `CRIS(C/A)` of divided
  power thickenings.
* `Crystalline.DividedPowerThickening.Hom` — morphisms of divided power thickenings.
* `Crystalline.DividedPowerThickening.IsCrystalline` — the property cutting out the little
  crystalline category.
* `Crystalline.CrystallineThickening` — the little crystalline category `Cris(C/A)`.

## Main results

* `Crystalline.DividedPowerThickening.hasFiniteProducts` — `CRIS(C/A)` has finite products.
* `Crystalline.DividedPowerThickening.hasProduct_of_pow_eq_zero` — the product of a family of
  thickenings over an arbitrary index type exists as soon as one power of `p` kills every
  member of the family.
* `Crystalline.DividedPowerThickening.hasProducts_of_charP` — `CRIS(C/A)` has arbitrary
  products when the base ring has characteristic `p`.
* `Crystalline.DividedPowerThickening.exists_pow_natCast_eq_zero_of_fan` — a cone over a
  family of thickenings forces a single power of `p` to kill every member.
* `Crystalline.DividedPowerThickening.not_hasProduct_of_forall_exists_pow_natCast_ne_zero` —
  a family on which the nilpotence orders of `p` are unbounded has no product.
* `Crystalline.DividedPowerThickening.hasProduct_iff_exists_pow_natCast_eq_zero` — a family
  has a product if and only if a single power of `p` kills every member.

## Implementation notes

The ring map `A → C` is represented by an `Algebra A C` instance, and the condition `IC = 0`
by saying that the image of `I` under this map is the zero ideal. The ring `ℤ_(p)` is
`DividedPowers.IntegersAtPrime p`.

For a thickening, the commutative square of the source is recorded after precomposition with
`A → A/I`; this is equivalent to the displayed square because the fixed map `A → C` kills
`I`. The little crystalline category uses Mathlib's full-subcategory construction, and its
defining isomorphism condition is represented by bijectivity of the underlying ring
homomorphism.

## References

* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Crystalline

/-- **Stacks Project, Tag 07MD.** The standing affine crystalline situation over a divided
power ring `(A, I, γ)`: the ring `A` is a `ℤ_(p)`-algebra, `I` vanishes in `C`, and `p`
is nilpotent in `C`. -/
@[stacks 07MD] public structure AffineCrystallineSituation where
  /-- The fixed prime number. -/
  p : ℕ
  /-- The primality hypothesis on `p`. -/
  [prime : Fact p.Prime]
  /-- The divided power ring `(A, I, γ)`. -/
  A : _root_.DividedPowerRing.{u}
  /-- The target of the fixed ring map from `A`. -/
  C : Type v
  /-- The commutative ring structure on `C`. -/
  [commRingC : CommRing C]
  /-- The `ℤ_(p)`-algebra structure on `A`. -/
  [algebraAtPrime : Algebra (DividedPowers.IntegersAtPrime p) A]
  /-- The fixed ring map `A → C`. -/
  [algebraC : Algebra A C]
  /-- The distinguished divided power ideal has zero image in `C`. -/
  ideal_map_eq_bot : A.ideal.map (algebraMap A C) = ⊥
  /-- The image of `p` in `C` is nilpotent. -/
  prime_nilpotent : IsNilpotent (p : C)

attribute [instance] AffineCrystallineSituation.prime AffineCrystallineSituation.commRingC
  AffineCrystallineSituation.algebraAtPrime AffineCrystallineSituation.algebraC

/-- **Stacks Project, Tag 07HM, part (1).** A divided power thickening in an affine
crystalline situation. -/
@[stacks 07HM "divided power thickenings and CRIS(C/A)"]
public structure DividedPowerThickening (S : AffineCrystallineSituation.{u, v}) where
  /-- The divided power ring `(B, J, δ)`. -/
  ring : _root_.DividedPowerRing.{w}
  /-- The divided power morphism `(A, I, γ) → (B, J, δ)`. -/
  fromBase : DividedPowers.DPMorphism S.A.dividedPowers ring.dividedPowers
  /-- The fixed prime is nilpotent in `B`. -/
  prime_nilpotent : IsNilpotent (S.p : ring)
  /-- The structural map `C → B/J`. -/
  toQuotient : S.C →+* ring ⧸ ring.ideal
  /-- The structural maps from `A` to `B/J` agree. -/
  commutes :
    (Ideal.Quotient.mk ring.ideal).comp fromBase.toRingHom =
      toQuotient.comp (algebraMap S.A S.C)

namespace DividedPowerThickening

section Category

variable {S : AffineCrystallineSituation.{u, v}}
variable {X Y Z : DividedPowerThickening.{u, v, w} S}

/-- **Stacks Project, Tag 07HM, part (2).** A morphism of divided power thickenings is a
divided power map over the base whose induced quotient map is compatible with the maps from
`C`. -/
@[ext, stacks 07HM "homomorphisms of divided power thickenings"]
public structure Hom (X Y : DividedPowerThickening.{u, v, w} S) where
  /-- The underlying divided power morphism. -/
  hom : X.ring ⟶ Y.ring
  /-- The underlying morphism is a morphism over the fixed divided power ring `A`. -/
  fromBase_comp : hom.comp X.fromBase = Y.fromBase
  /-- The induced map on quotients commutes with the structural maps from `C`. -/
  toQuotient_comp : (DividedPowerRing.quotientRingHom hom).comp X.toQuotient = Y.toQuotient

@[stacks 07HM "category structure on CRIS(C/A)"]
public instance : Category (DividedPowerThickening.{u, v, w} S) where
  Hom := Hom
  id X :=
    { hom := 𝟙 X.ring
      fromBase_comp := by ext; rfl
      toQuotient_comp := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      fromBase_comp := by
        rw [← g.fromBase_comp, ← f.fromBase_comp]
        ext
        rfl
      toQuotient_comp := by
        rw [DividedPowerRing.quotientRingHom_comp, RingHom.comp_assoc, f.toQuotient_comp,
          g.toQuotient_comp] }
  id_comp f := by apply Hom.ext; simp
  comp_id f := by apply Hom.ext; simp
  assoc f g h := by apply Hom.ext; simp

/-- The property that cuts out the little crystalline category: the structural map
`C → B/J` is an isomorphism. -/
public abbrev IsCrystalline : ObjectProperty (DividedPowerThickening.{u, v, w} S) :=
  fun X ↦ Function.Bijective X.toQuotient

end Category

end DividedPowerThickening

/-- **Stacks Project, Tag 07HM, part (4).** The little crystalline category `Cris(C/A)`,
the full subcategory of divided power thickenings for which `C → B/J` is an isomorphism. -/
@[stacks 07HM "the full subcategory Cris(C/A)"]
public abbrev CrystallineThickening (S : AffineCrystallineSituation.{u, v}) :=
  (DividedPowerThickening.IsCrystalline (S := S) :
    ObjectProperty (DividedPowerThickening.{u, v, w} S)).FullSubcategory

namespace DividedPowerThickening

section Products

open Limits

/-- The componentwise divided powers on a product of divided power ideals. -/
private noncomputable def piDividedPowers {ι : Type*} {R : ι → Type*}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i))
    (D : ∀ i, _root_.DividedPowers (I i)) :
    _root_.DividedPowers (Ideal.pi I) := by
  classical
  let d : ℕ → (∀ i, R i) → (∀ i, R i) :=
    fun n x => if x ∈ Ideal.pi I then fun i => (D i).dpow n (x i) else 0
  refine { dpow := d
           dpow_null := ?_
           dpow_zero := ?_
           dpow_one := ?_
           dpow_mem := ?_
           dpow_add := ?_
           dpow_mul := ?_
           mul_dpow := ?_
           dpow_comp := ?_ }
  · intro n x hx
    simp [d, hx]
  · intro x hx
    funext i
    simp [d, hx, (D i).dpow_zero ((Ideal.mem_pi I x).mp hx i)]
  · intro x hx
    funext i
    simp [d, hx, (D i).dpow_one ((Ideal.mem_pi I x).mp hx i)]
  · intro n x hn hx
    rw [Ideal.mem_pi]
    intro i
    simpa [d, hx] using (D i).dpow_mem hn ((Ideal.mem_pi I x).mp hx i)
  · intro n x y hx hy
    have hxy : x + y ∈ Ideal.pi I := add_mem hx hy
    funext i
    simp only [d, ite_eq_left hx, ite_eq_left hy, ite_eq_left hxy, Pi.add_apply, Pi.mul_apply,
      Finset.sum_apply]
    exact (D i).dpow_add ((Ideal.mem_pi I x).mp hx i) ((Ideal.mem_pi I y).mp hy i)
  · intro n a x hx
    have hax : a * x ∈ Ideal.pi I := Ideal.mul_mem_left _ _ hx
    funext i
    simp only [d, ite_eq_left hx, ite_eq_left hax, Pi.mul_apply, Pi.pow_apply]
    exact (D i).dpow_mul ((Ideal.mem_pi I x).mp hx i)
  · intro m n x hx
    funext i
    simp only [d, ite_eq_left hx, Pi.mul_apply, Pi.natCast_apply]
    exact (D i).mul_dpow ((Ideal.mem_pi I x).mp hx i)
  · intro m n x hn hx
    have hdx : d n x ∈ Ideal.pi I := by
      rw [Ideal.mem_pi]
      intro i
      simpa [d, hx] using (D i).dpow_mem hn ((Ideal.mem_pi I x).mp hx i)
    simp only [d, ite_eq_left hx] at hdx
    funext i
    simp only [d, ite_eq_left hx, ite_eq_left hdx, Pi.mul_apply, Pi.natCast_apply]
    exact (D i).dpow_comp hn ((Ideal.mem_pi I x).mp hx i)

/-- The quotient of a product of rings by the product of a family of ideals is the product of
the quotients. -/
private noncomputable def quotientPiRingEquiv {ι : Type*} {R : ι → Type*}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i)) :
    ((∀ i, R i) ⧸ Ideal.pi I) ≃+* (∀ i, R i ⧸ I i) := by
  classical
  let f : (∀ i, R i) →+* (∀ i, R i ⧸ I i) :=
    RingHom.pi fun i => (Ideal.Quotient.mk (I i)).comp (Pi.evalRingHom R i)
  let q : ((∀ i, R i) ⧸ Ideal.pi I) →+* (∀ i, R i ⧸ I i) :=
    Ideal.Quotient.lift (Ideal.pi I) f fun x hx =>
      funext fun i => Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.mem_pi I x).mp hx i)
  refine RingEquiv.ofBijective q ⟨fun a b hab => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hz : f (x - y) = 0 := by rw [map_sub, sub_eq_zero]; exact hab
    exact Ideal.Quotient.eq.mpr ((Ideal.mem_pi I (x - y)).mpr fun i =>
      Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hz i))
  · choose x hx using (fun i => Ideal.Quotient.mk_surjective (y i))
    exact ⟨Ideal.Quotient.mk (Ideal.pi I) x, funext fun i => hx i⟩

/-- An element of a product of finitely many rings is nilpotent as soon as each of its
components is. -/
private lemma nilpotent_pi {ι : Type*} [Finite ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (x : ∀ i, R i)
    (hx : ∀ i, IsNilpotent (x i)) : IsNilpotent x := by
  classical
  have := Fintype.ofFinite ι
  choose n hn using hx
  refine ⟨∑ i, n i, ?_⟩
  funext i
  simpa only [Pi.pow_apply, Pi.zero_apply] using
    pow_eq_zero_of_le
      (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (hn i)

/-- The identification of the quotient of a product, on the class of an explicit element. -/
private lemma quotientPiRingEquiv_mk {ι : Type*} {R : ι → Type*}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i)) (x : ∀ i, R i) :
    quotientPiRingEquiv I (Ideal.Quotient.mk (Ideal.pi I) x) =
      fun i => Ideal.Quotient.mk (I i) (x i) := by classical rfl

/-- The product of the underlying divided power rings of a family of thickenings. -/
private noncomputable def piRing {ι : Type w} {S : AffineCrystallineSituation.{u, v}}
    (X : ι → DividedPowerThickening.{u, v, w} S) : _root_.DividedPowerRing.{w} where
  carrier := ∀ i, (X i).ring
  ideal := Ideal.pi (fun i => (X i).ring.ideal)
  dividedPowers := piDividedPowers (fun i => (X i).ring.ideal)
    (fun i => (X i).ring.dividedPowers)

/-- The divided power map into a product induced by a family of maps into the factors. -/
private noncomputable def piLiftRing {ι : Type w} {S : AffineCrystallineSituation.{u, v}}
    {X : ι → DividedPowerThickening.{u, v, w} S} {A : _root_.DividedPowerRing}
    (g : ∀ i, _root_.DividedPowers.DPMorphism A.dividedPowers (X i).ring.dividedPowers) :
    _root_.DividedPowers.DPMorphism A.dividedPowers (piRing X).dividedPowers := by
  classical
  let f : A →+* piRing X := RingHom.pi fun i => (g i).toRingHom
  have hi : A.ideal ≤ (piRing X).ideal.comap f := by
    intro a ha
    change ∀ i, f a i ∈ (X i).ring.ideal
    intro i
    exact (Ideal.map_le_iff_le_comap.mp (g i).ideal_comp) ha
  apply _root_.DividedPowers.DPMorphism.mk' (f := f)
  refine { ideal_comp := Ideal.map_le_iff_le_comap.mpr hi, dpow_comp := ?_ }
  intro n a ha
  have hf : f a ∈ (piRing X).ideal := hi ha
  funext i
  change (if f a ∈ (piRing X).ideal then
      (fun j => (X j).ring.dividedPowers.dpow n (f a j)) else 0) i =
      f (A.dividedPowers.dpow n a) i
  rw [ite_eq_left hf]
  exact (g i).dpow_comp a ha

/-- The projection of a product of thickenings onto a factor. -/
private noncomputable def piProjection {ι : Type w} {S : AffineCrystallineSituation.{u, v}}
    (X : ι → DividedPowerThickening.{u, v, w} S) (i : ι) : piRing X ⟶ (X i).ring := by
  classical
  let f : piRing X →+* (X i).ring := Pi.evalRingHom (fun j => (X j).ring) i
  apply _root_.DividedPowers.DPMorphism.mk' (f := f)
  refine { ideal_comp := ?_, dpow_comp := ?_ }
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact (Ideal.mem_pi (fun j => (X j).ring.ideal) x).mp hx i
  · intro n x hx
    change (X i).ring.dividedPowers.dpow n (x i) =
      (if x ∈ (piRing X).ideal then
        (fun j => (X j).ring.dividedPowers.dpow n (x j)) else 0) i
    rw [ite_eq_left hx]

/-- The product of a family of divided power thickenings in whose product ring `p` is
nilpotent, as a thickening. -/
private noncomputable def piObject {ι : Type w} {S : AffineCrystallineSituation.{u, v}}
    (X : ι → DividedPowerThickening.{u, v, w} S) (hp : IsNilpotent (S.p : piRing X)) :
    DividedPowerThickening.{u, v, w} S := by
  classical
  let q := quotientPiRingEquiv (fun i => (X i).ring.ideal)
  let c : S.C →+* (∀ i, (X i).ring ⧸ (X i).ring.ideal) :=
    RingHom.pi fun i => (X i).toQuotient
  refine { ring := piRing X
           fromBase := piLiftRing fun i => (X i).fromBase
           prime_nilpotent := hp
           toQuotient := q.symm.toRingHom.comp c
           commutes := ?_ }
  · apply RingHom.ext
    intro a
    apply q.injective
    let x : ∀ i, (X i).ring := (piLiftRing fun i => (X i).fromBase) a
    change q (Ideal.Quotient.mk (Ideal.pi (fun i => (X i).ring.ideal)) x) =
      q (q.symm (c (algebraMap S.A S.C a)))
    rw [q.apply_symm_apply]
    change (quotientPiRingEquiv (fun i => (X i).ring.ideal))
      (Ideal.Quotient.mk (Ideal.pi (fun i => (X i).ring.ideal)) x) =
      c (algebraMap S.A S.C a)
    rw [quotientPiRingEquiv_mk]
    funext i
    exact congrArg (fun f : S.A →+* (X i).ring ⧸ (X i).ring.ideal => f a) (X i).commutes

/-- The projection of the product thickening onto a factor, as a morphism of thickenings. -/
private noncomputable def piProjectionThickening {ι : Type w}
    {S : AffineCrystallineSituation.{u, v}}
    (X : ι → DividedPowerThickening.{u, v, w} S) (hnil : IsNilpotent (S.p : piRing X))
    (i : ι) : piObject X hnil ⟶ X i := by
  classical
  let q := quotientPiRingEquiv (fun j => (X j).ring.ideal)
  have hp (z : (piObject X hnil).ring ⧸ (piObject X hnil).ring.ideal) :
      DividedPowerRing.quotientRingHom (piProjection X i) z = (q z) i := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    let y : ∀ j, (X j).ring := x
    change Ideal.Quotient.mk (X i).ring.ideal (y i) =
      (quotientPiRingEquiv (fun j => (X j).ring.ideal))
        (Ideal.Quotient.mk (Ideal.pi (fun j => (X j).ring.ideal)) y) i
    rw [quotientPiRingEquiv_mk]
  refine { hom := piProjection X i
           fromBase_comp := ?_
           toQuotient_comp := ?_ }
  · ext a
    rfl
  · ext c
    change DividedPowerRing.quotientRingHom (piProjection X i)
        ((piObject X hnil).toQuotient c) = (X i).toQuotient c
    rw [hp]
    change (q (q.symm ((RingHom.pi fun j => (X j).toQuotient) c))) i = _
    rw [q.apply_symm_apply]
    rfl

/-- The morphism into the product thickening induced by a family of morphisms into the
factors. -/
private noncomputable def piLift {ι : Type w} {S : AffineCrystallineSituation.{u, v}}
    {X : ι → DividedPowerThickening.{u, v, w} S} (hnil : IsNilpotent (S.p : piRing X))
    {Y : DividedPowerThickening.{u, v, w} S} (g : ∀ i, Y ⟶ X i) : Y ⟶ piObject X hnil := by
  classical
  let q := quotientPiRingEquiv (fun i => (X i).ring.ideal)
  refine { hom := piLiftRing fun i => (g i).hom
           fromBase_comp := ?_
           toQuotient_comp := ?_ }
  · ext a
    funext i
    exact congrArg (fun f => f a) (g i).fromBase_comp
  · ext c
    apply q.injective
    have hq (z : Y.ring ⧸ Y.ring.ideal) :
        q (DividedPowerRing.quotientRingHom (A := Y.ring) (B := (piObject X hnil).ring)
            (piLiftRing fun i => (g i).hom) z) =
          fun i => DividedPowerRing.quotientRingHom (g i).hom z := by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      let y : ∀ i, (X i).ring := (piLiftRing fun i => (g i).hom) x
      change q (Ideal.Quotient.mk (Ideal.pi (fun i => (X i).ring.ideal)) y) =
        fun i => Ideal.Quotient.mk (X i).ring.ideal ((g i).hom x)
      rw [quotientPiRingEquiv_mk]
      rfl
    change q (DividedPowerRing.quotientRingHom (A := Y.ring) (B := (piObject X hnil).ring)
      (piLiftRing fun i => (g i).hom) (Y.toQuotient c)) = q ((piObject X hnil).toQuotient c)
    rw [hq]
    change (fun i => DividedPowerRing.quotientRingHom (g i).hom (Y.toQuotient c)) =
      q (q.symm ((RingHom.pi fun i => (X i).toQuotient) c))
    rw [q.apply_symm_apply]
    funext i
    exact congrArg (fun f : S.C →+* (X i).ring ⧸ (X i).ring.ideal => f c)
      (g i).toQuotient_comp

/-- The product thickening is the categorical product of the factors. -/
private noncomputable def piIsLimit {ι : Type w} {S : AffineCrystallineSituation.{u, v}}
    (X : ι → DividedPowerThickening.{u, v, w} S) (hnil : IsNilpotent (S.p : piRing X)) :
    IsLimit (Fan.mk (piObject X hnil) (piProjectionThickening X hnil)) := by
  classical
  refine Fan.IsLimit.mk _ (fun s => piLift hnil (fun i => s.proj i)) ?_ ?_
  · intro s i
    apply Hom.ext
    apply _root_.DividedPowers.DPMorphism.ext
    funext a
    rfl
  · intro s m hm
    apply Hom.ext
    apply _root_.DividedPowers.DPMorphism.ext
    funext a i
    exact congrArg (fun f : s.pt ⟶ X i => f.hom a) (hm i)

/-! ### Finite products

The construction of the product of a finite family of divided power thickenings. The index
type lies in `Type 0` because `HasFiniteProducts` is stated for the shapes
`Discrete (Fin n)`.
-/

namespace FiniteProduct

/-- The product of a finite family of divided power thickenings, as a thickening. -/
private noncomputable def piObject {ι : Type} [Finite ι] {S : AffineCrystallineSituation.{u, v}}
    (X : ι → DividedPowerThickening.{u, v, w} S) : DividedPowerThickening.{u, v, w} S :=
  DividedPowerThickening.piObject (fun i : ULift.{w} ι => X i.down)
    (nilpotent_pi _ fun i => (X i.down).prime_nilpotent)

/-- The projection of the product thickening onto a factor, as a morphism of thickenings. -/
private noncomputable def piProjectionThickening {ι : Type} [Finite ι]
    {S : AffineCrystallineSituation.{u, v}} (X : ι → DividedPowerThickening.{u, v, w} S)
    (i : ι) : piObject X ⟶ X i :=
  DividedPowerThickening.piProjectionThickening _ _ (ULift.up i)

/-- The product thickening is the categorical product of the factors. -/
private noncomputable def piIsLimit {ι : Type} [Finite ι] {S : AffineCrystallineSituation.{u, v}}
    (X : ι → DividedPowerThickening.{u, v, w} S) :
    IsLimit (Fan.mk (piObject X) (piProjectionThickening X)) :=
  let L := DividedPowerThickening.piIsLimit (fun i : ULift.{w} ι => X i.down)
    (nilpotent_pi _ fun i => (X i.down).prime_nilpotent)
  Fan.IsLimit.mk _ (fun s => L.lift (Fan.mk s.pt fun j => s.proj j.down))
    (fun s i => L.fac (Fan.mk s.pt fun j => s.proj j.down) ⟨⟨i⟩⟩)
    (fun s m hm => L.uniq (Fan.mk s.pt fun j => s.proj j.down) m fun j => hm j.as.down)

end FiniteProduct

/-- **Stacks Project, Tag 07HN, finite-products part.** The category `CRIS(C/A)` of divided
power thickenings in an affine crystalline situation has finite products. -/
@[stacks 07HN "finite_products"]
public instance hasFiniteProducts (S : AffineCrystallineSituation.{u, v}) :
    HasFiniteProducts (DividedPowerThickening.{u, v, w} S) := by
  refine ⟨fun n ↦ ⟨fun F ↦ ?_⟩⟩
  let X : Fin n → DividedPowerThickening.{u, v, w} S := fun i => F.obj (Discrete.mk i)
  have : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    HasLimit.mk ⟨Fan.mk (FiniteProduct.piObject X) (FiniteProduct.piProjectionThickening X),
      FiniteProduct.piIsLimit X⟩
  exact hasLimit_of_iso (Discrete.natIsoFunctor (F := F)).symm

/-! ### Arbitrary products

The product of a family of divided power thickenings over an arbitrary index type, for a family
in whose product ring `p` is nilpotent.
-/

namespace InfiniteProduct

end InfiniteProduct

/-- **A product of a family of divided power thickenings exists as soon as a single power of
`p` kills every member of the family.** -/
public theorem hasProduct_of_pow_eq_zero {ι : Type w} {S : AffineCrystallineSituation.{u, v}}
    (X : ι → DividedPowerThickening.{u, v, w} S) (N : ℕ)
    (hN : ∀ i, (S.p : (X i).ring) ^ N = 0) : HasProduct X := by
  have hnil : IsNilpotent (S.p : piRing X) := ⟨N, funext hN⟩
  exact HasLimit.mk ⟨Fan.mk (piObject X hnil) (piProjectionThickening X hnil), piIsLimit X hnil⟩

/-- **If the base ring has characteristic `p`, the category `CRIS(C/A)` has arbitrary
products.** This complements [Stacks, Tag 07HN, part (1)], which only asserts finite products:
infinite products fail in general (see `Crystalline.not_hasProductsOfShape_of_infinite`), but
exist when `p = 0` in `A`, since then `p` vanishes in every thickening. -/
public instance hasProducts_of_charP (S : AffineCrystallineSituation.{u, v}) [CharP S.A S.p] :
    HasProducts.{w} (DividedPowerThickening.{u, v, w} S) := by
  classical
  refine fun ι ↦ ⟨fun F ↦ ?_⟩
  let X : ι → DividedPowerThickening.{u, v, w} S := fun i => F.obj (Discrete.mk i)
  have hone (i : ι) : (S.p : (X i).ring) ^ 1 = 0 := by
    rw [pow_one, ← map_natCast (X i).fromBase.toRingHom, CharP.cast_eq_zero S.A S.p, map_zero]
  have : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    hasProduct_of_pow_eq_zero (F.obj ∘ Discrete.mk) 1 hone
  exact hasLimit_of_iso (Discrete.natIsoFunctor (F := F)).symm

/-! ### The obstruction to arbitrary products -/

/-- **A morphism of thickenings carries a vanishing power of `p` forward.** -/
public theorem pow_natCast_eq_zero_of_hom {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S} (f : X ⟶ Y) {N : ℕ}
    (h : (S.p : X.ring) ^ N = 0) : (S.p : Y.ring) ^ N = 0 := by
  rw [← map_natCast f.hom.toRingHom, ← map_pow, h, map_zero]

/-- **A cone over a family of divided power thickenings forces a uniform bound on the
nilpotence order of `p` across the family.** -/
public theorem exists_pow_natCast_eq_zero_of_fan {ι : Type w}
    {S : AffineCrystallineSituation.{u, v}} (X : ι → DividedPowerThickening.{u, v, w} S)
    (c : Fan X) : ∃ N : ℕ, ∀ i, (S.p : (X i).ring) ^ N = 0 := by
  obtain ⟨N, hN⟩ := c.pt.prime_nilpotent
  exact ⟨N, fun i => pow_natCast_eq_zero_of_hom (c.proj i) hN⟩

/-- **A family of divided power thickenings on which no single power of `p` vanishes has no
product in `CRIS(C/A)`.** This is the obstruction behind the infinite-products caveat of
[Stacks, Tag 07HN, part (1)]; `Crystalline.not_hasProductsOfShape_of_infinite` uses it to show
that `CRIS(C/A)` has no infinite products in general. -/
public theorem not_hasProduct_of_forall_exists_pow_natCast_ne_zero {ι : Type w}
    {S : AffineCrystallineSituation.{u, v}} (X : ι → DividedPowerThickening.{u, v, w} S)
    (h : ∀ N : ℕ, ∃ i, (S.p : (X i).ring) ^ N ≠ 0) : ¬ HasProduct X := by
  intro hX
  obtain ⟨N, hN⟩ := exists_pow_natCast_eq_zero_of_fan X (limit.cone (Discrete.functor X))
  obtain ⟨i, hi⟩ := h N
  exact hi (hN i)

/-- **Exactly the uniformly annihilated families have products in `CRIS(C/A)`.** -/
public theorem hasProduct_iff_exists_pow_natCast_eq_zero {ι : Type w}
    {S : AffineCrystallineSituation.{u, v}} (X : ι → DividedPowerThickening.{u, v, w} S) :
    HasProduct X ↔ ∃ N : ℕ, ∀ i, (S.p : (X i).ring) ^ N = 0 :=
  ⟨fun _ => exists_pow_natCast_eq_zero_of_fan X (limit.cone (Discrete.functor X)),
    fun ⟨N, hN⟩ => hasProduct_of_pow_eq_zero X N hN⟩

end Products

end DividedPowerThickening

end Crystalline

end
