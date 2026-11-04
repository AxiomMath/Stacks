module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AlgClosedField
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.GroupTheory.TorsionDivisible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The `n`-torsion of a commutative group scheme

For a commutative group object `G` in a cartesian monoidal category with pullbacks,
multiplication by an integer `n` is the `n`-th power `[n] = (𝟙 G) ^ n` in the commutative group
`G ⟶ G`; it is a homomorphism of group objects, and its kernel `G[n]` is the fibre product of
`[n]` with the unit `𝟙_ C ⟶ G`, a group object.  For a commutative group scheme `G` over a field
`k` this file relates `G[n]` to the `n`-torsion of the group `G(k)` of rational points, and
assembles the group theory of `StacksFrontier.GroupTheory.TorsionDivisible` into the shape used in
parts (7) and (8) of Stacks Tag 03RP.

## Main definitions

* `CategoryTheory.GrpObj.torsion G n`: the `n`-torsion `G[n] = Ker([n])` of a commutative group
  object, as a group object.
* `CategoryTheory.GrpObj.torsionι G n`: its inclusion into `G`.
* `AlgebraicGeometry.torsionByEquivSections`: the `n`-torsion points of `G(k)` are the sections
  of `G[n] ⟶ Spec k`.

## Main results

* `CategoryTheory.GrpObj.isMonHom_zpow_id`: multiplication by `n` on a commutative group object
  is a homomorphism.
* `CategoryTheory.GrpObj.isPullback_torsion` and `AlgebraicGeometry.isPullback_torsion_left`:
  `G[n]` is the fibre of `[n]` over the unit, in `C` and, for group schemes, in schemes.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_torsion_hom` and
  `AlgebraicGeometry.etale_torsion_hom`: `G[n]` inherits finite local freeness of a given rank,
  and étaleness, from `[n]`.
* `AlgebraicGeometry.exists_zpow_eq_of_surjective`: over an algebraically closed field, if `[n]`
  is surjective then every rational point is an `n`-th power.
* `AlgebraicGeometry.nonempty_torsionBy_addEquiv_of_etale` and
  `AlgebraicGeometry.exists_torsionBy_prime_pow_addEquiv`: the structure of the torsion of `G(k)`
  from the structure of the torsion group schemes.

## Implementation notes

`G[n]` is the pullback in `Grp C` of the two homomorphisms `[n]` and the unit; `Grp C` has the
limits of `C` (`CategoryTheory.Grp.forget` creates them), so the group structure on `G[n]` is the
canonical one making the inclusion a homomorphism, and the forgetful functor carries the
pullback square to a pullback square in `C`.  Rational points of a scheme `G` over `Spec k` are
the morphisms `𝟙_ (Over (Spec k)) ⟶ G`, with the group structure coming from the group object;
the `n`-torsion of that group is written additively, as Mathlib's `AddSubgroup.torsionBy`.

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (G : C) [GrpObj G] [IsCommMonObj G]

/-- Multiplication by an integer on a commutative group object is a homomorphism. -/
instance isMonHom_zpow_id (n : ℤ) : IsMonHom ((𝟙 G) ^ n) := by
  simpa only [Grp.Hom.hom_hom_zpow, Grp.id_hom_hom] using
    (inferInstance : IsMonHom ((𝟙 (Grp.mk G)) ^ n).hom.hom)

variable [HasPullbacks C]

/-- The `n`-torsion `G[n] = Ker([n] : G ⟶ G)` of a commutative group object: the fibre product,
in group objects, of multiplication by `n` with the unit. -/
@[sga "3 IX 4.7", sga "3 X 8.5", sga "3 XI 2.4" "partial"]
noncomputable def torsion (n : ℤ) : Grp C :=
  pullback (Grp.ofHom ((𝟙 G) ^ n)) (Grp.ofHom η[G])

/-- The inclusion of the `n`-torsion `G[n]` into `G`. -/
noncomputable def torsionι (n : ℤ) : (torsion G n).X ⟶ G :=
  (pullback.fst (Grp.ofHom ((𝟙 G) ^ n)) (Grp.ofHom η[G])).hom.hom

/-- The inclusion of the `n`-torsion `G[n]` into `G` is a homomorphism of group objects. -/
instance (n : ℤ) : IsMonHom (torsionι G n) :=
  (pullback.fst (Grp.ofHom ((𝟙 G) ^ n)) (Grp.ofHom η[G])).hom.isMonHom_hom

/-- The `n`-torsion is the fibre of multiplication by `n` over the unit. -/
theorem isPullback_torsion (n : ℤ) :
    IsPullback (torsionι G n) (toUnit (torsion G n).X : _ ⟶ 𝟙_ C) ((𝟙 G) ^ n) η[G] := by
  have h := (IsPullback.of_hasPullback (Grp.ofHom ((𝟙 G) ^ n)) (Grp.ofHom η[G])).map (Grp.forget C)
  rwa [show (Grp.forget C).map (pullback.snd (Grp.ofHom ((𝟙 G) ^ n)) (Grp.ofHom η[G])) =
    toUnit _ from toUnit_unique _ _] at h

/-- The points of the `n`-torsion `G[n]` with values in `X` are the `n`-torsion points of `G`
with values in `X`, through the inclusion `G[n] ⟶ G`. -/
noncomputable def torsionPointsEquiv (X : C) (n : ℤ) :
    (X ⟶ (torsion G n).X) ≃ {x : X ⟶ G // x ^ n = 1} where
  toFun t := ⟨t ≫ torsionι G n, by
    rw [← Category.comp_id (t ≫ torsionι G n), ← GrpObj.comp_zpow, Category.assoc,
      (isPullback_torsion G n).w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ _)]⟩
  invFun x := (isPullback_torsion G n).lift x.1 (toUnit X) (by
    rw [GrpObj.comp_zpow, Category.comp_id, x.2]; rfl)
  left_inv t := (isPullback_torsion G n).hom_ext (by simp) (toUnit_unique _ _)
  right_inv x := Subtype.ext (by simp)

/-- The `n`-torsion point of `G` corresponding to `t : X ⟶ G[n]` is the composite of `t` with
the inclusion `G[n] ⟶ G`. -/
@[simp]
theorem torsionPointsEquiv_apply_coe (X : C) (n : ℤ) (t : X ⟶ (torsion G n).X) :
    (torsionPointsEquiv G X n t : X ⟶ G) = t ≫ torsionι G n := rfl

end CategoryTheory.GrpObj

namespace AlgebraicGeometry
variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]

/-- The `n`-torsion of a commutative group scheme is the scheme-theoretic fibre of
multiplication by `n` over the identity section. -/
@[sga "3 XI 2.4" "partial"]
theorem isPullback_torsion_left (n : ℤ) :
    IsPullback (GrpObj.torsionι G n).left (GrpObj.torsion G n).X.hom ((𝟙 G) ^ n).left
      (η[G]).left := by
  have := (GrpObj.isPullback_torsion G n).map (Over.forget S)
  simpa using this

/-- Sections of an object `Y` over `S` are the morphisms from the terminal object `𝟙_ (Over S)`
to `Y`. -/
noncomputable def sectionsEquivHomFromUnit (Y : Over S) :
    {σ : S ⟶ Y.left // σ ≫ Y.hom = 𝟙 S} ≃ (𝟙_ (Over S) ⟶ Y) where
  toFun σ := Over.homMk σ.1 σ.2
  invFun t := ⟨t.left, by simp⟩
  left_inv σ := rfl
  right_inv t := by ext; rfl

/-- The `n`-torsion of a commutative group scheme is finite locally free of rank `r` as soon as
multiplication by `n` is: it is a base change of multiplication by `n` (Tag 02KA). -/
theorem isFiniteLocallyFreeOfRank_torsion_hom (n : ℤ) (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 G) ^ n).left r] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (GrpObj.torsion G n).X.hom r :=
  Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback (isPullback_torsion_left G n)

/-- The `n`-torsion of a commutative group scheme is étale as soon as multiplication by `n` is:
it is a base change of multiplication by `n`. -/
@[sga "3 X 8.5" "kernel clause"]
theorem etale_torsion_hom (n : ℤ) [Etale ((𝟙 G) ^ n).left] :
    Etale (GrpObj.torsion G n).X.hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_torsion_left G n) ‹_›

/-- The inclusion of the `n`-torsion sends its identity to the identity. -/
theorem torsionι_left_unit_apply (n : ℤ) (s : S) :
    (GrpObj.torsionι G n).left ((η[(GrpObj.torsion G n).X]).left s) = (η[G]).left s := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]

end AlgebraicGeometry

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G]

/-- The `n`-torsion points of `G(k)`, written additively, are the morphisms from the terminal
object to the `n`-torsion group scheme `G[n]`. -/
noncomputable def torsionByEquivHomTorsion (n : ℤ) :
    AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ G)) n ≃
      (𝟙_ (Over (Spec (.of k))) ⟶ (GrpObj.torsion G n).X) :=
  have hmem : ∀ x : Additive (𝟙_ (Over (Spec (.of k))) ⟶ G),
      x ∈ AddSubgroup.torsionBy _ n ↔ x.toMul ^ n = 1 := fun x =>
    (Submodule.mem_torsionBy_iff n x).trans <| by
      rw [← toMul_zsmul, ← toMul_zero, Additive.toMul.injective.eq_iff]
  { toFun x := (GrpObj.torsionPointsEquiv G _ n).symm ⟨x.1.toMul, (hmem x.1).mp x.2⟩
    invFun t := ⟨Additive.ofMul (GrpObj.torsionPointsEquiv G _ n t : _ ⟶ G), (hmem _).mpr
      (GrpObj.torsionPointsEquiv G _ n t).2⟩
    left_inv x := Subtype.ext (by simp)
    right_inv t := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext rfl }

/-- The `n`-torsion points of `G(k)` are the sections of the `n`-torsion group scheme. -/
noncomputable def torsionByEquivSections (n : ℤ) :
    AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ G)) n ≃
      {σ : Spec (.of k) ⟶ (GrpObj.torsion G n).X.left //
        σ ≫ (GrpObj.torsion G n).X.hom = 𝟙 _} :=
  (torsionByEquivHomTorsion G n).trans (sectionsEquivHomFromUnit _).symm

omit [IsCommMonObj G] in
/-- **Points of a group scheme along a surjective multiplication map.** If multiplication by `n`
on a commutative group scheme `G`, locally of finite type over an algebraically closed field
`k`, is surjective, then every `k`-point of `G` is an `n`-th power. -/
theorem exists_zpow_eq_of_surjective [IsAlgClosed k] [LocallyOfFiniteType G.hom] (n : ℤ)
    [Surjective ((𝟙 G) ^ n).left] (x : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ G, y ^ n = x := by
  obtain ⟨y, hy, hyx⟩ := exists_comp_eq_of_surjective_of_isAlgClosed G.hom G.hom
    ((𝟙 G) ^ n).left (Over.w _) x.left (by simp)
  refine ⟨Over.homMk y hy, ?_⟩
  rw [← Category.comp_id (Over.homMk y hy : 𝟙_ (Over (Spec (.of k))) ⟶ G), ← GrpObj.comp_zpow]
  ext
  simpa using hyx

/-- If every element of a group is an `n`-th power, then every element of its additive version is
an `n`-fold multiple. -/
private theorem exists_zsmul_eq_of_forall_exists_zpow_eq {M : Type*} [Group M] {n : ℤ}
    (h : ∀ x : M, ∃ y, y ^ n = x) (x : Additive M) : ∃ y : Additive M, n • y = x :=
  let ⟨y, hy⟩ := h x.toMul
  ⟨Additive.ofMul y, by rw [← ofMul_zpow, hy, ofMul_toMul]⟩

/-- **Torsion points of a group scheme over an algebraically closed field.** Let `G` be a
commutative group scheme over an algebraically closed field `k` and `n ≠ 0`.  Suppose that every
`k`-point of `G` is an `ℓ`-th power for each prime `ℓ ∣ n`, and that the `ℓ`-torsion group scheme
`G[ℓ]` is étale and finite locally free of rank `ℓ ^ r` over `k`.  Then the `n`-torsion of
`G(k)` is isomorphic to `(ℤ/nℤ)^r`. -/
theorem nonempty_torsionBy_addEquiv_of_etale [IsAlgClosed k] (n : ℕ) (hn : n ≠ 0) (r : ℕ)
    (hdiv : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ G,
      ∃ y, y ^ (ℓ : ℤ) = x)
    (htors : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → Etale (GrpObj.torsion G ℓ).X.hom ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (GrpObj.torsion G ℓ).X.hom (ℓ ^ r)) :
    Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ G)) n ≃+
      (Fin r → ZMod n)) := by
  refine AddCommGroup.nonempty_torsionBy_addEquiv_of_divisible hn (fun ℓ hℓ hd x => ?_)
    (fun ℓ hℓ hd => ?_)
  · exact exists_zsmul_eq_of_forall_exists_zpow_eq (hdiv ℓ hℓ hd) x
  · obtain ⟨het, hrk⟩ := htors ℓ hℓ hd
    have hcard : Nat.card (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ G))
        (ℓ : ℤ)) = ℓ ^ r := by
      rw [Nat.card_congr (torsionByEquivSections G ℓ)]
      exact Stacks.Morphisms.card_sections_of_etale_of_isAlgClosed _ _ hrk het
    have : Finite (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ G))
        (ℓ : ℤ)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
    obtain ⟨f, hf, ⟨e⟩⟩ := AddCommGroup.exists_torsionBy_prime_addEquiv hℓ (G :=
      Additive (𝟙_ (Over (Spec (.of k))) ⟶ G))
    obtain rfl : f = r := Nat.pow_right_injective hℓ.two_le (hf.trans hcard)
    exact ⟨e⟩

/-- **Prime-power torsion points of a group scheme over an algebraically closed field.** Let `G`
be a commutative group scheme over an algebraically closed field `k`, and `p` a prime such that
every `k`-point of `G` is a `p`-th power and the `p`-torsion points of `G(k)` are finite in
number, at most `p ^ g`.  Then there is `f ≤ g` with `G(k)[p ^ m] ≅ (ℤ/p^mℤ)^f` for every `m`. -/
theorem exists_torsionBy_prime_pow_addEquiv [IsAlgClosed k] (p : ℕ) (hp : p.Prime) (g : ℕ)
    (hdiv : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ G, ∃ y, y ^ (p : ℤ) = x)
    [Finite (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ G)) p)]
    (hcard : Nat.card (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ G)) p) ≤
      p ^ g) :
    ∃ f ≤ g, ∀ m : ℕ, Nonempty
      (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ G)) ((p ^ m : ℕ) : ℤ) ≃+
        (Fin f → ZMod (p ^ m))) := by
  obtain ⟨f, hf, ⟨e⟩⟩ := AddCommGroup.exists_torsionBy_prime_addEquiv hp (G :=
    Additive (𝟙_ (Over (Spec (.of k))) ⟶ G))
  refine ⟨f, (Nat.pow_le_pow_iff_right hp.two_le).mp (hf ▸ hcard), fun m => ?_⟩
  have hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ p ^ m → ℓ = p := fun ℓ hℓ hd =>
    (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow hd)
  refine AddCommGroup.nonempty_torsionBy_addEquiv_of_divisible (pow_ne_zero _ hp.ne_zero)
    (fun ℓ hℓ hd x => ?_) (fun ℓ hℓ hd => ?_)
  · obtain rfl := hprime ℓ hℓ hd
    exact exists_zsmul_eq_of_forall_exists_zpow_eq hdiv x
  · obtain rfl := hprime ℓ hℓ hd
    exact ⟨e⟩

end AlgebraicGeometry
