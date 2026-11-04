module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Iterated
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Picard.PurelyInseparablePullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Prime-to-`p` torsion in the Picard group and a base change of bounded exponent

Let `k` be a field of characteristic `p > 0` and let `k'/k` be an extension in which the
`p ^ m`-th power of every element already lies in `k` — a purely inseparable extension of
exponent at most `m`, for instance. Then the `p ^ m`-power map `k' → k` is a ring
homomorphism, so `Spec k → Spec k'` is a morphism of schemes, and the two composites of it
with `Spec k' → Spec k` are the `m`-fold absolute Frobenius of `Spec k` and of `Spec k'`
respectively.

For an arbitrary `k`-scheme `f : X ⟶ Spec k`, the base change `X_{k'} = X ×_{Spec k} Spec k'`
then receives a morphism from `X`, the lift of the `m`-fold absolute Frobenius of `X` and of `f`
followed by `Spec k → Spec k'`. Composed with the first projection in either order, it gives the
`m`-fold absolute Frobenius of `X` and of `X_{k'}`. Consequently, for every integer `n` prime to
`p`, pullback along `X_{k'} → X` is a bijection on the `n`-torsion of the Picard groups.

## Main definitions

* `Stacks.FieldTheory.algebraMapRangeEquiv` — a field is isomorphic to the range of its
  structure map into an extension.
* `Stacks.FieldTheory.powDescent` — the `p ^ m`-power map of an extension of bounded exponent,
  read as a ring homomorphism into the base field.
* `AlgebraicGeometry.frobeniusBaseChangeSection` — the morphism from `X` to its base change,
  built from a Frobenius factorization of the base.

## Main results

* `AlgebraicGeometry.absoluteFrobeniusPow_zero`,
  `AlgebraicGeometry.absoluteFrobeniusPow_succ_eq_comp` — the two recursion equations for the
  iterated absolute Frobenius.
* `AlgebraicGeometry.absoluteFrobeniusPow_naturality` — the iterate of Stacks Tag 0CC7.
* `AlgebraicGeometry.absoluteFrobeniusPow_appTop_apply` — the `m`-fold absolute Frobenius
  raises a global section to its `p ^ m`-th power.
* `AlgebraicGeometry.specMap_eq_absoluteFrobeniusPow` — a ring endomorphism raising every
  element to its `p ^ m`-th power induces the `m`-fold absolute Frobenius on the spectrum.
* `Stacks.Picard.schemePullbackClass_absoluteFrobeniusPow_eq_zsmul` — pullback along the
  `m`-fold absolute Frobenius is multiplication by `p ^ m` on the Picard group.
* `AlgebraicGeometry.frobeniusBaseChangeSection_comp_fst`,
  `AlgebraicGeometry.fst_comp_frobeniusBaseChangeSection` — the two composites of the section
  with the first projection are the `m`-fold absolute Frobenius of `X` and of the base change.
* `Stacks.Picard.bijOn_schemePullbackClass_zsmulTorsion_of_frobenius` — a Frobenius
  factorization makes pullback a bijection on prime-to-`p` torsion.
* `Stacks.Picard.bijOn_schemePullbackClass_zsmulTorsion_of_pow_mem_range` — the same for the
  base change along an extension of bounded exponent.

## Implementation notes

No `@[stacks]` attribute is attached. This is the bounded-exponent case of Stacks Tag 0CD5, not
that tag: the tag asserts the conclusion for an arbitrary purely inseparable extension, with no
bound on the exponent. `StacksFrontier/AlgebraicGeometry/Picard/TorsionBaseChange.lean` removes the
bound by passing to the finite subextensions. The results here need neither quasi-compactness,
quasi-separatedness nor `H^0(X, O_X) = k`.

## References

* [Stacks Project, Tag 0CD5](https://stacks.math.columbia.edu/tag/0CD5)
* [Stacks Project, Tag 0CC7](https://stacks.math.columbia.edu/tag/0CC7)
* [Stacks Project, Tag 03SM](https://stacks.math.columbia.edu/tag/03SM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Frobenius

universe u

namespace Stacks.FieldTheory

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']

/-- A field extension is isomorphic, as a ring, to the range of its structure map. -/
def algebraMapRangeEquiv : k ≃+* (algebraMap k k').range :=
  RingEquiv.ofBijective (algebraMap k k').rangeRestrict
    ⟨RingHom.injective_codRestrict.mpr (algebraMap k k').injective,
      (algebraMap k k').rangeRestrict_surjective⟩

/-- The inverse of `Stacks.FieldTheory.algebraMapRangeEquiv`, followed by the structure map, is
the inclusion of the range. -/
theorem algebraMap_algebraMapRangeEquiv_symm (y : (algebraMap k k').range) :
    algebraMap k k' ((algebraMapRangeEquiv k k').symm y) = (y : k') :=
  congrArg Subtype.val ((algebraMapRangeEquiv k k').apply_symm_apply y)

variable (p m : ℕ)

/-- For a field extension `k'/k` of exponential characteristic `p` in which the `p ^ m`-th
power of every element lies in `k`, the `p ^ m`-power map read as a ring homomorphism to the
base field. -/
@[ega "0 22.4.8" "special case"]
def powDescent [ExpChar k' p] (h : ∀ x : k', x ^ p ^ m ∈ (algebraMap k k').range) :
    k' →+* k :=
  ((algebraMapRangeEquiv k k').symm : _ →+* k).comp
    ((iterateFrobenius k' p m).codRestrict (algebraMap k k').range h)

variable {k k' p m}

@[simp]
theorem algebraMap_powDescent [ExpChar k' p]
    (h : ∀ x : k', x ^ p ^ m ∈ (algebraMap k k').range) (x : k') :
    algebraMap k k' (powDescent k k' p m h x) = x ^ p ^ m :=
  algebraMap_algebraMapRangeEquiv_symm k k' _

@[simp]
theorem powDescent_algebraMap [ExpChar k' p]
    (h : ∀ x : k', x ^ p ^ m ∈ (algebraMap k k').range) (y : k) :
    powDescent k k' p m h (algebraMap k k' y) = y ^ p ^ m :=
  (algebraMap k k').injective <| by
    rw [algebraMap_powDescent, map_pow]

end Stacks.FieldTheory

namespace AlgebraicGeometry

/-- The `0`-fold absolute Frobenius is the identity. -/
@[simp]
theorem absoluteFrobeniusPow_zero (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) : absoluteFrobeniusPow X p hX 0 = 𝟙 X := by
  simp only [pow_zero]
  rfl

/-- The `n + 1`-fold absolute Frobenius is the absolute Frobenius followed by the `n`-fold
one. -/
theorem absoluteFrobeniusPow_succ_eq_comp (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (n : ℕ) :
    absoluteFrobeniusPow X p hX (n + 1) =
      absoluteFrobenius X p hX ≫ absoluteFrobeniusPow X p hX n := by
  simp only [pow_succ, End.mul_def]

/-- The `n`-fold absolute Frobenius is natural with respect to morphisms of schemes in
characteristic `p`: the iterate of Stacks Tag 0CC7. -/
@[ega "0 21.2.6" "more general",
  sga "3 VIIA 4.1" "more general",
  sga "4½ Rapport 1.3" "more general"]
theorem absoluteFrobeniusPow_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (n : ℕ) :
    absoluteFrobeniusPow X p hX n ≫ f = f ≫ absoluteFrobeniusPow Y p hY n := by
  induction n with
  | zero => rw [absoluteFrobeniusPow_zero, absoluteFrobeniusPow_zero, Category.id_comp,
      Category.comp_id]
  | succ m ih =>
      rw [absoluteFrobeniusPow_succ_eq_comp, absoluteFrobeniusPow_succ_eq_comp, Category.assoc,
        ih, ← Category.assoc, absoluteFrobenius_naturality f p hX hY, Category.assoc]

/-- On global sections the `n`-fold absolute Frobenius raises a section to its `p ^ n`-th
power. -/
@[simp]
theorem absoluteFrobeniusPow_appTop_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (n : ℕ) (g : Γ(X, ⊤)) :
    (absoluteFrobeniusPow X p hX n).appTop g = g ^ p ^ n := by
  induction n with
  | zero => rw [absoluteFrobeniusPow_zero, pow_zero, pow_one, Scheme.Hom.id_appTop]; rfl
  | succ n ih =>
      rw [absoluteFrobeniusPow_succ_eq_comp, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, ih,
        show (absoluteFrobenius X p hX).appTop (g ^ p ^ n) = (g ^ p ^ n) ^ p from
          absoluteFrobenius_app_apply X p hX ⊤ _, ← pow_mul, ← pow_succ]

/-- The spectrum of a ring in which `p` vanishes is a scheme in characteristic `p`. -/
theorem isInCharacteristic_spec (R : Type u) [CommRing R] (p : ℕ) (hp : (p : R) = 0) :
    IsInCharacteristic (Spec (.of R)) p := by
  show (p : Γ(Spec (.of R), ⊤)) = 0
  rw [← map_natCast (Scheme.ΓSpecIso (.of R)).inv.hom p, hp, map_zero]

/-- A ring endomorphism that raises every element to its `p ^ m`-th power induces the `m`-fold
absolute Frobenius on the spectrum. -/
theorem specMap_eq_absoluteFrobeniusPow {R : Type u} [CommRing R] (w : R →+* R)
    (p m : ℕ) [Fact p.Prime] (hR : IsInCharacteristic (Spec (.of R)) p)
    (hw : ∀ a : R, w a = a ^ p ^ m) :
    Spec.map (CommRingCat.ofHom w) = absoluteFrobeniusPow (Spec (.of R)) p hR m := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec.map (CommRingCat.ofHom w)).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (absoluteFrobeniusPow (Spec (CommRingCat.of R)) p hR m).appTop := by
    rw [← Scheme.ΓSpecIso_inv_naturality]
    ext a
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, absoluteFrobeniusPow_appTop_apply]
    show (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w a) = _
    rw [hw, map_pow]
  exact ext_to_Spec key

/-- If `b ∘ a` raises every element of `R` to its `p ^ m`-th power, then `Spec b` followed by
`Spec a` is the `m`-fold absolute Frobenius of `Spec R`. -/
private theorem specMap_comp_eq_absoluteFrobeniusPow {R S : Type u} [CommRing R] [CommRing S]
    (a : R →+* S) (b : S →+* R) (p m : ℕ) [Fact p.Prime]
    (hR : IsInCharacteristic (Spec (.of R)) p) (h : ∀ x : R, b (a x) = x ^ p ^ m) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) =
      absoluteFrobeniusPow (Spec (.of R)) p hR m := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact specMap_eq_absoluteFrobeniusPow _ p m hR h

/-- **A Frobenius factorization of a base change.** Suppose the base morphism `g : T ⟶ S`
admits `s : S ⟶ T` with the two composites `s ≫ g` and `g ≫ s` equal to the `m`-fold absolute
Frobenius. Then every `S`-scheme `f : X ⟶ S` receives a morphism to its base change along `g`,
the lift of the `m`-fold absolute Frobenius of `X` and of `f ≫ s`. -/
def frobeniusBaseChangeSection {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (s : S ⟶ T)
    (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (m : ℕ)
    (hsg : s ≫ g = absoluteFrobeniusPow S p hS m) :
    X ⟶ pullback f g :=
  pullback.lift (absoluteFrobeniusPow X p (isInCharacteristic_of_hom f p hS) m) (f ≫ s) (by
    rw [absoluteFrobeniusPow_naturality f p (isInCharacteristic_of_hom f p hS) hS, ← hsg,
      Category.assoc])

/-- Composing the Frobenius section with the first projection gives the absolute Frobenius
of the source. -/
@[simp]
theorem frobeniusBaseChangeSection_comp_fst {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (s : S ⟶ T) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (m : ℕ)
    (hsg : s ≫ g = absoluteFrobeniusPow S p hS m) :
    frobeniusBaseChangeSection f g s p hS m hsg ≫ pullback.fst f g =
      absoluteFrobeniusPow X p (isInCharacteristic_of_hom f p hS) m :=
  pullback.lift_fst _ _ _

/-- Composing the first projection with the Frobenius section gives the absolute Frobenius
of the base change. -/
theorem fst_comp_frobeniusBaseChangeSection {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (s : S ⟶ T) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (m : ℕ)
    (hsg : s ≫ g = absoluteFrobeniusPow S p hS m)
    (hgs : g ≫ s = absoluteFrobeniusPow T p (isInCharacteristic_of_hom g p hS) m) :
    pullback.fst f g ≫ frobeniusBaseChangeSection f g s p hS m hsg =
      absoluteFrobeniusPow (pullback f g) p
        (isInCharacteristic_of_hom (pullback.fst f g ≫ f) p hS) m := by
  apply pullback.hom_ext
  · rw [Category.assoc, frobeniusBaseChangeSection_comp_fst,
      absoluteFrobeniusPow_naturality (pullback.fst f g) p _ _ m]
  · rw [absoluteFrobeniusPow_naturality (pullback.snd f g) p
        (isInCharacteristic_of_hom (pullback.fst f g ≫ f) p hS)
        (isInCharacteristic_of_hom g p hS) m, ← hgs,
      Category.assoc, frobeniusBaseChangeSection, pullback.lift_snd, ← Category.assoc,
      pullback.condition, Category.assoc]

end AlgebraicGeometry

namespace Stacks.Picard

/-- **Pullback along the `m`-fold absolute Frobenius is multiplication by `p ^ m` on the Picard
group.** -/
theorem schemePullbackClass_absoluteFrobeniusPow_eq_zsmul {X : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (m : ℕ) (x : ofScheme X) :
    schemePullbackClass (absoluteFrobeniusPow X p hX m) x = ((p : ℤ) ^ m) • x := by
  induction m with
  | zero => rw [absoluteFrobeniusPow_zero, schemePullbackClass_id, pow_zero, one_zsmul]
  | succ m ih =>
      rw [absoluteFrobeniusPow_succ_eq_comp, ← schemePullbackClass_comp, ih,
        schemePullbackClass_absoluteFrobenius, smul_smul, ← pow_succ']

/-- **Prime-to-`p` torsion in the Picard group is unchanged by a Frobenius factorization.**
Let `pr : Y ⟶ X` and `φ : X ⟶ Y` be morphisms of schemes in characteristic `p` whose two
composites are the `m`-fold absolute Frobenius. Then pullback along `pr` is a bijection from the
`n`-torsion of `Pic X` onto the `n`-torsion of `Pic Y`, for every integer `n` prime to `p`. -/
theorem bijOn_schemePullbackClass_zsmulTorsion_of_frobenius
    {X Y : Scheme.{u}} (pr : Y ⟶ X) (φ : X ⟶ Y) (p : ℕ) [Fact p.Prime] (m : ℕ)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) {n : ℤ}
    (hn : n.natAbs.Coprime p)
    (hXcomp : φ ≫ pr = absoluteFrobeniusPow X p hX m)
    (hYcomp : pr ≫ φ = absoluteFrobeniusPow Y p hY m) :
    Set.BijOn (schemePullbackClass pr)
      {x : ofScheme X | n • x = 0} {y : ofScheme Y | n • y = 0} :=
  bijOn_zsmulTorsion_of_comp_eq_prime_pow_zsmul (A := ofScheme X) (B := ofScheme Y)
    (schemePullbackClassHom pr) (schemePullbackClassHom φ) hn
    (fun x => by
      show schemePullbackClass φ (schemePullbackClass pr x) = _
      rw [schemePullbackClass_comp, hXcomp, schemePullbackClass_absoluteFrobeniusPow_eq_zsmul])
    (fun y => by
      show schemePullbackClass pr (schemePullbackClass φ y) = _
      rw [schemePullbackClass_comp, hYcomp, schemePullbackClass_absoluteFrobeniusPow_eq_zsmul])

/-- **Prime-to-`p` torsion in the Picard group is unchanged by a base field extension of
bounded exponent.**

Let `k'/k` be an extension of fields of characteristic `p` in which the `p ^ m`-th power of
every element of `k'` lies in `k` — for instance a purely inseparable extension of exponent at
most `m`. Then for any `k`-scheme `X` and any integer `n` prime to `p`, pullback along
`X_{k'} → X` is a bijection from the `n`-torsion of `Pic X` onto the `n`-torsion of
`Pic X_{k'}`. -/
theorem bijOn_schemePullbackClass_zsmulTorsion_of_pow_mem_range
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (p m : ℕ) [Fact p.Prime] [CharP k p]
    (hexp : ∀ x : k', x ^ p ^ m ∈ (algebraMap k k').range)
    {n : ℤ} (hn : n.natAbs.Coprime p)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hk : IsInCharacteristic (Spec (.of k)) p) :
    Set.BijOn
      (schemePullbackClass
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))))
      {x : ofScheme X | n • x = 0}
      {y : ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) |
        n • y = 0} := by
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have : ExpChar k' p := .prime Fact.out
  set a : CommRingCat.of k ⟶ CommRingCat.of k' := CommRingCat.ofHom (algebraMap k k')
  set ψ : k' →+* k := Stacks.FieldTheory.powDescent k k' p m hexp
  have hsg : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map a =
      absoluteFrobeniusPow (Spec (CommRingCat.of k)) p hk m :=
    specMap_comp_eq_absoluteFrobeniusPow _ _ p m hk
      (fun y => Stacks.FieldTheory.powDescent_algebraMap hexp y)
  have hgs : Spec.map a ≫ Spec.map (CommRingCat.ofHom ψ) =
      absoluteFrobeniusPow (Spec (CommRingCat.of k')) p
        (isInCharacteristic_of_hom (Spec.map a) p hk) m :=
    specMap_comp_eq_absoluteFrobeniusPow _ _ p m _
      (fun x => Stacks.FieldTheory.algebraMap_powDescent hexp x)
  exact bijOn_schemePullbackClass_zsmulTorsion_of_frobenius
    (pullback.fst f (Spec.map a))
    (frobeniusBaseChangeSection f (Spec.map a) (Spec.map (CommRingCat.ofHom ψ)) p hk m hsg)
    p m _ _ hn
    (frobeniusBaseChangeSection_comp_fst f (Spec.map a) _ p hk m hsg)
    (fst_comp_frobeniusBaseChangeSection f (Spec.map a) _ p hk m hsg hgs)

end Stacks.Picard

end
