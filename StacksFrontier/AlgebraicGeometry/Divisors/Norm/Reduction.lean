module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.Frobenius
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# A Frobenius norm for the reduction of a scheme in prime characteristic

Let `X` be a Noetherian scheme on which a prime `p` vanishes. The nilradical of `X` is
nilpotent, say `N`-th powers of nilpotents vanish, so for `p ^ e ≥ N` the `e`-fold absolute
Frobenius `F^e : X ⟶ X` — the identity on points, the `p ^ e`-th power on sections — has
kernel exactly the nilradical. Its scheme-theoretic image is therefore the reduction
`X_red`, and `F^e` factors as `X ⟶ X_red ⟶ X`. The first factor, read on sections, is a
norm of degree `p ^ e` for the closed immersion `X_red ⟶ X`: it is multiplicative and
compatible with restriction because it is a map of structure sheaves, it preserves vanishing
at points because the two schemes have the same points, and the norm of a function pulled
back from `X` is its `p ^ e`-th power because the composite is `F^e`.

## Main results

* `Stacks.Divisors.exists_normOfDegree_reduction`: **Tag 0BDZ.**

## Implementation notes

`Stacks.Divisors.frobeniusPow` is written out from `Stacks.Frobenius.primePowerEndomorphism`
rather than assembled as an `e`-fold composite of `Stacks.Frobenius.absoluteFrobenius`, for
one reason: with the base map literally `𝟙` every open is its own inverse image
*definitionally*, and the kernel computation below is about `Scheme.Hom.app` on an arbitrary
open, where a propositional comparison of `U` with `F^e ⁻¹ᵁ U` would have to be transported
through at every step. `Stacks.Divisors.frobeniusPow_one` identifies it with the absolute
Frobenius itself, and its section map is the `e`-fold iterate `Stacks.Divisors.primePowerIter`
of the very ring endomorphism `Stacks.Frobenius.primePowerEndomorphism` that the absolute
Frobenius itself is built from, so no mathematics is duplicated.

Nilpotence of the nilradical is extracted affine-locally over a finite subcover of the affine
cover, where it is `IsNoetherianRing.isNilpotent_nilradical`; the exponent is the supremum of
the finitely many local ones.

## References

* [Stacks Project, Tag 0BDZ](https://stacks.math.columbia.edu/tag/0BDZ)
* [Stacks Project, Tag 03SM](https://stacks.math.columbia.edu/tag/03SM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.Frobenius

universe u

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

/-- Iterated `p`-th power on a commutative ring in which `p` vanishes, as a ring
endomorphism: the `e`-fold composite of `Stacks.Frobenius.primePowerEndomorphism`. -/
noncomputable def primePowerIter {R : Type u} [CommRing R] (p e : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) : R →+* R :=
  Nat.rec (RingHom.id R) (fun _ f => (primePowerEndomorphism R p hp).comp f) e

/-- The iterated prime power endomorphism raises an element to its `p ^ e`-th power. -/
@[simp]
theorem primePowerIter_apply {R : Type u} [CommRing R] (p e : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) (x : R) : primePowerIter p e hp x = x ^ p ^ e := by
  induction e with
  | zero => simp [primePowerIter]
  | succ e ih =>
    show primePowerEndomorphism R p hp (primePowerIter p e hp x) = _
    rw [primePowerEndomorphism_apply, ih, ← pow_mul]
    rfl

/-- **The `e`-fold absolute Frobenius** of a scheme in characteristic `p`: the identity on
points and the `p ^ e`-th power map on the structure sheaf. It is written out rather than
assembled as a composite of `Stacks.Frobenius.absoluteFrobenius` so that an open is its own
inverse image definitionally; `Stacks.Divisors.frobeniusPow_one` identifies it with the
absolute Frobenius at `e = 1`. -/
@[implicit_reducible,
  sga "3 VIIA 4.1" "more general",
  sga "3 VIIB 4.1.1" "more general",
  sga "4½ Fonctions_L 3.4" "more general",
  sga "4½ Rapport 1.1",
  sga "5 XV 1.Definition2" "more general",
  sga "7 IX 4.3.2",
  sga "7 XXI 1.0",
  sga "7 XXII 6.2"]
noncomputable def frobeniusPow (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (e : ℕ) : X ⟶ X := by
  let α : X.presheaf ⟶ X.presheaf :=
    { app := fun U => CommRingCat.ofHom <|
        primePowerIter p e (cast_eq_zero_of_isInCharacteristic hX U.unop)
      naturality := by
        intro U V j
        ext s
        change primePowerIter p e (cast_eq_zero_of_isInCharacteristic hX V.unop)
            ((X.presheaf.map j) s) =
          X.presheaf.map j (primePowerIter p e
            (cast_eq_zero_of_isInCharacteristic hX U.unop) s)
        rw [primePowerIter_apply, primePowerIter_apply, map_pow] }
  refine Scheme.Hom.mk <| LocallyRingedSpace.homMk
    (InducedCategory.homMk ({ base := 𝟙 _, c := α } :
      X.toPresheafedSpace ⟶ X.toPresheafedSpace)) ?_
  rw [InducedCategory.homMk_hom]
  intro x
  refine ⟨fun a ha => ?_⟩
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  change IsUnit (X.presheaf.germ U x hxU s)
  refine (isUnit_pow_iff (pow_ne_zero e (Fact.out : p.Prime).ne_zero)).mp ?_
  rw [PresheafedSpace.stalkMap_germ_apply] at ha
  change IsUnit (X.presheaf.germ U x hxU
    (primePowerIter p e (cast_eq_zero_of_isInCharacteristic hX U) s)) at ha
  simpa only [primePowerIter_apply, map_pow, id_apply] using ha

/-- The `e`-fold absolute Frobenius is the identity on the underlying topological space. -/
@[simp]
theorem frobeniusPow_base (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (e : ℕ) :
    (frobeniusPow X p hX e).base = 𝟙 (X : TopCat) := rfl

/-- On every open set the `e`-fold absolute Frobenius raises sections to their `p ^ e`-th
powers. -/
@[simp]
theorem frobeniusPow_app_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (e : ℕ) (U : X.Opens) (s : Γ(X, U)) :
    (frobeniusPow X p hX e).app U s = s ^ p ^ e :=
  primePowerIter_apply p e (cast_eq_zero_of_isInCharacteristic hX U) s

/-- Identifying an open with its inverse image, the `e`-fold absolute Frobenius acts on
sections as the `p ^ e`-th power map. -/
theorem frobeniusPow_appLE_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (e : ℕ) (U : X.Opens)
    (h : U ≤ (frobeniusPow X p hX e) ⁻¹ᵁ U) (s : Γ(X, U)) :
    (frobeniusPow X p hX e).appLE U U h s = s ^ p ^ e := by
  show X.presheaf.map (𝟙 (op U)) ((frobeniusPow X p hX e).app U s) = _
  rw [X.presheaf.map_id, frobeniusPow_app_apply]
  simp

/-- The one-fold absolute Frobenius power is the absolute Frobenius. -/
theorem frobeniusPow_one (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) : frobeniusPow X p hX 1 = absoluteFrobenius X p hX :=
  eq_absoluteFrobenius X p hX _ (frobeniusPow_base X p hX 1) fun U s => by
    simpa using frobeniusPow_appLE_apply X p hX 1 U _ s

/-- **The nilradical of a Noetherian scheme is nilpotent.** The exponent is the supremum of
the nilpotence exponents on the members of a finite affine subcover. -/
@[ega "I 6.1.6"]
theorem exists_nilradical_pow_eq_bot (X : Scheme.{u}) [IsNoetherian X] :
    ∃ n : ℕ, 0 < n ∧ X.nilradical ^ n = ⊥ := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  let V (i : 𝒰.I₀) : X.affineOpens := ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange (𝒰.f i)⟩
  have hV : (⨆ i, (V i).1 : X.Opens) = ⊤ := by rw [← 𝒰.iSup_opensRange]
  have : Fintype 𝒰.I₀ := Fintype.ofFinite _
  have hnilpotent (i : 𝒰.I₀) : IsNilpotent (nilradical Γ(X, V i)) := by
    have : IsNoetherianRing Γ(X, V i) :=
      (inferInstance : IsNoetherian X).toIsLocallyNoetherian.component_noetherian (V i)
    exact IsNoetherianRing.isNilpotent_nilradical _
  choose n hn using hnilpotent
  refine ⟨Finset.sup Finset.univ n + 1, by omega, ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top V hV fun i => ?_
  show (nilradical Γ(X, V i)) ^ (Finset.sup Finset.univ n + 1) = ⊥
  refine le_antisymm ?_ bot_le
  exact (pow_le_pow_right_of_le_one' (by simp)
    ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))).trans_eq (hn i)

/-- **The kernel of a high enough Frobenius power is the nilradical.** A section killed by
the `p ^ e`-th power map is nilpotent, and conversely a nilpotent section of nilpotence
exponent at most `p ^ e` is killed. -/
theorem frobeniusPow_ker (X : Scheme.{u}) (p e n : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (hnil : X.nilradical ^ n = ⊥) (hn : n ≤ p ^ e) :
    (frobeniusPow X p hX e).ker = X.nilradical := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Scheme.IdealSheafData.le_def]
    intro U
    refine (Scheme.Hom.ideal_ker_le (frobeniusPow X p hX e) U).trans fun x hx => ?_
    show x ∈ (⊥ : Ideal Γ(X, U)).radical
    rw [Ideal.mem_radical_iff]
    refine ⟨p ^ e, ?_⟩
    rw [← frobeniusPow_app_apply X p hX e U x, RingHom.mem_ker.mp hx]
    exact Ideal.zero_mem _
  · show X.nilradical ≤ Scheme.IdealSheafData.ofIdeals _
    rw [Scheme.IdealSheafData.le_ofIdeals_iff]
    intro U x hx
    have hpowU : (X.nilradical.ideal U) ^ n = ⊥ := by
      simpa using congrArg (fun I : X.IdealSheafData => I.ideal U) hnil
    have hxn : x ^ n = 0 := by simpa [hpowU] using Ideal.pow_mem_pow hx n
    refine RingHom.mem_ker.mpr ?_
    rw [frobeniusPow_app_apply X p hX e U x,
      show p ^ e = n + (p ^ e - n) by omega, pow_add, hxn, zero_mul]
    rfl

/-- **Stacks Project, Tag 0BDZ.** On a Noetherian scheme in prime characteristic `p` a
sufficiently high Frobenius power supplies a norm of degree a positive power of `p` for the
canonical morphism from the reduction. -/
@[stacks 0BDZ]
theorem exists_normOfDegree_reduction (X : Scheme.{u}) [IsNoetherian X]
    (p : ℕ) (hp : p.Prime) (hchar : (p : Γ(X, ⊤)) = 0) :
    ∃ e : ℕ, 0 < e ∧
      HasNormOfDegree (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subschemeι
        (p ^ e) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hnil⟩ := exists_nilradical_pow_eq_bot X
  refine ⟨Nat.log p n + 1, by omega, ?_⟩
  set e : ℕ := Nat.log p n + 1 with he
  have hn : n ≤ p ^ e := (Nat.lt_pow_succ_log_self hp.one_lt n).le
  set f : X ⟶ X := frobeniusPow X p hchar e with hf
  have hker : f.ker = X.nilradical := frobeniusPow_ker X p e n hchar hnil hn
  set g : X ⟶ f.image := f.toImage with hg
  set i : f.image ⟶ X := f.imageι with hi
  have hgi : g ≫ i = f := Scheme.Hom.toImage_imageι f
  have hpoint (z : X) : i (g z) = z := by
    simpa [Scheme.Hom.comp_apply, hf, frobeniusPow_base] using
      congrArg (fun k : X ⟶ X => k z) hgi
  set iOpen : X.Opens → f.image.Opens := fun U => (Opens.map i.base).obj U with hiOpen
  have hbound (U : X.Opens) : U ≤ g ⁻¹ᵁ iOpen U := fun z hz => by
    show i (g z) ∈ U
    rwa [hpoint z]
  let Nmap : MorphismNormMap i :=
    { app := fun U => (g.appLE (iOpen U) U (hbound U)).hom.toMonoidHom
      naturality := by
        intro U V j s
        show g.appLE (iOpen V) V (hbound V)
            ((f.image.presheaf.map ((Opens.map i.base).map j).op) s) =
          X.presheaf.map j.op (g.appLE (iOpen U) U (hbound U) s)
        rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE, ← ConcreteCategory.comp_apply,
          Scheme.Hom.appLE_map]
      app_eq_zero_at_image := by
        intro U s x hx hs
        show X.evaluation U (i x) hx (g.appLE (iOpen U) U (hbound U) s) = 0
        have hpoint' : g (i x) = x := i.isEmbedding.injective (by rw [hpoint])
        have hxg : g (i x) ∈ iOpen U := hbound U hx
        have hs' : (f.image.evaluation (iOpen U) (g (i x)) hxg) s = 0 := by
          suffices ∀ (y : f.image) (_ : y = x) (h : y ∈ iOpen U),
              (f.image.evaluation (iOpen U) y h) s = 0 from this (g (i x)) hpoint' hxg
          rintro y rfl h
          simpa only [hiOpen] using hs
        have hres : X.evaluation U (i x) hx (g.appLE (iOpen U) U (hbound U) s) =
            X.evaluation (g ⁻¹ᵁ iOpen U) (i x) (hbound U hx) (g.app (iOpen U) s) := by
          simp [Scheme.evaluation, Scheme.Hom.appLE]
        show X.evaluation U (i x) hx ((g.appLE (iOpen U) U (hbound U)).hom s) = 0
        rw [hres, ← Scheme.evaluation_naturality_apply g (i x) hxg s, hs']
        exact map_zero _ }
  have hnorm : MorphismNorm i (p ^ e) :=
    { toMorphismNormMap := Nmap
      app_pullback := by
        intro U s
        show g.appLE (i ⁻¹ᵁ U) U (hbound U) (i.app U s) = _
        have hcomp' : i.appLE U (i ⁻¹ᵁ U) le_rfl ≫ g.appLE (i ⁻¹ᵁ U) U (hbound U) =
            f.appLE U U (by simp [hf, frobeniusPow_base]) := by
          simpa only [hgi] using Scheme.Hom.appLE_comp_appLE g i U (i ⁻¹ᵁ U) U le_rfl (hbound U)
        rw [Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply, hcomp']
        simpa [hf] using frobeniusPow_appLE_apply X p hchar e U _ s }
  rw [Scheme.IdealSheafData.vanishingIdeal_top, ← hker]
  exact ⟨hnorm⟩

end Stacks.Divisors

end
