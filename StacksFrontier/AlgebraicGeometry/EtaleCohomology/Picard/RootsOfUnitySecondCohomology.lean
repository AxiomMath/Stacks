module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupSmoothCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.RootsOfUnityFirstCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# The second étale cohomology of the roots of unity on a curve

Let `X` be a scheme and `n ≠ 0` invertible on `X`, and suppose `H²_étale(X, 𝐆_m) = 0`. The
Kummer sequence `0 → μ_n → 𝐆_m → 𝐆_m → 0` (Stacks 03PL) has the segment

`H¹(X, 𝐆_m) --n--> H¹(X, 𝐆_m) --δ--> H²(X, μ_n) → H²(X, 𝐆_m) = 0`,

so the Kummer coboundary `δ` identifies `H²(X, μ_n)` with the cokernel of multiplication by `n`
on `H¹(X, 𝐆_m)`, and the étale identification `H¹(X, 𝐆_m) = Pic(X)` (Stacks 03P8) turns that
cokernel into `Pic(X)/n Pic(X)`.

On a smooth curve over an algebraically closed field the vanishing of `H²(X, 𝐆_m)` is Stacks
03RM, so `H²_étale(X, μ_n) ≅ Pic(X)/n Pic(X)` with no further hypothesis. This is the étale
cohomological half of the clause `q = 2` of Stacks 03RQ; the other half, `Pic(X)/n Pic(X) ≅ 𝐙/n𝐙`
through the degree, uses the `n`-divisibility of `Pic⁰(X)`.

The same Kummer segment one degree higher, with `H²(X, 𝐆_m) = H³(X, 𝐆_m) = 0`, gives the clause
`H^q_étale(X, μ_n) = 0` for `q ≥ 3`.

All names are in the namespace `Stacks.Kummer`.

## Main definitions

* `h2RootsOfUnityAddEquivPicardQuotient`: `H²(X, μ_n) ≃+ Pic(X)/n Pic(X)` when `H²(X, 𝐆_m) = 0`.
* `h2RootsOfUnityAddEquivPicardQuotient_of_smoothCurve`: the same on a smooth curve over an
  algebraically closed field, `n` invertible in the field.
* `quotientNsmulAddEquivZModOfSurjective`: `P/nP ≅ 𝐙/n𝐙` for an onto homomorphism `P → 𝐙` with
  `n`-divisible kernel; with `P = Pic(X)` and the degree it gives the clause `q = 2` of Stacks 03RQ
  when `Pic⁰(X)` is `n`-divisible.

## Main results

* `subsingleton_sheafH_rootsOfUnitySheaf_of_isCurve`: **Stacks 03RQ**, the clause `q ≥ 3`, for a
  smooth projective curve.

## Implementation notes

The curve statements are at the coefficient universe of Stacks 03RM, `AddCommGrpCat.{u + 1}` for
`X : Scheme.{u}` with cohomology `Sheaf.H.{u + 1}`; the Grothendieck abelian structure, which
provides `HasExt.{u + 1}`, is taken with its universe pinned as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupSmoothCurveVanishing`.

The quotient `Pic(X)/n Pic(X)` is written as the quotient by the range of
`nsmulAddMonoidHom n`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace Stacks.Kummer

open _root_.AlgebraicGeometry

section General

variable (X : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

include hn0 hX in
/-- The kernel of the Kummer coboundary `H¹(X, 𝐆_m) → H²(X, μ_n)` is the image of
multiplication by `n`. -/
theorem ker_kummerδ_one :
    (kummerδ.{w, u, v} X hn0 hX 1).ker =
      (nsmulAddMonoidHom n : Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) 1 →+ _).range := by
  ext x
  rw [AddMonoidHom.mem_ker, ← mem_range_sheafH_map_powMap_iff X hn0 hX 1 x]
  simp only [AddMonoidHom.mem_range, sheafH_map_powMap, nsmulAddMonoidHom_apply]

/-- An additive equivalence carries the image of multiplication by `n` onto the image of
multiplication by `n`. -/
theorem _root_.AddSubgroup.map_range_nsmulAddMonoidHom {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (e : A ≃+ B) (n : ℕ) :
    (nsmulAddMonoidHom n : A →+ A).range.map (e : A →+ B) =
      (nsmulAddMonoidHom n : B →+ B).range := by
  ext b
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨e a, by simp⟩
  · rintro ⟨b', rfl⟩
    exact ⟨n • e.symm b', ⟨e.symm b', rfl⟩, by simp⟩

include hn0 hX in
/-- **`H²_étale(X, μ_n) ≅ Pic(X)/n Pic(X)`** when `n` is invertible on `X` and
`H²_étale(X, 𝐆_m) = 0`: the Kummer coboundary is then onto, with kernel `n H¹(X, 𝐆_m)`, and
`H¹(X, 𝐆_m) = Pic(X)` by Stacks 03P8. -/
def h2RootsOfUnityAddEquivPicardQuotient
    (h2 : Subsingleton (Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) 2)) :
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 2 ≃+
      Picard.ofScheme X ⧸ (nsmulAddMonoidHom n : Picard.ofScheme X →+ Picard.ofScheme X).range :=
  (QuotientAddGroup.quotientKerEquivOfSurjective (kummerδ.{w, u, v} X hn0 hX 1)
      (surjective_kummerδ_one X hn0 hX h2)).symm.trans
    (QuotientAddGroup.congr _ _ (etaleH1MultiplicativeAddEquivPicard.{w, v, u} X)
      (by rw [ker_kummerδ_one X hn0 hX]; exact AddSubgroup.map_range_nsmulAddMonoidHom _ n))


/-- **`P/nP ≅ 𝐙/n𝐙` from an onto degree with `n`-divisible kernel.** Let `d : P →+ ℤ` be onto and
suppose every element of its kernel is an `n`-th multiple. Then `d` mod `n` identifies `P/nP`
with `𝐙/n𝐙`: an element `x` with `d x = n m` differs from `n y₀`, where `d y₀ = m`, by an element
of the kernel, hence is an `n`-th multiple.

With `P = Pic(X)` and `d` the degree, whose kernel is `Pic⁰(X)`, this is the clause `q = 2` of
Stacks 03RQ when `Pic⁰(X)` is `n`-divisible. -/
def quotientNsmulAddEquivZModOfSurjective {P : Type*} [AddCommGroup P] (d : P →+ ℤ)
    (hd : Function.Surjective d) (n : ℕ) (hdiv : ∀ x : P, d x = 0 → ∃ y : P, n • y = x) :
    P ⧸ (nsmulAddMonoidHom n : P →+ P).range ≃+ ZMod n :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
      ext x
      simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddMonoidHom.mem_ker,
        AddMonoidHom.coe_comp, Function.comp_apply, Int.coe_castAddHom,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨d y, by simp⟩
      · rintro ⟨m, hm⟩
        obtain ⟨y₀, hy₀⟩ := hd m
        obtain ⟨z, hz⟩ := hdiv (x - n • y₀) (by simp [hm, hy₀])
        exact ⟨y₀ + z, by rw [smul_add, hz, add_sub_cancel]⟩ :
      (nsmulAddMonoidHom n : P →+ P).range = ((Int.castAddHom (ZMod n)).comp d).ker)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (ZMod.intCast_surjective.comp hd))

end General

section Curve

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] {n : ℕ} (hn : IsUnit (n : k))

include f hn in
/-- **`H²_étale(X, μ_n) ≅ Pic(X)/n Pic(X)` on a smooth curve over an algebraically closed
field**, `n` invertible in the field. This is
`Stacks.Kummer.h2RootsOfUnityAddEquivPicardQuotient` with `H²(X, 𝐆_m) = 0` supplied by Stacks
03RM, `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve`. -/
def h2RootsOfUnityAddEquivPicardQuotient_of_smoothCurve :
    Sheaf.H.{u + 1, u + 1} (rootsOfUnitySheaf.{u, u + 1} X n) 2 ≃+
      Picard.ofScheme X ⧸ (nsmulAddMonoidHom n : Picard.ofScheme X →+ Picard.ofScheme X).range :=
  h2RootsOfUnityAddEquivPicardQuotient.{u + 1, u + 1, u} X (by rintro rfl; simp at hn)
    (isUnit_natCast_globalSections X n f hn)
    (Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve f 2 le_rfl)

include f hn in
/-- **Stacks Project, Tag 03RQ, the clause `q ≥ 3`.** Let `X` be a smooth projective curve over
an algebraically closed field `k` and let `n ≥ 1` be invertible in `k`. Then
`H^q_étale(X, μ_n) = 0` for every `q ≥ 3`.

The Kummer sequence places `H^q(X, μ_n)` between `H^{q-1}(X, 𝐆_m)` and `H^q(X, 𝐆_m)`, both zero
by Stacks 03RM since `q - 1 ≥ 2`. Projectivity is not used. -/
@[stacks 03RQ "the clause q >= 3: H^q_etale(X, mu_n) = 0 for every q >= 3",
  sga "4½ Arcata 3.3.5" "partial"]
theorem subsingleton_sheafH_rootsOfUnitySheaf_of_isCurve (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} (rootsOfUnitySheaf.{u, u + 1} X n) q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by lia⟩
  exact subsingleton_sheafH_rootsOfUnitySheaf.{u + 1, u, u + 1} X (by rintro rfl; simp at hn)
    (isUnit_natCast_globalSections X n f hn) p
    (Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve f p (by lia))
    (Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve f (p + 1)
      (by lia))

end Curve

end Stacks.Kummer

end
