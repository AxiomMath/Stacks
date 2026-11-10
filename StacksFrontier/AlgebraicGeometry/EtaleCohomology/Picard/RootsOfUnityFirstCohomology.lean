module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.CohomologySequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The first étale cohomology of the roots of unity is the `n`-torsion of the Picard group

Let `X` be a scheme and `n ≠ 0` invertible on `X`, and suppose that every global unit of `X` is an
`n`-th power. Then the Kummer sequence and the étale identification `H¹(X, 𝐆_m) = Pic(X)` of
[Stacks, Tag 03P8] give `H¹_étale(X, μ_n) ≅ Pic(X)[n]`.

On a smooth projective curve over an algebraically closed field `k` in which `n` is invertible,
the global units are `k^*`, which is `n`-divisible, so `H¹_étale(X, μ_n) ≅ Pic(X)[n]`; since
`Pic(X)/Pic⁰(X) = ℤ` is torsion free, this is `Pic⁰(X)[n]`, the case `q = 1` of
[Stacks, Tag 03RQ].

## Main definitions

* `Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion`: `H¹(X, μ_n) ≃+ Pic(X)[n]`.
* `Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion_of_isCurve`: the same for a smooth
  projective curve over an algebraically closed field, `n` invertible in the field.

## Main results

* `Stacks.Kummer.range_h1RootsOfUnityToPicard`: the image of `H¹(X, μ_n) → Pic(X)` is the
  `n`-torsion.
* `Stacks.Kummer.exists_pow_eq_globalUnit`: on a scheme integral and proper over an algebraically
  closed field, every global unit is an `n`-th power.

## References

* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace Stacks.Kummer

open _root_.AlgebraicGeometry

variable (X : Scheme.{u}) (n : ℕ) (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- The map `H¹(X, μ_n) → Pic(X)` induced by the inclusion `μ_n ⊆ 𝐆_m`, followed by
`H¹(X, 𝐆_m) ≅ Pic(X)`. -/
def h1RootsOfUnityToPicard : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 1 →+ Picard.ofScheme X :=
  (etaleH1MultiplicativeAddEquivPicard.{w, v, u} X).toAddMonoidHom.comp
    (Sheaf.H.map (rootsOfUnityι.{u, v} X n) 1)

include hn0 hX in
/-- The image of `H¹(X, μ_n) → Pic(X)` is the `n`-torsion. -/
@[sga "4 IX 4.7" "partial"]
theorem range_h1RootsOfUnityToPicard :
    (h1RootsOfUnityToPicard.{w, v, u} X n).range =
      AddSubgroup.torsionBy (Picard.ofScheme X) (n : ℤ) := by
  ext y
  rw [AddSubgroup.torsionBy.nsmul_iff]
  set e := etaleH1MultiplicativeAddEquivPicard.{w, v, u} X
  constructor
  · rintro ⟨x, rfl⟩
    change n • e (Sheaf.H.map (rootsOfUnityι.{u, v} X n) 1 x) = 0
    rw [← map_nsmul, ← sheafH_map_powMap X n 1,
      (mem_range_sheafH_map_rootsOfUnityι_iff X hn0 hX 1 _).1 ⟨x, rfl⟩, map_zero]
  · intro hy
    have : Sheaf.H.map (powMap.{u, v} X n) 1 (e.symm y) = 0 := by
      rw [sheafH_map_powMap, ← map_nsmul, hy, map_zero]
    obtain ⟨x, hx⟩ := (mem_range_sheafH_map_rootsOfUnityι_iff X hn0 hX 1 _).2 this
    refine ⟨x, ?_⟩
    simp only [h1RootsOfUnityToPicard, AddMonoidHom.coe_comp, Function.comp_apply, hx]
    exact e.apply_symm_apply y

include hn0 hX in
/-- **`H¹_étale(X, μ_n) ≅ Pic(X)[n]`** when `n` is invertible on `X` and every global unit of `X`
is an `n`-th power. -/
@[sga "4 IX 4.7" "partial"]
def h1RootsOfUnityAddEquivPicardTorsion
    (hsurj : Function.Surjective (Sheaf.H.map.{w} (powMap.{u, v} X n) 0)) :
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 1 ≃+
      AddSubgroup.torsionBy (Picard.ofScheme X) (n : ℤ) :=
  (AddMonoidHom.ofInjective (f := h1RootsOfUnityToPicard.{w, v, u} X n)
      ((etaleH1MultiplicativeAddEquivPicard.{w, v, u} X).injective.comp
        (injective_sheafH_map_rootsOfUnityι_one X hn0 hX hsurj))).trans
    (AddEquiv.addSubgroupCongr (range_h1RootsOfUnityToPicard.{w, v, u} X n hn0 hX))

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- On a scheme integral and proper over an algebraically closed field `k`, every global unit is
an `n`-th power for `n ≥ 1`. -/
theorem exists_pow_eq_globalUnit {k : Type u} [Field k] [IsAlgClosed k]
    (g : X ⟶ Spec (.of k)) [IsProper g] [IsIntegral X] (hn : 0 < n) (a : (Γ(X, ⊤))ˣ) :
    ∃ b : (Γ(X, ⊤))ˣ, b ^ n = a := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have hfin : Module.Finite k Γ(X, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k g
  have hint : Algebra.IsIntegral k Γ(X, ⊤) := Algebra.IsIntegral.of_finite k _
  have hbij : Function.Bijective (algebraMap k Γ(X, ⊤)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨c, hc⟩ := hbij.2 (a : Γ(X, ⊤))
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hd
    have : Nontrivial Γ(X, ⊤) := hbij.injective.nontrivial
    exact a.ne_zero (by rw [← hc, ← hd, map_zero])
  refine ⟨(IsUnit.map (algebraMap k Γ(X, ⊤)) (Ne.isUnit hd0)).unit, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow, hd, hc]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- If `n` is invertible in a field `k` over which `X` lies, it is invertible on `X`. -/
theorem isUnit_natCast_globalSections {k : Type u} [Field k] (g : X ⟶ Spec (.of k))
    (hn : IsUnit (n : k)) : IsUnit ((n : ℕ) : Γ(X, ⊤)) := by
  have := hn.map ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom
  rwa [map_natCast] at this

/-- **`H¹_étale(X, μ_n) ≅ Pic(X)[n]` for a smooth projective curve over an algebraically closed
field and `n` invertible in the field.** -/
@[sga "4 IX 4.7" "special case"]
def h1RootsOfUnityAddEquivPicardTorsion_of_isCurve {k : Type u} [Field k] [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProjectiveVariety k f]
    (hn : IsUnit (n : k)) :
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 1 ≃+
      AddSubgroup.torsionBy (Picard.ofScheme X) (n : ℤ) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have : IsProper f := inferInstance
  have : IsIntegral X := inferInstance
  exact h1RootsOfUnityAddEquivPicardTorsion.{w, v, u} X n hn0
    (isUnit_natCast_globalSections X n f hn)
    (surjective_sheafH_map_powMap_zero X (n := n)
      (exists_pow_eq_globalUnit X n f (Nat.pos_of_ne_zero hn0)))

end Stacks.Kummer
