module

public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationDescent
public import StacksFrontier.AlgebraicGeometry.DifferentialsAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSquareZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vector fields on an affine scheme over a field are derivations of its coordinate ring

Let `Y` be an affine scheme over a field `k`. This file proves that a vector field on `Y` in the
sense of Section 53.26 is the same thing as a `k`-derivation of the coordinate ring `Γ(Y, ⊤)`.

## Main results

* `Stacks.Curves.existsUnique_sheafDerivationOf_of_isAffine` — **a Leibniz additive map on the
  coordinate ring of an affine `k`-scheme which kills the image of `k` is the value on the global
  sections of a unique vector field.**

## References

* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 01UO](https://stacks.math.columbia.edu/tag/01UO)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- `Spec` of a field is a one-point space, so it has exactly two opens. -/
theorem opens_eq_bot_or_eq_top (V : (Spec (.of k)).Opens) : V = ⊥ ∨ V = ⊤ := by
  have : Subsingleton ↥(Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rcases (V : Set ↥(Spec (.of k))).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl (TopologicalSpace.Opens.ext h)
  · exact Or.inr (TopologicalSpace.Opens.ext
      (Set.eq_univ_of_forall fun y ↦ Subsingleton.elim y x ▸ hx))

variable {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))

/-- **A compatible Leibniz family of additive maps on the structure sheaf which kills the base is
a vector field.** The `Stacks.Curves.SheafDerivationOf g` given by a family of additive maps
`e W : Γ(Y, W) → Γ(Y, W)`, one for every open `W` of `Y`, which obey the Leibniz rule, commute
with restriction and annihilate the image of `Γ(Spec k, V)` in `Γ(Y, g⁻¹ V)` for every open `V`.
-/
noncomputable def sheafDerivationOfFamily
    (e : (W : Y.Opens) → Γ(Y, W) →+ Γ(Y, W))
    (hmul : ∀ (W : Y.Opens) (x y : Γ(Y, W)), e W (x * y) = x * e W y + y * e W x)
    (hmap : ∀ {W W' : Y.Opens} (h : W' ≤ W) (x : Γ(Y, W)),
      (Y.presheaf.map (homOfLE h).op).hom (e W x)
        = e W' ((Y.presheaf.map (homOfLE h).op).hom x))
    (hbase : ∀ (V : (Spec (.of k)).Opens) (r : Γ(Spec (.of k), V)),
      e (g ⁻¹ᵁ V) ((g.app V).hom r) = 0) :
    SheafDerivationOf g where
  d {W} := e W.unop
  d_mul {W} a b := hmul W.unop a b
  d_map {_ _} h x := (hmap h.unop.le x).symm
  d_app {W} a :=
    Stacks.Smooth.apply_inverseImageStructureApp_eq_zero g
      (SheafOfModules.unit Y.ringCatSheaf) e (fun W x y ↦ hmul W x y)
      (fun h x ↦ hmap h.unop.le x) hbase W a

/-- The vector field `sheafDerivationOfFamily g e hmul hmap hbase` acts on the sections over an
open `W` of `Y` as `e W`. -/
@[simp] theorem sheafDerivationOfFamily_onSections
    (e : (W : Y.Opens) → Γ(Y, W) →+ Γ(Y, W))
    (hmul : ∀ (W : Y.Opens) (x y : Γ(Y, W)), e W (x * y) = x * e W y + y * e W x)
    (hmap : ∀ {W W' : Y.Opens} (h : W' ≤ W) (x : Γ(Y, W)),
      (Y.presheaf.map (homOfLE h).op).hom (e W x)
        = e W' ((Y.presheaf.map (homOfLE h).op).hom x))
    (hbase : ∀ (V : (Spec (.of k)).Opens) (r : Γ(Spec (.of k), V)),
      e (g ⁻¹ᵁ V) ((g.app V).hom r) = 0)
    {W : Y.Opens} (s : Γ(Y, W)) :
    (sheafDerivationOfFamily g e hmul hmap hbase).onSections s = e W s :=
  rfl

/-- **A `k`-derivation of the coordinate ring of an affine `k`-scheme is a vector field.** For `Y`
an affine scheme over a field `k`, an additive map `Γ(Y, ⊤) → Γ(Y, ⊤)` obeying the Leibniz rule
and annihilating the image of `Γ(Spec k, ⊤)` is the value on the global sections of exactly one
vector field on `Y`. -/
@[ega "IV 16.5.2" "special case"]
theorem existsUnique_sheafDerivationOf_of_isAffine [IsAffine Y]
    (D : Γ(Y, ⊤) →+ Γ(Y, ⊤))
    (hmul : ∀ a b : Γ(Y, ⊤), D (a * b) = a * D b + b * D a)
    (hbase : ∀ r : Γ(Spec (.of k), ⊤), D ((g.app ⊤).hom r) = 0) :
    ∃! D' : SheafDerivationOf g, ∀ s : Γ(Y, ⊤), D'.onSections s = D s := by
  obtain ⟨e, hmulE, hresE, htopE⟩ :
      ∃ e : (W : Y.Opens) → Γ(Y, W) →+ Γ(Y, W),
        (∀ (W : Y.Opens) (x y : Γ(Y, W)), e W (x * y) = x * e W y + y * e W x) ∧
        (∀ (W W' : Y.Opens) (h : W' ≤ W) (x : Γ(Y, W)),
          (Y.presheaf.map (homOfLE h).op).hom (e W x)
            = e W' ((Y.presheaf.map (homOfLE h).op).hom x)) ∧
        e ⊤ = D := by
    obtain ⟨t, htmul, htres, httop⟩ :=
      Stacks.AlgebraicGeometry.DifferentialsAffine.exists_restrictions
        (M := SheafOfModules.unit Y.ringCatSheaf) (isAffineOpen_top Y) D hmul
    exact ⟨fun W ↦ t W le_top, fun W x y ↦ htmul W le_top x y,
      fun W W' h x ↦ (htres W W' le_top h x).symm, httop⟩
  have hbase' : ∀ (V : (Spec (.of k)).Opens) (r : Γ(Spec (.of k), V)),
      e (g ⁻¹ᵁ V) ((g.app V).hom r) = 0 := by
    intro V r
    rcases opens_eq_bot_or_eq_top V with rfl | rfl
    · refine TopCat.Presheaf.IsSheaf.section_ext
        (SheafOfModules.unit Y.ringCatSheaf).isSheaf ?_
      intro p hp
      exact absurd hp (by simp)
    · have h := hbase r
      rw [← htopE] at h
      exact h
  refine ⟨sheafDerivationOfFamily g e hmulE (fun {_ _} h x ↦ hresE _ _ h x) hbase',
    fun s ↦ DFunLike.congr_fun htopE s, fun D' hD' ↦ ?_⟩
  refine SheafDerivationOf.ext' fun W s ↦ ?_
  have key := Stacks.AlgebraicGeometry.DifferentialsAffine.eq_of_eq_on_affineOpen
    (M := SheafOfModules.unit Y.ringCatSheaf) (isAffineOpen_top Y)
    (fun W _ ↦ D'.d (X := op W)) (fun W _ ↦ e W)
    (fun W _ a b ↦ D'.d_mul (X := op W) a b) (fun W _ a b ↦ hmulE W a b)
    (fun W W' _ h a ↦ D'.d_map (X := op W) (Y := op W') (homOfLE h).op a)
    (fun W W' _ h a ↦ (hresE W W' h a).symm)
    (AddMonoidHom.ext fun s ↦ (hD' s).trans (DFunLike.congr_fun htopE s).symm)
  exact DFunLike.congr_fun (congrFun (congrFun key W) le_top) s

end Stacks.Curves

end
