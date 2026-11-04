module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicGermInjective
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MultiplierAgreement

/-!
# A ratio of meromorphic functions which is a unit at every point is a global unit

The descent datum of [Stacks, Tag 0BD7] asks for a transition unit `w ∈ Γ(Y, A')^*` on the
intersection of two charts, while the uniqueness sentence of the penultimate paragraph produces
only a unit on a neighbourhood of a single point. This file closes that gap for two meromorphic
functions on an integral base: a factor relating them which is a unit in every local ring of
`A'` is the restriction of a single unit of `Γ(Y, A')`.

Both halves are consequences of `AlgebraicGeometry.injective_totalQuotientSheaf_germ`: on an
integral scheme a meromorphic function is determined by one of its germs, so the locally chosen
factors are forced to agree on overlaps and glue, and the glued section is a unit because each
of its germs is.

## Main results

* `Stacks.InvertiblePullback.exists_units_mul_eq_of_forall_isUnit_germ`: the statement for the
  sheaf `𝒦_Y` of total quotient rings, with the factor acting by multiplication.
* `Stacks.InvertiblePullback.exists_units_eq_smul_of_forall_isUnit_germ`: the same for
  `AlgebraicGeometry.totalQuotientSheafAsModule`, with the factor acting as a scalar — the
  spelling in which the multipliers of the tag are carried.

## Implementation notes

The degenerate case is real and is dealt with first: if `b = 0` the factor is not determined by
anything, but then `a = 0` as well and `1` serves. Away from it the germ of `b` at every point
of `A'` is nonzero, the stalk of `𝒦_Y` is a field, and the factor is a quotient.

The two sheaf-theoretic inputs — the gluing of the local factors and the two local-to-global
identities — are taken once, at the top, in the `Y.presheaf` and
`Y.totalQuotientSheaf.presheaf` spellings; the `TopCat.Sheaf` statements are about
`Y.sheaf.obj` and `Y.sheaf.presheaf`, which are definitionally but not syntactically those, and
a rewrite crossing the two spellings fails to find its own pattern.

The `𝒪_Y(A')`-action on `𝒦_Y(A')` is multiplication by the image of the scalar, by `rfl`, but
neither spelling of an element finds the other's instance; the two statements below are
therefore the same theorem twice, the second deduced from the first by that definitional
equality alone.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Meromorphic

universe u

namespace Stacks.InvertiblePullback

variable {Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral Y]

/-- The map `Γ(Z, U) → 𝒦_Z(U)` commutes with restriction. -/
private theorem toTotalQuotientSheaf_app_map {Z : Scheme.{u}} {U V : Z.Opens} (h : V ≤ U)
    (w : Γ(Z, U)) :
    (Z.toTotalQuotientSheaf.hom.app (op V)).hom (Z.presheaf.map (homOfLE h).op w)
      = Z.totalQuotientSheaf.presheaf.map (homOfLE h).op
          ((Z.toTotalQuotientSheaf.hom.app (op U)).hom w) :=
  ConcreteCategory.congr_hom (Z.toTotalQuotientSheaf.hom.naturality (homOfLE h).op) w

/-- **A locally invertible ratio of two meromorphic functions is globally invertible.** If `a`
and `b` are meromorphic on `A'` and every point of `A'` has a neighbourhood on which `a` is a
regular multiple of `b` by a factor invertible at that point, then `a = w b` for a single unit
`w` of `Γ(Y, A')`. -/
theorem exists_units_mul_eq_of_forall_isUnit_germ {A' : Y.Opens}
    (a b : Y.totalQuotientSheaf.presheaf.obj (op A'))
    (hloc : ∀ y ∈ A',
      ∃ (B : Y.Opens) (hyB : y ∈ B) (hBA : B ≤ A') (w : Γ(Y, B)),
        IsUnit (Y.presheaf.germ B y hyB w) ∧
          Y.totalQuotientSheaf.presheaf.map (homOfLE hBA).op a
            = (Y.toTotalQuotientSheaf.hom.app (op B)).hom w *
              Y.totalQuotientSheaf.presheaf.map (homOfLE hBA).op b) :
    ∃ w : (Γ(Y, A'))ˣ,
      a = (Y.toTotalQuotientSheaf.hom.app (op A')).hom w.val * b := by
  classical
  choose B hyB hBA w hwu hwe using hloc
  have hcover : A' ≤ ⨆ i : {y : Y // y ∈ A'}, B i.1 i.2 :=
    fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyB y hy⟩
  have hKext : ∀ p q : Y.totalQuotientSheaf.presheaf.obj (op A'),
      (∀ (y : Y) (hy : y ∈ A'),
        Y.totalQuotientSheaf.presheaf.map (homOfLE (hBA y hy)).op p
          = Y.totalQuotientSheaf.presheaf.map (homOfLE (hBA y hy)).op q) → p = q :=
    fun p q h => TopCat.Sheaf.eq_of_locally_eq' Y.totalQuotientSheaf
      (fun i : {y : Y // y ∈ A'} => B i.1 i.2) A' (fun i => homOfLE (hBA i.1 i.2)) hcover p q
      fun i => h i.1 i.2
  have hOext : ∀ (U : Y.Opens) (p q : Γ(Y, U)),
      (∀ (v : Y) (hv : v ∈ U), Y.presheaf.germ U v hv p = Y.presheaf.germ U v hv q) → p = q :=
    fun U p q h => TopCat.Presheaf.section_ext Y.sheaf U p q h
  by_cases hb : b = 0
  · subst hb
    exact ⟨1, by rw [mul_zero]; exact hKext a 0 fun y hy => by rw [hwe y hy, map_zero, mul_zero]⟩
  have hkappa : ∀ (U : Y.Opens) (v : Y) (hv : v ∈ U) (r : Γ(Y, U)),
      Y.totalQuotientSheaf.presheaf.germ U v hv
          ((Y.toTotalQuotientSheaf.hom.app (op U)).hom r)
        = toTotalQuotientStalk Y v (Y.presheaf.germ U v hv r) :=
    fun U v hv r =>
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U v hv Y.toTotalQuotientSheaf.hom r).symm
  have hgerm : ∀ (y : Y) (hy : y ∈ A') (v : Y) (hv : v ∈ B y hy),
      Y.totalQuotientSheaf.presheaf.germ A' v (hBA y hy hv) a
        = toTotalQuotientStalk Y v (Y.presheaf.germ (B y hy) v hv (w y hy)) *
          Y.totalQuotientSheaf.presheaf.germ A' v (hBA y hy hv) b := by
    intro y hy v hv
    have h1 := congrArg
      (ConcreteCategory.hom (Y.totalQuotientSheaf.presheaf.germ (B y hy) v hv)) (hwe y hy)
    rwa [TopCat.Presheaf.germ_res_apply _ (homOfLE (hBA y hy)) v hv a, map_mul, hkappa,
      TopCat.Presheaf.germ_res_apply _ (homOfLE (hBA y hy)) v hv b] at h1
  have hbne : ∀ (v : Y) (hv : v ∈ A'),
      Y.totalQuotientSheaf.presheaf.germ A' v hv b ≠ 0 := fun v hv h0 =>
    hb (injective_totalQuotientSheaf_germ Y A' v hv (h0.trans (map_zero _).symm))
  have hcompat : TopCat.Presheaf.IsCompatible Y.presheaf
      (fun i : {y : Y // y ∈ A'} => B i.1 i.2) (fun i => w i.1 i.2) := by
    intro i j
    refine hOext (B i.1 i.2 ⊓ B j.1 j.2) _ _ fun v hv => ?_
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    refine toTotalQuotientStalk_injective Y v ?_
    let : Algebra ↑(Y.presheaf.stalk v) ↑(Y.totalQuotientSheaf.presheaf.stalk v) :=
      (toTotalQuotientStalk Y v).toAlgebra
    have := isFractionRing_stalk_totalQuotientSheaf Y v
    let : Field ↑(Y.totalQuotientSheaf.presheaf.stalk v) :=
      IsFractionRing.toField ↑(Y.presheaf.stalk v)
    exact mul_right_cancel₀ (hbne v (hBA i.1 i.2 hv.1))
      ((hgerm i.1 i.2 v hv.1).symm.trans (hgerm j.1 j.2 v hv.2))
  obtain ⟨wg, hwg⟩ : ∃ wg : Γ(Y, A'), ∀ (y : Y) (hy : y ∈ A'),
      Y.presheaf.map (homOfLE (hBA y hy)).op wg = w y hy := by
    obtain ⟨wg, hwg, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf
      (fun i : {y : Y // y ∈ A'} => B i.1 i.2) A' (fun i => homOfLE (hBA i.1 i.2)) hcover
      (fun i => w i.1 i.2) hcompat
    exact ⟨wg, fun y hy => hwg ⟨y, hy⟩⟩
  have hunit : IsUnit wg := by
    refine RingedSpace.isUnit_of_isUnit_germ Y.toRingedSpace A' wg fun v hv => ?_
    have h := TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (hBA v hv)) v (hyB v hv) wg
    rw [hwg v hv] at h
    exact h ▸ hwu v hv
  refine ⟨hunit.unit, hKext a _ fun y hy => ?_⟩
  rw [hwe y hy, map_mul, hunit.unit_spec, ← toTotalQuotientSheaf_app_map (hBA y hy) wg,
    hwg y hy]

/-- **The transition unit of [Stacks, Tag 0BD7] on an intersection of two charts.** The scalar
form of `Stacks.InvertiblePullback.exists_units_mul_eq_of_forall_isUnit_germ`: two meromorphic
multipliers related at every point of `A'` by a factor which is a unit there are related on all
of `A'` by one unit of `Γ(Y, A')`. -/
theorem exists_units_eq_smul_of_forall_isUnit_germ {A' : Y.Opens}
    (a b : (totalQuotientSheafAsModule Y).val.obj (op A'))
    (hloc : ∀ y ∈ A',
      ∃ (B : Y.Opens) (hyB : y ∈ B) (hBA : B ≤ A') (w : Γ(Y, B)),
        IsUnit (Y.presheaf.germ B y hyB w) ∧
          (totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hBA).op a
            = HSMul.hSMul
                (α := (Stacks.Sheaves.Differentials.ringSheaf
                  (J := Opens.grothendieckTopology Y) Y.sheaf).obj.obj (op B)) w
                ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hBA).op b)) :
    ∃ w : (Γ(Y, A'))ˣ,
      a = HSMul.hSMul
            (α := (Stacks.Sheaves.Differentials.ringSheaf
              (J := Opens.grothendieckTopology Y) Y.sheaf).obj.obj (op A')) w.val b :=
  exists_units_mul_eq_of_forall_isUnit_germ (Y := Y) (A' := A') a b hloc

/-- **The transition unit of [Stacks, Tag 0BD7], on an open over which both members of the
family generate.** On such an open the uniqueness sentence applies at every point, so the
locally chosen units glue to one unit of `Γ(Y, A')` relating the two multipliers there. This is
the hypothesis `hunit` of the descent, discharged. -/
theorem exists_units_restrictₛₗ_eq_smul_of_forall_mem_generatingLocus {X : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [AlgebraicGeometry.IsIntegral X]
    (L : _root_.SheafOfModules.{u} (_root_.structureSheafRing X.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (_root_.structureSheafRing X.toRingedSpace).property L]
    (s : MeromorphicSection X.sheaf L) {ι : Type*} {A : ι → Y.Opens}
    (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
    (t : ∀ i, L.val.obj (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier)))
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsPullMeromorphicFamily f L s g t)
    (i j : ι) {A' : Y.Opens} (hi : A' ≤ A i) (hj : A' ≤ A j)
    (hgen : ∀ y : Y, y ∈ A' → ∃ x : X, f.base x = y ∧
      x ∈ Stacks.SheafOfModules.generatingLocus L (t i) ∧
      x ∈ Stacks.SheafOfModules.generatingLocus L (t j)) :
    ∃ w : (Γ(Y, A'))ˣ,
      (totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hi).op (g i)
        = HSMul.hSMul
            (α := (Stacks.Sheaves.Differentials.ringSheaf
              (J := Opens.grothendieckTopology Y) Y.sheaf).obj.obj (op A')) w.val
            ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hj).op (g j)) := by
  have hcomp : ∀ {U V Z : Y.Opens} (h1 : V ≤ U) (h2 : Z ≤ V)
      (z : Y.totalQuotientSheaf.presheaf.obj (op U)),
      Y.totalQuotientSheaf.presheaf.map (homOfLE h2).op
          (Y.totalQuotientSheaf.presheaf.map (homOfLE h1).op z)
        = Y.totalQuotientSheaf.presheaf.map (homOfLE (h2.trans h1)).op z := by
    intro U V Z h1 h2 z
    rw [← ConcreteCategory.comp_apply, ← Y.totalQuotientSheaf.presheaf.map_comp,
      show (homOfLE h1).op ≫ (homOfLE h2).op = (homOfLE (h2.trans h1)).op from
        Subsingleton.elim _ _]
  refine exists_units_eq_smul_of_forall_isUnit_germ
    ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hi).op (g i))
    ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hj).op (g j)) fun y hy => ?_
  obtain ⟨x, hx, hxi, hxj⟩ := hgen y hy
  subst hx
  obtain ⟨C, hxC, hCi, hCj, w, hwu, hw⟩ :=
    exists_isUnit_germ_restrictₛₗ_eq_smul_of_isPullMeromorphicFamily f L s g t hs ht i j x hxi hxj
  have hwm : Y.totalQuotientSheaf.presheaf.map (homOfLE hCi).op (g i)
      = (Y.toTotalQuotientSheaf.hom.app (op C)).hom w *
        Y.totalQuotientSheaf.presheaf.map (homOfLE hCj).op (g j) := hw
  have hCA : C ⊓ A' ≤ C := inf_le_left
  refine ⟨C ⊓ A', ⟨hxC, hy⟩, inf_le_right, Y.presheaf.map (homOfLE hCA).op w, ?_, ?_⟩
  · rw [TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hCA) (f.base x) ⟨hxC, hy⟩ w]
    exact hwu
  · have key : Y.totalQuotientSheaf.presheaf.map (homOfLE (inf_le_right : C ⊓ A' ≤ A')).op
          (Y.totalQuotientSheaf.presheaf.map (homOfLE hi).op (g i))
        = (Y.toTotalQuotientSheaf.hom.app (op (C ⊓ A'))).hom
              (Y.presheaf.map (homOfLE hCA).op w) *
          Y.totalQuotientSheaf.presheaf.map (homOfLE (inf_le_right : C ⊓ A' ≤ A')).op
            (Y.totalQuotientSheaf.presheaf.map (homOfLE hj).op (g j)) := by
      rw [toTotalQuotientSheaf_app_map hCA w, hcomp hi inf_le_right (g i),
        hcomp hj inf_le_right (g j), ← hcomp hCi hCA (g i), ← hcomp hCj hCA (g j), hwm, map_mul]
    exact key

end Stacks.InvertiblePullback

end
