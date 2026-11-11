module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologySequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology

/-!
# Vanishing of cohomology over an object from a short exact sequence

Let `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` be a short exact sequence of abelian sheaves on a site and `T` an
object of the site. If `H^q(T, ℱ₂)` and `H^q(T, ℱ₃)` vanish for every `q > 0` and the map of
sections `ℱ₂(T) → ℱ₃(T)` is surjective, then `H^q(T, ℱ₁)` vanishes for every `q > 0`. This is
the long exact cohomology sequence, [Stacks, Tag 0159], read at `T`: in degree `q ≥ 2` the group
`H^q(T, ℱ₁)` sits between `H^{q-1}(T, ℱ₃) = 0` and `H^q(T, ℱ₂) = 0`, and in degree `1` the
connecting map out of `H^0(T, ℱ₃)` vanishes because `H^0(T, ℱ₂) → H^0(T, ℱ₃)` is the
surjective map of sections.

A finite product of copies of an object killed by an additive functor is killed by it as well;
this is how the vanishing passes from `ℱ₁` to `ℱ₁ⁿ`.

## Main results

* `Stacks.Cohomology.LongExactSequence.surjective_map_zero`: in degree zero the map of
  cohomology over `T` induced by a morphism of sheaves surjective on sections over `T` is
  surjective.
* `Stacks.Cohomology.LongExactSequence.isZero_H'_X₁_of_shortExact`: the vanishing above.
* `CategoryTheory.Functor.isZero_obj_of_isLimit_fan`: an additive functor killing `F` kills
  every finite product of copies of `F`.

## References

* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w v u

namespace Stacks.Cohomology.LongExactSequence

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- **In degree zero, a morphism surjective on sections over `T` is surjective on cohomology
over `T`.** A class of `H^0(T, 𝒢)` is a morphism out of the free abelian sheaf on `T`, that is a
section of `𝒢` over `T`; lifting the section lifts the class. -/
theorem surjective_map_zero {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) (T : C)
    (h : Function.Surjective (φ.hom.app (op T))) :
    Function.Surjective (map.{w} φ 0 T) := by
  intro x
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  let e := Stacks.Cohomology.BiggerSite.freeYonedaSheafHomEquiv J T
  obtain ⟨t, ht⟩ := h (e G f)
  let g : freeYoneda J T ⟶ F := (e F).symm t
  have hg : g ≫ φ = f := (e G).injective
    ((Stacks.Cohomology.BiggerSite.freeYonedaSheafHomEquiv_comp J T ((e F).symm t) φ).trans
      ((congrArg (φ.hom.app (op T)) ((e F).apply_symm_apply t)).trans ht))
  refine ⟨Ext.mk₀ g, ?_⟩
  change (Ext.mk₀ g).comp (Ext.mk₀ φ) (add_zero 0) = Ext.mk₀ f
  rw [Ext.mk₀_comp_mk₀, hg]

/-- **The kernel of a short exact sequence inherits the vanishing of positive-degree cohomology
over `T`** from the two other terms, as soon as the map of sections over `T` onto the third term
is surjective. This is the long exact cohomology sequence, [Stacks, Tag 0159], at `T`. -/
theorem isZero_H'_X₁_of_shortExact (S : ShortComplex (Sheaf J AddCommGrpCat.{v}))
    (hS : S.ShortExact) (T : C)
    (h₂ : ∀ q, 0 < q → IsZero (Sheaf.H'.{w} S.X₂ q T))
    (h₃ : ∀ q, 0 < q → IsZero (Sheaf.H'.{w} S.X₃ q T))
    (h₀ : Function.Surjective (S.g.hom.app (op T))) (q : ℕ) (hq : 0 < q) :
    IsZero (Sheaf.H'.{w} S.X₁ q T) := by
  have hsub : Subsingleton (Sheaf.H'.{w} S.X₁ q T) := by
    constructor
    suffices h : ∀ x : Sheaf.H'.{w} S.X₁ q T, x = 0 from fun a b => by rw [h a, h b]
    intro x
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    have hx : map.{w} S.f (p + 1) T x = 0 :=
      (AddCommGrpCat.subsingleton_of_isZero (h₂ _ hq)).elim _ _
    obtain ⟨y, rfl⟩ := (exact_δ_map S hS p (p + 1) rfl T x).1 hx
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · obtain ⟨y', rfl⟩ := surjective_map_zero S.g T h₀ y
      exact (exact_map_δ S hS 0 1 rfl T (map S.g 0 T y')).2 ⟨y', rfl⟩
    · rw [(AddCommGrpCat.subsingleton_of_isZero (h₃ p hp)).elim y 0, map_zero]
  exact AddCommGrpCat.isZero_of_subsingleton _

end Stacks.Cohomology.LongExactSequence

namespace CategoryTheory.Functor

/-- **An additive functor killing `F` kills every finite product of copies of `F`.** A limit fan
over `Fin n` of copies of `F` is a biproduct, whose identity is the sum of the composites through
the copies of `F`; the functor sends each of them through the zero object `E F`. -/
theorem isZero_obj_of_isLimit_fan {A D : Type*} [Category A] [Preadditive A]
    [HasFiniteProducts A] [Category D] [Preadditive D] (E : A ⥤ D) [E.Additive]
    {F P : A} {n : ℕ} (π : Fin n → (P ⟶ F)) (hP : IsLimit (Fan.mk P π))
    (hF : IsZero (E.obj F)) : IsZero (E.obj P) := by
  have : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  let e : P ≅ ⨁ (fun _ : Fin n => F) := hP.conePointUniqueUpToIso (biproduct.isLimit _)
  refine IsZero.of_iso ?_ (E.mapIso e)
  rw [IsZero.iff_id_eq_zero, ← E.map_id, ← biproduct.total, E.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h0 : E.map (biproduct.π (fun _ : Fin n => F) j) = 0 := hF.eq_of_tgt _ _
  rw [E.map_comp, h0, zero_comp]

end CategoryTheory.Functor

end
