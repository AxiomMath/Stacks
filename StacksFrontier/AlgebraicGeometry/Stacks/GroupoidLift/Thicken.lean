module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Cech
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.ModBaseChange

/-!
# Thickenings along a square-zero ideal of the base

Let `I ⊆ A'` be an ideal with `I ^ 2 = 0`. Every `A'`-algebra `N` is thickened over `N ⧸ I N`;
this is `AlgebraicGeometry.Stack.GroupoidLift.thk`, and algebra maps give maps of thickenings
(`thkHom`). For an `A'`-algebra `F`, the inclusion `x ↦ x ⊗ 1 : N → N ⊗[A'] F` is a base change
of thickenings (`isBaseChange_includeLeft`).

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.red`: the reduction `N ⧸ I N`.
* `AlgebraicGeometry.Stack.GroupoidLift.thk`: the square-zero thickening `N → N ⧸ I N`.
* `AlgebraicGeometry.Stack.GroupoidLift.thkHom`: the map of thickenings induced by an algebra map.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.isBaseChange_includeLeft`: the thickening of
  `N ⊗[A'] F` is the base change of the thickening of `N`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} (I : Ideal A') (hI : I ^ 2 = ⊥)

/-- The reduction `N ⧸ I N` of a small algebra. -/
abbrev red (N : SmallAlg A' κ) : SmallAlg A' κ :=
  SmallAlg.mk (N.obj ⧸ I.map (algebraMap A' N.obj))
    ((Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans_lt N.property)

include hI in
/-- **The thickening `N → N ⧸ I N`.** -/
def thk (N : SmallAlg A' κ) : SqZero N (red I N) where
  q := SmallAlg.homMk (Ideal.Quotient.mkₐ A' (I.map (algebraMap A' N.obj)))
  surj := Ideal.Quotient.mk_surjective
  sq := by
    change (RingHom.ker (Ideal.Quotient.mk (I.map (algebraMap A' N.obj)))) ^ 2 = ⊥
    rw [Ideal.mk_ker, ← Ideal.map_pow, hI, Ideal.map_bot]

/-- The map of the thickening `thk I hI N` sends `x` to its class in `N ⧸ I N`. -/
theorem thk_q_apply (N : SmallAlg A' κ) (x : N.obj) :
    (thk I hI N).q.hom.hom x = Ideal.Quotient.mk _ x := rfl

/-- The kernel of the thickening `thk I hI N` is the extension `I N` of `I`. -/
theorem ker_thk (N : SmallAlg A' κ) :
    RingHom.ker ((thk I hI N).q.hom.hom : N.obj →+* (red I N).obj) =
      I.map (algebraMap A' N.obj) :=
  Ideal.mk_ker

/-- The reduction of an algebra map. -/
def redMap {N N' : SmallAlg A' κ} (f : N.obj →ₐ[A'] N'.obj) : (red I N).obj →ₐ[A'] (red I N').obj :=
  Ideal.quotientMapₐ _ f (by
    rw [← Ideal.map_le_iff_le_comap]
    change Ideal.map (f : N.obj →+* N'.obj) (Ideal.map (algebraMap A' N.obj) I) ≤ _
    rw [Ideal.map_map, show (f : N.obj →+* N'.obj).comp (algebraMap A' N.obj) =
      algebraMap A' N'.obj from f.comp_algebraMap])

/-- `redMap I f` sends the class of `x` to the class of `f x`. -/
theorem redMap_mk {N N' : SmallAlg A' κ} (f : N.obj →ₐ[A'] N'.obj) (x : N.obj) :
    redMap I f (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x) := rfl

/-- **The map of thickenings induced by an algebra map.** -/
def thkHom {N N' : SmallAlg A' κ} (f : N.obj →ₐ[A'] N'.obj) :
    SqZero.Hom (thk I hI N) (thk I hI N') where
  top := SmallAlg.homMk f
  bot := SmallAlg.homMk (redMap I f)
  w := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext x
    rfl

/-- The top map of `thkHom I hI f` is `f`. -/
@[simp] theorem thkHom_top {N N' : SmallAlg A' κ} (f : N.obj →ₐ[A'] N'.obj) :
    (thkHom I hI f).top.hom.hom = f := rfl

/-- The bottom map of `thkHom I hI f` is `redMap I f`. -/
@[simp] theorem thkHom_bot {N N' : SmallAlg A' κ} (f : N.obj →ₐ[A'] N'.obj) :
    (thkHom I hI f).bot.hom.hom = redMap I f := rfl

/-- The reduction of a composite is the composite of the reductions. -/
theorem redMap_comp {N N' N'' : SmallAlg A' κ} (f : N.obj →ₐ[A'] N'.obj)
    (g : N'.obj →ₐ[A'] N''.obj) :
    (redMap I (N := N') (N' := N'') g).comp (redMap I f) = redMap I (N' := N'') (g.comp f) := by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The reduction of the identity is the identity. -/
theorem redMap_id (N : SmallAlg A' κ) :
    redMap I (N := N) (N' := N) (AlgHom.id A' _) = AlgHom.id A' _ := by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-! ### The base change -/

variable {F : Type u} [CommRing F] [Algebra A' F]

/-- The thickening of `N ⊗[A'] F` is the base change of the thickening of `N`. -/
theorem isBaseChange_includeLeft (N : SmallAlg A' κ) (hY : Cardinal.mk (N.obj ⊗[A'] F) < κ) :
    IsBaseChange (thk I hI N) F (thk I hI (SmallAlg.mk (N.obj ⊗[A'] F) hY))
      (thkHom I hI (N' := SmallAlg.mk (N.obj ⊗[A'] F) hY)
        (Algebra.TensorProduct.includeLeft (S := A'))) where
  ker_eq := by
    rw [ker_thk, ker_thk, extIdeal]
    show _ = Ideal.map ((Algebra.TensorProduct.includeLeft (S := A') :
      N.obj →ₐ[A'] N.obj ⊗[A'] F) : N.obj →+* N.obj ⊗[A'] F) (Ideal.map (algebraMap A' N.obj) I)
    rw [Ideal.map_map]
    congr 1
  top_apply _ := rfl

end AlgebraicGeometry.Stack.GroupoidLift

end
