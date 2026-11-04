module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ProductOfPuncturedSchemes
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdUnderlying
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# The finite fibre power over the base as an object of the big fppf site

The `n`-fold product over a base `S` of objects of the big fppf site over `S` is again an object
of that site: its underlying scheme is the product `Stacks.Chow.overProd` taken in `Over S`,
which is an iterated fibre product and so satisfies the site's size cutoff.

## Main definitions

* `Stacks.Chow.overProdLift`: a morphism over the base into the finite product over the base,
  given by its components.
* `AlgebraicGeometry.Space.overProdObj`: the finite fibre power over the base as an object of
  the big fppf category over `S`, with its projections `AlgebraicGeometry.Space.overProdObjπ`
  and the lift `AlgebraicGeometry.Space.overProdObjLift` of a family of morphisms of the site.

## Main results

* `AlgebraicGeometry.Scheme.size_overProd_lt`: the finite product over the base of schemes
  satisfying a size cutoff satisfies it again.
* `AlgebraicGeometry.Space.overProdObj_toScheme` and
  `AlgebraicGeometry.Space.overProdObj_hom`: the underlying scheme of
  `AlgebraicGeometry.Space.overProdObj` and its structure morphism are those of
  `Stacks.Chow.overProd`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow

variable {S : Scheme.{u}}

/-- The empty product over the base is the base. -/
def overProdFinZeroIso {Y : Fin 0 → Scheme.{u}} (g : ∀ i, Y i ⟶ S) :
    (overProd g).left ≅ S := by
  refine (Over.forget S).mapIso ((limit.isLimit _).conePointUniqueUpToIso
    (?_ : IsLimit (Fan.mk (f := fun i ↦ Over.mk (g i)) (Over.mk (𝟙 S)) fun i ↦ Fin.elim0 i)))
  exact
    { lift := fun t ↦ Over.homMk t.pt.hom
      fac := fun _ i ↦ Fin.elim0 i.as
      uniq := fun _ m _ ↦ by
        ext
        exact (Category.comp_id m.left).symm.trans m.w }

/-- A product over the base of `n + 1` factors is the fibre product of the first factor with
the product of the remaining `n`. -/
def overProdFinSuccIso {n : ℕ} {Y : Fin (n + 1) → Scheme.{u}} (g : ∀ i, Y i ⟶ S) :
    (overProd g).left ≅ pullback (g 0) (overProd fun i : Fin n ↦ g i.succ).hom :=
  (Over.forget S).mapIso
      ((limit.isLimit _).conePointUniqueUpToIso
        (extendFanIsLimit (fun i ↦ Over.mk (g i)) (limit.isLimit _)
          (prodIsProd (Over.mk (g 0)) (overProd fun i : Fin n ↦ g i.succ)))) ≪≫
    OverProducts.prodLeftIso (Over.mk (g 0)) (overProd fun i : Fin n ↦ g i.succ)

/-- A morphism over the base into a finite product over the base, given by its components. -/
def overProdLift {T : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}} (g : ∀ i, Y i ⟶ S)
    (t : T ⟶ S) (f : ∀ i, T ⟶ Y i) (hf : ∀ i, f i ≫ g i = t) : T ⟶ (overProd g).left :=
  (Pi.lift fun i ↦ (Over.homMk (f i) (hf i) : Over.mk t ⟶ Over.mk (g i))).left

/-- The `i`-th component of `Stacks.Chow.overProdLift` is the `i`-th given morphism. -/
@[simp]
theorem overProdLift_comp_π {T : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}}
    (g : ∀ i, Y i ⟶ S) (t : T ⟶ S) (f : ∀ i, T ⟶ Y i) (hf : ∀ i, f i ≫ g i = t) (i : Fin n) :
    overProdLift g t f hf ≫ overProdπ g i = f i :=
  congrArg Over.Hom.left (Pi.lift_π _ i)

/-- `Stacks.Chow.overProdLift` is a morphism over the base. -/
@[simp]
theorem overProdLift_comp_hom {T : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}}
    (g : ∀ i, Y i ⟶ S) (t : T ⟶ S) (f : ∀ i, T ⟶ Y i) (hf : ∀ i, f i ≫ g i = t) :
    overProdLift g t f hf ≫ (overProd g).hom = t :=
  (Pi.lift fun i ↦ (Over.homMk (f i) (hf i) : Over.mk t ⟶ Over.mk (g i))).w

end Stacks.Chow

namespace AlgebraicGeometry

/-- The finite product over a base of schemes satisfying a size cutoff satisfies it again,
provided the base does. -/
theorem Scheme.size_overProd_lt {κ : Cardinal.{u}} {S : Scheme.{u}} (hS : S.size < κ) :
    ∀ (n : ℕ) {Y : Fin n → Scheme.{u}} (g : ∀ i, Y i ⟶ S), (∀ i, (Y i).size < κ) →
      (Stacks.Chow.overProd g).left.size < κ
  | 0, _, g, _ => by
      rw [Scheme.size_congr (Stacks.Chow.overProdFinZeroIso g)]; exact hS
  | n + 1, _, g, hY => by
      rw [Scheme.size_congr (Stacks.Chow.overProdFinSuccIso g)]
      exact Scheme.size_pullback_lt _ _ (hY 0)
        (Scheme.size_overProd_lt hS n _ fun i ↦ hY i.succ)

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The finite fibre power over the base as an object of the big fppf category over `S`: the
product `Stacks.Chow.overProd` of the structure morphisms of the factors. -/
def overProdObj {n : ℕ} (Y : Fin n → BigFppfOver B S hS) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS
    (Scheme.size_overProd_lt hS n (fun i ↦ B.inclusion.map (Y i).hom) fun i ↦ (Y i).left.2)
    (Stacks.Chow.overProd fun i ↦ B.inclusion.map (Y i).hom).hom

/-- The underlying scheme of `AlgebraicGeometry.Space.overProdObj` is the product
`Stacks.Chow.overProd` of the structure morphisms of the factors. -/
theorem overProdObj_toScheme {n : ℕ} (Y : Fin n → BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).obj (overProdObj B S hS Y) =
      (Stacks.Chow.overProd fun i ↦ B.inclusion.map (Y i).hom).left :=
  rfl

/-- The structure morphism of `AlgebraicGeometry.Space.overProdObj` is that of
`Stacks.Chow.overProd`. -/
theorem overProdObj_hom {n : ℕ} (Y : Fin n → BigFppfOver B S hS) :
    B.inclusion.map (overProdObj B S hS Y).hom =
      (Stacks.Chow.overProd fun i ↦ B.inclusion.map (Y i).hom).hom :=
  rfl

/-- The `i`-th projection of `AlgebraicGeometry.Space.overProdObj`, as a morphism of the big
fppf category over `S`. -/
def overProdObjπ {n : ℕ} (Y : Fin n → BigFppfOver B S hS) (i : Fin n) :
    overProdObj B S hS Y ⟶ Y i :=
  Over.homMk
    (ObjectProperty.homMk (Stacks.Chow.overProdπ (fun i ↦ B.inclusion.map (Y i).hom) i))
    (ObjectProperty.hom_ext _ (Stacks.Chow.overProdπ_comp (fun i ↦ B.inclusion.map (Y i).hom) i))

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.overProdObjπ` is
`Stacks.Chow.overProdπ`. -/
theorem overProdObjπ_toScheme {n : ℕ} (Y : Fin n → BigFppfOver B S hS) (i : Fin n) :
    (BigFppfOver.toScheme B S hS).map (overProdObjπ B S hS Y i) =
      Stacks.Chow.overProdπ (fun i ↦ B.inclusion.map (Y i).hom) i :=
  rfl

/-- A morphism of the big fppf category over `S` into
`AlgebraicGeometry.Space.overProdObj`, given by its components. -/
def overProdObjLift {n : ℕ} (Y : Fin n → BigFppfOver B S hS) (T : BigFppfOver B S hS)
    (f : ∀ i, T ⟶ Y i) : T ⟶ overProdObj B S hS Y :=
  BigFppfOver.homMk B S hS _ _
    (Stacks.Chow.overProdLift (fun i ↦ B.inclusion.map (Y i).hom)
      (B.inclusion.map T.hom) (fun i ↦ (BigFppfOver.toScheme B S hS).map (f i))
      fun i ↦ by
        rw [show (BigFppfOver.toScheme B S hS).map (f i) = B.inclusion.map (f i).left from rfl,
          ← Functor.map_comp, Over.w])
    (Stacks.Chow.overProdLift_comp_hom _ _ _ _)

/-- The `i`-th component of `AlgebraicGeometry.Space.overProdObjLift` is the `i`-th given
morphism. -/
theorem overProdObjLift_comp_π {n : ℕ} (Y : Fin n → BigFppfOver B S hS)
    (T : BigFppfOver B S hS) (f : ∀ i, T ⟶ Y i) (i : Fin n) :
    overProdObjLift B S hS Y T f ≫ overProdObjπ B S hS Y i = f i :=
  BigFppfOver.map_toScheme_injective B S hS
    (Stacks.Chow.overProdLift_comp_π (fun i ↦ B.inclusion.map (Y i).hom)
      (B.inclusion.map T.hom) (fun i ↦ (BigFppfOver.toScheme B S hS).map (f i)) _ i)

end Space

end AlgebraicGeometry

end
