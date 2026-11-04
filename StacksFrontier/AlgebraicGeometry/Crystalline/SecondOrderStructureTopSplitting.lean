module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningScheme
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningSections

/-!
# The top summand of the structure sheaf of the second-order universal thickening

Let `(T, J, δ)` be a divided power scheme over a scheme `Y` and let `T''` be the second-order
universal thickening of [Stacks, Remark 60.14.5, Tag 07J3]: the space of `T` carrying the ring

`𝒪_{T''} = 𝒪_T ⊕ Ω_{T/Y,δ} ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}`,

whose multiplication is corrected in the last coordinate by the exterior product of the two
middle ones.  The morphism `q₀ : T'' ⟶ T` is the inclusion `g ↦ (g, 0, 0, 0)` on sections and is
the identity on the space.

Reading `𝒪_{T''}` through `q₀` makes it a sheaf of `𝒪_T`-modules, and this module proves that as
such the top summand is a **direct summand**:

`Ω²_{T/Y,δ} ⟶ q₀_* 𝒪_{T''}`,  `η ↦ (0, 0, 0, η)`,

is a split monomorphism, retracted by the top coordinate.  Both maps are `𝒪_T`-linear because the
top summand is an ideal on which `𝒪_T` acts through the first coordinate,
`Crystalline.secondOrderExt_top_mul`, and because the top coordinate of `(a, 0, 0, 0) · x` is
`a · (top coordinate of x)` — the two middle coordinates of `q₀ a` vanishing, the exterior
correction term of the multiplication does not contribute.

This is the degree-two counterpart of
`Crystalline.firstOrderThickeningInrSheaf` and `Crystalline.firstOrderThickeningSndSheaf` of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderStructureSplitting.lean`, cut to what the
degree-two monomorphism of [Stacks, Lemma 60.15.1, Tag 07J6] needs: a retraction of the top
inclusion, rather than the whole four-fold decomposition.

## Main definitions

* `Crystalline.secondOrderThickeningUnitRestriction` — `𝒪_{T''}` read as a sheaf of
  `𝒪_T`-modules, through the comorphism of `q₀`.
* `Crystalline.secondOrderThickeningTopInrSheaf` — **the top summand as a sheaf of
  `𝒪_T`-modules**: the inclusion `Ω²_{T/Y,δ} ⟶ q₀_* 𝒪_{T''}`, `η ↦ (0, 0, 0, η)`.
* `Crystalline.secondOrderThickeningTopSheaf` — its retraction, the top coordinate.

## Main results

* `Crystalline.secondOrderThickeningTopInrSheaf_comp_topSheaf` — the retraction identity.
* `Crystalline.isSplitMono_secondOrderThickeningTopInrSheaf` — **the top inclusion is a split
  monomorphism** of sheaves of `𝒪_T`-modules.

## Scope

Nothing here carries a `@[stacks]` attribute.  That `𝒪_{T''}` is
`𝒪_T ⊕ Ω_{T/Y,δ} ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}` is already tagged where the ring is built, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderThickening.lean`; what is added here is
only that the top summand splits off as a sheaf of `𝒪_T`-modules rather than as a family of
abelian groups over the opens.

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open PresheafOfModules

universe u

noncomputable section

namespace Crystalline

/-! ### Two identities in the abstract second-order extension

They are proved here rather than in the crystalline setting for the reason recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderThickeningSections.lean`: over a section
ring of the crystalline site the module structures are reached through `inferInstanceAs`, and
`rw` does not see through that. -/

section SecondOrderExt

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
  {q : Stacks.BilinearMap M₁ M₂ N} {X : Cᵒᵖ}

/-- **The top coordinate of `(a, 0, 0, 0) · y` is `a · (top coordinate of y)`.**  The two middle
coordinates of the left factor vanish, so neither correction term of the second-order
multiplication contributes. -/
theorem secondOrderExtTop_incl_mul (a : ↑(R.obj X)) (y : SecondOrderExt q X) :
    secondOrderExtTop (secondOrderExtMk (q := q) a 0 0 0 * y) = a • secondOrderExtTop y := by
  rw [secondOrderExtTop_mul, secondOrderExtFst_mk, secondOrderExtTop_mk, secondOrderExtLeft_mk,
    secondOrderExtRight_mk, smul_zero, add_zero, bilinearApp_zero_left, add_zero,
    bilinearApp_zero_right, add_zero]

/-- **The top summand is a module over the ring through the inclusion of the first
coordinate**: `(a, 0, 0, 0) · (0, 0, 0, p) = (0, 0, 0, a p)`. -/
theorem secondOrderExt_incl_mul_top (a : ↑(R.obj X)) (p : ↑(N.obj X)) :
    secondOrderExtMk (q := q) a 0 0 0 * secondOrderExtMk (q := q) 0 0 0 p =
      secondOrderExtMk (q := q) 0 0 0 (a • p) :=
  (mul_comm _ _).trans ((secondOrderExt_top_mul p _).trans
    (congrArg (secondOrderExtMk (q := q) 0 0 0) (congrArg (fun c ↦ c • p)
      (secondOrderExtFst_mk (q := q) a 0 0 0))))

end SecondOrderExt

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- **`𝒪_{T''}` as a sheaf of `𝒪_T`-modules**, the scalars being read through the comorphism
`g ↦ (g, 0, 0, 0)` of `q₀ : T'' ⟶ T`. -/
abbrev secondOrderThickeningUnitRestriction : T.scheme.Modules :=
  (Scheme.Modules.pushforward (secondOrderThickeningQ₀Hom T Y f)).obj
    (SheafOfModules.unit (secondOrderThickeningScheme T Y f).ringCatSheaf)

/-! ### The top coordinate of a product with a section pulled back along `q₀` -/

/-- **The top coordinate of `(a, 0, 0, 0) · x` is `a · (top coordinate of x)`.**  The two middle
coordinates of `q₀ a` vanish, so neither exterior correction term of the second-order
multiplication contributes. -/
theorem secondOrderExtTop_secondOrderThickeningQ₀_mul (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : T.scheme.sheaf.obj.obj W) (x : ↑((secondOrderThickeningPresheaf T Y f).obj W)) :
    secondOrderExtTop (q := dpWedge T Y f) (((secondOrderThickeningQ₀ T Y f).app W).hom a * x) =
      a • secondOrderExtTop x :=
  secondOrderExtTop_incl_mul a x

/-- **The first coordinate of `(a, 0, 0, 0) · x` is `a · (first coordinate of x)`.** -/
theorem secondOrderExtFst_secondOrderThickeningQ₀_mul (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : T.scheme.sheaf.obj.obj W) (x : ↑((secondOrderThickeningPresheaf T Y f).obj W)) :
    secondOrderExtFst (q := dpWedge T Y f) (((secondOrderThickeningQ₀ T Y f).app W).hom a * x) =
      a * secondOrderExtFst x := rfl

/-! ### The top summand and its retraction -/

/-- The inclusion `η ↦ (0, 0, 0, η)` of the top summand of `𝒪_{T''}`, on sections over an
open. -/
def secondOrderThickeningTopInr (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑((dpSecondExteriorModules T Y f).obj W) →+
      ↑((secondOrderThickeningPresheaf T Y f).obj W) where
  toFun η := secondOrderExtMk (q := dpWedge T Y f) 0 0 0 η
  map_zero' := rfl
  map_add' η η' := secondOrderExtMk_top_add η η'

/-- **Multiplying a section of the top summand of `𝒪_{T''}` by `q₀ a` scales the two-form by
`a`**: `(a, 0, 0, 0) · (0, 0, 0, η) = (0, 0, 0, a η)`.  This is the `𝒪_T`-linearity of the top
inclusion. -/
theorem secondOrderThickeningQ₀_mul_topInr (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : T.scheme.sheaf.obj.obj W) (η : ↑((dpSecondExteriorModules T Y f).obj W)) :
    ((secondOrderThickeningQ₀ T Y f).app W).hom a * secondOrderThickeningTopInr T Y f W η =
      secondOrderThickeningTopInr T Y f W (a • η) :=
  secondOrderExt_incl_mul_top a η

/-- The inclusion `η ↦ (0, 0, 0, η)` of the top summand, as a morphism of the underlying
presheaves of abelian groups. -/
def secondOrderThickeningTopInrPresheaf :
    (dpSecondExteriorPower T Y f).val.presheaf ⟶
      (secondOrderThickeningUnitRestriction T Y f).val.presheaf where
  app W := AddCommGrpCat.ofHom (secondOrderThickeningTopInr T Y f W)
  naturality _ _ _ := by
    ext η
    exact secondOrderExt_ext (map_zero _).symm (map_zero _).symm (map_zero _).symm rfl

/-- **The top summand of `𝒪_{T''}`, as a sheaf of `𝒪_T`-modules.**  The inclusion
`Ω²_{T/Y,δ} ⟶ q₀_* 𝒪_{T''}`, `η ↦ (0, 0, 0, η)`, of [Stacks, Tag 07J3].  It is `𝒪_T`-linear
because `(a, 0, 0, 0) · (0, 0, 0, η) = (0, 0, 0, a η)`, which is
`Crystalline.secondOrderThickeningQ₀_mul_topInr`. -/
def secondOrderThickeningTopInrSheaf :
    dpSecondExteriorPower T Y f ⟶ secondOrderThickeningUnitRestriction T Y f :=
  ⟨PresheafOfModules.homMk (secondOrderThickeningTopInrPresheaf T Y f) (by
    intro W a η
    exact (secondOrderThickeningQ₀_mul_topInr T Y f W a η).symm)⟩

/-- On sections over `W`, the sheaf map `secondOrderThickeningTopInrSheaf` is the inclusion
`η ↦ (0, 0, 0, η)` given by `secondOrderThickeningTopInr`. -/
@[simp]
theorem secondOrderThickeningTopInrSheaf_val_app (W : (Opens ↑T.scheme)ᵒᵖ)
    (η : (dpSecondExteriorPower T Y f).val.obj W) :
    (secondOrderThickeningTopInrSheaf T Y f).val.app W η =
      secondOrderThickeningTopInr T Y f W η := rfl

/-- The top coordinate `(g, ω₁, ω₂, η) ↦ η` of `𝒪_{T''}`, as a morphism of the underlying
presheaves of abelian groups. -/
def secondOrderThickeningTopPresheaf :
    (secondOrderThickeningUnitRestriction T Y f).val.presheaf ⟶
      (dpSecondExteriorPower T Y f).val.presheaf where
  app _ := AddCommGrpCat.ofHom
    { toFun x := secondOrderExtTop (q := dpWedge T Y f) x
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

/-- **The retraction of the top summand**, `(g, ω₁, ω₂, η) ↦ η`.  It is `𝒪_T`-linear because the
top coordinate of `(a, 0, 0, 0) · x` is `a · (top coordinate of x)`,
`Crystalline.secondOrderExtTop_secondOrderThickeningQ₀_mul`. -/
def secondOrderThickeningTopSheaf :
    secondOrderThickeningUnitRestriction T Y f ⟶ dpSecondExteriorPower T Y f :=
  ⟨PresheafOfModules.homMk (secondOrderThickeningTopPresheaf T Y f) (by
    intro W a x
    exact secondOrderExtTop_secondOrderThickeningQ₀_mul T Y f W a x)⟩

/-- **The top coordinate retracts the top inclusion.** -/
@[reassoc (attr := simp)]
theorem secondOrderThickeningTopInrSheaf_comp_topSheaf :
    secondOrderThickeningTopInrSheaf T Y f ≫ secondOrderThickeningTopSheaf T Y f =
      𝟙 (dpSecondExteriorPower T Y f) := by
  ext W x
  rfl

/-- **The inclusion of the top summand `Ω²_{T/Y,δ} ⟶ q₀_* 𝒪_{T''}` is a split monomorphism** of
sheaves of `𝒪_T`-modules. -/
theorem isSplitMono_secondOrderThickeningTopInrSheaf :
    IsSplitMono (secondOrderThickeningTopInrSheaf T Y f) :=
  ⟨⟨⟨secondOrderThickeningTopSheaf T Y f,
    secondOrderThickeningTopInrSheaf_comp_topSheaf T Y f⟩⟩⟩

end Crystalline

end

end
