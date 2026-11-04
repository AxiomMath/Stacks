module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Limits
public import StacksFrontier.AlgebraicGeometry.Crystalline.ClosedFiberPullback

/-!
# The closed fibre `S₀` as a divided power base, and `X/S₀`

Let `(p, (S, I, γ), X)` be a global crystalline situation [Stacks, Tag 07MF], and let
`S₀ = V(I)` be the closed fibre of the divided power base.  The scheme `S₀` carries the *trivial*
divided power structure, on its zero ideal sheaf (`Crystalline.trivialDividedPowerScheme`).  This
file records:

* the closed fibre of `(S₀, 0, 0)` is `S₀` itself: the identity of `S₀` presents it
  (`Crystalline.trivialClosedFiberPresentation`), whence an isomorphism
  `Crystalline.trivialClosedFiberIso` over `S₀`;
* the closed immersion `S₀ ⟶ S` is a divided power morphism `(S₀, 0, 0) ⟶ (S, I, γ)`
  (`Crystalline.GlobalCrystallineSituation.closedFiberToBaseHom`), it kills `I`;
* `X/S₀` is a global crystalline situation on the same `X`, over `(S₀, 0, 0)`
  (`Crystalline.GlobalCrystallineSituation.trivialBaseSituation`);
* the closed-fibre square of the pair `(S₀ ⟶ S, 𝟙_X)` commutes
  (`Crystalline.GlobalCrystallineSituation.trivialBaseSituation_comm`), in the shape taken by
  change of divided power base `changeBase (trivialBaseSituation S) S (closedFiberToBaseHom S)
  (𝟙 _) _` and by everything built on it.

## References

* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07I8](https://stacks.math.columbia.edu/tag/07I8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-- **The closed fibre of a scheme with its zero divided power ideal is presented by the identity
of the scheme**: no section of the zero ideal is nonzero, and the identity kills only zero. -/
def trivialClosedFiberPresentation (Y : Scheme.{u}) :
    DividedPowerScheme.ClosedFiberPresentation (trivialDividedPowerScheme Y) where
  carrier := (trivialDividedPowerScheme Y).scheme
  ι := 𝟙 _
  isClosedImmersion := inferInstance
  app_eq_zero_of_mem V s hs := by
    have h0 := (SheafOfModules.Submodule.bot_obj _ (op V)).le hs
    have h1 := (Submodule.mem_bot _).1 h0
    rw [show s = 0 from h1]
    exact map_zero _
  mem_of_app_eq_zero V s hs :=
    (SheafOfModules.Submodule.bot_obj _ (op V.1)).ge ((Submodule.mem_bot _).mpr hs)

/-- **The closed fibre of a scheme with its zero divided power ideal is the scheme itself**: the
comparison of the canonical presentation of the closed fibre with the presentation by the
identity. -/
def trivialClosedFiberIso (Y : Scheme.{u}) :
    DividedPowerScheme.closedFiber (trivialDividedPowerScheme Y) ≅
      (trivialDividedPowerScheme Y).scheme :=
  (DividedPowerScheme.closedFiberPresentation _).isoOfPresentations
    (trivialClosedFiberPresentation Y)

/-- The isomorphism `Crystalline.trivialClosedFiberIso` is the inclusion of the closed fibre. -/
theorem trivialClosedFiberIso_hom (Y : Scheme.{u}) :
    (trivialClosedFiberIso Y).hom = DividedPowerScheme.closedFiberι (trivialDividedPowerScheme Y) :=
  (Category.comp_id _).symm.trans
    (DividedPowerScheme.ClosedFiberPresentation.isoOfPresentations_hom_comp_ι
      (DividedPowerScheme.closedFiberPresentation _) (trivialClosedFiberPresentation Y))

/-- **The inclusion of the closed fibre of a scheme with its zero divided power ideal is an
isomorphism.** -/
instance isIso_closedFiberι_trivialDividedPowerScheme (Y : Scheme.{u}) :
    IsIso (DividedPowerScheme.closedFiberι (trivialDividedPowerScheme Y)) := by
  rw [← trivialClosedFiberIso_hom]
  infer_instance

/-- The inverse of `Crystalline.trivialClosedFiberIso` followed by the inclusion of the closed
fibre is the identity. -/
@[reassoc (attr := simp)]
theorem trivialClosedFiberIso_inv_closedFiberι (Y : Scheme.{u}) :
    (trivialClosedFiberIso Y).inv ≫
      DividedPowerScheme.closedFiberι (trivialDividedPowerScheme Y) = 𝟙 _ := by
  rw [← trivialClosedFiberIso_hom, Iso.inv_hom_id]

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-- **The closed immersion `S₀ ⟶ S` as a divided power morphism `(S₀, 0, 0) ⟶ (S, I, γ)`**: it
kills the divided power ideal `I`, and its source has zero divided power ideal. -/
def closedFiberToBaseHom :
    trivialDividedPowerScheme (DividedPowerScheme.closedFiber S.S) ⟶ S.S where
  hom := DividedPowerScheme.closedFiberι S.S
  compatible :=
    isDPMorphism_trivialDividedPowerScheme (DividedPowerScheme.closedFiberι S.S)
      (DividedPowerScheme.closedFiberPresentation S.S).app_eq_zero_of_mem

/-- The underlying morphism of `S₀ ⟶ S` is the inclusion of the closed fibre. -/
@[simp]
theorem closedFiberToBaseHom_hom :
    (closedFiberToBaseHom S).hom = DividedPowerScheme.closedFiberι S.S := rfl

/-- **The map on closed fibres of `S₀ ⟶ S` is the inverse of the identification of the closed
fibre of `(S₀, 0, 0)` with `S₀`.** -/
theorem closedFiberMap_closedFiberToBaseHom :
    DividedPowerScheme.closedFiberMap (closedFiberToBaseHom S) =
      (trivialClosedFiberIso (DividedPowerScheme.closedFiber S.S)).hom :=
  (DividedPowerScheme.eq_closedFiberMap _ _ (by rw [trivialClosedFiberIso_hom]; rfl)).symm

/-- The `ℤ_(p)`-algebra structure on the global sections of `S₀`, through those of `S`. -/
instance algebraAtPrimeClosedFiber :
    Algebra (DividedPowers.IntegersAtPrime S.p)
      Γ((trivialDividedPowerScheme (DividedPowerScheme.closedFiber S.S)).scheme, ⊤) :=
  ((DividedPowerScheme.closedFiberι S.S).appTop.hom.comp
    (algebraMap (DividedPowers.IntegersAtPrime S.p) Γ(S.S.scheme, ⊤))).toAlgebra

/-- **`X/S₀`: the global crystalline situation on the same scheme `X` over the closed fibre
`S₀ = V(I)` of the divided power base, with its zero divided power ideal.**  Its closed fibre is
`S₀` itself, and the structure morphism `X ⟶ S₀` is that of `X/S`. -/
abbrev trivialBaseSituation : GlobalCrystallineSituation.{u} where
  p := S.p
  S := trivialDividedPowerScheme (DividedPowerScheme.closedFiber S.S)
  X := S.X
  toClosedFiber := S.toClosedFiber ≫ (trivialClosedFiberIso _).inv
  prime_locallyNilpotent := S.prime_locallyNilpotent

/-- The scheme of `X/S₀` is `X`. -/
@[simp]
theorem trivialBaseSituation_X : (trivialBaseSituation S).X = S.X := rfl

/-- The prime `p` of `X/S₀` is that of `X/S`. -/
@[simp]
theorem trivialBaseSituation_p : (trivialBaseSituation S).p = S.p := rfl

/-- The divided power base of `X/S₀` is the closed fibre `S₀` with its zero divided power ideal. -/
@[simp]
theorem trivialBaseSituation_S :
    (trivialBaseSituation S).S = trivialDividedPowerScheme (DividedPowerScheme.closedFiber S.S) :=
  rfl

/-- The structure morphism of `X/S₀`, followed by the identification of the closed fibre of
`(S₀, 0, 0)` with `S₀`, is that of `X/S`. -/
theorem trivialBaseSituation_toClosedFiber_comp :
    (trivialBaseSituation S).toClosedFiber ≫
        DividedPowerScheme.closedFiberι (trivialDividedPowerScheme
          (DividedPowerScheme.closedFiber S.S)) = S.toClosedFiber :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ S.toClosedFiber ≫ k)
      (trivialClosedFiberIso_inv_closedFiberι (DividedPowerScheme.closedFiber S.S))).trans
      (Category.comp_id _))

/-- **The closed-fibre square of `(S₀ ⟶ S, 𝟙_X)` commutes**: the hypothesis taken by change of
divided power base from `X/S₀` to `X/S` along the divided power morphism `S₀ ⟶ S` and the identity
of `X`. -/
theorem trivialBaseSituation_comm :
    (trivialBaseSituation S).toClosedFiber ≫
        DividedPowerScheme.closedFiberMap (closedFiberToBaseHom S) =
      𝟙 S.X ≫ S.toClosedFiber := by
  refine (cancel_mono (DividedPowerScheme.closedFiberι S.S)).1 ?_
  rw [Category.assoc, DividedPowerScheme.closedFiberMap_comp_closedFiberι, closedFiberToBaseHom_hom,
    Category.id_comp]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ DividedPowerScheme.closedFiberι S.S) (trivialBaseSituation_toClosedFiber_comp S))

/-- **Change of divided power base from `X/S₀` to `X/S`** along the divided power morphism
`S₀ ⟶ S` and the identity of `X`, [Stacks, Tag 07IC]. -/
abbrev trivialBaseChangeBase : Thickening (trivialBaseSituation S) ⥤ Thickening S :=
  changeBase (trivialBaseSituation S) S (closedFiberToBaseHom S) (𝟙 S.X)
    (trivialBaseSituation_comm S)

/-- The closed fibre of an affine divided power base is affine. -/
instance isAffine_trivialBaseSituation_S [IsAffine S.S.scheme] :
    IsAffine (trivialBaseSituation S).S.scheme :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine
    (DividedPowerScheme.closedFiberPresentation S.S).ι).1

end GlobalCrystallineSituation

end Crystalline
