module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerGluing
public import StacksFrontier.AlgebraicGeometry.Crystalline.Restrict
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Functoriality

/-!
# Restricting a global crystalline situation to a pair of opens

Fix a global crystalline situation `(p, (S, I, γ), X)`, an open `W ⊆ S` and an open `V ⊆ X` whose
image in `S` lies in `W`.  Then `(p, (S, I, γ)|_W, V)` is again a global crystalline situation: the
divided power base is restricted by `Crystalline.DividedPowerScheme.restrict`, the thickened space
is the open subscheme `V`, and the structure morphism `V ⟶ (S|_W)₀` comes from the identification
of the closed fibre of a restriction with the corresponding open of the closed fibre.

The point of the construction is that an object of `CRIS(X/S)` whose ambient scheme maps into `W`
and whose thickened scheme maps into `V` *is* an object of `CRIS(V/S|_W)`, and that the two
categories agree on such objects.  Change of base along the two open immersions,
[Stacks, Tag 07IC], is fully faithful, so a construction carried out in `CRIS(V/S|_W)` — where `V`
and `W` may be taken affine — transports back to `CRIS(X/S)`.  This is how the binary products of
[Stacks, Tag 07I9], whose construction is local on `S` and on `X`, are obtained.

## Main definitions

* `Crystalline.DividedPowerScheme.restrictClosedFiberIso` — the closed fibre of a restriction
  `X|_W` is the open subscheme `closedFiberι X ⁻¹ᵁ W` of the closed fibre of `X`.
* `Crystalline.GlobalCrystallineSituation.restrict` — the restricted situation `(p, S|_W, V)`.
* `Crystalline.GlobalCrystallineSituation.extend` — change of base from the restricted situation
  back to `S`, along the two open immersions.

## Main results

* `Crystalline.GlobalCrystallineSituation.extendFullyFaithful` — change of base along the two open
  immersions is fully faithful.

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

namespace DividedPowerScheme

variable (X : DividedPowerScheme.{u}) (W : X.scheme.Opens)

/-- **The closed fibre inclusion of `X`, restricted over an open `W`, as a closed immersion into
the restriction `X|_W`.**  This is the morphism `closedFiberι X ∣_ W` of
`AlgebraicGeometry.morphismRestrict`, with its target named as the underlying scheme of the
divided power scheme `X|_W` rather than as the open subscheme `W`. -/
def restrictClosedFiberι : (closedFiberι X ⁻¹ᵁ W).toScheme ⟶ (X.restrict W).scheme :=
  (closedFiberι X) ∣_ W

/-- The restricted closed fibre inclusion `closedFiberι X ∣_ W` is a closed immersion. -/
instance isClosedImmersion_restrictClosedFiberι :
    IsClosedImmersion (restrictClosedFiberι X W) :=
  inferInstanceAs (IsClosedImmersion ((closedFiberι X) ∣_ W))

/-- **The closed fibre inclusion of a restriction and the restriction of the closed fibre
inclusion cut out the same ideal sheaf.**  Over an affine open `V` of `W` both are the divided
power ideal of `X` over the image of `V`: for the closed fibre of the restriction this is
`Crystalline.DividedPowerScheme.closedFiberι_ker_ideal` together with
`AlgebraicGeometry.Scheme.Opens.restrictSubmodule_obj`, and for the restricted inclusion it is
`AlgebraicGeometry.Scheme.ker_morphismRestrict_ideal`. -/
theorem ker_restrictClosedFiberι :
    Scheme.Hom.ker (restrictClosedFiberι X W) =
      Scheme.Hom.ker (closedFiberι (X.restrict W)) := by
  ext1
  funext V
  refine (Scheme.ker_morphismRestrict_ideal _ W V).trans ?_
  refine (closedFiberι_ker_ideal X _).trans ?_
  exact (closedFiberι_ker_ideal (X.restrict W) V).symm

/-- **The closed fibre of a restriction of a divided power scheme is the corresponding open of its
closed fibre.**  Two closed immersions into `W` cutting out the same ideal sheaf differ by a unique
isomorphism, and the two ideal sheaves agree by
`Crystalline.DividedPowerScheme.ker_restrictClosedFiberι`. -/
def restrictClosedFiberIso :
    closedFiber (X.restrict W) ≅ (closedFiberι X ⁻¹ᵁ W).toScheme :=
  haveI : IsIso (IsClosedImmersion.lift (restrictClosedFiberι X W)
      (closedFiberι (X.restrict W)) (ker_restrictClosedFiberι X W).le) :=
    IsClosedImmersion.isIso_lift _ _ (ker_restrictClosedFiberι X W)
  asIso (IsClosedImmersion.lift (restrictClosedFiberι X W) (closedFiberι (X.restrict W))
    (ker_restrictClosedFiberι X W).le)

/-- The identification of the closed fibre of a restriction with an open of the closed fibre is
compatible with the two closed immersions into `W`. -/
@[reassoc]
theorem restrictClosedFiberIso_hom_restrictClosedFiberι :
    (restrictClosedFiberIso X W).hom ≫ restrictClosedFiberι X W =
      closedFiberι (X.restrict W) :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inverse form of
`Crystalline.DividedPowerScheme.restrictClosedFiberIso_hom_restrictClosedFiberι`. -/
@[reassoc]
theorem restrictClosedFiberIso_inv_closedFiberι :
    (restrictClosedFiberIso X W).inv ≫ closedFiberι (X.restrict W) =
      restrictClosedFiberι X W :=
  (Iso.inv_comp_eq _).mpr (restrictClosedFiberIso_hom_restrictClosedFiberι X W).symm

/-- **The identification of the closed fibre of a restriction with an open of the closed fibre
intertwines the map of closed fibres with the open immersion.**  Both sides become the restricted
closed fibre inclusion after composing with the closed fibre inclusion of `X`, which is a
monomorphism. -/
@[reassoc]
theorem restrictClosedFiberIso_inv_closedFiberMap :
    (restrictClosedFiberIso X W).inv ≫ closedFiberMap (X.restrictι W) =
      (closedFiberι X ⁻¹ᵁ W).ι :=
  (cancel_mono (closedFiberι X)).mp <| by
    rw [Category.assoc, closedFiberMap_comp_closedFiberι,
      restrictClosedFiberIso_inv_closedFiberι_assoc]
    exact morphismRestrict_ι _ _

end DividedPowerScheme

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

/-- The structure morphism of the restricted situation, before it is read in the closed fibre of
the restricted base: the open immersion of `V` followed by the structure morphism of `S`, which
lands in the preimage of `W` because the image of `V` in `S` lies in `W`. -/
def restrictToClosedFiberAux : V.toScheme ⟶ (DividedPowerScheme.closedFiberι S.S ⁻¹ᵁ W).toScheme :=
  IsOpenImmersion.lift (DividedPowerScheme.closedFiberι S.S ⁻¹ᵁ W).ι (V.ι ≫ S.toClosedFiber)
    (by
      rintro y ⟨x, rfl⟩
      exact ⟨⟨S.toClosedFiber (V.ι x), hVW x.property⟩, rfl⟩)

/-- The auxiliary structure morphism composed with the open immersion of the preimage of `W` is
the structure morphism of `S` restricted to `V`. -/
@[reassoc]
theorem restrictToClosedFiberAux_ι :
    restrictToClosedFiberAux S W V hVW ≫ (DividedPowerScheme.closedFiberι S.S ⁻¹ᵁ W).ι =
      V.ι ≫ S.toClosedFiber :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The restriction of a global crystalline situation to an open of the base and an open of the
thickened space.**  The divided power base is `S|_W`, the thickened space is `V`, and the structure
morphism is the structure morphism of `S` restricted to `V`, read in the closed fibre of `S|_W`
through `Crystalline.DividedPowerScheme.restrictClosedFiberIso`.  Local nilpotence of `p` is
inherited from `S` because the local rings of an open subscheme are those of the ambient
scheme. -/
def restrict : GlobalCrystallineSituation.{u} where
  p := S.p
  prime := S.prime
  S := S.S.restrict W
  algebraAtPrime :=
    (((S.S.restrictι W).hom.appTop).hom.comp
      (algebraMap (DividedPowers.IntegersAtPrime S.p) Γ(S.S.scheme, ⊤))).toAlgebra
  X := V.toScheme
  toClosedFiber :=
    restrictToClosedFiberAux S W V hVW ≫ (DividedPowerScheme.restrictClosedFiberIso S.S W).inv
  prime_locallyNilpotent x := by
    have h := S.prime_locallyNilpotent (V.ι.base x)
    simpa using h.map (V.ι.stalkMap x).hom

/-- The prime of the restricted situation is that of `S`. -/
@[simp]
theorem restrict_p : (restrict S W V hVW).p = S.p := rfl

/-- The divided power base of the restricted situation is `S|_W`. -/
@[simp]
theorem restrict_S : (restrict S W V hVW).S = S.S.restrict W := rfl

/-- The thickened space of the restricted situation is the open subscheme `V`. -/
@[simp]
theorem restrict_X : (restrict S W V hVW).X = V.toScheme := rfl

/-- The structure morphism of the restricted situation, by definition. -/
@[simp]
theorem restrict_toClosedFiber :
    (restrict S W V hVW).toClosedFiber =
      restrictToClosedFiberAux S W V hVW ≫
        (DividedPowerScheme.restrictClosedFiberIso S.S W).inv :=
  rfl

/-- **The compatibility of the two open immersions with the structure morphisms**, which is the
hypothesis of change of base, [Stacks, Tag 07IC], for the pair `(S|_W ⟶ S, V ⟶ X)`. -/
theorem restrict_changeBase_condition :
    (restrict S W V hVW).toClosedFiber ≫
        DividedPowerScheme.closedFiberMap (S.S.restrictι W) = V.ι ≫ S.toClosedFiber :=
  (Category.assoc _ _ _).trans <|
    (congrArg _ (DividedPowerScheme.restrictClosedFiberIso_inv_closedFiberMap S.S W)).trans
      (restrictToClosedFiberAux_ι S W V hVW)

/-- **Change of base from the restricted situation back to `S`.**  This is [Stacks, Tag 07IC] for
the two open immersions `S|_W ⟶ S` and `V ⟶ X`: an object of `CRIS(V/S|_W)` is read as an object
of `CRIS(X/S)` with the same thickening, by composing its two structure morphisms with the open
immersions. -/
def extend : Thickening (restrict S W V hVW) ⥤ Thickening S :=
  changeBase (restrict S W V hVW) S (S.S.restrictι W) V.ι
    (restrict_changeBase_condition S W V hVW)

/-- The restriction morphism of the divided power base is a monomorphism, being an open immersion
on underlying schemes. -/
instance mono_restrictι : Mono (S.S.restrictι W) :=
  DividedPowerScheme.mono_of_mono_hom (IsOpenImmersion.mono (S.S.restrictι W).hom)

/-- **Change of base along the two open immersions is full**, because both structure morphisms are
monomorphisms. -/
instance extend_full : (extend S W V hVW).Full :=
  changeBase_full (S := restrict S W V hVW) (S' := S) (f := S.S.restrictι W) (g := V.ι)
    (h := restrict_changeBase_condition S W V hVW) (mono_restrictι S W)
    (IsOpenImmersion.mono V.ι)

/-- Change of base is always faithful. -/
instance extend_faithful : (extend S W V hVW).Faithful :=
  changeBase_faithful (S := restrict S W V hVW) (S' := S) (f := S.S.restrictι W) (g := V.ι)
    (h := restrict_changeBase_condition S W V hVW)

/-- **Change of base along the two open immersions is fully faithful.**  Change of base is always
faithful, and it is full as soon as its two structure morphisms are monomorphisms, which open
immersions are. -/
def extendFullyFaithful : (extend S W V hVW).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (extend S W V hVW)

end GlobalCrystallineSituation

end Crystalline

end
