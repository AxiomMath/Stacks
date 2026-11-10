module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.AffineSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Comparison07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureMorphism
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections

/-!
# Smooth lifts of affine opens as objects of the big crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine, `A = Γ(S, ⊤)`, and `p`
nilpotent in `A`.  For a scheme `U` with a map `j : U ⟶ X`, `U` affine, a *smooth lift* of `U` is a
smooth `A`-algebra `B` together with an identification `Γ(U, ⊤) ≅ B/IB` over `A`
(`Crystalline.GlobalCrystallineSituation.CechEnvelope.SmoothLift`).  Then `Y = Spec B` is smooth
over `S`, its closed fibre `Y ×_S S₀ = Spec(B/IB)` is `U`, and the extension of `γ` to `IB` along
the flat map `A → B` ([Stacks, Tag 07H1]) makes `(U, Y)` an object of `CRIS(X/S)` through
`U ⟶ X` (`SmoothLift.object`).  When `j` is an open immersion the object lies in `Cris(X/S)`.

Smooth lifts exist as soon as `U ⟶ S₀` is smooth (`nonempty_smoothLift`): the sections
`Γ(U, ⊤)` are smooth over `Γ(S₀, ⊤) = A/I`, and smooth algebras lift along the surjection
`A → A/I` (`Stacks.Smoothing.exists_smooth_lift_of_surjective`).

The objects are built in the situation `X'/S` of the scheme `U` over `X`
(`...SmallSite.overSituation`), where `X' = U` is affine and the affine-to-global bridge
`Crystalline.GlobalCrystallineSituation.specThickeningOfAffine` applies, and pushed to `CRIS(X/S)`
by `overPush`, which composes the map to the base scheme with `j`.

## Main definitions

* `CechEnvelope.overPush` — `CRIS(U/S) ⥤ CRIS(X/S)` for `j : U ⟶ X`, full and faithful when `j`
  is a monomorphism; `CechEnvelope.overLift` and `CechEnvelope.homOfOverLift` read an object of
  `CRIS(X/S)` whose map to `X` factors through `j` in `CRIS(U/S)`.
* `CechEnvelope.SmoothLift` — a smooth lift of `U` over `A`.
* `CechEnvelope.SmoothLift.dividedPowerRing` — `(B, IB, γ_B)`, `γ_B` the extension of `γ`.
* `CechEnvelope.SmoothLift.thickening` — the object of `CRIS(Γ(U, ⊤)/A)` it defines.
* `CechEnvelope.SmoothLift.object` — **the object `(U, Spec B, γ_B)` of `CRIS(X/S)`.**

## Main results

* `CechEnvelope.nonempty_smoothLift` — **every affine `U` smooth over `S₀` has a smooth lift.**
* `CechEnvelope.SmoothLift.isOpenImmersion_object_toX` — the object lies in `Cris(X/S)` when `j`
  is an open immersion; `isAffine_object_target`, `isAffine_object_source` — its two schemes are
  affine.

## References

* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite

variable (S : GlobalCrystallineSituation.{u}) {U : Scheme.{u}} (j : U ⟶ S.X)

/-! ### Objects over a scheme mapping to `X` -/

/-- The objects of `CRIS(U/S)` for a scheme `U` over `X`, read as objects of `CRIS(X/S)`. -/
def overPush : Thickening (overSituation S j) ⥤ Thickening S where
  obj A :=
    { thickening := A.thickening
      toBase := A.toBase
      toX := A.toX ≫ j
      over_base := by
        rw [A.over_base, Category.assoc]
        rfl }
  map {A B} k :=
    { sourceHom := k.sourceHom
      targetHom := k.targetHom
      immersion_naturality := k.immersion_naturality
      base_naturality := k.base_naturality
      toX_naturality := by
        change k.sourceHom ≫ B.toX ≫ j = A.toX ≫ j
        rw [← Category.assoc, k.toX_naturality] }

/-- `overPush` on objects. -/
@[simp]
theorem overPush_obj_thickening (A : Thickening (overSituation S j)) :
    ((overPush S j).obj A).thickening = A.thickening := rfl

/-- `overPush` on objects. -/
@[simp]
theorem overPush_obj_toBase (A : Thickening (overSituation S j)) :
    ((overPush S j).obj A).toBase = A.toBase := rfl

/-- `overPush` on objects. -/
@[simp]
theorem overPush_obj_toX (A : Thickening (overSituation S j)) :
    ((overPush S j).obj A).toX = A.toX ≫ j := rfl

/-- `overPush` on morphisms. -/
@[simp]
theorem overPush_map_sourceHom {A B : Thickening (overSituation S j)} (k : A ⟶ B) :
    ((overPush S j).map k).sourceHom = k.sourceHom := rfl

/-- `overPush` on morphisms. -/
@[simp]
theorem overPush_map_targetHom {A B : Thickening (overSituation S j)} (k : A ⟶ B) :
    ((overPush S j).map k).targetHom = k.targetHom := rfl

/-- `overPush` is faithful: a morphism is its two maps of schemes. -/
instance faithful_overPush : (overPush S j).Faithful where
  map_injective {A B} _ _ h :=
    Thickening.Hom.ext
      (congrArg (fun f : (overPush S j).obj A ⟶ (overPush S j).obj B ↦ f.sourceHom) h)
      (congrArg (fun f : (overPush S j).obj A ⟶ (overPush S j).obj B ↦ f.targetHom) h)

/-- `overPush` is full when `j` is a monomorphism: the compatibility with the maps to `U` follows
from the compatibility with the maps to `X`. -/
instance full_overPush [Mono j] : (overPush S j).Full where
  map_surjective k :=
    ⟨{ sourceHom := k.sourceHom
       targetHom := k.targetHom
       immersion_naturality := k.immersion_naturality
       base_naturality := k.base_naturality
       toX_naturality := (cancel_mono j).1 ((Category.assoc _ _ _).trans k.toX_naturality) },
      rfl⟩

/-- An object of `CRIS(X/S)` whose map to `X` factors through `j`, read as an object of
`CRIS(U/S)`. -/
def overLift (T : Thickening S) (t : T.thickening.source ⟶ U) (ht : t ≫ j = T.toX) :
    Thickening (overSituation S j) where
  thickening := T.thickening
  toBase := T.toBase
  toX := t
  over_base := by
    rw [T.over_base, ← ht]
    simp only [sourceToBase, Category.assoc]

/-- A morphism out of `overLift` gives a morphism of `CRIS(X/S)` into `overPush`. -/
def homOfOverLift {T : Thickening S} {t : T.thickening.source ⟶ U} {ht : t ≫ j = T.toX}
    {D : Thickening (overSituation S j)} (k : overLift S j T t ht ⟶ D) :
    T ⟶ (overPush S j).obj D where
  sourceHom := k.sourceHom
  targetHom := k.targetHom
  immersion_naturality := k.immersion_naturality
  base_naturality := k.base_naturality
  toX_naturality := by
    change k.sourceHom ≫ D.toX ≫ j = T.toX
    rw [← Category.assoc]
    exact (congrArg (· ≫ j) k.toX_naturality).trans ht

/-! ### Smooth lifts -/

section SmoothLift

variable [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤)))

omit [IsAffine S.S.scheme] in
include hp in
/-- The prime is nilpotent on the global sections of a scheme over `X` when it is on the base. -/
theorem isNilpotent_prime_over : IsNilpotent ((overSituation S j).p : Γ(U, ⊤)) := by
  simpa only [map_natCast] using hp.map (sourceToBase (overSituation S j)).appTop.hom

/-- **A smooth lift of `U` over `A = Γ(S, ⊤)`**: a smooth `A`-algebra `B` with an identification
`Γ(U, ⊤) ≅ B/IB` compatible with the two maps from `A`, `I` the divided power ideal of `A`. -/
structure SmoothLift where
  /-- The smooth algebra. -/
  ring : Type u
  /-- Its ring structure. -/
  [commRing : CommRing ring]
  /-- Its algebra structure. -/
  [algebra : Algebra (baseSectionsRing S) ring]
  /-- Smoothness. -/
  smooth : Algebra.Smooth (baseSectionsRing S) ring
  /-- The identification of its reduction with the sections of `U`. -/
  equiv : Γ(U, ⊤) ≃+*
    ring ⧸ (baseSectionsRing S).ideal.map (algebraMap (baseSectionsRing S) ring)
  /-- Compatibility. -/
  equiv_sourceToBase (a : baseSectionsRing S) :
    equiv ((sourceToBase (overSituation S j)).appTop.hom a) =
      Ideal.Quotient.mk _ (algebraMap (baseSectionsRing S) ring a)

attribute [instance] SmoothLift.commRing SmoothLift.algebra

namespace SmoothLift

variable {S j} (L : SmoothLift S j)

omit [IsAffine S.S.scheme] in
/-- A smooth algebra is flat. -/
theorem flat_algebraMap : (algebraMap (baseSectionsRing S) L.ring).Flat :=
  have := L.smooth
  RingHom.flat_algebraMap_iff.mpr inferInstance

/-- **The divided power ring `(B, IB, γ_B)`**, `γ_B` the extension of `γ` along the flat map
`A → B` of [Stacks, Tag 07H1]. -/
def dividedPowerRing : DividedPowerRing.{u} where
  carrier := L.ring
  ideal := (baseSectionsRing S).ideal.map (algebraMap (baseSectionsRing S) L.ring)
  dividedPowers := DividedPowers.DividedPowerRing.extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat
    (baseSectionsRing S) (algebraMap (baseSectionsRing S) L.ring)
    (Or.inr (Or.inr L.flat_algebraMap))

omit [IsAffine S.S.scheme] in
/-- `A → B` is a divided power morphism for `γ_B`. -/
theorem isDPMorphism_algebraMap :
    DividedPowers.IsDPMorphism (baseSectionsRing S).dividedPowers L.dividedPowerRing.dividedPowers
      (algebraMap (baseSectionsRing S) L.ring) :=
  DividedPowers.DividedPowerRing.isDPMorphism_extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat
    _ _ (Or.inr (Or.inr L.flat_algebraMap))

variable [IsAffine U]

/-- **The object `(B, IB, γ_B)` of `CRIS(Γ(U, ⊤)/A)`**, with structural map
`Γ(U, ⊤) ≅ B/IB`. -/
def thickening :
    DividedPowerThickening.{u, u, u} (affineSituation (overSituation S j)
      (isNilpotent_prime_over S j hp)) where
  ring := L.dividedPowerRing
  fromBase := DividedPowers.DPMorphism.mk' L.isDPMorphism_algebraMap
  prime_nilpotent := by
    change IsNilpotent ((S.p : ℕ) : L.ring)
    rw [← map_natCast (algebraMap (baseSectionsRing S) L.ring)]
    exact hp.map _
  toQuotient := L.equiv.toRingHom
  commutes := RingHom.ext fun a ↦ (L.equiv_sourceToBase a).symm

omit [IsAffine U] [IsAffine S.S.scheme] in
/-- The structural map of the thickening is bijective. -/
theorem bijective_thickening_toQuotient : Function.Bijective (L.thickening hp).toQuotient :=
  L.equiv.bijective

/-- **The object `(U, Spec B, γ_B)` of `CRIS(X/S)`** attached to a smooth lift: its thickened
scheme is `Spec(B/IB) ≅ U`, mapping to `X` through `j`. -/
def object : Thickening S :=
  (overPush S j).obj (specThickeningOfAffine (isNilpotent_prime_over S j hp) (L.thickening hp))

/-- The map of the object to `X`. -/
theorem object_toX :
    (L.object hp).toX = specToX (isNilpotent_prime_over S j hp) (L.thickening hp) ≫ j := rfl

omit [IsAffine S.S.scheme] in
/-- The thickened scheme of the object is `U`. -/
theorem isIso_specToX :
    IsIso (specToX (isNilpotent_prime_over S j hp) (L.thickening hp)) :=
  GlobalCrystallineSituation.isIso_specToX _ _ (L.bijective_thickening_toQuotient hp)

/-- The object lies in `Cris(X/S)` when `j` is an open immersion. -/
instance isOpenImmersion_object_toX [IsOpenImmersion j] : IsOpenImmersion (L.object hp).toX := by
  have := L.isIso_specToX hp
  have : IsOpenImmersion (specToX (isNilpotent_prime_over S j hp) (L.thickening hp)) :=
    IsOpenImmersion.of_isIso _
  rw [object_toX]
  exact IsOpenImmersion.comp (X := Spec _) (Y := U) (Z := S.X) _ j

/-- The ambient scheme of the object is affine. -/
instance isAffine_object_target : IsAffine (L.object hp).thickening.target.scheme := by
  change IsAffine (Spec _)
  infer_instance

/-- The thickened scheme of the object is affine. -/
instance isAffine_object_source : IsAffine (L.object hp).thickening.source := by
  change IsAffine (Spec _)
  infer_instance

end SmoothLift

omit hp in
/-- **Every affine scheme `U` over `X` which is smooth over `S₀` has a smooth lift**: smooth
algebras lift along the surjection `A → Γ(S₀, ⊤)`, whose kernel is the divided power ideal. -/
theorem nonempty_smoothLift [IsAffine U] (hsm : Smooth (j ≫ S.toClosedFiber)) :
    Nonempty (SmoothLift S j) := by
  have : IsAffine (DividedPowerScheme.closedFiber S.S) :=
    isAffine_of_isAffineHom (DividedPowerScheme.closedFiberι S.S)
  let : Algebra ↥(baseSectionsRing S) Γ(DividedPowerScheme.closedFiber S.S, ⊤) :=
    (DividedPowerScheme.closedFiberι S.S).appTop.hom.toAlgebra
  let : Algebra Γ(DividedPowerScheme.closedFiber S.S, ⊤) Γ(U, ⊤) :=
    (j ≫ S.toClosedFiber).appTop.hom.toAlgebra
  have hR : Function.Surjective
      (algebraMap ↥(baseSectionsRing S) Γ(DividedPowerScheme.closedFiber S.S, ⊤)) :=
    (DividedPowerScheme.closedFiberι S.S).app_surjective ⊤ (isAffineOpen_top _)
  have hA₀ : Algebra.Smooth Γ(DividedPowerScheme.closedFiber S.S, ⊤) Γ(U, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp hsm
  obtain ⟨B, _, a, hB, e, he⟩ := Stacks.Smoothing.exists_smooth_lift_of_surjective
    ↥(baseSectionsRing S) Γ(DividedPowerScheme.closedFiber S.S, ⊤) Γ(U, ⊤) hR hA₀
  let := a
  have hker : RingHom.ker
      (algebraMap ↥(baseSectionsRing S) Γ(DividedPowerScheme.closedFiber S.S, ⊤)) =
      (baseSectionsRing S).ideal :=
    ((DividedPowerScheme.ideal_obj_eq_ker_ideal_closedFiberι S.S
      ⟨⊤, isAffineOpen_top _⟩).trans (Scheme.Hom.ker_apply _ _)).symm
  refine ⟨{
    ring := B
    smooth := hB
    equiv := e.trans (Ideal.quotEquivOfEq (by rw [hker]))
    equiv_sourceToBase := fun r ↦ ?_ }⟩
  simp only [RingEquiv.trans_apply]
  change (Ideal.quotEquivOfEq _) (e (algebraMap _ Γ(U, ⊤)
    (algebraMap ↥(baseSectionsRing S) Γ(DividedPowerScheme.closedFiber S.S, ⊤) r))) = _
  rw [he r, Ideal.quotEquivOfEq_mk]

end SmoothLift

end Crystalline.GlobalCrystallineSituation.CechEnvelope
