module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystallineDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Basic

/-!
# The divided power ring of sections of an object of `CRIS(X/S)`, and the affine objects

Fix a global crystalline situation `(p, (S, I, γ), X)`.  For an object `(U, T, δ)` of
`CRIS(X/S)`, the global sections `Γ(T, 𝒪_T)` of its ambient scheme form a divided power ring, with
the divided powers `δ` on the sections of the divided power ideal
(`Crystalline.GlobalCrystallineSituation.sectionsDPRing`), and an algebra over
`A = Γ(S, 𝒪_S)` through the structure morphism.  A morphism of `CRIS(X/S)` induces a divided power
morphism of `A`-algebras between them (`sectionsDPRingMap`).

These are the rings over which the value of a crystal on an affine object carries its connection
in the spelling `Crystalline.DeRhamPair` of the de Rham complexes of modules with integrable
connection; `AffineCris S` is the full subcategory of `Cris(X/S)` of the objects with affine
ambient scheme, on which those connections live.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.sectionsDPRing` — `(Γ(T, 𝒪_T), Γ(T, J), δ)`.
* `Crystalline.GlobalCrystallineSituation.sectionsDPRingMap` — the divided power morphism of
  `A`-algebras induced by a morphism of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.AffineCris` — the objects of `Cris(X/S)` with affine
  ambient scheme.

## References

* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-- **The divided power ring of global sections of the ambient scheme of an object of
`CRIS(X/S)`**: `Γ(T, 𝒪_T)` with the divided powers `δ` of the object on the global sections of its
divided power ideal. -/
def sectionsDPRing (T : Thickening S) : DividedPowerRing.{u} :=
  DividedPowerRing.of Γ(T.thickening.target.scheme, ⊤) _ (crysDividedPowers S T)

/-- The underlying ring of `sectionsDPRing` is `Γ(T, 𝒪_T)`. -/
theorem sectionsDPRing_carrier (T : Thickening S) :
    (sectionsDPRing S T : Type u) = Γ(T.thickening.target.scheme, ⊤) := rfl

/-- The divided powers of `sectionsDPRing` are those of the object. -/
theorem sectionsDPRing_dividedPowers (T : Thickening S) :
    HEq (sectionsDPRing S T).dividedPowers (crysDividedPowers S T) := HEq.rfl

/-- `Γ(T, 𝒪_T)` is an algebra over `A = Γ(S, 𝒪_S)` through the structure morphism. -/
instance algebraSectionsDPRing (T : Thickening S) :
    Algebra Γ(S.S.scheme, ⊤) (sectionsDPRing S T) :=
  (crysBaseAppLE S T).hom.toAlgebra

/-- The algebra map of `sectionsDPRing` is the map on global sections of the structure
morphism. -/
theorem algebraMap_sectionsDPRing (T : Thickening S) (a : Γ(S.S.scheme, ⊤)) :
    algebraMap Γ(S.S.scheme, ⊤) (sectionsDPRing S T) a = crysBaseAppLE S T a := rfl

variable {S}

/-- **The divided power morphism of `A`-algebras induced by a morphism of `CRIS(X/S)`**: the map on
global sections of the ambient schemes. -/
def sectionsDPRingMap {T T' : Thickening S} (k : T ⟶ T') :
    (sectionsDPRing S T' : Type u) →ₐ[Γ(S.S.scheme, ⊤)] (sectionsDPRing S T : Type u) where
  toRingHom := k.targetHom.hom.appTop.hom
  commutes' a := by
    change k.targetHom.hom.appTop (crysBaseAppLE S T' a) = crysBaseAppLE S T a
    exact (congrArg (fun φ : Γ(S.S.scheme, ⊤) ⟶ Γ(T.thickening.target.scheme, ⊤) ↦ φ a)
      (crysBaseAppLE_fac S k)).symm

/-- The underlying ring map of `sectionsDPRingMap` is the map on global sections. -/
theorem sectionsDPRingMap_apply {T T' : Thickening S} (k : T ⟶ T')
    (b : Γ(T'.thickening.target.scheme, ⊤)) :
    sectionsDPRingMap k b = k.targetHom.hom.appTop b := rfl

/-- `sectionsDPRingMap` is a divided power morphism. -/
theorem isDPMorphism_sectionsDPRingMap {T T' : Thickening S} (k : T ⟶ T') :
    DividedPowers.IsDPMorphism (sectionsDPRing S T').dividedPowers
      (sectionsDPRing S T).dividedPowers (sectionsDPRingMap k).toRingHom :=
  k.targetHom.compatible ⊤

/-- `sectionsDPRingMap` of an identity is the identity. -/
theorem sectionsDPRingMap_id (T : Thickening S) :
    sectionsDPRingMap (𝟙 T) = AlgHom.id _ _ := by
  ext b
  change (𝟙 T : T ⟶ T).targetHom.hom.appTop b = b
  rfl

/-- `sectionsDPRingMap` is contravariantly functorial. -/
theorem sectionsDPRingMap_comp {T T' T'' : Thickening S} (k : T ⟶ T') (k' : T' ⟶ T'') :
    sectionsDPRingMap (k ≫ k') = (sectionsDPRingMap k).comp (sectionsDPRingMap k') := by
  ext b
  change (k ≫ k').targetHom.hom.appTop b = k.targetHom.hom.appTop (k'.targetHom.hom.appTop b)
  rfl

variable (S)

/-- **The objects of `Cris(X/S)` with affine ambient scheme**, as a full subcategory. -/
abbrev AffineCris : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun T : CrystallineThickening S ↦ IsAffine T.obj.thickening.target.scheme)

/-- The ambient scheme of an object of `AffineCris S` is affine. -/
instance isAffine_affineCris_target (T : AffineCris S) :
    IsAffine T.obj.obj.thickening.target.scheme := T.property

/-- The inclusion of `AffineCris S` into `CRIS(X/S)`. -/
abbrev AffineCris.ι : AffineCris S ⥤ Thickening S :=
  ObjectProperty.ι _ ⋙ CrystallineThickening.ι S

end Crystalline.GlobalCrystallineSituation
