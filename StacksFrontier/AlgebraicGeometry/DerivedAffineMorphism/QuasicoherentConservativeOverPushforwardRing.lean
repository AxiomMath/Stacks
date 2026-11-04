module

public import StacksFrontier.AlgebraicGeometry.AffineQcohUnit.Unit
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.FlatOverPushforwardRing
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardOverRingConservative
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.ReflectsIsomorphismsAffineHom

/-!
# `Φ` and `Lg^*` are both conservative on the quasi-coherent derived categories

Let `f : X ⟶ S` be an affine morphism of schemes, `Φ : D(𝒪_X) ⥤ D(f_* 𝒪_X)` the functor of
[Stacks, Tag 0AVW] and `Lg^* : D(f_* 𝒪_X) ⥤ D(𝒪_X)` its left adjoint of
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/FlatOverPushforwardRing.lean`.  This file
proves that each of the two detects vanishing, and that `Φ` reflects isomorphisms, on objects
with quasi-coherent cohomology.

For `Φ` this is [Stacks, Tag 08I8] read over `f_* 𝒪_X`: restriction of scalars loses no
information, so the question is the same question for `Rf_*`
(`isZero_homologyFunctor_derivedPushforwardOverRing_iff`,
`isIso_derivedPushforwardOverRing_map_iff`), where it is answered by
`AlgebraicGeometry.AnyModel.isZero_homologyFunctor_derivedPushforward_iff_of_isAffineHom` and
`AlgebraicGeometry.AnyModel.isIso_of_isIso_derivedPushforward_map_of_isAffineHom`.

For `Lg^*` it is the abelian statement that `g^*` is conservative on quasi-coherent modules,
carried across `homologyDerivedPullbackOverRingIso`: `H^i(Lg^* M) ≅ g^*(H^i M)`, and a
quasi-coherent `f_* 𝒪_X`-module killed by `g^*` is killed by `g_* g^*`, which it is isomorphic
to by the unit of [Stacks, Tag 01SB].

## Main results

All in the namespace `Stacks.AlgebraicGeometry.DerivedAffinePushforward`.

* `isZero_pullbackModules_obj_iff_of_isQuasicoherent` — `g^*` is conservative on quasi-coherent
  modules.
* `isZero_homologyFunctor_derivedPullbackOverRing_iff` and
  `isZero_derivedPullbackOverRing_obj_iff` — `Lg^*` detects vanishing on `D_QCoh(f_* 𝒪_X)`.
* `isZero_homologyFunctor_derivedPushforwardOverRing_iff_of_isAffineHom` and
  `isZero_derivedPushforwardOverRing_obj_iff_of_isAffineHom` — `Φ` detects vanishing on
  `D_QCoh(𝒪_X)`.
* `isIso_of_isIso_derivedPushforwardOverRing_map_of_isAffineHom` — **`Φ` reflects isomorphisms on
  `D_QCoh(𝒪_X)`**, which is [Stacks, Tag 08I8] over `f_* 𝒪_X`.

## Implementation notes

*What these do and do not buy for the equivalence clause of [Stacks, Tag 0AVW].*  They are the
two conservativity inputs the final assembly consumes, and they are not by themselves enough.
The adjunction identities make `Φ(ε_K)` a split epimorphism and `Lg^*(η_M)` a split
monomorphism, so each of "the unit is invertible" and "the counit is invertible" follows from
the other through conservativity — a circle.  Breaking it needs the cohomological input: a
natural isomorphism `H^i ∘ Φ ≅ g_* ∘ H^i` on `D_QCoh(𝒪_X)`, which is the vanishing of higher
direct images along an affine morphism ([Stacks, Tag 01XC]) together with the bounds of
[Stacks, Tag 08D5].  Conservativity cannot replace it: a split epimorphism in a distinguished
triangle exhibits `Φ` as a retract, not as fully faithful, and a retract is exactly what a
formal argument from the adjunction identities can give.

*The additivity of `g^*` is passed across a spelling seam.*  `g^*` is
`RingedSpaceModuleAdjunction.modulePullback (toPushforwardStructureSpace f)` and
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules f` interchangeably — the two are
equal by `modulePullback_toPushforwardStructureSpace`, which holds by `rfl` — but instance search
does not cross the equality, so the additivity registered for the first spelling is handed to the
second by `inferInstanceAs`.

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 08I8](https://stacks.math.columbia.edu/tag/08I8)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.AffineQcohEquivalence

universe w u

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### `g^*` is conservative on quasi-coherent modules -/

/-- **`g^*` is conservative on quasi-coherent modules.**  A quasi-coherent `f_* 𝒪_X`-module `G`
is a zero object exactly when `g^* G` is.

One direction is additivity.  For the other, the unit `G ⟶ g_* g^* G` of [Stacks, Tag 01SB] is
invertible at a quasi-coherent `G` for an affine morphism, and `g_*` carries a zero object to a
zero object. -/
theorem isZero_pullbackModules_obj_iff_of_isQuasicoherent [IsAffineHom f]
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) (hG : G.IsQuasicoherent) :
    IsZero ((pullbackModules f).obj G) ↔ IsZero G := by
  have : (pullbackModules f).Additive :=
    inferInstanceAs (RingedSpaceModuleAdjunction.modulePullback
      (toPushforwardStructureSpace f)).Additive
  refine ⟨fun h => ?_, fun h => Functor.map_isZero _ h⟩
  have := Stacks.AlgebraicGeometry.AffineQcohUnit.isIso_unit_app_of_isQuasicoherent f G hG
  exact (Functor.map_isZero (pushforwardModules.{u} f.base X.ringCatSheaf) h).of_iso
    (asIso ((pullbackPushforwardAdjunction f).unit.app G))

/-! ### `Lg^*` detects vanishing on `D_QCoh(f_* 𝒪_X)` -/

section Pullback

variable [IsAffineHom f]
  [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]

/-- **`H^i(Lg^* M)` vanishes exactly when `H^i(M)` does**, for `M` with quasi-coherent cohomology
over `f_* 𝒪_X`: the first is `g^*` of the second by `homologyDerivedPullbackOverRingIso`, and
`g^*` is conservative on quasi-coherent modules. -/
theorem isZero_homologyFunctor_derivedPullbackOverRing_iff
    (M : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj M).IsQuasicoherent)
    (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
        ((derivedPullbackOverRing.{w} f).obj M)) ↔
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj M) :=
  (Iso.isZero_iff (homologyDerivedPullbackOverRingIso.{w} f i M)).trans
    (isZero_pullbackModules_obj_iff_of_isQuasicoherent f _ (hcoh i))

/-- **`Lg^*` is conservative on `D_QCoh(f_* 𝒪_X)`**: `Lg^* M` is a zero object exactly when `M`
is, both being detected on cohomology. -/
theorem isZero_derivedPullbackOverRing_obj_iff
    (M : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj M).IsQuasicoherent) :
    IsZero ((derivedPullbackOverRing.{w} f).obj M) ↔ IsZero M := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology,
    DerivedCategory.isZero_iff_forall_isZero_homology]
  exact forall_congr' fun i => isZero_homologyFunctor_derivedPullbackOverRing_iff.{w} f M hcoh i

end Pullback

/-! ### `Φ` detects vanishing and reflects isomorphisms on `D_QCoh(𝒪_X)` -/

section Pushforward

variable [IsAffineHom f]
  [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-- **`H^i(Φ E)` vanishes exactly when `H^i(E)` does**, for `E` with quasi-coherent cohomology:
restriction of scalars turns the question into the same question for `Rf_*`, where it is the
vanishing criterion for an affine morphism. -/
theorem isZero_homologyFunctor_derivedPushforwardOverRing_iff_of_isAffineHom
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj
        ((derivedPushforwardOverRing.{w} f).obj E)) ↔
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj E) :=
  (isZero_homologyFunctor_derivedPushforwardOverRing_iff.{w} f E i).trans
    (AlgebraicGeometry.AnyModel.isZero_homologyFunctor_derivedPushforward_iff_of_isAffineHom.{w}
      f E hcoh i)

/-- **`Φ` is conservative on `D_QCoh(𝒪_X)`**: `Φ E` is a zero object exactly when `E` is. -/
theorem isZero_derivedPushforwardOverRing_obj_iff_of_isAffineHom
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) :
    IsZero ((derivedPushforwardOverRing.{w} f).obj E) ↔ IsZero E := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology,
    DerivedCategory.isZero_iff_forall_isZero_homology]
  exact forall_congr' fun i =>
    isZero_homologyFunctor_derivedPushforwardOverRing_iff_of_isAffineHom.{w} f E hcoh i

/-- **[Stacks, Tag 08I8] over `f_* 𝒪_X`: `Φ` reflects isomorphisms on `D_QCoh(𝒪_X)`.**  A map of
complexes of `𝒪_X`-modules with quasi-coherent cohomology whose image under `Φ` is invertible is
itself invertible.

`Φ α` is invertible exactly when `Rf_* α` is, by `isIso_derivedPushforwardOverRing_map_iff`, and
for `Rf_*` this is the tag itself. -/
theorem isIso_of_isIso_derivedPushforwardOverRing_map_of_isAffineHom
    {E F : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)}
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent)
    (hF : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj F).IsQuasicoherent)
    (α : E ⟶ F) (h : IsIso ((derivedPushforwardOverRing.{w} f).map α)) : IsIso α :=
  AlgebraicGeometry.AnyModel.isIso_of_isIso_derivedPushforward_map_of_isAffineHom.{w} f hE hF α
    ((isIso_derivedPushforwardOverRing_map_iff.{w} f α).1 h)

end Pushforward

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

end
