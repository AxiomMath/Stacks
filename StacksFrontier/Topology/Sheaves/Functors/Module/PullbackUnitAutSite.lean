module

public import StacksFrontier.Topology.Sheaves.Functors.Module.UnitEndomorphismSections

/-!
# Pullback of an automorphism of the free sheaf of rank one, on a ringed site

Let `φ : S ⟶ F_* R` be a morphism of sheaves of rings over a continuous functor of sites
`F : C ⥤ D`, and suppose the pushforward of sheaves of modules along `φ` has a left adjoint.
Pulling an automorphism `a` of the free sheaf of `S`-modules of rank one back along `φ` and
reading the result through the identification `φ^* 𝒪 ≅ 𝒪` gives an automorphism
`pullbackUnitAut φ a` of the free sheaf of `R`-modules of rank one, and when `φ` acts on
sections as the `p`-th power map it is the `p`-fold composite of `a`:

`pullbackUnitAut φ a = a ^ p`.

This is the Frobenius half of the classical computation `F^* L ≅ L^{⊗ p}` for an invertible
sheaf in characteristic `p`, at the generality in which the computation is used. The same
statement for a morphism of ringed spaces is
`AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius`
(`StacksFrontier/AlgebraicGeometry/Variety/Frobenius/PullbackUnitAut.lean`); the content here is
that neither the ringed space nor the absolute Frobenius is used. What is used is that the
functor of sites is the identity, so that the two values at `1` compared below are values of
the *same* section — and that is why the exponent statement sits in its own section, with `F`
specialized to `𝟭 C`, rather than at the generality of the rest of the file.

The generality matters for a reason that is not cosmetic. The transition cocycle of an
invertible sheaf is read on the opens of a trivializing cover, i.e. on a *localized* site, and
the Frobenius of a localized ringed site is not a morphism of ringed spaces. The exponent
statement below applies there verbatim, because the identity functor of the localized site is
continuous, cocontinuous and final, and the restricted structure-sheaf endomorphism still acts
on sections by `g ↦ g ^ p`.

## Main definitions

* `Stacks.SheafOfModules.pullbackUnitIso`: the identification `φ^* 𝒪 ≅ 𝒪`, which is
  `SheafOfModules.pullbackObjUnitToUnit` made invertible by finality of `F`.
* `Stacks.SheafOfModules.pullbackUnitAut`: the automorphism of the free sheaf of `R`-modules of
  rank one obtained from one of the free sheaf of `S`-modules of rank one by pullback,
  conjugated by `Stacks.SheafOfModules.pullbackUnitIso`.

## Main results

* `Stacks.SheafOfModules.pullbackUnitAut_eq_iff`: the pullback is characterized by the
  transposed square `a ≫ φ = φ ≫ φ_* b`, in which `φ` acts on sections as the given morphism
  of sheaves of rings.
* `Stacks.SheafOfModules.pullbackUnitAut_eq_iff_val_app_one`: that square is a single equation
  between values at `1`, with no sheafification and no adjunction left in it.
* `Stacks.SheafOfModules.pullbackUnitAut_structureSheafHom`: for a morphism of ringed spaces
  this is `RingedSpaceModuleAdjunction.pullbackUnitAut`, by `rfl`.
* `Stacks.SheafOfModules.pullbackUnitAut_eq_autPow`: **an endomorphism of the structure sheaf
  acting on sections as the `p`-th power map pulls an automorphism back to its `p`-fold
  composite.**
* `Stacks.SheafOfModules.unitAutValue_pullbackUnitAut`: the same, read as an equation between
  units of a ring of sections, which is the spelling in which transition data of an invertible
  sheaf is recorded.

## Implementation notes

The proof of the characterization is one transposition across the adjunction, already available
at this generality as `SheafOfModules.pullback_map_unit_comm_iff`
(`StacksFrontier/Topology/Sheaves/Functors/Module/PullbackUnitEndomorphism.lean`), followed by
`Stacks.SheafOfModules.comm_unitToPushforwardObjUnit_iff`, which reduces the square to values
at `1`. Nothing about sheafification or about the construction of the left adjoint enters.

**Instance resolution does not cross the identity functor, and the exponent statement is where
that bites.** `pullbackUnitAut_eq_autPow` is stated with `F := 𝟭 C`, while a consumer arriving
from a ringed space has `F := opensMap f`. For the absolute Frobenius those are definitionally
equal — `Stacks.Frobenius.absoluteFrobenius_preimage` — so the *statement* elaborates, but
`SheafOfModules.pushforward` takes the functor as an implicit argument, so the instance
`(SheafOfModules.pushforward φ).IsRightAdjoint` that instance search is asked for is the one at
the `𝟭 C` spelling, and the one the library provides
(`RingedSpaceModuleAdjunction.pushforward_structureSheafHom_isRightAdjoint`) is the one at the
`opensMap f` spelling. Search runs at reducible transparency and does not identify them, and
because the functor is implicit the two unsolved goals *print identically*. The crossing is
`inferInstanceAs` at the `𝟭` spelling, which is checked at default transparency; on
the absolute Frobenius it recovers
`AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius` from the theorem below.

## References

* [Stacks Project, Tag 0CD5](https://stacks.math.columbia.edu/tag/0CD5)
* [Stacks Project, Tag 03SM](https://stacks.math.columbia.edu/tag/03SM)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u₁ u₂ u

namespace Stacks.SheafOfModules

section Pullback

variable {C : Type u₁} [Category C] {D : Type u₂} [Category D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [F.IsContinuous J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint] [F.Final]

/-- **The pullback of the free sheaf of modules of rank one is the free sheaf of modules of rank
one**, `φ^* 𝒪 ≅ 𝒪`. The morphism is `SheafOfModules.pullbackObjUnitToUnit φ`, the transpose of
the morphism of sheaves of rings itself; it is invertible because `F` is final. -/
def pullbackUnitIso :
    (_root_.SheafOfModules.pullback.{u} φ).obj (_root_.SheafOfModules.unit S) ≅
      _root_.SheafOfModules.unit R :=
  asIso (_root_.SheafOfModules.pullbackObjUnitToUnit.{u} φ)

/-- The forward morphism of `Stacks.SheafOfModules.pullbackUnitIso φ` is
`SheafOfModules.pullbackObjUnitToUnit φ`. -/
theorem pullbackUnitIso_hom :
    (pullbackUnitIso φ).hom = _root_.SheafOfModules.pullbackObjUnitToUnit.{u} φ := rfl

/-- **The pullback of an automorphism of the free sheaf of modules of rank one**, conjugated by
the identification `φ^* 𝒪 ≅ 𝒪`. -/
def pullbackUnitAut (a : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S) :
    _root_.SheafOfModules.unit R ≅ _root_.SheafOfModules.unit R :=
  (pullbackUnitIso φ).symm ≪≫ (_root_.SheafOfModules.pullback.{u} φ).mapIso a ≪≫
    pullbackUnitIso φ

/-- The forward morphism of `Stacks.SheafOfModules.pullbackUnitAut φ a` is the pullback of
`a.hom` conjugated by `Stacks.SheafOfModules.pullbackUnitIso φ`. -/
theorem pullbackUnitAut_hom
    (a : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S) :
    (pullbackUnitAut φ a).hom = (pullbackUnitIso φ).inv ≫
      ((_root_.SheafOfModules.pullback.{u} φ).map a.hom ≫ (pullbackUnitIso φ).hom) := rfl

/-- **`Stacks.SheafOfModules.pullbackUnitAut` is characterized by the transposed square.** `b`
is the pullback of `a` exactly when `a ≫ φ` and `φ ≫ φ_* b` agree, an equation between
morphisms `𝒪_S ⟶ φ_* 𝒪_R` in which `φ` acts on sections as the given morphism of sheaves of
rings. -/
theorem pullbackUnitAut_eq_iff
    (a : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S)
    (b : _root_.SheafOfModules.unit R ≅ _root_.SheafOfModules.unit R) :
    pullbackUnitAut φ a = b ↔
      a.hom ≫ _root_.SheafOfModules.unitToPushforwardObjUnit φ =
        _root_.SheafOfModules.unitToPushforwardObjUnit φ ≫
          (_root_.SheafOfModules.pushforward.{u} φ).map b.hom := by
  refine Iff.trans ?_ (_root_.SheafOfModules.pullback_map_unit_comm_iff φ a.hom b.hom)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : (pullbackUnitIso φ).inv ≫
        ((_root_.SheafOfModules.pullback.{u} φ).map a.hom ≫ (pullbackUnitIso φ).hom) = b.hom :=
      (pullbackUnitAut_hom φ a).symm.trans (congrArg Iso.hom h)
    exact (Iso.hom_inv_id_assoc (pullbackUnitIso φ) _).symm.trans
      (congrArg (fun z => (pullbackUnitIso φ).hom ≫ z) h')
  · exact Iso.ext ((pullbackUnitAut_hom φ a).trans
      ((congrArg (fun z => (pullbackUnitIso φ).inv ≫ z) h).trans (Iso.inv_hom_id_assoc _ _)))

/-- **The pullback of an automorphism of the free sheaf of rank one is computed by one equation
on sections.** `b` is the pullback of `a` exactly when the image under `φ` of the value of `a`
at `1` is the value of `b` at `1`, on every object of the site. -/
theorem pullbackUnitAut_eq_iff_val_app_one
    (a : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S)
    (b : _root_.SheafOfModules.unit R ≅ _root_.SheafOfModules.unit R) :
    pullbackUnitAut φ a = b ↔
      ∀ X : Cᵒᵖ, φ.hom.app X (a.hom.val.app X (1 : S.obj.obj X)) =
        b.hom.val.app (F.op.obj X) (1 : R.obj.obj (F.op.obj X)) :=
  (pullbackUnitAut_eq_iff φ a b).trans (comm_unitToPushforwardObjUnit_iff φ a.hom b.hom)

end Pullback

section RingedSpace

open AlgebraicGeometry RingedSpaceModuleAdjunction TopologicalSpace

/-- **The bridge to the ringed-space spelling.** For a morphism of ringed spaces the
construction above is `RingedSpaceModuleAdjunction.pullbackUnitAut`, on the nose:
`modulePullback f` is `SheafOfModules.pullback (structureSheafHom f)` and
`modulePullbackObjUnitIso f` is `Stacks.SheafOfModules.pullbackUnitIso (structureSheafHom f)`,
both by definition. Finality of the inverse-image functor on opens is a theorem rather than an
instance in this library — `CategoryTheory.final_of_representablyFlat` — so it is taken as an
instance argument here. -/
theorem pullbackUnitAut_structureSheafHom {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [(opensMap f).Final]
    (a : _root_.SheafOfModules.unit (structureSheafRing Y) ≅
      _root_.SheafOfModules.unit (structureSheafRing Y)) :
    pullbackUnitAut (structureSheafHom f) a =
      RingedSpaceModuleAdjunction.pullbackUnitAut f a := rfl

end RingedSpace

section Power

variable {C : Type u₁} [Category C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}
  (φ : S ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{u} J J).obj S)
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint] (p : ℕ)

/-- **An endomorphism of the structure sheaf acting on sections as the `p`-th power map pulls an
automorphism of the free sheaf of rank one back to its `p`-fold composite.**

Both sides of the equation on values at `1` supplied by
`Stacks.SheafOfModules.pullbackUnitAut_eq_iff_val_app_one` are `r ^ p`: on the left by
hypothesis, on the right by `Stacks.SheafOfModules.unitAut_autPow_val_app_one`. The two indices
in that equation are the *same* object of the site, which is what restricts this to the identity
functor; for a functor moving the objects the statement would need the comparison of the two
sections as well. -/
theorem pullbackUnitAut_eq_autPow
    (hφ : ∀ (X : Cᵒᵖ) (r : S.obj.obj X), φ.hom.app X r = r ^ p)
    (a : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S) :
    pullbackUnitAut φ a = a.autPow p :=
  (pullbackUnitAut_eq_iff_val_app_one φ a _).2 fun X =>
    (hφ X _).trans (unitAut_autPow_val_app_one a X _ rfl p).symm

/-- **The `p`-th power formula in the unit-of-a-ring spelling.** The unit of the ring of sections
attached to `φ^* a` is the `p`-th power of the unit attached to `a`. This is the form a
transition-cocycle comparison consumes, since the transition data of an invertible sheaf is
recorded as units of rings of sections rather than as automorphisms of the free sheaf of rank
one. -/
theorem unitAutValue_pullbackUnitAut
    (hφ : ∀ (X : Cᵒᵖ) (r : S.obj.obj X), φ.hom.app X r = r ^ p)
    (a : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S) (X : Cᵒᵖ) :
    unitAutValue (pullbackUnitAut φ a) X = unitAutValue a X ^ p :=
  (congrArg (fun e => unitAutValue e X) (pullbackUnitAut_eq_autPow φ p hφ a)).trans
    (unitAutValue_autPow a X p)

end Power

end Stacks.SheafOfModules

end
