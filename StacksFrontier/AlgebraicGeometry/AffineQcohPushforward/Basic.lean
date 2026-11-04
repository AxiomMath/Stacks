module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits

/-!
# Direct image along an affine morphism as a module over the pushed-forward structure sheaf

Let `f : X ⟶ S` be a morphism of schemes.  The direct image of an `𝒪_X`-module is a module
over the sheaf of rings `f_* 𝒪_X` on `S`, and restricting scalars along the structure map
`𝒪_S ⟶ f_* 𝒪_X` recovers the usual direct image of `𝒪_X`-modules.  This file sets up that
pair of functors and records the identification, which is an equality of functors, together
with the consequences of Stacks Tag 02KG that the identification makes available.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing` is the pushed-forward sheaf
  of rings `f_* R` of a sheaf of rings `R` along a continuous map.
* `Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules` is the direct image of
  sheaves of modules, regarded as a functor to modules over `f_* R`.

## Main results

* `Stacks.AlgebraicGeometry.AffineQcohPushforward.restrictScalars_pushforwardModules`:
  restricting scalars along `f.toRingCatSheafHom` after `pushforwardModules f` is *equal* to
  `Scheme.Modules.pushforward f`.
* `Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules_unit`: the direct image of
  the structure sheaf is the unit module over `f_* 𝒪_X`, again an equality.
* `Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_restrictScalars_pushforward`:
  for `f` affine and `M` quasi-coherent, the direct image `f_* M` is quasi-coherent *as an
  `𝒪_S`-module*.
* `Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_restrictScalars_pushforwardRing`:
  for `f` affine, `f_* 𝒪_X` is quasi-coherent as an `𝒪_S`-module, i.e. it is a quasi-coherent
  `𝒪_S`-algebra.  This is the hypothesis of Stacks Tag 0H88 in the case at hand.
* `Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_pushforwardModules_of_reflects`:
  the reduction of the first assertion of Stacks Tag 01SB to the non-trivial implication of
  Stacks Tag 0H88.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.pushforward f` is by definition
`SheafOfModules.pushforward f.toRingCatSheafHom`, and `SheafOfModules.pushforward φ` is by
definition the direct image of the underlying presheaf followed by restriction of scalars along
`φ`.  Consequently `pushforwardModules f`, which is the same direct image with `φ` taken to be
the identity of `f_* 𝒪_X`, satisfies
`pushforwardModules f ⋙ SheafOfModules.restrictScalars f.toRingCatSheafHom =
  Scheme.Modules.pushforward f` on the nose; both `restrictScalars_pushforwardModules` and
`pushforwardModules_unit` are proved by `rfl`.  This is what makes the quasi-coherence
statements of Tag 02KG, which are about `Scheme.Modules.pushforward`, say something about
`pushforwardModules`.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.AffineQcohPushforward

/-! ### The pushed-forward sheaf of rings and the direct image over it -/

section Topological

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The pushforward `f_* R` of a sheaf of rings along a continuous map. -/
noncomputable def pushforwardRing :
    Sheaf (Opens.grothendieckTopology Y) RingCat.{u} :=
  ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R

/-- The direct image of sheaves of modules along a continuous map `f`, regarded as a functor to
the sheaves of modules over `f_* R`. -/
noncomputable def pushforwardModules :
    SheafOfModules.{v} R ⥤ SheafOfModules.{v} (pushforwardRing f R) :=
  SheafOfModules.pushforward.{v} (𝟙 (pushforwardRing f R))

end Topological

/-! ### The structure sheaf is quasi-coherent -/

/-- On a scheme isomorphic to a spectrum, the structure sheaf is quasi-coherent. -/
theorem isQuasicoherent_unit_of_isoSpec {Y : Scheme.{u}} {R : CommRingCat.{u}} (e : Y ≅ Spec R) :
    (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
  have _h0 : (SheafOfModules.unit.{u} (Spec R).ringCatSheaf).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  have h1 := Scheme.Modules.isQuasicoherent_restrictFunctor e.hom
    (SheafOfModules.unit.{u} (Spec R).ringCatSheaf)
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (Scheme.Modules.restrictUnitIso e.hom) h1

/-- The structure sheaf of a scheme is quasi-coherent as a module over itself. -/
instance isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
  refine QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens _ fun V ↦ ?_
  exact (SheafOfModules.isQuasicoherent (V : X.Opens).toScheme.ringCatSheaf).prop_of_iso
    (Scheme.Modules.restrictUnitIso (V : X.Opens).ι).symm
    (isQuasicoherent_unit_of_isoSpec V.2.isoSpec)

/-! ### Comparison with the direct image of modules over the structure sheaves -/

section Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Restricting scalars along `f.toRingCatSheafHom` turns the direct image over `f_* 𝒪_X` into
the direct image of `𝒪_X`-modules. -/
theorem restrictScalars_pushforwardModules :
    pushforwardModules.{u} f.base X.ringCatSheaf ⋙
        SheafOfModules.restrictScalars f.toRingCatSheafHom =
      Scheme.Modules.pushforward f :=
  rfl

/-- The direct image of the structure sheaf is the unit module over `f_* 𝒪_X`. -/
theorem pushforwardModules_unit :
    (pushforwardModules.{u} f.base X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) =
      SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf) :=
  rfl

/-- The direct image of a quasi-coherent module along an affine morphism is quasi-coherent as a
module over the structure sheaf of the target.  This is the `𝒪_S`-half of the first assertion
of Stacks Tag 01SB; the content is Stacks Tag 02KG. -/
theorem isQuasicoherent_restrictScalars_pushforward [IsAffineHom f] (M : X.Modules)
    [M.IsQuasicoherent] :
    ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
      ((pushforwardModules.{u} f.base X.ringCatSheaf).obj M)).IsQuasicoherent :=
  AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f M

/-- For an affine morphism `f : X ⟶ S`, the sheaf of rings `f_* 𝒪_X` is quasi-coherent as an
`𝒪_S`-module: it is a quasi-coherent `𝒪_S`-algebra. -/
theorem isQuasicoherent_restrictScalars_pushforwardRing [IsAffineHom f] :
    ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
      (SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf))).IsQuasicoherent :=
  AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f
    (SheafOfModules.unit X.ringCatSheaf)

/-- The quasi-coherence over `f_* 𝒪_X` of a direct image along an affine morphism follows from
the implication of Stacks Tag 0H88 that quasi-coherence over `𝒪_S` of an `f_* 𝒪_X`-module
implies its quasi-coherence over `f_* 𝒪_X`.  This is the exact reduction of the first assertion
of Stacks Tag 01SB to Tag 0H88. -/
theorem isQuasicoherent_pushforwardModules_of_reflects [IsAffineHom f]
    (h : ∀ G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf),
      ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj G).IsQuasicoherent →
        G.IsQuasicoherent)
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforwardModules.{u} f.base X.ringCatSheaf).obj M).IsQuasicoherent :=
  h _ (isQuasicoherent_restrictScalars_pushforward f M)

end Scheme

end Stacks.AlgebraicGeometry.AffineQcohPushforward

end
