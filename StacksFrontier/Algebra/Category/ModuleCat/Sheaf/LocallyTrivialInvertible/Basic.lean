module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOneLocal
public import Mathlib.Geometry.RingedSpace.Basic

/-!
# A sheaf of modules trivial on a covering is invertible

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` and let `L` be a sheaf of
`𝒪`-modules. If `L` is trivial on each member of a covering of the terminal object — that is,
`L|_{X i} ≅ 𝒪|_{X i}` for a family `X` covering the terminal object — then `L` is invertible.

A trivialization `L|_U ≅ 𝒪|_U` is a rank-one dual basis over `U`: its basis section is the one
corresponding to `1`, and its dual coordinate is the trivialization, read as a section of the
dual. In particular a sheaf of modules that is finite locally free of rank one is invertible.

## Main definitions

* `Stacks.SheafOfModules.DualBasisOne.ofIsoUnit`: the rank-one dual basis of a trivialization.

## Main results

* `Stacks.SheafOfModules.isInvertible_of_coversTop_iso_unit`: a sheaf of modules trivial on a
  covering of the terminal object is invertible.
* `Stacks.SheafOfModules.isInvertible_of_isFiniteLocallyFreeOfRank_one`: a sheaf of modules
  that is finite locally free of rank one is invertible.
* `Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one`: the same on a ringed
  space.

## Implementation notes

The ring universe is `max u v` for a site `C : Type u` with `Category.{v} C`, and so is the
module universe, as the internal hom of Tag 03EM requires through `dualSheaf`. On the site of
opens of a topological space `v = 0`, so the restriction is vacuous there.

A section of the unit sheaf of the localized site over an object `V` of `C/U` and a section of
the structure sheaf over `V.left` have the same carrier but different `ModuleCat` indices, and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` is not reducible, so instance search
does not connect them. `unitOneOver` names the section `1` in the spelling the dual-basis fields
use, and the lemmas below are stated in that spelling.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/


@[expose] public section

open CategoryTheory Opposite

universe v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)}
  {L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
  {U : C}

/-- The restriction map of the localized site from its terminal object `Over.mk (𝟙 U)` to an
object `V` of `C/U`. It is the structural map along which a section over `U` restricts. -/
noncomputable def termRestrict (V : (Over U)ᵒᵖ) :
    (op (Over.mk (𝟙 U)) : (Over U)ᵒᵖ) ⟶ V :=
  (Over.homMk V.unop.hom (by simp) : V.unop ⟶ Over.mk (𝟙 U)).op

/-- The unit section of the unit sheaf of the localized site over an object `V` of `C/U`, in
the spelling the dual-basis fields use. -/
noncomputable def unitOneOver (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
      {U : C}
    (V : (Over U)ᵒᵖ) :
    (SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over
      U)).val.obj V :=
  (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op V.unop.left))

namespace IsoUnit

/-- The sections of the structure sheaf form a commutative ring, in the `ModuleCat`-index
spelling. -/
local instance commRingStructureSheafObjLocTriv (V : Cᵒᵖ) :
    CommRing ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj V) :=
  inferInstanceAs (CommRing (𝒪.obj V))

variable (φ : L.over U ≅ SheafOfModules.unit
  ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U))

/-- The section of `L` over `V.left` corresponding to `1` under the trivialization. -/
noncomputable def invUnitOne (V : (Over U)ᵒᵖ) : L.val.obj (op V.unop.left) :=
  (φ.inv.val.app V).hom (unitOneOver 𝒪 h𝒪 V)

/-- Restricting along `termRestrict V` the section over `U` that corresponds to `1` gives the
section over `V` that corresponds to `1`. -/
theorem restrict_invUnitOne (V : (Over U)ᵒᵖ) :
    ((L.over U).val.map (termRestrict V)).hom
        ((φ.inv.val.app (op (Over.mk (𝟙 U)))).hom (unitOneOver 𝒪 h𝒪 _)) =
      (φ.inv.val.app V).hom (unitOneOver 𝒪 h𝒪 V) := by
  have hone : ((SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
    h𝒪).over U)).val.map
      (termRestrict V)).hom (unitOneOver 𝒪 h𝒪 (op (Over.mk (𝟙 U)))) = unitOneOver 𝒪 h𝒪 V := by
    show ((((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.map
      (termRestrict V)).hom
      (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U))) = _
    exact map_one _
  have hnat : (φ.inv.val.app V).hom
        (((SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
          h𝒪).over U)).val.map
          (termRestrict V)).hom (unitOneOver 𝒪 h𝒪 (op (Over.mk (𝟙 U))))) =
      ((L.over U).val.map (termRestrict V)).hom
        ((φ.inv.val.app (op (Over.mk (𝟙 U)))).hom (unitOneOver 𝒪 h𝒪 (op (Over.mk (𝟙 U))))) :=
    PresheafOfModules.naturality_apply φ.inv.val (termRestrict V) _
  rw [← hnat, hone]

/-- Scaling the unit section of the unit sheaf is multiplication. -/
theorem smul_unitOne (V : (Over U)ᵒᵖ)
    (c : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj V) :
    c • unitOneOver 𝒪 h𝒪 V =
      (c : (SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
        h𝒪).over U)).val.obj V) := by
  show c * (1 : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj
    V) = c
  exact mul_one c

/-- The section corresponding to `1` generates: scaling it by `c` gives the section
corresponding to `c`. -/
theorem smul_invUnitOne (V : (Over U)ᵒᵖ)
    (c : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj V) :
    c • (φ.inv.val.app V).hom (unitOneOver 𝒪 h𝒪 V) =
      (φ.inv.val.app V).hom
        (c : (SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
          h𝒪).over U)).val.obj V) := by
  have h := ((φ.inv.val.app V).hom).map_smul c (unitOneOver 𝒪 h𝒪 V)
  rw [← h, smul_unitOne]

/-- The generating property of the section corresponding to `1`, in the spelling of
`DualBasisOne.span`. -/
theorem span_of_isoUnit (V : (Over U)ᵒᵖ) (g : L.val.obj (op V.unop.left)) :
    dualApp ((SheafOfModules.forget _).map φ.hom) V g •
        resSection (L := L) V
          ((φ.inv.val.app (op (Over.mk (𝟙 U)))).hom (unitOneOver 𝒪 h𝒪 _)) = g := by
  have h1 : resSection (L := L) V
        ((φ.inv.val.app (op (Over.mk (𝟙 U)))).hom (unitOneOver 𝒪 h𝒪 _)) = invUnitOne φ V :=
    restrict_invUnitOne φ V
  rw [h1]
  have h2 : dualApp ((SheafOfModules.forget _).map φ.hom) V g • invUnitOne φ V =
      (φ.inv.val.app V).hom ((φ.hom.val.app V).hom g) := smul_invUnitOne φ V _
  rw [h2]
  exact trivialization_inv_hom_apply φ V g

/-- The duality property of the section corresponding to `1`, in the spelling of
`DualBasisOne.eval_self`. -/
theorem evalSelf_of_isoUnit :
    dualEval ((SheafOfModules.forget _).map φ.hom)
      ((φ.inv.val.app (op (Over.mk (𝟙 U)))).hom (unitOneOver 𝒪 h𝒪 _)) = 1 :=
  trivialization_hom_inv_apply φ (op (Over.mk (𝟙 U))) _

end IsoUnit

/-- The rank-one dual basis of `L` over `U` given by a trivialization `φ : L|_U ≅ 𝒪|_U`: the
basis section is the one corresponding to `1`, and the dual coordinate is `φ` itself, read as a
section of the dual sheaf over `U`. -/
noncomputable def DualBasisOne.ofIsoUnit
    (φ : L.over U ≅ SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf
      𝒪 h𝒪).over U)) :
    DualBasisOne 𝒪 h𝒪 L U where
  e := (φ.inv.val.app (op (Over.mk (𝟙 U)))).hom (unitOneOver 𝒪 h𝒪 _)
  lam := (SheafOfModules.forget _).map φ.hom
  span := IsoUnit.span_of_isoUnit φ
  eval_self := IsoUnit.evalSelf_of_isoUnit φ

variable (𝒪 h𝒪)

section Descent

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- A sheaf of modules `L` with a trivialization `L|_{X i} ≅ 𝒪|_{X i}` over each member of a
family `X` covering the terminal object is invertible. -/
theorem isInvertible_of_coversTop_iso_unit
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (φ : ∀ i, L.over (X i) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over (X
        i))) :
    IsInvertible 𝒪 h𝒪 L :=
  isInvertible_of_dualBasisOne 𝒪 h𝒪 hX fun i => DualBasisOne.ofIsoUnit (φ i)

/-- A sheaf of modules trivial on a covering of the terminal object is invertible, with the
trivializations given only up to existence. -/
theorem isInvertible_of_coversTop_nonempty_iso_unit
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (φ : ∀ i, Nonempty (L.over (X i) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over (X
        i)))) :
    IsInvertible 𝒪 h𝒪 L :=
  isInvertible_of_coversTop_iso_unit 𝒪 h𝒪 L hX fun i => (φ i).some

variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- A sheaf of modules that is finite locally free of rank one is invertible. -/
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank L 1] :
    IsInvertible 𝒪 h𝒪 L :=
  have ⟨_, _, hX, φ⟩ :=
    Stacks.InvertibleLocallyFree.exists_coversTop_nonempty_iso_unit_of_isFiniteLocallyFreeOfRank_one
      𝒪 h𝒪 L
  isInvertible_of_coversTop_nonempty_iso_unit 𝒪 h𝒪 L hX φ

end Descent

end Stacks.SheafOfModules

namespace Stacks.RingedSpace

open AlgebraicGeometry TopologicalSpace

/-- A sheaf of modules on a ringed space that is finite locally free of rank one is
invertible. -/
@[stacks 0B8M "locally free of rank one implies invertible"]
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (C := Opens X) (J := Opens.grothendieckTopology X) L 1] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L :=
  @Stacks.SheafOfModules.isInvertible_of_isFiniteLocallyFreeOfRank_one
    (Opens X) _ (Opens.grothendieckTopology X) X.sheaf.obj
    (structureSheaf X.sheaf).property _ _ _ _ L h

end Stacks.RingedSpace

end
