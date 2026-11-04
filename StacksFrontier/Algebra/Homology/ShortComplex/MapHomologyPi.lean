module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# `mapHomologyIso` is compatible with `homologyπ`

Let `S : ShortComplex C` and let `F : C ⥤ D` be a functor preserving zero morphisms and the
left homology of `S`.  Mathlib provides the two comparison isomorphisms
`CategoryTheory.ShortComplex.mapCyclesIso` and `CategoryTheory.ShortComplex.mapHomologyIso`,
and records that `mapCyclesIso` is compatible with `iCycles`
(`CategoryTheory.ShortComplex.mapCyclesIso_hom_iCycles`) and that `mapHomologyIso` is natural
(`CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality`), but nothing relating the two
isomorphisms to the projection `CategoryTheory.ShortComplex.homologyπ`.  This file supplies that
missing square.

## Main results

* `CategoryTheory.ShortComplex.homologyπ_comp_mapHomologyIso_hom`: the square
  `(S.map F).homologyπ ≫ (S.mapHomologyIso F).hom = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ`.
* `CategoryTheory.ShortComplex.mapCyclesIso_inv_comp_homologyπ`,
  `CategoryTheory.ShortComplex.π_comp_mapHomologyIso_inv`: the two inverted forms.

## Implementation notes

`S.mapCyclesIso F` is `(S.leftHomologyData.map F).cyclesIso` by definition and `S.mapHomologyIso F`
is `(S.homologyData.left.map F).homologyIso` by definition, so the two are expressed through
*different* left homology data of `S`.  Reading both through `S.leftHomologyData` — via
`CategoryTheory.ShortComplex.LeftHomologyData.mapHomologyIso_eq` and the simp lemma
`CategoryTheory.ShortComplex.LeftHomologyData.homologyIso_leftHomologyData` — makes the cycles
halves agree syntactically, and what is left is `S.leftHomologyData.π ≫ S.leftHomologyIso.hom`
against `S.homologyπ`, which is a definitional unfolding of
`CategoryTheory.ShortComplex.homologyπ` and `CategoryTheory.ShortComplex.leftHomologyπ`.

This is Mathlib-level infrastructure about Mathlib-only notions and belongs upstream, next to
`CategoryTheory.ShortComplex.mapCyclesIso_hom_iCycles` in
`Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The comparison isomorphism `S.mapHomologyIso F : (S.map F).homology ≅ F.obj S.homology` is
compatible with the projection `homologyπ` from cycles to homology and with the comparison
isomorphism `S.mapCyclesIso F : (S.map F).cycles ≅ F.obj S.cycles`. -/
@[reassoc]
lemma homologyπ_comp_mapHomologyIso_hom [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  have hiso : S.leftHomologyData.homologyIso.inv = S.leftHomologyIso.hom :=
    congrArg Iso.inv (LeftHomologyData.homologyIso_leftHomologyData S)
  have e : (S.mapHomologyIso F).hom =
      (S.leftHomologyData.map F).homologyIso.hom ≫ F.map S.leftHomologyIso.hom :=
    (congrArg Iso.hom (S.leftHomologyData.mapHomologyIso_eq F)).trans
      (congrArg (fun g => (S.leftHomologyData.map F).homologyIso.hom ≫ F.map g) hiso)
  calc (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom
      = (S.map F).homologyπ ≫
          (S.leftHomologyData.map F).homologyIso.hom ≫ F.map S.leftHomologyIso.hom :=
        congrArg (fun g => (S.map F).homologyπ ≫ g) e
    _ = ((S.map F).homologyπ ≫ (S.leftHomologyData.map F).homologyIso.hom) ≫
          F.map S.leftHomologyIso.hom := (assoc _ _ _).symm
    _ = ((S.leftHomologyData.map F).cyclesIso.hom ≫ (S.leftHomologyData.map F).π) ≫
          F.map S.leftHomologyIso.hom :=
        congrArg (fun g => g ≫ F.map S.leftHomologyIso.hom)
          (LeftHomologyData.homologyπ_comp_homologyIso_hom (S.map F)
            (S.leftHomologyData.map F))
    _ = (S.leftHomologyData.map F).cyclesIso.hom ≫
          (S.leftHomologyData.map F).π ≫ F.map S.leftHomologyIso.hom := assoc _ _ _
    _ = (S.leftHomologyData.map F).cyclesIso.hom ≫
          F.map S.leftHomologyπ ≫ F.map S.leftHomologyIso.hom :=
        congrArg
          (fun g => (S.leftHomologyData.map F).cyclesIso.hom ≫
            g ≫ F.map S.leftHomologyIso.hom)
          (LeftHomologyData.map_π S.leftHomologyData F)
    _ = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ :=
        congrArg (fun g => (S.leftHomologyData.map F).cyclesIso.hom ≫ g)
          (F.map_comp S.leftHomologyπ S.leftHomologyIso.hom).symm

/-- The inverse form of `ShortComplex.mapCyclesIso_hom_iCycles`: the comparison isomorphism
`S.mapCyclesIso F` identifies the inclusion of the cycles of `S.map F` with the image under `F`
of the inclusion of the cycles of `S`. -/
@[reassoc]
lemma mapCyclesIso_inv_comp_iCycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [← mapCyclesIso_hom_iCycles S F, Iso.inv_hom_id_assoc]

/-- The inverse form of `ShortComplex.homologyπ_comp_mapHomologyIso_hom`, on the cycles side. -/
@[reassoc]
lemma mapCyclesIso_inv_comp_homologyπ [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      F.map S.homologyπ := by
  rw [homologyπ_comp_mapHomologyIso_hom, Iso.inv_hom_id_assoc]

/-- The inverse form of `ShortComplex.homologyπ_comp_mapHomologyIso_hom`, on the homology side. -/
@[reassoc]
lemma π_comp_mapHomologyIso_inv [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  rw [← cancel_mono (S.mapHomologyIso F).hom, assoc, assoc, Iso.inv_hom_id, comp_id,
    homologyπ_comp_mapHomologyIso_hom, Iso.inv_hom_id_assoc]

end ShortComplex

end CategoryTheory

end
