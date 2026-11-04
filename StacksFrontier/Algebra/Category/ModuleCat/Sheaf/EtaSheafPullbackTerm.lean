module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafIdealInclSucc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackInclInt
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback

/-!
# The degreewise comparison of décalages under a flat pullback

For a flat morphism of ringed spaces `f : X ⟶ Y`, an invertible ideal sheaf `I` with inclusion
`ι` and a cochain complex `F` of sheaves of `𝒪_Y`-modules, the pullback of the degree-`n` term of
`η_I F` is identified with the degree-`n` term of `η_{f^*I} (f^*F)`.

## Main definitions

* `Stacks.IdealTorsion.Eta.pullbackComplex`: The termwise pullback of a cochain complex of
  sheaves of modules.
* `Stacks.IdealTorsion.Eta.pullbackEtaTermIso`: The isomorphism between the pullback of the
  degree-`n` term of `η_I F` and the degree-`n` term of `η_{f^*I} (f^*F)`.

## Main results

* `Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl`: The pullback of an ideal inclusion along a
  flat morphism is a monomorphism.
* `Stacks.IdealTorsion.Eta.map_idealPowerIncl`: The interchange of a pullback with an integer
  ideal power respects the inclusion of consecutive ideal powers.
* `Stacks.IdealTorsion.Eta.pullbackEtaTermIso_hom_fst`,
  `Stacks.IdealTorsion.Eta.pullbackEtaTermIso_hom_snd`: The projections of the degreewise
  comparison.
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open RingedSpaceModuleAdjunction (modulePullbackObjUnitIso)

open Stacks.RingedSpace (pullbackFunctor)

universe u

namespace Stacks.IdealTorsion.Eta

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The termwise pullback of a cochain complex of sheaves of modules. -/
noncomputable abbrev pullbackComplex
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ℤ :=
  ((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- The pullback of an ideal inclusion along a flat morphism is again a monomorphism: pullback
along a flat morphism preserves monomorphisms, and the identification `f^*𝒪_Y ≅ 𝒪_X` that
`pullbackIdealIncl` composes with is an isomorphism. -/
theorem mono_pullbackIdealIncl (hf : AlgebraicGeometry.IsFlat f)
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Mono ι] :
    Mono (pullbackIdealIncl f I ι) :=
  have : (pullbackFunctor f).PreservesMonomorphisms :=
    RingedSpaceModuleAdjunction.preservesMonomorphisms_modulePullback_of_isFlat f hf
  -- `ι` and its `Mono` instance are typed over `Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf`
  -- and the pullback functor over `structureRingSheaf Y`, so the instance is supplied explicitly.
  have h1 : Mono ((pullbackFunctor f).map ι) :=
    @Functor.map_mono _ _ _ _ (pullbackFunctor f) this _ _ ι (by assumption)
  have h2 : Mono (modulePullbackObjUnitIso f).hom := IsIso.mono_of_iso _
  -- `modulePullbackObjUnitIso` is typed over the `structureSheafRing` spelling of the structure
  -- sheaf of rings and the goal over `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, so the two
  -- `Mono` applications carry different `Category` instance terms and instance search does not
  -- match them; the two monos are therefore supplied to `mono_comp` explicitly, where the
  -- identification is a `default` transparency check rather than a discrimination-tree lookup.
  @mono_comp _ _ _ _ _ _ h1 _ h2

/-! ### The inclusion square in the spelling of `idealPowerIncl` -/

/-- **The interchange of a pullback with an integer invertible ideal power respects the inclusion
of consecutive ideal powers**, written with `Stacks.IdealTorsion.Eta.idealPowerIncl` on both
sides.

This is `Stacks.IdealTorsion.Eta.map_idealIncl`, which is stated in the spelling the abstract
transport produces — the successor comparison followed by a component of the ideal inclusion as a
natural transformation to the identity — rewritten by
`Stacks.IdealTorsion.Eta.idealPowerIncl_eq_powSuccIso_inv_comp` on each side. -/
theorem map_idealPowerIncl (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    (n : ℤ) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    (pullbackFunctor f).map (idealPowerIncl Y I ι n M) ≫ (pullbackIdealPowerIso f I n M).hom =
      (pullbackIdealPowerIso f I (n + 1) M).hom ≫
        idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) n
          ((pullbackFunctor f).obj M) := by
  rw [idealPowerIncl_eq_powSuccIso_inv_comp Y I ι n M,
    idealPowerIncl_eq_powSuccIso_inv_comp X ((pullbackFunctor f).obj I)
      (pullbackIdealIncl f I ι) n ((pullbackFunctor f).obj M)]
  exact map_idealIncl f I ι n M

/-! ### The degreewise comparison of décalage terms -/

/-- **The degreewise comparison of décalages under a flat pullback**: the pullback of the
degree-`n` fibre product defining `η_I F` is the degree-`n` fibre product defining
`η_{f^*I} (f^*F)`.

Pullback along a flat morphism is left exact, so it carries the defining fibre product to the
fibre product of the pulled-back cospan; the two cospans are then identified by the interchange
of pullbacks with ideal powers, whose two squares are
`Stacks.IdealTorsion.Eta.pullbackIdealPowerIso_natural` for the twisted differential and
`Stacks.IdealTorsion.Eta.map_idealPowerIncl` for the inclusion of consecutive ideal powers. -/
noncomputable def pullbackEtaTermIso (hf : AlgebraicGeometry.IsFlat f)
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) :
    (pullbackFunctor f).obj (etaTerm Y I ι F n) ≅
      etaTerm X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F) n :=
  let : PreservesFiniteLimits (pullbackFunctor f) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat f hf
  PreservesPullback.iso (pullbackFunctor f)
      (idealPowerMap Y I n (F.d n (n + 1))) (idealPowerIncl Y I ι n (F.X (n + 1))) ≪≫
    @asIso _ _ _ _ (pullback.map _ _
      (idealPowerMap X ((pullbackFunctor f).obj I) n ((pullbackFunctor f).map (F.d n (n + 1))))
      (idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) n
        ((pullbackFunctor f).obj (F.X (n + 1))))
      (pullbackIdealPowerIso f I n (F.X n)).hom
      (pullbackIdealPowerIso f I (n + 1) (F.X (n + 1))).hom
      (pullbackIdealPowerIso f I n (F.X (n + 1))).hom
      (pullbackIdealPowerIso_natural f I n (F.d n (n + 1)))
      (map_idealPowerIncl f I ι n (F.X (n + 1))))
      -- The three comparisons are typed over `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` and
      -- the fibre products over `structureRingSheaf X`, so their `IsIso` instances are supplied
      -- explicitly.
      (@pullback.map_isIso _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (Iso.isIso_hom _) (Iso.isIso_hom _) (Iso.isIso_hom _))

/-- The first projection of the degreewise comparison. -/
theorem pullbackEtaTermIso_hom_fst (hf : AlgebraicGeometry.IsFlat f)
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) :
    (pullbackEtaTermIso f hf I ι F n).hom ≫
        pullback.fst
          (idealPowerMap X ((pullbackFunctor f).obj I) n
            ((pullbackFunctor f).map (F.d n (n + 1))))
          (idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) n
            ((pullbackFunctor f).obj (F.X (n + 1)))) =
      (pullbackFunctor f).map
          (pullback.fst (idealPowerMap Y I n (F.d n (n + 1)))
            (idealPowerIncl Y I ι n (F.X (n + 1)))) ≫
        (pullbackIdealPowerIso f I n (F.X n)).hom := by
  let : PreservesFiniteLimits (pullbackFunctor f) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat f hf
  -- The statement is not type-correct at `implicit` transparency (the fibre products live over
  -- `structureRingSheaf X`, the comparisons over
  -- `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`), so the chain is written as a term, checked
  -- at `default` transparency.
  exact (Category.assoc _ _ _).trans
    ((whisker_eq _ (pullback.lift_fst _ _ _)).trans (PreservesPullback.iso_hom_fst_assoc _ _ _ _))

/-- The second projection of the degreewise comparison. -/
theorem pullbackEtaTermIso_hom_snd (hf : AlgebraicGeometry.IsFlat f)
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) :
    (pullbackEtaTermIso f hf I ι F n).hom ≫
        pullback.snd
          (idealPowerMap X ((pullbackFunctor f).obj I) n
            ((pullbackFunctor f).map (F.d n (n + 1))))
          (idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) n
            ((pullbackFunctor f).obj (F.X (n + 1)))) =
      (pullbackFunctor f).map
          (pullback.snd (idealPowerMap Y I n (F.d n (n + 1)))
            (idealPowerIncl Y I ι n (F.X (n + 1)))) ≫
        (pullbackIdealPowerIso f I (n + 1) (F.X (n + 1))).hom := by
  let : PreservesFiniteLimits (pullbackFunctor f) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat f hf
  -- The statement is not type-correct at `implicit` transparency (the fibre products live over
  -- `structureRingSheaf X`, the comparisons over
  -- `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`), so the chain is written as a term, checked
  -- at `default` transparency.
  exact (Category.assoc _ _ _).trans
    ((whisker_eq _ (pullback.lift_snd _ _ _)).trans (PreservesPullback.iso_hom_snd_assoc _ _ _ _))

end Stacks.IdealTorsion.Eta

end
