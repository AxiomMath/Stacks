module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.CoborderDifferentialsStalk
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentConormalDifferentialAssembly
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentTowerPullbackDifferentials

/-!
# Both transposes of the conormal differential send `f` to `1 ⊗ d f`

Let `i : X ⟶ P` be an immersion of schemes and `g : P ⟶ Y` any morphism.  Write `W` for the
coborder neighbourhood `i.coborderRange`, `ι : W ⟶ P` for the open factor, `j = i.liftCoborder`
for the closed factor and `ℐ` for the ideal sheaf
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal i` of `j`.  Two morphisms of sheaves of
`𝒪_W`-modules `ℐ ⟶ j_*(i^*Ω_{P/Y})` have been constructed independently.

* The **sites-level** one: the adjoint transpose
  `Stacks.Conormal.Sites.conormalTranspose i` of the conormal comparison, which carries a section
  `f` of `ℐ` to the conormal class of `f` in `I/I²` for `I` the kernel of `i⁻¹𝒪_P ⟶ 𝒪_X`,
  followed by the first arrow of the conormal sequence of [Stacks Project, Tag 08TF] for the tower
  `i⁻¹g⁻¹𝒪_Y ⟶ i⁻¹𝒪_P ⟶ 𝒪_X` and by the degree `0` crossing
  `Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g`, which identifies the middle term
  of that sequence with `i^*Ω_{P/Y}`.  The source is read at the spelling of `ℐ` that
  [Stacks Project, Tag 01UZ] uses through
  `Stacks.Conormal.DefiningIdealBridge.idealSheafBridge`.
* The **geometric** one: `Stacks.ConormalSequenceRight.conormalDifferentialTranspose i g`, which
  carries `f` to `1 ⊗ d_{P/Y} f` directly and is the datum pinning down the first arrow of the
  conormal sequence of [Stacks Project, Tag 01UZ].

This file proves that the two agree.  Both send `f` to `1 ⊗ d f`; there is no further
mathematical content, and the work is the bookkeeping of three opens of `X` that are equal only
propositionally.

## Main results

* `Stacks.NaiveCotangentConormalTranspose.conormalTranspose_comp`: **the two transposes agree.**
  This is verbatim the hypothesis `hτ` of
  `Stacks.NaiveCotangentConormalAssembly.hsq_of_transpose`, so together with
  `Stacks.NaiveCotangentTower.tensorDifferentialsCrossing` it discharges the last remaining input
  of [Stacks Project, Tag 0FV4].
* `Stacks.NaiveCotangentConormalTranspose.towerTensorDifferential_map`: the local section
  `1 ⊗ d y` of the middle term of the tower's conormal sequence is compatible with a restriction
  between two *equal* opens.

## Route

Both sides are compared on a section `s` of `ℐ` over an open `V` of `W`.  Put `U = ι ''ᵁ V`, an
open of `P`, and note that the sections of `𝒪_W` over `V` are the sections of `𝒪_P` over `U` on
the nose, so `s.1` is already a section of `𝒪_P` over `U`.

On the left, `Stacks.Conormal.DefiningIdealBridge.idealSection_idealSheafBridge_hom` says the
bridge changes no section, so the transpose is the conormal class of
`Stacks.Conormal.Sites.coborderUnit i V s.1`, which by construction is the image of `s.1` under
the unit of the inverse-image/direct-image adjunction over `U`, restricted along
`AlgebraicGeometry.Scheme.Hom.liftCoborder_preimage`.
`Stacks.Sites.Conormal.conormalSequence_f_class` turns that class into the local section
`1 ⊗ d`, and `Stacks.NaiveCotangentTower.tensorDifferentialsCrossing_hom_tensorDifferential`
evaluates the crossing on it, giving the image of `d_{P/Y}s.1` under the unit of
`i^* ⊣ i_*` over `U`.  Moving the restriction out of the way needs
`towerTensorDifferential_map` and the naturality of the crossing.

On the right, `Stacks.ConormalSequenceRight.conormalDifferentialTranspose_val_app` is the
definition of `1 ⊗ d f`, and
`Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso_germ` says that the coborder
comparison carries `1 ⊗ d_{W/Y}(ι^♯ a)` to `1 ⊗ d_{P/Y}a` — on germs, since the two sides sit
over the propositionally equal opens `j ⁻¹ᵁ ι ⁻¹ᵁ U` and `i ⁻¹ᵁ U`.  The transport from `V` to
`ι ⁻¹ᵁ U` is the naturality of `conormalDifferentialTranspose` itself.

The two resulting germs are the same, and `TopCat.Presheaf.section_ext` upgrades that to the
equality of the two sections.

## Implementation notes

The opens `i ⁻¹ᵁ U`, `j ⁻¹ᵁ V` and `j ⁻¹ᵁ ι ⁻¹ᵁ U` are pairwise equal, but none of the
equalities is definitional: they come from `AlgebraicGeometry.Scheme.Hom.liftCoborder_ι`, which
is not.  So the comparison is made on germs, where a section is allowed to sit over any of them.
`towerTensorDifferential_map` is therefore only stated for a restriction map between two equal
opens, which is all that is needed and is provable by `subst`; no general naturality of
`Stacks.Sites.Conormal.tensorDifferential` in the object of the site is proved here.

Morphisms between opens are subsingletons, which is what identifies the restriction map
`𝒪_W(V) ⟶ 𝒪_W(ι ⁻¹ᵁ U)` with `ι.app U`: by `AlgebraicGeometry.Scheme.Opens.ι_app` and
`AlgebraicGeometry.Scheme.Opens.toScheme_presheaf_map` both are `𝒪_P` applied to a morphism
`op U ⟶ op (ι ''ᵁ ι ⁻¹ᵁ U)`, and there is only one.

Every step is a chain of `Eq.trans` and `congrArg` rather than `rw`.  This is forced: the goal
mixes `AlgebraicGeometry.Scheme.Modules` with
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf _)`, and the `TopCat.Sheaf` spelling of
the structure sheaf with the `Sheaf (Opens.grothendieckTopology _)` one; such a goal is not
type-correct at the transparency `rw` builds its motive at.

## References

* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4), whose last input this is.
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the conormal sequence of
  an immersion, whose first arrow the right-hand transpose pins down.
* [Stacks Project, Tag 08TF](https://stacks.math.columbia.edu/tag/08TF), the conormal sequence of
  a tower of sheaves of rings on a site, whose first arrow the left-hand side uses.
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2), the conormal sheaf.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.SheafOfModules (inverseImageBaseRing inverseImageFirstRingMap
  inverseImageMiddleRing ringedSpaceStructureMap)
open RingedSpaceModuleAdjunction (modulePushforward)

universe u

noncomputable section

namespace Stacks.NaiveCotangentConormalTranspose

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (g : P ⟶ Y) [IsImmersion i]

/-- The conormal sequence of the tower `i⁻¹g⁻¹𝒪_Y ⟶ i⁻¹𝒪_P ⟶ 𝒪_X`. -/
abbrev towerSequence :=
  Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
    (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
    (ringedSpaceStructureMap (ringedSpaceHom i))

/-- The local section `1 ⊗ d y` of the middle term of `towerSequence`. -/
abbrev towerTensorDifferential (O : (Opens X.toRingedSpace.carrier)ᵒᵖ)
    (y : (inverseImageMiddleRing (ringedSpaceHom i)).obj.obj O) :=
  Stacks.Sites.Conormal.tensorDifferential.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
    (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
    (ringedSpaceStructureMap (ringedSpaceHom i)) O y

/-- The conormal class of a section of the kernel ideal, in the left term of
`towerSequence`. -/
abbrev towerConormalClass (O : (Opens X.toRingedSpace.carrier)ᵒᵖ)
    (y : Stacks.Sites.Conormal.kernelIdeal
      (ringedSpaceStructureMap (ringedSpaceHom i)).hom O) :=
  Stacks.Sites.Conormal.conormalClass.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
    (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
    (ringedSpaceStructureMap (ringedSpaceHom i)) O y

/-- **`1 ⊗ d y` is compatible with a restriction between two equal opens.**  A restriction map
between opens that are propositionally equal is a restriction along the identity, so this is
functoriality and nothing more; it is the only naturality of
`Stacks.Sites.Conormal.tensorDifferential` the comparison below needs. -/
theorem towerTensorDifferential_map {O O' : (Opens X.toRingedSpace.carrier)ᵒᵖ} (ρ : O ⟶ O')
    (hO : O = O') (y : (inverseImageMiddleRing (ringedSpaceHom i)).obj.obj O) :
    towerTensorDifferential i g O' (((inverseImageMiddleRing (ringedSpaceHom i)).obj.map ρ) y) =
      (towerSequence i g).X₂.val.map ρ (towerTensorDifferential i g O y) := by
  subst hO
  obtain rfl : ρ = 𝟙 O := Subsingleton.elim _ _
  have hy : ((inverseImageMiddleRing (ringedSpaceHom i)).obj.map (𝟙 O)) y = y :=
    ConcreteCategory.congr_hom
      ((inverseImageMiddleRing (ringedSpaceHom i)).obj.map_id O) y
  have hz : (towerSequence i g).X₂.val.map (𝟙 O) (towerTensorDifferential i g O y) =
      towerTensorDifferential i g O y := by
    rw [(towerSequence i g).X₂.val.map_id]; rfl
  exact (congrArg (towerTensorDifferential i g O) hy).trans hz.symm

/-- **The two transposes of the conormal differential agree.**  Out of the ideal sheaf of the
canonical closed factor of an immersion `i : X ⟶ P`, the sites-level transpose — the conormal
class of a section, pushed through the first arrow of the conormal sequence of the tower
`i⁻¹g⁻¹𝒪_Y ⟶ i⁻¹𝒪_P ⟶ 𝒪_X` and through the degree `0` crossing — is the geometric transpose of
the first arrow of the conormal sequence of [Stacks Project, Tag 01UZ].  Both carry a section `f`
to `1 ⊗ d f`. -/
theorem conormalTranspose_comp :
    (Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom ≫
        Stacks.Conormal.Sites.conormalTranspose i ≫
        (modulePushforward i.liftCoborder.toLRSHom.toShHom).map
          ((Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
              (Opens.grothendieckTopology X.toRingedSpace.carrier)
              (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
              (inverseImageMiddleRing (ringedSpaceHom i))
              X.toRingedSpace.sheaf
              (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
              (ringedSpaceStructureMap (ringedSpaceHom i))).f ≫
            (Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g).hom) =
      Stacks.ConormalSequenceRight.conormalDifferentialTranspose i g := by
  ext V s
  obtain ⟨V⟩ := V
  have hpre : i.liftCoborder ⁻¹ᵁ V = i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V) :=
    i.liftCoborder_preimage V
  have hpi : i.coborderRange.ι ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V) = V :=
    i.coborderRange.ι.preimage_image_eq V
  -- the left-hand side, on sections
  have hL1 : ((((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom ≫
        Stacks.Conormal.Sites.conormalTranspose i ≫
        (modulePushforward i.liftCoborder.toLRSHom.toShHom).map
          ((towerSequence i g).f ≫
            (Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g).hom)).val.app
            (op V))) s =
      (Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g).hom.val.app
        (op (i.liftCoborder ⁻¹ᵁ V))
        ((towerSequence i g).f.val.app (op (i.liftCoborder ⁻¹ᵁ V))
          (towerConormalClass i g (op (i.liftCoborder ⁻¹ᵁ V))
            (Stacks.Conormal.Sites.kernelSection i V
              ((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom.val.app
                (op V) s)))) := rfl
  have hL2 : (towerSequence i g).f.val.app (op (i.liftCoborder ⁻¹ᵁ V))
        (towerConormalClass i g (op (i.liftCoborder ⁻¹ᵁ V))
          (Stacks.Conormal.Sites.kernelSection i V
            ((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom.val.app (op V) s))) =
      towerTensorDifferential i g (op (i.liftCoborder ⁻¹ᵁ V))
        (Stacks.Conormal.Sites.kernelSection i V
          ((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom.val.app (op V) s)) :=
    Stacks.Sites.Conormal.conormalSequence_f_class.{u, u, u, u} _ _ _ _ _ _ _ _
  have hker : ((Stacks.Conormal.Sites.kernelSection i V
        ((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom.val.app (op V) s) :
          (inverseImageMiddleRing (ringedSpaceHom i)).obj.obj
            (op (i.liftCoborder ⁻¹ᵁ V)))) =
      (Stacks.Conormal.Sites.coborderUnit i V).hom s.1 :=
    congrArg (Stacks.Conormal.Sites.coborderUnit i V).hom
      (Stacks.Conormal.DefiningIdealBridge.idealSection_idealSheafBridge_hom i V s)
  have hu : (Stacks.Conormal.Sites.coborderUnit i V).hom s.1 =
      ((inverseImageMiddleRing (ringedSpaceHom i)).obj.map (eqToHom hpre).op).hom
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
          P.sheaf).hom.app (op (i.coborderRange.ι ''ᵁ V))).hom s.1) :=
    CommRingCat.comp_apply _ _ _
  have htd := towerTensorDifferential_map i g (eqToHom hpre).op (congrArg op hpre.symm)
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
      P.sheaf).hom.app (op (i.coborderRange.ι ''ᵁ V))).hom s.1)
  have hnat := PresheafOfModules.naturality_apply
    (Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g).hom.val (eqToHom hpre).op
    (towerTensorDifferential i g (op (i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V)))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
        P.sheaf).hom.app (op (i.coborderRange.ι ''ᵁ V))).hom s.1))
  have hcross := Stacks.NaiveCotangentTower.tensorDifferentialsCrossing_hom_tensorDifferential
    i g (i.coborderRange.ι ''ᵁ V) s.1
  have hL : ((((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom ≫
        Stacks.Conormal.Sites.conormalTranspose i ≫
        (modulePushforward i.liftCoborder.toLRSHom.toShHom).map
          ((towerSequence i g).f ≫
            (Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g).hom)).val.app
            (op V))) s =
      ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials g)).val.map
        (eqToHom hpre).op
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
            (Scheme.Hom.relativeDifferentials g)).val.app
          (op (i.coborderRange.ι ''ᵁ V))
          ((Scheme.Hom.universalRelativeDerivation g).d s.1)) := by
    refine hL1.trans ?_
    refine Eq.trans (congrArg
      ((Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g).hom.val.app
        (op (i.liftCoborder ⁻¹ᵁ V))) hL2) ?_
    refine Eq.trans (congrArg (fun y =>
      (Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g).hom.val.app
        (op (i.liftCoborder ⁻¹ᵁ V))
        (towerTensorDifferential i g (op (i.liftCoborder ⁻¹ᵁ V)) y)) (hker.trans hu)) ?_
    refine Eq.trans (congrArg
      ((Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g).hom.val.app
        (op (i.liftCoborder ⁻¹ᵁ V))) htd) ?_
    refine hnat.trans ?_
    exact congrArg
      (((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials g)).val.map
        (eqToHom hpre).op) hcross
  -- the right-hand side, on sections
  have hR : ∀ (V' : Opens i.coborderRange.toScheme)
      (s' : (AlgebraicGeometry.RegularIdealSheaf.definingIdeal i).toSheafOfModules.val.obj (op V')),
      ((Stacks.ConormalSequenceRight.conormalDifferentialTranspose i g).val.app (op V')) s' =
      (Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso i g).hom.val.app
        (op (i.liftCoborder ⁻¹ᵁ V'))
        (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ g))).val.app (op V')
          ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ g)).d s'.1)) :=
    fun _ _ => rfl
  have hRnat := PresheafOfModules.naturality_apply
    (Stacks.ConormalSequenceRight.conormalDifferentialTranspose i g).val (eqToHom hpi).op s
  have hval : (((AlgebraicGeometry.RegularIdealSheaf.definingIdeal i).toSheafOfModules.val.map
        (eqToHom hpi).op s)).1 =
      (i.coborderRange.toScheme.presheaf.map (eqToHom hpi).op).hom s.1 := rfl
  have hιapp : (i.coborderRange.toScheme.presheaf.map (eqToHom hpi).op).hom s.1 =
      (i.coborderRange.ι.app (i.coborderRange.ι ''ᵁ V)).hom s.1 :=
    ConcreteCategory.congr_hom (congrArg P.presheaf.map (Subsingleton.elim _ _)) s.1
  -- both sides are sections of a sheaf over `i.liftCoborder ⁻¹ᵁ V`, so it is enough to
  -- compare their germs
  refine hL.trans (Eq.trans ?_ (hR V s).symm)
  refine TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf _).obj
      ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials g)))
    (i.liftCoborder ⁻¹ᵁ V) _ _ ?_
  intro z hz
  have hzV : z ∈ i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V)) :=
    hpi.ge hz
  have hgerm := Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso_germ i g
    (i.coborderRange.ι ''ᵁ V) s.1 z (hpre.le hz) hzV
  refine Eq.trans (TopCat.Presheaf.germ_res_apply _ (eqToHom hpre) z hz _) ?_
  refine Eq.trans hgerm.symm ?_
  refine Eq.trans ?_ (TopCat.Presheaf.germ_res_apply _
    ((Opens.map i.liftCoborder.base).map (eqToHom hpi)) z hzV _)
  refine congrArg (TopCat.Presheaf.germ (C := Ab.{u})
    ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials g)).val.presheaf
    (i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V))) z hzV) ?_
  refine Eq.trans (congrArg (fun y =>
    (Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso i g).hom.val.app
      (op (i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V))))
      (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
          (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ g))).val.app
        (op (i.coborderRange.ι ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V)))
        ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ g)).d y)))
    (hval.trans hιapp).symm) ?_
  exact (hR _ _).symm.trans (hRnat.trans (congrArg
    (((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials g)).val.map
      ((Opens.map i.liftCoborder.base).map (eqToHom hpi)).op) (hR V s)))

end Stacks.NaiveCotangentConormalTranspose

end

end
