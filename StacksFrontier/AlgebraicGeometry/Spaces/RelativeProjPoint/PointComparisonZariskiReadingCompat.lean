module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonZariskiReading
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardComparison

/-!
# The direct-image compatibility of the Zariski readings

For a morphism `τ : T' ⟶ T` of the site, the identification
`AlgebraicGeometry.Space.zariskiDirectImageNatTrans` of the Zariski reading of a direct image is
the composite of the comparison of the small étale sites with direct images
(`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`) and the comparison of
restriction to the Zariski sites with direct images (`SheafOfModules.pushforwardSquareIso`):
this is `AlgebraicGeometry.Space.ZariskiReadingDirectImageCompat`, proved here as
`AlgebraicGeometry.Space.zariskiReadingDirectImageCompat` by reducing it to an identity of
sections over a Zariski open: both sides are computed there.  It also holds the
abstract mate lemmas used by `AlgebraicGeometry.Space.pointComparison_app_eq` and bridge K.

## Main results

* `CategoryTheory.Adjunction.rightAdjointSquareCompat_of_tail`: the abstract reduction of
  `CategoryTheory.Adjunction.RightAdjointSquareCompat` to its tail
  `CategoryTheory.Adjunction.rightAdjointSquareTail`.
* `AlgebraicGeometry.Space.zariskiReadingCompat_tail_section`: the tail on sections over a
  Zariski open, two restriction maps.
* `AlgebraicGeometry.Space.zariskiReadingIso_hom_app_comp_zariskiDirectImageNatTrans_app_apply`:
  the left-hand side on sections over a Zariski open.
* `AlgebraicGeometry.Space.directImageSelfOpensModuleSection_eq_tail_section`: the right-hand side
  on sections over a Zariski open.
* `AlgebraicGeometry.Space.zariskiReadingDirectImageCompat`: the compatibility holds for every
  morphism of the site.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Adjunction

section RightAdjointSquare

variable {M M' Ec Ec' Z Z' : Type*} [Category* M] [Category* M'] [Category* Ec] [Category* Ec']
  [Category* Z] [Category* Z']
  {φs : M ⥤ M'} {φp : M' ⥤ M} {gs : Ec ⥤ Ec'} {gp : Ec' ⥤ Ec} {τs : Z ⥤ Z'} {τp : Z' ⥤ Z}
  {Ei : M ⥤ Ec} {Ef : Ec ⥤ M} {Ei' : M' ⥤ Ec'} {zR : M ⥤ Z} {zR' : M' ⥤ Z'}

/-- The transpose along `τs ⊣ τp` of `zR g ≫ zDI` for `g` the `φs ⊣ φp`-transpose of `m` is the
transpose of `zR` of the unit followed by `zDI`, followed by `zR' m`. -/
theorem homEquiv_symm_map_comp_app_eq (aφ : φs ⊣ φp) (aτ : τs ⊣ τp)
    (zDI : φp ⋙ zR ⟶ zR' ⋙ τp) {N : M} {N' : M'} (m : φs.obj N ⟶ N') (g : N ⟶ φp.obj N')
    (hg : (aφ.homEquiv _ _).symm g = m) :
    (aτ.homEquiv _ _).symm (zR.map g ≫ zDI.app N') =
      (aτ.homEquiv _ _).symm (zR.map (aφ.unit.app N) ≫ zDI.app (φs.obj N)) ≫ zR'.map m := by
  have hg' : g = aφ.unit.app N ≫ φp.map m := by
    rw [← hg]
    exact (Equiv.apply_symm_apply (aφ.homEquiv N N') g).symm.trans (aφ.homEquiv_unit _ _ _)
  have hn : zR.map (φp.map m) ≫ zDI.app N' = zDI.app (φs.obj N) ≫ τp.map (zR'.map m) := by
    simpa only [Functor.comp_map] using zDI.naturality m
  rw [← homEquiv_naturality_right_symm, hg', Functor.map_comp, Category.assoc, hn,
    Category.assoc]
  rfl

/-- **The abstract shape of bridge K**: reflected along a faithful reading `F`, the composite
`x₁ ≫ x₂ ≫ x₃` is `y₁ ≫ y₂ ≫ y₃`, given the readings of the six factors (`h1`, `h2`, `h3`, `hB`,
`hB'`) and the compatibility `hU` of the readings with the comparisons. -/
theorem comp_comp_eq_of_reading {C' Z₀ Z₁ : Type*} [Category* C'] [Category* Z₀] [Category* Z₁]
    (F : C' ⥤ Z₁) (G : Z₀ ⥤ Z₁) {a b c d n₂ n₃ : C'} {zN zAM zM : Z₀} {zM' : Z₁}
    (x₁ : a ⟶ b) (x₂ : b ⟶ c) (x₃ : c ⟶ d) (y₁ : a ⟶ n₂) (y₂ : n₂ ⟶ n₃) (y₃ : n₃ ⟶ d)
    (hinj : Function.Injective (fun x : a ⟶ d => F.map x))
    (R : G.obj zN ≅ F.obj a) (R' : G.obj zAM ≅ F.obj b) (bT : zN ⟶ zAM) (QM : zAM ⟶ zM)
    (ιN : zN ⟶ zM) (hB : bT ≫ QM = ιN) (h1 : R.hom ≫ F.map x₁ = G.map bT ≫ R'.hom)
    (Q' : F.obj c ≅ G.obj zM) (h2 : F.map x₂ = R'.inv ≫ G.map QM ≫ Q'.inv)
    (Q'' : F.obj d ≅ zM') (p : G.obj zM ⟶ zM') (h3 : F.map x₃ = Q'.hom ≫ p ≫ Q''.inv)
    (ι'N : F.obj n₃ ⟶ zM') (hB' : F.map y₃ ≫ Q''.hom = ι'N)
    (hU : G.map ιN ≫ p = R.hom ≫ F.map (y₁ ≫ y₂) ≫ ι'N) :
    x₁ ≫ x₂ ≫ x₃ = y₁ ≫ y₂ ≫ y₃ := by
  apply hinj
  dsimp only
  have h1' : F.map x₁ = R.inv ≫ G.map bT ≫ R'.hom := by
    rw [← h1, Iso.inv_hom_id_assoc]
  have hB'' : F.map y₃ = ι'N ≫ Q''.inv := by
    rw [← hB', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp, h1', h2, h3,
    show y₁ ≫ y₂ ≫ y₃ = (y₁ ≫ y₂) ≫ y₃ from (Category.assoc _ _ _).symm,
    Functor.map_comp F (y₁ ≫ y₂) y₃, hB'']
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, hB, reassoc_of% hU]
  simp only [Iso.inv_hom_id_assoc]

/-- The part of the right-hand side of `CategoryTheory.Adjunction.RightAdjointSquareCompat` after
the comparison of right adjoints: for `g : N ⟶ Ef (gp (Ei' M₀))`, the image under `r` of the
transpose of `g` along `Ei ⊣ Ef`, followed by `R1` and `τp ι'`. -/
def rightAdjointSquareTail {r' : Ec' ⥤ Z'} (aE : Ei ⊣ Ef) (r : Ec ⥤ Z) (ι' : Ei' ⋙ r' ≅ zR')
    (R1 : gp ⋙ r ≅ r' ⋙ τp) (N : M) (M₀ : M') (g : N ⟶ (gp ⋙ Ef).obj (Ei'.obj M₀)) :
    (Ei ⋙ r).obj N ⟶ (zR' ⋙ τp).obj M₀ :=
  r.map (Ei.map g ≫ aE.counit.app (gp.obj (Ei'.obj M₀))) ≫ R1.hom.app (Ei'.obj M₀) ≫
    τp.map (ι'.hom.app M₀)

/-- `CategoryTheory.Adjunction.RightAdjointSquareCompat` for a comparison `P` of composite right
adjoints and an identification `α : φpm ≅ φpb` of two right adjoints: `α` is moved past the unit of
`Ei' ⊣ Ef'` by naturality, so the morphism transposed along `Ei ⊣ Ef` is `k`, then `α`, then the
image under `φpb` of the unit, then `α⁻¹` and `P⁻¹`. -/
theorem rightAdjointSquareCompat_of_tail {Ef' : Ec' ⥤ M'} {φpm φpb : M' ⥤ M}
    (k : ∀ M₀ : M', φp.obj M₀ ⟶ φpm.obj M₀) (aE : Ei ⊣ Ef) (aE' : Ei' ⊣ Ef')
    (P : gp ⋙ Ef ≅ Ef' ⋙ φpm) (α : φpm ≅ φpb) (r : Ec ⥤ Z) (r' : Ec' ⥤ Z')
    (ι : Ei ⋙ r ≅ zR) (ι' : Ei' ⋙ r' ≅ zR') (zDI : φp ⋙ zR ⟶ zR' ⋙ τp) (R1 : gp ⋙ r ≅ r' ⋙ τp)
    (h : ∀ M₀ : M', ι.hom.app (φp.obj M₀) ≫ zDI.app M₀ =
      rightAdjointSquareTail aE r ι' R1 (φp.obj M₀) M₀
        (k M₀ ≫ α.hom.app M₀ ≫ φpb.map (aE'.unit.app M₀) ≫
          α.inv.app (Ef'.obj (Ei'.obj M₀)) ≫ P.inv.app (Ei'.obj M₀))) :
    RightAdjointSquareCompat k aE aE' P r r' ι ι' zDI R1 := by
  intro M₀
  rw [h M₀, rightAdjointSquareTail]
  have hn : φpm.map (aE'.unit.app M₀) = α.hom.app M₀ ≫ φpb.map (aE'.unit.app M₀) ≫
      α.inv.app (Ef'.obj (Ei'.obj M₀)) := by
    have hn' := α.hom.naturality (aE'.unit.app M₀)
    simp only [Functor.comp_obj, Functor.id_obj] at hn'
    rw [← reassoc_of% hn', Iso.hom_inv_id_app, Category.comp_id]
  rw [hn]
  simp only [Category.assoc]

/-- `CategoryTheory.Adjunction.rightAdjointSquareCompat_of_tail` for a comparison `P` of composite
right adjoints whose last factor is `α⁻¹` whiskered by `Ef'`: then `α⁻¹` cancels, and the
morphism transposed along `Ei ⊣ Ef` is `k`, then `α`, then the image under `φpb` of the unit of
`Ei' ⊣ Ef'`, then the inverse of the remaining factors `a ≪≫ b ≪≫ c` of `P`. -/
theorem rightAdjointSquareCompat_of_tail_trans {Ef' : Ec' ⥤ M'} {φpm φpb : M' ⥤ M}
    {G₁ G₂ : Ec' ⥤ M} (k : ∀ M₀ : M', φp.obj M₀ ⟶ φpm.obj M₀) (aE : Ei ⊣ Ef) (aE' : Ei' ⊣ Ef')
    (P : gp ⋙ Ef ≅ Ef' ⋙ φpm) (α : φpm ≅ φpb) (a : gp ⋙ Ef ≅ G₁) (b : G₁ ≅ G₂)
    (c : G₂ ≅ Ef' ⋙ φpb) (hP : P = a ≪≫ b ≪≫ c ≪≫ Functor.isoWhiskerLeft Ef' α.symm)
    (r : Ec ⥤ Z) (r' : Ec' ⥤ Z') (ι : Ei ⋙ r ≅ zR) (ι' : Ei' ⋙ r' ≅ zR')
    (zDI : φp ⋙ zR ⟶ zR' ⋙ τp) (R1 : gp ⋙ r ≅ r' ⋙ τp)
    (h : ∀ M₀ : M', ι.hom.app (φp.obj M₀) ≫ zDI.app M₀ =
      rightAdjointSquareTail aE r ι' R1 (φp.obj M₀) M₀
        (k M₀ ≫ α.hom.app M₀ ≫ φpb.map (aE'.unit.app M₀) ≫ (a ≪≫ b ≪≫ c).inv.app (Ei'.obj M₀))) :
    RightAdjointSquareCompat k aE aE' P r r' ι ι' zDI R1 := by
  refine rightAdjointSquareCompat_of_tail k aE aE' P α r r' ι ι' zDI R1 (fun M₀ => ?_)
  rw [h M₀]
  subst hP
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
    Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc, Category.assoc]

end RightAdjointSquare

end CategoryTheory.Adjunction

/-- For a presheaf of types `F`, the restriction along `ρ = a ≫ b ≫ c ≫ d` is the composite of
the four restrictions. -/
theorem CategoryTheory.FunctorToTypes.map_op_apply_eq_of_comp_eq {C : Type*} [Category* C]
    (F : Cᵒᵖ ⥤ Type*) {X₀ X₁ X₂ X₃ X₄ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) {ρ : X₀ ⟶ X₄} (hρ : a ≫ b ≫ c ≫ d = ρ) (w : F.obj (Opposite.op X₄)) :
    F.map ρ.op w = F.map a.op (F.map b.op (F.map c.op (F.map d.op w))) := by
  subst hρ
  simp only [op_comp, Functor.map_comp_apply]

namespace AlgebraicGeometry.Space

universe u

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (τ : T' ⟶ T)

/-- The tail `CategoryTheory.Adjunction.rightAdjointSquareTail` of
`AlgebraicGeometry.Space.ZariskiReadingDirectImageCompat` on sections over a Zariski open `O` of
`T`: two restriction maps of `M₀` applied to the section of `g` over the chart of `O`. -/
theorem zariskiReadingCompat_tail_section
    (M₀ : SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
    {N : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)}
    (g : N ⟶ _)
    (O : (TopologicalSpace.Opens ((BigFppfOver.toScheme B S hS).obj T))ᵒᵖ)
    (x : (((representedSmallEtaleModuleEquivalence B S hS T).symm.functor ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj N).val.obj O) :
    @Eq _ (((@Adjunction.rightAdjointSquareTail
      (SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
      (SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
      _ _ ((BigFppfOver.toScheme B S hS).obj T).Modules
      ((BigFppfOver.toScheme B S hS).obj T').Modules
      _ _ _ _ (Scheme.Modules.instCategory (X := (BigFppfOver.toScheme B S hS).obj T))
      (Scheme.Modules.instCategory (X := (BigFppfOver.toScheme B S hS).obj T'))
      (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS τ))
      (@Stacks.RingedSpace.pushforwardFunctor
        (chartScheme (idEtaleChart B S hS T')).toSheafedSpace
        (chartScheme (idEtaleChart B S hS T)).toSheafedSpace
        (@ringedSpaceHom (chartScheme (idEtaleChart B S hS T'))
          (chartScheme (idEtaleChart B S hS T))
          (@CategoryTheory.Functor.map _ _ _ _ (BigFppfOver.toScheme B S hS)
            ((SmallEtale.toOver B S hS _).obj (idEtaleChart B S hS T'))
            ((SmallEtale.toOver B S hS _).obj (idEtaleChart B S hS T)) τ)))
      (representedSmallEtaleModuleEquivalence B S hS T).symm.functor
      (representedSmallEtaleModuleEquivalence B S hS T).functor
      (representedSmallEtaleModuleEquivalence B S hS T').symm.functor _ _
      ((representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction :
        (representedSmallEtaleModuleEquivalence B S hS T).inverse ⊣
          (representedSmallEtaleModuleEquivalence B S hS T).functor)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (zariskiReadingIso T')
      (SheafOfModules.pushforwardSquareIso.{u}
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          τ.left).toRingCatSheafHom
        (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
          T'.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
          T.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
          τ.left)
        (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B) τ.left)
        (_root_.AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso
          (associatedBigEtaleSite B) τ.left)) N M₀ g).val.app O).hom x)
    (((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj.map
      ((representedSmallEtaleEquivalence B S hS T').inverse.map
        ((_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B)
          τ.left).hom.app O.unop)).op
      (((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj.map
        ((representedSmallEtaleEquivalence B S hS T').inverse.map
          ((_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) τ.left).map
            ((representedSmallEtaleEquivalence B S hS T).counitIso.inv.app
              (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property O.unop)))).op
        ((g.val.app (Opposite.op ((selfOpensFunctor B S hS T).obj O.unop))).hom x))) :=
  rfl

/-- The Zariski reading of `φ_* M₀` followed by the identification of the Zariski reading of a
direct image, on a section over a Zariski open `O` of `T`: the identification of sections
`AlgebraicGeometry.Space.directImageSelfOpensModuleSection`. -/
theorem zariskiReadingIso_hom_app_comp_zariskiDirectImageNatTrans_app_apply
    (M₀ : SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
    (O : (TopologicalSpace.Opens ((BigFppfOver.toScheme B S hS).obj T))ᵒᵖ)
    (x : (((representedSmallEtaleModuleEquivalence B S hS T).symm.functor ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
          ((smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules.obj
            M₀)).val.obj O) :
    @Eq _ ((((zariskiReadingIso T).hom.app
      ((smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules.obj M₀) ≫
        (zariskiDirectImageNatTrans τ).app M₀).val.app O).hom x)
      (directImageSelfOpensModuleSection τ O.unop M₀ x) :=
  rfl

/-- The comparison `AlgebraicGeometry.Space.modulePushforwardChartIso` along the morphism of
test objects, followed by any morphism `R`, on sections over an étale chart `V`: the comparison
`AlgebraicGeometry.Space.chartComparison` of the underlying sheaves of sets followed by `R`. -/
theorem modulePushforwardChartIso_hom_app_comp_val_app_apply
    (M₀ : SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
    (V : (SmallEtale B S hS (yoneda.obj T))ᵒᵖ)
    {W : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)}
    (R : @Quiver.Hom (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) _
      ((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS τ)
        (relativelyRepresentable_yoneda_map B S hS τ)).obj M₀) W)
    (g : @CategoryTheory.Functor.obj
        (SheafOfModules.{u} (representedStructureRingSheaf B S hS T')) _
        (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) _
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules M₀ ⟶ W)
    (hg : g = (pushforwardModulesIsoModulePushforward B S hS (representedSpaceMap B S hS τ)).hom.app
      M₀ ≫ (modulePushforwardChartIso B S hS (representedSpaceMap B S hS τ)
        (relativelyRepresentable_yoneda_map B S hS τ)).hom.app M₀ ≫ R)
    (x : ((smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules.obj
      M₀).val.obj V) :
    (g.val.app V).hom x =
      (R.val.app V).hom (@id (((smallBaseChangeModulePushforward.{u, u} B S hS
        (representedSpaceMap B S hS τ) (relativelyRepresentable_yoneda_map B S hS τ)).obj
          M₀).val.obj V : Type u)
            (((chartComparison B S hS (representedSpaceMap B S hS τ)
              (relativelyRepresentable_yoneda_map B S hS τ)).hom.app
                (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS
                  ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩) M₀)).hom.app V x)) := by
  subst hg
  exact congrArg (fun m => ((Sheaf.moduleSheafFunctor.{u, u, u + 1}
      (structureRingSheaf B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)).map R).hom.app V
        (m.hom.app V x))
    (moduleSheafFunctor_map_modulePushforwardChartIso_hom_app B S hS (representedSpaceMap B S hS τ)
      (relativelyRepresentable_yoneda_map B S hS τ) M₀)

/-- The image under the base change of charts of the unit of the identification of the small
étale sites of `T'`, followed by the comparison of the two routes of pushforwards round the square
of small étale sites, on sections over an étale chart `V` of `yoneda.obj T`: two restriction maps
of `M₀`. -/
theorem sections_smallBaseChangeModulePushforward_map_unit_comp_inv_app
    (M₀ : SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
    (R₀ : @Quiver.Hom (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) _
      ((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS τ)
        (relativelyRepresentable_yoneda_map B S hS τ)).obj M₀)
        ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS τ) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T).functor).obj
            ((representedSmallEtaleModuleEquivalence B S hS T').symm.functor.obj M₀)))
    (hR₀ : R₀ = (smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS τ)
          (relativelyRepresentable_yoneda_map B S hS τ)).map
            ((representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction.unit.app M₀) ≫
        (SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
            (representedSchemeStructureMapRing B S hS τ) ≪≫
          SheafOfModules.pushforwardCongr₂.{u} _ (representedSmallEtaleBaseChangeIso B S hS τ
              (relativelyRepresentable_yoneda_map B S hS τ))
            (representedStructureMapRing_square B S hS τ
              (relativelyRepresentable_yoneda_map B S hS τ)) ≪≫
          (SheafOfModules.pushforwardComp.{u}
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS τ)
              (relativelyRepresentable_yoneda_map B S hS τ))
            (representedEquivSharp B S hS T')).symm).inv.app
          ((representedSmallEtaleModuleEquivalence B S hS T').symm.functor.obj M₀))
    (V : (SmallEtale B S hS (yoneda.obj T))ᵒᵖ)
    (z : ((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS τ)
      (relativelyRepresentable_yoneda_map B S hS τ)).obj M₀).val.obj V) :
    (R₀.val.app V).hom z =
      ((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj.map
        ((representedSmallEtaleEquivalence B S hS T').inverse.map
          ((representedSmallEtaleBaseChangeIso B S hS τ
            (relativelyRepresentable_yoneda_map B S hS τ)).inv.app V.unop)).op
        (((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj.map
          ((representedSmallEtaleEquivalence B S hS T').unitIso.inv.app
            ((smallBaseChange B S hS (representedSpaceMap B S hS τ)
              (relativelyRepresentable_yoneda_map B S hS τ)).obj V.unop)).op z) := by
  subst hR₀
  rfl

/-- `AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_comp_val_app_apply` followed by
`AlgebraicGeometry.Space.sections_smallBaseChangeModulePushforward_map_unit_comp_inv_app`: the
section over an étale chart `V` of the right-hand side morphism of the direct-image compatibility
is two restriction maps of `M₀` applied to the chart comparison. -/
theorem sections_modulePushforwardChartIso_comp_unit_inv_app
    (M₀ : SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
    (R₀ : @Quiver.Hom (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) _
      ((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS τ)
        (relativelyRepresentable_yoneda_map B S hS τ)).obj M₀)
        ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS τ) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T).functor).obj
            ((representedSmallEtaleModuleEquivalence B S hS T').symm.functor.obj M₀)))
    (hR₀ : R₀ = (smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS τ)
          (relativelyRepresentable_yoneda_map B S hS τ)).map
            ((representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction.unit.app M₀) ≫
        (SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
            (representedSchemeStructureMapRing B S hS τ) ≪≫
          SheafOfModules.pushforwardCongr₂.{u} _ (representedSmallEtaleBaseChangeIso B S hS τ
              (relativelyRepresentable_yoneda_map B S hS τ))
            (representedStructureMapRing_square B S hS τ
              (relativelyRepresentable_yoneda_map B S hS τ)) ≪≫
          (SheafOfModules.pushforwardComp.{u}
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS τ)
              (relativelyRepresentable_yoneda_map B S hS τ))
            (representedEquivSharp B S hS T')).symm).inv.app
          ((representedSmallEtaleModuleEquivalence B S hS T').symm.functor.obj M₀))
    (g : @CategoryTheory.Functor.obj
        (SheafOfModules.{u} (representedStructureRingSheaf B S hS T')) _
        (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) _
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules M₀ ⟶
      ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS τ) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor).obj
          ((representedSmallEtaleModuleEquivalence B S hS T').symm.functor.obj M₀)))
    (hg : g = (pushforwardModulesIsoModulePushforward B S hS (representedSpaceMap B S hS τ)).hom.app
      M₀ ≫ (modulePushforwardChartIso B S hS (representedSpaceMap B S hS τ)
        (relativelyRepresentable_yoneda_map B S hS τ)).hom.app M₀ ≫ R₀)
    (V : (SmallEtale B S hS (yoneda.obj T))ᵒᵖ)
    (x : ((smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules.obj
      M₀).val.obj V) :
    (g.val.app V).hom x =
      ((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj.map
        ((representedSmallEtaleEquivalence B S hS T').inverse.map
          ((representedSmallEtaleBaseChangeIso B S hS τ
            (relativelyRepresentable_yoneda_map B S hS τ)).inv.app V.unop)).op
        (((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj.map
          ((representedSmallEtaleEquivalence B S hS T').unitIso.inv.app
            ((smallBaseChange B S hS (representedSpaceMap B S hS τ)
              (relativelyRepresentable_yoneda_map B S hS τ)).obj V.unop)).op
          (@id (((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS τ)
            (relativelyRepresentable_yoneda_map B S hS τ)).obj M₀).val.obj V : Type u)
            (((chartComparison B S hS (representedSpaceMap B S hS τ)
              (relativelyRepresentable_yoneda_map B S hS τ)).hom.app
                (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS
                  ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩) M₀)).hom.app V x))) :=
  (modulePushforwardChartIso_hom_app_comp_val_app_apply τ M₀ V R₀ g hg x).trans
    (sections_smallBaseChangeModulePushforward_map_unit_comp_inv_app τ M₀ R₀ hR₀ V _)

/-- The four restrictions of the Zariski reading of the direct image compose to the inverse of
`AlgebraicGeometry.Space.baseChangeSelfOpensIso`: both are morphisms into the chart of a Zariski
open. -/
theorem baseChangeSelfOpensIso_inv_eq_comp
    (O : (TopologicalSpace.Opens ((BigFppfOver.toScheme B S hS).obj T))ᵒᵖ) :
    (representedSmallEtaleEquivalence B S hS T').inverse.map
        ((_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B)
          τ.left).hom.app O.unop) ≫
      (representedSmallEtaleEquivalence B S hS T').inverse.map
        ((_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) τ.left).map
          ((representedSmallEtaleEquivalence B S hS T).counitIso.inv.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property O.unop))) ≫
      (representedSmallEtaleEquivalence B S hS T').inverse.map
        ((representedSmallEtaleBaseChangeIso B S hS τ
          (relativelyRepresentable_yoneda_map B S hS τ)).inv.app
            ((selfOpensFunctor B S hS T).obj O.unop)) ≫
      (representedSmallEtaleEquivalence B S hS T').unitIso.inv.app
        ((smallBaseChange B S hS (representedSpaceMap B S hS τ)
          (relativelyRepresentable_yoneda_map B S hS τ)).obj
            ((selfOpensFunctor B S hS T).obj O.unop)) =
      (baseChangeSelfOpensIso τ O.unop).inv :=
  (cancel_mono (baseChangeSelfOpensIso τ O.unop).hom).1 (Subsingleton.elim _ _)

/-- The right-hand side of `AlgebraicGeometry.Space.ZariskiReadingDirectImageCompat` on sections
over a Zariski open `O`: its tail `CategoryTheory.Adjunction.rightAdjointSquareTail`, for the
morphism `g` of the reduction `CategoryTheory.Adjunction.rightAdjointSquareCompat_of_tail_trans`,
is the identification of sections `AlgebraicGeometry.Space.directImageSelfOpensModuleSection`. -/
theorem directImageSelfOpensModuleSection_eq_tail_section
    (M₀ : SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
    (R₀ : @Quiver.Hom (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) _
      ((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS τ)
        (relativelyRepresentable_yoneda_map B S hS τ)).obj M₀)
        ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS τ) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T).functor).obj
            ((representedSmallEtaleModuleEquivalence B S hS T').symm.functor.obj M₀)))
    (hR₀ : R₀ = (smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS τ)
          (relativelyRepresentable_yoneda_map B S hS τ)).map
            ((representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction.unit.app M₀) ≫
        (SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
            (representedSchemeStructureMapRing B S hS τ) ≪≫
          SheafOfModules.pushforwardCongr₂.{u} _ (representedSmallEtaleBaseChangeIso B S hS τ
              (relativelyRepresentable_yoneda_map B S hS τ))
            (representedStructureMapRing_square B S hS τ
              (relativelyRepresentable_yoneda_map B S hS τ)) ≪≫
          (SheafOfModules.pushforwardComp.{u}
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS τ)
              (relativelyRepresentable_yoneda_map B S hS τ))
            (representedEquivSharp B S hS T')).symm).inv.app
          ((representedSmallEtaleModuleEquivalence B S hS T').symm.functor.obj M₀))
    (g : @CategoryTheory.Functor.obj
        (SheafOfModules.{u} (representedStructureRingSheaf B S hS T')) _
        (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) _
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules M₀ ⟶
      ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS τ) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor).obj
          ((representedSmallEtaleModuleEquivalence B S hS T').symm.functor.obj M₀)))
    (hg : g = (pushforwardModulesIsoModulePushforward B S hS (representedSpaceMap B S hS τ)).hom.app
      M₀ ≫ (modulePushforwardChartIso B S hS (representedSpaceMap B S hS τ)
        (relativelyRepresentable_yoneda_map B S hS τ)).hom.app M₀ ≫ R₀)
    (O : (TopologicalSpace.Opens ((BigFppfOver.toScheme B S hS).obj T))ᵒᵖ)
    (x : ((((representedSmallEtaleModuleEquivalence B S hS T).symm.functor ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
          ((smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules.obj
            M₀)).val.obj O)) :
    directImageSelfOpensModuleSection τ O.unop M₀ x =
      (((@Adjunction.rightAdjointSquareTail
      (SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
      (SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
      _ _ ((BigFppfOver.toScheme B S hS).obj T).Modules
      ((BigFppfOver.toScheme B S hS).obj T').Modules
      _ _ _ _ (Scheme.Modules.instCategory (X := (BigFppfOver.toScheme B S hS).obj T))
      (Scheme.Modules.instCategory (X := (BigFppfOver.toScheme B S hS).obj T'))
      (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS τ))
      (@Stacks.RingedSpace.pushforwardFunctor
        (chartScheme (idEtaleChart B S hS T')).toSheafedSpace
        (chartScheme (idEtaleChart B S hS T)).toSheafedSpace
        (@ringedSpaceHom (chartScheme (idEtaleChart B S hS T'))
          (chartScheme (idEtaleChart B S hS T))
          (@CategoryTheory.Functor.map _ _ _ _ (BigFppfOver.toScheme B S hS)
            ((SmallEtale.toOver B S hS _).obj (idEtaleChart B S hS T'))
            ((SmallEtale.toOver B S hS _).obj (idEtaleChart B S hS T)) τ)))
      (representedSmallEtaleModuleEquivalence B S hS T).symm.functor
      (representedSmallEtaleModuleEquivalence B S hS T).functor
      (representedSmallEtaleModuleEquivalence B S hS T').symm.functor _ _
      ((representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction :
        (representedSmallEtaleModuleEquivalence B S hS T).inverse ⊣
          (representedSmallEtaleModuleEquivalence B S hS T).functor)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (zariskiReadingIso T')
      (SheafOfModules.pushforwardSquareIso.{u}
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          τ.left).toRingCatSheafHom
        (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
          T'.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
          T.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
          τ.left)
        (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B) τ.left)
        (_root_.AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso
          (associatedBigEtaleSite B) τ.left))
        (@CategoryTheory.Functor.obj
          (SheafOfModules.{u} (representedStructureRingSheaf B S hS T')) _
          (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) _
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules M₀)
        M₀ g).val.app O).hom x) := by
  rw [zariskiReadingCompat_tail_section τ M₀ g O x]
  simp only [sections_modulePushforwardChartIso_comp_unit_inv_app τ M₀ R₀ hR₀ g hg
    (Opposite.op ((selfOpensFunctor B S hS T).obj O.unop)) x]
  exact CategoryTheory.FunctorToTypes.map_op_apply_eq_of_comp_eq
    ((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj _ _ _ _
    (baseChangeSelfOpensIso_inv_eq_comp τ O) _

/-- **The identification of the Zariski reading of a direct image is the composite of the two
comparisons of routes of direct images**: `AlgebraicGeometry.Space.ZariskiReadingDirectImageCompat`
holds for every morphism `τ : T' ⟶ T` of the site.  Both sides are computed on sections over a
Zariski open `O` of `T`: each is the restriction of the chart comparison of the direct image along
the identification `AlgebraicGeometry.Space.baseChangeSelfOpensIso` of the base change of the chart
of `O` with the chart of `τ⁻¹(O)`. -/
theorem zariskiReadingDirectImageCompat : ZariskiReadingDirectImageCompat τ := by
  refine Adjunction.rightAdjointSquareCompat_of_tail_trans _ _ _
    (representedModulePushforwardSquareIso B S hS τ (relativelyRepresentable_yoneda_map B S hS τ))
    (modulePushforwardChartIso B S hS (representedSpaceMap B S hS τ)
      (relativelyRepresentable_yoneda_map B S hS τ))
    _ _ _ rfl _ _ _ _ _ _ (fun M₀ => ?_)
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun O => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine (zariskiReadingIso_hom_app_comp_zariskiDirectImageNatTrans_app_apply τ M₀ O x).trans ?_
  apply directImageSelfOpensModuleSection_eq_tail_section τ M₀ _ rfl
  congr


end AlgebraicGeometry.Space

end
