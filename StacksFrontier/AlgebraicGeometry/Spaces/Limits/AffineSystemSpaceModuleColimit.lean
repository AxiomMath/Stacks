module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSystemSmallEtaleModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackSquareComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteIff

/-!
# Stacks 07V7 for an inverse system of affine schemes, on their algebraic spaces

Let `c` be a cone on a cofiltered diagram `V` of objects of the big fppf site of `S` whose
underlying schemes are affine and form a limit.  The modules of an algebraic space are sheaves on
its small étale site.  This file proves the three clauses of the colimit assertion of Stacks 07V7
— equivalently of Stacks 01ZR — for the modules of finite presentation on the algebraic spaces
represented by the `V i` and by `c.pt`, with the inverse images of Stacks 03LU and their
composition comparisons `AlgebraicGeometry.Space.modulePullbackTriangle`:

* **faithfulness**: two morphisms of finitely presented modules at a stage whose inverse images
  to the limit agree have equal inverse images at a later stage;
* **fullness**: a morphism between the inverse images to the limit of two finitely presented
  modules at a stage is, through the comparisons, the inverse image of a morphism at a later
  stage;
* **essential surjectivity**: a finitely presented module on the limit is the inverse image of a
  finitely presented module at a stage.

They are read off the scheme-level Stacks 01ZR through the small étale sites of the underlying
schemes (`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineSystemSmallEtaleModuleColimit.lean`)
and the equivalence between the small étale site of a scheme and that of the algebraic space it
represents, which matches the inverse images coherently
(`AlgebraicGeometry.Space.representedModulePullbackIso_comp`).

## Main definitions

* `AlgebraicGeometry.Space.affineSpacePullbackSystem`: the pullback system of modules on the
  algebraic spaces represented by `V` and `c.pt`.
* `AlgebraicGeometry.Space.etalePullbackSystem`: the pullback system of modules on the small étale
  sites of the underlying schemes.
* `AlgebraicGeometry.Space.affineSpaceTransfer`: the comparison between the two, by the
  equivalences `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`.

## Main results

* `AlgebraicGeometry.Space.affineSpacePullbackSystem_faithfulness`, `_fullness` and
  `_essSurj`: the three clauses.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I] (V : I ⥤ BigFppfOver B S hS) (c : Cone V)

/-- The projection of the cone to a stage, with its source written as the vertex. -/
abbrev conePr (j : I) : c.pt ⟶ V.obj j := c.π.app j

omit [IsCofiltered I] in
/-- The projections of the cone commute with the transition morphisms. -/
theorem conePr_comp {j k : I} (e : j ⟶ k) : conePr B S hS V c j ≫ V.map e = conePr B S hS V c k :=
  c.w e

/-- **The pullback system of modules on the algebraic spaces represented by `V` and by `c.pt`**,
with the inverse images of Stacks 03LU along the represented morphisms, their composition
comparisons `AlgebraicGeometry.Space.modulePullbackTriangle`, and finite presentation in the sense
of Stacks 03DL (7) as the property of objects. -/
abbrev affineSpacePullbackSystem : Stacks.ModuleColimit.PullbackSystem.{u, u, u + 1, u + 1} I where
  C j := Modules.{u, u} B S hS (representedAlgebraicSpace B S hS (V.obj j)).obj
    (representedAlgebraicSpace B S hS (V.obj j)).property
  L := Modules.{u, u} B S hS (representedAlgebraicSpace B S hS c.pt).obj
    (representedAlgebraicSpace B S hS c.pt).property
  pb e := modulePullback B S hS (representedSpaceMap B S hS (V.map e))
  pbL j := modulePullback B S hS (representedSpaceMap B S hS (conePr B S hS V c j))
  comp {j _k} e := modulePullbackTriangle B S hS
    ((representedSpaceMap_comp B S hS (conePr B S hS V c j) (V.map e)).trans
      (congrArg (representedSpaceMap B S hS) (conePr_comp B S hS V c e)))
  P _ M := M.IsFinitePresentationOnSite
  PL M := M.IsFinitePresentationOnSite

/-- An object of the big fppf site, read as an object of the big étale site carried by the same
category of schemes. -/
abbrev etaleObj (T : BigFppfOver B S hS) : (associatedBigEtaleSite B).Scheme :=
  T.left

/-- A morphism of the big fppf site, read as a morphism between the objects
`AlgebraicGeometry.Space.etaleObj`. -/
abbrev etaleHom {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    etaleObj B S hS T' ⟶ etaleObj B S hS T :=
  g.left

/-- The underlying diagram in the big étale site carried by the same category of schemes. -/
abbrev etaleDiagram : I ⥤ (associatedBigEtaleSite B).Scheme where
  obj j := etaleObj B S hS (V.obj j)
  map e := etaleHom B S hS (V.map e)
  map_id j := congrArg (fun q => q.left) (V.map_id j)
  map_comp e e' := congrArg (fun q => q.left) (V.map_comp e e')

/-- The underlying cone in the big étale site carried by the same category of schemes. -/
abbrev etaleCone : Cone (etaleDiagram B S hS V) where
  pt := etaleObj B S hS c.pt
  π :=
    { app j := etaleHom B S hS (conePr B S hS V c j)
      naturality _j _k e := congrArg (fun q => q.left) (c.π.naturality e) }

/-- The reading of a module on the algebraic space represented by `T` on the small étale site of
the scheme underlying `T`, with its source written as the modules of the algebraic space. -/
abbrev reprInv (T : BigFppfOver B S hS) :
    Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).obj
        (representedAlgebraicSpace B S hS T).property ⥤
      SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) (etaleObj B S hS T).obj (etaleObj B S hS T).property) :=
  (representedSmallEtaleModuleEquivalence B S hS T).inverse

/-- The reading `AlgebraicGeometry.Space.reprInv` is fully faithful, being the inverse of an
equivalence. -/
def reprInvFullyFaithful (T : BigFppfOver B S hS) : (reprInv B S hS T).FullyFaithful :=
  (representedSmallEtaleModuleEquivalence B S hS T).fullyFaithfulInverse

/-- The pullback along the morphism of small étale ringed sites of a morphism of the big fppf
site, in the spelling of `AlgebraicGeometry.Space.etaleObj`. -/
abbrev etalePb {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :=
  SheafOfModules.pullback.{u} (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing
    (associatedBigEtaleSite B) (etaleHom B S hS g))

/-- The comparison of inverse images along a represented morphism with the pullback of the
underlying morphism of small étale ringed sites, at an arbitrary morphism. -/
abbrev affineSpaceβ {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    modulePullback B S hS (representedSpaceMap B S hS g) ⋙ reprInv B S hS T' ≅
      reprInv B S hS T ⋙ etalePb B S hS g :=
  representedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)

/-- The comparison of the two pullbacks along a composite, in the spelling of
`AlgebraicGeometry.Space.etaleObj`, transported along a factorization. -/
abbrev etaleComp {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T) (p : T'' ⟶ T)
    (hp : h ≫ g = p) :=
  _root_.AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso (associatedBigEtaleSite B)
      (etaleHom B S hS h) (etaleHom B S hS g) ≪≫
    eqToIso (congrArg (fun a => SheafOfModules.pullback.{u}
      (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B) a))
      (show etaleHom B S hS h ≫ etaleHom B S hS g = etaleHom B S hS p from
        congrArg (fun q => q.left) hp))

/-- **The pasting coherence of the identification of inverse images**, at an arbitrary
factorization `h ≫ g = p`, componentwise and in the orientation of
`Stacks.ModuleColimit.PullbackSystem.Transfer.coherence`. -/
theorem affineSpaceβ_coherence {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T)
    (p : T'' ⟶ T) (hp : h ≫ g = p)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).obj
      (representedAlgebraicSpace B S hS T).property) :
    (reprInv B S hS T'').map
        ((modulePullbackTriangle B S hS ((representedSpaceMap_comp B S hS h g).trans
          (congrArg (representedSpaceMap B S hS) hp))).hom.app M) =
      (affineSpaceβ B S hS p).hom.app M ≫
        (etaleComp B S hS h g p hp).symm.hom.app ((reprInv B S hS T).obj M) ≫
        (etalePb B S hS h).map ((affineSpaceβ B S hS g).inv.app M) ≫
        (affineSpaceβ B S hS h).inv.app
          ((modulePullback B S hS (representedSpaceMap B S hS g)).obj M) := by
  subst hp
  have key := representedModulePullbackIso_comp_inv B S hS h g
    (relativelyRepresentable_yoneda_map B S hS h) (relativelyRepresentable_yoneda_map B S hS g)
    (relativelyRepresentable_yoneda_map B S hS (h ≫ g)) M
  change ((reprInv B S hS T'').mapIso
      ((representedModulePullbackCompIso B S hS h g).app M)).inv = _
  symm
  refine (Iso.comp_hom_eq_id _).mp ?_
  have key' : (etalePb B S hS h).map ((affineSpaceβ B S hS g).inv.app M) ≫
      (affineSpaceβ B S hS h).inv.app
        ((modulePullback B S hS (representedSpaceMap B S hS g)).obj M) ≫
      (reprInv B S hS T'').map
        ((representedModulePullbackCompIso B S hS h g).hom.app M) =
      (_root_.AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso (associatedBigEtaleSite B)
          (etaleHom B S hS h) (etaleHom B S hS g)).hom.app ((reprInv B S hS T).obj M) ≫
        (affineSpaceβ B S hS (h ≫ g)).inv.app M := key
  simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.trans_inv, eqToIso_refl,
    Iso.refl_inv, Category.assoc, NatTrans.comp_app, NatTrans.id_app]
  rw [key', Iso.inv_hom_id_app_assoc]
  convert (affineSpaceβ B S hS (h ≫ g)).hom_inv_id_app M using 2

/-- `AlgebraicGeometry.Space.affineSpaceβ_coherence` with the inverse images, their comparisons
and the identifications of inverse images abstracted into variables, each pinned down by an
equation.  Instantiating it at the projections of two pullback systems, with `rfl` for the
equations, gives the coherence in exactly the spelling of the projections, which the kernel then
only has to match syntactically. -/
theorem affineSpaceβ_coherence_abstract {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T')
    (g : T' ⟶ T) (p : T'' ⟶ T) (hp : h ≫ g = p)
    (Pk : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).obj
        (representedAlgebraicSpace B S hS T).property ⥤
      Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T'').obj
        (representedAlgebraicSpace B S hS T'').property)
    (hPk : Pk = modulePullback B S hS (representedSpaceMap B S hS p))
    (Pe : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).obj
        (representedAlgebraicSpace B S hS T).property ⥤
      Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T').obj
        (representedAlgebraicSpace B S hS T').property)
    (hPe : Pe = modulePullback B S hS (representedSpaceMap B S hS g))
    (Pj : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T').obj
        (representedAlgebraicSpace B S hS T').property ⥤
      Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T'').obj
        (representedAlgebraicSpace B S hS T'').property)
    (hPj : Pj = modulePullback B S hS (representedSpaceMap B S hS h))
    (κ : Pk ≅ Pe ⋙ Pj) (hκ : HEq κ (modulePullbackTriangle B S hS
      ((representedSpaceMap_comp B S hS h g).trans (congrArg (representedSpaceMap B S hS) hp))))
    (Ak : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) (etaleObj B S hS T).obj (etaleObj B S hS T).property) ⥤
      SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) (etaleObj B S hS T'').obj (etaleObj B S hS T'').property))
    (hAk : Ak = etalePb B S hS p)
    (Ae : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) (etaleObj B S hS T).obj (etaleObj B S hS T).property) ⥤
      SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) (etaleObj B S hS T').obj (etaleObj B S hS T').property))
    (hAe : Ae = etalePb B S hS g)
    (Aj : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) (etaleObj B S hS T').obj (etaleObj B S hS T').property) ⥤
      SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) (etaleObj B S hS T'').obj (etaleObj B S hS T'').property))
    (hAj : Aj = etalePb B S hS h)
    (l : Ak ≅ Ae ⋙ Aj) (hl : HEq l (etaleComp B S hS h g p hp).symm)
    (βk : Pk ⋙ reprInv B S hS T'' ≅ reprInv B S hS T ⋙ Ak) (hβk : HEq βk (affineSpaceβ B S hS p))
    (βe : Pe ⋙ reprInv B S hS T' ≅ reprInv B S hS T ⋙ Ae) (hβe : HEq βe (affineSpaceβ B S hS g))
    (βj : Pj ⋙ reprInv B S hS T'' ≅ reprInv B S hS T' ⋙ Aj) (hβj : HEq βj (affineSpaceβ B S hS h))
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).obj
        (representedAlgebraicSpace B S hS T).property) :
    (reprInv B S hS T'').map (κ.hom.app M) =
      βk.hom.app M ≫ l.hom.app ((reprInv B S hS T).obj M) ≫
        Aj.map (βe.inv.app M) ≫ βj.inv.app (Pe.obj M) := by
  subst hPk hPe hPj hAk hAe hAj
  obtain rfl := eq_of_heq hκ
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hβk
  obtain rfl := eq_of_heq hβe
  obtain rfl := eq_of_heq hβj
  refine Eq.trans ?_ ((affineSpaceβ_coherence B S hS h g p hp M).trans ?_) <;> rfl

/-- Finite presentation of a module on a represented algebraic space, read on the small étale site
of the representing scheme. -/
theorem isFinitePresentation_reprInv_obj_iff (T : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).obj
      (representedAlgebraicSpace B S hS T).property) :
    ((reprInv B S hS T).obj M).IsFinitePresentation ↔ M.IsFinitePresentationOnSite := by
  have : ∀ X : (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS T).obj
      (representedAlgebraicSpace B S hS T).property).C,
      HasSheafify ((smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS T).obj
        (representedAlgebraicSpace B S hS T).property).J.over X) AddCommGrpCat.{u} :=
    fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  rw [show ((reprInv B S hS T).obj M).IsFinitePresentation ↔
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj M).IsFinitePresentation
      from Iff.rfl, isFinitePresentation_representedSmallEtaleModule_iff,
    SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation]
  exact ⟨fun h => Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((representedSmallEtaleModuleEquivalence B S hS T).counitIso.app M) h,
    fun h => Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((representedSmallEtaleModuleEquivalence B S hS T).counitIso.app M).symm h⟩

/-- The pullback system of modules on the small étale sites of the schemes underlying `V` and
`c.pt`, in the spelling of `AlgebraicGeometry.Space.etaleObj`; it is
`AlgebraicGeometry.SmallEtale.smallEtalePullbackSystem` of `AlgebraicGeometry.Space.etaleDiagram`
and `AlgebraicGeometry.Space.etaleCone` (`AlgebraicGeometry.Space.etalePullbackSystem_eq`). -/
abbrev etalePullbackSystem : Stacks.ModuleColimit.PullbackSystem.{u, u, u + 1, u + 1} I where
  C j := SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
    (associatedBigEtaleSite B) (etaleObj B S hS (V.obj j)).obj (etaleObj B S hS (V.obj j)).property)
  L := SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
    (associatedBigEtaleSite B) (etaleObj B S hS c.pt).obj (etaleObj B S hS c.pt).property)
  pb e := etalePb B S hS (V.map e)
  pbL j := etalePb B S hS (conePr B S hS V c j)
  comp {j k} e := (etaleComp B S hS (conePr B S hS V c j) (V.map e) (conePr B S hS V c k)
    (conePr_comp B S hS V c e)).symm
  P _ M := M.IsFinitePresentation
  PL M := M.IsFinitePresentation

omit [IsCofiltered I] in
/-- `AlgebraicGeometry.Space.etalePullbackSystem` is the pullback system of the small étale sites
of `AlgebraicGeometry.Space.etaleDiagram` and `AlgebraicGeometry.Space.etaleCone`. -/
theorem etalePullbackSystem_eq : etalePullbackSystem B S hS V c =
    AlgebraicGeometry.SmallEtale.smallEtalePullbackSystem (associatedBigEtaleSite B)
      (etaleDiagram B S hS V) (etaleCone B S hS V c) :=
  rfl

/- The inverse images and their composition comparisons are not unfolded below, so that the
projections of the pullback systems are matched with them without unfolding them. -/
attribute [local irreducible] modulePullback modulePullbackTriangle SheafOfModules.pullback
  _root_.AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso

omit [IsCofiltered I] in
/-- The pasting coherence of `AlgebraicGeometry.Space.affineSpaceβ` with the comparisons of the
pullback systems `AlgebraicGeometry.Space.etalePullbackSystem` and
`AlgebraicGeometry.Space.affineSpacePullbackSystem`, in the spelling of their projections. -/
theorem affineSpaceTransfer_coherence {j k : I} (e : j ⟶ k)
    (M : (affineSpacePullbackSystem B S hS V c).C k) :
    (reprInv B S hS c.pt).map (((affineSpacePullbackSystem B S hS V c).comp e).hom.app M) =
      (affineSpaceβ B S hS (conePr B S hS V c k)).hom.app M ≫
        ((etalePullbackSystem B S hS V c).comp e).hom.app ((reprInv B S hS (V.obj k)).obj M) ≫
        ((etalePullbackSystem B S hS V c).pbL j).map ((affineSpaceβ B S hS (V.map e)).inv.app M) ≫
        (affineSpaceβ B S hS (conePr B S hS V c j)).inv.app
          (((affineSpacePullbackSystem B S hS V c).pb e).obj M) := by
  have H := affineSpaceβ_coherence_abstract B S hS (conePr B S hS V c j) (V.map e)
    (conePr B S hS V c k) (conePr_comp B S hS V c e)
    ((affineSpacePullbackSystem B S hS V c).pbL k) rfl
    ((affineSpacePullbackSystem B S hS V c).pb e) rfl
    ((affineSpacePullbackSystem B S hS V c).pbL j) rfl
    ((affineSpacePullbackSystem B S hS V c).comp e) HEq.rfl
    ((etalePullbackSystem B S hS V c).pbL k) rfl ((etalePullbackSystem B S hS V c).pb e) rfl
    ((etalePullbackSystem B S hS V c).pbL j) rfl ((etalePullbackSystem B S hS V c).comp e) HEq.rfl
    (affineSpaceβ B S hS (conePr B S hS V c k)) HEq.rfl (affineSpaceβ B S hS (V.map e)) HEq.rfl
    (affineSpaceβ B S hS (conePr B S hS V c j)) HEq.rfl M
  refine Eq.trans ?_ (H.trans ?_) <;> rfl

/-- **The comparison of modules on represented algebraic spaces with modules on the small étale
sites of the representing schemes**, as a comparison of pullback systems. -/
def affineSpaceTransfer :
    Stacks.ModuleColimit.PullbackSystem.Transfer (etalePullbackSystem B S hS V c)
      (affineSpacePullbackSystem B S hS V c) where
  F j := reprInv B S hS (V.obj j)
  FL := reprInv B S hS c.pt
  β e := affineSpaceβ B S hS (V.map e)
  βL j := affineSpaceβ B S hS (conePr B S hS V c j)
  coherence := by
    intro j k e M
    refine Eq.trans ?_ ((affineSpaceTransfer_coherence B S hS V c e M).trans ?_)
    · rfl
    · rfl
  Q _ M := M.IsQuasicoherentOnSite
  QL M := M.IsQuasicoherentOnSite
  Q_of_P _ M hM := by
    have : M.IsFinitePresentationOnSite := hM
    infer_instance
  Q_pb e M hM := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M hM
  QL_pbL j M hM := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M hM
  faithful j _ _ _ _ f g h := (reprInvFullyFaithful B S hS (V.obj j)).map_injective h
  full j _ _ _ _ f := ⟨(reprInvFullyFaithful B S hS (V.obj j)).preimage f,
    (reprInvFullyFaithful B S hS (V.obj j)).map_preimage f⟩
  faithfulL _ _ f g h := (reprInvFullyFaithful B S hS c.pt).map_injective h
  fullL _ _ f := ⟨(reprInvFullyFaithful B S hS c.pt).preimage f,
    (reprInvFullyFaithful B S hS c.pt).map_preimage f⟩
  P_map j M hM := (isFinitePresentation_reprInv_obj_iff B S hS _ M).2 hM
  PL_map M hM := (isFinitePresentation_reprInv_obj_iff B S hS _ M).2 hM
  essSurjP j X hX := by
    refine ⟨(representedSmallEtaleModuleEquivalence B S hS (V.obj j)).functor.obj X, ?_,
      ⟨((representedSmallEtaleModuleEquivalence B S hS (V.obj j)).unitIso.app X).symm⟩⟩
    refine (isFinitePresentation_reprInv_obj_iff B S hS _ _).1 ?_
    exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((representedSmallEtaleModuleEquivalence B S hS (V.obj j)).unitIso.app X) hX

variable (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))

include hV hc in
/-- The three clauses of Stacks 01ZR on the small étale sites of the schemes underlying `V`. -/
theorem etaleClauses :
    (etalePullbackSystem B S hS V c).Faithfulness ∧ (etalePullbackSystem B S hS V c).Fullness ∧
      (etalePullbackSystem B S hS V c).EssSurj := by
  rw [etalePullbackSystem_eq]
  have hV' : ∀ i, IsAffine ((etaleDiagram B S hS V ⋙ (associatedBigEtaleSite B).inclusion).obj i) :=
    hV
  have : ∀ {i j : I} (f : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom
        ((etaleDiagram B S hS V ⋙ (associatedBigEtaleSite B).inclusion).map f) :=
    fun _ => inferInstance
  have : ∀ i, CompactSpace ((etaleDiagram B S hS V ⋙ (associatedBigEtaleSite B).inclusion).obj i) :=
    fun _ => inferInstance
  have : ∀ i, QuasiSeparatedSpace
      ((etaleDiagram B S hS V ⋙ (associatedBigEtaleSite B).inclusion).obj i) :=
    fun _ => inferInstance
  have hc' : IsLimit ((associatedBigEtaleSite B).inclusion.mapCone (etaleCone B S hS V c)) := hc
  exact ⟨AlgebraicGeometry.SmallEtale.smallEtalePullbackSystem_faithfulness _ _ _ hc',
    AlgebraicGeometry.SmallEtale.smallEtalePullbackSystem_fullness _ _ _ hc',
    AlgebraicGeometry.SmallEtale.smallEtalePullbackSystem_essSurj _ _ _ hc'⟩

include hV hc in
/-- **Stacks 07V7 (3) for an inverse system of affine schemes**, on their algebraic spaces: two
morphisms of modules of finite presentation at a stage whose inverse images to the limit agree
have equal inverse images at a later stage. -/
theorem affineSpacePullbackSystem_faithfulness :
    (affineSpacePullbackSystem B S hS V c).Faithfulness :=
  (affineSpaceTransfer B S hS V c).faithfulness (etaleClauses B S hS V c hV hc).1

include hV hc in
/-- **Stacks 07V7 (2) for an inverse system of affine schemes**, on their algebraic spaces: a
morphism between the inverse images to the limit of two modules of finite presentation at a stage
is, through the comparisons `AlgebraicGeometry.Space.modulePullbackTriangle`, the inverse image of
a morphism at a later stage. -/
theorem affineSpacePullbackSystem_fullness :
    (affineSpacePullbackSystem B S hS V c).Fullness :=
  (affineSpaceTransfer B S hS V c).fullness (etaleClauses B S hS V c hV hc).2.1

include hV hc in
/-- **Stacks 07V7 (1) for an inverse system of affine schemes**, on their algebraic spaces: a
module of finite presentation on the limit is the inverse image of a module of finite presentation
at a stage. -/
theorem affineSpacePullbackSystem_essSurj :
    (affineSpacePullbackSystem B S hS V c).EssSurj :=
  (affineSpaceTransfer B S hS V c).essSurj (etaleClauses B S hS V c hV hc).2.2
    (fun M hM => by
      have : M.IsFinitePresentationOnSite := hM
      change M.IsQuasicoherentOnSite
      infer_instance)

end AlgebraicGeometry.Space

end
