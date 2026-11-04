module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardNaturalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiBaseChange

/-!
# The Zariski reading of a direct image along a morphism of test objects, on modules

Let `τ : T' ⟶ T` be a morphism of the big fppf category over `S` and `φ` the morphism of
represented algebraic spaces it induces.  For a sheaf of modules `M` on the small étale site of
`yoneda.obj T'`, the sections over a Zariski open `O` of `T` of the direct image `φ_* M` are the
sections of `M` over the chart of `τ⁻¹(O)`
(`AlgebraicGeometry.Space.directImageSelfOpensSection`).  This file shows that this
identification is additive, linear over the scheme morphism of `τ`, and compatible with
restriction to smaller opens.

## Main definitions

* `AlgebraicGeometry.Space.directImageSelfOpensModuleSection`: the identification, read from
  the Zariski reading of `φ_* M` to the direct image along `τ` of the Zariski reading of `M`.

## Main results

* `AlgebraicGeometry.Space.directImageSelfOpensModuleSection_add` and
  `AlgebraicGeometry.Space.directImageSelfOpensModuleSection_smul`: it is linear.
* `AlgebraicGeometry.Space.directImageSelfOpensSection_restrict`: it commutes with restriction.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Modules

variable {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)

/-- The structure sheaf of rings of the small étale site of a test object. -/
noncomputable abbrev testRing (T' : BigFppfOver B S hS) :=
  structureRingSheaf B S hS (yonedaSpace B S hS T')

/-- The identification of sections, for the underlying sheaf of a sheaf of modules, from the
Zariski reading of the direct image to the direct image of the Zariski reading. -/
noncomputable def directImageSelfOpensModuleSection
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T')))
    (x : ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
        ((testToposHom τ).pushforwardModules.obj M)).val.obj (op O)) :
    ((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ)).obj
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj M)).val.obj (op O) :=
  directImageSelfOpensSection τ O ((Sheaf.moduleSheafFunctor (testRing T')).obj M) (by exact x)

/-- The identification of sections is additive. -/
theorem directImageSelfOpensModuleSection_add (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T')))
    (x y : ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
        ((testToposHom τ).pushforwardModules.obj M)).val.obj (op O)) :
    directImageSelfOpensModuleSection τ O M (x + y) =
      directImageSelfOpensModuleSection τ O M x + directImageSelfOpensModuleSection τ O M y := by
  have := (testToposHom τ).toToposHom.adj.isRightAdjoint
  exact ((Sheaf.moduleAddObj_naturality (testRing T') M
    (directImageSelfOpensNatTrans τ O) x y).trans
    (Sheaf.sectionsFunctor_map_moduleAddHom (testRing T') M
      (op ((selfOpensFunctor B S hS T').obj (preimageOpens τ O)))
      (directImageSelfOpensModuleSection τ O M x) (directImageSelfOpensModuleSection τ O M y)))

/-- The identification of sections is linear over the scheme morphism of `τ`. -/
theorem directImageSelfOpensModuleSection_smul (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T')))
    (r : (chartScheme (idEtaleChart B S hS T)).ringCatSheaf.obj.obj (op O))
    (x : ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
        ((testToposHom τ).pushforwardModules.obj M)).val.obj (op O)) :
    directImageSelfOpensModuleSection τ O M (r • x) =
      (show ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.obj.obj (op O) from r) •
        directImageSelfOpensModuleSection τ O M x := by
  have := (testToposHom τ).toToposHom.adj.isRightAdjoint
  have hr : (directImageSelfOpensNatTrans τ O).app (Sheaf.ringSheaf (testRing T'))
      ((testToposHom τ).structureRingMap.hom.app _
        ((selfOpensStructureMap B S hS T).hom.app (op O) r)) =
      (selfOpensStructureMap B S hS T').hom.app (op (preimageOpens τ O))
          (((BigFppfOver.toScheme B S hS).map τ).app O r) := by
    rw [show (testToposHom τ).structureRingMap =
        structureSharp B S hS (representedSpaceMap B S hS τ) from
      map_structureSharpCommRing B S hS (representedSpaceMap B S hS τ)]
    exact directImageSelfOpensSection_structureSharp τ O r
  exact Sheaf.natTrans_moduleSMulObj (testRing T') M
    (directImageSelfOpensNatTrans τ O) _ x _ hr

/-- The identification of sections commutes with restriction to a smaller open. -/
theorem directImageSelfOpensSection_restrict (O O' : (chartScheme (idEtaleChart B S hS T)).Opens)
    (h : O' ≤ O) (F : Sheaf (SmallEtale.topology B S hS (yoneda.obj T')) (Type u))
    (x : ((testToposHom τ).toToposHom.pushforward.obj F).obj.obj
      (op ((selfOpensFunctor B S hS T).obj O))) :
    directImageSelfOpensSection τ O' F
        (((testToposHom τ).toToposHom.pushforward.obj F).obj.map
          ((selfOpensFunctor B S hS T).map (homOfLE h)).op x) =
      F.obj.map ((selfOpensFunctor B S hS T').map
        (homOfLE (Scheme.Hom.preimage_mono _ h))).op (directImageSelfOpensSection τ O F x) := by
  have := subsingleton_inverseImage_selfOpens (representedSpaceMap B S hS τ) O
    (op ((selfOpensFunctor B S hS T').obj (preimageOpens τ O')))
  refine Stacks.Sites.SheafSection.natural_family_ext (testToposHom τ).toToposHom.adj
    (op ((selfOpensFunctor B S hS T).obj O))
    (fun F x => directImageSelfOpensSection τ O' F
        (((testToposHom τ).toToposHom.pushforward.obj F).obj.map
          ((selfOpensFunctor B S hS T).map (homOfLE h)).op x))
    (fun F x => F.obj.map ((selfOpensFunctor B S hS T').map
        (homOfLE (Scheme.Hom.preimage_mono _ h))).op (directImageSelfOpensSection τ O F x))
    (fun g x => ?_) (fun g x => ?_) F x
  · dsimp only
    rw [← NatTrans.naturality_apply ((testToposHom τ).toToposHom.pushforward.map g).hom]
    exact directImageSelfOpensSection_map τ O' g _
  · dsimp only
    rw [directImageSelfOpensSection_map]
    exact (NatTrans.naturality_apply g.hom _ _).symm

/-- The restriction maps of the Zariski reading of a direct image are those of the underlying
direct image of sheaves of sets. -/
theorem zariskiReading_pushforwardModules_map_apply
    (M : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T')))
    {O O' : (chartScheme (idEtaleChart B S hS T)).Opensᵒᵖ} (i : O ⟶ O')
    (x : ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
        ((testToposHom τ).pushforwardModules.obj M)).val.obj O) :
    ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
          ((testToposHom τ).pushforwardModules.obj M)).val.map i x =
      ((testToposHom τ).toToposHom.pushforward.obj
        ((Sheaf.moduleSheafFunctor (testRing T')).obj M)).obj.map
          ((selfOpensFunctor B S hS T).map i.unop).op x :=
  rfl

/-- The restriction maps of the direct image along `τ` of the Zariski reading. -/
theorem pushforward_zariskiReading_map_apply
    (M : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T')))
    {O O' : (chartScheme (idEtaleChart B S hS T)).Opensᵒᵖ} (i : O ⟶ O')
    (y : ((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ)).obj
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj M)).val.obj O) :
    ((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ)).obj
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj M)).val.map i y =
      M.val.map ((selfOpensFunctor B S hS T').map
        ((TopologicalSpace.Opens.map ((BigFppfOver.toScheme B S hS).map τ).base).map
          i.unop)).op y :=
  rfl

/-- The identification of sections commutes with the restriction maps of the two presheaves. -/
theorem directImageSelfOpensModuleSection_naturality
    (M : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T')))
    {O O' : (chartScheme (idEtaleChart B S hS T)).Opensᵒᵖ} (i : O ⟶ O')
    (x : ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
        ((testToposHom τ).pushforwardModules.obj M)).val.obj O) :
    directImageSelfOpensModuleSection τ O'.unop M
        (((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
          ((testToposHom τ).pushforwardModules.obj M)).val.map i x) =
      ((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ)).obj
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj M)).val.map i
        (directImageSelfOpensModuleSection τ O.unop M x) := by
  refine (congrArg (directImageSelfOpensModuleSection τ O'.unop M)
    (zariskiReading_pushforwardModules_map_apply τ M i x)).trans ?_
  refine (directImageSelfOpensSection_restrict τ O.unop O'.unop (leOfHom i.unop)
    ((Sheaf.moduleSheafFunctor (testRing T')).obj M) x).trans ?_
  refine Eq.trans ?_ (pushforward_zariskiReading_map_apply τ M i _).symm
  refine (congrArg (fun k => ((Sheaf.moduleSheafFunctor (testRing T')).obj M).obj.map k
      (directImageSelfOpensSection τ O.unop ((Sheaf.moduleSheafFunctor (testRing T')).obj M) x))
    (congrArg Quiver.Hom.op (congrArg (selfOpensFunctor B S hS T').map
      (Subsingleton.elim _
        ((TopologicalSpace.Opens.map ((BigFppfOver.toScheme B S hS).map τ).base).map
          i.unop))))).trans ?_
  rfl

/-- The identification of sections, as a morphism of presheaves of abelian groups. -/
def zariskiDirectImagePresheafHom
    (M : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T'))) :
    ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
        ((testToposHom τ).pushforwardModules.obj M)).val.presheaf ⟶
      ((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ)).obj
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj M)).val.presheaf where
  app O := AddCommGrpCat.ofHom (AddMonoidHom.mk' (directImageSelfOpensModuleSection τ O.unop M)
    (directImageSelfOpensModuleSection_add τ O.unop M))
  naturality _ _ i := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
    directImageSelfOpensModuleSection_naturality τ M i x)

/-- **The Zariski reading of a direct image along a morphism of test objects, on modules.**
For a sheaf of modules `M` on the small étale site of `yoneda.obj T'`, the Zariski reading on
`T` of `φ_* M` maps to the direct image along `τ` of the Zariski reading of `M` on `T'`: on
sections over an open `O` it is the identification of the sections of `φ_* M` over `O` with
those of `M` over `τ⁻¹(O)`. -/
def zariskiDirectImageModuleHom
    (M : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T'))) :
    (SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
        ((testToposHom τ).pushforwardModules.obj M) ⟶
      (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ)).obj
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj M) :=
  ⟨PresheafOfModules.homMk (zariskiDirectImagePresheafHom τ M)
    (fun O r x => directImageSelfOpensModuleSection_smul τ O.unop M r x)⟩

/-- On sections over an open `O`, `zariskiDirectImageModuleHom τ M` is
`directImageSelfOpensModuleSection τ O.unop M`. -/
theorem zariskiDirectImageModuleHom_val_app_apply
    (M : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T')))
    (O : (chartScheme (idEtaleChart B S hS T)).Opensᵒᵖ)
    (x : ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
        ((testToposHom τ).pushforwardModules.obj M)).val.obj O) :
    (zariskiDirectImageModuleHom τ M).val.app O x =
      directImageSelfOpensModuleSection τ O.unop M x :=
  rfl

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom) in
open Stacks.Sheaves.GradedAlgebraEssentiallySmall in
/-- **The Zariski reading of a direct image along a morphism of test objects.** For a sheaf of
graded algebras `E` on the small étale site of `yoneda.obj T'`, the Zariski reading on `T` of
`φ_* E` maps to the direct image along `τ` of the Zariski reading of `E` on `T'`, as sheaves of
graded algebras. -/
def zariskiDirectImageHom
    (E : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS T'))) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (zariskiReading T ((gradedPush (testToposHom τ)).obj E))
      (Stacks.RingedSpace.pushforwardAlgebra (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))
        (zariskiReading T' E)) where
  app n := zariskiDirectImageModuleHom τ (E.piece n)
  map_mul i j O x y :=
    natural_family_mul (testToposHom τ) (op ((selfOpensFunctor B S hS T).obj O.unop))
      (op ((selfOpensFunctor B S hS T').obj (preimageOpens τ O.unop)))
      (directImageSelfOpensSection τ O.unop) (directImageSelfOpensSection_map τ O.unop) E i j x y
  map_one O :=
    natural_family_one (testToposHom τ) (op ((selfOpensFunctor B S hS T).obj O.unop))
      (op ((selfOpensFunctor B S hS T').obj (preimageOpens τ O.unop)))
      (directImageSelfOpensSection τ O.unop) (directImageSelfOpensSection_map τ O.unop) E

/-- The identification of sections is natural in the sheaf of modules. -/
theorem zariskiDirectImageModuleHom_naturality
    {M M' : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T'))} (g : M ⟶ M') :
    (SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
        ((testToposHom τ).pushforwardModules.map g) ≫ zariskiDirectImageModuleHom τ M' =
      zariskiDirectImageModuleHom τ M ≫
        (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ)).map
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).map g) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun O => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact directImageSelfOpensSection_map τ O.unop ((Sheaf.moduleSheafFunctor (testRing T')).map g) x

/-- The identification of sections is bijective on every open. -/
theorem directImageSelfOpensSection_bijective (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (F : Sheaf (SmallEtale.topology B S hS (yoneda.obj T')) (Type u)) :
    Function.Bijective (directImageSelfOpensSection τ O F) := by
  let e := (smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS τ) ≪≫
    chartRanIso B S hS (representedSpaceMap B S hS τ)
      (relativelyRepresentable_yoneda_map B S hS τ)).app F
  have h1 : Function.Bijective (e.hom.hom.app (op ((selfOpensFunctor B S hS T).obj O))) := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    exact inferInstanceAs (IsIso (((sheafToPresheaf _ _).mapIso e).app _).hom)
  have h2 : Function.Bijective (F.obj.map (baseChangeSelfOpensIso τ O).inv.op) := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    exact inferInstanceAs (IsIso (F.obj.mapIso (baseChangeSelfOpensIso τ O).symm.op).hom)
  exact h2.comp h1

/-- A morphism of sheaves of modules which is bijective on sections is an isomorphism. -/
theorem _root_.SheafOfModules.isIso_of_bijective_val_app' {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (g : M ⟶ N) (hg : ∀ U : Cᵒᵖ, Function.Bijective (g.val.app U).hom) : IsIso g := by
  have hiso : IsIso ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map g) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun U => (ConcreteCategory.isIso_iff_bijective _).mpr (hg U)
  exact isIso_of_reflects_iso g (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj)

/-- **The identification of sections is an isomorphism of sheaves of modules.** -/
instance isIso_zariskiDirectImageModuleHom
    (M : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T'))) :
    IsIso (zariskiDirectImageModuleHom τ M) :=
  SheafOfModules.isIso_of_bijective_val_app' _ fun O =>
    directImageSelfOpensSection_bijective τ O.unop ((Sheaf.moduleSheafFunctor (testRing T')).obj M)

end Modules

end AlgebraicGeometry.Space
