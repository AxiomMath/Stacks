module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationBiproduct
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationExtension
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Quasi-coherent modules as colimits of finitely presented modules

On a quasi-compact and quasi-separated scheme every quasi-coherent module is a filtered colimit
of finitely presented modules, and may equivalently be written as the colimit of a system of
finitely presented modules indexed by a directed partially ordered set.  A quasi-coherent module
of finite type is consequently a quotient of a finitely presented module, and the quotient map
may be arranged to be an isomorphism over any quasi-compact open on which the module is already
of finite presentation.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.FinitePresentationOver F` is the category of finitely
  presented modules mapping to `F`.
* `AlgebraicGeometry.Scheme.Modules.finitePresentationOverDiagram F` and
  `AlgebraicGeometry.Scheme.Modules.finitePresentationOverCocone F` are the tautological
  diagram on that category and its cocone with cone point `F`.
* `AlgebraicGeometry.Scheme.Modules.stalkAbelianFunctor x` takes the stalk at `x`, as a functor
  into abelian groups.

## Main results

* `AlgebraicGeometry.exists_filtered_diagram_of_isFinitePresentation`: a quasi-coherent module
  on a quasi-compact, quasi-separated scheme is a filtered colimit of finitely presented
  modules.
* `AlgebraicGeometry.exists_directed_system_of_isFinitePresentation`: the same with a directed
  partially ordered index set.
* `AlgebraicGeometry.exists_finitePresentation_epi`: a quasi-coherent module of finite type is
  a quotient of a finitely presented module.
* `AlgebraicGeometry.exists_finitePresentation_epi_isIso_restrict`: the quotient map may be
  taken to be an isomorphism over a quasi-compact open on which the module is of finite
  presentation.
* `AlgebraicGeometry.Scheme.Modules.isFiltered_finitePresentationOver` and
  `AlgebraicGeometry.Scheme.Modules.essentiallySmall_finitePresentationOver`: the category of
  finitely presented modules over `F` is filtered and essentially small.

## References

* [Stacks Project, Tag 01PJ](https://stacks.math.columbia.edu/tag/01PJ)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
* [Stacks Project, Tag 080V](https://stacks.math.columbia.edu/tag/080V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules Opposite TopologicalSpace
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

namespace Scheme.Modules

/-! ### The category of finitely presented modules over a given module -/

/-- The category of finitely presented `𝒪_X`-modules equipped with a morphism to `F`: the full
subcategory of `Over F` on the objects whose source is of finite presentation. -/
abbrev FinitePresentationOver (F : X.Modules) :=
  ObjectProperty.FullSubcategory (fun A : Over F => A.left.IsFinitePresentation)

/-- The tautological diagram of finitely presented modules over `F`. -/
def finitePresentationOverDiagram (F : X.Modules) : FinitePresentationOver F ⥤ X.Modules where
  obj i := i.1.left
  map f := f.1.left
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The tautological cocone on `finitePresentationOverDiagram F` with cone point `F`, whose
legs are the structural morphisms to `F`. -/
def finitePresentationOverCocone (F : X.Modules) : Cocone (finitePresentationOverDiagram F) where
  pt := F
  ι :=
    { app := fun i => i.1.hom
      naturality := fun _ _ f => Over.w f.1 }

/-- The category of finitely presented modules over `F` is filtered. -/
instance isFiltered_finitePresentationOver (F : X.Modules) :
    IsFiltered (FinitePresentationOver F) := by
  classical
  have : IsFilteredOrEmpty (FinitePresentationOver F) :=
    { cocone_objs := by
        intro A B
        have : A.1.left.IsFinitePresentation := A.2
        have : B.1.left.IsFinitePresentation := B.2
        have hsum : (A.1.left ⊞ B.1.left).IsFinitePresentation :=
          isFinitePresentation_biprod _ _
        exact ⟨⟨Over.mk (biprod.desc A.1.hom B.1.hom), hsum⟩,
          ObjectProperty.homMk (Over.homMk biprod.inl),
          ObjectProperty.homMk (Over.homMk biprod.inr), trivial⟩
      cocone_maps := by
        intro A B f g
        let d : A.1.left ⟶ B.1.left := f.1.left - g.1.left
        have hd : d ≫ B.1.hom = 0 := by
          dsimp [d]
          rw [Preadditive.sub_comp, Over.w f.1, Over.w g.1, sub_self]
        have : B.1.left.IsFinitePresentation := B.2
        have : A.1.left.IsFinitePresentation := A.2
        have : A.1.left.IsFiniteType :=
          SheafOfModules.instIsFiniteTypeOfIsFinitePresentation A.1.left
        have : (cokernel d).IsFinitePresentation :=
          Stacks.SheafOfModules.isFinitePresentation_cokernel d
        refine ⟨⟨Over.mk (cokernel.desc d B.1.hom hd),
            show (cokernel d).IsFinitePresentation from inferInstance⟩,
          ObjectProperty.homMk (Over.homMk (cokernel.π d)), ?_⟩
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        change f.1.left ≫ cokernel.π d = g.1.left ≫ cokernel.π d
        apply sub_eq_zero.mp
        rw [← Preadditive.sub_comp]
        exact cokernel.condition d }
  have : Nonempty (FinitePresentationOver F) :=
    ⟨⟨Over.mk (0 : (0 : X.Modules) ⟶ F), isFinitePresentation_zero X⟩⟩
  exact IsFiltered.mk

/-- The category of finitely presented modules over `F` is essentially small, in the universe of
the scheme. -/
theorem essentiallySmall_finitePresentationOver (F : X.Modules) :
    EssentiallySmall.{u} (FinitePresentationOver F) := by
  have hFT : ObjectProperty.EssentiallySmall.{u} (fun M : X.Modules => M.IsFiniteType) :=
    Stacks.SheafOfModules.essentiallySmall_isFiniteType X.toRingedSpace
  let P : ObjectProperty X.Modules := fun M => M.IsFinitePresentation
  have hFP : ObjectProperty.EssentiallySmall.{u} P :=
    ObjectProperty.EssentiallySmall.of_le (P := P)
      (Q := fun M : X.Modules => M.IsFiniteType)
      fun M h => have : M.IsFinitePresentation := h
        SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M
  let T : FinitePresentationOver F ⥤ CostructuredArrow P.ι F :=
    { obj A := CostructuredArrow.mk (Y := (⟨A.1.left, A.2⟩ : P.FullSubcategory)) A.1.hom
      map f := CostructuredArrow.homMk (ObjectProperty.homMk f.1.left) (Over.w f.1) }
  have : T.Full := ⟨fun f => ⟨ObjectProperty.homMk (Over.homMk f.left.hom f.w), rfl⟩⟩
  have : T.Faithful := ⟨fun h => ObjectProperty.hom_ext _
    (Over.OverMorphism.ext (congrArg (fun t => t.left.hom) h))⟩
  exact essentiallySmall_of_fully_faithful T

/-! ### Stalks -/

/-- Taking the stalk at a point of a scheme, as a functor from `𝒪_X`-modules to abelian
groups. -/
noncomputable abbrev stalkAbelianFunctor (x : X) : X.Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ x

/-- The morphism `𝒪_X ⟶ M` of `𝒪_X`-modules determined by a global section of `M`. -/
noncomputable def homFromUnit (M : X.Modules) (s : Γ(M, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm (PresheafOfModules.sectionsMk
    (fun V => M.presheaf.map (homOfLE le_top : V.unop ⟶ ⊤).op s)
    (by
      intro V W f
      change M.presheaf.map f (M.presheaf.map _ s) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      congr 2))

/-- `homFromUnit M s` sends the unit global section of `𝒪_X` to `s`. -/
lemma homFromUnit_app_one (M : X.Modules) (s : Γ(M, ⊤)) :
    ((toPresheaf X).map (homFromUnit M s)).app (op ⊤)
      (1 : X.ringCatSheaf.obj.obj (op ⊤)) = s := by
  have h := congrArg (fun t => t.val (op ⊤))
    (show M.unitHomEquiv (homFromUnit M s) = _ from M.unitHomEquiv.apply_symm_apply _)
  change (homFromUnit M s).val.app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op ⊤)) =
    M.presheaf.map (𝟙 (op ⊤)) s at h
  exact h.trans (congrArg (fun k : Γ(M, ⊤) ⟶ Γ(M, ⊤) => k s) (M.presheaf.map_id (op ⊤)))

/-- Taking the stalk at a point commutes with all colimits of `𝒪_X`-modules. -/
lemma preservesColimits_stalkAbelianFunctor (x : X) :
    PreservesColimits (stalkAbelianFunctor x) := by
  change PreservesColimits
    (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x ⋙
      forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) X.ringCatSheaf.obj x))
        AddCommGrpCat)
  infer_instance

/-- A morphism of `𝒪_X`-modules which is an isomorphism on every stalk is an isomorphism. -/
lemma isIso_of_isIso_stalkAbelianFunctor_map {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x : X, IsIso ((stalkAbelianFunctor x).map f)) : IsIso f := by
  have : IsIso ((toPresheaf X).map f) := by
    have hApp (U : X.Opensᵒᵖ) : IsIso (((toPresheaf X).map f).app U) := by
      have h' (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom) := h x
      exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
        ((SheafOfModules.toSheaf X.ringCatSheaf).map f) U.unop
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso f (toPresheaf X)

end Scheme.Modules

open Scheme.Modules

/-! ### Every germ comes from a finitely presented module over `F` -/

/-- Every germ of a quasi-coherent module `F` at a point of a quasi-compact, quasi-separated
scheme is the image of a germ of a finitely presented module mapping to `F`. -/
lemma exists_isFinitePresentation_stalk_preimage [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (x : X) (s : (stalkAbelianFunctor x).obj F) :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (p : G ⟶ F)
      (t : (stalkAbelianFunctor x).obj G), (stalkAbelianFunctor x).map p t = s := by
  obtain ⟨U, hxU, hU, a, ha⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens F.presheaf x s
  change X.Opens at U
  let y : U.toScheme := ⟨x, hxU⟩
  let N := F.restrict U.ι
  have eU : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by simp
  let b : Γ(N, ⊤) := F.presheaf.map (eqToHom eU).op a
  have : (SheafOfModules.unit U.toScheme.ringCatSheaf).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit _
  obtain ⟨G, hG, p, e, he⟩ :=
    exists_finitePresentation_extension_of_hom F U hU.isCompact
      (SheafOfModules.unit U.toScheme.ringCatSheaf) (homFromUnit N b)
  let one : (stalkAbelianFunctor y).obj (SheafOfModules.unit U.toScheme.ringCatSheaf) :=
    ((toPresheaf U.toScheme).obj (SheafOfModules.unit U.toScheme.ringCatSheaf)).germ ⊤ y
      (show y ∈ (⊤ : U.toScheme.Opens) from trivial)
      (1 : U.toScheme.ringCatSheaf.obj.obj (op ⊤))
  let t := (stalkAbelianFunctor y).map e.inv one
  refine ⟨G, hG, p, (restrictStalkNatIso U.ι y).hom.app G t, ?_⟩
  change (stalkAbelianFunctor (U.ι y)).map p
    ((restrictStalkNatIso U.ι y).hom.app G t) = s
  rw [← ConcreteCategory.comp_apply, ← NatTrans.naturality]
  change (restrictStalkNatIso U.ι y).hom.app F
    ((stalkAbelianFunctor y).map ((restrictFunctor U.ι).map p) t) = s
  have hcomp : e.inv ≫ (restrictFunctor U.ι).map p = homFromUnit N b :=
    (congrArg (fun m => e.inv ≫ m) he.symm).trans (e.inv_hom_id_assoc (homFromUnit N b))
  have hmap : (stalkAbelianFunctor y).map e.inv ≫
      (stalkAbelianFunctor y).map ((restrictFunctor U.ι).map p) =
      (stalkAbelianFunctor y).map (homFromUnit N b) :=
    ((stalkAbelianFunctor y).map_comp e.inv ((restrictFunctor U.ι).map p)).symm.trans
      (congrArg (fun m => (stalkAbelianFunctor y).map m) hcomp)
  have key : (stalkAbelianFunctor y).map ((restrictFunctor U.ι).map p) t =
      (stalkAbelianFunctor y).map (homFromUnit N b) one := by
    rw [← hmap, ConcreteCategory.comp_apply]
  rw [key]
  have htop : y ∈ (⊤ : U.toScheme.Opens) := trivial
  have hx' : x ∈ U.ι ''ᵁ (⊤ : U.toScheme.Opens) := by simpa using hxU
  have h₁ : (stalkAbelianFunctor y).map (homFromUnit N b) one =
      ((toPresheaf U.toScheme).obj N).germ ⊤ y htop
        (((toPresheaf U.toScheme).map (homFromUnit N b)).app (op ⊤)
          (1 : U.toScheme.ringCatSheaf.obj.obj (op ⊤))) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _
  rw [h₁, homFromUnit_app_one N b]
  have h₂ : ((toPresheaf U.toScheme).obj N).germ ⊤ y htop ≫
      (restrictStalkNatIso U.ι y).hom.app F =
      F.presheaf.germ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) x hx' :=
    germ_restrictStalkNatIso_hom_app U.ι y F htop
  have h₃ : (restrictStalkNatIso U.ι y).hom.app F
      (((toPresheaf U.toScheme).obj N).germ ⊤ y htop b) =
      F.presheaf.germ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) x hx' b :=
    (ConcreteCategory.comp_apply _ _ b).symm.trans
      (congrArg (fun m => (ConcreteCategory.hom m) b) h₂)
  rw [h₃]
  have h₄ : F.presheaf.map (eqToHom eU).op ≫
      F.presheaf.germ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) x hx' = F.presheaf.germ U x hxU :=
    TopCat.Presheaf.germ_res' _ _ _ _
  rw [← ConcreteCategory.comp_apply, h₄]
  exact ha

/-- A germ of a finitely presented module over `F` which dies in `F` already dies further along
the diagram. -/
lemma exists_hom_stalkAbelianFunctor_map_eq_zero [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (x : X) (i : FinitePresentationOver F)
    (s : (stalkAbelianFunctor x).obj i.1.left)
    (hs : (stalkAbelianFunctor x).map i.1.hom s = 0) :
    ∃ (j : FinitePresentationOver F) (f : i ⟶ j),
      (stalkAbelianFunctor x).map f.1.left s = 0 := by
  have : i.1.left.IsFinitePresentation := i.2
  have : i.1.left.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation _
  have : (kernel i.1.hom).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel i.1.hom
  have hex := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    X.ringCatSheaf (ShortComplex.kernelSequence i.1.hom)).mp
    (ShortComplex.kernelSequence_exact i.1.hom) x
  obtain ⟨t, ht⟩ := (ShortComplex.ab_exact_iff _).mp hex s hs
  obtain ⟨G, hG, q, v, hv⟩ :=
    exists_isFinitePresentation_stalk_preimage (kernel i.1.hom) x t
  have : G.IsFinitePresentation := hG
  let d : G ⟶ i.1.left := q ≫ kernel.ι i.1.hom
  have hd : d ≫ i.1.hom = 0 := by simp [d]
  have : G.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation G
  have : (cokernel d).IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_cokernel d
  let j : FinitePresentationOver F := ⟨Over.mk (cokernel.desc d i.1.hom hd),
    show (cokernel d).IsFinitePresentation from inferInstance⟩
  let f : i ⟶ j := ObjectProperty.homMk (Over.homMk (cokernel.π d))
  refine ⟨j, f, ?_⟩
  have hds : (stalkAbelianFunctor x).map d v = s := by
    rwa [Functor.map_comp, ConcreteCategory.comp_apply, hv]
  rw [← hds]
  change (stalkAbelianFunctor x).map (cokernel.π d) ((stalkAbelianFunctor x).map d v) = 0
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, cokernel.condition, Functor.map_zero]
  rfl

/-- The tautological cocone on the finitely presented modules over `F` is colimiting on every
stalk, as a cocone of types. -/
noncomputable def isColimitStalkMapCoconeFinitePresentationOver [CompactSpace X]
    [QuasiSeparatedSpace X] (F : X.Modules) [F.IsQuasicoherent] (x : X) :
    IsColimit ((stalkAbelianFunctor x ⋙ forget AddCommGrpCat).mapCocone
      (finitePresentationOverCocone F)) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro s
    obtain ⟨G, hG, p, t, ht⟩ := exists_isFinitePresentation_stalk_preimage F x s
    exact ⟨⟨Over.mk p, hG⟩, t, ht.symm⟩
  · intro i a b h
    change (stalkAbelianFunctor x).obj i.1.left at a b
    change (stalkAbelianFunctor x).map i.1.hom a = (stalkAbelianFunctor x).map i.1.hom b at h
    obtain ⟨j, f, hf⟩ := exists_hom_stalkAbelianFunctor_map_eq_zero F x i (a - b)
      (by
        change ((stalkAbelianFunctor x).map i.1.hom).hom (a - b) = 0
        rw [map_sub]
        exact sub_eq_zero.mpr h)
    refine ⟨j, f, ?_⟩
    change (stalkAbelianFunctor x).map f.1.left a = (stalkAbelianFunctor x).map f.1.left b
    apply sub_eq_zero.mp
    change ((stalkAbelianFunctor x).map f.1.left).hom (a - b) = 0 at hf
    rwa [map_sub] at hf

/-! ### The two colimit presentations -/

/-- A quasi-coherent module on a quasi-compact, quasi-separated scheme is a filtered colimit of
finitely presented modules. -/
@[stacks 01PJ]
theorem exists_filtered_diagram_of_isFinitePresentation (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (I : Type u) (inst : SmallCategory I),
      let _ := inst
      ∃ (_ : IsFiltered I) (D : CategoryTheory.Functor I X.Modules)
        (φ : NatTrans D ((Functor.const I).obj F)),
        (∀ i, (D.obj i).IsFinitePresentation) ∧
          Nonempty (IsColimit (Cocone.mk F φ)) := by
  have : EssentiallySmall.{u} (FinitePresentationOver F) :=
    essentiallySmall_finitePresentationOver F
  let I := SmallModel.{u} (FinitePresentationOver F)
  let e : I ≌ FinitePresentationOver F := (equivSmallModel (FinitePresentationOver F)).symm
  have : IsFiltered I := IsFiltered.of_equivalence e.symm
  let D := e.functor ⋙ finitePresentationOverDiagram F
  let c : Cocone D := (finitePresentationOverCocone F).whisker e.functor
  let q : colimit D ⟶ F := colimit.desc D c
  have hq : IsIso q := by
    refine isIso_of_isIso_stalkAbelianFunctor_map _ fun x => ?_
    have : PreservesColimits (stalkAbelianFunctor x) := preservesColimits_stalkAbelianFunctor x
    let h₁ := isColimitOfPreserves (stalkAbelianFunctor x) (colimit.isColimit D)
    have : ReflectsColimit (D ⋙ stalkAbelianFunctor x) (forget AddCommGrpCat) :=
      reflectsColimit_of_reflectsIsomorphisms _ _
    have h₂ : IsColimit ((stalkAbelianFunctor x).mapCocone c) :=
      isColimitOfReflects (forget AddCommGrpCat)
        ((isColimitStalkMapCoconeFinitePresentationOver F x).whiskerEquivalence e)
    have heq : (stalkAbelianFunctor x).map q =
        h₁.desc ((stalkAbelianFunctor x).mapCocone c) :=
      h₁.hom_ext fun i =>
        (((stalkAbelianFunctor x).map_comp (colimit.ι D i) q).symm.trans
            (congrArg (fun m => (stalkAbelianFunctor x).map m) (colimit.ι_desc c i))).trans
          (h₁.fac ((stalkAbelianFunctor x).mapCocone c) i).symm
    rw [heq]
    exact h₁.nonempty_isColimit_iff_isIso_desc.mp ⟨h₂⟩
  exact ⟨I, inferInstance, inferInstance, D, c.ι, fun i => (e.functor.obj i).2,
    (colimit.isColimit D).nonempty_isColimit_iff_isIso_desc.mpr hq⟩

/-- A quasi-coherent module on a quasi-compact, quasi-separated scheme is a directed colimit of
finitely presented modules. -/
@[stacks 01PK]
theorem exists_directed_system_of_isFinitePresentation (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I)
      (_ : IsDirected I (· ≤ ·)) (D : I ⥤ X.Modules)
      (φ : D ⟶ (Functor.const I).obj F),
      (∀ i, (D.obj i).IsFinitePresentation) ∧
        Nonempty (IsColimit (Cocone.mk F φ)) := by
  obtain ⟨J, _, _, G, φ, hfinite, ⟨hcolim⟩⟩ :=
    exists_filtered_diagram_of_isFinitePresentation X F
  obtain ⟨I, _, hI, hIne, e, he⟩ := CategoryTheory.IsFiltered.exists_directed J
  exact ⟨I, inferInstance, hIne, hI, e ⋙ G, Functor.whiskerLeft e φ, fun i => hfinite _,
    ⟨(Functor.Final.isColimitWhiskerEquiv e _).symm hcolim⟩⟩

/-! ### Finitely presented approximation over a quasi-compact open -/

/- `AlgebraicGeometry.Scheme.Modules` is a plain definition for `SheafOfModules X.ringCatSheaf`
carrying its own `Category` instance, whose `Hom` field is
`AlgebraicGeometry.Scheme.Modules.Hom` rather than `SheafOfModules.Hom`.  The two categories are
definitionally equal but not syntactically, so instance search — being syntactic — does not
transport a statement about a colimit of `𝒪_X`-modules to the corresponding statement about a
colimit in `SheafOfModules X.ringCatSheaf`, unless the three definitions are made implicitly
reducible. -/
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory

/-- A quasi-coherent module of finite type on a quasi-compact, quasi-separated scheme is a
quotient of a finitely presented module. -/
theorem exists_finitePresentation_epi (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (A : X.Modules) (_ : A.IsFinitePresentation) (f : A ⟶ F), Epi f := by
  obtain ⟨I, _, _, _, D, φ, hD, ⟨hc⟩⟩ := exists_directed_system_of_isFinitePresentation X F
  let q : colimit D ⟶ F := colimit.desc D (Cocone.mk F φ)
  have hq : IsIso q := (colimit.isColimit D).nonempty_isColimit_iff_isIso_desc.mp ⟨hc⟩
  have : (colimit D).IsFiniteType := Stacks.SheafOfModules.isFiniteType_of_iso.{u} (asIso q).symm
  obtain ⟨i, hi⟩ := Stacks.SheafOfModules.exists_epi_to_colimit_of_isFiniteType X.ringCatSheaf D
  have hfac : colimit.ι D i ≫ q = φ.app i := colimit.ι_desc (Cocone.mk F φ) i
  have : Epi (colimit.ι D i) := hi
  refine ⟨D.obj i, hD i, φ.app i, ?_⟩
  rw [← hfac]
  infer_instance

/-- Let `F` be a quasi-coherent module of finite type on a quasi-compact, quasi-separated scheme
`X` whose restriction to a quasi-compact open `U` is of finite presentation.  Then there is a
morphism `φ : G ⟶ F` with `G` of finite presentation, `φ` surjective, and `φ|_U` an
isomorphism. -/
@[stacks 080V]
theorem exists_finitePresentation_epi_isIso_restrict [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (U : X.Opens) (hU : IsCompact U.1)
    [(F.restrict U.ι).IsFinitePresentation] :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (φ : G ⟶ F),
      Epi φ ∧ IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) := by
  obtain ⟨A, hA, f, hf⟩ := exists_finitePresentation_epi X F
  have : A.IsFinitePresentation := hA
  exact exists_finitePresentation_epi_isIso_restrict_of_epi f hf U hU

end AlgebraicGeometry

end
