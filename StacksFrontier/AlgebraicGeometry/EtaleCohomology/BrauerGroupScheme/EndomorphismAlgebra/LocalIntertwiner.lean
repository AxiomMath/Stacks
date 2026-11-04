module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.IntertwinerSheaf
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.ModuleConjugation
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.IntertwinerSheaf

/-!
# The intertwiner sheaf over a trivializing open

Bases of the sections of a free sheaf of modules and of the sheaves it trivializes, the induced
basis of the endomorphism sections and the algebra isomorphism of section endomorphism algebras
over an open trivializing both `F` and `G`, and the proof that a linear equivalence conjugating
that algebra isomorphism names a section of the intertwiner sheaf, which is then a one-element
basis.
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.EtaleCohomology

section

open CategoryTheory.Limits

section
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (Rc : Sheaf J CommRingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (I : Type u) [Finite I] (U : Cᵒᵖ)
/-- The sections over `U` of the free sheaf of modules on a finite type `I` form the finitely
supported functions `I →₀ R(U)`. -/
private noncomputable def freeSectionsIso :
    ModuleCat.of (Rc.obj.obj U) (I →₀ Rc.obj.obj U) ≅
      (SheafOfModules.free.{u}
        (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc)) I).val.obj U :=
  (ModuleCat.finsuppCoconeIsColimit (Rc.obj.obj U) (Rc.obj.obj U) I).coconePointUniqueUpToIso
    (isColimitOfPreserves
      (SheafOfModules.forget.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc) ⋙
        PresheafOfModules.evaluation
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc).obj U)
      (SheafOfModules.isColimitFreeCofan I))
/-- The basis, indexed by `I`, of the sections over `U` of the free sheaf of modules on `I`. -/
private noncomputable def freeSectionBasis :
    Module.Basis I (Rc.obj.obj U)
      ((SheafOfModules.free.{u}
        (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc)) I).val.obj U) :=
  (Finsupp.basisSingleOne : Module.Basis I (Rc.obj.obj U) (I →₀ Rc.obj.obj U)).map
    (CategoryTheory.Iso.toLinearEquiv (freeSectionsIso Rc I U))
/-- The `i`-th member of the section basis of a free sheaf of modules is the `i`-th free section.
-/
private lemma freeSectionBasis_apply (i : I) :
    freeSectionBasis Rc I U i = (SheafOfModules.freeSection
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc)) i).eval U := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (ModuleCat.finsuppCoconeIsColimit (Rc.obj.obj U) (Rc.obj.obj U) I)
    (isColimitOfPreserves
      (SheafOfModules.forget.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc) ⋙
        PresheafOfModules.evaluation
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc).obj U)
      (SheafOfModules.isColimitFreeCofan I)) (Discrete.mk i)
  exact congrArg (fun f => f.hom (1 : Rc.obj.obj U)) h

/-- An isomorphism of sheaves of modules, read on the sections over `U` as a linear equivalence
over the *commutative* section ring. The type ascription is what matters: it forces the scalar ring
and its module instances into the same spelling as `freeSectionBasis`, so that transporting a basis
along it is an equality the simplifier can see through. -/
private noncomputable def sectionLinearEquivOfIso
    {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc)}
    (e : SheafOfModules.free.{u} I ≅ M) :
    ((SheafOfModules.free.{u}
        (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc) I).val.obj U)
      ≃ₗ[Rc.obj.obj U] (M.val.obj U) :=
  ((PresheafOfModules.evaluation _ U).mapIso
    ((SheafOfModules.forget.{u} _).mapIso e)).toLinearEquiv

/-- The basis of the sections over `U` of a sheaf of modules trivialized by an isomorphism from a
free sheaf on a finite type. -/
private noncomputable def sectionBasisOfIso
    {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc)}
    (e : SheafOfModules.free.{u} I ≅ M) : Module.Basis I (Rc.obj.obj U) (M.val.obj U) :=
  (freeSectionBasis Rc I U).map (sectionLinearEquivOfIso Rc I U e)

/-- The members of the transported basis are the images of the free sections. -/
private lemma sectionBasisOfIso_apply
    {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc)}
    (e : SheafOfModules.free.{u} I ≅ M) (i : I) :
    sectionBasisOfIso Rc I U e i =
      (SheafOfModules.sectionsMap e.hom (SheafOfModules.freeSection i)).eval U := by
  simp only [sectionBasisOfIso, Module.Basis.map_apply, freeSectionBasis_apply]
  rfl

/-- The members of the transported basis restrict to the members of the transported basis. -/
private lemma sectionBasisOfIso_natural
    {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc)}
    (e : SheafOfModules.free.{u} I ≅ M) {V : Cᵒᵖ} (k : U ⟶ V) (i : I) :
    M.val.map k (sectionBasisOfIso Rc I U e i) = sectionBasisOfIso Rc I V e i := by
  rw [sectionBasisOfIso_apply, sectionBasisOfIso_apply]
  exact PresheafOfModules.sections_property _ k

/-- The coordinates of a restricted section are the restrictions of its coordinates. -/
private lemma sectionBasisOfIso_repr_natural
    {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc)}
    (e : SheafOfModules.free.{u} I ≅ M) {V : Cᵒᵖ} (k : U ⟶ V)
    (x : M.val.obj U) (i : I) :
    (sectionBasisOfIso Rc I V e).repr (M.val.map k x) i =
      Rc.obj.map k ((sectionBasisOfIso Rc I U e).repr x i) :=
  basis_coord_map_of_apply (Rc.obj.map k).hom (sectionBasisOfIso Rc I U e)
    (sectionBasisOfIso Rc I V e)
    (show M.val.obj U →+ M.val.obj V from (M.val.map k).hom.toAddMonoidHom)
    (fun r m => PresheafOfModules.map_smul M.val k r m)
    (fun j => sectionBasisOfIso_natural Rc I U e k j) x i

/-- If the source of a morphism is trivialized by a free sheaf on a finite type and `U` is initial
in the site, then a morphism is determined by, and may be prescribed as, its component at `U`. -/
private lemma homEvaluation_bijective_of_free
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc)}
    (e : SheafOfModules.free.{u} I ≅ M) (hU : IsInitial U) :
    Function.Bijective (fun f : M ⟶ N => (f.val.app U).hom) := by
  classical
  have hsections (s : N.sections) (V : Cᵒᵖ) :
      s.eval V = N.val.map (hU.to V) (s.eval U) :=
    (PresheafOfModules.sections_property s (hU.to V)).symm
  constructor
  · intro f g hfg
    apply (cancel_epi e.hom).mp
    apply N.freeHomEquiv.injective
    funext i
    apply PresheafOfModules.sections_ext
    intro V
    change (N.freeHomEquiv (e.hom ≫ f) i).eval V =
      (N.freeHomEquiv (e.hom ≫ g) i).eval V
    rw [hsections (N.freeHomEquiv (e.hom ≫ f) i) V,
      hsections (N.freeHomEquiv (e.hom ≫ g) i) V]
    apply congrArg (fun y : N.val.obj U => N.val.map (hU.to V) y)
    change f.val.app U (e.hom.val.app U ((SheafOfModules.freeSection i).eval U)) =
      g.val.app U (e.hom.val.app U ((SheafOfModules.freeSection i).eval U))
    exact DFunLike.congr_fun hfg _
  · intro f
    let s (i : I) : N.sections := N.val.sectionsMk
      (fun V => N.val.map (hU.to V) (f (sectionBasisOfIso Rc I U e i)))
      (fun {V W} k => by
        rw [← PresheafOfModules.map_comp_apply, hU.hom_ext (hU.to V ≫ k) (hU.to W)])
    refine ⟨e.inv ≫ N.freeHomEquiv.symm s, ?_⟩
    apply (sectionBasisOfIso Rc I U e).ext
    intro i
    change (N.freeHomEquiv.symm s).val.app U
      (e.inv.val.app U (sectionBasisOfIso Rc I U e i)) = _
    have hi : e.inv.val.app U (sectionBasisOfIso Rc I U e i) =
        (SheafOfModules.freeSection i).eval U := by
      rw [sectionBasisOfIso_apply]
      change (e.hom ≫ e.inv).val.app U ((SheafOfModules.freeSection i).eval U) = _
      rw [e.hom_inv_id]
      rfl
    rw [hi]
    have hs := congrArg (fun t : N.sections => t.eval U)
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s i)
    change (N.freeHomEquiv.symm s).val.app U
      ((SheafOfModules.freeSection i).eval U) = (s i).eval U at hs
    rw [hs]
    change N.val.map (hU.to U) (f (sectionBasisOfIso Rc I U e i)) = _
    rw [hU.hom_ext (hU.to U) (𝟙 U)]
    simp
    rfl

end
section
variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
  {F G : SheafOfModules.{u} (structureSheaf Rc)} {I : Type u}
  {U V : Opens X}
/-- A trivialization of a sheaf of modules over `U` restricts to a trivialization over `V ≤ U`. -/
private noncomputable def restrictFreeIso
    (e : SheafOfModules.free I ≅ F.over U) (hVU : V ≤ U) :
    SheafOfModules.free I ≅ F.over V :=
  SheafOfModules.mapFreeIso (SheafOfModules.overMap (structureSheaf Rc) (homOfLE hVU)) I
      (SheafOfModules.overMapUnitIso (homOfLE hVU)).symm ≪≫
    (SheafOfModules.overMap (structureSheaf Rc) (homOfLE hVU)).mapIso e ≪≫
    (SheafOfModules.overFunctorMap (structureSheaf Rc) (homOfLE hVU)).app F

/-- Over an open on which `F` is free of finite rank, a section of `SheafHom(F, G)` is determined
by, and may be prescribed as, its component at the terminal object of the slice site. -/
private lemma sheafHomApp_bijective_of_free
    (H : SheafHom Rc F G) [Finite I]
    (e : SheafOfModules.free I ≅ F.over U) :
    Function.Bijective (fun s : H.obj.val.obj (op U) =>
      ((H.sectionsEquiv U s).val.app (op (Over.mk (𝟙 U)))).hom) :=
  (homEvaluation_bijective_of_free (Rc.over U) I (op (Over.mk (𝟙 U))) e
    (initialOpOfTerminal (Over.mkIdTerminal (X := U)))).comp
    (H.sectionsEquiv U).bijective

end

end

section
variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
  {F : SheafOfModules.{u} (structureSheaf Rc)} {I : Type u} [Fintype I]
  [DecidableEq I]

/-- The basis, indexed by `I × I`, of the sections over `U` of the endomorphism sheaf of a sheaf of
modules trivialized over `U` by a free sheaf on a finite type `I`. -/
private noncomputable def sheafEndSectionBasis
    (H : SheafHom Rc F F) (U : Opens X)
    (e : SheafOfModules.free I ≅ F.over U) :
    Module.Basis (I × I) (Rc.obj.obj (op U)) (H.obj.val.obj (op U)) := by
  classical
  let b := sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e
  let a := LinearEquiv.ofBijective (sheafHomSectionLinearMap H U)
    (sheafHomApp_bijective_of_free H e)
  exact b.end.map a.symm

/-- The members of the endomorphism section basis are the elementary matrices of the section
basis. -/
private lemma sheafEndSectionBasis_apply
    (H : SheafHom Rc F F) (U : Opens X)
    (e : SheafOfModules.free I ≅ F.over U) (ij : I × I) :
    sheafHomSectionLinearMap H U (sheafEndSectionBasis H U e ij) =
      (sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e).end ij := by
  classical
  exact (LinearEquiv.ofBijective (sheafHomSectionLinearMap H U)
    (sheafHomApp_bijective_of_free H e)).apply_symm_apply _

end

section
/-- An isomorphism of endomorphism sheaves which preserves the identity and composition induces, on
an open trivializing both sheaves of modules, an algebra isomorphism of the endomorphism
algebras of the modules of sections. -/
private noncomputable def sheafEndSectionAlgEquiv
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (HFF : SheafHom Rc F F) (HGG : SheafHom Rc G G) (α : HFF.obj ≅ HGG.obj)
    (hα_one : ∀ U : Opens X, HGG.sectionsEquiv U
      (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (𝟙 (F.over U)))) = 𝟙 (G.over U))
    (hα_comp : ∀ (U : Opens X) (f g : F.over U ⟶ F.over U),
      HGG.sectionsEquiv U (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (f ≫ g))) =
      HGG.sectionsEquiv U (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm f)) ≫
      HGG.sectionsEquiv U (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm g)))
    (U : Opens X) {I K : Type u} [Finite I] [Finite K]
    (eF : SheafOfModules.free I ≅ F.over U) (eG : SheafOfModules.free K ≅ G.over U) :
    Module.End (Rc.obj.obj (op U)) (F.val.obj (op U)) ≃ₐ[Rc.obj.obj (op U)]
      Module.End (Rc.obj.obj (op U)) (G.val.obj (op U)) := by
  let a := LinearEquiv.ofBijective (sheafHomSectionLinearMap HFF U)
    (sheafHomApp_bijective_of_free HFF eF)
  let b := LinearEquiv.ofBijective (sheafHomSectionLinearMap HGG U)
    (sheafHomApp_bijective_of_free HGG eG)
  let c : HFF.obj.val.obj (op U) ≃ₗ[Rc.obj.obj (op U)] HGG.obj.val.obj (op U) :=
    ((PresheafOfModules.evaluation _ (op U)).mapIso
    ((SheafOfModules.forget _).mapIso α)).toLinearEquiv
  let d := a.symm.trans (c.trans b)
  have ha (x : F.over U ⟶ F.over U) : a ((HFF.sectionsEquiv U).symm x) =
      (x.val.app (op (Over.mk (𝟙 U)))).hom := by
    change ((HFF.sectionsEquiv U ((HFF.sectionsEquiv U).symm _)).val.app _).hom = _
    rw [(HFF.sectionsEquiv U).apply_symm_apply]
    rfl
  refine AlgEquiv.ofLinearEquiv d ?_ ?_
  · have ha1 : a ((HFF.sectionsEquiv U).symm (𝟙 (F.over U))) = 1 := (ha _).trans rfl
    change b (c (a.symm 1)) = 1
    rw [← ha1, a.symm_apply_apply]
    exact congrArg (fun f : G.over U ⟶ G.over U =>
      (f.val.app (op (Over.mk (𝟙 U)))).hom) (hα_one U)
  · intro f g
    let sf := a.symm f
    let sg := a.symm g
    have ha2 : a ((HFF.sectionsEquiv U).symm
        (HFF.sectionsEquiv U sg ≫ HFF.sectionsEquiv U sf)) = f * g := by
      rw [ha]
      change a sf ∘ₗ a sg = f * g
      simp [sf, sg, Module.End.mul_eq_comp]
    change b (c (a.symm (f * g))) = b (c (a.symm f)) * b (c (a.symm g))
    rw [← ha2, a.symm_apply_apply]
    have h := congrArg (fun t : G.over U ⟶ G.over U =>
      (t.val.app (op (Over.mk (𝟙 U)))).hom)
      (hα_comp U (HFF.sectionsEquiv U sg) (HFF.sectionsEquiv U sf))
    simp only [AddEquiv.symm_apply_apply] at h
    exact LinearMap.ext fun x => congrArg (fun t => t x) h
end

section
/-- Restricting a section of an internal hom gives the restriction of the linear map it names. -/
private lemma sheafHomSectionLinearMap_restrict
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (H : SheafHom Rc F G) {U V : Opens X} (hVU : V ≤ U)
    (s : H.obj.val.obj (op U)) (f : F.val.obj (op U)) :
    (sheafHomSectionLinearMap H V)
        (H.obj.val.map (homOfLE hVU).op s) (F.val.map (homOfLE hVU).op f) =
      G.val.map (homOfLE hVU).op ((sheafHomSectionLinearMap H U s) f) :=
  (sheafHomApp_restrict H hVU le_rfl s (F.val.map (homOfLE hVU).op f)).trans
    (sheafHomApp_naturality H le_rfl hVU s f).symm

/-- The section basis of a restricted trivialization consists of the restrictions of the members of
the original section basis. -/
private lemma sectionBasisOfIso_restrictFreeIso_apply
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F : SheafOfModules.{u} (structureSheaf Rc)} {I : Type u} [Finite I]
    {U V : Opens X} (hVU : V ≤ U)
    (e : SheafOfModules.free I ≅ F.over U) (i : I) :
    sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V)))
        (restrictFreeIso e hVU) i =
      F.val.map (homOfLE hVU).op
        (sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e i) := by
  rw [sectionBasisOfIso_apply (Rc.over V) I _ (restrictFreeIso e hVU) i,
    sectionBasisOfIso_apply (Rc.over U) I _ e i]
  let uV := SheafOfModules.unit ((structureSheaf Rc).over V)
  let uU := SheafOfModules.unit ((structureSheaf Rc).over U)
  let oneV : uV.sections := uV.unitHomEquiv (𝟙 uV)
  let oneU : uU.sections := uU.unitHomEquiv (𝟙 uU)
  change ((SheafOfModules.ιFree i ≫ (restrictFreeIso e hVU).hom).val.app
      (op (Over.mk (𝟙 V)))).hom (oneV.eval (op (Over.mk (𝟙 V)))) =
    F.val.map (homOfLE hVU).op
      (((SheafOfModules.ιFree i ≫ e.hom).val.app
        (op (Over.mk (𝟙 U)))).hom (oneU.eval (op (Over.mk (𝟙 U)))))
  have hcomp : SheafOfModules.ιFree i ≫ (restrictFreeIso e hVU).hom =
      (SheafOfModules.overMapUnitIso (homOfLE hVU)).symm.hom ≫
        (SheafOfModules.overMap (structureSheaf Rc) (homOfLE hVU)).map
          (SheafOfModules.ιFree i ≫ e.hom) ≫
        ((SheafOfModules.overFunctorMap (structureSheaf Rc) (homOfLE hVU)).app F).hom := by
    simp only [restrictFreeIso, Iso.trans_hom, Functor.map_comp,
      Functor.mapIso_hom]
    rw [← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom]
    simp only [Category.assoc]
  rw [hcomp]
  let sec : (F.over U).sections :=
    SheafOfModules.sectionsMap (SheafOfModules.ιFree i ≫ e.hom) oneU
  change sec.val ((Over.map (homOfLE hVU)).op.obj (op (Over.mk (𝟙 V)))) =
    F.val.map (homOfLE hVU).op (sec.val (op (Over.mk (𝟙 U))))
  let k : Over.mk (homOfLE hVU) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (homOfLE hVU)
  exact (PresheafOfModules.sections_property sec k.op).symm

/-- The coordinates of a restricted section with respect to a restricted trivialization are the
restrictions of its coordinates. -/
private lemma sectionBasisOfIso_restrictFreeIso_coord
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F : SheafOfModules.{u} (structureSheaf Rc)} {I : Type u} [Finite I]
    {U V : Opens X} (hVU : V ≤ U)
    (e : SheafOfModules.free I ≅ F.over U) (f : F.val.obj (op U)) (i : I) :
    (sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V)))
        (restrictFreeIso e hVU)).coord i (F.val.map (homOfLE hVU).op f) =
      (Rc.obj.map (homOfLE hVU).op).hom
        ((sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e).coord i f) :=
  basis_coord_map_of_apply (Rc.obj.map (homOfLE hVU).op).hom
    (sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e)
    (sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V))) (restrictFreeIso e hVU))
    (show F.val.obj (op U) →+ F.val.obj (op V) from
      (F.val.map (homOfLE hVU).op).hom.toAddMonoidHom)
    (fun r m => PresheafOfModules.map_smul F.val (homOfLE hVU).op r m)
    (fun j => (sectionBasisOfIso_restrictFreeIso_apply hVU e j).symm) f i

/-- The endomorphism section basis of a restricted trivialization consists of the restrictions of
the members of the original endomorphism section basis. -/
private lemma sheafEndSectionBasis_restrict
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F : SheafOfModules.{u} (structureSheaf Rc)} {I : Type u}
    [Fintype I] [DecidableEq I]
    (H : SheafHom Rc F F) {U V : Opens X} (hVU : V ≤ U)
    (e : SheafOfModules.free I ≅ F.over U) (ij : I × I) :
    H.obj.val.map (homOfLE hVU).op (sheafEndSectionBasis H U e ij) =
      sheafEndSectionBasis H V (restrictFreeIso e hVU) ij := by
  let eV := restrictFreeIso e hVU
  let bU := sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e
  let bV := sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V))) eV
  apply (sheafHomApp_bijective_of_free H eV).injective
  change sheafHomSectionLinearMap H V
      (H.obj.val.map (homOfLE hVU).op (sheafEndSectionBasis H U e ij)) =
    sheafHomSectionLinearMap H V (sheafEndSectionBasis H V eV ij)
  apply bV.ext
  intro k
  have hk : bV k = F.val.map (homOfLE hVU).op (bU k) :=
    sectionBasisOfIso_restrictFreeIso_apply hVU e k
  conv_lhs => rw [hk]
  refine (sheafHomSectionLinearMap_restrict H hVU
    (sheafEndSectionBasis H U e ij) (bU k)).trans ?_
  rw [sheafEndSectionBasis_apply H U e ij,
    sheafEndSectionBasis_apply H V eV ij]
  change F.val.map (homOfLE hVU).op ((bU.end ij) (bU k)) =
    (bV.end ij) (bV k)
  rw [Module.Basis.end_apply_apply, Module.Basis.end_apply_apply]
  by_cases h : ij.2 = k
  · simp only [h, ↓reduceIte]
    exact (sectionBasisOfIso_restrictFreeIso_apply hVU e ij.1).symm
  · simp only [h, ↓reduceIte]
    exact map_zero _

/-- A rank-one projection of a section basis commutes with restriction. -/
private lemma rankOne_sectionBasis_restrict_apply
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F : SheafOfModules.{u} (structureSheaf Rc)} {I : Type u} [Finite I]
    {U V : Opens X} (hVU : V ≤ U)
    (e : SheafOfModules.free I ≅ F.over U) (i : I)
    (f : F.val.obj (op U)) :
    (LinearMap.smulRight
      ((sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V)))
        (restrictFreeIso e hVU)).coord i)
      (sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V)))
        (restrictFreeIso e hVU) i))
        (F.val.map (homOfLE hVU).op f) =
      F.val.map (homOfLE hVU).op
        ((LinearMap.smulRight
          ((sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e).coord i)
          (sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e i)) f) :=
  basis_smulRight_map (Rc.obj.map (homOfLE hVU).op).hom
    (sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e)
    (sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V))) (restrictFreeIso e hVU))
    (show F.val.obj (op U) →+ F.val.obj (op V) from
      (F.val.map (homOfLE hVU).op).hom.toAddMonoidHom)
    (fun r m => PresheafOfModules.map_smul F.val (homOfLE hVU).op r m)
    (fun j => (sectionBasisOfIso_restrictFreeIso_apply hVU e j).symm) f i

/-- The linear map named by the image under `α` of a restricted section is the restriction of the
linear map named by the image of the section. -/
private lemma sheafHomSectionLinearMap_alpha_restrict
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (HFF : SheafHom Rc F F) (HGG : SheafHom Rc G G)
    (α : HFF.obj ⟶ HGG.obj) {U V : Opens X} (hVU : V ≤ U)
    (s : HFF.obj.val.obj (op U)) (f : G.val.obj (op U)) :
    (sheafHomSectionLinearMap HGG V
      (α.val.app (op V) (HFF.obj.val.map (homOfLE hVU).op s)))
        (G.val.map (homOfLE hVU).op f) =
      G.val.map (homOfLE hVU).op
        ((sheafHomSectionLinearMap HGG U (α.val.app (op U) s)) f) := by
  have hα : HGG.obj.val.map (homOfLE hVU).op (α.val.app (op U) s) =
      α.val.app (op V) (HFF.obj.val.map (homOfLE hVU).op s) :=
    (PresheafOfModules.naturality_apply α.val (homOfLE hVU).op s).symm
  rw [← hα]
  exact sheafHomSectionLinearMap_restrict HGG hVU (α.val.app (op U) s) f

/-- The induced algebra isomorphism sends the linear map named by a section of the endomorphism
sheaf of `F` to the one named by its image under `α`. -/
private lemma sheafEndSectionAlgEquiv_apply_section
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (HFF : SheafHom Rc F F) (HGG : SheafHom Rc G G)
    (α : HFF.obj ≅ HGG.obj)
    (hα_one : ∀ U : Opens X, HGG.sectionsEquiv U
      (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (𝟙 (F.over U)))) =
        𝟙 (G.over U))
    (hα_comp : ∀ (U : Opens X) (f g : F.over U ⟶ F.over U),
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (f ≫ g))) =
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm f)) ≫
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm g)))
    (U : Opens X) {I K : Type u} [Finite I] [Finite K]
    (eF : SheafOfModules.free I ≅ F.over U)
    (eG : SheafOfModules.free K ≅ G.over U)
    (s : HFF.obj.val.obj (op U)) :
    (sheafEndSectionAlgEquiv HFF HGG α hα_one hα_comp U eF eG)
        (sheafHomSectionLinearMap HFF U s) =
      sheafHomSectionLinearMap HGG U (α.hom.val.app (op U) s) := by
  unfold sheafEndSectionAlgEquiv
  simp only [AlgEquiv.ofLinearEquiv_apply, LinearEquiv.trans_apply]
  have ha : (sheafHomSectionLinearMap HFF U s) =
      (LinearEquiv.ofBijective (sheafHomSectionLinearMap HFF U)
        (sheafHomApp_bijective_of_free HFF eF)) s := rfl
  rw [ha, LinearEquiv.symm_apply_apply]
  rfl

/-- The induced algebra isomorphisms on two nested opens agree after restriction, so they do not
depend on the chosen trivializations. -/
private lemma sheafEndSectionAlgEquiv_restrict_apply
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (HFF : SheafHom Rc F F) (HGG : SheafHom Rc G G)
    (α : HFF.obj ≅ HGG.obj)
    (hα_one : ∀ U : Opens X, HGG.sectionsEquiv U
      (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (𝟙 (F.over U)))) =
        𝟙 (G.over U))
    (hα_comp : ∀ (U : Opens X) (f g : F.over U ⟶ F.over U),
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (f ≫ g))) =
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm f)) ≫
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm g)))
    {U V : Opens X} (hVU : V ≤ U)
    {I K J L : Type u} [Finite I] [Finite K] [Finite J] [Finite L]
    (eFU : SheafOfModules.free I ≅ F.over U)
    (eGU : SheafOfModules.free K ≅ G.over U)
    (eFV : SheafOfModules.free J ≅ F.over V)
    (eGV : SheafOfModules.free L ≅ G.over V)
    (s : HFF.obj.val.obj (op U)) (f : G.val.obj (op U)) :
    (sheafEndSectionAlgEquiv HFF HGG α hα_one hα_comp V eFV eGV)
        (sheafHomSectionLinearMap HFF V
          (HFF.obj.val.map (homOfLE hVU).op s))
        (G.val.map (homOfLE hVU).op f) =
      G.val.map (homOfLE hVU).op
        ((sheafEndSectionAlgEquiv HFF HGG α hα_one hα_comp U eFU eGU)
          (sheafHomSectionLinearMap HFF U s) f) := by
  have hV := sheafEndSectionAlgEquiv_apply_section HFF HGG α hα_one hα_comp V eFV eGV
    (HFF.obj.val.map (homOfLE hVU).op s)
  have hU := sheafEndSectionAlgEquiv_apply_section HFF HGG α hα_one hα_comp U eFU eGU s
  rw [hV, hU]
  exact sheafHomSectionLinearMap_alpha_restrict HFF HGG α.hom hVU s f

/-- The restriction of a section naming a rank-one projection of a section basis names the
rank-one projection of the restricted section basis. -/
private lemma sheafHomSectionLinearMap_restrict_rankOne
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F : SheafOfModules.{u} (structureSheaf Rc)} {I : Type u} [Finite I]
    (H : SheafHom Rc F F) {U V : Opens X} (hVU : V ≤ U)
    (e : SheafOfModules.free I ≅ F.over U) (i : I) (s : H.obj.val.obj (op U))
    (hs : sheafHomSectionLinearMap H U s = LinearMap.smulRight
      ((sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e).coord i)
      (sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) e i)) :
    sheafHomSectionLinearMap H V (H.obj.val.map (homOfLE hVU).op s) =
      LinearMap.smulRight
        ((sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V)))
          (restrictFreeIso e hVU)).coord i)
        (sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V))) (restrictFreeIso e hVU) i) := by
  refine (sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V)))
    (restrictFreeIso e hVU)).ext fun i' => ?_
  rw [sectionBasisOfIso_restrictFreeIso_apply hVU e i']
  refine (sheafHomSectionLinearMap_restrict H hVU s _).trans ?_
  rw [hs]
  exact (rankOne_sectionBasis_restrict_apply hVU e i _).symm

/-- The coefficients of the induced algebra isomorphism applied to a restricted section commute
with restriction. -/
private lemma sheafEndSectionAlgEquiv_coord_restrict
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (HFF : SheafHom Rc F F) (HGG : SheafHom Rc G G)
    (α : HFF.obj ≅ HGG.obj)
    (hα_one : ∀ U : Opens X, HGG.sectionsEquiv U
      (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (𝟙 (F.over U)))) =
        𝟙 (G.over U))
    (hα_comp : ∀ (U : Opens X) (f g : F.over U ⟶ F.over U),
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (f ≫ g))) =
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm f)) ≫
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm g)))
    {U V : Opens X} (hVU : V ≤ U) {I K : Type u} [Finite I] [Finite K]
    (eF : SheafOfModules.free I ≅ F.over U) (eG : SheafOfModules.free K ≅ G.over U)
    (s : HFF.obj.val.obj (op U)) (j k : K) :
    (sectionBasisOfIso (Rc.over V) K (op (Over.mk (𝟙 V))) (restrictFreeIso eG hVU)).coord j
        (sheafEndSectionAlgEquiv HFF HGG α hα_one hα_comp V (restrictFreeIso eF hVU)
          (restrictFreeIso eG hVU) (sheafHomSectionLinearMap HFF V
            (HFF.obj.val.map (homOfLE hVU).op s))
          (sectionBasisOfIso (Rc.over V) K (op (Over.mk (𝟙 V))) (restrictFreeIso eG hVU) k)) =
      (Rc.obj.map (homOfLE hVU).op).hom
        ((sectionBasisOfIso (Rc.over U) K (op (Over.mk (𝟙 U))) eG).coord j
          (sheafEndSectionAlgEquiv HFF HGG α hα_one hα_comp U eF eG
            (sheafHomSectionLinearMap HFF U s)
            (sectionBasisOfIso (Rc.over U) K (op (Over.mk (𝟙 U))) eG k))) := by
  have hA := sheafEndSectionAlgEquiv_restrict_apply HFF HGG α hα_one hα_comp hVU eF eG
    (restrictFreeIso eF hVU) (restrictFreeIso eG hVU) s
    (sectionBasisOfIso (Rc.over U) K (op (Over.mk (𝟙 U))) eG k)
  rw [← sectionBasisOfIso_restrictFreeIso_apply hVU eG k] at hA
  rw [hA]
  exact sectionBasisOfIso_restrictFreeIso_coord hVU eG _ j

/-- A section of `SheafHom(F, G)` naming a linear equivalence that conjugates the induced algebra
isomorphism over `U` intertwines, after restriction to `V ≤ U`, each member of the restricted
endomorphism section basis with its image under `α`. -/
private lemma sheafHom_intertwines_basis_of_conjugator
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (HFF : SheafHom Rc F F) (HGG : SheafHom Rc G G)
    (HFG : SheafHom Rc F G) (α : HFF.obj ≅ HGG.obj)
    (hα_one : ∀ U : Opens X, HGG.sectionsEquiv U
      (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (𝟙 (F.over U)))) =
        𝟙 (G.over U))
    (hα_comp : ∀ (U : Opens X) (f g : F.over U ⟶ F.over U),
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (f ≫ g))) =
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm f)) ≫
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm g)))
    (U : Opens X) {I K : Type u} [Finite I] [Finite K] [Fintype I] [DecidableEq I]
    (eF : SheafOfModules.free I ≅ F.over U)
    (eG : SheafOfModules.free K ≅ G.over U)
    (t : HFG.obj.val.obj (op U))
    (T : F.val.obj (op U) ≃ₗ[Rc.obj.obj (op U)] G.val.obj (op U))
    (ht : sheafHomSectionLinearMap HFG U t = T.toLinearMap)
    (hT : sheafEndSectionAlgEquiv HFF HGG α hα_one hα_comp U eF eG =
      T.conjAlgEquiv (Rc.obj.obj (op U)))
    {V : Opens X} (hVU : V ≤ U) (ij : I × I) :
    (sheafHomSectionLinearMap HGG V (α.hom.val.app (op V)
        (sheafEndSectionBasis HFF V (restrictFreeIso eF hVU) ij))).comp
      (sheafHomSectionLinearMap HFG V (HFG.obj.val.map (homOfLE hVU).op t)) =
    (sheafHomSectionLinearMap HFG V (HFG.obj.val.map (homOfLE hVU).op t)).comp
      (sheafHomSectionLinearMap HFF V
        (sheafEndSectionBasis HFF V (restrictFreeIso eF hVU) ij)) := by
  let bFU := sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) eF
  let bFV := sectionBasisOfIso (Rc.over V) I (op (Over.mk (𝟙 V))) (restrictFreeIso eF hVU)
  let TV := sheafHomSectionLinearMap HFG V
    (HFG.obj.val.map (homOfLE hVU).op t)
  have hTV (g : F.val.obj (op U)) :
      TV (F.val.map (homOfLE hVU).op g) =
        G.val.map (homOfLE hVU).op (T g) := by
    change (sheafHomSectionLinearMap HFG V
      (HFG.obj.val.map (homOfLE hVU).op t))
      (F.val.map (homOfLE hVU).op g) = _
    rw [sheafHomSectionLinearMap_restrict HFG hVU t g, ht]
    rfl
  have hcommU (sU : HFF.obj.val.obj (op U)) (g : F.val.obj (op U)) :
      (sheafHomSectionLinearMap HGG U (α.hom.val.app (op U) sU)) (T g) =
        T ((sheafHomSectionLinearMap HFF U sU) g) := by
    rw [← sheafEndSectionAlgEquiv_apply_section HFF HGG α hα_one hα_comp U eF eG sU, hT]
    simp [LinearEquiv.conjAlgEquiv_apply]
  let sU := sheafEndSectionBasis HFF U eF ij
  let sV := sheafEndSectionBasis HFF V (restrictFreeIso eF hVU) ij
  have hs : HFF.obj.val.map (homOfLE hVU).op sU = sV :=
    sheafEndSectionBasis_restrict HFF hVU eF ij
  apply bFV.ext
  intro i
  have hbi : bFV i = F.val.map (homOfLE hVU).op (bFU i) :=
    sectionBasisOfIso_restrictFreeIso_apply hVU eF i
  have hAV : (sheafHomSectionLinearMap HFF V sV) (bFV i) =
      F.val.map (homOfLE hVU).op
        ((sheafHomSectionLinearMap HFF U sU) (bFU i)) := by
    rw [← hs, hbi]
    exact sheafHomSectionLinearMap_restrict HFF hVU sU (bFU i)
  have hαV :
      (sheafHomSectionLinearMap HGG V (α.hom.val.app (op V) sV))
        (G.val.map (homOfLE hVU).op (T (bFU i))) =
      G.val.map (homOfLE hVU).op
        ((sheafHomSectionLinearMap HGG U (α.hom.val.app (op U) sU))
          (T (bFU i))) := by
    rw [← hs]
    exact sheafHomSectionLinearMap_alpha_restrict HFF HGG α.hom hVU sU
      (T (bFU i))
  change (sheafHomSectionLinearMap HGG V (α.hom.val.app (op V) sV))
    (TV (bFV i)) = TV ((sheafHomSectionLinearMap HFF V sV) (bFV i))
  exact (congrArg
      (fun z => (sheafHomSectionLinearMap HGG V (α.hom.val.app (op V) sV)) z)
      ((congrArg (fun y => TV y) hbi).trans (hTV (bFU i)))).trans
    (hαV.trans ((congrArg (fun y => G.val.map (homOfLE hVU).op y)
        (hcommU sU (bFU i))).trans
      ((hTV ((sheafHomSectionLinearMap HFF U sU) (bFU i))).symm.trans
        (congrArg (fun y => TV y) hAV.symm))))

/-- A section of `SheafHom(F, G)` which names a linear equivalence conjugating the induced algebra
isomorphism over `U` intertwines the endomorphism sheaves on every open subset of `U`. The
finite endomorphism section basis is what lets the identity descend. -/
private lemma sheafHom_intertwines_of_conjugator
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (HFF : SheafHom Rc F F) (HGG : SheafHom Rc G G)
    (HFG : SheafHom Rc F G) (α : HFF.obj ≅ HGG.obj)
    (hα_one : ∀ U : Opens X, HGG.sectionsEquiv U
      (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (𝟙 (F.over U)))) =
        𝟙 (G.over U))
    (hα_comp : ∀ (U : Opens X) (f g : F.over U ⟶ F.over U),
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm (f ≫ g))) =
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm f)) ≫
      HGG.sectionsEquiv U
        (α.hom.val.app (op U) ((HFF.sectionsEquiv U).symm g)))
    (U : Opens X) {I K : Type u} [Finite I] [Finite K]
    (eF : SheafOfModules.free I ≅ F.over U)
    (eG : SheafOfModules.free K ≅ G.over U)
    (t : HFG.obj.val.obj (op U))
    (T : F.val.obj (op U) ≃ₗ[Rc.obj.obj (op U)] G.val.obj (op U))
    (ht : sheafHomSectionLinearMap HFG U t = T.toLinearMap)
    (hT : sheafEndSectionAlgEquiv HFF HGG α hα_one hα_comp U eF eG =
      T.conjAlgEquiv (Rc.obj.obj (op U))) :
    ∀ (V : Opens X) (hVU : V ≤ U) (s : HFF.obj.val.obj (op V))
      (f : F.val.obj (op V)),
      sheafHomApp HGG V V le_rfl (α.hom.val.app (op V) s)
          (sheafHomApp HFG U V hVU t f) =
        sheafHomApp HFG U V hVU t
          (sheafHomApp HFF V V le_rfl s f) := by
  intro V hVU s f
  classical
  let : Fintype I := Fintype.ofFinite I
  let eFV := restrictFreeIso eF hVU
  let TV := sheafHomSectionLinearMap HFG V (HFG.obj.val.map (homOfLE hVU).op t)
  have hmat (ij : I × I) := sheafHom_intertwines_basis_of_conjugator HFF HGG HFG α hα_one
    hα_comp U eF eG t T ht hT hVU ij
  let lhs : HFF.obj.val.obj (op V) →ₗ[Rc.obj.obj (op V)] G.val.obj (op V) :=
    (LinearMap.applyₗ (TV f)).comp
      ((sheafHomSectionLinearMap HGG V).comp
        (show HFF.obj.val.obj (op V) →ₗ[Rc.obj.obj (op V)] HGG.obj.val.obj (op V) from
          (α.hom.val.app (op V)).hom))
  let rhs : HFF.obj.val.obj (op V) →ₗ[Rc.obj.obj (op V)] G.val.obj (op V) :=
    TV.comp ((LinearMap.applyₗ f).comp (sheafHomSectionLinearMap HFF V))
  have hlr : lhs = rhs := by
    apply (sheafEndSectionBasis HFF V eFV).ext
    intro ij
    change (sheafHomSectionLinearMap HGG V
        (α.hom.val.app (op V) (sheafEndSectionBasis HFF V eFV ij))) (TV f) =
      TV ((sheafHomSectionLinearMap HFF V
        (sheafEndSectionBasis HFF V eFV ij)) f)
    exact LinearMap.congr_fun (hmat ij) f
  change sheafHomApp HGG V V le_rfl (α.hom.val.app (op V) s)
      (sheafHomApp HFG U V hVU t f) =
    sheafHomApp HFG U V hVU t (sheafHomApp HFF V V le_rfl s f)
  rw [← sheafHomApp_restrict HFG hVU le_rfl t f,
    ← sheafHomApp_restrict HFG hVU le_rfl t
      (sheafHomApp HFF V V le_rfl s f)]
  exact LinearMap.congr_fun hlr s

/-- A section of the intertwiner sheaf over `U` naming a bijection is a basis of one element of the
intertwiner sheaf over `U`: every intertwiner is a unique scalar multiple of it. -/
private lemma sheafIntertwiner_basis_of_bijective
    {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf Rc)}
    (HFF : SheafHom Rc F F) (HGG : SheafHom Rc G G) (HFG : SheafHom Rc F G)
    (α : HFF.obj ⟶ HGG.obj) (U : Opens X) {I : Type u} [Finite I] [Nonempty I]
    (eF : SheafOfModules.free I ≅ F.over U)
    (t : (sheafIntertwiner HFF HGG HFG α).toSheafOfModules.val.obj (op U))
    (ht : Function.Bijective (sheafHomApp HFG U U le_rfl t.1)) :
    Function.Bijective (fun r : Rc.obj.obj (op U) => r • t) := by
  let N := sheafIntertwiner HFF HGG HFG α
  let a := sheafHomSectionLinearMap HFG U
  let T := LinearEquiv.ofBijective (a t.1) ht
  let b := sectionBasisOfIso (Rc.over U) I (op (Over.mk (𝟙 U))) eF
  have hscalar (l : N.toSheafOfModules.val.obj (op U)) :
      ∃! r : Rc.obj.obj (op U), a l.1 = r • T.toLinearMap := by
    apply existsUnique_scalar_of_intertwines b T (a l.1)
    intro A
    obtain ⟨s, hs⟩ := (sheafHomApp_bijective_of_free HFF eF).surjective A
    have key (l : N.toSheafOfModules.val.obj (op U)) (f : F.val.obj (op U)) :
        sheafHomApp HGG U U le_rfl (α.val.app (op U) s) (sheafHomApp HFG U U le_rfl l.1 f) =
          sheafHomApp HFG U U le_rfl l.1 (A f) := by
      rw [← hs]
      exact l.2 U le_rfl s f
    exact ⟨_, LinearMap.ext (key t), LinearMap.ext (key l)⟩
  constructor
  · intro r s hrs
    obtain ⟨c, hc, huniq⟩ := hscalar (r • t)
    have hr : a (r • t).1 = r • T.toLinearMap := a.map_smul r t.1
    have hs : a (r • t).1 = s • T.toLinearMap :=
      (congrArg (fun l : N.toSheafOfModules.val.obj (op U) => a l.1) hrs).trans
        (a.map_smul s t.1)
    exact (huniq r hr).trans (huniq s hs).symm
  · intro l
    obtain ⟨r, hr, _⟩ := hscalar l
    refine ⟨r, Subtype.ext ?_⟩
    apply (sheafHomApp_bijective_of_free HFG eF).injective
    change a (r • t.1) = a l.1
    rw [a.map_smul]
    exact hr.symm
end

end Stacks.EtaleCohomology
