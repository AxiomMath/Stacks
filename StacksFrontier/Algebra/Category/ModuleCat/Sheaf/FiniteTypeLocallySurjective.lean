module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Limits.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Topology.Sheaves.LocallySurjective
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Surjectivity near a point of a map onto a module of finite type

Let `(X, O_X)` be a ringed space and `φ : G ⟶ F` a homomorphism of `O_X`-modules with `F` of
finite type. If the induced map on stalks `G_x → F_x` is surjective at a point `x`, then there is
an open neighbourhood `U` of `x` such that the induced map on stalks is surjective at every point
of `U`.

## Main definitions

* `Stacks.SheafOfModules.LocallySurjective.underlyingAb`: the morphism of underlying sheaves of
  abelian groups of a homomorphism of `O_X`-modules.
* `Stacks.SheafOfModules.LocallySurjective.SurjOnStalk`: the induced map on the stalk at a point
  is surjective.
* `Stacks.SheafOfModules.LocallySurjective.LocallySurjOn`: local surjectivity at the points of an
  open set.
* `Stacks.SheafOfModules.LocallySurjective.LocalLinComb`: every section over an open contained in
  `V` is locally an `O`-linear combination of the given sections over `V`.

## Main results

* `Stacks.SheafOfModules.LocallySurjective.main_theorem`: a map onto a module of finite type
  which is surjective on the stalk at `x` is surjective on the stalks at all points of some open
  neighbourhood of `x`.

## References

* [Stacks Project, Tag 01B8](https://stacks.math.columbia.edu/tag/01B8)
-/

open CategoryTheory AlgebraicGeometry TopCat Opposite TopologicalSpace

universe uO u v

namespace Stacks.SheafOfModules.LocallySurjective

variable {X : AlgebraicGeometry.RingedSpace.{uO, u}}
    {R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- The underlying morphism of sheaves of abelian groups associated to a
homomorphism `φ : G ⟶ F` of `O_X`-modules. -/
noncomputable def underlyingAb {F G : SheafOfModules.{u} R} (φ : G ⟶ F) :
    (G.val.presheaf : TopCat.Presheaf Ab.{u} X.toPresheafedSpace) ⟶ F.val.presheaf :=
  (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget R).map φ)

/-- The induced map `G_x → F_x` on stalks at `x` of a homomorphism `φ : G ⟶ F` of `O_X`-modules is
surjective. -/
def SurjOnStalk {F G : SheafOfModules.{u} R} (φ : G ⟶ F) (x : X) : Prop :=
  Function.Surjective
    (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map (underlyingAb φ)))

/-- `LocallySurjOn φ W` says that `underlyingAb φ` is locally surjective at the points of the open
set `W`: for every section `t` of `F` over an open `U` and every point `y ∈ U ∩ W`, there are an
open `V ∋ y` with `V ≤ U` and a section `g` of `G` over `V` with `φ(g) = t|_V`. -/
def LocallySurjOn {F G : SheafOfModules.{u} R} (φ : G ⟶ F) (W : TopologicalSpace.Opens X) : Prop :=
  ∀ (U : TopologicalSpace.Opens X) (t : (F.val.presheaf.obj (op U)))
    (y : X), y ∈ U → y ∈ W →
    ∃ (V : TopologicalSpace.Opens X) (hVU : V ≤ U),
      (∃ g, (ConcreteCategory.hom ((underlyingAb φ).app (op V))) g
              = (F.val.presheaf.map (homOfLE hVU).op) t) ∧ y ∈ V

/-- `LocalLinComb V s` says that the sections `s : J₀ → F(V)` locally generate `F` over `V`: for
every open `U ≤ V`, point `y ∈ U`, and section `t ∈ F(U)`, there are an open `V' ≤ U` with
`y ∈ V'` and scalars `a : J₀ → O(V')` such that `t|_{V'} = Σ_j a_j • (s_j)|_{V'}`. -/
def LocalLinComb {F : SheafOfModules.{u} R} {J₀ : Type v} [Fintype J₀]
    (V : TopologicalSpace.Opens X) (s : J₀ → F.val.presheaf.obj (op V)) : Prop :=
  ∀ (U : TopologicalSpace.Opens X) (hUV : U ≤ V) (t : F.val.presheaf.obj (op U)) (y : X),
    y ∈ U →
    ∃ (V' : TopologicalSpace.Opens X) (hV'U : V' ≤ U), y ∈ V' ∧
      ∃ a : J₀ → R.obj.obj (op V'),
        (F.val.presheaf.map (homOfLE hV'U).op) t
          = ∑ j, (a j • ((F.val.presheaf.map (homOfLE (le_trans hV'U hUV)).op) (s j) :
              F.val.obj (op V')) : F.val.obj (op V'))

/-- If every section `s` of `F` over an open `U ∋ y` is, on some open `V ∋ y` inside `U`, the image
of a section of `G`, then `φ` is surjective on the stalk at `y`. -/
private theorem surjOnStalk_of_exists_lift {F G : SheafOfModules.{u} R} (φ : G ⟶ F) {y : X}
    (h : ∀ (U : TopologicalSpace.Opens X) (s : F.val.presheaf.obj (op U)), y ∈ U →
      ∃ (V : TopologicalSpace.Opens X) (hVU : V ≤ U),
        (∃ g, (ConcreteCategory.hom ((underlyingAb φ).app (op V))) g
              = (F.val.presheaf.map (homOfLE hVU).op) s) ∧ y ∈ V) :
    SurjOnStalk φ y := by
  intro t
  obtain ⟨U, hyU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf t
  obtain ⟨V, hVU, ⟨r, hr⟩, hyV⟩ := h U s hyU
  refine ⟨(ConcreteCategory.hom (TopCat.Presheaf.germ G.val.presheaf V y hyV)) r, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hr]
  exact TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE hVU) y hyV s

/-- If the underlying morphism of sheaves of abelian groups is locally surjective, then it is
surjective on the stalk at every point `y`. -/
theorem surjOnStalk_of_isLocallySurjective {F G : SheafOfModules.{u} R} (φ : G ⟶ F)
    (h : TopCat.Presheaf.IsLocallySurjective (underlyingAb φ)) (y : X) :
    SurjOnStalk φ y := by
  rw [TopCat.Presheaf.isLocallySurjective_iff] at h
  exact surjOnStalk_of_exists_lift φ fun U s hyU ↦ h U s y hyU

/-- If `LocallySurjOn φ W`, then `φ` is surjective on the stalk at every point of `W`. -/
theorem surjOnStalk_of_locallySurjOn {F G : SheafOfModules.{u} R} (φ : G ⟶ F)
    {W : TopologicalSpace.Opens X} (h : LocallySurjOn φ W) {y : X} (hy : y ∈ W) :
    SurjOnStalk φ y :=
  surjOnStalk_of_exists_lift φ fun U s hyU ↦ h U s y hyU hy

/-- The functor `SheafOfModules.toSheaf` preserves every colimit that exists in presheaves of
modules, since sheafification and the forgetful functor do and the counit is an isomorphism. -/
private theorem preservesColimit_toSheaf {J : Type*} [Category J] (V : Opens X)
    [Limits.HasColimitsOfShape J AddCommGrpCat.{u}]
    (K : J ⥤ SheafOfModules.{u} (R.over V)) :
    Limits.PreservesColimit K (SheafOfModules.toSheaf (R.over V)) := by
  let RV := R.over V
  let JV := (Opens.grothendieckTopology X).over V
  let L := PresheafOfModules.sheafification (R := RV) (𝟙 RV.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := RV) (𝟙 RV.obj)
  let Rt := SheafOfModules.forget RV ⋙ PresheafOfModules.restrictScalars (𝟙 RV.obj)
  have : Limits.PreservesColimitsOfShape J L := inferInstance
  let K'' : J ⥤ PresheafOfModules.{u} RV.obj := K ⋙ Rt
  let G := (PresheafOfModules.toPresheaf RV.obj) ⋙ (presheafToSheaf JV AddCommGrpCat.{u})
  have isoG : (L ⋙ (SheafOfModules.toSheaf RV)) ≅ G :=
    PresheafOfModules.sheafificationCompToSheaf (R := RV) (𝟙 RV.obj)
  have : Limits.PreservesColimitsOfShape J (PresheafOfModules.toPresheaf RV.obj) :=
    PresheafOfModules.toPresheaf_preservesColimitsOfShape RV.obj J
  have : Limits.PreservesColimitsOfShape J G := inferInstance
  have : Limits.PreservesColimit K'' (L ⋙ (SheafOfModules.toSheaf RV)) :=
    Limits.preservesColimit_of_natIso K'' isoG.symm
  have : IsIso adj.counit := inferInstance
  let εiso : Rt ⋙ L ≅ 𝟭 (SheafOfModules.{u} RV) := asIso adj.counit
  have e : K ≅ K''.comp L :=
    (Functor.rightUnitor K).symm ≪≫ Functor.isoWhiskerLeft K εiso.symm ≪≫
      (Functor.associator K Rt L).symm
  have hc : Limits.IsColimit (L.mapCocone (Limits.colimit.cocone K'')) :=
    Limits.isColimitOfPreserves L (Limits.colimit.isColimit K'')
  have hF : Limits.IsColimit ((SheafOfModules.toSheaf RV).mapCocone
      (L.mapCocone (Limits.colimit.cocone K''))) :=
    Limits.isColimitOfPreserves (L ⋙ (SheafOfModules.toSheaf RV)) (Limits.colimit.isColimit K'')
  have hpc : Limits.PreservesColimit (K''.comp L) (SheafOfModules.toSheaf RV) :=
    Limits.preservesColimit_of_preserves_colimit_cocone hc hF
  exact Limits.preservesColimit_of_iso_diagram (SheafOfModules.toSheaf RV) e.symm

set_option maxHeartbeats 1000000 in
-- this proof's elaboration needs more than the default heartbeat budget
set_option synthInstance.maxHeartbeats 400000 in
/-- The canonical map from the presheaf coproduct of copies of the unit presheaf to the underlying
presheaf of the free module `SheafOfModules.free I` is locally surjective. -/
theorem freeUnderlyingPresheafLocallySurjective
    (V : TopologicalSpace.Opens X) (I : Type u) :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X |>.over V)
      (show (∐ fun _ : I => (SheafOfModules.unit (R.over V)).val.presheaf) ⟶
          (SheafOfModules.free (R := R.over V) I).val.presheaf from
        Limits.Sigma.desc (fun j : I => (PresheafOfModules.toPresheaf (R.over V).obj).map
          ((SheafOfModules.forget (R.over V)).map (SheafOfModules.ιFree (R := R.over V) j)))) := by
  let RV := R.over V
  let JV := (Opens.grothendieckTopology X).over V
  have hpres : Limits.PreservesColimit (Discrete.functor (fun _ : I => SheafOfModules.unit RV))
      (SheafOfModules.toSheaf RV) := preservesColimit_toSheaf V _
  let Dpre : Discrete I ⥤ ((CategoryTheory.Over V)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    Discrete.functor (fun _ : I => (SheafOfModules.unit RV).val.presheaf)
  let Dq : Discrete I ⥤ CategoryTheory.Sheaf JV AddCommGrpCat.{u} :=
    Dpre.comp (presheafToSheaf JV AddCommGrpCat.{u})
  let s : Limits.Cocone Dq :=
    (presheafToSheaf JV AddCommGrpCat.{u}).mapCocone (Limits.colimit.cocone Dpre)
  have hs : Limits.IsColimit s :=
    Limits.isColimitOfPreserves (presheafToSheaf JV AddCommGrpCat.{u})
      (Limits.colimit.isColimit Dpre)
  let unitIso : (SheafOfModules.toSheaf RV).obj (SheafOfModules.unit RV) ≅
      (presheafToSheaf JV AddCommGrpCat.{u}).obj (SheafOfModules.unit RV).val.presheaf := by
    refine (sheafToPresheaf JV AddCommGrpCat.{u}).preimageIso ?_
    have : IsIso (toSheafify JV (SheafOfModules.unit RV).val.presheaf) :=
      isIso_toSheafify JV (SheafOfModules.unit RV).isSheaf
    exact asIso (toSheafify JV (SheafOfModules.unit RV).val.presheaf)
  have hunitval : (sheafToPresheaf JV AddCommGrpCat.{u}).map unitIso.hom
      = toSheafify JV (SheafOfModules.unit RV).val.presheaf := by
    simp only [unitIso, Functor.preimageIso_hom, Functor.map_preimage]
    rfl
  let diso : (Discrete.functor (fun _ : I => SheafOfModules.unit RV)).comp
      (SheafOfModules.toSheaf RV) ≅ Dq :=
    Discrete.natIso (fun _ ↦ unitIso)
  have htfree : Limits.IsColimit ((SheafOfModules.toSheaf RV).mapCocone (SheafOfModules.freeCofan
      I)) :=
    Limits.isColimitOfPreserves (SheafOfModules.toSheaf RV) (SheafOfModules.isColimitFreeCofan I)
  let β := htfree.coconePointsIsoOfNatIso hs diso
  set m : (SheafOfModules.toSheaf RV).obj (SheafOfModules.free I) ⟶
      (presheafToSheaf JV AddCommGrpCat.{u}).obj (Limits.colimit Dpre) := β.hom with hm
  set mval := (sheafToPresheaf JV AddCommGrpCat.{u}).map m with hmval
  set η : (∐ fun _ : I => (SheafOfModules.unit RV).val.presheaf) ⟶
          (SheafOfModules.free (R := RV) I).val.presheaf :=
        Limits.Sigma.desc (fun j : I => (PresheafOfModules.toPresheaf RV.obj).map
          ((SheafOfModules.forget RV).map (SheafOfModules.ιFree (R := RV) j))) with hη
  have hfac : η ≫ mval = toSheafify JV (Limits.colimit Dpre) := by
    apply Limits.colimit.hom_ext
    intro j
    obtain ⟨j⟩ := j
    have hleg := htfree.comp_coconePointsIsoOfNatIso_hom hs diso ⟨j⟩
    have hlegval := congrArg (fun (φ : _ ⟶ _) ↦ (sheafToPresheaf JV AddCommGrpCat.{u}).map φ) hleg
    simp only [Functor.map_comp] at hlegval
    have hηj : Limits.colimit.ι Dpre ⟨j⟩ ≫ η
        = (sheafToPresheaf JV AddCommGrpCat.{u}).map
            (((SheafOfModules.toSheaf RV).mapCocone (SheafOfModules.freeCofan I)).ι.app ⟨j⟩) := by
      rw [hη]
      rw [Limits.colimit.ι_desc]
      show _ = ((SheafOfModules.toSheaf RV).map ((SheafOfModules.freeCofan I).ι.app ⟨j⟩)).hom
      rw [SheafOfModules.toSheaf_map_hom]
      simp only [SheafOfModules.freeCofan, Limits.Cofan.mk_ι_app]
      rfl
    have hsj : (sheafToPresheaf JV AddCommGrpCat.{u}).map (s.ι.app ⟨j⟩)
        = sheafifyMap JV (Limits.colimit.ι Dpre ⟨j⟩) := rfl
    have hdj : (sheafToPresheaf JV AddCommGrpCat.{u}).map (diso.hom.app ⟨j⟩)
        = toSheafify JV (SheafOfModules.unit RV).val.presheaf := by
      simp only [diso, Discrete.natIso_hom_app]; exact hunitval
    rw [← Category.assoc, hηj, hlegval, hdj, hsj]
    exact (toSheafify_naturality _ _).symm
  have : IsIso m := β.isIso_hom
  have : IsIso mval := by rw [hmval]; infer_instance
  have : Presheaf.IsLocallyInjective JV mval := inferInstance
  have : Presheaf.IsLocallySurjective JV (toSheafify JV (Limits.colimit Dpre)) :=
    Presheaf.isLocallySurjective_toSheafify' (J := JV) (P := Limits.colimit Dpre)
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac JV _ hfac

set_option backward.isDefEq.respectTransparency true in
/-- In a category of presheaves of abelian groups, the `W`-component of an element of a finite
biproduct is the sum of the injections of its projections. -/
theorem biproduct_decode {C : Type*} [Category C]
    {J : Type v} [Fintype J] (f : J → (Cᵒᵖ ⥤ AddCommGrpCat.{u})) [Limits.HasBiproduct f]
    (W : Cᵒᵖ) (x : ToType ((⨁ f).obj W)) :
    x = ∑ j, (ConcreteCategory.hom ((Limits.biproduct.ι f j).app W))
        ((ConcreteCategory.hom ((Limits.biproduct.π f j).app W)) x) := by
  have htot := Limits.IsBilimit.total (Limits.biproduct.isBilimit f)
  have hev : (ConcreteCategory.hom ((𝟙 (⨁ f) : (⨁ f) ⟶ (⨁ f)).app W)) x = x := by
    rw [NatTrans.id_app, ConcreteCategory.id_apply]
  rw [← htot] at hev
  conv_lhs => rw [← hev]
  rw [NatTrans.app_sum]
  have hsumapp : ∀ (T : Finset J) (φ : J → ((⨁ f).obj W ⟶ (⨁ f).obj W)) (z : ToType ((⨁ f).obj W)),
      (ConcreteCategory.hom (∑ i ∈ T, φ i)) z = ∑ i ∈ T, (ConcreteCategory.hom (φ i)) z := by
    classical
    intro T φ z
    induction T using Finset.induction with
    | empty => simp
    | insert a S ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]
  rw [hsumapp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply]

set_option maxHeartbeats 4000000 in
-- this proof's elaboration needs more than the default heartbeat budget
set_option synthInstance.maxHeartbeats 400000 in
/-- The `j`-th coproduct component of the composite of the canonical map from the presheaf
coproduct of unit presheaves to the free module with `ψ` is the underlying presheaf map of
`unitHomEquiv.symm (gs.s j)`. -/
theorem comb_component {F : SheafOfModules.{u} R}
    (V : TopologicalSpace.Opens X) (gs : (F.over V).GeneratingSections)
    (ψ : SheafOfModules.free gs.I ⟶ (F.over V))
    (hgen : ∀ i, SheafOfModules.ιFree i ≫ ψ
        = (F.over V).unitHomEquiv.symm (gs.s i))
    (j : gs.I) :
    Limits.Sigma.ι (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) j ≫
        (Limits.Sigma.desc (fun j : gs.I => (PresheafOfModules.toPresheaf (R.over V).obj).map
          ((SheafOfModules.forget (R.over V)).map (SheafOfModules.ιFree (R := R.over V) j)))
          ≫ ((SheafOfModules.toSheaf (R.over V)).map ψ).hom)
      = (PresheafOfModules.toPresheaf (R.over V).obj).map
          ((SheafOfModules.forget (R.over V)).map ((F.over V).unitHomEquiv.symm (gs.s j))) := by
  rw [← Category.assoc, Limits.Sigma.ι_desc,
    show ((SheafOfModules.toSheaf (R.over V)).map ψ).hom
      = (PresheafOfModules.toPresheaf (R.over V).obj).map ((SheafOfModules.forget (R.over V)).map
          ψ) from rfl,
    ← Functor.map_comp, ← Functor.map_comp, hgen j]

set_option maxHeartbeats 4000000 in
-- this proof's elaboration needs more than the default heartbeat budget
set_option synthInstance.maxHeartbeats 400000 in
/-- The underlying presheaf map of `unitHomEquiv.symm (gs.s j)` at the slice object of `V' ≤ V`
sends a ring element `r` to `r • (s_j)|_{V'}`. -/
theorem unitHom_app_smul {F : SheafOfModules.{u} R}
    (V : TopologicalSpace.Opens X) (gs : (F.over V).GeneratingSections)
    (s : gs.I → F.val.presheaf.obj (op V))
    (hsdef : s = fun j => (gs.s j).val (op (Over.mk (𝟙 V))))
    (j : gs.I) (V' : TopologicalSpace.Opens X) (hV'V : V' ≤ V)
    (r : R.obj.obj (op V')) :
    (ConcreteCategory.hom (((PresheafOfModules.toPresheaf (R.over V).obj).map
        ((SheafOfModules.forget (R.over V)).map ((F.over V).unitHomEquiv.symm (gs.s j)))).app
        (op (Over.mk (homOfLE hV'V))))) r
      = r • ((F.val.presheaf.map (homOfLE hV'V).op) (s j)) := by
  have hval : ((SheafOfModules.forget (R.over V)).map ((F.over V).unitHomEquiv.symm (gs.s j)))
      = (F.over V).val.unitHomEquiv.symm (gs.s j) := by
    simp only [SheafOfModules.unitHomEquiv, Equiv.symm_trans_apply]
    rfl
  rw [hval]
  have hsval : (gs.s j).val (op (Over.mk (homOfLE hV'V)))
      = (F.val.presheaf.map (homOfLE hV'V).op) (s j) := by
    rw [hsdef]
    exact ((gs.s j).2 (Over.homMk (homOfLE hV'V) (by simp) :
      Over.mk (homOfLE hV'V) ⟶ Over.mk (𝟙 V)).op).symm
  rw [← hsval]
  simp only [PresheafOfModules.unitHomEquiv, Equiv.coe_fn_symm_mk]
  rfl

set_option maxHeartbeats 4000000 in
-- this proof's elaboration needs more than the default heartbeat budget
set_option synthInstance.maxHeartbeats 400000 in
/-- The composite of the canonical map from the presheaf coproduct of unit presheaves to the free
module with `ψ`, applied to a section `a₁` of the coproduct over the slice object of `V' ≤ V`, is
a linear combination `∑ a_j • (s_j|_{V'})` of the generators. -/
theorem combApp_decode {F : SheafOfModules.{u} R}
    (V : TopologicalSpace.Opens X) (gs : (F.over V).GeneratingSections) [Fintype gs.I]
    (s : gs.I → F.val.presheaf.obj (op V))
    (hsdef : s = fun j => (gs.s j).val (op (Over.mk (𝟙 V))))
    (ψ : SheafOfModules.free gs.I ⟶ (F.over V))
    (hgen : ∀ i, SheafOfModules.ιFree i ≫ ψ
        = (F.over V).unitHomEquiv.symm (gs.s i))
    (V' : TopologicalSpace.Opens X) (hV'V : V' ≤ V)
    (a₁ : ((∐ fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).obj
        (op (Over.mk (homOfLE hV'V)))) :
    ∃ a : gs.I → R.obj.obj (op V'),
      (ConcreteCategory.hom ((Limits.Sigma.desc (fun j : gs.I =>
            (PresheafOfModules.toPresheaf (R.over V).obj).map
              ((SheafOfModules.forget (R.over V)).map (SheafOfModules.ιFree (R := R.over V) j)))
            ≫ ((SheafOfModules.toSheaf (R.over V)).map ψ).hom).app (op (Over.mk (homOfLE hV'V)))))
                a₁
        = ∑ j, (a j • ((F.val.presheaf.map (homOfLE hV'V).op) (s j) :
            F.val.obj (op V')) : F.val.obj (op V')) := by
  set comb := (Limits.Sigma.desc (fun j : gs.I =>
        (PresheafOfModules.toPresheaf (R.over V).obj).map
          ((SheafOfModules.forget (R.over V)).map (SheafOfModules.ιFree (R := R.over V) j)))
        ≫ ((SheafOfModules.toSheaf (R.over V)).map ψ).hom) with hcomb
  have : Limits.HasFiniteBiproducts ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    Limits.HasFiniteBiproducts.of_hasFiniteCoproducts
  set a : gs.I → R.obj.obj (op V') := fun j ↦
    (ConcreteCategory.hom ((Limits.biproduct.π
      (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) j).app
      (op (Over.mk (homOfLE hV'V)))))
      ((ConcreteCategory.hom ((Limits.biproduct.isoCoproduct
        (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).inv.app
        (op (Over.mk (homOfLE hV'V))))) a₁) with ha
  refine ⟨a, ?_⟩
  have hcomp2 : ∀ j, (Limits.biproduct.ι
        (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) j ≫
        (Limits.biproduct.isoCoproduct
          (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).hom) ≫ comb
      = (PresheafOfModules.toPresheaf (R.over V).obj).map
          ((SheafOfModules.forget (R.over V)).map ((F.over V).unitHomEquiv.symm (gs.s j))) := by
    intro j
    rw [(by rw [← Iso.eq_comp_inv, Limits.biproduct.isoCoproduct_inv, Limits.Sigma.ι_desc] :
      Limits.biproduct.ι (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) j ≫
        (Limits.biproduct.isoCoproduct
          (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).hom
        = Limits.Sigma.ι (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) j),
      hcomb]
    exact comb_component V gs ψ hgen j
  have hact : ∀ (j : gs.I) (r : R.obj.obj (op V')),
      (ConcreteCategory.hom (((Limits.biproduct.ι
        (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) j ≫
        (Limits.biproduct.isoCoproduct
          (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).hom) ≫ comb).app
        (op (Over.mk (homOfLE hV'V))))) r
      = r • ((F.val.presheaf.map (homOfLE hV'V).op) (s j)) := by
    intro j r
    rw [hcomp2 j]
    exact unitHom_app_smul V gs s hsdef j V' hV'V r
  have hround : a₁ = (ConcreteCategory.hom ((Limits.biproduct.isoCoproduct
        (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).hom.app
          (op (Over.mk (homOfLE hV'V)))))
        ((ConcreteCategory.hom ((Limits.biproduct.isoCoproduct
          (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).inv.app
            (op (Over.mk (homOfLE hV'V))))) a₁) :=
    (Iso.inv_hom_id_app_apply (Limits.biproduct.isoCoproduct
      (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf))
        (op (Over.mk (homOfLE hV'V))) a₁).symm
  have htotapp : (ConcreteCategory.hom ((Limits.biproduct.isoCoproduct
          (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).inv.app
            (op (Over.mk (homOfLE hV'V))))) a₁
      = ∑ j, (ConcreteCategory.hom ((Limits.biproduct.ι
          (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) j).app
          (op (Over.mk (homOfLE hV'V)))))
          (a j) :=
    biproduct_decode
      (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) (op (Over.mk (homOfLE hV'V)))
      ((ConcreteCategory.hom ((Limits.biproduct.isoCoproduct
          (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).inv.app
            (op (Over.mk (homOfLE hV'V))))) a₁)
  have hdecomp : a₁ = ∑ j, (ConcreteCategory.hom (((Limits.biproduct.ι
        (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) j ≫
        (Limits.biproduct.isoCoproduct
          (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).hom)).app
        (op (Over.mk (homOfLE hV'V))))) (a j) := by
    rw [hround, htotapp, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
  calc (ConcreteCategory.hom (comb.app (op (Over.mk (homOfLE hV'V))))) a₁
      = (ConcreteCategory.hom (comb.app (op (Over.mk (homOfLE hV'V)))))
          (∑ j, (ConcreteCategory.hom (((Limits.biproduct.ι
            (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) j ≫
            (Limits.biproduct.isoCoproduct
              (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).hom)).app
            (op (Over.mk (homOfLE hV'V))))) (a j)) := by
        rw [← hdecomp]
    _ = ∑ j, (ConcreteCategory.hom (comb.app (op (Over.mk (homOfLE hV'V)))))
          ((ConcreteCategory.hom (((Limits.biproduct.ι
            (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) j ≫
            (Limits.biproduct.isoCoproduct
              (fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf)).hom)).app
            (op (Over.mk (homOfLE hV'V))))) (a j)) := by
        rw [map_sum]
    _ = ∑ j, (a j •
        ((F.val.presheaf.map (homOfLE hV'V).op) (s j) : F.val.obj (op V'))
        : F.val.obj (op V')) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        have h1 := hact j (a j)
        rwa [NatTrans.comp_app, ConcreteCategory.comp_apply] at h1

set_option maxHeartbeats 1000000 in
-- this proof's elaboration needs more than the default heartbeat budget
set_option synthInstance.maxHeartbeats 400000 in
/-- For generating sections `gs` of `F.over V` with finite index set and their components `s` over
`V`, every section of `F` over an open `U ≤ V` is, near each point of `U`, an `O`-linear
combination of the restrictions of the `s j`. -/
theorem localLinComb_of_combSurj {F : SheafOfModules.{u} R}
    (V : TopologicalSpace.Opens X) (gs : (F.over V).GeneratingSections)
    [Fintype gs.I]
    (s : gs.I → F.val.presheaf.obj (op V))
    (hsdef : s = fun j => (gs.s j).val (op (Over.mk (𝟙 V))))
    (ψ : SheafOfModules.free gs.I ⟶ (F.over V))
    (hψ : ψ = (F.over V).freeHomEquiv.symm gs.s)
    (hgen : ∀ i, SheafOfModules.ιFree i ≫ ψ
        = (F.over V).unitHomEquiv.symm (gs.s i))
    (U : TopologicalSpace.Opens X) (hUV : U ≤ V)
    (t : F.val.presheaf.obj (op U)) (y : X) (hyU : y ∈ U) :
    ∃ (V' : TopologicalSpace.Opens X) (hV'U : V' ≤ U), y ∈ V' ∧
      ∃ a : gs.I → R.obj.obj (op V'),
        (F.val.presheaf.map (homOfLE hV'U).op) t
          = ∑ j, (a j • ((F.val.presheaf.map (homOfLE (le_trans hV'U hUV)).op) (s j) :
              F.val.obj (op V')) : F.val.obj (op V')) := by
  set JV := (Opens.grothendieckTopology X).over V with hJV
  set η : (∐ fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf) ⟶
          (SheafOfModules.free (R := R.over V) gs.I).val.presheaf :=
        Limits.Sigma.desc (fun j : gs.I => (PresheafOfModules.toPresheaf (R.over V).obj).map
          ((SheafOfModules.forget (R.over V)).map (SheafOfModules.ιFree (R := R.over V) j))) with hη
  set comb := η ≫ ((SheafOfModules.toSheaf (R.over V)).map ψ).hom with hcomb
  have hηsurj : Presheaf.IsLocallySurjective JV η := freeUnderlyingPresheafLocallySurjective V gs.I
  have hψsurj :
      Presheaf.IsLocallySurjective JV ((SheafOfModules.toSheaf (R.over V)).map ψ).hom := by
    let RV := R.over V
    have hepi : Epi ψ := by rw [hψ]; exact gs.epi
    have hpres : Limits.PreservesColimit (Limits.span ψ ψ) (SheafOfModules.toSheaf RV) :=
      preservesColimit_toSheaf V _
    have hpush : IsPushout ψ ψ (𝟙 _) (𝟙 _) := (epi_iff_isPushout ψ).mp hepi
    have hpush2 := hpush.map (SheafOfModules.toSheaf RV)
    simp only [CategoryTheory.Functor.map_id] at hpush2
    exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((SheafOfModules.toSheaf RV).map ψ)).mpr ((epi_iff_isPushout _).mpr hpush2)
  have hcombsurj : Presheaf.IsLocallySurjective JV comb := by
    rw [hcomb]
    exact Presheaf.isLocallySurjective_comp JV η ((SheafOfModules.toSheaf (R.over V)).map ψ).hom
  let Uo : Over V := Over.mk (homOfLE hUV)
  have hmem := Presheaf.imageSieve_mem JV comb (U := op Uo) t
  rw [GrothendieckTopology.mem_over_iff] at hmem
  obtain ⟨W', f', harr, hyW'⟩ := hmem y hyU
  obtain ⟨Z, g, h, hgmem, hfeq⟩ := harr
  obtain ⟨a₀, ha₀⟩ := hgmem
  have hV'U : W' ≤ U := leOfHom f'
  refine ⟨W', hV'U, hyW', ?_⟩
  set W'sl : Over V := Over.mk (homOfLE (le_trans hV'U hUV)) with hW'sl
  have hcomm : h ≫ Z.hom = (homOfLE (le_trans hV'U hUV)) := Subsingleton.elim _ _
  set hs : W'sl ⟶ Z := Over.homMk h hcomm with hhs
  set a₁ := (ConcreteCategory.hom
    ((∐ fun _ : gs.I => (SheafOfModules.unit (R.over V)).val.presheaf).map hs.op)) a₀ with ha₁
  have key : (ConcreteCategory.hom (comb.app (op W'sl))) a₁
      = (F.val.presheaf.map (homOfLE hV'U).op) t := by
    rw [ha₁]
    have hnat := comb.naturality hs.op
    have happ := congrArg (fun m ↦ (ConcreteCategory.hom m) a₀) hnat
    simp only [ConcreteCategory.comp_apply] at happ
    rw [happ, ha₀]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl
  obtain ⟨a, hae⟩ := combApp_decode V gs s hsdef ψ hgen W' (le_trans hV'U hUV) a₁
  refine ⟨a, ?_⟩
  rw [← key, hcomb, hη]
  exact hae

set_option maxHeartbeats 1000000 in
-- this proof's elaboration needs more than the default heartbeat budget
set_option synthInstance.maxHeartbeats 400000 in
/-- The components over `V` of finitely many generating sections of `F.over V` locally generate
`F` over `V`. -/
theorem localLinComb_of_generatingSections {F : SheafOfModules.{u} R}
    (V : TopologicalSpace.Opens X) (gs : (F.over V).GeneratingSections)
    [Fintype gs.I] :
    LocalLinComb V (fun j => (gs.s j).val (op (Over.mk (𝟙 V)))) := by
  set s := (fun j ↦ (gs.s j).val (op (Over.mk (𝟙 V)))) with hsdef
  set ψ : SheafOfModules.free gs.I ⟶ (F.over V) := (F.over V).freeHomEquiv.symm gs.s with hψ
  have hgen : ∀ i, SheafOfModules.ιFree i ≫ ψ
      = (F.over V).unitHomEquiv.symm (gs.s i) := by
    intro i
    show (SheafOfModules.freeCofan gs.I).inj i ≫ _ = _
    rw [hψ, SheafOfModules.freeHomEquiv]
    exact (SheafOfModules.isColimitFreeCofan gs.I).fac _ ⟨i⟩
  intro U hUV t y hyU
  exact localLinComb_of_combSurj V gs s hsdef ψ hψ hgen U hUV t y hyU

set_option maxHeartbeats 1000000 in
-- this proof's elaboration needs more than the default heartbeat budget
set_option synthInstance.maxHeartbeats 400000 in
/-- If `F` is of finite type, then there are an open `V ∋ x`, a finite index type `J₀`, and
sections `s : J₀ → F(V)` such that every section of `F` over an open `U ≤ V` is locally an
`O`-linear combination of the `s j`. -/
theorem exists_local_generators {F : SheafOfModules.{u} R}
    (hF : SheafOfModules.IsFiniteType.{u, u, u} F) (x : X) :
    ∃ (V : TopologicalSpace.Opens X) (_ : x ∈ V) (J₀ : Type u) (_ : Fintype J₀)
      (s : J₀ → F.val.presheaf.obj (op V)), LocalLinComb V s := by
  obtain ⟨σ, hσ⟩ := hF.exists_localGeneratorsData
  obtain ⟨U, f, ⟨i, ⟨g⟩⟩, hxU⟩ := σ.coversTop ⊤ x (by trivial)
  set V := σ.X i with hV
  have hxi : x ∈ V := (leOfHom g) hxU
  set gs := σ.generators i with hgs
  have hJ : Finite gs.I := (hσ.isFiniteType i).finite
  let : Fintype gs.I := Fintype.ofFinite _
  exact ⟨V, hxi, gs.I, inferInstance,
    (fun j ↦ (gs.s j).val (op (Over.mk (𝟙 V)))),
    localLinComb_of_generatingSections V gs⟩

set_option maxHeartbeats 4000000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- If `φ` is surjective on the stalk at `x`, then for every section `sj` of `F` over an open
`V ∋ x` there are an open `W ∋ x` with `W ≤ V` and a section `tj` of `G` over `W` whose image is
`sj|_W`. -/
theorem exists_lift_single {F G : SheafOfModules.{u} R} (φ : G ⟶ F) (x : X)
    (hx : SurjOnStalk φ x)
    {V : TopologicalSpace.Opens X} (hxV : x ∈ V)
    (sj : F.val.presheaf.obj (op V)) :
    ∃ (W : TopologicalSpace.Opens X) (hWV : W ≤ V) (_ : x ∈ W)
      (tj : G.val.presheaf.obj (op W)),
      (ConcreteCategory.hom ((underlyingAb φ).app (op W))) tj
            = (F.val.presheaf.map (homOfLE hWV).op) sj := by
  set germ_sj := (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf V x hxV)) sj with hgsj
  obtain ⟨gj, hgj⟩ := hx germ_sj
  obtain ⟨Wj, hxWj, tj0, htj0⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf gj
  have hgerm : (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf Wj x hxWj))
        ((ConcreteCategory.hom ((underlyingAb φ).app (op Wj))) tj0) = germ_sj := by
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply, htj0, hgj]
  rw [hgsj] at hgerm
  obtain ⟨W, hxW, iU, iV, hagree⟩ := TopCat.Presheaf.germ_eq F.val.presheaf x hxWj hxV
    ((ConcreteCategory.hom ((underlyingAb φ).app (op Wj))) tj0) sj hgerm
  refine ⟨W, leOfHom iV, hxW, (ConcreteCategory.hom (G.val.presheaf.map iU.op)) tj0, ?_⟩
  rw [show (homOfLE (leOfHom iV)) = iV from rfl, ← hagree, ← ConcreteCategory.comp_apply,
    (underlyingAb φ).naturality iU.op, ConcreteCategory.comp_apply]

set_option maxHeartbeats 4000000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- If the image of `tj` is `sj|_{W₀}`, then the image of `tj|_W` is `sj|_W` for `W ≤ W₀`. -/
theorem lift_restrict {F G : SheafOfModules.{u} R} (φ : G ⟶ F)
    {V W₀ W : TopologicalSpace.Opens X} (hW₀V : W₀ ≤ V) (hWW₀ : W ≤ W₀) (hWV : W ≤ V)
    (sj : F.val.presheaf.obj (op V)) (tj : G.val.presheaf.obj (op W₀))
    (h : (ConcreteCategory.hom ((underlyingAb φ).app (op W₀))) tj
            = (F.val.presheaf.map (homOfLE hW₀V).op) sj) :
    (ConcreteCategory.hom ((underlyingAb φ).app (op W)))
        ((ConcreteCategory.hom (G.val.presheaf.map (homOfLE hWW₀).op)) tj)
      = (F.val.presheaf.map (homOfLE hWV).op) sj := by
  rw [← ConcreteCategory.comp_apply, (underlyingAb φ).naturality (homOfLE hWW₀).op,
      ConcreteCategory.comp_apply, h,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

set_option maxHeartbeats 4000000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- If `φ` is surjective on the stalk at `x`, then for sections `s : J₀ → F(V)` over an open
`V ∋ x` and a finite set `S` of indices there are an open `W ∋ x` with `W ≤ V` and sections
`t : J₀ → G(W)` whose images are the `(s j)|_W` for all `j ∈ S`. -/
theorem exists_lifts_finset {F G : SheafOfModules.{u} R} (φ : G ⟶ F) (x : X)
    (hx : SurjOnStalk φ x)
    {J₀ : Type v} {V : TopologicalSpace.Opens X} (hxV : x ∈ V)
    (s : J₀ → F.val.presheaf.obj (op V)) (S : Finset J₀) :
    ∃ (W : TopologicalSpace.Opens X) (hWV : W ≤ V) (_ : x ∈ W)
      (t : J₀ → G.val.presheaf.obj (op W)),
      ∀ j ∈ S, (ConcreteCategory.hom ((underlyingAb φ).app (op W))) (t j)
            = (F.val.presheaf.map (homOfLE hWV).op) (s j) := by
  classical
  induction S using Finset.induction with
  | empty =>
    exact ⟨V, le_refl V, hxV, fun _ ↦ 0, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨W₀, hW₀V, hxW₀, t₀, ht₀⟩ := ih
    obtain ⟨Wa, hWaV, hxWa, ta, hta⟩ := exists_lift_single φ x hx hxV (s a)
    refine ⟨W₀ ⊓ Wa, le_trans inf_le_left hW₀V, ⟨hxW₀, hxWa⟩,
      fun j ↦ if j = a then
        (ConcreteCategory.hom (G.val.presheaf.map (homOfLE (inf_le_right : W₀ ⊓ Wa ≤ Wa)).op)) ta
      else
        (ConcreteCategory.hom (G.val.presheaf.map (homOfLE (inf_le_left : W₀ ⊓ Wa ≤ W₀)).op)) (t₀
            j),
      ?_⟩
    intro j hj
    by_cases hja : j = a
    · subst hja
      simp only [↓reduceIte]
      exact lift_restrict φ hWaV inf_le_right (le_trans inf_le_left hW₀V) (s j) ta hta
    · simp only [ite_eq_right hja]
      exact lift_restrict φ hW₀V inf_le_left (le_trans inf_le_left hW₀V) (s j) (t₀ j)
        (ht₀ j ((Finset.mem_insert.mp hj).resolve_left hja))

/-- If `φ` is surjective on the stalk at `x`, then for finitely many sections `s : J₀ → F(V)` over
an open `V ∋ x` there are an open `W ∋ x` with `W ≤ V` and sections `t : J₀ → G(W)` with
`φ(t j) = (s j)|_W` for every `j`. -/
theorem exists_lifts {F G : SheafOfModules.{u} R} (φ : G ⟶ F) (x : X)
    (hx : SurjOnStalk φ x)
    {J₀ : Type v} [Finite J₀] {V : TopologicalSpace.Opens X} (hxV : x ∈ V)
    (s : J₀ → F.val.presheaf.obj (op V)) :
    ∃ (W : TopologicalSpace.Opens X) (hWV : W ≤ V) (_ : x ∈ W)
      (t : J₀ → G.val.presheaf.obj (op W)),
      ∀ j, (ConcreteCategory.hom ((underlyingAb φ).app (op W))) (t j)
            = (F.val.presheaf.map (homOfLE hWV).op) (s j) := by
  let := Fintype.ofFinite J₀
  obtain ⟨W, hWV, hxW, t, ht⟩ := exists_lifts_finset φ x hx hxV s Finset.univ
  exact ⟨W, hWV, hxW, t, fun j ↦ ht j (Finset.mem_univ j)⟩

/-- If the sections `s` over `V` locally generate `F` over `V` and their restrictions to `W ≤ V`
are the images of sections `t` of `G` over `W`, then `φ` is locally surjective at the points of
`W`. -/
theorem locallySurjOn_of_data {F G : SheafOfModules.{u} R} (φ : G ⟶ F)
    {J₀ : Type v} [Fintype J₀] {V W : TopologicalSpace.Opens X} (hWV : W ≤ V)
    (s : J₀ → F.val.presheaf.obj (op V)) (hs : LocalLinComb V s)
    (t : J₀ → G.val.presheaf.obj (op W))
    (ht : ∀ j, (ConcreteCategory.hom ((underlyingAb φ).app (op W))) (t j)
            = (F.val.presheaf.map (homOfLE hWV).op) (s j)) :
    LocallySurjOn φ W := by
  intro U r y hyU hyW
  set U' : TopologicalSpace.Opens X := U ⊓ W with hU'def
  have hU'U : U' ≤ U := inf_le_left
  have hU'W : U' ≤ W := inf_le_right
  have hU'V : U' ≤ V := le_trans hU'W hWV
  have hyU' : y ∈ U' := ⟨hyU, hyW⟩
  set rU' : F.val.presheaf.obj (op U') :=
    (F.val.presheaf.map (homOfLE hU'U).op) r with hrU'def
  obtain ⟨V', hV'U', hyV', a, ha⟩ := hs U' hU'V rU' y hyU'
  have hV'U : V' ≤ U := le_trans hV'U' hU'U
  have hV'W : V' ≤ W := le_trans hV'U' hU'W
  set g : G.val.presheaf.obj (op V') :=
    ∑ j, (a j • ((G.val.presheaf.map (homOfLE hV'W).op) (t j) :
        G.val.obj (op V')) : G.val.obj (op V')) with hgdef
  refine ⟨V', hV'U, ⟨g, ?_⟩, hyV'⟩
  set ψ := (SheafOfModules.forget R).map φ with hψdef
  have key : ∀ (z : G.val.presheaf.obj (op V')),
      (ConcreteCategory.hom ((underlyingAb φ).app (op V'))) z
        = (ConcreteCategory.hom (ψ.app (op V'))) z := fun _ ↦ rfl
  rw [key g, hgdef, map_sum]
  simp only [map_smul]
  have hterm := fun x ↦ lift_restrict φ hWV hV'W (le_trans hV'W hWV) (s x) (t x) (ht x)
  simp only [key] at hterm
  simp only [hterm]
  rw [← ha, hrU'def, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- If `F` is of finite type and `φ` is surjective on the stalk at `x`, then `φ` is locally
surjective at the points of some open neighbourhood of `x`. -/
theorem exists_nbhd_locallySurjOn {F G : SheafOfModules.{u} R} (φ : G ⟶ F)
    (hF : SheafOfModules.IsFiniteType.{u, u, u} F) (x : X)
    (hx : SurjOnStalk φ x) :
    ∃ W : TopologicalSpace.Opens X, x ∈ W ∧ LocallySurjOn φ W := by
  obtain ⟨V, hxV, J₀, _, s, hs⟩ := exists_local_generators hF x
  obtain ⟨W, hWV, hxW, t, ht⟩ := exists_lifts φ x hx hxV s
  exact ⟨W, hxW, locallySurjOn_of_data φ hWV s hs t ht⟩

/-- Let `(X, O_X)` be a ringed space and `φ : G ⟶ F` a homomorphism of `O_X`-modules. Suppose `F`
is of finite type and the induced map on stalks at `x` is surjective. Then there is an open
neighbourhood `U` of `x` over which `φ` is surjective, i.e. for every `y ∈ U` the induced map on
the stalk at `y` is surjective. -/
@[stacks 01B8, ega "0 5.2.2" "generating sections"]
theorem main_theorem
    {F G : SheafOfModules.{u} R} (φ : G ⟶ F)
    (hF : SheafOfModules.IsFiniteType.{u, u, u} F) (x : X)
    (hx : SurjOnStalk φ x) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧ ∀ y ∈ U, SurjOnStalk φ y := by
  obtain ⟨W, hxW, hW⟩ := exists_nbhd_locallySurjOn φ hF x hx
  exact ⟨W, hxW, fun y hy ↦ surjOnStalk_of_locallySurjOn φ hW hy⟩

end Stacks.SheafOfModules.LocallySurjective
