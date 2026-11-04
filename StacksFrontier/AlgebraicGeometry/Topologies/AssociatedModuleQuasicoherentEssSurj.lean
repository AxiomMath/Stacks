module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleGlueTransitions
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.GaloisDescentEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherent modules on a site of schemes

Let `S` be a scheme and let a site `C` of schemes over `S` satisfy the conditions of Tag 03OJ.
This file proves the tag: the presheaf `𝒪` is a sheaf, and every quasi-coherent `𝒪`-module `M`
on the site is isomorphic to `Fᵃ` for a quasi-coherent `𝒪_S`-module `F`
(`Stacks.Sites.isSheaf_structurePresheaf_and_exists_iso_siteAssociatedModule`).

## Main results

* `Stacks.Sites.testPullbacks`: the fibre products of the site along a covering of the final
  object, as test objects for the descent datum.
* `Stacks.Sites.sieve_ofArrows_mem_fpqcTopology`: the structure morphisms of the members of a
  covering of the final object generate an fpqc covering sieve of `S`.
* `Stacks.Sites.nonempty_iso_of_glueDatum`: an effectivity witness `N` of the descent datum
  `Stacks.Sites.glueDatum` has `Nᵃ ≅ M`.
* `Stacks.Sites.exists_iso_siteAssociatedModule_of_preservesCoveringFibreProducts`: the second
  assertion of Tag 03OJ, with the final object of condition (3) given as an object with
  invertible structure morphism.
* `Stacks.Sites.isSheaf_structurePresheaf_and_exists_iso_siteAssociatedModule`: **Tag 03OJ**, both
  assertions, with condition (3) in the source's form.

## Implementation notes

**The site.**  A site in the sense of Stacks 00VH is rendered as a precoverage `K` on `C` with
`CategoryTheory.Precoverage.HasIsos` and `…IsStableUnderComposition` (axioms (1) and (2)) and
`…HasPullbacks` with `…IsStableUnderBaseChange` (axiom (3): the fibre products `Uᵢ ×_U V` of a
covering exist in `C` and form a covering).  `C` is not assumed to have any other fibre products.
Condition (1) of the tag, that `C` is a full subcategory of `Sch/S`, is a fully faithful functor
`toOver : C ⥤ Over S`, together with `CategoryTheory.EssentiallySmall`, which renders the
set-theoretic smallness that Stacks imposes on every site (Sites, Remark 00VI): the category of a
site is required to be a set.

**The fibre products.**  The fibre products of the site along covering arrows are assumed to be
fibre products of schemes
(`Stacks.Sites.PreservesCoveringFibreProducts K (toOver ⋙ Over.forget S)`), as they are on every
site of the Topologies chapter, whose underlying categories are closed under fibre products in
`Sch/S`.  Without this assumption `𝒪` need not be a sheaf
(`Stacks.Sites.not_forall_isSheaf_structurePresheaf`).

## References

* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 00VH](https://stacks.math.columbia.edu/tag/00VH)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites

open _root_.AlgebraicGeometry

attribute [local instance] CategoryTheory.hasWeakSheafify_addCommGrpCat_of_essentiallySmall
  CategoryTheory.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall
  CategoryTheory.hasSheafify_addCommGrpCat_of_essentiallySmall

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)
  [toOver.Full] [toOver.Faithful] (e : C) [IsIso (toOver.obj e).hom]

/-! ### The fibre products of the site as test objects -/

omit [toOver.Full] [toOver.Faithful] in
/-- **A pullback of schemes over the underlying scheme of the final object is a pullback over
`S`**, the structure morphism of the final object being invertible. -/
public theorem isPullback_left_of_isPullback {P X Y : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ e}
    {g : Y ⟶ e}
    (h : IsPullback ((toOver ⋙ Over.forget S).map fst) ((toOver ⋙ Over.forget S).map snd)
      ((toOver ⋙ Over.forget S).map f) ((toOver ⋙ Over.forget S).map g)) :
    IsPullback (toOver.map fst).left (toOver.map snd).left (toOver.obj X).hom (toOver.obj Y).hom :=
  h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (asIso (toOver.obj e).hom) ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Over.w (toOver.map f)).trans (Category.id_comp _).symm)
    ((Over.w (toOver.map g)).trans (Category.id_comp _).symm)

section TestPullbacks

variable (K : Precoverage C) [K.HasPullbacks] [K.IsStableUnderBaseChange] {ι : Type*}
  {V : ι → C} (π : ∀ i, V i ⟶ e) (hV : Presieve.ofArrows V π ∈ K e)

include hV in
omit [K.IsStableUnderBaseChange] in
/-- Two members of a covering family have a fibre product in the site (Stacks 00VH (3)). -/
public theorem hasPullback_ofArrows (i j : ι) : HasPullback (π i) (π j) :=
  have := K.hasPullbacks_of_mem (π j) hV
  Presieve.hasPullback (π j) (Presieve.ofArrows.mk i)

/-- The fibre product of two members of a covering family. -/
public noncomputable abbrev pair (i j : ι) : C :=
  @pullback _ _ _ _ _ (π i) (π j) (hasPullback_ofArrows e K π hV i j)

/-- The first projection of the fibre product of two members. -/
public noncomputable abbrev pairFst (i j : ι) : pair e K π hV i j ⟶ V i :=
  @pullback.fst _ _ _ _ _ (π i) (π j) (hasPullback_ofArrows e K π hV i j)

/-- The second projection of the fibre product of two members. -/
public noncomputable abbrev pairSnd (i j : ι) : pair e K π hV i j ⟶ V j :=
  @pullback.snd _ _ _ _ _ (π i) (π j) (hasPullback_ofArrows e K π hV i j)

omit [K.IsStableUnderBaseChange] in
/-- The fibre product of two members is a pullback square. -/
public theorem isPullback_pair (i j : ι) :
    IsPullback (pairFst e K π hV i j) (pairSnd e K π hV i j) (π i) (π j) :=
  @IsPullback.of_hasPullback _ _ _ _ _ (π i) (π j) (hasPullback_ofArrows e K π hV i j)

/-- The second projections to a fixed member form a covering family of it: the base change of the
covering family along that member (Stacks 00VH (3)). -/
public theorem pairSnd_mem (j : ι) :
    Presieve.ofArrows (fun i => pair e K π hV i j) (fun i => pairSnd e K π hV i j) ∈ K (V j) :=
  Precoverage.mem_coverings_of_isPullback π hV (π j) (fun i => pairSnd e K π hV i j)
    (fun i => pairFst e K π hV i j) (fun _ => (isPullback_pair e K π hV _ j).flip)

/-- The fibre product of three members has a fibre product in the site, along the second
projection of the first two, which is a covering arrow. -/
public theorem hasPullback_triple (i j k : ι) :
    HasPullback (pairSnd e K π hV i j) (pairFst e K π hV j k) :=
  have := K.hasPullbacks_of_mem (pairFst e K π hV j k) (pairSnd_mem e K π hV j)
  Presieve.hasPullback (pairFst e K π hV j k)
    (Presieve.ofArrows.mk i : Presieve.ofArrows (fun i => pair e K π hV i j)
      (fun i => pairSnd e K π hV i j) (pairSnd e K π hV i j))

variable (hpres : PreservesCoveringFibreProducts K (toOver ⋙ Over.forget S))

/-- **The fibre products of two and of three members of a covering family of the final object**,
formed in the site, read as test objects: they are fibre products along covering arrows, which
the canonical functor to schemes preserves, and the final object lies over `S` by an
isomorphism. -/
public noncomputable def testPullbacks :
    Stacks.Descent.TestPullbacks (fun T : C => (toOver.obj T).left)
      (fun T => (toOver.obj T).hom) V where
  P i j := pair e K π hV i j
  p₁ i j := (toOver.map (pairFst e K π hV i j)).left
  p₂ i j := (toOver.map (pairSnd e K π hV i j)).left
  isPullback i j := isPullback_left_of_isPullback S toOver e
    (hpres _ hV (Presieve.ofArrows.mk i) (π j) _ _ (isPullback_pair e K π hV i j))
  p₁_q i j := Over.w (toOver.map (pairFst e K π hV i j))
  P₃ i j k := @pullback _ _ _ _ _ (pairSnd e K π hV i j) (pairFst e K π hV j k)
    (hasPullback_triple e K π hV i j k)
  r₁₂ i j k := (toOver.map (@pullback.fst _ _ _ _ _ (pairSnd e K π hV i j)
    (pairFst e K π hV j k) (hasPullback_triple e K π hV i j k))).left
  r₂₃ i j k := (toOver.map (@pullback.snd _ _ _ _ _ (pairSnd e K π hV i j)
    (pairFst e K π hV j k) (hasPullback_triple e K π hV i j k))).left
  isPullback₃ i j k := hpres _ (pairSnd_mem e K π hV j) (Presieve.ofArrows.mk i)
    (pairFst e K π hV j k) _ _
    (@IsPullback.of_hasPullback _ _ _ _ _ (pairSnd e K π hV i j) (pairFst e K π hV j k)
      (hasPullback_triple e K π hV i j k))
  r₁₂_q i j k := Over.w (toOver.map (@pullback.fst _ _ _ _ _ (pairSnd e K π hV i j)
    (pairFst e K π hV j k) (hasPullback_triple e K π hV i j k)))

end TestPullbacks

/-! ### Effectivity -/

/-- **A quasi-coherent descent datum for a family generating an fpqc covering sieve is
effective.** -/
public theorem isEffective_of_sieve_mem {I : Type*} {S' : Scheme.{u}} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ S'} (hf : Sieve.ofArrows X f ∈ Scheme.fpqcTopology.{u} S')
    (D : QuasicoherentDescentData f) : D.IsEffective := by
  have := Stacks.Descent.qcohPseudofunctor.isEquivalence_toDescentData f hf
  obtain ⟨M, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage
    (F := Stacks.Descent.qcohPseudofunctor.toDescentData f) (Stacks.Descent.descentDataLift D)
  exact ⟨M, ⟨eqToIso (Stacks.Descent.descentDataForgetFunctor_obj_toDescentData M).symm ≪≫
    Stacks.Descent.descentDataForgetFunctor.mapIso i ≪≫
      eqToIso (Stacks.Descent.descentDataForgetFunctor_obj_descentDataLift D)⟩⟩

variable (K : Precoverage C)
  (hfpqc : ∀ (T : C) (Q : Presieve T), Q ∈ K T →
    Presieve.map (toOver ⋙ Over.forget S) Q ∈
      Scheme.fpqcPrecoverage.{u} ((toOver.obj T).left))

omit [toOver.Full] [toOver.Faithful] in
include hfpqc in
/-- **The structure morphisms of the members of a covering family of the final object generate an
fpqc covering sieve of `S`.** -/
public theorem sieve_ofArrows_mem_fpqcTopology {ι : Type*} {V : ι → C} (π : ∀ i, V i ⟶ e)
    (hV : Presieve.ofArrows V π ∈ K e) :
    Sieve.ofArrows (fun i => (toOver.obj (V i)).left) (fun i => (toOver.obj (V i)).hom) ∈
      Scheme.fpqcTopology.{u} S := by
  have h1 := Precoverage.generate_mem_toGrothendieck (hfpqc e _ hV)
  rw [Presieve.map_ofArrows] at h1
  refine Scheme.fpqcTopology.superset_covering ?_
    (Scheme.fpqcTopology.pullback_stable (inv (toOver.obj e).hom) h1)
  rintro Z h ⟨Y, g, m, ⟨i⟩, hm⟩
  refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨i, g, ?_⟩
  have hm' : h = g ≫ (toOver.map (π i)).left ≫ (toOver.obj e).hom := by
    have hm'' : h ≫ inv (toOver.obj e).hom = g ≫ (toOver.map (π i)).left := hm.symm
    rw [← Category.assoc, ← hm'', Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hm', Over.w (toOver.map (π i))]

include S toOver in
/-- The members of a covering family of the final object cover the final object of the topos. -/
public theorem coversTop_of_mem {ι : Type*} {V : ι → C} (π : ∀ i, V i ⟶ e)
    (hV : Presieve.ofArrows V π ∈ K e) : K.toGrothendieck.CoversTop V := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ e (isTerminalOfIsIsoHom S toOver e)]
  refine K.toGrothendieck.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck hV)
  rintro Y f ⟨Z, g, _, ⟨i⟩, -⟩
  exact ⟨i, ⟨g⟩⟩

/-! ### The descent datum -/

section Descent

variable [EssentiallySmall.{u} C] [K.HasPullbacks] [K.IsStableUnderBaseChange]
  (hSh : ∀ (X : C) (F : ((toOver.obj X).left).Modules) (_ : F.IsQuasicoherent),
    Presheaf.IsSheaf (K.toGrothendieck.over X)
      (associatedPresheaf ((toOver.obj X).left) F (sliceToOver S toOver X)))
  (hR : Presheaf.IsSheaf K.toGrothendieck (structurePresheaf S toOver))
  (M : SheafOfModules.{u} (siteStructureSheaf S toOver K.toGrothendieck hR))
  {ι : Type*} {V : ι → C} (dd : ∀ i, SliceCokernelDatum S toOver K hSh hR M (V i))
  (Q : Stacks.Descent.TestPullbacks (fun T : C => (toOver.obj T).left)
    (fun T => (toOver.obj T).hom) V)
  (Θ : Stacks.Descent.TestTransitions modulePullbackPseudofunctor
    (fun T : C => (toOver.obj T).left) (fun T => (toOver.obj T).hom) V (fun i => (dd i).F))
  (hΘ : ∀ (T : C) ⦃i j : ι⦄ (α : (toOver.obj T).left ⟶ (toOver.obj (V i)).left)
    (β : (toOver.obj T).left ⟶ (toOver.obj (V j)).left)
    (hα : α ≫ (toOver.obj (V i)).hom = (toOver.obj T).hom)
    (hβ : β ≫ (toOver.obj (V j)).hom = (toOver.obj T).hom),
    SliceCokernelDatum.Good (dd i) (dd j) α β (Θ.τ T α β hα hβ))

/-- **The quasi-coherent descent datum of Tag 03OJ**, for the family of structure morphisms of the
members of a family `V`: the local cokernels, with transitions `Θ` over the objects of the site,
read on the fibre products `Q`. -/
public noncomputable def glueDatum :
    QuasicoherentDescentData (fun i => (toOver.obj (V i)).hom) :=
  ⟨(Θ.descentData' Q).descentData, fun i => (inferInstance : ((dd i).F).IsQuasicoherent)⟩

omit [toOver.Full] [toOver.Faithful] [EssentiallySmall.{u} C] [K.HasPullbacks]
  [K.IsStableUnderBaseChange] in
/-- The components of `Stacks.Sites.glueDatum` are the local cokernels. -/
public theorem glueDatum_obj (i : ι) :
    (glueDatum S toOver K hSh hR M dd Q Θ).obj.obj i = (dd i).F :=
  rfl

include hΘ in
omit [toOver.Full] [toOver.Faithful] [EssentiallySmall.{u} C] [K.HasPullbacks]
  [K.IsStableUnderBaseChange] in
/-- **The transitions of `Stacks.Sites.glueDatum` over an object of the site are good.** -/
public theorem good_glueDatum_hom (T : C) {i j : ι}
    (α : (toOver.obj T).left ⟶ (toOver.obj (V i)).left)
    (β : (toOver.obj T).left ⟶ (toOver.obj (V j)).left)
    (hα : α ≫ (toOver.obj (V i)).hom = (toOver.obj T).hom)
    (hβ : β ≫ (toOver.obj (V j)).hom = (toOver.obj T).hom) :
    SliceCokernelDatum.Good (dd i) (dd j) α β
      ((glueDatum S toOver K hSh hR M dd Q Θ).obj.hom (toOver.obj T).hom α β hα hβ) :=
  (congrArg (SliceCokernelDatum.Good (dd i) (dd j) α β) (Θ.descentData_hom Q T α β hα hβ)).mpr
    (hΘ T α β hα hβ)

/-- The comparison `pullbackCompHom` undone on global sections. -/
public theorem pullbackCompHom_app_top_inv {Z Z' Z'' : Scheme.{u}} (c : Z'' ⟶ Z') (h : Z' ⟶ Z)
    (k : Z'' ⟶ Z) (hk : c ≫ h = k) (A : Z.Modules) (x : Γ((Scheme.Modules.pullback k).obj A, ⊤)) :
    (Stacks.Descent.pullbackCompHom c h k hk A).app ⊤
      (((Scheme.Modules.pullbackComp c h).inv.app A).app ⊤
        (((Scheme.Modules.pullbackCongr hk).inv.app A).app ⊤ x)) = x := by
  simp only [Stacks.Descent.pullbackCompHom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [natIso_app_top_inv_hom, natIso_app_top_inv_hom]

/-- A section is recovered from its image under `pullbackCompHom`. -/
public theorem eq_of_pullbackCompHom_app_top {Z Z' Z'' : Scheme.{u}} (c : Z'' ⟶ Z') (h : Z' ⟶ Z)
    (k : Z'' ⟶ Z) (hk : c ≫ h = k) (A : Z.Modules)
    (z : Γ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback h).obj A), ⊤)) :
    z = ((Scheme.Modules.pullbackComp c h).inv.app A).app ⊤
      (((Scheme.Modules.pullbackCongr hk).inv.app A).app ⊤
        ((Stacks.Descent.pullbackCompHom c h k hk A).app ⊤ z)) := by
  simp only [Stacks.Descent.pullbackCompHom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [natIso_app_top_hom_inv, natIso_app_top_hom_inv]

/-- The canonical quasi-coherent descent datum of a quasi-coherent module `N`, the pullbacks of
`N` with their canonical transitions, spelled through
`CategoryTheory.Pseudofunctor.DescentData.ofObj`.  It is the image of `N` under
`AlgebraicGeometry.canonicalDescentFunctor` on the nose. -/
@[sga "4½ Arcata 1.4.4"]
public noncomputable abbrev ofObjQcoh {I : Type*} {S' : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S') (N : (SheafOfModules.isQuasicoherent S'.ringCatSheaf).FullSubcategory) :
    QuasicoherentDescentData f :=
  ⟨Pseudofunctor.DescentData.ofObj (F := modulePullbackPseudofunctor) (f := f) N.obj,
    fun i => Stacks.Modules.isQuasicoherent_pullback (f i) N.obj N.property⟩

/-- **The compatibility square of a morphism of descent data out of the canonical datum of a
module, in the categories of modules.** -/
public theorem ofObjQcoh_hom_comm_pullback {I : Type*} {S' : Scheme.{u}} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ S'} {N : (SheafOfModules.isQuasicoherent S'.ringCatSheaf).FullSubcategory}
    {D : modulePullbackPseudofunctor.DescentData f} (φ : (ofObjQcoh f N).obj ⟶ D)
    {Y : Scheme.{u}} (q : Y ⟶ S') {i₁ i₂ : I} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (Scheme.Modules.pullback f₁).map (φ.hom i₁) ≫ D.hom q f₁ f₂ hf₁ hf₂ =
      (ofObjQcoh f N).obj.hom q f₁ f₂ hf₁ hf₂ ≫ (Scheme.Modules.pullback f₂).map (φ.hom i₂) :=
  φ.comm q f₁ f₂ hf₁ hf₂

/-- The transitions of `Stacks.Sites.ofObjQcoh` are those of
`CategoryTheory.Pseudofunctor.DescentData.ofObj`. -/
public theorem ofObjQcoh_obj_hom {I : Type*} {S' : Scheme.{u}} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ S'} (N : (SheafOfModules.isQuasicoherent S'.ringCatSheaf).FullSubcategory)
    {Y : Scheme.{u}} (q : Y ⟶ S') {i₁ i₂ : I} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (h₁ : f₁ ≫ f i₁ = q) (h₂ : f₂ ≫ f i₂ = q) :
    (ofObjQcoh f N).obj.hom q f₁ f₂ h₁ h₂ =
      (Pseudofunctor.DescentData.ofObj (F := modulePullbackPseudofunctor) (f := f) N.obj).hom
        q f₁ f₂ h₁ h₂ :=
  rfl

/-- **The transition of the canonical descent datum of a module, followed by the comparison
`Stacks.Descent.pullbackCompHom` at the second member, is the comparison at the first member.** -/
public theorem ofObjQcoh_hom_comp_pullbackCompHom {I : Type*} {S' : Scheme.{u}}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S'}
    (N : (SheafOfModules.isQuasicoherent S'.ringCatSheaf).FullSubcategory) {Y : Scheme.{u}}
    (q : Y ⟶ S') {i₁ i₂ : I} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (h₁ : f₁ ≫ f i₁ = q)
    (h₂ : f₂ ≫ f i₂ = q) :
    (ofObjQcoh f N).obj.hom q f₁ f₂ h₁ h₂ ≫ Stacks.Descent.pullbackCompHom f₂ (f i₂) q h₂ N.obj =
      Stacks.Descent.pullbackCompHom f₁ (f i₁) q h₁ N.obj :=
  (congrArg (· ≫ Stacks.Descent.pullbackCompHom f₂ (f i₂) q h₂ N.obj)
    (ofObjQcoh_obj_hom N q f₁ f₂ h₁ h₂)).trans
    (Stacks.Descent.ofObj_hom_comp_pullbackCompHom N.obj q f₁ f₂ h₁ h₂)

omit [toOver.Full] [toOver.Faithful] [EssentiallySmall.{u} C] [K.HasPullbacks]
  [K.IsStableUnderBaseChange] in
/-- **The agreement of the local identifications on overlaps, at abstract data.** -/
public theorem θ_agree_of_square {X Y T : C} {d : SliceCokernelDatum S toOver K hSh hR M X}
    {d' : SliceCokernelDatum S toOver K hSh hR M Y} {a : T ⟶ X} {b : T ⟶ Y} {G : S.Modules}
    (ζ₁ : (Scheme.Modules.pullback (toOver.obj X).hom).obj G ⟶ d.F)
    (ζ₂ : (Scheme.Modules.pullback (toOver.obj Y).hom).obj G ⟶ d'.F)
    (D : (Scheme.Modules.pullback (toOver.map a).left).obj d.F ⟶
      (Scheme.Modules.pullback (toOver.map b).left).obj d'.F)
    (hD : SliceCokernelDatum.Good d d' (toOver.map a).left (toOver.map b).left D)
    (c : (Scheme.Modules.pullback (toOver.map a).left).obj
        ((Scheme.Modules.pullback (toOver.obj X).hom).obj G) ⟶
      (Scheme.Modules.pullback (toOver.map b).left).obj
        ((Scheme.Modules.pullback (toOver.obj Y).hom).obj G))
    (h₀ : (Scheme.Modules.pullback (toOver.map a).left).map ζ₁ ≫ D =
      c ≫ (Scheme.Modules.pullback (toOver.map b).left).map ζ₂)
    (hc : c ≫ Stacks.Descent.pullbackCompHom (toOver.map b).left (toOver.obj Y).hom
        (toOver.obj T).hom (Over.w (toOver.map b)) G =
      Stacks.Descent.pullbackCompHom (toOver.map a).left (toOver.obj X).hom
        (toOver.obj T).hom (Over.w (toOver.map a)) G)
    (x : Γ((Scheme.Modules.pullback (toOver.obj T).hom).obj G, ⊤)) :
    d.θ a (((Scheme.Modules.pullback (toOver.map a).left).map ζ₁).app ⊤
        (((Scheme.Modules.pullbackComp (toOver.map a).left (toOver.obj X).hom).inv.app G).app ⊤
          (((Scheme.Modules.pullbackCongr (Over.w (toOver.map a))).inv.app G).app ⊤ x))) =
      d'.θ b (((Scheme.Modules.pullback (toOver.map b).left).map ζ₂).app ⊤
        (((Scheme.Modules.pullbackComp (toOver.map b).left (toOver.obj Y).hom).inv.app G).app ⊤
          (((Scheme.Modules.pullbackCongr (Over.w (toOver.map b))).inv.app G).app ⊤ x))) := by
  have key : ∀ {A B : (toOver.obj T).left.Modules} {φ ψ : A ⟶ B}, φ = ψ →
      ∀ y, φ.app ⊤ y = ψ.app ⊤ y := fun h y => by rw [h]
  refine (hD.apply_self _).symm.trans (congrArg (d'.θ b) ?_)
  generalize hy : ((Scheme.Modules.pullbackComp (toOver.map a).left (toOver.obj X).hom).inv.app
    G).app ⊤ (((Scheme.Modules.pullbackCongr (Over.w (toOver.map a))).inv.app G).app ⊤ x) = y
  have h₀' := key h₀ y
  have hc' := key hc y
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h₀' hc'
  refine h₀'.trans (congrArg (((Scheme.Modules.pullback (toOver.map b).left).map ζ₂).app ⊤) ?_)
  refine (eq_of_pullbackCompHom_app_top _ _ _ (Over.w (toOver.map b)) G _).trans ?_
  refine congrArg (fun z => ((Scheme.Modules.pullbackComp (toOver.map b).left
    (toOver.obj Y).hom).inv.app G).app ⊤
      (((Scheme.Modules.pullbackCongr (Over.w (toOver.map b))).inv.app G).app ⊤ z)) ?_
  exact hc'.trans (hy ▸ pullbackCompHom_app_top_inv _ _ _ _ _ x)

/-- The transport along a reversed equality of morphisms is the inverse transport. -/
public theorem pullbackCongr_symm_hom_app_top {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (A : Y.Modules) (x : Γ((Scheme.Modules.pullback g).obj A, ⊤)) :
    ((Scheme.Modules.pullbackCongr h.symm).hom.app A).app ⊤ x =
      ((Scheme.Modules.pullbackCongr h).inv.app A).app ⊤ x := by
  subst h
  rfl

/-- The associated module of an isomorphism of quasi-coherent modules, as an isomorphism. -/
public noncomputable def associatedModuleIso {S' : Scheme.{u}} {C' : Type (u + 1)} [Category.{u} C']
    (toOver' : C' ⥤ Over S') {P Q : S'.Modules} [P.IsQuasicoherent] [Q.IsQuasicoherent]
    (ι : P ≅ Q) :
    associatedModulePresheaf S' P toOver' ≅ associatedModulePresheaf S' Q toOver' where
  hom := associatedModuleMap S' toOver' ι.hom
  inv := associatedModuleMap S' toOver' ι.inv
  hom_inv_id := by rw [← associatedModuleMap_comp, ι.hom_inv_id, associatedModuleMap_id]
  inv_hom_id := by rw [← associatedModuleMap_comp, ι.inv_hom_id, associatedModuleMap_id]

/-- The restriction of a morphism of restricted presheaves of modules along `f`, on a section. -/
public theorem homRestr_app_apply {D : Type*} [Category D] (O : Dᵒᵖ ⥤ CommRingCat.{u})
    (F G : PresheafOfModules.{u} (Oforget O)) {V U : D} (f : V ⟶ U)
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) (W : Over V)
    (x : F.obj (op W.left)) :
    (homRestr O F G f α).app (op W) x = α.app (op ((Over.map f).obj W)) x := rfl

/-! ### The local isomorphisms and their agreement -/

variable {S toOver K hSh hR M dd Q Θ}

/-- The component at a member of an isomorphism of descent data, as an isomorphism. -/
public noncomputable def componentIso
    {N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    (ν : ofObjQcoh (fun i => (toOver.obj (V i)).hom) N ≅
      glueDatum S toOver K hSh hR M dd Q Θ) (i : ι) :
    (Scheme.Modules.pullback (toOver.obj (V i)).hom).obj N.obj ≅ (dd i).F where
  hom := ν.hom.hom.hom i
  inv := ν.inv.hom.hom i
  hom_inv_id := congrArg (fun φ => φ.hom.hom i) ν.hom_inv_id
  inv_hom_id := congrArg (fun φ => φ.hom.hom i) ν.inv_hom_id

omit [toOver.Full] [toOver.Faithful] [EssentiallySmall.{u} C] [K.HasPullbacks]
  [K.IsStableUnderBaseChange] in
/-- The compatibility square of the identification `ν`, over a scheme mapping to two members. -/
public theorem componentIso_comm
    {N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    (ν : ofObjQcoh (fun i => (toOver.obj (V i)).hom) N ≅ glueDatum S toOver K hSh hR M dd Q Θ)
    {Y : Scheme.{u}} (q : Y ⟶ S) {i j : ι} (α : Y ⟶ (toOver.obj (V i)).left)
    (β : Y ⟶ (toOver.obj (V j)).left) (hα : α ≫ (toOver.obj (V i)).hom = q)
    (hβ : β ≫ (toOver.obj (V j)).hom = q) :
    (Scheme.Modules.pullback α).map (componentIso ν i).hom ≫
      (glueDatum S toOver K hSh hR M dd Q Θ).obj.hom q α β hα hβ =
    (ofObjQcoh (fun i => (toOver.obj (V i)).hom) N).obj.hom q α β hα hβ ≫
      (Scheme.Modules.pullback β).map (componentIso ν j).hom :=
  ofObjQcoh_hom_comm_pullback ν.hom.hom q α β hα hβ

omit [toOver.Full] [toOver.Faithful] [EssentiallySmall.{u} C] [K.HasPullbacks]
  [K.IsStableUnderBaseChange] in
include hΘ in
/-- **The agreement of the local identifications on overlaps**, for the identification `ν` of
an effectivity witness. -/
public theorem θ_component_eq
    {N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    (ν : ofObjQcoh (fun i => (toOver.obj (V i)).hom) N ≅
      glueDatum S toOver K hSh hR M dd Q Θ) {W : C} {i j : ι} (a : W ⟶ V i)
    (b : W ⟶ V j) (x : Γ((Scheme.Modules.pullback (toOver.obj W).hom).obj N.obj, ⊤)) :
    (dd i).θ a (((Scheme.Modules.pullback (toOver.map a).left).map (componentIso ν i).hom).app ⊤
        (((Scheme.Modules.pullbackComp (toOver.map a).left (toOver.obj (V i)).hom).inv.app
          N.obj).app ⊤
          (((Scheme.Modules.pullbackCongr (Over.w (toOver.map a))).inv.app N.obj).app ⊤ x))) =
      (dd j).θ b (((Scheme.Modules.pullback (toOver.map b).left).map (componentIso ν j).hom).app ⊤
        (((Scheme.Modules.pullbackComp (toOver.map b).left (toOver.obj (V j)).hom).inv.app
          N.obj).app ⊤
          (((Scheme.Modules.pullbackCongr (Over.w (toOver.map b))).inv.app N.obj).app ⊤ x))) :=
  θ_agree_of_square S toOver K hSh hR M (componentIso ν i).hom (componentIso ν j).hom _
    (good_glueDatum_hom S toOver K hSh hR M dd Q Θ hΘ W (toOver.map a).left
      (toOver.map b).left (Over.w (toOver.map a)) (Over.w (toOver.map b)))
    _ (componentIso_comm ν (toOver.obj W).hom (toOver.map a).left (toOver.map b).left
      (Over.w (toOver.map a)) (Over.w (toOver.map b)))
    (ofObjQcoh_hom_comp_pullbackCompHom N (toOver.obj W).hom (toOver.map a).left
      (toOver.map b).left (Over.w (toOver.map a)) (Over.w (toOver.map b))) x

/-- **The local isomorphism at a member**: on the slice at `V i`, the associated module of the
glued module is the restriction of `M`.  It is the base change of the associated module to the
slice (`Stacks.Sites.sliceAssociatedModulePresheafIso`), the associated module of the component of
`ν`, and the local datum. -/
public noncomputable def localIso
    {N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    [N.obj.IsQuasicoherent] (ν : ofObjQcoh (fun i => (toOver.obj (V i)).hom) N ≅
      glueDatum S toOver K hSh hR M dd Q Θ) (i : ι) :
    (PresheafOfModules.pushforward₀ (Over.forget (V i)) (structurePresheaf S toOver)).obj
        (associatedModulePresheaf S N.obj toOver) ≅
      (sliceModuleOver S toOver (V i) K.toGrothendieck hR M).val :=
  have := Stacks.Modules.isQuasicoherent_pullback (toOver.obj (V i)).hom N.obj inferInstance
  sliceAssociatedModulePresheafIso S toOver N.obj (V i) ≪≫
    associatedModuleIso (sliceToOver S toOver (V i)) (componentIso ν i) ≪≫
    (SheafOfModules.forget _).mapIso (dd i).iso

omit [toOver.Full] [toOver.Faithful] [EssentiallySmall.{u} C] [K.HasPullbacks]
  [K.IsStableUnderBaseChange] in
/-- **The local isomorphism at a member, on a section.** -/
public theorem localIso_hom_app_apply
    {N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    [N.obj.IsQuasicoherent] (ν : ofObjQcoh (fun i => (toOver.obj (V i)).hom) N ≅
      glueDatum S toOver K hSh hR M dd Q Θ) {i : ι} (T' : Over (V i))
    (x : Γ((Scheme.Modules.pullback (toOver.obj T'.left).hom).obj N.obj, ⊤)) :
    (localIso ν i).hom.app (op T') x =
      (dd i).θ T'.hom (((Scheme.Modules.pullback (toOver.map T'.hom).left).map
          (componentIso ν i).hom).app ⊤
        (((Scheme.Modules.pullbackComp (toOver.map T'.hom).left (toOver.obj (V i)).hom).inv.app
          N.obj).app ⊤
          (((Scheme.Modules.pullbackCongr (Over.w (toOver.map T'.hom))).inv.app N.obj).app ⊤
            x))) := by
  show (dd i).θ T'.hom (((Scheme.Modules.pullback (toOver.map T'.hom).left).map
    (componentIso ν i).hom).app ⊤
    ((sliceAssociatedPresheafIso S toOver N.obj (V i)).hom.app (op T') x)) = _
  have := Stacks.Modules.isQuasicoherent_pullback (toOver.obj (V i)).hom N.obj inferInstance
  refine congrArg (fun z => (dd i).θ T'.hom
    (((Scheme.Modules.pullback (toOver.map T'.hom).left).map (componentIso ν i).hom).app ⊤ z)) ?_
  refine (sliceAssociatedPresheafIso_hom_app_apply S toOver N.obj (V i) (op T') x).trans ?_
  refine congrArg (fun z => ((Scheme.Modules.pullbackComp (toOver.map T'.hom).left
    (toOver.obj (V i)).hom).inv.app N.obj).app ⊤ z) ?_
  exact (pullbackSectionsMap_homMk_id N.obj
    ((Category.id_comp _).trans (Over.w (toOver.map T'.hom)).symm)
    (Over.w (toOver.map T'.hom)).symm x).trans
    (pullbackCongr_symm_hom_app_top _ _ x)

/-- The local isomorphism at a member, between the restrictions of the two presheaves of modules
along `CategoryTheory.Over.forget`. -/
public noncomputable def restrLocalIso
    {N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    [N.obj.IsQuasicoherent] (ν : ofObjQcoh (fun i => (toOver.obj (V i)).hom) N ≅
      glueDatum S toOver K hSh hR M dd Q Θ) (i : ι) :
    (restrFun ((toOver ⋙ Over.forget S).op ⋙ Scheme.Γ) (V i)).obj
        (associatedModulePresheaf S N.obj toOver) ≅
      (restrFun ((toOver ⋙ Over.forget S).op ⋙ Scheme.Γ) (V i)).obj M.val :=
  PresheafOfModules.isoOfPresheafIso ((PresheafOfModules.toPresheaf _).mapIso (localIso ν i))
    (fun T r m => ((localIso ν i).hom.app T).hom.map_smul r m)

omit [toOver.Full] [toOver.Faithful] [EssentiallySmall.{u} C] [K.HasPullbacks]
  [K.IsStableUnderBaseChange] in
/-- `Stacks.Sites.restrLocalIso` on a section is `Stacks.Sites.localIso`. -/
public theorem restrLocalIso_hom_app_apply
    {N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    [N.obj.IsQuasicoherent] (ν : ofObjQcoh (fun i => (toOver.obj (V i)).hom) N ≅
      glueDatum S toOver K hSh hR M dd Q Θ) {i : ι} (T' : Over (V i))
    (x : Γ((Scheme.Modules.pullback (toOver.obj T'.left).hom).obj N.obj, ⊤)) :
    (restrLocalIso ν i).hom.app (op T') x = (localIso ν i).hom.app (op T') x := rfl

omit [toOver.Full] [toOver.Faithful] [EssentiallySmall.{u} C] [K.HasPullbacks]
  [K.IsStableUnderBaseChange] in
include hΘ in
/-- **The local isomorphisms are compatible on overlaps**, as sections of the internal hom
(Stacks 03EM). -/
public theorem isCompatible_restrLocalIso
    {N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    [N.obj.IsQuasicoherent] (ν : ofObjQcoh (fun i => (toOver.obj (V i)).hom) N ≅
      glueDatum S toOver K hSh hR M dd Q Θ) :
    Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (internalHom ((toOver ⋙ Over.forget S).op ⋙ Scheme.Γ)
        (associatedModulePresheaf S N.obj toOver) M.val).presheaf ⋙ CategoryTheory.forget _)
      (fun i => (restrLocalIso ν i).hom) := by
  intro Z i j f g
  refine (internalHomForget_map_apply _ _ _ f (restrLocalIso ν i).hom).trans (Eq.trans ?_
    (internalHomForget_map_apply _ _ _ g (restrLocalIso ν j).hom).symm)
  refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨W⟩ := W
  refine (homRestr_app_apply _ _ _ f (restrLocalIso ν i).hom W x).trans ?_
  refine Eq.trans ?_ (homRestr_app_apply _ _ _ g (restrLocalIso ν j).hom W x).symm
  exact (restrLocalIso_hom_app_apply ν ((Over.map f).obj W) x).trans
    ((localIso_hom_app_apply ν ((Over.map f).obj W) x).trans
      ((θ_component_eq hΘ ν (W.hom ≫ f) (W.hom ≫ g) x).trans
        ((localIso_hom_app_apply ν ((Over.map g).obj W) x).symm.trans
          (restrLocalIso_hom_app_apply ν ((Over.map g).obj W) x).symm)))

omit [toOver.Full] [toOver.Faithful] [EssentiallySmall.{u} C] [K.HasPullbacks]
  [K.IsStableUnderBaseChange] in
include hΘ in
/-- **The gluing step of Tag 03OJ**: an effectivity witness `N` of the descent datum, with its
identification `ν`, has `Nᵃ ≅ M`. -/
public theorem nonempty_iso_of_glueDatum
    {N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    [N.obj.IsQuasicoherent] (ν : ofObjQcoh (fun i => (toOver.obj (V i)).hom) N ≅
      glueDatum S toOver K hSh hR M dd Q Θ)
    (hV : K.toGrothendieck.CoversTop V)
    (hN : Presheaf.IsSheaf K.toGrothendieck (associatedPresheaf S N.obj toOver)) :
    Nonempty (siteAssociatedModule S N.obj toOver K.toGrothendieck hR hN ≅ M) := by
  obtain ⟨ψ, -⟩ := exists_iso_of_isCompatible ((toOver ⋙ Over.forget S).op ⋙ Scheme.Γ)
    (associatedModulePresheaf S N.obj toOver) M.val hV hN
    M.isSheaf (fun i => restrLocalIso ν i) (isCompatible_restrLocalIso hΘ ν)
  exact ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso ψ⟩

end Descent

section Assertion

variable [EssentiallySmall.{u} C] [K.HasPullbacks] [K.IsStableUnderBaseChange] [K.HasIsos]
  [K.IsStableUnderComposition] (hpres : PreservesCoveringFibreProducts K (toOver ⋙ Over.forget S))
  (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
    R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
      ∃ Q : Presieve T, Q ∈ K T ∧
        Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)

include e hZariski in
/-- **The second assertion of Tag 03OJ, with the final object of condition (3) given as an
object with invertible structure morphism.**  Every quasi-coherent `𝒪`-module `M` is isomorphic to
`Fᵃ` for a quasi-coherent `𝒪_S`-module `F`. -/
public theorem exists_iso_siteAssociatedModule_of_preservesCoveringFibreProducts
    (hR : Presheaf.IsSheaf K.toGrothendieck (structurePresheaf S toOver))
    (M : SheafOfModules.{u} (siteStructureSheaf S toOver K.toGrothendieck hR))
    (hM : M.IsQuasicoherentOnSite) :
    ∃ (F : S.Modules) (_ : F.IsQuasicoherent),
      Nonempty (siteAssociatedModule S F toOver K.toGrothendieck hR
        (isSheaf_associatedPresheaf_of_preservesCoveringFibreProducts K toOver hfpqc hpres F) ≅
          M) := by
  obtain ⟨ι, V, π, hV, hloc⟩ := exists_covering_cokernel_iso_sliceModuleOver S toOver K hpres
    hfpqc hR hZariski M hM e
  choose L L' φ hiso using hloc
  let dd : ∀ i, SliceCokernelDatum S toOver K
      (fun X F hF => isSheaf_associatedPresheaf_sliceToOver S toOver K hpres hfpqc X F hF) hR M
      (V i) := fun i => ⟨L i, L' i, φ i, (hiso i).some⟩
  obtain ⟨N, ⟨ν⟩⟩ := isEffective_of_sieve_mem
    (sieve_ofArrows_mem_fpqcTopology S toOver e K hfpqc π hV)
    (glueDatum S toOver K _ hR M dd (testPullbacks S toOver e K π hV hpres)
      (SliceCokernelDatum.testTransitions hZariski V dd))
  have : N.obj.IsQuasicoherent := N.property
  exact ⟨N.obj, N.property, nonempty_iso_of_glueDatum
    (SliceCokernelDatum.good_testTransitions hZariski V dd) ν
    (coversTop_of_mem S toOver e K π hV) _⟩

include hZariski in
/-- Let a site of schemes over `S` be presented by a precoverage `K` on a category
`C` and a functor `toOver : C ⥤ Over S`, satisfying the site axioms of Stacks 00VH (isomorphisms,
composites and base changes of coverings are coverings, the base changes being fibre products in
`C` along covering arrows) and the four conditions of the tag: (1) `toOver` is fully faithful and
`C` is essentially small; (2) every Zariski covering of the underlying scheme of an object is
refined by a covering of the site; (3) `S/S` is an object of the site; (4) every covering of the
site is an fpqc covering of schemes.  Assume that the fibre products of the site along covering
arrows are fibre products of schemes.  Then the presheaf `𝒪` is a sheaf, and every quasi-coherent
`𝒪`-module `M` is isomorphic to `Fᵃ` for a quasi-coherent `𝒪_S`-module `F`. -/
@[stacks 03OJ "both assertions: O is a sheaf and every quasi-coherent O-module is F^a for a \
quasi-coherent F on S. Corrected form: the source's statement is false when the fibre products \
of the site along coverings are not fibre products of schemes \
(not_isSheaf_structurePresheaf_counterexample), so that is assumed \
(PreservesCoveringFibreProducts), \
as the source's sites of schemes form fibre products in Sch/S. Condition (1) is fullness, \
faithfulness and essential smallness; the site axioms are Stacks 00VH"]
public theorem isSheaf_structurePresheaf_and_exists_iso_siteAssociatedModule
    (hTerminal : ∃ T : C, Nonempty (toOver.obj T ≅ Over.mk (𝟙 S))) :
    ∃ hR : Presheaf.IsSheaf K.toGrothendieck (structurePresheaf S toOver),
      ∀ (M : SheafOfModules.{u} (siteStructureSheaf S toOver K.toGrothendieck hR)),
        M.IsQuasicoherentOnSite →
        ∃ (F : S.Modules) (_ : F.IsQuasicoherent),
          Nonempty (M ≅ siteAssociatedModule S F toOver K.toGrothendieck hR
            (isSheaf_associatedPresheaf_of_preservesCoveringFibreProducts K toOver hfpqc hpres
              F)) := by
  obtain ⟨T, ⟨i⟩⟩ := hTerminal
  have : IsIso (toOver.obj T).hom := by
    rw [← Over.w i.hom]
    exact IsIso.comp_isIso' (inferInstanceAs (IsIso ((Over.forget S).map i.hom)))
      (inferInstanceAs (IsIso (𝟙 S)))
  refine ⟨isSheaf_structurePresheaf_of_preservesCoveringFibreProducts K toOver hfpqc hpres,
    fun M hM => ?_⟩
  obtain ⟨F, hF, ⟨φ⟩⟩ :=
    exists_iso_siteAssociatedModule_of_preservesCoveringFibreProducts S toOver T
    K hfpqc hpres hZariski _ M hM
  exact ⟨F, hF, ⟨φ.symm⟩⟩

end Assertion

end Stacks.Sites

end
