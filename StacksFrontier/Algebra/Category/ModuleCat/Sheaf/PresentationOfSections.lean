module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules

/-!
# A global presentation from generating sections and locally generating relations

Let `N` be a sheaf of modules over a sheaf of rings `R` on a site, with sections in the universe
of the coefficient rings. Given global sections `σ i` (`i : I`) of `N` which generate `N` locally,
and global sections `ρ k` (`k : K`) of the free module `⊕_I O` which are relations among the
`σ i` and which generate all relations among the `σ i` locally, `N` is the cokernel of
`⊕_K O ⟶ ⊕_I O`: it has a global presentation (Stacks 03DE (6)) at the universe of the sections.
The index types are arbitrary; for finite ones this is
`SheafOfModules.hasFiniteGlobalPresentation_of_sections`.

The one computation needed is a local description of the sections of an infinite free sheaf of
modules: every section of `⊕_I O` is locally a finite linear combination of the canonical
sections (`Stacks.SheafOfModules.FreeSheafification.exists_finsupp_free`). It comes from the
local surjectivity of the objectwise coproduct onto the free sheaf
(`Stacks.SheafOfModules.FreeSheafification.imageSieve_toFree_mem`) and the fact that a coproduct
of modules is spanned by the images of its coprojections.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u'

/-- **A colimit of modules is spanned by the images of its legs.** -/
theorem ModuleCat.iSup_range_eq_top_of_isColimit {A : Type u} [Ring A] {ι : Type*}
    {F : Discrete ι ⥤ ModuleCat.{u} A} {c : Cocone F} (hc : IsColimit c) :
    ⨆ i : ι, (LinearMap.range (c.ι.app ⟨i⟩).hom : Submodule A c.pt) = ⊤ := by
  let P : Submodule A c.pt := ⨆ i : ι, (LinearMap.range (c.ι.app ⟨i⟩).hom : Submodule A c.pt)
  have h : ModuleCat.ofHom P.mkQ = 0 := by
    refine hc.hom_ext fun j ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    change P.mkQ ((c.ι.app j : F.obj j ⟶ c.pt).hom x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_iSup_of_mem j.as (LinearMap.mem_range_self _ x)
  refine eq_top_iff.2 fun x _ ↦ ?_
  have := congrArg (fun f ↦ f.hom x) h
  simpa [P, Submodule.Quotient.mk_eq_zero] using this

namespace Stacks.SheafOfModules


variable {C' : Type*} [Category C'] {C : Type*} [Category C]
  {J' : GrothendieckTopology C'} {J : GrothendieckTopology C}
  (ι : C' ⥤ C) [ι.IsContinuous J' J] [ι.Full] (R : Sheaf J RingCat.{u})

/-- A map out of the structure sheaf is linear over the structure sheaf. -/
theorem unit_hom_app_eq_smul_one {M : _root_.SheafOfModules.{u} R}
    (x : _root_.SheafOfModules.unit R ⟶ M) (U : Cᵒᵖ) (r : R.obj.obj U) :
    x.val.app U r = r • (show M.val.obj U from x.val.app U (1 : R.obj.obj U)) := by
  have h1 := (x.val.app U).hom.map_smul r
    (show (_root_.SheafOfModules.unit R).val.obj U from (1 : R.obj.obj U))
  have hr : (r • (show (_root_.SheafOfModules.unit R).val.obj U from
      (1 : R.obj.obj U))) = r := mul_one r
  rw [hr] at h1
  exact h1

/-- A map out of the structure sheaf is determined by the image of `1` over any object a given
object maps to. -/
theorem unit_hom_app_eq_smul {M : _root_.SheafOfModules.{u} R}
    (x : _root_.SheafOfModules.unit R ⟶ M) {U V : C} (h : U ⟶ V) (r : R.obj.obj (op U)) :
    x.val.app (op U) r =
      r • (show M.val.obj (op U) from
        M.val.map h.op (x.val.app (op V) (1 : R.obj.obj (op V)))) := by
  have h2 : (_root_.SheafOfModules.unit R).val.map h.op (1 : R.obj.obj (op V)) =
      (1 : R.obj.obj (op U)) := map_one (R.obj.map h.op).hom
  have h3 := PresheafOfModules.naturality_apply x.val h.op (1 : R.obj.obj (op V))
  rw [h2] at h3
  exact (unit_hom_app_eq_smul_one R x (op U) r).trans (congrArg (r • ·) h3)

/-- **Restriction along a full functor whose image contains a terminal object is bijective on
maps out of the structure sheaf.** -/
theorem bijective_pushforward_map_unit (t' : C') (ht : IsTerminal (ι.obj t'))
    (M : _root_.SheafOfModules.{u} R) :
    Function.Bijective (fun x : _root_.SheafOfModules.unit R ⟶ M ↦
      (_root_.SheafOfModules.pushforward.{u} (F := ι)
        (𝟙 ((ι.sheafPushforwardContinuous RingCat.{u} J' J).obj R))).map x) := by
  constructor
  · intro x x' hxx'
    have h0 : x.val.app (op (ι.obj t')) (1 : R.obj.obj (op (ι.obj t'))) =
        x'.val.app (op (ι.obj t')) (1 : R.obj.obj (op (ι.obj t'))) :=
      congrArg (fun φ ↦ φ.val.app (op t') (1 : R.obj.obj (op (ι.obj t')))) hxx'
    refine M.unitHomEquiv.injective (Subtype.ext (funext fun U ↦ ?_))
    change x.val.app U (1 : R.obj.obj U) = x'.val.app U (1 : R.obj.obj U)
    rw [unit_hom_app_eq_smul R x (ht.from U.unop), unit_hom_app_eq_smul R x' (ht.from U.unop), h0]
  · intro ψ
    let m : M.val.obj (op (ι.obj t')) := ψ.val.app (op t') (1 : R.obj.obj (op (ι.obj t')))
    let s : M.sections := PresheafOfModules.sectionsMk (fun U ↦ M.val.map (ht.from U.unop).op m)
      (fun U V f ↦ by
        rw [← PresheafOfModules.map_comp_apply]
        exact M.val.congr_map_apply (congrArg Quiver.Hom.op (ht.hom_ext _ _)) m)
    refine ⟨M.unitHomEquiv.symm s, ?_⟩
    have hx : ∀ U : C, (M.unitHomEquiv.symm s).val.app (op U) (1 : R.obj.obj (op U)) =
        M.val.map (ht.from U).op m :=
      fun U ↦ congrArg (fun σ : M.sections ↦ σ.val (op U)) (M.unitHomEquiv.apply_symm_apply s)
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
      ModuleCat.hom_ext (LinearMap.ext ?_))
    change ∀ r : ((ι.sheafPushforwardContinuous RingCat.{u} J' J).obj R).obj.obj U,
      (M.unitHomEquiv.symm s).val.app (op (ι.obj U.unop)) r = ψ.val.app U r
    intro r
    have hψ := unit_hom_app_eq_smul_one (R := (ι.sheafPushforwardContinuous RingCat.{u} J' J).obj R)
      (M := (_root_.SheafOfModules.pushforward.{u} (F := ι)
        (𝟙 ((ι.sheafPushforwardContinuous RingCat.{u} J' J).obj R))).obj M) ψ U r
    have hψ1 := PresheafOfModules.naturality_apply ψ.val (ι.preimage (ht.from (ι.obj U.unop))).op
        (1 : R.obj.obj (op (ι.obj t')))
    have h2 : ((_root_.SheafOfModules.pushforward.{u} (F := ι)
        (𝟙 ((ι.sheafPushforwardContinuous RingCat.{u} J' J).obj R))).obj
          (_root_.SheafOfModules.unit R)).val.map
        (ι.preimage (ht.from (ι.obj U.unop))).op (1 : R.obj.obj (op (ι.obj t'))) =
        (1 : R.obj.obj (op (ι.obj U.unop))) := map_one (R.obj.map _).hom
    rw [h2] at hψ1
    have key : (M.unitHomEquiv.symm s).val.app (op (ι.obj U.unop)) (1 : R.obj.obj _) =
        ψ.val.app U (1 : R.obj.obj (op (ι.obj U.unop))) := by
      rw [hx, hψ1]
      exact M.val.congr_map_apply (congrArg Quiver.Hom.op (ι.map_preimage _).symm) m
    exact (unit_hom_app_eq_smul_one R (M.unitHomEquiv.symm s) (op (ι.obj U.unop)) r).trans
      ((congrArg (fun z : M.val.obj (op (ι.obj U.unop)) ↦
        (show R.obj.obj (op (ι.obj U.unop)) from r) • z) key).trans hψ.symm)

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules.FreeSheafification

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Every section of the objectwise coproduct of copies of `O` is a finite combination of the
coprojections. -/
theorem exists_finsupp_freePres (I : Type u) {B : C}
    (p : (PresheafOfModules.evaluation R.obj (op B)).obj (freePres R I)) :
    ∃ c : I →₀ R.obj.obj (op B), p = c.sum fun i r ↦
      (Sigma.ι (fun _ : I ↦ PresheafOfModules.unit R.obj) i).app (op B)
        (show (PresheafOfModules.unit R.obj).obj (op B) from r) := by
  classical
  have hc := isColimitOfPreserves (PresheafOfModules.evaluation R.obj (op B))
    (colimit.isColimit (Discrete.functor fun _ : I ↦ PresheafOfModules.unit R.obj))
  have htop := ModuleCat.iSup_range_eq_top_of_isColimit hc
  have hp : p ∈ (⊤ : Submodule (R.obj.obj (op B))
      ((PresheafOfModules.evaluation R.obj (op B)).obj (freePres R I))) :=
    Submodule.mem_top
  rw [← htop] at hp
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ p).1 hp
  have hex : ∀ i, ∃ r : R.obj.obj (op B),
      (Sigma.ι (fun _ : I ↦ PresheafOfModules.unit R.obj) i).app (op B)
        (show (PresheafOfModules.unit R.obj).obj (op B) from r) = f i ∧
        (f i = 0 → r = 0) := by
    intro i
    by_cases h : f i = 0
    · exact ⟨0, by rw [h]; exact map_zero _, fun _ ↦ rfl⟩
    · obtain ⟨r, hr⟩ := LinearMap.mem_range.1 (hf i)
      exact ⟨r, hr, fun h' ↦ absurd h' h⟩
  choose c hc₁ hc₂ using hex
  refine ⟨Finsupp.onFinset f.support c (fun i hi ↦ ?_), ?_⟩
  · rw [Finsupp.mem_support_iff]
    exact fun h0 ↦ hi (hc₂ i h0)
  · refine Eq.symm ((Finsupp.onFinset_sum _ fun i ↦ ?_).trans ?_)
    · exact map_zero _
    · exact Finset.sum_congr rfl fun i _ ↦ hc₁ i

/-- **A section of a free sheaf of modules is locally a finite combination of the canonical
sections.** -/
theorem exists_finsupp_free (I : Type u) {V : C}
    (y : (SheafOfModules.free (R := R) I).val.obj (op V)) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
      ∃ c : I →₀ R.obj.obj (op B), (SheafOfModules.free (R := R) I).val.map g.op y =
        c.sum fun i r ↦ r • (show (SheafOfModules.free (R := R) I).val.obj (op B) from
          (SheafOfModules.ιFree (R := R) i).val.app (op B) (1 : R.obj.obj (op B))) := by
  refine ⟨_, imageSieve_toFree_mem R I y, fun B g hg ↦ ?_⟩
  obtain ⟨p, hp⟩ := hg
  obtain ⟨c, rfl⟩ := exists_finsupp_freePres R I p
  refine ⟨c, hp.symm.trans ?_⟩
  change (toFree R I).app (op B) (c.sum fun i r ↦ _) = _
  rw [map_finsuppSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := congrArg (fun φ ↦ (PresheafOfModules.Hom.app φ (op B)).hom (c i)) (ι_toFree R I i)
  exact h.trans (Stacks.SheafOfModules.unit_hom_app_eq_smul_one R
    (SheafOfModules.ιFree (R := R) i) (op B) (c i))


section Engine

variable {R} (t : C) (ht : IsTerminal t)

/-- The global section of a presheaf of modules extending a section over a terminal object. -/
def terminalSection (P : PresheafOfModules.{u} R.obj) (m : P.obj (op t)) : P.sections :=
  PresheafOfModules.sectionsMk (fun U ↦ P.map (ht.from U.unop).op m) (fun U V f ↦ by
    rw [← PresheafOfModules.map_comp_apply]
    exact P.congr_map_apply (congrArg Quiver.Hom.op (ht.hom_ext _ _)) m)

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
include ht in
/-- On a site with a terminal object `t`, a global section is determined by its value at `t`. -/
theorem sections_ext {P : PresheafOfModules.{u} R.obj} {σ τ : P.sections}
    (h : σ.val (op t) = τ.val (op t)) : σ = τ := by
  refine Subtype.ext (funext fun U ↦ ?_)
  rw [← σ.property (ht.from U.unop).op, ← τ.property (ht.from U.unop).op, h]

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Restriction maps of a presheaf of modules are semilinear on finite combinations. -/
theorem map_finsupp_sum_smul (P : PresheafOfModules.{u} R.obj) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    {ι : Type*} (c : ι →₀ R.obj.obj X) (v : ι → P.obj X) :
    P.map f (c.sum fun i r ↦ r • v i) =
      (c.mapRange (R.obj.map f).hom (map_zero _)).sum fun i r ↦
        r • (show P.obj Y from P.map f (v i)) := by
  rw [map_finsuppSum, Finsupp.sum_mapRange_index]
  · exact Finset.sum_congr rfl fun i _ ↦ P.map_smul f (c i) (v i)
  · intro i
    exact zero_smul _ _

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A morphism of presheaves of modules is linear on finite combinations. -/
theorem app_finsupp_sum_smul {P Q : PresheafOfModules.{u} R.obj} (φ : P ⟶ Q) (X : Cᵒᵖ)
    {ι : Type*} (c : ι →₀ R.obj.obj X) (v : ι → P.obj X) :
    φ.app X (c.sum fun i r ↦ r • v i) = c.sum fun i r ↦ r • φ.app X (v i) := by
  rw [map_finsuppSum]
  exact Finset.sum_congr rfl fun i _ ↦ (φ.app X).hom.map_smul (c i) (v i)

/-- The canonical section `e_i` of the free sheaf of modules over an object. -/
abbrev freeElt (I : Type u) (B : C) (i : I) : (SheafOfModules.free (R := R) I).val.obj (op B) :=
  (SheafOfModules.ιFree (R := R) i).val.app (op B) (1 : R.obj.obj (op B))

theorem map_freeElt (I : Type u) {B V : C} (g : B ⟶ V) (i : I) :
    (SheafOfModules.free (R := R) I).val.map g.op (freeElt I V i) = freeElt I B i := by
  refine (PresheafOfModules.naturality_apply (SheafOfModules.ιFree (R := R) i).val g.op
    (1 : R.obj.obj (op V))).symm.trans ?_
  exact congrArg _ (map_one (R.obj.map g.op).hom)

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
include ht in
theorem map_from_self (P : PresheafOfModules.{u} R.obj) (m : P.obj (op t)) :
    P.map (ht.from t).op m = m := by
  change (P.presheaf ⋙ forget _).map (ht.from t).op m = m
  rw [ht.hom_ext (ht.from t) (𝟙 t), op_id, CategoryTheory.Functor.map_id]
  rfl

variable (N : SheafOfModules.{u} R)

/-- **A global presentation from sections over a terminal object generating locally, and
relations generating all relations locally.** Let `t` be a terminal object of the site and
`s i` (`i : I`) sections of `N` over `t`, and `ρ k` (`k : K`) finite relations among them. If
every section of `N` is locally a combination of the `s i`, and every relation among the `s i`
over an object is locally a combination of the `ρ k`, then `N` is the cokernel of
`⊕_K O ⟶ ⊕_I O`; the presentation is finite when `I` and `K` are. -/
theorem isPresentedByGlobalSections_of_terminal (I K : Type u) (s : I → N.val.obj (op t))
    (ρ : K → I →₀ R.obj.obj (op t)) (hρ : ∀ k, ((ρ k).sum fun i r ↦ r • s i) = 0)
    (hgen : ∀ (V : C) (x : N.val.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ c : I →₀ R.obj.obj (op B),
        (c.sum fun i r ↦ r • (show N.val.obj (op B) from N.val.map (ht.from B).op (s i))) =
          N.val.map g.op x)
    (hrel : ∀ (V : C) (c : I →₀ R.obj.obj (op V)),
      (c.sum fun i r ↦ r • (show N.val.obj (op V) from N.val.map (ht.from V).op (s i))) = 0 →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ d : K →₀ R.obj.obj (op B), c.mapRange (R.obj.map g.op).hom (map_zero _) =
          d.sum fun k r ↦ r • (ρ k).mapRange (R.obj.map (ht.from B).op).hom (map_zero _)) :
    N.IsPresentedByGlobalSections ∧
      (Finite I → Finite K → N.IsFinitelyPresentedByGlobalSections) := by
  classical
  let F := SheafOfModules.free (R := R) I
  let rel : K → F.sections := fun k ↦
    terminalSection t ht F.val ((ρ k).sum fun i r ↦ r • freeElt I t i)
  let b : F ⟶ N := N.freeHomEquiv.symm (fun i ↦ terminalSection t ht N.val (s i))
  let a : SheafOfModules.free (R := R) K ⟶ F := F.freeHomEquiv.symm rel
  have hb : ∀ (B : C) (i : I), b.val.app (op B) (freeElt I B i) =
      N.val.map (ht.from B).op (s i) := fun B i ↦
    congrArg (fun σ : N.sections ↦ σ.val (op B))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
        (fun i ↦ terminalSection t ht N.val (s i)) i)
  have ha : ∀ (B : C) (k : K), a.val.app (op B) (freeElt K B k) =
      F.val.map (ht.from B).op ((ρ k).sum fun i r ↦ r • freeElt I t i) := fun B k ↦
    congrArg (fun σ : F.sections ↦ σ.val (op B))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection rel k)
  have hbsum : ∀ (B : C) (c : I →₀ R.obj.obj (op B)),
      b.val.app (op B) (c.sum fun i r ↦ r • freeElt I B i) =
        c.sum fun i r ↦ r • (show N.val.obj (op B) from N.val.map (ht.from B).op (s i)) := by
    intro B c
    rw [app_finsupp_sum_smul]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (c i • ·) (hb B i)
  have hab : a ≫ b = 0 := by
    refine N.freeHomEquiv.injective (funext fun k ↦ sections_ext t ht ?_)
    change b.val.app (op t) (a.val.app (op t) (freeElt K t k)) =
      (SheafOfModules.ιFree (R := R) k ≫ 0).val.app (op t) (1 : R.obj.obj (op t))
    rw [ha, map_from_self t ht, hbsum, comp_zero]
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) (hρ k)
    exact congrArg (ρ k i • ·) (map_from_self t ht N.val (s i))
  have hbepi : Epi b := SheafOfModules.epi_of_sections b fun V x ↦ by
    obtain ⟨T, hT, hx⟩ := hgen V x
    exact ⟨T, hT, fun B g hg ↦ by
      obtain ⟨c, hc⟩ := hx g hg
      exact ⟨c.sum fun i r ↦ r • freeElt I B i, (hbsum B c).trans hc⟩⟩
  have hlepi : Epi (kernel.lift b a hab) := by
    refine SheafOfModules.epi_of_isLocallySurjective _ ⟨fun {V} z ↦ ?_⟩
    let y := (kernel.ι b).val.app (op V) z
    obtain ⟨T₁, hT₁, hy⟩ := exists_finsupp_free R I y
    refine J.transitive hT₁ _ (fun B g hg ↦ ?_)
    obtain ⟨c, hc⟩ := hy g hg
    have hby : (c.sum fun i r ↦ r •
        (show N.val.obj (op B) from N.val.map (ht.from B).op (s i))) = 0 := by
      rw [← hbsum, ← hc, PresheafOfModules.naturality_apply]
      change N.val.map g.op (((kernel.ι b).val ≫ b.val).app (op V) z) = 0
      rw [← SheafOfModules.comp_val, kernel.condition]
      exact map_zero _
    obtain ⟨T₂, hT₂, hd⟩ := hrel B c hby
    refine J.superset_covering (fun B' h hh ↦ ?_) hT₂
    obtain ⟨d, hd'⟩ := hd h hh
    refine ⟨d.sum fun k r ↦ r • freeElt K B' k, ?_⟩
    apply SheafOfModules.kernel_ι_val_app_injective b (op B')
    have e1 := congrArg (fun φ ↦ φ.val.app (op B') (d.sum fun k r ↦ r • freeElt K B' k))
      (kernel.lift_ι b a hab)
    refine (e1.trans ?_).trans (PresheafOfModules.naturality_apply (kernel.ι b).val (h ≫ g).op
      z).symm
    let L := Finsupp.linearCombination (R.obj.obj (op B')) (freeElt (R := R) I B')
    have hL : ∀ c' : I →₀ R.obj.obj (op B'), L c' = c'.sum fun i r ↦ r • freeElt I B' i :=
      fun c' ↦ Finsupp.linearCombination_apply _ _
    have eR : F.val.map (h ≫ g).op y = L (c.mapRange (R.obj.map h.op).hom (map_zero _)) := by
      rw [op_comp, PresheafOfModules.map_comp_apply, hc, map_finsupp_sum_smul, hL]
      exact Finset.sum_congr rfl fun i _ ↦ congrArg (_ • ·) (map_freeElt I h i)
    have eL : a.val.app (op B') (d.sum fun k r ↦ r • freeElt K B' k) =
        L (d.sum fun k r ↦ r • (ρ k).mapRange (R.obj.map (ht.from B').op).hom (map_zero _)) := by
      rw [app_finsupp_sum_smul, map_finsuppSum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      change d k • a.val.app (op B') (freeElt K B' k) = L (d k • _)
      rw [ha, map_smul, map_finsupp_sum_smul, hL]
      exact congrArg (_ • ·)
        (Finset.sum_congr rfl fun i _ ↦ congrArg (_ • ·) (map_freeElt I (ht.from B') i))
    exact eL.trans ((congrArg L hd').symm.trans eR.symm)
  have hcok : IsColimit (CokernelCofork.ofπ b hab) :=
    isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel b))
      (kernel.lift b a hab) (kernel.lift_ι _ _ _).symm
  refine ⟨⟨I, K, F, _, SheafOfModules.ιFree, SheafOfModules.ιFree,
    ⟨SheafOfModules.isColimitFreeCofan I⟩, ⟨SheafOfModules.isColimitFreeCofan K⟩, a, b, hab,
    ⟨hcok⟩⟩, fun hI hK ↦ ?_⟩
  obtain ⟨n, ⟨eI⟩⟩ := Finite.exists_equiv_fin I
  obtain ⟨m, ⟨eK⟩⟩ := Finite.exists_equiv_fin K
  exact ⟨n, m, F, _, fun j ↦ SheafOfModules.ιFree (eI.symm j),
    fun j ↦ SheafOfModules.ιFree (eK.symm j),
    ⟨(Cofan.isColimitEquivOfEquiv eI.symm (SheafOfModules.freeCofan I))
      (SheafOfModules.isColimitFreeCofan I)⟩,
    ⟨(Cofan.isColimitEquivOfEquiv eK.symm (SheafOfModules.freeCofan K))
      (SheafOfModules.isColimitFreeCofan K)⟩, a, b, hab, ⟨hcok⟩⟩

end Engine

end Stacks.SheafOfModules.FreeSheafification

end
