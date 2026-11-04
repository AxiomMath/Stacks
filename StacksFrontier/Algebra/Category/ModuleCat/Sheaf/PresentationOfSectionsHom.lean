module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PresentationOfSections

/-!
# Maps out of a module presented by sections over a terminal object

Let `t` be a terminal object of a site, `R` a sheaf of rings and `N` a sheaf of `R`-modules with
sections `s i` (`i : I`) over `t` which generate `N` locally, together with relations `ρ k`
(`k : K`) among them which generate all relations locally. Then `N` is the cokernel of
`⊕_K O ⟶ ⊕_I O`
(`Stacks.SheafOfModules.FreeSheafification.isPresentedByGlobalSections_of_terminal`),
so a map `N ⟶ P` is the same thing as a family of sections of `P` over `t` satisfying the
relations: evaluation at the `s i` is a bijection
`Hom(N, P) ≃ {g : I → P(t) | ∑ ρ k i • g i = 0 for all k}`.

## Main results

* `Stacks.SheafOfModules.FreeSheafification.hom_ext_of_terminal`: maps out of `N` agreeing on
  the `s i` are equal (only local generation is used).
* `Stacks.SheafOfModules.FreeSheafification.exists_hom_of_terminal`: every family of sections of
  `P` over `t` satisfying the relations is the family of values of a map `N ⟶ P`.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u'

namespace Stacks.SheafOfModules.FreeSheafification

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (t : C) (ht : IsTerminal t) (N : _root_.SheafOfModules.{u} R)

/-- The map `⊕_I O ⟶ N` attached to sections of `N` over a terminal object. -/
def homOfTerminalSections {I : Type u} (s : I → N.val.obj (op t)) :
    SheafOfModules.free (R := R) I ⟶ N :=
  N.freeHomEquiv.symm (fun i ↦ terminalSection t ht N.val (s i))

/-- `homOfTerminalSections` sends the canonical section `freeElt I B i` over `B` to the
restriction of `s i` along `B ⟶ t`. -/
theorem homOfTerminalSections_app_freeElt {I : Type u} (s : I → N.val.obj (op t)) (B : C)
    (i : I) : (homOfTerminalSections t ht N s).val.app (op B) (freeElt I B i) =
      N.val.map (ht.from B).op (s i) :=
  congrArg (fun σ : N.sections ↦ σ.val (op B))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun i ↦ terminalSection t ht N.val (s i)) i)

/-- `homOfTerminalSections` sends the linear combination `∑ c i • freeElt I B i` over `B` to the
linear combination `∑ c i • s i|_B`. -/
theorem homOfTerminalSections_app_sum {I : Type u} (s : I → N.val.obj (op t)) (B : C)
    (c : I →₀ R.obj.obj (op B)) :
    (homOfTerminalSections t ht N s).val.app (op B) (c.sum fun i r ↦ r • freeElt I B i) =
      c.sum fun i r ↦ r • (show N.val.obj (op B) from N.val.map (ht.from B).op (s i)) := by
  rw [app_finsupp_sum_smul]
  exact Finset.sum_congr rfl fun i _ ↦
    congrArg (c i • ·) (homOfTerminalSections_app_freeElt t ht N s B i)

/-- `homOfTerminalSections` sends the canonical section over `t` to `s i`. -/
private theorem homOfTerminalSections_app_freeElt_self {I : Type u} (s : I → N.val.obj (op t))
    (i : I) : (homOfTerminalSections t ht N s).val.app (op t) (freeElt I t i) = s i :=
  (homOfTerminalSections_app_freeElt t ht N s t i).trans (map_from_self t ht N.val (s i))

/-- `homOfTerminalSections` is an epimorphism if the sections `s i` generate `N` locally. -/
private theorem epi_homOfTerminalSections {I : Type u} (s : I → N.val.obj (op t))
    (hgen : ∀ (V : C) (x : N.val.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ c : I →₀ R.obj.obj (op B),
        (c.sum fun i r ↦ r • (show N.val.obj (op B) from N.val.map (ht.from B).op (s i))) =
          N.val.map g.op x) :
    Epi (homOfTerminalSections t ht N s) :=
  SheafOfModules.epi_of_sections _ fun V x ↦ by
    obtain ⟨T, hT, hx⟩ := hgen V x
    exact ⟨T, hT, fun B g hg ↦ by
      obtain ⟨c, hc⟩ := hx g hg
      exact ⟨c.sum fun i r ↦ r • freeElt I B i,
        (homOfTerminalSections_app_sum t ht N s B c).trans hc⟩⟩

include ht in
/-- Two maps out of the free module `⊕_I O` agreeing on the canonical sections over a terminal
object are equal. -/
theorem free_hom_ext_of_terminal {I : Type u} {P : _root_.SheafOfModules.{u} R}
    {φ ψ : SheafOfModules.free (R := R) I ⟶ P}
    (h : ∀ i, φ.val.app (op t) (freeElt I t i) = ψ.val.app (op t) (freeElt I t i)) :
    φ = ψ :=
  P.freeHomEquiv.injective (funext fun i ↦ sections_ext t ht (h i))

/-- **Maps out of a module generated locally by sections over a terminal object are determined by
their values on those sections.** -/
theorem hom_ext_of_terminal {I : Type u} (s : I → N.val.obj (op t))
    (hgen : ∀ (V : C) (x : N.val.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ c : I →₀ R.obj.obj (op B),
        (c.sum fun i r ↦ r • (show N.val.obj (op B) from N.val.map (ht.from B).op (s i))) =
          N.val.map g.op x)
    {P : _root_.SheafOfModules.{u} R} {φ ψ : N ⟶ P}
    (h : ∀ i, φ.val.app (op t) (s i) = ψ.val.app (op t) (s i)) : φ = ψ := by
  have hbepi := epi_homOfTerminalSections t ht N s hgen
  refine (cancel_epi (homOfTerminalSections t ht N s)).1
    (free_hom_ext_of_terminal t ht (fun i ↦ ?_))
  change φ.val.app (op t) ((homOfTerminalSections t ht N s).val.app (op t) (freeElt I t i)) =
    ψ.val.app (op t) ((homOfTerminalSections t ht N s).val.app (op t) (freeElt I t i))
  rw [homOfTerminalSections_app_freeElt_self]
  exact h i

/-- **Maps out of a module presented by sections over a terminal object.** If the sections `s i`
generate `N` locally and the relations `ρ k` generate all relations among them locally, then
every family `g i` of sections of `P` over `t` satisfying the relations is the family of values
of a map `N ⟶ P`. -/
theorem exists_hom_of_terminal (I K : Type u) (s : I → N.val.obj (op t))
    (ρ : K → I →₀ R.obj.obj (op t)) (hρ : ∀ k, ((ρ k).sum fun i r ↦ r • s i) = 0)
    (hgen : ∀ (V : C) (x : N.val.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ c : I →₀ R.obj.obj (op B),
        (c.sum fun i r ↦ r • (show N.val.obj (op B) from N.val.map (ht.from B).op (s i))) =
          N.val.map g.op x)
    (hrel : ∀ (V : C) (c : I →₀ R.obj.obj (op V)),
      (c.sum fun i r ↦ r • (show N.val.obj (op V) from N.val.map (ht.from V).op (s i))) = 0 →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ d : K →₀ R.obj.obj (op B), c.mapRange (R.obj.map g.op).hom (map_zero _) =
          d.sum fun k r ↦ r • (ρ k).mapRange (R.obj.map (ht.from B).op).hom (map_zero _))
    (P : _root_.SheafOfModules.{u} R) (gP : I → P.val.obj (op t))
    (hgP : ∀ k, ((ρ k).sum fun i r ↦ r • gP i) = 0) :
    ∃ φ : N ⟶ P, ∀ i, φ.val.app (op t) (s i) = gP i := by
  classical
  let F := SheafOfModules.free (R := R) I
  let rel : K → F.sections := fun k ↦
    terminalSection t ht F.val ((ρ k).sum fun i r ↦ r • freeElt I t i)
  let b : F ⟶ N := homOfTerminalSections t ht N s
  let a : SheafOfModules.free (R := R) K ⟶ F := F.freeHomEquiv.symm rel
  have ha : ∀ (B : C) (k : K), a.val.app (op B) (freeElt K B k) =
      F.val.map (ht.from B).op ((ρ k).sum fun i r ↦ r • freeElt I t i) := fun B k ↦
    congrArg (fun σ : F.sections ↦ σ.val (op B))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection rel k)
  have hzero : ∀ (Q : _root_.SheafOfModules.{u} R) (h : F ⟶ Q),
      (∀ k, ((ρ k).sum fun i r ↦ r • h.val.app (op t) (freeElt I t i)) = 0) → a ≫ h = 0 := by
    intro Q h hk
    refine Q.freeHomEquiv.injective (funext fun k ↦ sections_ext t ht ?_)
    change h.val.app (op t) (a.val.app (op t) (freeElt K t k)) =
      (SheafOfModules.ιFree (R := R) k ≫ 0).val.app (op t) (1 : R.obj.obj (op t))
    rw [ha, map_from_self t ht, app_finsupp_sum_smul, comp_zero]
    exact hk k
  have hab : a ≫ b = 0 := hzero N b fun k ↦ by
    exact (Finset.sum_congr rfl fun i _ ↦
      congrArg (ρ k i • ·) (homOfTerminalSections_app_freeElt_self t ht N s i)).trans (hρ k)
  have hbepi : Epi b := epi_homOfTerminalSections t ht N s hgen
  have hlepi : Epi (kernel.lift b a hab) := by
    refine SheafOfModules.epi_of_isLocallySurjective _ ⟨fun {V} z ↦ ?_⟩
    let y := (kernel.ι b).val.app (op V) z
    obtain ⟨T₁, hT₁, hy⟩ := exists_finsupp_free R I y
    refine J.transitive hT₁ _ (fun B g hg ↦ ?_)
    obtain ⟨c, hc⟩ := hy g hg
    have hby : (c.sum fun i r ↦ r •
        (show N.val.obj (op B) from N.val.map (ht.from B).op (s i))) = 0 := by
      rw [← homOfTerminalSections_app_sum t ht N s B c, ← hc, PresheafOfModules.naturality_apply]
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
  let hP : F ⟶ P := homOfTerminalSections t ht P gP
  have hhP : ∀ i, hP.val.app (op t) (freeElt I t i) = gP i :=
    homOfTerminalSections_app_freeElt_self t ht P gP
  have hzP : a ≫ hP = 0 := hzero P hP fun k ↦
    (Finset.sum_congr rfl fun i _ ↦ congrArg (ρ k i • ·) (hhP i)).trans (hgP k)
  refine ⟨hcok.desc (CokernelCofork.ofπ hP hzP), fun i ↦ ?_⟩
  have hfac := hcok.fac (CokernelCofork.ofπ hP hzP) WalkingParallelPair.one
  change b ≫ hcok.desc (CokernelCofork.ofπ hP hzP) = hP at hfac
  have := congrArg (fun φ ↦ φ.val.app (op t) (freeElt I t i)) hfac
  change (hcok.desc (CokernelCofork.ofπ hP hzP)).val.app (op t)
    (b.val.app (op t) (freeElt I t i)) = hP.val.app (op t) (freeElt I t i) at this
  rw [homOfTerminalSections_app_freeElt_self] at this
  exact this.trans (hhP i)

end Stacks.SheafOfModules.FreeSheafification

namespace Stacks.SheafOfModules.FreeSheafification

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (t : C) (ht : IsTerminal t) (N : _root_.SheafOfModules.{u} R)

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Local generation from generation over the members of a covering family.** If every object
carries a covering family over whose members the sections `s i` generate, the `s i` generate
locally. -/
theorem hgen_of_presieve {I : Type u} (s : I → N.val.obj (op t)) (good : C → Prop)
    (hcov : ∀ V : C, ∃ T : Presieve V, Sieve.generate T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T g → good B)
    (hspan : ∀ B : C, good B → ∀ x : N.val.obj (op B), ∃ c : I →₀ R.obj.obj (op B),
      (c.sum fun i r ↦ r • (show N.val.obj (op B) from N.val.map (ht.from B).op (s i))) = x)
    (V : C) (x : N.val.obj (op V)) : ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ c : I →₀ R.obj.obj (op B),
        (c.sum fun i r ↦ r • (show N.val.obj (op B) from N.val.map (ht.from B).op (s i))) =
          N.val.map g.op x := by
  obtain ⟨T, hT, hgood⟩ := hcov V
  refine ⟨Sieve.generate T, hT, ?_⟩
  rintro B _ ⟨B', e, g, hg, rfl⟩
  obtain ⟨c, hc⟩ := hspan B' (hgood g hg) (N.val.map g.op x)
  refine ⟨c.mapRange (R.obj.map e.op).hom (map_zero _), Eq.trans ?_
    ((congrArg (N.val.map e.op) hc).trans (N.val.map_comp_apply g.op e.op x).symm)⟩
  refine Eq.trans ?_ (map_finsupp_sum_smul N.val e.op c
    (fun i ↦ (show N.val.obj (op B') from N.val.map (ht.from B').op (s i)))).symm
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (_ • ·) ?_
  exact (N.val.congr_map_apply (congrArg Quiver.Hom.op (ht.hom_ext (ht.from B)
    (e ≫ ht.from B'))) (s i)).trans (N.val.map_comp_apply (ht.from B').op e.op (s i))

end Stacks.SheafOfModules.FreeSheafification

namespace CategoryTheory.Presieve

/-- **A morphism of sheaves of types which is bijective over a covering class of objects is
bijective everywhere.** -/
theorem bijective_app_of_bijective_cover {C : Type*} [Category C] {J : GrothendieckTopology C}
    {P Q : Cᵒᵖ ⥤ Type _} (hP : Presieve.IsSheaf J P) (hQ : Presieve.IsSheaf J Q) (c : P ⟶ Q)
    (good : C → Prop)
    (hcov : ∀ V : C, ∃ T : Presieve V, Sieve.generate T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T g → good B)
    (hgood : ∀ B : C, good B → Function.Bijective (c.app (op B))) (V : C) :
    Function.Bijective (c.app (op V)) := by
  have hnat : ∀ {X Y : Cᵒᵖ} (h : X ⟶ Y) (x : P.obj X), c.app Y (P.map h x) = Q.map h (c.app X x) :=
    fun h x ↦ by
      simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (c.naturality h) x
  have hinj : ∀ V : C, Function.Injective (c.app (op V)) := by
    intro V x y hxy
    obtain ⟨T, hT, hg⟩ := hcov V
    refine ((Presieve.isSheafFor_iff_generate T).2 (hP _ hT)).isSeparatedFor.ext
      fun B g hgT ↦ (hgood B (hg g hgT)).1 ?_
    rw [hnat, hnat, hxy]
  refine ⟨hinj V, fun z ↦ ?_⟩
  obtain ⟨T, hT', hg⟩ := hcov V
  have hT := (Presieve.isSheafFor_iff_generate T).2 (hP _ hT')
  have hTQ := (Presieve.isSheafFor_iff_generate T).2 (hQ _ hT')
  let a : T.FamilyOfElements P := fun B g hgT ↦
    (hgood B (hg g hgT)).2 (Q.map g.op z) |>.choose
  have ha : ∀ B (g : B ⟶ V) (hgT : T g), c.app (op B) (a g hgT) = Q.map g.op z :=
    fun B g hgT ↦ ((hgood B (hg g hgT)).2 (Q.map g.op z)).choose_spec
  have hcomp : a.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    apply hinj Z
    rw [hnat, hnat, ha, ha, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hcomm]
    exacts [h₂, h₁]
  refine ⟨hT.amalgamate a hcomp, hTQ.isSeparatedFor.ext fun B g hgT ↦ ?_⟩
  rw [← hnat, hT.valid_glue hcomp g hgT, ha]
  exact hgT

end CategoryTheory.Presieve

end
