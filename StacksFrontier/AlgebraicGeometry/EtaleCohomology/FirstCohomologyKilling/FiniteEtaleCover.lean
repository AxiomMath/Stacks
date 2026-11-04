module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MainstreamRepresentability
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.BoundaryRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.CoverCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.OverMapConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageRepresentable
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianUnderlyingSets
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre

/-!
# First étale cohomology with finite constant coefficients, through finite étale covers

Let `i : Z ⟶ Y` be a morphism of schemes and `M` a finite abelian group. A class of
`H¹(Z, M)` is the class of an `M`-torsor (Stacks 03AJ), a torsor is finite locally constant, and
a finite locally constant sheaf of sets is represented by a scheme finite étale over `Z`
(Stacks 03RV); so a class dies on a surjective finite étale cover of `Z`. This file proves
that, and deduces that restriction `H¹(Y, M) ⟶ H¹(Z, M)` is bijective whenever base change along
`i` is an equivalence on finite étale covers and every nonempty closed subset of `Y` meets the
image of `i`. This is the argument of Stacks 0A5G, with the input of Stacks 0A48 left as the
hypothesis on `i`.


## Main results

* `Stacks.EtaleCohomology.exists_finite_etale_surjective_mapExactFunctor_eq_zero` — a class of
  `H¹(Z, M)` dies on a surjective finite étale cover of `Z`.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_constantSheaf_one` — restriction
  on `H¹` with finite constant coefficients is bijective along a morphism inducing an equivalence
  of finite étale covers and meeting every nonempty closed subset.

## References

* [Stacks Project, Tag 0A5G](https://stacks.math.columbia.edu/tag/0A5G)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe w u v

namespace Stacks.ExtAdjunction

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]

/-- A class postcomposed with an isomorphism vanishes exactly when the class does. -/
lemma comp_mk₀_eq_zero_iff_of_isIso {X Y Z : C} (f : Y ⟶ Z) [IsIso f] {n : ℕ}
    (x : Ext.{w} X Y n) : x.comp (Ext.mk₀ f) (add_zero n) = 0 ↔ x = 0 := by
  refine ⟨fun h => (postcomp_mk₀_bijective_of_isIso f n).1 ?_, fun h => by rw [h, Ext.zero_comp]⟩
  rwa [postcomp_apply, postcomp_apply, Ext.zero_comp]

end Stacks.ExtAdjunction

namespace Stacks.EtaleCohomology

section FiberTorsor

variable {X : Scheme.{u}} (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
  (c : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ S.X₃)

/-- The global section `c(1)` of `F₃` read as a morphism from the constant presheaf `ℤ`. -/
abbrev boundaryPresheafSection :
    (Functor.const (X.Etale)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ S.X₃.obj :=
  toSheafify X.smallEtaleTopology _ ≫ c.hom

/-- **The fibre sheaf of `F₂ ⟶ F₃` over the global section `c(1)`**: its sections over `V` are the
sections of `F₂` over `V` lifting `c(1)|_V`. -/
def fiberSheaf : Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  ⟨Stacks.Cohomology.Torsors.fiberPresheaf S (boundaryPresheafSection S c),
    Stacks.Cohomology.Torsors.fiberPresheaf_isSheaf S _⟩

/-- A section of the fibre sheaf lifts the restriction of the global section `c(1)`. -/
theorem fiberSheaf_spec {V : X.Etale} (s : (fiberSheaf S c).obj.obj (op V)) :
    S.g.hom.app (op V) s.1 =
      S.X₃.obj.map ((etaleSiteTerminalIsTerminal X).from V).op
        (c.hom.app (op (etaleSiteTerminal X))
          (Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (etaleSiteTerminal X) (ULift.up 1))) := by
  refine s.2.trans ?_
  have := Stacks.ConstantSheaf.constantSheafSection_comp X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) c ((etaleSiteTerminalIsTerminal X).from V)
  exact ConcreteCategory.congr_hom this (ULift.up 1)

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse in
/-- **A section of the fibre sheaf kills the boundary class.** -/
theorem mapExactFunctor_eq_zero_of_fiberSheaf (hS : S.ShortExact) {V : X.Etale}
    (s : (fiberSheaf S c).obj.obj (op V)) :
    ((Ext.mk₀ c).comp hS.extClass (zero_add 1)).mapExactFunctor
      (etaleAbelianInverseImage.{u, 0} V.hom) = 0 :=
  mapExactFunctor_etaleAbelianInverseImage_eq_zero_of_lift hS c V s.1 (fiberSheaf_spec S c s)

/-- Translation of a section of the fibre sheaf by a section of `F₁`. -/
def fiberSheafAct (_hS : S.ShortExact) {V : X.Etale} (a : S.X₁.obj.obj (op V))
    (s : (fiberSheaf S c).obj.obj (op V)) : (fiberSheaf S c).obj.obj (op V) :=
  ⟨S.f.hom.app (op V) a + s.1, by
    rw [map_add, Stacks.Cohomology.Torsors.shortComplex_sections_zero S (op V), zero_add]
    exact s.2⟩

/-- The translate of `s` by `a` has underlying section `f(a) + s` of `F₂`. -/
theorem fiberSheafAct_val (hS : S.ShortExact) {V : X.Etale} (a : S.X₁.obj.obj (op V))
    (s : (fiberSheaf S c).obj.obj (op V)) :
    (fiberSheafAct S c hS a s).1 = S.f.hom.app (op V) a + s.1 :=
  rfl

/-- Translation by sections of `F₁` is simply transitive on the sections of the fibre sheaf. -/
theorem bijective_fiberSheafAct (hS : S.ShortExact) {V : X.Etale}
    (s : (fiberSheaf S c).obj.obj (op V)) :
    Function.Bijective (fun a : S.X₁.obj.obj (op V) => fiberSheafAct S c hS a s) := by
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · have h := congrArg Subtype.val hab
    simp only [fiberSheafAct_val, add_left_inj] at h
    exact (Stacks.Cohomology.Torsors.shortExact_sections_left_exact S hS (op V)).1 h
  · have hker : S.g.hom.app (op V) (t.1 - s.1) = 0 := by
      rw [map_sub, t.2, s.2, sub_self]
    obtain ⟨a, ha⟩ :=
      (Stacks.Cohomology.Torsors.shortExact_sections_left_exact S hS (op V)).2 _ hker
    exact ⟨a, Subtype.ext (by rw [fiberSheafAct_val, ha, sub_add_cancel])⟩

/-- Translation commutes with restriction. -/
theorem fiberSheaf_map_fiberSheafAct (hS : S.ShortExact) {V V' : X.Etale} (g : V' ⟶ V)
    (a : S.X₁.obj.obj (op V)) (s : (fiberSheaf S c).obj.obj (op V)) :
    (fiberSheaf S c).obj.map g.op (fiberSheafAct S c hS a s) =
      fiberSheafAct S c hS (S.X₁.obj.map g.op a) ((fiberSheaf S c).obj.map g.op s) := by
  apply Subtype.ext
  change S.X₂.obj.map g.op (S.f.hom.app (op V) a + s.1) =
    S.f.hom.app (op V') (S.X₁.obj.map g.op a) + S.X₂.obj.map g.op s.1
  rw [map_add, NatTrans.naturality_apply]

/-- Translating the restrictions of a section commutes with restriction along a morphism over the
base. -/
theorem fiberSheafAct_restrict (hS : S.ShortExact) {W : X.Etale}
    (s : (fiberSheaf S c).obj.obj (op W)) {V V' : Over W} (f : V' ⟶ V)
    (a : S.X₁.obj.obj (op V.left)) :
    fiberSheafAct S c hS (S.X₁.obj.map f.left.op a) ((fiberSheaf S c).obj.map V'.hom.op s) =
      (fiberSheaf S c).obj.map f.left.op
        (fiberSheafAct S c hS a ((fiberSheaf S c).obj.map V.hom.op s)) := by
  rw [fiberSheaf_map_fiberSheafAct]
  congr 1
  rw [← Functor.map_comp_apply, ← op_comp, Over.w f]

/-- **Over an étale scheme carrying a section `s`, the fibre sheaf is the restriction of `F₁`**,
as a sheaf of sets: translation of `s` by sections of `F₁`. -/
def overPullbackFiberSheafIso (hS : S.ShortExact) {W : X.Etale}
    (s : (fiberSheaf S c).obj.obj (op W)) :
    (X.smallEtaleTopology.overPullback (Type (u + 1)) W).obj
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj S.X₁) ≅
      (X.smallEtaleTopology.overPullback (Type (u + 1)) W).obj (fiberSheaf S c) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
    (fun V => (Equiv.ofBijective _
      (bijective_fiberSheafAct S c hS ((fiberSheaf S c).obj.map V.unop.hom.op s))).toIso)
    (fun {V V'} f => by
      ext a
      exact fiberSheafAct_restrict S c hS s f.unop a))

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse in
/-- **The fibre sheaf of a short exact sequence whose kernel is a finite constant sheaf is
finite locally constant**: it is locally nonempty, and over an étale scheme with a section it is
the restriction of the kernel. -/
theorem isFiniteLocallyConstant_fiberSheaf (hS : S.ShortExact) (M : AddCommGrpCat.{u + 1})
    [Finite M] (e : S.X₁ ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant X.smallEtaleTopology (fiberSheaf S c) := by
  let T := etaleSiteTerminal X
  obtain ⟨R, hR, hne⟩ := Stacks.Cohomology.Torsors.fiberPseudoTorsor_isTorsor.{u + 1} S hS
    (boundaryPresheafSection S c) T
  refine Stacks.ConstantSheaf.isFiniteLocallyConstant_of_finite_cover X.smallEtaleTopology
    (etaleSiteTerminalIsTerminal X) (fiberSheaf S c)
    (Stacks.ConstantSheaf.sieve_ofArrows_arrows_mem X.smallEtaleTopology R hR) (fun p => ?_)
  obtain ⟨s⟩ := hne p.2.2
  refine ⟨(forget AddCommGrpCat.{u + 1}).obj M, inferInstanceAs (Finite M), ⟨?_⟩⟩
  exact ((Stacks.ConstantSheaf.overPullbackConstantSheafIsoType.{u + 1, u, u + 1}
      X.smallEtaleTopology (etaleSiteTerminalIsTerminal X) p.1).app _).symm ≪≫
    (X.smallEtaleTopology.overPullback (Type (u + 1)) p.1).mapIso
      (((constantCommuteCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).app M).symm ≪≫
        (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).mapIso e.symm) ≪≫
    overPullbackFiberSheafIso S c hS s

/-- Translation by `a + b` is translation by `a` followed by translation by `b`. -/
theorem fiberSheafAct_add (hS : S.ShortExact) {W : X.Etale} (a b : S.X₁.obj.obj (op W))
    (s : (fiberSheaf S c).obj.obj (op W)) :
    fiberSheafAct S c hS (a + b) s = fiberSheafAct S c hS b (fiberSheafAct S c hS a s) :=
  Subtype.ext (by simp only [fiberSheafAct_val, map_add]; abel)

/-- Translation by `0` is the identity. -/
theorem fiberSheafAct_zero (hS : S.ShortExact) {W : X.Etale} (s : (fiberSheaf S c).obj.obj (op W)) :
    fiberSheafAct S c hS 0 s = s :=
  Subtype.ext (by simp only [fiberSheafAct_val, map_zero, zero_add])

end FiberTorsor

/-- The abelian unit is the unit for sheaves of sets followed by a bijection on sections. -/
private theorem exists_bijective_comp_unit_app_forget {X Y : Scheme.{u}} (i : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Etale) :
    ∃ f, Function.Bijective f ∧
      ⇑(((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange i) AddCommGrpCat.{u + 1} X.smallEtaleTopology
        Y.smallEtaleTopology).unit.app F).hom.app (op U)) =
        f ∘ ⇑(((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app
          ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F)).hom.app
            (op U)) := by
  have := preservesLeftKanExtensions_forget_smallEtaleBaseChange i
  let c := coefficientPullbackComparison (smallEtaleBaseChange i) X.smallEtaleTopology
    Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F
  have hc : IsIso c := by
    have : IsIso ((coefficientPullbackTwoSquare (smallEtaleBaseChange i) X.smallEtaleTopology
        Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).natTrans.app F) :=
      inferInstance
    rwa [coefficientPullbackTwoSquare_app] at this
  have hc' : IsIso (c.hom.app (op ((smallEtaleBaseChange i).obj U))) := by
    have : IsIso c.hom := (sheafToPresheaf _ _).map_isIso c
    infer_instance
  have h := congrArg (fun φ => φ.hom.app (op U))
    (coefficientPullbackComparison_unit (smallEtaleBaseChange i) X.smallEtaleTopology
      Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F)
  change _ ≫ c.hom.app (op ((smallEtaleBaseChange i).obj U)) =
    (forget AddCommGrpCat.{u + 1}).map _ ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  exact ⟨_, (isIso_iff_bijective _).1 hc', funext fun x => (ConcreteCategory.congr_hom h x).symm⟩

section DegreeZero

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]

/-- Restriction on `H⁰` and the unit on global sections agree up to bijections: the unit on sections
over the final object is the restriction followed by `H⁰ = Hom(ℤ, -)` and evaluation there. -/
private theorem exists_equiv_comp_restrictionMap_zero_eq_unit_app
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ (a : Sheaf.H.{w} F 0 ≃ _)
      (b : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, 0} i).obj F) 0 ≃ _),
      ⇑(((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange i) AddCommGrpCat.{u + 1} X.smallEtaleTopology
        Y.smallEtaleTopology).unit.app F).hom.app (op (terminal X.Etale))) =
        b ∘ ⇑(etaleCohomologyRestrictionMap.{u, 0, w} i F 0) ∘ a.symm := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange i) AddCommGrpCat.{u + 1} X.smallEtaleTopology
    Y.smallEtaleTopology
  let η := adj.unit.app F
  let e := (etaleAbelianInverseImageConstantIso.{u, 0} i).app (AddCommGrpCat.of (ULift ℤ))
  let Φ : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, 0} i).obj F) 0 ≃
      Sheaf.H.{w} ((smallEtaleBaseChange i).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology |>.obj
          ((etaleAbelianInverseImage.{u, 0} i).obj F)) 0 :=
    Ext.homEquiv₀.trans (((Iso.homCongr e.symm (Iso.refl _)).trans
      (adj.homEquiv _ _)).trans Ext.homEquiv₀.symm)
  have hΦ : ∀ x, Φ (etaleCohomologyRestrictionMap.{u, 0, w} i F 0 x) = Sheaf.H.map η 0 x := by
    intro x
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    rw [etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    change Ext.mk₀ (adj.homEquiv _ _ (e.symm.inv ≫ Ext.homEquiv₀ (Ext.mk₀ _) ≫ 𝟙 _)) =
      (Ext.mk₀ f).comp (Ext.mk₀ η) (add_zero 0)
    rw [Ext.mk₀_comp_mk₀]
    congr 1
    have h₀ : Ext.homEquiv₀ (Ext.mk₀ (e.inv ≫ (etaleAbelianInverseImage.{u, 0} i).map f)) =
        e.inv ≫ (etaleAbelianInverseImage.{u, 0} i).map f :=
      Ext.homEquiv₀.apply_symm_apply _
    rw [h₀, Category.comp_id, Iso.symm_inv, Iso.hom_inv_id_assoc,
      ← Category.comp_id ((etaleAbelianInverseImage.{u, 0} i).map f),
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_id]
  have hη : ∀ s, η.hom.app (op (terminal X.Etale)) s =
      (Sheaf.H.equiv₀ _ terminalIsTerminal) (Sheaf.H.map η 0
        ((Sheaf.H.equiv₀.{w} F terminalIsTerminal).symm s)) := by
    intro s
    rw [← Sheaf.H.equiv₀_naturality]
    exact congrArg _ ((Sheaf.H.equiv₀ F terminalIsTerminal).apply_symm_apply s).symm
  refine ⟨(Sheaf.H.equiv₀ F terminalIsTerminal).toEquiv,
    Φ.trans (Sheaf.H.equiv₀ _ terminalIsTerminal).toEquiv, funext fun s => ?_⟩
  refine (hη s).trans ?_
  rw [← hΦ]
  rfl

/-- **Restriction on `H⁰` is the unit on global sections, for surjectivity.** Let `i : Y ⟶ X`
be a morphism of schemes and `F` an abelian sheaf on `X_étale`. Restriction
`H⁰(X, F) ⟶ H⁰(Y, i⁻¹F)` is surjective if and only if the unit `F ⟶ i_* i⁻¹ F` of the
inverse-image/direct-image adjunction is surjective on sections over the final object of `X_étale`.

Under `H⁰ = Hom(ℤ, -)` and the identification `i⁻¹ ℤ = ℤ`, restriction sends `f : ℤ ⟶ F` to
`i⁻¹ f`, whose adjoint transpose is `f` followed by the unit; and `Hom(ℤ, -)` is evaluation at
the final object (`CategoryTheory.Sheaf.H.equiv₀`). -/
theorem surjective_etaleCohomologyRestrictionMap_zero_iff
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} i F 0) ↔
      Function.Surjective (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange i) AddCommGrpCat.{u + 1} X.smallEtaleTopology
        Y.smallEtaleTopology).unit.app F).hom.app (op (terminal X.Etale))) := by
  obtain ⟨a, b, h⟩ := exists_equiv_comp_restrictionMap_zero_eq_unit_app i F
  rw [h, Equiv.comp_surjective, Equiv.surjective_comp]

omit [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}] in
/-- **The abelian unit is surjective on sections exactly when the unit for sheaves of sets is.**
For an abelian sheaf `F` on `X_étale` and an étale `U` over `X`, the unit `F ⟶ i_* i⁻¹ F` of
abelian sheaves is surjective on sections over `U` if and only if the unit of the adjunction for
sheaves of sets is surjective on sections over `U`, at the underlying sheaf of sets of `F`.

Forgetting the group structure commutes with inverse image through an isomorphism compatible
with the two units (`Stacks.EtaleCohomology.coefficientPullbackComparison_unit`). -/
theorem surjective_unit_app_iff_forget
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Etale) :
    Function.Surjective (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange i) AddCommGrpCat.{u + 1} X.smallEtaleTopology
        Y.smallEtaleTopology).unit.app F).hom.app (op U)) ↔
      Function.Surjective (((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F)).hom.app
          (op U)) := by
  obtain ⟨f, hf, h⟩ := exists_bijective_comp_unit_app_forget i F U
  rw [h]
  exact Function.Surjective.of_comp_iff' hf _

/-- **Restriction on `H⁰` is the unit on global sections, for injectivity.** Let `i : Y ⟶ X`
be a morphism of schemes and `F` an abelian sheaf on `X_étale`. Restriction
`H⁰(X, F) ⟶ H⁰(Y, i⁻¹F)` is injective if and only if the unit `F ⟶ i_* i⁻¹ F` of the
inverse-image/direct-image adjunction is injective on sections over the final object of `X_étale`.

Under `H⁰ = Hom(ℤ, -)` and the identification `i⁻¹ ℤ = ℤ`, restriction sends `f : ℤ ⟶ F` to
`i⁻¹ f`, whose adjoint transpose is `f` followed by the unit; and `Hom(ℤ, -)` is evaluation at
the final object (`CategoryTheory.Sheaf.H.equiv₀`). -/
theorem injective_etaleCohomologyRestrictionMap_zero_iff
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w} i F 0) ↔
      Function.Injective (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange i) AddCommGrpCat.{u + 1} X.smallEtaleTopology
        Y.smallEtaleTopology).unit.app F).hom.app (op (terminal X.Etale))) := by
  obtain ⟨a, b, h⟩ := exists_equiv_comp_restrictionMap_zero_eq_unit_app i F
  rw [h, Equiv.comp_injective, Equiv.injective_comp]

omit [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}] in
/-- **The abelian unit is injective on sections exactly when the unit for sheaves of sets is.**
For an abelian sheaf `F` on `X_étale` and an étale `U` over `X`, the unit `F ⟶ i_* i⁻¹ F` of
abelian sheaves is injective on sections over `U` if and only if the unit of the adjunction for
sheaves of sets is injective on sections over `U`, at the underlying sheaf of sets of `F`.

Forgetting the group structure commutes with inverse image through an isomorphism compatible
with the two units (`Stacks.EtaleCohomology.coefficientPullbackComparison_unit`). -/
theorem injective_unit_app_iff_forget
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Etale) :
    Function.Injective (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange i) AddCommGrpCat.{u + 1} X.smallEtaleTopology
        Y.smallEtaleTopology).unit.app F).hom.app (op U)) ↔
      Function.Injective (((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F)).hom.app
          (op U)) := by
  obtain ⟨f, hf, h⟩ := exists_bijective_comp_unit_app_forget i F U
  rw [h]
  exact Function.Injective.of_comp_iff hf.1 _

end DegreeZero

section DirectImageComparison

variable [∀ S : Scheme.{u}, HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]

section DirectImage

variable {W' W : Scheme.{u}} (p : W' ⟶ W)

/-- **The comparison `H^q(W, p_* K) → H^q(W', K)`** for a morphism of schemes `p : W' ⟶ W`:
apply the exact inverse image `p⁻¹`, postcompose with the counit `p⁻¹ p_* K ⟶ K`, and identify
`p⁻¹ ℤ` with the constant sheaf `ℤ` on `W'`. -/
def etaleCohomologyDirectImageExtMap (K : Sheaf W'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) : Sheaf.H.{w} ((etaleAbelianDirectImage.{u, 0} p).obj K) q →+ Sheaf.H.{w} K q :=
  ((Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} p).app
      (AddCommGrpCat.of (ULift ℤ))).inv).precomp K (zero_add q)).comp
    (Stacks.ExtAdjunction.extMap (etaleAbelianInverseImageDirectImageAdj.{u, 0} p) _ K q)

/-- **Étale cohomology does not change under direct image along an integral morphism.** For
`p : W' ⟶ W` integral — a finite morphism, for instance — the comparison
`H^q(W, p_* K) → H^q(W', K)` is bijective: `p⁻¹ ⊣ p_*` is an adjoint pair of exact functors
(direct image along an integral morphism is exact, Stacks 03QP), so it induces bijections on
`Ext` groups. -/
theorem etaleCohomologyDirectImageExtMap_bijective [IsIntegralHom p]
    (K : Sheaf W'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (etaleCohomologyDirectImageExtMap p K q) := by
  have : (etaleAbelianDirectImage.{u, 0} p).IsRightAdjoint :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} p).isRightAdjoint
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ q).comp
    (Stacks.ExtAdjunction.extMap_bijective (etaleAbelianInverseImageDirectImageAdj.{u, 0} p) _ K q)

/-- The comparison `H^q(W, p_* K) → H^q(W', K)` is natural in `K`. -/
theorem etaleCohomologyDirectImageExtMap_comp_mk₀
    {K L : Sheaf W'.smallEtaleTopology AddCommGrpCat.{u + 1}} (g : K ⟶ L) (q : ℕ)
    (x : Sheaf.H.{w} ((etaleAbelianDirectImage.{u, 0} p).obj K) q) :
    etaleCohomologyDirectImageExtMap p L q
        (x.comp (Ext.mk₀ ((etaleAbelianDirectImage.{u, 0} p).map g)) (add_zero q)) =
      (etaleCohomologyDirectImageExtMap p K q x).comp (Ext.mk₀ g) (add_zero q) := by
  simp only [etaleCohomologyDirectImageExtMap, AddMonoidHom.comp_apply,
    Stacks.ExtAdjunction.extMap_naturality_mk₀, Stacks.ExtAdjunction.precomp_apply,
    Ext.comp_assoc_of_third_deg_zero]

/-- **A class followed by the unit is its restriction.** For `N` on `W` and `ξ ∈ H^q(W, N)`,
the comparison `H^q(W, p_* p⁻¹ N) → H^q(W', p⁻¹ N)` carries `ξ` followed by the unit
`N ⟶ p_* p⁻¹ N` to the restriction of `ξ` along `p`: this is the triangle identity of the
adjunction. -/
theorem etaleCohomologyDirectImageExtMap_comp_unit
    (N : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (ξ : Sheaf.H.{w} N q) :
    etaleCohomologyDirectImageExtMap p _ q
        (ξ.comp (Ext.mk₀ ((etaleAbelianInverseImageDirectImageAdj.{u, 0} p).unit.app N))
          (add_zero q)) =
      etaleCohomologyRestrictionMap.{u, 0, w} p N q ξ := by
  rw [etaleCohomologyRestrictionMap_apply, etaleCohomologyDirectImageExtMap,
    AddMonoidHom.comp_apply, Stacks.ExtAdjunction.extMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Adjunction.left_triangle_components, Ext.comp_mk₀_id]
  rfl

end DirectImage

section BaseChangeUnit

/-! The two steps of the argument that pass through a base change map are proved here with the
categories and functors as variables, so that their geometric instances are single applications
whose types need no conversion. -/

variable {𝒜 ℬ 𝒜' ℬ' : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒜'] [Category* ℬ']
  [Abelian 𝒜'] [HasExt.{w} 𝒜']

omit [∀ S : Scheme.{u}, HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- **A class killed by the unit downstairs is killed by the image of the unit upstairs.** In a
square of adjunctions as in `Stacks.CategoryTheory.BaseChange.twoSquare` whose base change map
is invertible, a class `x ∈ Ext^q(T, Lg A₀)` which dies under the unit
`Lg A₀ ⟶ Rf' (Lf' (Lg A₀))` also dies under `Lg` of the unit `A₀ ⟶ Rf (Lf A₀)`: by
`CategoryTheory.unit_mateEquiv`, the latter followed by the base change map is the former
followed by `Rf'` of an isomorphism. -/
private lemma ext_comp_mk₀_map_unit_eq_zero {Lf : 𝒜 ⥤ ℬ} {Rf : ℬ ⥤ 𝒜} {Lf' : 𝒜' ⥤ ℬ'}
    {Rf' : ℬ' ⥤ 𝒜'} {Lg : 𝒜 ⥤ 𝒜'} {Lg' : ℬ ⥤ ℬ'} {Lc : 𝒜 ⥤ ℬ'} (adjf : Lf ⊣ Rf)
    (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (hiso : IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef).natTrans)
    (A₀ : 𝒜) {T : 𝒜'} {q : ℕ} (x : Ext.{w} T (Lg.obj A₀) q)
    (hx : x.comp (Ext.mk₀ (adjf'.unit.app (Lg.obj A₀))) (add_zero q) = 0) :
    x.comp (Ext.mk₀ (Lg.map (adjf.unit.app A₀))) (add_zero q) = 0 := by
  refine (Stacks.ExtAdjunction.comp_mk₀_eq_zero_iff_of_isIso
    ((Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef).natTrans.app (Lf.obj A₀)) _).1 ?_
  have key : Lg.map (adjf.unit.app A₀) ≫
      (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef).natTrans.app (Lf.obj A₀) =
      adjf'.unit.app (Lg.obj A₀) ≫ Rf'.map
        ((Stacks.CategoryTheory.BaseChange.pullbackComparison eg ef).natTrans.app A₀) :=
    unit_mateEquiv adjf adjf' (Stacks.CategoryTheory.BaseChange.pullbackComparison eg ef) A₀
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, key, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, hx, Ext.zero_comp]

end BaseChangeUnit

section Killing

/-- **On `Y_Z`: a class whose restriction to a finite cover vanishes dies under the inverse
image of the unit of the cover.** Let `i' : P ⟶ Y` be a morphism of schemes, `π : Y' ⟶ Y` a
finite morphism and `A` an abelian sheaf on `Y`. If the restriction of `ξ ∈ H^q(P, i'⁻¹ A)` to
`Y' ×_Y P` vanishes, then `ξ` dies under `i'⁻¹` of the unit `A ⟶ π_* π⁻¹ A`.

By the triangle identity the restriction is the image of `ξ` followed by the unit of the finite
morphism `Y' ×_Y P ⟶ P` under `H^q(P, -_*) ≃ H^q(Y' ×_Y P, -)`, so the class followed by that
unit vanishes; by Stacks 0959 the base change map of the square is invertible, and it carries
the inverse image of the unit of `π` to that unit followed by an isomorphism. -/
theorem ext_comp_mk₀_map_unit_eq_zero_of_restriction {P Y Y' : Scheme.{u}} (i' : P ⟶ Y)
    (π : Y' ⟶ Y) [IsFinite π] (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    {q : ℕ} (ξ : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, 0} i').obj A) q)
    (hξ : etaleCohomologyRestrictionMap.{u, 0, w} (pullback.snd π i') _ q ξ = 0) :
    ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i').map
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app A))) (add_zero q) = 0 := by
  have sq' := IsPullback.of_hasPullback π i'
  have : IsFinite (pullback.snd π i') :=
    MorphismProperty.of_isPullback (P := @IsFinite) sq' inferInstance
  have h₂ : ξ.comp (Ext.mk₀ ((etaleAbelianInverseImageDirectImageAdj.{u, 0}
      (pullback.snd π i')).unit.app ((etaleAbelianInverseImage.{u, 0} i').obj A))) (add_zero q) =
        0 := by
    apply (etaleCohomologyDirectImageExtMap_bijective (pullback.snd π i') _ q).1
    rw [etaleCohomologyDirectImageExtMap_comp_unit, hξ, map_zero]
  have : IsIso (etaleAbelianBaseChange.{u, 0} π i' (pullback.fst π i') (pullback.snd π i')
      sq'.w) :=
    isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite π i' _ _ sq'
  exact ext_comp_mk₀_map_unit_eq_zero (etaleAbelianInverseImageDirectImageAdj.{u, 0} π)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (pullback.snd π i'))
    (etaleAbelianInverseImageCompIso.{u, 0} (pullback.snd π i') i').symm
    ((etaleAbelianInverseImageCompIso.{u, 0} (pullback.fst π i') π).symm ≪≫
      eqToIso (congrArg (fun k : pullback π i' ⟶ Y ↦ etaleAbelianInverseImage.{u, 0} k) sq'.w))
    this A ξ h₂
end Killing

end DirectImageComparison

section Unit

variable {Y Z : Scheme.{u}} (i : Z ⟶ Y)

/-- A morphism `V ⟶ W` of étale `Y`-schemes with finite structure morphisms, read as a morphism of
finite étale covers. -/
private def finiteEtaleOverOfEtale (V : Y.Etale) (hV : IsFinite V.hom) : FiniteEtaleOver Y :=
  MorphismProperty.Over.mk ⊤ V.hom ⟨hV, V.prop⟩

/-- **Base change along `i` is full on étale schemes with finite structure morphisms**, as soon
as it is full on finite étale covers: the two base change functors are built from the same
chosen pullbacks. -/
theorem exists_smallEtaleBaseChange_map_eq [(finiteEtaleBaseChange i).Full] {V W : Y.Etale}
    (hV : IsFinite V.hom) (hW : IsFinite W.hom)
    (ψ : (smallEtaleBaseChange i).obj V ⟶ (smallEtaleBaseChange i).obj W) :
    ∃ φ : V ⟶ W, (smallEtaleBaseChange i).map φ = ψ := by
  let V' := finiteEtaleOverOfEtale V hV
  let W' := finiteEtaleOverOfEtale W hW
  let ψ' : (finiteEtaleBaseChange i).obj V' ⟶ (finiteEtaleBaseChange i).obj W' :=
    MorphismProperty.Over.homMk ψ.left (MorphismProperty.Over.w ψ)
  let φ' := (finiteEtaleBaseChange i).preimage ψ'
  exact ⟨MorphismProperty.Over.homMk φ'.left (MorphismProperty.Over.w φ'),
    MorphismProperty.Over.Hom.ext
      (congrArg (fun k => k.left) ((finiteEtaleBaseChange i).map_preimage ψ'))⟩

/-- The unit of the inverse-image/direct-image adjunction for sheaves of sets, at the sheaf
represented by `W`, on sections over `V`: up to the identification of `i⁻¹ h_W` with
`h_{W ×_Y Z}`, it is base change of `Y`-morphisms `V ⟶ W`. -/
theorem smallEtaleRepresentableUnit_apply (V W : Y.Etale) (φ : V ⟶ W) :
    (((smallEtaleBaseChange i).sheafAdjunctionContinuous (Type (u + 1)) Y.smallEtaleTopology
        Z.smallEtaleTopology).homEquiv _ _
      (smallEtalePullbackRepresentableIso.{u, 0} i W).hom).hom.app (op V) ⟨φ⟩ =
      ⟨(smallEtaleBaseChange i).map φ⟩ := by
  have h := smallEtalePullbackRepresentableIso_hom_comp.{u, 0} i W _ (𝟙 _)
  rw [Category.comp_id] at h
  have h' : Y.smallEtaleTopology.uliftYonedaEquiv
      ((((smallEtaleBaseChange i).sheafAdjunctionContinuous (Type (u + 1)) Y.smallEtaleTopology
        Z.smallEtaleTopology).homEquiv _ _) (smallEtalePullbackRepresentableIso.{u, 0} i W).hom) =
      Z.smallEtaleTopology.uliftYonedaEquiv
        (𝟙 (Z.smallEtaleTopology.uliftYoneda.{u + 1}.obj ((smallEtaleBaseChange i).obj W))) := h
  rw [← GrothendieckTopology.map_uliftYonedaEquiv, h']
  exact GrothendieckTopology.map_uliftYonedaEquiv (J := Z.smallEtaleTopology) (𝟙 _)
    ((smallEtaleBaseChange i).map φ)

/-- The unit on a representable sheaf of sets, on sections over `V`, is base change of
`Y`-morphisms `V ⟶ W` followed by a bijection. -/
private theorem exists_equiv_unit_app_uliftYoneda_eq (V W : Y.Etale) :
    ∃ g : ULift.{u + 1} ((smallEtaleBaseChange i).obj V ⟶ (smallEtaleBaseChange i).obj W) ≃ _,
      ∀ φ : V ⟶ W, ((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app
        (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj W)).hom.app (op V) ⟨φ⟩ =
        g ⟨(smallEtaleBaseChange i).map φ⟩ := by
  let adjM := (smallEtaleBaseChange i).sheafAdjunctionContinuous (Type (u + 1))
    Y.smallEtaleTopology Z.smallEtaleTopology
  let adjC := smallEtaleInverseImageAdjunction.{u, 0} i
  let R := (smallEtaleBaseChange i).sheafPushforwardContinuous (Type (u + 1))
    Y.smallEtaleTopology Z.smallEtaleTopology
  let hW' := Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj W
  let e := smallEtalePullbackRepresentableIso.{u, 0} i W
  let c := (Adjunction.leftAdjointUniq adjM adjC).app hW'
  have hθ : ∀ φ : V ⟶ W, (R.map e.hom).hom.app (op V) ((adjM.unit.app hW').hom.app (op V) ⟨φ⟩) =
      ⟨(smallEtaleBaseChange i).map φ⟩ := by
    intro φ
    rw [← smallEtaleRepresentableUnit_apply i V W φ, Adjunction.homEquiv_unit]
    rfl
  have hC : ⇑((adjC.unit.app hW').hom.app (op V)) =
      ⇑((R.map c.hom).hom.app (op V)) ∘ ⇑((adjM.unit.app hW').hom.app (op V)) := by
    funext x
    exact (congrArg (fun k => k.hom.app (op V) x)
      (Adjunction.unit_leftAdjointUniq_hom_app adjM adjC hW')).symm
  have hbe := (isIso_iff_bijective _).1 (inferInstance : IsIso ((R.map e.hom).hom.app (op V)))
  have hbc := (isIso_iff_bijective _).1 (inferInstance : IsIso ((R.map c.hom).hom.app (op V)))
  refine ⟨(Equiv.ofBijective _ hbe).symm.trans (Equiv.ofBijective _ hbc), fun φ => ?_⟩
  rw [congrFun hC ⟨φ⟩, ← hθ φ]
  exact (congrArg (Equiv.ofBijective _ hbc)
    (Equiv.symm_apply_apply (Equiv.ofBijective _ hbe) _)).symm

/-- The unit on a sheaf of sets isomorphic to a representable one, on sections over `V`, is the
unit on the representable sheaf up to bijections. -/
private theorem exists_bijective_comp_unit_app_of_iso
    {P : Sheaf Y.smallEtaleTopology (Type (u + 1))} {W : Y.Etale}
    (e : P ≅ Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj W) (V : Y.Etale) :
    ∃ (f : _ → _) (g : _ → _), Function.Bijective f ∧ Function.Bijective g ∧
      g ∘ ⇑(((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app P).hom.app (op V)) =
        ⇑(((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app
          (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj W)).hom.app (op V)) ∘ f := by
  have hnat := congrArg (fun k => k.hom.app (op V))
    ((smallEtaleInverseImageAdjunction.{u, 0} i).unit.naturality e.hom)
  exact ⟨_, _, (isIso_iff_bijective _).1 (inferInstance : IsIso (e.hom.hom.app (op V))),
    (isIso_iff_bijective _).1 inferInstance,
    funext fun x => (ConcreteCategory.congr_hom hnat x).symm⟩

/-- **The unit on a representable sheaf of sets is surjective on finite étale sections.** If base
change along `i` is full on finite étale covers, then for étale `Y`-schemes `V` and `W` with finite
structure morphisms the unit `h_W ⟶ i_* i⁻¹ h_W` is surjective on sections over `V`. -/
theorem surjective_smallEtaleInverseImageAdjunction_unit_app_uliftYoneda
    [(finiteEtaleBaseChange i).Full] {V W : Y.Etale} (hV : IsFinite V.hom)
    (hW : IsFinite W.hom) :
    Function.Surjective (((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app
      (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj W)).hom.app (op V)) := by
  obtain ⟨g, hg⟩ := exists_equiv_unit_app_uliftYoneda_eq i V W
  intro y
  obtain ⟨φ, hφ⟩ := exists_smallEtaleBaseChange_map_eq i hV hW (g.symm y).down
  exact ⟨⟨φ⟩, by rw [hg, hφ]; exact g.apply_symm_apply y⟩

/-- **The unit on a finite locally constant sheaf of sets is surjective on finite étale
sections.** If base change along `i` is full on finite étale covers, then for a finite locally
constant sheaf of sets `P` on `Y_étale` and an étale `Y`-scheme `V` with finite structure morphism,
the unit `P ⟶ i_* i⁻¹ P` is surjective on sections over `V`: `P` is representable by a scheme
finite étale over `Y`, where this is
`surjective_smallEtaleInverseImageAdjunction_unit_app_uliftYoneda`. -/
theorem surjective_smallEtaleInverseImageAdjunction_unit_app [(finiteEtaleBaseChange i).Full]
    (P : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology P] {V : Y.Etale}
    (hV : IsFinite V.hom) :
    Function.Surjective (((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app P).hom.app
      (op V)) := by
  obtain ⟨W, hW, ⟨e⟩⟩ := exists_isFinite_iso_uliftYoneda_of_isFiniteLocallyConstant P
  obtain ⟨f, g, hf, hg, h⟩ := exists_bijective_comp_unit_app_of_iso i e V
  have hs := (surjective_smallEtaleInverseImageAdjunction_unit_app_uliftYoneda i hV hW).comp hf.2
  rw [← h] at hs
  exact (Function.Surjective.of_comp_iff' hg _).1 hs

/-- **Base change along `i` is faithful on étale schemes with finite structure morphisms**, as soon
as it is faithful on finite étale covers. -/
theorem smallEtaleBaseChange_map_injective [(finiteEtaleBaseChange i).Faithful] {V W : Y.Etale}
    (hV : IsFinite V.hom) (hW : IsFinite W.hom) :
    Function.Injective ((smallEtaleBaseChange i).map : (V ⟶ W) → _) := by
  intro φ₁ φ₂ h
  let V' := finiteEtaleOverOfEtale V hV
  let W' := finiteEtaleOverOfEtale W hW
  let φ₁' : V' ⟶ W' := MorphismProperty.Over.homMk φ₁.left (MorphismProperty.Over.w φ₁)
  let φ₂' : V' ⟶ W' := MorphismProperty.Over.homMk φ₂.left (MorphismProperty.Over.w φ₂)
  have h' : (finiteEtaleBaseChange i).map φ₁' = (finiteEtaleBaseChange i).map φ₂' :=
    MorphismProperty.Over.Hom.ext (congrArg (fun k => k.left) h)
  exact MorphismProperty.Over.Hom.ext
    (congrArg (fun k => k.left) ((finiteEtaleBaseChange i).map_injective h'))

/-- **The unit on a representable sheaf of sets is injective on finite étale sections**, when base
change along `i` is faithful on finite étale covers. -/
theorem injective_smallEtaleInverseImageAdjunction_unit_app_uliftYoneda
    [(finiteEtaleBaseChange i).Faithful] {V W : Y.Etale} (hV : IsFinite V.hom)
    (hW : IsFinite W.hom) :
    Function.Injective (((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app
      (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj W)).hom.app (op V)) := by
  obtain ⟨g, hg⟩ := exists_equiv_unit_app_uliftYoneda_eq i V W
  rintro ⟨φ₁⟩ ⟨φ₂⟩ h
  rw [hg, hg] at h
  exact congrArg ULift.up (smallEtaleBaseChange_map_injective i hV hW
    (congrArg ULift.down (g.injective h)))

/-- **The unit on a finite locally constant sheaf of sets is injective on finite étale sections**,
when base change along `i` is faithful on finite étale covers. -/
theorem injective_smallEtaleInverseImageAdjunction_unit_app [(finiteEtaleBaseChange i).Faithful]
    (P : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology P] {V : Y.Etale}
    (hV : IsFinite V.hom) :
    Function.Injective (((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app P).hom.app
      (op V)) := by
  obtain ⟨W, hW, ⟨e⟩⟩ := exists_isFinite_iso_uliftYoneda_of_isFiniteLocallyConstant P
  obtain ⟨f, g, hf, hg, h⟩ := exists_bijective_comp_unit_app_of_iso i e V
  have hs := (injective_smallEtaleInverseImageAdjunction_unit_app_uliftYoneda i hV hW).comp hf.1
  rw [← h] at hs
  exact hs.of_comp

end Unit

/-! ### Killing a class of `H¹` with finite constant coefficients by a finite étale cover -/

section Killing

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {Y Z : Scheme.{u}} (i : Z ⟶ Y)

/-- The arrows of a covering sieve of Mathlib's small étale site are jointly surjective on
underlying spaces. -/
private theorem exists_mem_range_of_mem_smallEtaleTopology' (S : Scheme.{u}) {U : S.Etale}
    (T : Sieve U) (hT : T ∈ S.smallEtaleTopology U) (t : U.left) :
    ∃ (W : S.Etale) (f : W ⟶ U), T f ∧ t ∈ Set.range f.left := by
  have h : Sieve.ofArrows (fun a : Σ W : S.Etale, {f : W ⟶ U // T f} ↦ a.1)
      (fun a ↦ a.2.1) = T := by
    refine le_antisymm ?_ fun W f hf ↦ ?_
    · rw [Sieve.generate_le_iff]
      rintro W f ⟨a⟩
      exact a.2.2
    · exact Sieve.ofArrows_mk _ _ (⟨W, f, hf⟩ : Σ W : S.Etale, {f : W ⟶ U // T f})
  rw [← h] at hT
  have hcov := (Scheme.ofArrows_mem_smallEtaleTopology_iff
    (fun a : Σ W : S.Etale, {f : W ⟶ U // T f} ↦ a.2.1)).1 hT
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ t)
  exact ⟨a.1, a.2.1, a.2.2, ha⟩

/-- An étale morphism whose image contains the image of `i` is surjective, as soon as every
nonempty closed subset of `Y` meets the image of `i`: the complement of its image is closed,
an étale morphism being open, and misses the image of `i`. -/
theorem surjective_of_range_subset_of_etale {W : Scheme.{u}} (π : W ⟶ Y) [Etale π]
    (hmeet : ∀ C : Set Y, IsClosed C → C.Nonempty → ∃ z, i.base z ∈ C)
    (hrange : Set.range i.base ⊆ Set.range π.base) : Surjective π := by
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hC : IsClosed (Set.range π.base)ᶜ := π.isOpenMap.isOpen_range.isClosed_compl
  obtain ⟨z, hz⟩ := hmeet _ hC ⟨y, hy⟩
  exact hz (hrange ⟨z, rfl⟩)

/-- **A class of `H¹` with finite constant coefficients dies on a surjective finite étale
cover.** The class is the boundary of a global section of the quotient of an injective
presentation; the fibre over that section is a torsor under the constant sheaf
([Stacks, Tag 03AJ]), a finite locally constant sheaf of sets, hence represented by a scheme `V`
finite étale over `Z` ([Stacks, Tag 03RV]). The torsor has a section over `V`, which kills the
class, and `V ⟶ Z` is surjective because the torsor has sections locally. -/
theorem exists_finite_etale_surjective_mapExactFunctor_eq_zero {Z : Scheme.{u}}
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    (θ : Sheaf.H.{u + 1} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) 1) :
    ∃ V : Z.Etale, IsFinite V.hom ∧ Surjective V.hom ∧
      θ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} V.hom) = 0 := by
  let IP : InjectivePresentation
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) :=
    Classical.arbitrary _
  let S := ShortComplex.mk IP.f (cokernel.π IP.f) (cokernel.condition IP.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel IP.f }
  have : Injective S.X₂ := IP.injective
  obtain ⟨c, hc⟩ := Stacks.Cohomology.Torsors.ext_one_boundary_surjective S hS _ θ
  have := isFiniteLocallyConstant_fiberSheaf S c hS M (Iso.refl _)
  obtain ⟨V₀, hV₀, ⟨e₀⟩⟩ :=
    exists_isFinite_iso_uliftYoneda_of_isFiniteLocallyConstant (fiberSheaf S c)
  refine ⟨V₀, hV₀, ⟨fun z => ?_⟩, ?_⟩
  · obtain ⟨R, hR, hne⟩ := Stacks.Cohomology.Torsors.fiberPseudoTorsor_isTorsor.{u + 1} S hS
      (boundaryPresheafSection S c) (etaleSiteTerminal Z)
    obtain ⟨V, g, hg, v, hv⟩ := exists_mem_range_of_mem_smallEtaleTopology' Z R hR z
    obtain ⟨s⟩ := hne hg
    let φ : V ⟶ V₀ := (e₀.hom.hom.app (op V) s).down
    refine ⟨φ.left.base v, ?_⟩
    have h1 : φ.left ≫ V₀.hom = g.left := by
      rw [MorphismProperty.Over.w φ]
      exact (MorphismProperty.Over.w g).symm.trans (Category.comp_id _)
    rwa [← Scheme.Hom.comp_apply, h1]
  · have hkill := mapExactFunctor_eq_zero_of_fiberSheaf S c hS
      (e₀.inv.hom.app (op V₀) ⟨𝟙 V₀⟩)
    rwa [hc] at hkill

/-- **A class of `H¹` with finite constant coefficients on `Z` dies on the base change of a
surjective finite étale cover of `Y`**, when base change along `i : Z ⟶ Y` is essentially
surjective on finite étale covers and every nonempty closed subset of `Y` meets the image of
`i`.

The class dies on a surjective finite étale `V₀ ⟶ Z`
(`exists_finite_etale_surjective_mapExactFunctor_eq_zero`). By essential surjectivity `V₀` is the
base change of a finite étale `π : W ⟶ Y`, so the class dies on `W ×_Y Z`. The image of `π`
contains that of `i`, so `π` is surjective. -/
theorem exists_finite_etale_surjective_restriction_eq_zero
    [(finiteEtaleBaseChange i).EssSurj]
    (hmeet : ∀ C : Set Y, IsClosed C → C.Nonempty → ∃ z, i.base z ∈ C)
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    (θ : Sheaf.H.{u + 1} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) 1) :
    ∃ (W : Scheme.{u}) (π : W ⟶ Y), IsFinite π ∧ Etale π ∧ Surjective π ∧
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π i) _ 1 θ = 0 := by
  obtain ⟨V₀, hV₀, hV₀s, hk⟩ := exists_finite_etale_surjective_mapExactFunctor_eq_zero M θ
  let A₀ : FiniteEtaleOver Z := MorphismProperty.Over.mk ⊤ V₀.hom ⟨hV₀, V₀.prop⟩
  let W' := (finiteEtaleBaseChange i).objPreimage A₀
  let eW : (finiteEtaleBaseChange i).obj W' ≅ A₀ := (finiteEtaleBaseChange i).objObjPreimageIso A₀
  have hπe : Etale W'.hom := W'.prop.2
  let b : (pullback W'.hom i : Scheme.{u}) ⟶ V₀.left := eW.hom.left
  have hfac : pullback.snd W'.hom i = b ≫ V₀.hom :=
    (MorphismProperty.Over.w eW.hom).symm
  refine ⟨W'.left, W'.hom, W'.prop.1, hπe,
    surjective_of_range_subset_of_etale i W'.hom hmeet ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨v, hv⟩ := hV₀s.surj z
    let w : (pullback W'.hom i : Scheme.{u}) := eW.inv.left.base v
    have hw : (pullback.snd W'.hom i).base w = z := by
      rw [← hv]
      exact (Scheme.Hom.comp_apply eW.inv.left (pullback.snd W'.hom i) v).symm.trans
        (congrArg (fun k => k.base v) (MorphismProperty.Over.w eW.inv))
    refine ⟨(pullback.fst W'.hom i).base w, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hw]
  · have h₁ : θ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} (b ≫ V₀.hom)) = 0 := by
      refine (mapExactFunctor_etaleAbelianInverseImage_comp_eq_zero_iff V₀.hom b θ).1 ?_
      rw [hk]
      exact Ext.mapExactFunctor_zero _ _ _ _
    have h₂ : θ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} (pullback.snd W'.hom i)) = 0 :=
      (Stacks.ExtFunctorial.mapExactFunctor_eq_zero_iff_of_iso
        (eqToIso (congrArg (fun k => etaleAbelianInverseImage.{u, 0} k) hfac)) θ).2 h₁
    rw [etaleCohomologyRestrictionMap_apply, h₂, Ext.comp_zero]

end Killing

/-! ### Finite local constancy of the quotient of a finite étale cover -/

section FiniteLocallyConstant

/-- A constant sheaf of sets with finite value on Mathlib's small étale site is finite locally
constant: the identity covers the final object, over which it is constant. -/
theorem isFiniteLocallyConstant_constantSheaf_type (X : Scheme.{u}) (E : Type (u + 1))
    [Finite E] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant X.smallEtaleTopology
      ((constantSheaf X.smallEtaleTopology (Type (u + 1))).obj E) := by
  let T := etaleSiteTerminal X
  refine Stacks.ConstantSheaf.isFiniteLocallyConstant_of_finite_cover.{u + 1} X.smallEtaleTopology
    (etaleSiteTerminalIsTerminal X) _ (I := PUnit.{1}) (X := fun _ => T) (f := fun _ => 𝟙 T)
    ?_ fun _ => ⟨E, ‹_›, ⟨((Stacks.ConstantSheaf.overPullbackConstantSheafIsoType.{u + 1}
      X.smallEtaleTopology (etaleSiteTerminalIsTerminal X) T).app E).symm⟩⟩
  exact X.smallEtaleTopology.covering_of_eq_top
    (Sieve.id_mem_iff_eq_top.1 (Sieve.ofArrows_mk _ _ PUnit.unit))

/-- A constant abelian sheaf with finite value on Mathlib's small étale site is finite locally
constant, its underlying sheaf of sets being the constant sheaf on the underlying set. -/
theorem isFiniteLocallyConstant_constantSheaf_smallEtale (X : Scheme.{u})
    (M : AddCommGrpCat.{u + 1})
    [Finite M] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant X.smallEtaleTopology
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) := by
  have : Finite ((forget AddCommGrpCat.{u + 1}).obj M) := ‹Finite M›
  have : Stacks.ConstantSheaf.IsFiniteLocallyConstant X.smallEtaleTopology
      ((forget AddCommGrpCat.{u + 1} ⋙ constantSheaf X.smallEtaleTopology (Type (u + 1))).obj M) :=
    isFiniteLocallyConstant_constantSheaf_type X ((forget AddCommGrpCat.{u + 1}).obj M)
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_of_forget _ _
    (Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
      ((constantCommuteCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).app M).symm)

/-- **The pushforward of a finite constant sheaf along a finite étale cover is finite locally
constant** ([Stacks, Tag 095B]). -/
theorem isFiniteLocallyConstant_directImage_inverseImage_constantSheaf {Y W : Scheme.{u}}
    (π : W ⟶ Y) [IsFinite π] [Etale π] (M : AddCommGrpCat.{u + 1}) [Finite M] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology
      ((etaleAbelianDirectImage.{u, 0} π).obj ((etaleAbelianInverseImage.{u, 0} π).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M))) := by
  have := isFiniteLocallyConstant_constantSheaf_smallEtale W M
  have : Stacks.ConstantSheaf.IsFiniteLocallyConstant W.smallEtaleTopology
      ((etaleAbelianInverseImage.{u, 0} π).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) :=
    Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
      ((etaleAbelianInverseImageConstantIso.{u, 0} π).app M).symm
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_finiteEtalePushforward_abelian.{u, 0} π
    ((etaleAbelianInverseImage.{u, 0} π).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M))

/-- **The quotient of a finite constant sheaf in its pushforward along a finite étale cover is
finite locally constant**, as a sheaf of sets: the constant sheaf and its pushforward along a
finite étale morphism are finite locally constant ([Stacks, Tag 095B]), and finite locally
constant abelian sheaves form a weak Serre subcategory ([Stacks, Tag 093U]). -/
theorem isFiniteLocallyConstant_forget_cokernel_unit {Y W : Scheme.{u}} (π : W ⟶ Y) [IsFinite π]
    [Etale π] (M : AddCommGrpCat.{u + 1}) [Finite M] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj
        (cokernel ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)))) := by
  have h₁ := isFiniteLocallyConstant_constantSheaf_smallEtale Y M
  have h₂ := isFiniteLocallyConstant_directImage_inverseImage_constantSheaf π M
  have := Stacks.ConstantSheaf.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf.{u, u + 1, 0}
    Y.smallEtaleTopology
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_forget _ _
    ((Stacks.ConstantSheaf.isFiniteLocallyConstantAbelianSheaf.{u, u + 1, 0}
      Y.smallEtaleTopology).prop_cokernel
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) h₁ h₂)

end FiniteLocallyConstant

/-! ### Lifting sections, and lifting first cohomology classes -/

section Lifting

variable {Y Z : Scheme.{u}} (i : Z ⟶ Y)

/-- **The abelian unit on a finite locally constant sheaf is surjective on finite étale
sections**, when base change along `i` is full on finite étale covers: forgetting the group
structure commutes with inverse image compatibly with the units
(`Stacks.EtaleCohomology.surjective_unit_app_iff_forget`). -/
theorem surjective_etaleAbelianUnit_app_of_isFiniteLocallyConstant
    [(finiteEtaleBaseChange i).Full] (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj Q)]
    {V : Y.Etale} (hV : IsFinite V.hom) :
    Function.Surjective (((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app Q).hom.app
      (op V)) :=
  (surjective_unit_app_iff_forget i Q V).2
    (surjective_smallEtaleInverseImageAdjunction_unit_app i _ hV)

/-- The final object of the small étale site has an invertible, hence finite, structure
morphism. -/
theorem isFinite_terminal_hom (X : Scheme.{u}) : IsFinite (⊤_ X.Etale).hom := by
  let e := terminalIsoIsTerminal (etaleSiteTerminalIsTerminal X)
  have h : (⊤_ X.Etale).hom = e.hom.left :=
    (MorphismProperty.Over.w e.hom).symm.trans (Category.comp_id _)
  let eL : (⊤_ X.Etale).left ≅ X :=
    { hom := e.hom.left
      inv := e.inv.left
      hom_inv_id := congrArg (fun k => k.left) e.hom_inv_id
      inv_hom_id := congrArg (fun k => k.left) e.inv_hom_id }
  rw [h]
  change IsFinite eL.hom
  have : CategoryTheory.IsIso eL.hom := Iso.isIso_hom eL
  infer_instance

/-- **Restriction on `H⁰` of a finite locally constant sheaf is surjective**, when base change
along `i` is full on finite étale covers. -/
theorem surjective_etaleCohomologyRestrictionMap_zero_of_isFiniteLocallyConstant
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(finiteEtaleBaseChange i).Full] (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj Q)] :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} i Q 0) :=
  (surjective_etaleCohomologyRestrictionMap_zero_iff i Q).2
    (surjective_etaleAbelianUnit_app_of_isFiniteLocallyConstant i Q (isFinite_terminal_hom Y))

/-- **A class of `H¹` which dies in the middle term of a short exact sequence is a restriction**,
as soon as restriction is surjective on `H⁰` of the quotient term. Let `0 → F₁ → F₂ → F₃ → 0` be
short exact on `X_étale` and `ξ ∈ H¹(Y, i⁻¹F₁)` die in `H¹(Y, i⁻¹F₂)`. Then `ξ` is the boundary
of a class of `H⁰(Y, i⁻¹F₃)`, which is the restriction of a class of `H⁰(X, F₃)`, whose boundary
restricts to `ξ`. -/
theorem exists_etaleCohomologyRestrictionMap_one_eq_of_comp_eq_zero {X Y : Scheme.{u}}
    (i : Y ⟶ X) [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (h₃ : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} i S.X₃ 0))
    (ξ : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, 0} i).obj S.X₁) 1)
    (hξ : ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map S.f)) (add_zero 1) = 0) :
    ∃ x, etaleCohomologyRestrictionMap.{u, 0, w} i S.X₁ 1 x = ξ := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _
    (hS.map_of_exact (etaleAbelianInverseImage.{u, 0} i)) ξ hξ (zero_add 1)
  obtain ⟨x₃, rfl⟩ := h₃ y
  refine ⟨x₃.comp hS.extClass (zero_add 1), ?_⟩
  rwa [etaleCohomologyRestrictionMap_comp_extClass]

/-- **The abelian unit on a finite locally constant sheaf is injective on finite étale
sections**, when base change along `i` is faithful on finite étale covers. -/
theorem injective_etaleAbelianUnit_app_of_isFiniteLocallyConstant
    [(finiteEtaleBaseChange i).Faithful] (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj Q)]
    {V : Y.Etale} (hV : IsFinite V.hom) :
    Function.Injective (((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app Q).hom.app
      (op V)) :=
  (injective_unit_app_iff_forget i Q V).2
    (injective_smallEtaleInverseImageAdjunction_unit_app i _ hV)

/-- **Restriction on `H⁰` of a finite locally constant sheaf is injective**, when base change
along `i` is faithful on finite étale covers. -/
theorem injective_etaleCohomologyRestrictionMap_zero_of_isFiniteLocallyConstant
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(finiteEtaleBaseChange i).Faithful] (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj Q)] :
    Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w} i Q 0) :=
  (injective_etaleCohomologyRestrictionMap_zero_iff i Q).2
    (injective_etaleAbelianUnit_app_of_isFiniteLocallyConstant i Q (isFinite_terminal_hom Y))

/-- **Restriction is injective on `H¹(X, F₁)` for a short exact sequence `0 → F₁ → F₂ → F₃ → 0`**
whose classes die in `F₂`, as soon as restriction is surjective on `H⁰` of `F₂` and injective on
`H⁰` of `F₃`. A class `x` dying in `F₂` is the boundary of a class `s` of `H⁰(X, F₃)`; if its
restriction vanishes, the restriction of `s` comes from `H⁰(Y, i⁻¹F₂)`, hence from `H⁰(X, F₂)`,
so `s` itself comes from `H⁰(X, F₂)` and its boundary vanishes. -/
theorem eq_zero_of_etaleCohomologyRestrictionMap_one_eq_zero {X Y : Scheme.{u}}
    (i : Y ⟶ X) [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (h₂ : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} i S.X₂ 0))
    (h₃ : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w} i S.X₃ 0))
    (x : Sheaf.H.{w} S.X₁ 1) (hx : x.comp (Ext.mk₀ S.f) (add_zero 1) = 0)
    (hres : etaleCohomologyRestrictionMap.{u, 0, w} i S.X₁ 1 x = 0) : x = 0 := by
  obtain ⟨s, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x hx (zero_add 1)
  have h1 : (etaleCohomologyRestrictionMap.{u, 0, w} i S.X₃ 0 s).comp
      (hS.map_of_exact (etaleAbelianInverseImage.{u, 0} i)).extClass (zero_add 1) = 0 := by
    rwa [← etaleCohomologyRestrictionMap_comp_extClass]
  obtain ⟨t₀, ht₀⟩ := Ext.covariant_sequence_exact₃ _
    (hS.map_of_exact (etaleAbelianInverseImage.{u, 0} i)) _ (zero_add 1) h1
  obtain ⟨t, rfl⟩ := h₂ t₀
  have h2 : s = t.comp (Ext.mk₀ S.g) (add_zero 0) := by
    apply h₃
    rw [etaleCohomologyRestrictionMap_comp_mk₀]
    exact ht₀.symm
  rw [h2, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

end Lifting

/-! ### Stacks 0A5G: surjectivity of restriction on `H¹` with finite constant coefficients -/

section FirstCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {Y Z : Scheme.{u}} (i : Z ⟶ Y)

/-- **Restriction `H¹(Y, M) ⟶ H¹(Z, M)` is surjective for a finite abelian group `M`**, when base
change along `i : Z ⟶ Y` is an equivalence of categories of finite étale covers and every
nonempty closed subset of `Y` meets the image of `i`.

A class `ξ` on `Z` dies on the base change of a surjective finite étale `π : W ⟶ Y`
(`exists_finite_etale_surjective_restriction_eq_zero`), hence in `i⁻¹ π_* π⁻¹ M`. The short
exact sequence `0 → M → π_* π⁻¹ M → Q → 0` on `Y` has finite locally constant quotient, on whose
sections over `Y` restriction to `Z` is surjective; so `ξ` is the restriction of a boundary
(`exists_etaleCohomologyRestrictionMap_one_eq_of_comp_eq_zero`). -/
theorem surjective_etaleCohomologyRestrictionMap_constantSheaf_one
    [(finiteEtaleBaseChange i).IsEquivalence]
    (hmeet : ∀ C : Set Y, IsClosed C → C.Nonempty → ∃ z, i.base z ∈ C)
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) 1) := by
  intro ξ
  let A := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  obtain ⟨W, π, hπf, hπe, hπs, hres⟩ := exists_finite_etale_surjective_restriction_eq_zero i hmeet M
    (ξ.comp (Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} i).app M).hom) (add_zero 1))
  have h0 : etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π i) _ 1 ξ = 0 := by
    rw [etaleCohomologyRestrictionMap_comp_mk₀] at hres
    exact (Stacks.ExtAdjunction.comp_mk₀_eq_zero_iff_of_isIso _ _).1 hres
  have hk := ext_comp_mk₀_map_unit_eq_zero_of_restriction i π A ξ h0
  have : Mono ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app A) :=
    mono_etaleAbelianUnit_of_surjective π A
  let S := ShortComplex.mk ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app A)
    (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have := isFiniteLocallyConstant_forget_cokernel_unit π M
  exact exists_etaleCohomologyRestrictionMap_one_eq_of_comp_eq_zero i hS
    (surjective_etaleCohomologyRestrictionMap_zero_of_isFiniteLocallyConstant i S.X₃) ξ hk

/-- **Restriction `H¹(Y, M) ⟶ H¹(Z, M)` is injective for a finite abelian group `M`**, when base
change along `i : Z ⟶ Y` is fully faithful on finite étale covers.

A class `x` on `Y` dies on a surjective finite étale `π : W ⟶ Y`
(`exists_finite_etale_surjective_mapExactFunctor_eq_zero`), hence in `π_* π⁻¹ M`. In the short
exact sequence `0 → M → π_* π⁻¹ M → Q → 0` both `π_* π⁻¹ M` and `Q` are finite locally constant,
so restriction to `Z` is surjective on `H⁰` of the first and injective on `H⁰` of the second;
hence a class which restricts to zero vanishes
(`eq_zero_of_etaleCohomologyRestrictionMap_one_eq_zero`). -/
theorem injective_etaleCohomologyRestrictionMap_constantSheaf_one
    [(finiteEtaleBaseChange i).Full] [(finiteEtaleBaseChange i).Faithful]
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) 1) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨V, hVf, hVs, hk⟩ := exists_finite_etale_surjective_mapExactFunctor_eq_zero M x
  let A := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  have h0 : etaleCohomologyRestrictionMap.{u, 0, u + 1} V.hom A 1 x = 0 := by
    rw [etaleCohomologyRestrictionMap_apply, hk, Ext.comp_zero]
  have hu : x.comp (Ext.mk₀ ((etaleAbelianInverseImageDirectImageAdj.{u, 0} V.hom).unit.app A))
      (add_zero 1) = 0 :=
    (etaleCohomologyDirectImageExtMap_bijective V.hom _ 1).1 (by
      rw [etaleCohomologyDirectImageExtMap_comp_unit, h0, map_zero])
  have : Etale V.hom := V.prop
  have : Mono ((etaleAbelianInverseImageDirectImageAdj.{u, 0} V.hom).unit.app A) :=
    mono_etaleAbelianUnit_of_surjective V.hom A
  let S := ShortComplex.mk ((etaleAbelianInverseImageDirectImageAdj.{u, 0} V.hom).unit.app A)
    (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have : Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj S.X₃) :=
    isFiniteLocallyConstant_forget_cokernel_unit V.hom M
  have : Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj S.X₂) :=
    Stacks.ConstantSheaf.isFiniteLocallyConstant_forget _ _
      (isFiniteLocallyConstant_directImage_inverseImage_constantSheaf V.hom M)
  exact eq_zero_of_etaleCohomologyRestrictionMap_one_eq_zero i hS
    (surjective_etaleCohomologyRestrictionMap_zero_of_isFiniteLocallyConstant i S.X₂)
    (injective_etaleCohomologyRestrictionMap_zero_of_isFiniteLocallyConstant i S.X₃) x hu hx

/-- **Restriction `H¹(Y, M) ⟶ H¹(Z, M)` is bijective for a finite abelian group `M`**, when base
change along `i : Z ⟶ Y` is an equivalence of categories of finite étale covers and every
nonempty closed subset of `Y` meets the image of `i`. -/
theorem bijective_etaleCohomologyRestrictionMap_constantSheaf_one
    [(finiteEtaleBaseChange i).IsEquivalence]
    (hmeet : ∀ C : Set Y, IsClosed C → C.Nonempty → ∃ z, i.base z ∈ C)
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) 1) :=
  ⟨injective_etaleCohomologyRestrictionMap_constantSheaf_one i M,
    surjective_etaleCohomologyRestrictionMap_constantSheaf_one i hmeet M⟩

end FirstCohomology

end Stacks.EtaleCohomology

end
