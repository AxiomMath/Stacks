module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.Presentable
public import StacksFrontier.CategoryTheory.KanExtension.Extend
public import StacksCore.Tactic.StacksAttribute
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Presentable.Limits

/-!
# Extending a functor from the finite modules to all modules

Let `A` and `B` be commutative rings with `A` Noetherian. A functor from finite `A`-modules to
finite `B`-modules extends to a functor on all modules which preserves filtered colimits, and
that extension is unique up to a unique natural isomorphism compatible with the chosen
identification on finite modules. The extension is the pointwise left Kan extension along the
inclusion of the finite modules, which is a dense family of finitely presentable objects
because `A` is Noetherian.

## Main definitions

* `ModuleCat.FGFilteredColimitExtension` packages such an extension together with its
  identification on finite modules.
* `ModuleCat.fgFilteredColimitExtension` constructs the extension.

## Main results

* `ModuleCat.ind_finiteModule`: every module is a filtered colimit of its finite submodules.
* `ModuleCat.fg_isFinitelyPresentable`: over a Noetherian ring a finite module is a finitely
  presentable object of the module category.
* `ModuleCat.FGFilteredColimitExtension.existsUnique_iso` is the uniqueness statement.

## Implementation notes

The restriction condition is recorded as a natural isomorphism after applying the inclusions
of the two full subcategories of finite modules, and uniqueness is relative to that specified
identification. The construction needs only `A` to be Noetherian, so the statement is recorded
in that stronger form. The two module categories share one object universe, and preservation is
stated explicitly for filtered diagrams in that universe. Uniqueness is proved by comparing the
two extensions on the filtered diagram of finite submodules of a module, which is where
preservation of filtered colimits is used.

This is the version of the extension theorem for *finite* modules; the version for finitely
presented modules over an arbitrary ring, with values in an arbitrary category, is
`ModuleCat.FilteredColimitExtension` and is a different object: it is indexed by one ring only
and its target need not be a module category.

## References

* [Stacks Project, Tag 0GP9](https://stacks.math.columbia.edu/tag/0GP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat

private lemma ulift_preserves_filtered
    (A : Type u) [CommRing A] :
    PreservesFilteredColimitsOfSize.{v, v}
      (ModuleCat.uliftFunctor.{u, v} A : ModuleCat.{v} A ⥤ ModuleCat.{max u v} A) := by
  let U : ModuleCat.{v} A ⥤ ModuleCat.{max u v} A := ModuleCat.uliftFunctor.{u, v} A
  let G := forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}
  refine ⟨fun J _ _ => ?_⟩
  have : PreservesColimitsOfShape J (U ⋙ G) := preservesColimitsOfShape_of_natIso
    (Iso.refl (forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v} ⋙ AddCommGrpCat.uliftFunctor.{u, v}))
  exact preservesColimitsOfShape_of_reflects_of_preserves U G

private instance liftedCategory (J : Type v) [SmallCategory J] :
    SmallCategory (ULift.{max u v, v} J) where
  Hom X Y := ULift.{max u v, v} (X.down ⟶ Y.down)
  id X := ULift.up (𝟙 X.down)
  comp f g := ULift.up (f.down ≫ g.down)
  id_comp := by
    rintro X Y ⟨f⟩
    simp
  comp_id := by
    rintro X Y ⟨f⟩
    simp
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    simp

private def liftedEquiv (J : Type v) [SmallCategory J] :
    ULift.{max u v, v} J ≌ J := by
  let E : CategoryTheory.Functor (ULift.{max u v, v} J) J := {
    obj := ULift.down
    map := fun f => f.down }
  let I : CategoryTheory.Functor J (ULift.{max u v, v} J) := {
    obj := ULift.up
    map := ULift.up }
  refine Equivalence.mk' E I ?_ ?_ ?_
  · refine NatIso.ofComponents (fun X => {
      hom := ULift.up (𝟙 X.down)
      inv := ULift.up (𝟙 X.down)
      hom_inv_id := by
        cases X
        change ULift.up (𝟙 _ ≫ 𝟙 _) = ULift.up (𝟙 _)
        simp
      inv_hom_id := by
        cases X
        change ULift.up (𝟙 _ ≫ 𝟙 _) = ULift.up (𝟙 _)
        simp }) ?_
    rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
    change ULift.up (f ≫ 𝟙 _) = ULift.up (𝟙 _ ≫ f)
    simp
  · exact NatIso.ofComponents Iso.refl
  · rintro ⟨x⟩
    simp [E, I]

variable (A : Type u) [CommRing A]
variable (B : Type w) [CommRing B]

/-- The index category of the finite submodules of a module, ordered by inclusion. -/
private abbrev FGSubmoduleIndex (M : ModuleCat.{v} A) :=
  {N : Submodule A M // Module.Finite A N}

private instance (M : ModuleCat.{v} A) : Nonempty (FGSubmoduleIndex A M) := ⟨⟨⊥, inferInstance⟩⟩

private instance (M : ModuleCat.{v} A) : IsDirected (FGSubmoduleIndex A M) (· ≤ ·) := by
  refine ⟨fun N N' => ?_⟩
  have := N.2
  have := N'.2
  exact ⟨⟨N.1 ⊔ N'.1, inferInstance⟩, (le_sup_left : N.1 ≤ _), (le_sup_right : N'.1 ≤ _)⟩

private def fgSubmoduleDiagram (M : ModuleCat.{v} A) :
    FGSubmoduleIndex A M ⥤ ModuleCat.{v} A where
  obj i := ModuleCat.of A i.1
  map f := ModuleCat.ofHom (Submodule.inclusion f.down.down)
  map_id := by
    intro i
    ext x
    rfl
  map_comp := by
    intro i j k f g
    ext x
    rfl

@[reducible] private def fgSubmoduleCocone (M : ModuleCat.{v} A) :
    Cocone (fgSubmoduleDiagram A M) where
  pt := M
  ι := {
    app := fun i ↦ ModuleCat.ofHom i.1.subtype
    naturality := by
      intro i j f
      ext x
      rfl }

@[reducible] private def fgSubmoduleObject (M : ModuleCat.{v} A) (i : FGSubmoduleIndex A M) :
    FGModuleCat.{v} A :=
  ⟨(fgSubmoduleDiagram A M).obj i, i.2⟩

private lemma fgSubmoduleIndex_filtered (M : ModuleCat.{v} A) :
    IsFiltered (FGSubmoduleIndex A M) :=
  inferInstance

private noncomputable def fgSubmoduleCocone_isColimit (M : ModuleCat.{v} A) :
    IsColimit (fgSubmoduleCocone A M) := by
  classical
  let ι := FGSubmoduleIndex A M
  letI : Preorder ι := inferInstance
  letI : DecidableEq ι := Classical.decEq _
  let G : ι → Type v := fun N ↦ N.1
  let f : (i j : ι) → i ≤ j → G i →ₗ[A] G j := fun i j h ↦ Submodule.inclusion h
  have : DirectedSystem G (fun i j h => f i j h) := by
    constructor <;> intros <;> rfl
  let phi : (i : ι) → G i →ₗ[A] M := fun i ↦ i.1.subtype
  have hphi : ∀ i j (h : i ≤ j) (x : G i), phi j (f i j h x) = phi i x :=
    fun _ _ _ _ => rfl
  let g : Module.DirectLimit G f →ₗ[A] M :=
    Module.DirectLimit.lift A ι G f phi hphi
  have hbij : Function.Bijective g := by
    refine ⟨Module.DirectLimit.lift_injective _ _ fun _ ↦ Subtype.val_injective, fun x ↦ ?_⟩
    let N : ι := ⟨Submodule.span A ({x} : Set M), inferInstance⟩
    refine ⟨Module.DirectLimit.of A ι G f N ⟨x, Submodule.mem_span_singleton_self x⟩, ?_⟩
    rw [Module.DirectLimit.lift_of]
    rfl
  let p : ColimitPresentation ι (ModuleCat.of A (Module.DirectLimit G f)) :=
    { diag := ModuleCat.directLimitDiagram G f
      ι := (ModuleCat.directLimitCocone G f).ι
      isColimit := ModuleCat.directLimitIsColimit G f }
  let pM := p.ofIso (LinearEquiv.ofBijective g hbij).toModuleIso
  have hι : ∀ i, pM.ι.app i = (fgSubmoduleCocone A M).ι.app i := by
    intro i
    change ModuleCat.ofHom (g.comp (Module.DirectLimit.of A ι G f i)) =
      ModuleCat.ofHom i.1.subtype
    apply ModuleCat.hom_ext
    ext x
    simp [g, phi, Module.DirectLimit.lift_of]
  exact IsColimit.ofIsoColimit pM.isColimit (Cocone.ext (Iso.refl M) hι)

/-- Every module is the filtered colimit of its finite submodules. -/
lemma ind_finiteModule (M : ModuleCat.{v} A) [IsNoetherianRing A] :
    (ModuleCat.isFG A).ind.{v} M :=
  ⟨FGSubmoduleIndex A M, inferInstance, fgSubmoduleIndex_filtered A M,
    { diag := fgSubmoduleDiagram A M
      ι := (fgSubmoduleCocone A M).ι
      isColimit := fgSubmoduleCocone_isColimit A M },
    fun i => i.2⟩

private def fgSubmoduleTransportCocone
    (E₁ E₂ : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    (β : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₁) ≅
      (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₂))
    (M : ModuleCat.{v} A) : Cocone (fgSubmoduleDiagram A M ⋙ E₁) where
  pt := E₂.obj M
  ι := {
    app := fun i ↦ β.hom.app (fgSubmoduleObject A M i) ≫
      E₂.map ((fgSubmoduleCocone A M).ι.app i)
    naturality := by
      intro i j f
      dsimp
      let fFG : fgSubmoduleObject A M i ⟶ fgSubmoduleObject A M j :=
        InducedCategory.homMk (ModuleCat.ofHom (Submodule.inclusion f.down.down))
      have hmap : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)).map fFG =
          (fgSubmoduleDiagram A M).map f := rfl
      rw [← hmap, reassoc_of% (β.hom.naturality fFG), hmap]
      congr 1
      exact (E₂.map_comp _ _).symm.trans (congrArg E₂.map ((fgSubmoduleCocone A M).w f)) }

private noncomputable def fgSubmoduleComparison
    (E₁ E₂ : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    (β : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₁) ≅
      (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₂))
    [PreservesFilteredColimitsOfSize.{v, v} E₁]
    (M : ModuleCat.{v} A) : E₁.obj M ⟶ E₂.obj M :=
  (isColimitOfPreserves E₁ (fgSubmoduleCocone_isColimit A M)).desc
    (fgSubmoduleTransportCocone A B E₁ E₂ β M)

private lemma fgSubmoduleComparison_fac
    (E₁ E₂ : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    (β : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₁) ≅
      (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₂))
    [PreservesFilteredColimitsOfSize.{v, v} E₁]
    (M : ModuleCat.{v} A) (i : FGSubmoduleIndex A M) :
    E₁.map ((fgSubmoduleCocone A M).ι.app i) ≫
        fgSubmoduleComparison A B E₁ E₂ β M =
      β.hom.app (fgSubmoduleObject A M i) ≫
        E₂.map ((fgSubmoduleCocone A M).ι.app i) :=
  (isColimitOfPreserves E₁ (fgSubmoduleCocone_isColimit A M)).fac
    (fgSubmoduleTransportCocone A B E₁ E₂ β M) i

/-- Maps out of `E₁.obj M` are determined by their precompositions with the images of the
inclusions of the finite submodules. -/
private lemma fgSubmoduleComparison_hom_ext (E₁ : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    [PreservesFilteredColimitsOfSize.{v, v} E₁] {M : ModuleCat.{v} A} {X : ModuleCat.{v} B}
    {g h : E₁.obj M ⟶ X}
    (H : ∀ i : FGSubmoduleIndex A M, E₁.map ((fgSubmoduleCocone A M).ι.app i) ≫ g =
      E₁.map ((fgSubmoduleCocone A M).ι.app i) ≫ h) : g = h :=
  (isColimitOfPreserves E₁ (fgSubmoduleCocone_isColimit A M)).hom_ext H

private lemma fgSubmoduleComparison_naturality
    (E₁ E₂ : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    (β : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₁) ≅
      (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₂))
    [PreservesFilteredColimitsOfSize.{v, v} E₁] {M N : ModuleCat.{v} A} (f : M ⟶ N) :
    E₁.map f ≫ fgSubmoduleComparison A B E₁ E₂ β N =
      fgSubmoduleComparison A B E₁ E₂ β M ≫ E₂.map f := by
  refine fgSubmoduleComparison_hom_ext A B E₁ fun i => ?_
  have := i.2
  let qlin : i.1 →ₗ[A] N := f.hom.comp i.1.subtype
  let k : FGSubmoduleIndex A N := ⟨qlin.range, inferInstance⟩
  let q : (fgSubmoduleDiagram A M).obj i ⟶ (fgSubmoduleDiagram A N).obj k :=
    ModuleCat.ofHom qlin.rangeRestrict
  have hfactor : (fgSubmoduleCocone A M).ι.app i ≫ f = q ≫ (fgSubmoduleCocone A N).ι.app k :=
    ModuleCat.hom_ext (LinearMap.subtype_comp_rangeRestrict qlin).symm
  have hβ : E₁.map q ≫ β.hom.app (fgSubmoduleObject A N k) =
      β.hom.app (fgSubmoduleObject A M i) ≫ E₂.map q :=
    β.hom.naturality
      (InducedCategory.homMk q : fgSubmoduleObject A M i ⟶ fgSubmoduleObject A N k)
  calc
    E₁.map ((fgSubmoduleCocone A M).ι.app i) ≫ E₁.map f ≫ fgSubmoduleComparison A B E₁ E₂ β N =
        E₁.map ((fgSubmoduleCocone A M).ι.app i ≫ f) ≫ fgSubmoduleComparison A B E₁ E₂ β N := by
      rw [E₁.map_comp, Category.assoc]
    _ = (E₁.map q ≫ E₁.map ((fgSubmoduleCocone A N).ι.app k)) ≫
        fgSubmoduleComparison A B E₁ E₂ β N := by
      rw [hfactor, E₁.map_comp]
    _ = (β.hom.app (fgSubmoduleObject A M i) ≫ E₂.map q) ≫
        E₂.map ((fgSubmoduleCocone A N).ι.app k) := by
      rw [Category.assoc (E₁.map q), fgSubmoduleComparison_fac A B E₁ E₂ β N k,
        ← Category.assoc, hβ]
    _ = β.hom.app (fgSubmoduleObject A M i) ≫
        (E₂.map ((fgSubmoduleCocone A M).ι.app i) ≫ E₂.map f) := by
      rw [Category.assoc, ← E₂.map_comp q, ← E₂.map_comp ((fgSubmoduleCocone A M).ι.app i),
        hfactor]
    _ = (E₁.map ((fgSubmoduleCocone A M).ι.app i) ≫ fgSubmoduleComparison A B E₁ E₂ β M) ≫
        E₂.map f := by
      rw [fgSubmoduleComparison_fac A B E₁ E₂ β M i, Category.assoc]

@[reducible] private noncomputable def fgSubmoduleComparison_natTrans
    (E₁ E₂ : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    (β : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₁) ≅
      (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₂))
    [PreservesFilteredColimitsOfSize.{v, v} E₁] :
    E₁ ⟶ E₂ where
  app M := fgSubmoduleComparison A B E₁ E₂ β M
  naturality _ _ f := fgSubmoduleComparison_naturality A B E₁ E₂ β f

private lemma fgSubmoduleComparison_comp
    (E₁ E₂ : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    (β : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₁) ≅
      (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₂))
    [PreservesFilteredColimitsOfSize.{v, v} E₁]
    [PreservesFilteredColimitsOfSize.{v, v} E₂] :
    fgSubmoduleComparison_natTrans A B E₁ E₂ β ≫
      fgSubmoduleComparison_natTrans A B E₂ E₁ β.symm = 𝟙 E₁ := by
  ext M : 2
  refine fgSubmoduleComparison_hom_ext A B E₁ fun i => ?_
  change E₁.map ((fgSubmoduleCocone A M).ι.app i) ≫ fgSubmoduleComparison A B E₁ E₂ β M ≫
      fgSubmoduleComparison A B E₂ E₁ β.symm M = E₁.map ((fgSubmoduleCocone A M).ι.app i) ≫ 𝟙 _
  rw [reassoc_of% (fgSubmoduleComparison_fac A B E₁ E₂ β M i),
    fgSubmoduleComparison_fac A B E₂ E₁ β.symm M i]
  simp

/-- Over a Noetherian ring, a finite module is a finitely presentable object of the module
category. -/
lemma fg_isFinitelyPresentable (M : ModuleCat.{v} A) [IsNoetherianRing A]
    (hM : Module.Finite A M) : IsFinitelyPresentable.{v} M := by
  let U : ModuleCat.{v} A ⥤ ModuleCat.{max u v} A := ModuleCat.uliftFunctor.{u, v} A
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have : IsFinitelyPresentable.{max u v} (U.obj M) := by
    change IsFinitelyPresentable.{max u v} (ModuleCat.of A (ULift.{u, v} M))
    exact ModuleCat.finitePresentation_isFinitelyPresentable A _
      (Module.FinitePresentation.of_equiv (ULift.moduleEquiv.{u, v}.symm : M ≃ₗ[A] ULift.{u, v} M))
  have : PreservesFilteredColimitsOfSize.{v, v} U := ulift_preserves_filtered A
  have : Fact (Cardinal.aleph0 : Cardinal.{v}).IsRegular := Cardinal.fact_isRegular_aleph0
  refine IsCardinalPresentable.mk (κ := Cardinal.aleph0) fun J _ _ D c hc => ?_
  have : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  let e : ULift.{max u v, v} J ≌ J := liftedEquiv J
  have : IsFiltered (ULift.{max u v, v} J) := IsFiltered.of_equivalence e.symm
  let c' : Cocone (e.functor ⋙ D ⋙ U) := Cocone.whisker e.functor (U.mapCocone c)
  have hc' : IsColimit c' := (isColimitOfPreserves U hc).whiskerEquivalence e
  refine ⟨fun g => ?_, fun j f₁ f₂ hf => ?_⟩
  · obtain ⟨⟨j⟩, f, hf⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc' (U.map g)
    change U.obj M ⟶ U.obj (D.obj j) at f
    refine ⟨j, U.preimage f, U.map_injective ?_⟩
    rwa [U.map_comp, U.map_preimage]
  · have hleg : c'.ι.app ⟨j⟩ = U.map (c.ι.app j) := rfl
    have hfU : U.map f₁ ≫ c'.ι.app ⟨j⟩ = U.map f₂ ≫ c'.ι.app ⟨j⟩ := by
      simpa [hleg] using congrArg U.map hf
    have : Fact (Cardinal.aleph0 : Cardinal.{max u v}).IsRegular :=
      Cardinal.fact_isRegular_aleph0
    have : IsCardinalFiltered (ULift.{max u v, v} J) Cardinal.aleph0 :=
      (isCardinalFiltered_aleph0_iff _).2 inferInstance
    obtain ⟨⟨k⟩, a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit'.{max u v}
      Cardinal.aleph0 hc' (U.map f₁) (U.map f₂) hfU
    refine ⟨k, a.down, U.map_injective ?_⟩
    rwa [U.map_comp, U.map_comp]

/-- A filtered-colimit-preserving extension to all modules of a functor between the categories
of finite modules. -/
structure FGFilteredColimitExtension
    (F : FGModuleCat.{v} A ⥤ FGModuleCat.{v} B) where
  /-- The extended functor on all modules. -/
  functor : ModuleCat.{v} A ⥤ ModuleCat.{v} B
  /-- The extended functor commutes with filtered colimits. -/
  preservesFilteredColimits : PreservesFilteredColimitsOfSize.{v, v} functor
  /-- The restriction of the extended functor agrees with the original functor. -/
  iso :
    (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ functor) ≅
      (F ⋙ forget₂ (FGModuleCat.{v} B) (ModuleCat.{v} B))

/-- The functor underlying an extension preserves filtered colimits. -/
instance FGFilteredColimitExtension.instPreservesFilteredColimitsOfSize
    {F : FGModuleCat.{v} A ⥤ FGModuleCat.{v} B}
    (E : FGFilteredColimitExtension.{u, v, w} A B F) :
    PreservesFilteredColimitsOfSize.{v, v} E.functor :=
  E.preservesFilteredColimits

/-- **Stacks Project, Tag 0GP9.** A functor between finite module categories over Noetherian
rings extends to all modules and commutes with filtered colimits. -/
@[stacks 0GP9 "extension"]
noncomputable def fgFilteredColimitExtension
    [IsNoetherianRing A]
    (F : FGModuleCat.{v} A ⥤ FGModuleCat.{v} B) :
    FGFilteredColimitExtension.{u, v, w} A B F := by
  let P := ModuleCat.isFG A
  have hcompact : P ≤ ObjectProperty.isFinitelyPresentable.{v} (ModuleCat.{v} A) :=
    fun M hM => fg_isFinitelyPresentable A M hM
  let F' := F ⋙ forget₂ (FGModuleCat.{v} B) (ModuleCat.{v} B)
  have hpt : P.ι.HasPointwiseLeftKanExtension F' :=
    ObjectProperty.hasPointwiseLeftKanExtension_ι P hcompact (fun M ↦ ind_finiteModule A M) F'
  let Ex : Functor.LeftExtension P.ι F' :=
    Functor.LeftExtension.mk (P.ι.pointwiseLeftKanExtension F')
      (Functor.pointwiseLeftKanExtensionUnit P.ι F')
  have hEx := Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension P.ι F'
  have : PreservesFilteredColimitsOfSize.{v, v} Ex.right :=
    ObjectProperty.preservesFilteredColimitsOfSize_right P hcompact Ex hEx
  have := hEx.isIso_hom
  exact ⟨Ex.right, inferInstance, (asIso Ex.hom).symm⟩

private lemma fgSubmoduleComparison_whiskerLeft
    (E₁ E₂ : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    (β : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₁) ≅
      (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₂))
    [PreservesFilteredColimitsOfSize.{v, v} E₁] :
    Functor.whiskerLeft (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A))
      (fgSubmoduleComparison_natTrans A B E₁ E₂ β) = β.hom := by
  apply NatTrans.ext
  funext X
  let M := (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)).obj X
  have : Module.Finite A M := X.2
  let i : FGSubmoduleIndex A M := ⟨⊤, inferInstance⟩
  let g := (fgSubmoduleCocone A M).ι.app i
  have : IsIso g := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (Submodule.topEquiv (R := A) (M := M)).bijective
  have hnat : β.hom.app (fgSubmoduleObject A M i) ≫ E₂.map g = E₁.map g ≫ β.hom.app X :=
    (β.hom.naturality (InducedCategory.homMk g : fgSubmoduleObject A M i ⟶ X)).symm
  change fgSubmoduleComparison A B E₁ E₂ β M = β.hom.app X
  exact (cancel_epi (E₁.map g)).mp (by rw [fgSubmoduleComparison_fac A B E₁ E₂ β M i, hnat])

private lemma fgSubmoduleComparison_unique
    (E₁ E₂ : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    (β : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₁) ≅
      (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E₂))
    [PreservesFilteredColimitsOfSize.{v, v} E₁] (α : E₁ ⟶ E₂)
    (hα : Functor.whiskerLeft (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)) α = β.hom) :
    α = fgSubmoduleComparison_natTrans A B E₁ E₂ β := by
  ext M : 2
  refine fgSubmoduleComparison_hom_ext A B E₁ fun i => ?_
  have h : α.app ((fgSubmoduleDiagram A M).obj i) = β.hom.app (fgSubmoduleObject A M i) :=
    NatTrans.congr_app hα (fgSubmoduleObject A M i)
  refine (α.naturality _).trans ?_
  rw [h]
  exact (fgSubmoduleComparison_fac A B E₁ E₂ β M i).symm

/-- **Stacks Project, Tag 0GP9.** Two filtered-colimit-preserving extensions are related by a
unique natural isomorphism compatible with their specified identifications on finite
modules. -/
@[stacks 0GP9 "extension"]
theorem FGFilteredColimitExtension.existsUnique_iso
    {F : FGModuleCat.{v} A ⥤ FGModuleCat.{v} B}
    (E₁ E₂ : FGFilteredColimitExtension.{u, v, w} A B F) :
    ∃! e : E₁.functor ≅ E₂.functor,
      Functor.whiskerLeft (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)) e.hom =
        (E₁.iso.trans E₂.iso.symm).hom := by
  let β := E₁.iso.trans E₂.iso.symm
  refine ⟨⟨fgSubmoduleComparison_natTrans A B E₁.functor E₂.functor β,
      fgSubmoduleComparison_natTrans A B E₂.functor E₁.functor β.symm,
      fgSubmoduleComparison_comp A B E₁.functor E₂.functor β,
      fgSubmoduleComparison_comp A B E₂.functor E₁.functor β.symm⟩,
    fgSubmoduleComparison_whiskerLeft A B E₁.functor E₂.functor β,
    fun e' he' => Iso.ext (fgSubmoduleComparison_unique A B E₁.functor E₂.functor β e'.hom he')⟩

end ModuleCat
