module

import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.ENatToNat
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.Functor.Derived.Computing
import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksFrontier.CategoryTheory.Functor.Derived.Shift
public import StacksFrontier.CategoryTheory.Functor.Derived.Triangle
import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.CategoryTheory.Triangulated.Functor
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.DeltaFunctor

/-!
# Derived functors from acyclic resolutions

If every object of `𝒜` embeds into an object acyclic for `RF` in the partial sense of
[Stacks, Tag 05SX], then `RF` is defined on all of `K⁺(𝒜)`, is exact, and is computed by bounded
below complexes of acyclic objects ([Stacks, Tag 05TA]); dually for `LF` on `D⁻`.

It also proves Leray's acyclicity lemma ([Stacks, Tag 015E]) in the same pointwise setting: a
bounded below complex of acyclic objects at which `RF` is defined computes `RF`.

## Main results

* `CategoryTheory.Functor.hasDerivedFunctors_of_enough_acyclic_objects`
* `CategoryTheory.Functor.isIso_ι_app_of_computesRightDerived_single_of_isRightDerivedValueAt`

## References

* [Stacks, Tag 05TA]
* [Stacks, Tag 015E]
-/

@[expose] public section

universe v₁ v₂ v₃ w₁ w₂ u₁ u₂ u₃

open CategoryTheory Limits

namespace CategoryTheory.Functor

open CochainComplex

/-! ### Derived functors from acyclic resolutions ([Stacks, Tag 05TA]) -/

section AcyclicResolutions

universe w w' v v' u u'

open CochainComplex ZeroObject

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

section RightCat

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]

/-- The cocone on the resolution ind-object of `G` at `X` given by `α : G ⟶ L ⋙ R`. -/
private noncomputable def unitCocone {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (G : C ⥤ E) (L : C ⥤ D) (R : D ⥤ E)
    (W : MorphismProperty C) [L.IsLocalization W] (α : G ⟶ L ⋙ R) (X : C) :
    Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ G) where
  pt := R.obj (L.obj X)
  ι :=
    { app s := α.app s.right ≫ R.map (Localization.isoOfHom L W s.hom s.prop).inv
      naturality s t u := by
        have : IsIso (L.map s.hom) := Localization.inverts L W s.hom s.prop
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map,
          MorphismProperty.Under.forget_comp_forget_comp_obj,
          MorphismProperty.Under.forget_comp_forget_comp_map]
        rw [Category.comp_id, α.naturality_assoc, Functor.comp_map, ← R.map_comp]
        congr 2
        rw [← cancel_epi (L.map s.hom), ← L.map_comp_assoc, MorphismProperty.Under.w u]
        simp }

private lemma unitCocone_ι_app_id {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (G : C ⥤ E) (L : C ⥤ D) (R : D ⥤ E)
    (W : MorphismProperty C) [W.ContainsIdentities] [L.IsLocalization W] (α : G ⟶ L ⋙ R)
    (X : C) : (unitCocone G L R W α X).ι.app
      (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X)) = α.app X := by
  simp [unitCocone, Localization.isoOfHom]

/-- If every object of `C` maps by a morphism of `W` to one at which `α` is invertible, then `X`
computes the right derived functor of `G` in the essentially constant sense of Stacks 05SX exactly
when `α` is invertible at `X`. -/
public lemma computesRightDerived_iff_isIso_app {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (G : C ⥤ E) (L : C ⥤ D) (R : D ⥤ E)
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] [L.IsLocalization W]
    (α : G ⟶ L ⋙ R) (X : C)
    (h : ∀ K : C, ∃ (I : C) (s : K ⟶ I) (_ : W s), IsIso (α.app I)) :
    G.ComputesRightDerived W X ↔ IsIso (α.app X) := by
  let c := unitCocone G L R W α X
  have hleg (s : W.Under ⊤ X) : ∃ (t : W.Under ⊤ X) (_ : s ⟶ t), IsIso (c.ι.app t) := by
    obtain ⟨I, f, hf, hI⟩ := h s.right
    exact ⟨MorphismProperty.Under.mk ⊤ (s.hom ≫ f) (W.comp_mem _ _ s.prop hf),
      MorphismProperty.Under.homMk f rfl, by
        dsimp only [c, unitCocone, MorphismProperty.Under.mk_right]
        exact IsIso.comp_isIso' hI inferInstance⟩
  obtain ⟨s₀, _, hs₀⟩ := hleg (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X))
  have hc : G.IsRightDerivedValueAt W X c := by
    refine (G.isRightDerivedValueAt_iff W X c).2 ⟨s₀, @CategoryTheory.inv _ _ _ _ (c.ι.app s₀) hs₀,
      ⟨@IsIso.inv_hom_id _ _ _ _ _ hs₀, fun s => ?_⟩⟩
    obtain ⟨t, w, ht⟩ := hleg (IsFiltered.max s s₀)
    refine ⟨t, IsFiltered.rightToMax s s₀ ≫ w, IsFiltered.leftToMax s s₀ ≫ w, ?_⟩
    rw [← cancel_mono (c.ι.app t), c.w, Category.assoc, Category.assoc, c.w,
      @IsIso.inv_hom_id _ _ _ _ _ hs₀]
    exact (Category.comp_id _).symm
  have hi : c.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X)) =
      α.app X := unitCocone_ι_app_id G L R W α X
  constructor
  · rintro ⟨d, hd, hdι⟩
    rw [← hi, ← hd.isColimit.comp_coconePointUniqueUpToIso_hom hc.isColimit]
    exact IsIso.comp_isIso' hdι (Iso.isIso_hom _)
  · intro hα
    exact ⟨c, hc, hi ▸ hα⟩

end RightCat

section Localization
variable {A B : Type*} [Category* A] [Category* B]

/-- Objectwise resolutions by a full subcategory `P` give resolutions of arrows, when `W` has a
calculus of left fractions: resolve the source, complete the resulting span by a left fraction,
and resolve its target. -/
private lemma hasRightResolutions_arrow_of_resolutions (W : MorphismProperty A)
    [W.HasLeftCalculusOfFractions] (P : ObjectProperty A)
    (hP : ∀ X, ∃ (Y : A) (_ : P Y) (r : X ⟶ Y), W r) :
    (LocalizerMorphism.ofEq (F := P.ι)
      (W₁ := W.inverseImage P.ι) rfl).arrow.HasRightResolutions := by
  intro g
  obtain ⟨X, hX, r, hr⟩ := hP g.left
  obtain ⟨q, hq⟩ := (MorphismProperty.RightFraction.mk r hr g.hom).exists_leftFraction
  obtain ⟨Y, hY, s, hs⟩ := hP q.Y'
  exact ⟨{
    X₁ := Arrow.mk (ObjectProperty.homMk (q.f ≫ s) : (⟨X, hX⟩ : P.FullSubcategory) ⟶ ⟨Y, hY⟩)
    w := Arrow.homMk r (q.s ≫ s)
      ((Category.assoc _ _ _).symm.trans ((hq =≫ s).symm.trans (Category.assoc _ _ _)))
    hw := ⟨hr, W.comp_mem _ _ q.hs hs⟩ }⟩

/-- Enough right resolutions in a full subcategory give a right derivability structure:
Ore squares provide connected resolution categories and resolutions of arrows. -/
public lemma rightDerivability_of_resolutions (W : MorphismProperty A)
    [W.HasLeftCalculusOfFractions] (P : ObjectProperty A)
    (hP : ∀ X, ∃ (Y : A) (_ : P Y) (r : X ⟶ Y), W r) :
    (LocalizerMorphism.ofEq (F := P.ι)
      (W₁ := W.inverseImage P.ι) rfl).IsRightDerivabilityStructure := by
  let Φ := LocalizerMorphism.ofEq (F := P.ι) (W₁ := W.inverseImage P.ι) rfl
  have hres : Φ.HasRightResolutions := by
    intro X
    obtain ⟨Y, hY, r, hr⟩ := hP X
    exact ⟨{ X₁ := ⟨Y, hY⟩, w := r, hw := hr }⟩
  have : (W.inverseImage P.ι).HasLeftCalculusOfFractions := by
    constructor
    · intro X Y φ
      let ψ : W.RightFraction X.obj Y.obj := { s := φ.s.hom, hs := φ.hs, f := φ.f.hom }
      obtain ⟨q, hq⟩ := ψ.exists_leftFraction
      obtain ⟨Z, hZ, r, hr⟩ := hP q.Y'
      exact ⟨{ Y' := ⟨Z, hZ⟩, f := ObjectProperty.homMk (q.f ≫ r)
               s := ObjectProperty.homMk (q.s ≫ r), hs := W.comp_mem _ _ q.hs hr },
        ObjectProperty.hom_ext _ (by simpa [ψ] using hq =≫ r)⟩
    · intro X' X Y f g s hs h
      obtain ⟨Z, t, ht, hfg⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
        f.hom g.hom s.hom hs (congrArg (fun t ↦ t.hom) h)
      obtain ⟨Z', hZ', r, hr⟩ := hP Z
      exact ⟨⟨Z', hZ'⟩, ObjectProperty.homMk (t ≫ r), W.comp_mem _ _ ht hr,
        ObjectProperty.hom_ext _ (by simpa using hfg =≫ r)⟩
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.functor.Full := inferInstanceAs P.ι.Full
  have : Φ.functor.Faithful := inferInstanceAs P.ι.Faithful
  have : Φ.IsLocalizedEquivalence :=
    RightAcyclicCriterion.localizedEquivalence_of_rightResolutions Φ
  have : ∀ X, IsConnected (Φ.RightResolution X) := by
    intro X
    apply zigzag_isConnected
    intro R S
    let ψ : W.RightFraction R.X₁.obj S.X₁.obj := { s := R.w, hs := R.hw, f := S.w }
    obtain ⟨q, hq⟩ := ψ.exists_leftFraction
    obtain ⟨Z, hZ, r, hr⟩ := hP q.Y'
    let T : Φ.RightResolution X :=
      { X₁ := ⟨Z, hZ⟩, w := S.w ≫ q.s ≫ r, hw := W.comp_mem _ _ S.hw (W.comp_mem _ _ q.hs hr) }
    let a : R ⟶ T :=
      { f := ObjectProperty.homMk (q.f ≫ r)
        comm := by simpa [Φ, LocalizerMorphism.ofEq, ψ, T] using (hq =≫ r).symm }
    let b : S ⟶ T := { f := ObjectProperty.homMk (q.s ≫ r) }
    exact (Zigzag.of_hom a).trans (Zigzag.of_inv b)
  have := hasRightResolutions_arrow_of_resolutions W P hP
  exact LocalizerMorphism.IsRightDerivabilityStructure.mk' Φ
end Localization

section Resolutions


variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]

omit [HasDerivedCategory C] in
/-- The quasi-isomorphisms of `K⁺(𝒜)` form a saturated multiplicative system: they admit a left
and a right calculus of fractions, and a morphism `g` is a quasi-isomorphism as soon as `f ≫ g`
and `g ≫ h` are. -/
lemma quasiIsoPlus_isSaturated :
    (HomotopyCategory.Plus.quasiIso C).IsSaturated := by
  have hleft : (HomotopyCategory.Plus.quasiIso C).HasLeftCalculusOfFractions := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  have hright : (HomotopyCategory.Plus.quasiIso C).HasRightCalculusOfFractions := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  refine ⟨hleft, hright, ?_⟩
  intro X Y Z T f g h hfg hgh n
  let H := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n
  have : IsIso (H.map f.hom ≫ H.map g.hom) := by
    rw [← H.map_comp]; exact hfg n
  have : IsIso (H.map g.hom ≫ H.map h.hom) := by
    rw [← H.map_comp]; exact hgh n
  have : Epi (H.map g.hom) := epi_of_epi (H.map f.hom) (H.map g.hom)
  have : Mono (H.map g.hom) := mono_of_mono (H.map g.hom) (H.map h.hom)
  exact isIso_of_mono_of_epi (H.map g.hom)

omit [HasDerivedCategory C] in
private lemma quasiIsoPlus_compatible :
    (HomotopyCategory.Plus.quasiIso C).IsCompatibleWithTriangulation := by
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

private noncomputable abbrev derivedSituation (F : C ⥤ D) [F.Additive] :
  Stacks.DerivedFunctor.Shift.Situation where
  D := HomotopyCategory.Plus C
  D' := DerivedCategory.Plus D
  F := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  S := HomotopyCategory.Plus.quasiIso C
  saturatedS := quasiIsoPlus_isSaturated
  shiftCompatibleS := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  compatibleTriangulationS := quasiIsoPlus_compatible

/-- A lower cohomological bound is preserved by retracts. -/
private lemma isGE_of_retract_plus {X Y : DerivedCategory.Plus D}
    (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X)
    (a : ℤ) [Y.IsGE a] : X.IsGE a := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
  exact StacksDraft.RightDerivedMovesRight.isGE_of_retract (DerivedCategory.Plus.ι.map i)
    (DerivedCategory.Plus.ι.map p)
    (by rw [← Functor.map_comp, hip, Functor.map_id]) a inferInstance

omit [HasDerivedCategory C] in
/-- A termwise lower bound remains a cohomological lower bound after applying an
additive functor. -/
private lemma isGE_mapHomotopyCategoryPlus_obj
    (F : C ⥤ D) [F.Additive] (X : HomotopyCategory.Plus C) (a : ℤ)
    [h : CochainComplex.IsStrictlyGE X.obj.as a] :
    ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj X).IsGE a :=
  isGE_Phi_obj F X.obj.as ⟨a, h⟩ a h

omit [HasDerivedCategory C] in
/-- Source derived values inherit the lower cohomological bound of their argument.
The value is a retract of a resolution; good truncation makes that resolution
termwise bounded in the same degrees. -/
private lemma isGE_of_retraction
    (F : C ⥤ D) [F.Additive] (X : HomotopyCategory.Plus C) (a : ℤ)
    (hX : CochainComplex.IsGE X.obj.as a)
    (c : Cocone (MorphismProperty.Under.forget (HomotopyCategory.Plus.quasiIso C) ⊤ X ⋙
      Under.forget X ⋙ (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)))
    (s : (HomotopyCategory.Plus.quasiIso C).Under ⊤ X)
    (r : c.pt ⟶ (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj s.right)
    (hr : r ≫ c.ι.app s = 𝟙 c.pt) :
    c.pt.IsGE a := by
  let G := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let W := HomotopyCategory.Plus.quasiIso C
  have hs : CochainComplex.IsGE s.right.obj.as a := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have hz : IsZero (X.obj.as.homology n) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact (CochainComplex.isGE_iff _ a).1 hX n hn
    have : IsIso ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map
        s.hom.hom) := s.prop n
    exact hz.of_iso
      (((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).app
          s.right.obj.as).symm ≪≫
        (asIso ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map
          s.hom.hom)).symm ≪≫
        (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).app X.obj.as)
  let Y : HomotopyCategory.Plus C :=
    (HomotopyCategory.Plus.quotient C).obj
      ⟨CochainComplex.truncGE s.right.obj.as a, ⟨a, inferInstance⟩⟩
  let q : s.right ⟶ Y := ObjectProperty.homMk
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (CochainComplex.πTruncGE s.right.obj.as a))
  have hq : HomotopyCategory.Plus.quasiIso C q :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      ((CochainComplex.quasiIso_πTruncGE_iff _ a).2 hs)
  let t : W.Under ⊤ X := MorphismProperty.Under.mk ⊤ (s.hom ≫ q) (W.comp_mem _ _ s.prop hq)
  let f : s ⟶ t := MorphismProperty.Under.homMk q rfl
  have hw : G.map q ≫ c.ι.app t = c.ι.app s := c.w f
  have hret : (r ≫ G.map q) ≫ c.ι.app t = 𝟙 c.pt :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hw).trans hr)
  have : CochainComplex.IsStrictlyGE Y.obj.as a :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      (CochainComplex.truncGE s.right.obj.as a) a)
  have : (G.obj Y).IsGE a := isGE_mapHomotopyCategoryPlus_obj F Y a
  exact isGE_of_retract_plus (r ≫ G.map q) (c.ι.app t) hret a

omit [HasDerivedCategory C] in
/-- If a complex computes its source derived functor, applying the additive functor
preserves its lower cohomological bound. -/
private lemma isGE_map_of_computesRightDerived
    (F : C ⥤ D) [F.Additive] (X : HomotopyCategory.Plus C) (a : ℤ)
    (hX : CochainComplex.IsGE X.obj.as a)
    (h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) X) :
    ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj X).IsGE a := by
  obtain ⟨c, ⟨s, r, hr, -⟩, hi⟩ := h
  have : c.pt.IsGE a := isGE_of_retraction F X a hX c s r hr
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    (@asIso _ _ ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj X) c.pt _ hi).symm a

omit [HasDerivedCategory C] in
private lemma source_computes_of_isZero (F : C ⥤ D) [F.Additive]
    {X : HomotopyCategory.Plus C} (hX : IsZero X) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) X := by
  let G := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let W := HomotopyCategory.Plus.quasiIso C
  have hZ : IsZero (G.obj X) := G.map_isZero hX
  let c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ G) :=
    { pt := G.obj X
      ι := { app t := G.map (0 : t.right ⟶ X)
             naturality := fun _ _ _ => hZ.eq_of_tgt _ _ } }
  let i₀ : W.Under ⊤ X := MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X)
  refine ⟨c, ⟨i₀, 𝟙 _, hZ.eq_of_src _ _, fun t => ?_⟩, hZ.isIso hZ _⟩
  exact ⟨i₀, MorphismProperty.Under.homMk (0 : t.right ⟶ X) (hX.eq_of_src _ _), 𝟙 _,
    hZ.eq_of_tgt _ _⟩

omit [HasDerivedCategory C] in
private lemma source_computes_of_distTriang (F : C ⥤ D) [F.Additive]
    (T : Pretriangulated.Triangle (HomotopyCategory.Plus C))
    (hT : T ∈ distTriang _) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) T.obj₃ →
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) T.obj₁ →
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) T.obj₂ := by
  have := quasiIsoPlus_compatible (C := C)
  exact (Functor.computesRightDerived_and_computesLeftDerived_of_distTriang _ _
    quasiIsoPlus_isSaturated T hT).2.2.1

omit [HasDerivedCategory C] in
private lemma source_computes_single (F : C ⥤ D) [F.Additive] (A : C)
    (hA : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj A))
    (n : ℤ) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C n).obj A) := by
  apply (derivedSituation F).computesRightDerived_of_iso
    (((HomotopyCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).app A)
  exact ((derivedSituation F).computesRightDerived_shift_iff _ (-n)).1 hA

omit [HasDerivedCategory C] in
private lemma source_acyclic_stupidTrunc (F : C ⥤ D) [F.Additive]
    {ι : Type*} {c : ComplexShape ι} (e : c.Embedding (ComplexShape.up ℤ)) [e.IsRelIff]
    (K : CochainComplex C ℤ)
    (hK : ∀ n, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X n))) (n : ℤ) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj ((K.stupidTrunc e).X n)) := by
  by_cases hn : ∃ i, e.f i = n
  · obtain ⟨i, hi⟩ := hn
    exact (derivedSituation F).computesRightDerived_of_iso
      ((HomotopyCategory.Plus.singleFunctor C 0).mapIso (K.stupidTruncXIso e hi).symm) (hK n)
  · exact source_computes_of_isZero F ((HomotopyCategory.Plus.singleFunctor C 0).map_isZero
      (K.isZero_stupidTrunc_X e n (by simpa using hn)))

omit [HasDerivedCategory C] in
private lemma source_computes_of_isZero_ne (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K) (a : ℤ)
    (hzero : ∀ i, i ≠ a → IsZero (K.X i))
    (hA : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X a))) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) (plusObj K hK) :=
  (derivedSituation F).computesRightDerived_of_iso (isoSingleFunctorObjPlus K hK a hzero).symm
    (source_computes_single F _ hA a)

omit [HasDerivedCategory C] in
private lemma source_computes_of_bounded_aux (F : C ⥤ D) [F.Additive] (m : ℕ) :
    ∀ (a : ℤ) (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K),
    (∀ i, (i < a ∨ a + m < i) → IsZero (K.X i)) →
    (∀ i, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X i))) →
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) (plusObj K hK) := by
  induction m with
  | zero =>
    intro a K hK hz ha
    apply source_computes_of_isZero_ne F K hK a (fun i hi => hz i ?_) (ha a)
    omega
  | succ m ih =>
    intro a K hK hz ha
    apply source_computes_of_distTriang F (stupidTruncTrianglehPlus K a hK)
      (stupidTruncTrianglehPlus_distinguished K a hK)
    · apply source_computes_of_isZero_ne F _ (plus_stupidTruncLE K hK a) a
        (fun i hi => ?_) (source_acyclic_stupidTrunc F _ K ha a)
      rcases lt_or_gt_of_ne hi with h | h
      · exact isZero_stupidTrunc_X_of_isZero K _ i (hz i (Or.inl h))
      · exact isZero_stupidTruncLE_X_of_lt K a i h
    · refine ih (a + 1) _ (plus_stupidTruncGE K (a + 1)) (fun i hi => ?_)
        (source_acyclic_stupidTrunc F _ K ha)
      rcases hi with hi | hi
      · exact isZero_stupidTruncGE_X_of_lt K (a + 1) i hi
      · exact isZero_stupidTrunc_X_of_isZero K _ i (hz i (Or.inr (by push_cast; omega)))

omit [HasDerivedCategory C] in
private lemma source_computes_of_bounded (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K) (a b : ℤ)
    (hz : ∀ i, (i < a ∨ b < i) → IsZero (K.X i))
    (ha : ∀ i, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X i))) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) (plusObj K hK) :=
  source_computes_of_bounded_aux F (b - a).toNat a K hK (fun i hi => hz i (by omega)) ha

omit [HasDerivedCategory C] in
/-- In a commutative square `a ≫ v = b ≫ d` of `D⁺(D)` with `d` invertible, if `H ⁱ` inverts `v`
and `b` then it inverts `a`. -/
private lemma isIso_homologyFunctor_map_of_comp_eq {X Y Y' Z : DerivedCategory.Plus D} (i : ℤ)
    (a : X ⟶ Y) (v : Y ⟶ Z) (b : X ⟶ Y') (d : Y' ⟶ Z) (h : a ≫ v = b ≫ d)
    (hv : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map v))
    (hb : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map b))
    (hd : IsIso d) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D i).map a) := by
  have : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map a ≫
      (DerivedCategory.Plus.homologyFunctor D i).map v) := by
    rw [← Functor.map_comp, h, Functor.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.homologyFunctor D i).map v)

omit [HasDerivedCategory C] in
/-- **Leray's acyclicity lemma**, [Stacks, Tag 015E], in Stacks' generality: `RF` is assumed to be
defined at `K` alone; no global existence of `RF` and no injectives are assumed.

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, and write
`G : K⁺(𝒜) ⥤ D⁺(ℬ)` for `F` applied termwise followed by the localization, and `W` for the
quasi-isomorphisms of `K⁺(𝒜)`. Let `K` be a bounded below complex all of whose terms `Kⁿ` are
right `F`-acyclic in the sense of [Stacks, Tag 0157]: `RF` is defined at `Kⁿ[0]` and `Kⁿ[0]`
computes `RF` ([Stacks, Tag 05SX]). Suppose `RF` is defined at `K` ([Stacks, Tag 05S9]: the
ind-object `(s : K ⟶ K') ↦ G(K')` is essentially constant). Then the canonical map
`F(K) ⟶ RF(K)` — the coprojection at the index `𝟙 K` of any value `RF(K)` — is an isomorphism
in `D⁺(ℬ)`; in particular `K` computes `RF`.

The proof is the source's: the bounded case is the induction along stupid truncations
(`source_computes_of_bounded`); in general, for each `i` the triangle
`(σ_{≥ i + 2}K, K, σ_{≤ i + 1}K)` has `RF` defined at its last two vertices, hence at the first,
with a distinguished triangle of values ([Stacks, Tag 05SC]), and `H ⁱ` of the canonical map at
`K` is compared with that at `σ_{≤ i + 1}K`, both `σ_{≥ i + 2}F(K)` and `RF(σ_{≥ i + 2}K)` being
concentrated in degrees `≥ i + 2`. -/
@[stacks 015E "`RF` defined at `K` in the sense of Tag 05S9, terms right `F`-acyclic in the sense \
  of Tag 0157; conclusion: the canonical map `F(K) ⟶ RF(K)` is an isomorphism"]
public theorem isIso_ι_app_of_computesRightDerived_single_of_isRightDerivedValueAt
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K)
    (hacyclic : ∀ n, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X n)))
    (hdef : ∃ c, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivedValueAt
      (HomotopyCategory.Plus.quasiIso C) (plusObj K hK) c) :
    (∀ c, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivedValueAt
        (HomotopyCategory.Plus.quasiIso C) (plusObj K hK) c →
      IsIso (c.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 (plusObj K hK))
        (MorphismProperty.id_mem _ _)))) ∧
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) (plusObj K hK) := by
  have := quasiIsoPlus_compatible (C := C)
  have hall : ∀ c, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivedValueAt
      (HomotopyCategory.Plus.quasiIso C) (plusObj K hK) c →
      IsIso (c.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 (plusObj K hK))
        (MorphismProperty.id_mem _ _))) := by
    intro c hc
    obtain ⟨b, hb⟩ : ∃ b, CochainComplex.IsStrictlyGE K b := id hK
    refine (DerivedCategory.Plus.isIso_iff _).2 fun i ↦ ?_
    have hT := stupidTruncTrianglehPlus_distinguished K (i + 1) hK
    -- the last vertex `σ_{≤ i + 1}K` is bounded, so it computes `RF`
    obtain ⟨cZ, hcZ, hcZι⟩ := source_computes_of_bounded F _
      (plus_stupidTruncLE K hK (i + 1)) b (i + 1) (fun n hn ↦ by
        rcases hn with hn | hn
        · exact isZero_stupidTrunc_X_of_isZero K _ n
            ((CochainComplex.isStrictlyGE_iff K b).1 hb n hn)
        · exact isZero_stupidTruncLE_X_of_lt K (i + 1) n hn)
      (source_acyclic_stupidTrunc F _ K hacyclic)
    have hsol := exists_isRightDerivedValueAt_and_isLeftDerivedValueAt_and_triangle_distinguished
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) (HomotopyCategory.Plus.quasiIso C)
      quasiIsoPlus_isSaturated _ hT
    -- so `RF` is defined at the first vertex `σ_{≥ i + 2}K`, with a triangle of values
    obtain ⟨cX, hcX⟩ := hsol.1.2.1 ⟨c, hc⟩ ⟨cZ, hcZ⟩
    obtain ⟨u, v, w, hdist, -, hv, -⟩ := hsol.1.2.2.2 cX hcX c hc cZ hcZ
    have hcomm := hv (MorphismProperty.Under.mk ⊤ (𝟙 _) (MorphismProperty.id_mem _ _))
      (MorphismProperty.Under.mk ⊤ (𝟙 _) (MorphismProperty.id_mem _ _))
      (stupidTruncTrianglehPlus K (i + 1) hK).mor₂ (by simp)
    have hge : CochainComplex.IsStrictlyGE
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE (i + 1 + 1))) (i + 1 + 1) :=
      isStrictlyGE_stupidTruncGE K (i + 1 + 1)
    -- `RF(σ_{≥ i + 2}K)` lies in degrees `≥ i + 2`, being a retract of `F` of a resolution
    have hcX_ge : cX.pt.IsGE (i + 1 + 1) := by
      obtain ⟨s, r, hr, -⟩ := hcX
      exact isGE_of_retraction F _ (i + 1 + 1) (inferInstanceAs (CochainComplex.IsGE
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE (i + 1 + 1))) (i + 1 + 1))) cX s r hr
    have h₁ : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map v) :=
      isIso_homologyFunctor_map_mor₂_of_isGE (Pretriangulated.Triangle.mk u v w) hdist i hcX_ge
    have h₂ : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map
        ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map
          (stupidTruncTrianglehPlus K (i + 1) hK).mor₂)) :=
      isIso_homologyFunctor_map_mor₂_of_isGE _
        ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map_distinguished _ hT) i
        (isGE_Phi_obj F _ (plus_stupidTruncGE K (i + 1 + 1)) (i + 1 + 1) hge)
    exact isIso_homologyFunctor_map_of_comp_eq i _ v _ _ hcomm h₁ h₂ hcZι
  obtain ⟨c, hc⟩ := hdef
  exact ⟨hall, c, hc, hall c hc⟩

omit [HasDerivedCategory C] [HasDerivedCategory D] in
private lemma quasiIsoAt_of_isIso_f {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ)
    (h : ∀ i, n - 1 ≤ i → i ≤ n + 1 → IsIso (f.f i)) : QuasiIsoAt f n := by
  rw [quasiIsoAt_iff]
  have h₁ : IsIso (((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map f).τ₁) :=
    h _ (by simp) (by rw [CochainComplex.prev]; omega)
  have h₂ : IsIso (((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map f).τ₂) :=
    h _ (by omega) (by omega)
  have h₃ : IsIso (((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map f).τ₃) :=
    h _ (by rw [CochainComplex.next]; omega) (by simp)
  have := ShortComplex.isIso_of_isIso
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map f)
  infer_instance

omit [HasDerivedCategory C] in
private lemma isGE_mapComplex_of_isGE_mapPlus (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K) (a : ℤ)
    (h : ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj (plusObj K hK)).IsGE a) :
    CochainComplex.IsGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a := by
  rw [← DerivedCategory.isGE_Q_obj_iff]
  have h' := (DerivedCategory.Plus.isGE_ι_obj_iff _ a).2 h
  have : (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))).IsGE a := h'
  let e := (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K
  let e' := DerivedCategory.Qh.mapIso e ≪≫ (DerivedCategory.quotientCompQhIso D).app _
  have : DerivedCategory.TStructure.t.IsGE
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) a := h'
  exact DerivedCategory.TStructure.t.isGE_of_iso e' a

omit [HasDerivedCategory C] in
private lemma map_acyclic_of_source_acyclic_terms (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K) (hac : K.Acyclic)
    (ha : ∀ i, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X i))) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  intro n
  let L := K.stupidTrunc (ComplexShape.embeddingUpIntLE (n + 1))
  let q : K ⟶ L := K.πStupidTrunc _
  have hq (i : ℤ) (hi : i ≤ n + 1) : IsIso (q.f i) :=
    K.isIso_πStupidTrunc_f _ (i := (n + 1 - i).toNat)
      (by rw [embeddingUpIntLE_f']; omega)
  have hL : CochainComplex.IsGE L (n + 1) := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    have : QuasiIsoAt q i := quasiIsoAt_of_isIso_f q i (fun j hj hj' => hq j (by omega))
    exact (exactAt_iff_of_quasiIsoAt q i).1 (hac i)
  obtain ⟨a, hge⟩ := hK
  have hK : CochainComplex.plus C K := ⟨a, hge⟩
  have hc : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) (plusTruncLE K (n + 1) hK) := by
    refine source_computes_of_bounded F L (plus_stupidTruncLE K hK (n + 1)) a (n + 1)
      (fun i hi => ?_) (source_acyclic_stupidTrunc F _ K ha)
    rcases hi with hi | hi
    · exact isZero_stupidTrunc_X_of_isZero K _ i
        ((CochainComplex.isStrictlyGE_iff K a).1 hge i hi)
    · exact isZero_stupidTruncLE_X_of_lt K (n + 1) i hi
  have hFL := isGE_map_of_computesRightDerived F (plusTruncLE K (n + 1) hK) (n + 1)
    hL hc
  have hFL' := isGE_mapComplex_of_isGE_mapPlus F L (plus_stupidTruncLE K hK (n + 1)) (n + 1) hFL
  have : QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) n := by
    apply quasiIsoAt_of_isIso_f
    intro i hi hi'
    have := hq i hi'
    exact inferInstanceAs (IsIso (F.map (q.f i)))
  exact (exactAt_iff_of_quasiIsoAt ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) n).2
    ((CochainComplex.isGE_iff _ _).1 hFL' n (by omega))

omit [HasDerivedCategory C] in
private lemma source_acyclic_biprod (F : C ⥤ D) [F.Additive] (X Y : C)
    (hX : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj X))
    (hY : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj Y)) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (X ⊞ Y)) := by
  apply (derivedSituation F).computesRightDerived_of_iso
    ((HomotopyCategory.Plus.singleFunctor C 0).mapBiprod X Y).symm
  exact source_computes_of_distTriang F _
    (Pretriangulated.binaryBiproductTriangle_distinguished _ _) hY hX

/-- A morphism is a quasi-isomorphism iff its mapping cone is acyclic. -/
private lemma quasiIso_iff_acyclic_mappingCone {E : Type*} [Category* E] [Abelian E]
    {X Y : CochainComplex E ℤ} (φ : X ⟶ Y) :
    QuasiIso φ ↔ (CochainComplex.mappingCone φ).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    ← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact ObjectProperty.trW_iff_of_distinguished _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)

omit [HasDerivedCategory C] in
/-- The mapping cone of a quasi-isomorphism is acyclic. -/
public lemma acyclic_mappingCone {X Y : CochainComplex C ℤ} (φ : X ⟶ Y) (h : QuasiIso φ) :
    (CochainComplex.mappingCone φ).Acyclic :=
  (quasiIso_iff_acyclic_mappingCone φ).1 h

omit [HasDerivedCategory C] in
/-- Conversely, a morphism whose mapping cone is acyclic is a quasi-isomorphism: the same
triangle, read in the other direction. -/
public lemma quasiIso_of_acyclic_mappingCone {X Y : CochainComplex C ℤ} (φ : X ⟶ Y)
    (h : (CochainComplex.mappingCone φ).Acyclic) : QuasiIso φ :=
  (quasiIso_iff_acyclic_mappingCone φ).2 h

omit [HasDerivedCategory C] in
private lemma plus_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (mappingCone f) := by
  obtain ⟨a, ha⟩ := hK
  obtain ⟨b, hb⟩ := hL
  exact ⟨min (a - 1) b, isStrictlyGE_mappingCone f a b _ (by omega) (by omega)⟩

omit [HasDerivedCategory C] in
private lemma source_acyclic_terms_mappingCone (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : ∀ i, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X i)))
    (hL : ∀ i, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (L.X i))) :
    ∀ i, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj ((mappingCone f).X i)) := by
  intro i
  have heq : (mappingCone f).X i = (K.X ((ComplexShape.up ℤ).next i) ⊞ L.X i) :=
    dite_eq_left (by simp)
  rw [heq]
  exact source_acyclic_biprod F _ _ (hK _) (hL i)

omit [HasDerivedCategory C] in
private lemma map_quasiIso_of_source_acyclic_terms (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (hf : QuasiIso f)
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L)
    (haK : ∀ i, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X i)))
    (haL : ∀ i, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (L.X i))) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have hc := map_acyclic_of_source_acyclic_terms F (mappingCone f)
    (plus_mappingCone f hK hL) (acyclic_mappingCone f hf)
    (source_acyclic_terms_mappingCone F f haK haL)
  apply quasiIso_of_acyclic_mappingCone
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hc i).isZero_homology.of_iso
    (((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i).mapIso
      (mappingCone.mapHomologicalComplexIso f F)).symm)

omit [HasDerivedCategory C] in
private lemma source_acyclic_resolution (F : C ⥤ D) [F.Additive]
    (h : ∀ X : C, ∃ (Y : C) (i : X ⟶ Y), Mono i ∧
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj Y))
    (X : HomotopyCategory.Plus C) (a : ℤ) (hX : CochainComplex.IsGE X.obj.as a) :
    ∃ (Y : HomotopyCategory.Plus C) (r : X ⟶ Y),
      HomotopyCategory.Plus.quasiIso C r ∧
      (∀ n, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
          (HomotopyCategory.Plus.quasiIso C)
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (Y.obj.as.X n))) ∧
      CochainComplex.IsStrictlyGE Y.obj.as a := by
  let I : ObjectProperty C := fun A =>
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C)
    ((HomotopyCategory.Plus.singleFunctor C 0).obj A)
  have hI : ∀ A : C, ∃ (B : C) (_ : I B) (i : A ⟶ B), Mono i := by
    intro A
    obtain ⟨B, i, hi, hB⟩ := h A
    exact ⟨B, hB, i, hi⟩
  have : I.ContainsZero := ⟨0, isZero_zero C,
    source_computes_of_isZero F ((HomotopyCategory.Plus.singleFunctor C 0).map_isZero
      (isZero_zero C))⟩
  obtain ⟨N, r, hr, hIN, _, hn⟩ := CochainComplex.exists_quasiIso_prop_isStrictlyGE I hI a X.obj.as
  let Y : HomotopyCategory.Plus C := plusObj N ⟨a, hn⟩
  exact ⟨Y, ObjectProperty.homMk ((HomotopyCategory.quotient C _).map r),
    (HomotopyCategory.quotient_map_mem_quasiIso_iff r).2 hr, hIN, hn⟩

/-- Objects of `K⁺(E)` are bounded below complexes. -/
private lemma plus_obj_as {E : Type*} [Category* E] [Abelian E] (X : HomotopyCategory.Plus E) :
    CochainComplex.plus E X.obj.as :=
  (HomotopyCategory.plus_quotient_obj_iff X.obj.as).1 X.property

omit [HasDerivedCategory C] in
private lemma source_acyclic_derivability (F : C ⥤ D) [F.Additive]
    (h : ∀ X : C, ∃ (Y : C) (i : X ⟶ Y), Mono i ∧
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj Y)) :
    let P : ObjectProperty (HomotopyCategory.Plus C) := fun X => ∀ n,
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
          (HomotopyCategory.Plus.quasiIso C)
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (X.obj.as.X n))
    let Φ := LocalizerMorphism.ofEq (F := P.ι)
      (W₁ := (HomotopyCategory.Plus.quasiIso C).inverseImage P.ι) rfl
    Φ.IsRightDerivabilityStructure ∧
      Φ.Derives (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) := by
  let P : ObjectProperty (HomotopyCategory.Plus C) := fun X => ∀ n,
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (X.obj.as.X n))
  let W := HomotopyCategory.Plus.quasiIso C
  let Φ := LocalizerMorphism.ofEq (F := P.ι) (W₁ := W.inverseImage P.ι) rfl
  have := quasiIsoPlus_isSaturated (C := C) |>.hasLeftCalculusOfFractions
  have hΦ : Φ.IsRightDerivabilityStructure := rightDerivability_of_resolutions W P (by
    intro X
    obtain ⟨a, ha⟩ := plus_obj_as X
    obtain ⟨Y, r, hr, hY, _⟩ := source_acyclic_resolution F h X a inferInstance
    exact ⟨Y, hY, r, hr⟩)
  refine ⟨hΦ, ?_⟩
  intro X Y f hf
  have hq : QuasiIso f.hom.hom.out :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1
      (by rwa [HomotopyCategory.quotient_map_out])
  have hF := map_quasiIso_of_source_acyclic_terms F f.hom.hom.out hq
    (plus_obj_as X.obj) (plus_obj_as Y.obj) X.property Y.property
  have key : HomotopyCategory.quasiIso D _ ((F.mapHomotopyCategory _).map
      ((HomotopyCategory.quotient C _).map f.hom.hom.out)) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hF
  rw [HomotopyCategory.quotient_map_out] at key
  exact Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)
    (F.mapHomotopyCategoryPlus.map f.hom) key

private noncomputable def mappingConeTrianglePlus {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L) :
    Pretriangulated.Triangle (HomotopyCategory.Plus C) :=
  Pretriangulated.Triangle.mk
    (ObjectProperty.homMk (X := plusObj K hK) (Y := plusObj L hL)
      ((HomotopyCategory.quotient C _).map f))
    (ObjectProperty.homMk (X := plusObj L hL)
      (Y := plusObj (mappingCone f) (plus_mappingCone f hK hL))
      ((HomotopyCategory.quotient C _).map (mappingCone.inr f)))
    (ObjectProperty.homMk
      (X := plusObj (mappingCone f) (plus_mappingCone f hK hL))
      (Y := (plusObj K hK)⟦(1 : ℤ)⟧)
      ((mappingCone.triangleh f).mor₃ ≫
        ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ)).inv.app (plusObj K hK)))

omit [HasDerivedCategory C] in
private lemma mappingConeTrianglePlus_distinguished {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L) :
    mappingConeTrianglePlus f hK hL ∈ distTriang _ := by
  rw [← Functor.map_distinguished_iff (HomotopyCategory.Plus.ι C)]
  refine Pretriangulated.isomorphic_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished f) _
    (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have h : (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map
        (Iso.refl (((HomotopyCategory.Plus.ι C).mapTriangle.obj
          (mappingConeTrianglePlus f hK hL)).obj₁)).hom = 𝟙 _ := by simp
    have h₂ : ((mappingCone.triangleh f).mor₃ ≫
        ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ)).inv.app (plusObj K hK)) ≫
        ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ)).hom.app (plusObj K hK) =
        (mappingCone.triangleh f).mor₃ :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun g => (mappingCone.triangleh f).mor₃ ≫ g)
          (Iso.inv_hom_id_app ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ))
            (plusObj K hK))).trans (Category.comp_id _))
    exact (congrArg (fun g => ((HomotopyCategory.Plus.ι C).mapTriangle.obj
        (mappingConeTrianglePlus f hK hL)).mor₃ ≫ g) h).trans
      ((Category.comp_id _).trans (h₂.trans (Category.id_comp _).symm))

private lemma isTriangulated_of_source_comparison (F : C ⥤ D) [F.Additive]
    (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.CommShift ℤ] [NatTrans.CommShift α ℤ]
    (hres : let P : ObjectProperty (HomotopyCategory.Plus C) := fun X => ∀ n,
              (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
                (HomotopyCategory.Plus.quasiIso C)
                ((HomotopyCategory.Plus.singleFunctor C 0).obj (X.obj.as.X n))
      (LocalizerMorphism.ofEq (F := P.ι)
        (W₁ := (HomotopyCategory.Plus.quasiIso C).inverseImage P.ι)
          rfl).IsRightDerivabilityStructure)
    (hα : ∀ X : HomotopyCategory.Plus C,
      (∀ n, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
          (HomotopyCategory.Plus.quasiIso C)
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (X.obj.as.X n))) → IsIso (α.app X)) :
    RF.IsTriangulated := by
  let P : ObjectProperty (HomotopyCategory.Plus C) := fun X => ∀ n,
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (X.obj.as.X n))
  let Φ := LocalizerMorphism.ofEq (F := P.ι)
    (W₁ := (HomotopyCategory.Plus.quasiIso C).inverseImage P.ι) rfl
  have : Φ.IsRightDerivabilityStructure := hres
  have hP : ∀ X : HomotopyCategory.Plus C,
      ∃ (Y : HomotopyCategory.Plus C) (_ : P Y) (r : X ⟶ Y),
        HomotopyCategory.Plus.quasiIso C r := by
    intro X
    let R : Φ.RightResolution X := Classical.arbitrary _
    exact ⟨R.X₁.obj, R.X₁.property, R.w, R.hw⟩
  have := quasiIsoPlus_isSaturated (C := C) |>.hasLeftCalculusOfFractions
  have : Φ.arrow.HasRightResolutions :=
    hasRightResolutions_arrow_of_resolutions (HomotopyCategory.Plus.quasiIso C) P hP
  have : (P.ι ⋙ DerivedCategory.Plus.Qh).mapArrow.EssSurj :=
    LocalizerMorphism.essSurj_mapArrow_functor_comp Φ _
  apply RF.isTriangulated_of_leftExtension α
  intro X Y f
  let g := (P.ι ⋙ DerivedCategory.Plus.Qh).mapArrow.objPreimage (Arrow.mk f)
  let e := (P.ι ⋙ DerivedCategory.Plus.Qh).mapArrow.objObjPreimageIso (Arrow.mk f)
  let T := mappingConeTrianglePlus g.hom.hom.hom.out (plus_obj_as g.left.obj)
    (plus_obj_as g.right.obj)
  refine ⟨T, mappingConeTrianglePlus_distinguished _ _ _, hα _ g.left.property,
    hα _ g.right.property, hα _ (source_acyclic_terms_mappingCone F _
      g.left.property g.right.property), ?_⟩
  have heq : T.mor₁ = g.hom.hom :=
    ObjectProperty.hom_ext _ (HomotopyCategory.quotient_map_out g.hom.hom.hom)
  rw [heq]
  rw [Functor.mapArrow_obj, Functor.comp_map, ObjectProperty.ι_map] at e
  exact ⟨e⟩

/-- The unit of a right derived functor is invertible on complexes with acyclic terms. -/
private lemma isIso_unit_of_source_acyclic_terms (F : C ⥤ D) [F.Additive]
    (h : ∀ X : C, ∃ (Y : C) (i : X ⟶ Y), Mono i ∧
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj Y))
    (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)]
    (X : HomotopyCategory.Plus C)
    (hX : ∀ n, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (X.obj.as.X n))) :
    IsIso (α.app X) := by
  obtain ⟨hΦ, hd⟩ := source_acyclic_derivability F h
  have := hΦ
  exact hd.isIso_of_isRightDerivedFunctor α ⟨X, hX⟩

private lemma isGE_derived_of_source_resolutions (F : C ⥤ D) [F.Additive]
    (h : ∀ X : C, ∃ (Y : C) (i : X ⟶ Y), Mono i ∧
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj Y))
    (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    (hα : ∀ X : HomotopyCategory.Plus C,
      (∀ n, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
          (HomotopyCategory.Plus.quasiIso C)
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (X.obj.as.X n))) → IsIso (α.app X))
    (X : HomotopyCategory.Plus C) (a : ℤ) (hX : CochainComplex.IsGE X.obj.as a) :
    (RF.obj (DerivedCategory.Plus.Qh.obj X)).IsGE a := by
  obtain ⟨Y, r, hr, hY, hge⟩ := source_acyclic_resolution F h X a hX
  have := hα Y hY
  have := Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) r hr
  have := isGE_mapHomotopyCategoryPlus_obj F Y a
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    (asIso (α.app Y) ≪≫ (RF.mapIso (asIso (DerivedCategory.Plus.Qh.map r))).symm) a


/-- Enough source acyclic objects: `RF` is defined on all of `K⁺(C)`, it is triangulated, and a
bounded below complex of right acyclic objects computes it. -/
@[sga "4 XVII 1.2.7"]
public theorem hasRightDerivedFunctor_of_enough_source_acyclic_objects (F : C ⥤ D) [F.Additive]
    (h : ∀ X : C, ∃ (Y : C) (i : X ⟶ Y), Mono i ∧
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj Y)) :
    ∃ h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso C),
      letI := h
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
          DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).IsTriangulated ∧
        ∀ X : HomotopyCategory.Plus C,
          (∀ n : ℤ, F.rightAcyclic (X.obj.as.X n)) →
            IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
              DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app X) := by
  let P : ObjectProperty (HomotopyCategory.Plus C) := fun X => ∀ n,
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (X.obj.as.X n))
  let W := HomotopyCategory.Plus.quasiIso C
  let Φ := LocalizerMorphism.ofEq (F := P.ι) (W₁ := W.inverseImage P.ι) rfl
  let G := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  obtain ⟨hΦ, hd⟩ := source_acyclic_derivability F h
  have : Φ.IsRightDerivabilityStructure := hΦ
  have hRF := hd.hasPointwiseRightDerivedFunctor
  let RF := G.totalRightDerived DerivedCategory.Plus.Qh W
  let α := G.totalRightDerivedUnit DerivedCategory.Plus.Qh W
  have hα := isIso_unit_of_source_acyclic_terms F h RF α
  have htri : RF.IsTriangulated := isTriangulated_of_source_comparison F RF α hΦ hα
  refine ⟨hRF, htri, ?_⟩
  intro X hX
  exact isIso_app_of_plus F (fun L hL a ha ↦
      have := ha
      isGE_derived_of_source_resolutions F h RF α hα (plusObj L hL) a
        (inferInstance : CochainComplex.IsGE L a))
    X.obj.as (plus_obj_as X) hX

/-- Enough source acyclic objects: every right derived functor `(RF, α)` of `F` on `D⁺` is computed
by bounded below complexes whose terms have single complexes computing `RF` in the sense of
Stacks 05SX, and it sends a complex concentrated in degrees `≥ a` to an object of `D⁺(D)` whose
homology vanishes in degrees `< a`. -/
public theorem isIso_unit_and_isGE_of_enough_source_acyclic_objects (F : C ⥤ D) [F.Additive]
    (h : ∀ X : C, ∃ (Y : C) (i : X ⟶ Y), Mono i ∧
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj Y))
    (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)] :
    (∀ X : HomotopyCategory.Plus C,
      (∀ n, (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (X.obj.as.X n))) →
      IsIso (α.app X)) ∧
    (∀ (X : HomotopyCategory.Plus C) (a : ℤ), CochainComplex.IsGE X.obj.as a →
      (RF.obj (DerivedCategory.Plus.Qh.obj X)).IsGE a) := by
  have hα := isIso_unit_of_source_acyclic_terms F h RF α
  exact ⟨hα, isGE_derived_of_source_resolutions F h RF α hα⟩

/-- Enough source acyclic objects: for every right derived functor `(RF, α)` of `F` on `D⁺`, a
bounded below complex `X` computes `RF` in the sense of Stacks 05SX — the resolution ind-object
of `X` is essentially constant with invertible canonical map — exactly when `α` is invertible
at `X`. -/
public theorem computesRightDerived_iff_isIso_unit_of_enough_source_acyclic_objects
    (F : C ⥤ D) [F.Additive]
    (h : ∀ X : C, ∃ (Y : C) (i : X ⟶ Y), Mono i ∧
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj Y))
    (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)]
    (X : HomotopyCategory.Plus C) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) X ↔ IsIso (α.app X) := by
  have := quasiIsoPlus_isSaturated (C := C) |>.hasLeftCalculusOfFractions
  refine computesRightDerived_iff_isIso_app _ DerivedCategory.Plus.Qh RF _ α X fun K => ?_
  obtain ⟨a, ha⟩ := plus_obj_as K
  obtain ⟨I, s, hs, hI, _⟩ := source_acyclic_resolution F h K a inferInstance
  exact ⟨I, s, hs, (isIso_unit_and_isGE_of_enough_source_acyclic_objects F h RF α).1 I hI⟩

omit [HasDerivedCategory C] in
/-- The quasi-isomorphisms of `K⁺(C)` form a saturated multiplicative system compatible with the
triangulation ([Stacks, Tag 05RT]). -/
public theorem isSaturated_and_isCompatibleWithTriangulation_quasiIsoPlus :
    (HomotopyCategory.Plus.quasiIso C).IsSaturated ∧
      (HomotopyCategory.Plus.quasiIso C).IsCompatibleWithTriangulation :=
  ⟨quasiIsoPlus_isSaturated, quasiIsoPlus_compatible⟩

omit [HasDerivedCategory C] in
/-- **Right derived functors move to the right, on `K⁺`** ([Stacks, Tag 05TC] part (1)). If the
right derived functor of `K⁺(F) ⋙ Q : K⁺(C) ⥤ D⁺(D)` is defined at `X` with value `c.pt`, and
`H ⁱ(X) = 0` for `i < a`, then `H ⁱ(c.pt) = 0` for `i < a`: the value is a retract of `F` applied
to a resolution of `X`, which good truncation makes termwise `≥ a`. -/
public theorem isGE_of_isRightDerivedValueAt_plus (F : C ⥤ D) [F.Additive]
    (X : HomotopyCategory.Plus C) (a : ℤ) (hX : CochainComplex.IsGE X.obj.as a)
    (c : Cocone (MorphismProperty.Under.forget (HomotopyCategory.Plus.quasiIso C) ⊤ X ⋙
      Under.forget X ⋙ (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)))
    (hc : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivedValueAt
      (HomotopyCategory.Plus.quasiIso C) X c) :
    c.pt.IsGE a := by
  obtain ⟨s, r, hr, -⟩ := hc
  exact isGE_of_retraction F X a hX c s r hr

variable [HasDerivedCategory.{w} Cᵒᵖ] [HasDerivedCategory.{w'} Dᵒᵖ]

/-- **Stacks 05TA.** Let `F : C ⥤ D` be an additive functor of abelian categories.

1. If every object of `C` injects into an object `Y` acyclic for `RF` — that is, `Y[0]`
   computes the right derived functor of `K⁺(C) ⥤ D⁺(D)` in the sense of [Stacks, Tag 05SX],
   with no global existence of `RF` assumed — then `RF` is defined on all of `K⁺(C)`, the
   resulting functor `RF : D⁺(C) ⥤ D⁺(D)` is exact (triangulated), and every bounded below
   complex whose terms are acyclic for `RF` computes `RF`: the unit of `RF` is invertible there.
2. Dually, if every object of `C` is a quotient of an object acyclic for `LF`, then `LF` is
   defined on all of `K⁻(C)`, is exact, and is computed by bounded above complexes of objects
   acyclic for `LF`.

Part (2) is stated through opposite categories, as in [Stacks, Tag 0157]: `K⁻(C)` is `K⁺(Cᵒᵖ)`,
`LF` is the right derived functor of `F.op`, and acyclicity for `LF` is right acyclicity for
`F.op`. -/
@[stacks 05TA, sga "4 XVII 1.2.7"]
public theorem hasDerivedFunctors_of_enough_acyclic_objects (F : C ⥤ D) [F.Additive] :
    ((∀ X : C, ∃ (Y : C) (i : X ⟶ Y), Mono i ∧
        (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
          (HomotopyCategory.Plus.quasiIso C)
          ((HomotopyCategory.Plus.singleFunctor C 0).obj Y)) →
      ∃ h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
          (HomotopyCategory.Plus.quasiIso C),
        letI := h
        ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
            DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).IsTriangulated ∧
          ∀ X : HomotopyCategory.Plus C,
            (∀ n : ℤ, F.rightAcyclic (X.obj.as.X n)) →
              IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
                DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app X)) ∧
    ((∀ X : C, ∃ (Y : C) (p : Y ⟶ X), Epi p ∧
        (F.op.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
          (HomotopyCategory.Plus.quasiIso Cᵒᵖ)
          ((HomotopyCategory.Plus.singleFunctor Cᵒᵖ 0).obj (Opposite.op Y))) →
      ∃ h : (F.op.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
          (HomotopyCategory.Plus.quasiIso Cᵒᵖ),
        letI := h
        ((F.op.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
            DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso Cᵒᵖ)).IsTriangulated ∧
          ∀ X : HomotopyCategory.Plus Cᵒᵖ,
            (∀ n : ℤ, F.op.rightAcyclic (X.obj.as.X n)) →
              IsIso (((F.op.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
                DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso Cᵒᵖ)).app X)) := by
  refine ⟨hasRightDerivedFunctor_of_enough_source_acyclic_objects F, fun h ↦
    hasRightDerivedFunctor_of_enough_source_acyclic_objects F.op fun X ↦ ?_⟩
  obtain ⟨Y, p, hp, hY⟩ := h X.unop
  exact ⟨Opposite.op Y, p.op, inferInstance, hY⟩

end Resolutions

end AcyclicResolutions

end CategoryTheory.Functor

end
