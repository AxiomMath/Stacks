module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Limits.ProperFinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.H.Coverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Refining an h covering of an affine scheme by a covering of finite presentation

An h covering of an affine scheme is refined by a finite family of affine opens of a single
proper surjective morphism of finite presentation onto that scheme.

## Main results

* `AlgebraicGeometry.exists_finitePresentation_proper_refinement_of_isHCovering`:
  **Stacks 0ETU**.

## Implementation notes

Finite presentation is `AlgebraicGeometry.FinitePresentation`, as elsewhere in this
development. The finite affine open covering of the source is given by open immersions from
affine schemes whose ranges cover it, and refinement means that each member factors through
some member of the given h covering over the base.

Over the affine open `⊤` the ph-covering condition supplies a proper surjection onto the base
together with a finite affine open cover of its source refining the given family; the only
missing property is finite presentation. Writing that proper surjection as a directed inverse
limit of proper morphisms of finite presentation ([Stacks, Tag 09ZR]) with closed immersions
for transition morphisms, the finite affine open cover descends to some stage
(`AlgebraicGeometry.Scheme.exists_isOpenCover_and_isAffine_of_finite`) and, local finite
presentation of the members of the h covering being what the functorial criterion needs, the
refinement morphisms descend to a possibly later stage
(`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`), applied to
the limit presentation of each descended open. A cofiltered lower bound for the finitely many
resulting stages gives one stage carrying all of the data.

## References

* [Stacks Project, Tag 0ETU](https://stacks.math.columbia.edu/tag/0ETU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- A morphism from the preimage in the limit of an affine open `V₀` of a stage to a scheme
locally of finite presentation over `T` descends to the preimage of `V₀` at every sufficiently
late stage. -/
public theorem Scheme.exists_preimage_lift_of_locallyOfFinitePresentation
    {K : Type u} [Category.{u} K] [IsCofiltered K] {D : K ⥤ Scheme.{u}}
    [∀ {i j : K} (m : i ⟶ j), IsAffineHom (D.map m)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {T X : Scheme.{u}} (t : D ⟶ (Functor.const K).obj T)
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ T) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (f : X ⟶ T) [LocallyOfFinitePresentation f] {i₀ : K} (V₀ : (D.obj i₀).Opens)
    (hV₀ : IsAffineOpen V₀) (a : (c.π.app i₀ ⁻¹ᵁ V₀).toScheme ⟶ X)
    (ha : a ≫ f = (c.π.app i₀ ⁻¹ᵁ V₀).ι ≫ p) :
    ∃ q : Over i₀, ∀ q' : Over i₀, (q' ⟶ q) →
      ∃ b : (D.map q'.hom ⁻¹ᵁ V₀).toScheme ⟶ X,
        b ≫ f = (D.map q'.hom ⁻¹ᵁ V₀).ι ≫ t.app q'.left := by
  let A := opensDiagram D i₀ V₀
  let C := opensCone D c i₀ V₀
  let t' : A ⟶ (Functor.const (Over i₀)).obj T :=
    opensDiagramι D i₀ V₀ ≫ (Over.forget i₀).whiskerLeft t
  have (q : Over i₀) : CompactSpace (A.obj q) := isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := D.map q.hom) _ V₀.2 hV₀.isCompact)
  have (q : Over i₀) : QuasiSeparatedSpace (A.obj q) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map q.hom ⁻¹ᵁ V₀).2).mp
      (.of_quasiSeparatedSpace _)
  have hA : C.π ≫ t' = (Functor.const (Over i₀)).map (a ≫ f) := by
    ext q
    have he : c.π.app i₀ ⁻¹ᵁ V₀ ≤ c.π.app q.left ⁻¹ᵁ (D.map q.hom ⁻¹ᵁ V₀) := by
      rw [← Scheme.Hom.comp_preimage, c.w]
    have hr : (c.π.app i₀ ⁻¹ᵁ V₀).ι ≫ c.π.app q.left =
        C.π.app q ≫ (opensDiagramι D i₀ V₀).app q := by
      dsimp only [C]
      simp only [opensCone_π_app, opensDiagramι_app]
      exact (Scheme.Hom.resLE_comp_ι (f := c.π.app q.left)
        (U := D.map q.hom ⁻¹ᵁ V₀) (V := c.π.app i₀ ⁻¹ᵁ V₀) he).symm
    show C.π.app q ≫ (opensDiagramι D i₀ V₀).app q ≫ t.app q.left = a ≫ f
    rw [ha, ← hp q.left, ← Category.assoc, ← hr]
    exact Category.assoc _ _ _
  obtain ⟨q, b, -, hbf⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    A t' f C (isLimitOpensCone D c hc i₀ V₀) a hA
  refine ⟨q, fun q' m => ⟨A.map m ≫ b, ?_⟩⟩
  show (A.map m ≫ b) ≫ f = t'.app q'
  rw [Category.assoc, hbf]
  exact t'.naturality m

/-- A finite affine open cover of the source of a proper surjection `g : Y ⟶ T` onto an affine
scheme, each member of which factors over `T` through a member of a family locally of finite
presentation, descends to a proper surjection of finite presentation onto `T`. -/
public theorem exists_finitePresentation_proper_refinement_of_isProper
    {T : Scheme.{u}} [IsAffine T] {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    [∀ i, LocallyOfFinitePresentation (f i)] {Y : Scheme.{u}} (g : Y ⟶ T) [IsProper g]
    [Surjective g] {J : Type u} [Finite J] {Z : J → Scheme.{u}} [∀ k, IsAffine (Z k)]
    (j₀ : ∀ k, Z k ⟶ Y) [∀ k, IsOpenImmersion (j₀ k)]
    (hcover : (⋃ k, Set.range (j₀ k)) = Set.univ) (σ : J → I) (a : ∀ k, Z k ⟶ X (σ k))
    (ha : ∀ k, a k ≫ f (σ k) = j₀ k ≫ g) :
    ∃ (Y' : Scheme.{u}) (p : Y' ⟶ T) (V : J → Scheme.{u}) (j : ∀ k, V k ⟶ Y'),
      IsProper p ∧ Surjective p ∧ FinitePresentation p ∧ (∀ k, IsAffine (V k)) ∧
        (∀ k, IsOpenImmersion (j k)) ∧ (⋃ k, Set.range (j k)) = Set.univ ∧
        (∀ k, ∃ h : V k ⟶ X (σ k), h ≫ f (σ k) = j k ≫ p) := by
  classical
  obtain ⟨K, _, _, _, D, t, pcone, hc, hcompat, hstage, htrans, -⟩ :=
    exists_isLimit_isProper_finitePresentation_isClosedImmersion g
  let c : Cone D := Cone.mk Y pcone
  have : ∀ {i j : Kᵒᵖ} (m : i ⟶ j), IsAffineHom (D.map m) := fun m =>
    have := htrans _ _ m
    inferInstance
  have (i : Kᵒᵖ) : CompactSpace (D.obj i) := by
    have : QuasiCompact (t.app i) := (hstage i).2.2.1
    have : CompactSpace (((Functor.const Kᵒᵖ).obj T).obj i) := by dsimp; infer_instance
    exact QuasiCompact.compactSpace_of_compactSpace (t.app i)
  have (i : Kᵒᵖ) : QuasiSeparatedSpace (D.obj i) := by
    have : QuasiSeparated (t.app i) := (hstage i).2.2.2
    have : QuasiSeparatedSpace (((Functor.const Kᵒᵖ).obj T).obj i) := by dsimp; infer_instance
    exact quasiSeparatedSpace_of_quasiSeparated (t.app i)
  have hp (i : Kᵒᵖ) : c.π.app i ≫ t.app i = g := by
    simpa [c] using congrArg (fun η => η.app i) hcompat
  let W (k : J) : Y.Opens := (j₀ k).opensRange
  have hWcover : IsOpenCover W :=
    IsOpenCover.of_sets (fun k => (j₀ k).isOpenEmbedding.isOpen_range)
      (by simpa [W, Scheme.Hom.opensRange] using hcover)
  obtain ⟨i₀, V₀, hVcover, hV⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite D c hc W
    hWcover fun k => isAffineOpen_opensRange (j₀ k)
  have hfactor (k : J) := Scheme.exists_preimage_lift_of_locallyOfFinitePresentation t c hc g hp
    (f (σ k)) (V₀ k) (hV k).1 ((Y.isoOfEq (hV k).2.symm).hom ≫ (j₀ k).isoOpensRange.inv ≫ a k)
    (by
      simp only [Category.assoc, ha k]
      rw [← Category.assoc (j₀ k).isoOpensRange.inv, Scheme.Hom.isoOpensRange_inv_comp,
        ← Category.assoc, Scheme.isoOfEq_hom_ι])
  choose qfun hq using hfactor
  have := Fintype.ofFinite J
  obtain ⟨q, hq'⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image qfun)
  choose b hb using fun k => hq k q (hq' (by simp)).some
  refine ⟨D.obj q.left, t.app q.left, fun k => D.map q.hom ⁻¹ᵁ V₀ k, fun k => Scheme.Opens.ι _,
    (hstage q.left).1, ?_, (hstage q.left).2, fun k => (hV k).1.preimage _, fun _ => inferInstance,
    ?_, fun k => ⟨b k, hb k⟩⟩
  · have : Surjective (pcone.app q.left ≫ t.app q.left) := by
      rw [hp q.left]
      infer_instance
    exact Surjective.of_comp (pcone.app q.left) (t.app q.left)
  · have hVcover' : IsOpenCover (fun k => (D.map q.hom) ⁻¹ᵁ V₀ k) :=
      hVcover.comap (D.map q.hom).base.hom'
    simpa [Scheme.Opens.range_ι] using hVcover'.iSup_set_eq_univ

/-- **Stacks 0ETU.** An h covering of an affine scheme `T` is refined by a finite family of
affine opens of a single proper surjective morphism `Y ⟶ T` of finite presentation: the opens
cover `Y` and each of them maps to a member of the h covering over `T`. -/
@[stacks 0ETU]
public theorem exists_finitePresentation_proper_refinement_of_isHCovering
    {T : Scheme.{u}} [IsAffine T] {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : IsHCovering X f) :
    ∃ (J : Type u) (Y : Scheme.{u}) (p : Y ⟶ T)
      (V : J → Scheme.{u}) (j : ∀ k, V k ⟶ Y),
      Finite J ∧
        IsProper p ∧
        Surjective p ∧
        FinitePresentation p ∧
        (∀ k, IsAffine (V k)) ∧
        (∀ k, IsOpenImmersion (j k)) ∧
        (⋃ k, Set.range (j k)) = Set.univ ∧
        (∀ k, ∃ i : I, ∃ h : V k ⟶ X i, h ≫ f i = j k ≫ p) := by
  have : IsAffine (⊤ : T.Opens).toScheme := isAffineOpen_top T
  obtain ⟨E, hE, ⟨φ⟩⟩ := ((isPHCovering_iff X f).mp hf.2).2 ⊤ (isAffineOpen_top T)
  obtain ⟨Y, g, j₀, _, _, _, hcover, hcomp⟩ := hE.exists_presentation
  have := hf.1
  have := hE.finite
  have := hE.isAffine
  have ha (k : E.I₀) : (φ.h₀ k ≫ pullback.fst (f (φ.s₀ k)) (⊤ : T.Opens).ι) ≫ f (φ.s₀ k) =
      j₀ k ≫ g ≫ T.topIso.hom := by
    have hw : φ.h₀ k ≫ pullback.snd (f (φ.s₀ k)) (⊤ : T.Opens).ι = E.f k := φ.w₀ k
    exact (Category.assoc _ _ _).trans <| (congrArg (φ.h₀ k ≫ ·) pullback.condition).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ (⊤ : T.Opens).ι) (hw.trans (hcomp k).symm)).trans (Category.assoc _ _ _)
  obtain ⟨Y', p, V, j, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ :=
    exists_finitePresentation_proper_refinement_of_isProper X f (g ≫ T.topIso.hom) j₀ hcover _ _ ha
  exact ⟨E.I₀, Y', p, V, j, hE.finite, h₁, h₂, h₃, h₄, h₅, h₆, fun k => ⟨_, h₇ k⟩⟩

end AlgebraicGeometry
