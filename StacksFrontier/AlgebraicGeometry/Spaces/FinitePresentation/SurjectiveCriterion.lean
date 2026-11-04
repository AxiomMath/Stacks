module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation

/-!
# Surjectivity alone suffices for local finite presentation of a morphism of spaces

A morphism `f : X ⟶ Y` of algebraic spaces over `S` is locally of finite presentation as
soon as, for every cofiltered inverse limit `T = lim T i` of affine objects of the site, the
comparison map `colim X(T i) ⟶ X(T) ×_{Y(T)} colim Y(T i)` is surjective. Injectivity of
that map, which the cartesian-square criterion of Tag 06BC also demands, is not needed.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_affineLimit_surjective` is the
  surjective affine-limit criterion.

## Implementation notes

Surjectivity is phrased elementwise: a section of the source over the limit together with a
section of the target at a finite stage which agree over the limit have a common antecedent
in the colimit of the sections of the source. That is exactly surjectivity onto the fibre
product, without naming it.

The index categories are cofiltered categories in the universe of the schemes, as in the
affine-limit characterisation of Tag 0CM0 for schemes. This makes the hypothesis quantify
over as few inverse systems as possible, hence the criterion as strong as possible, and it
is the size at which the inverse systems produced in the proof arise.

The scheme-level criterion of Tag 0CM0 is not applicable: it quantifies over inverse systems
of arbitrary schemes over the base, whereas the hypothesis here only sees systems internal to
the size-bounded site. The relevant systems are therefore built inside the site, which is the
set-theoretic step the source's proof defers to Proposition 70.3.10: an affine open of a chart
is the limit of the spectra of the finitely presented subalgebras of its ring of functions, and
those spectra are again below the site's cutoff because the cutoff is a strong prelimit.

A section of the source over the limit is lifted along the étale chart of the source by the
representable case of Tag 04AK: an étale morphism is locally of finite presentation, so a
morphism out of a cofiltered limit of affine schemes into its represented pullback factors
through a stage of the system, compatibly with the projections.

## References

* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
* [Stacks Project, Tag 0CM0](https://stacks.math.columbia.edu/tag/0CM0)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace AlgebraicGeometry.Space

attribute [local instance] IsCofiltered.isConnected uliftCategory

private theorem colimMap_apply_ι
    {I : Type w} [Category.{w'} I] {F G : I ⥤ Type u}
    [HasColimit F] [HasColimit G] (α : F ⟶ G) (i : I) (x : F.obj i) :
    colimMap α (colimit.ι F i x) = colimit.ι G i (α.app i x) :=
  congrArg (fun g : F.obj i ⟶ colimit G ↦ g x) (ι_colimMap α i)

/-- Two elements of a filtered colimit of types which agree after one of them is pushed
along a transformation agree already at a common later stage. -/
private theorem exists_common_stage_of_colimMap_eq
    {I : Type w} [Category.{w'} I] [IsFiltered I] [UnivLE.{max w w', u}]
    {F G : I ⥤ Type u} [HasColimitsOfShape I (Type u)]
    (α : F ⟶ G) (i : I) (x : F.obj i) (j : I) (y : G.obj j)
    (h : colimMap α (colimit.ι F i x) = colimit.ι G j y) :
    ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k), G.map f (α.app i x) = G.map g y :=
  (Types.FilteredColimit.colimit_eq_iff (F := G)).mp
    ((colimMap_apply_ι α i x).symm.trans h)

/-- A morphism out of a cofiltered limit of affine schemes over a morphism locally of
finite presentation factors through a stage of the system, compatibly with the projections. -/
@[sga "3 XI 3.2" "partial"]
private theorem exists_later_stage_factorization_of_locallyOfFinitePresentation
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : Jᵒᵖ ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : J)
    {Z : Scheme.{u}} (f : Z ⟶ D.obj (Opposite.op i))
    [LocallyOfFinitePresentation f] (a : c.pt ⟶ Z)
    (ha : c.π.app (Opposite.op i) = a ≫ f) :
    ∃ (j : J) (g : i ⟶ j) (u : D.obj (Opposite.op j) ⟶ Z),
      c.π.app (Opposite.op j) ≫ u = a ∧ u ≫ f = D.map g.op := by
  let E := Over (Opposite.op i)
  let p : E ⥤ Jᵒᵖ := Over.forget _
  let D' := p ⋙ D
  let c' := c.whisker p
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv p c).symm hc
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : ∀ j, IsAffine (D'.obj j) := fun j ↦ inferInstanceAs (IsAffine (D.obj _))
  have : ∀ {j k} (g : j ⟶ k), IsAffineHom (D'.map g) := fun g ↦ inferInstance
  let t : D' ⟶ (Functor.const E).obj (D.obj (Opposite.op i)) :=
    { app := fun j ↦ D.map j.hom
      naturality := by
        intro j k α
        dsimp [D', p]
        simp only [Category.comp_id]
        rw [← Functor.map_comp]
        congr 1
        exact Over.w α }
  have hcompat : c'.π ≫ t = (Functor.const E).map (a ≫ f) := by
    ext j
    show c.π.app (p.obj j) ≫ D.map j.hom = a ≫ f
    exact (c.w j.hom).trans ha
  obtain ⟨j, u, hu, hu'⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D' t f c' hc' a hcompat
  refine ⟨j.left.unop, j.hom.unop, u, ?_, ?_⟩
  · simpa [c', D', p] using hu
  · simpa [t, D', p] using hu'

/-- An algebra is the filtered colimit of its finitely presented subalgebras. -/
private theorem exists_small_finitePresentation_colimit
    {R : CommRingCat.{u}} (A : Under R) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (pres : ColimitPresentation J A),
      ∀ j, (pres.diag.obj j).hom.hom.FinitePresentation := by
  let E : ObjectProperty (Under R) := fun T ↦ T.hom.hom.FinitePresentation
  have hInd : ObjectProperty.ind.{u} E A := by
    rw [CommRingCat.ind_under_iff_exists_factorization A le_rfl]
    intro T hT g
    exact ⟨T, 𝟙 _, g, by simp, hT⟩
  obtain ⟨J, hJ, hFilt, pres, hE⟩ := hInd
  exact ⟨J, hJ, hFilt, pres, hE⟩

/-- The spectra of a system of algebras, as schemes over the spectrum of the base ring. -/
private noncomputable def specUnderFunctor (R : CommRingCat.{u}) :
    (Under R)ᵒᵖ ⥤ Over (Spec R) where
  obj A := Over.mk (Spec.map A.unop.hom)
  map g := Over.homMk (Spec.map g.unop.right) (by
    change Spec.map g.unop.right ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    exact congrArg Spec.map g.unop.w)
  map_id A := by
    apply Over.OverMorphism.ext
    exact Spec.map_id A.unop.right
  map_comp g h := by
    apply Over.OverMorphism.ext
    exact Spec.map_comp h.unop.right g.unop.right

private noncomputable abbrev algDiagram
    {R : CommRingCat.{u}} {J : Type u} [Category.{u} J]
    (F : J ⥤ Under R) : Jᵒᵖ ⥤ Over (Spec R) :=
  F.op ⋙ specUnderFunctor R

private noncomputable abbrev specCone
    {R : CommRingCat.{u}} {J : Type u} [Category.{u} J]
    (F : J ⥤ Under R) (c : Cocone F) : Cone (algDiagram F) :=
  (specUnderFunctor R).mapCone c.op

/-- `Spec` turns a filtered colimit of algebras into a cofiltered limit of affine schemes
over the spectrum of the base ring. -/
private noncomputable def specCone_isLimit
    {R : CommRingCat.{u}} {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c) :
    IsLimit (specCone F c) := by
  apply isLimitOfReflects (Over.forget (Spec R))
  exact isLimitOfPreserves Scheme.Spec (isColimitOfPreserves (Under.forget R) hc).op

/-- The spectrum of a finitely presented algebra over a ring whose spectrum is below the
cutoff of a site is again below that cutoff. -/
private theorem spec_size_lt_cutoff_of_finitePresentation
    (B : BigFppfSite.{u}) {R : CommRingCat.{u}}
    (hR : (Spec R).size < B.cutoff) (A : Under R)
    (hA : A.hom.hom.FinitePresentation) : (Spec A.right).size < B.cutoff := by
  have : Algebra.FiniteType (R : Type u) (A.right : Type u) :=
    RingHom.FiniteType.of_finitePresentation hA
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit R A.right hR

/-- An algebra which is a retract, in the category of algebras, of a finitely presented
algebra is itself finitely presented. The retraction is given on spectra. -/
private theorem finitePresentation_of_spec_retract
    {R : CommRingCat.{u}} (A T : Under R)
    (hT : T.hom.hom.FinitePresentation) (r : T ⟶ A)
    (s : Spec T.right ⟶ Spec A.right)
    (hs : s ≫ Spec.map A.hom = Spec.map T.hom)
    (hr : Spec.map r.right ≫ s = 𝟙 (Spec A.right)) :
    A.hom.hom.FinitePresentation := by
  let s' : A.right ⟶ T.right := (Scheme.Spec.preimage (X := Opposite.op T.right)
    (Y := Opposite.op A.right) s).unop
  have hs' : Spec.map s' = s := Scheme.Spec.map_preimage (X := Opposite.op T.right)
    (Y := Opposite.op A.right) s
  let sr : A ⟶ T := Under.homMk s' (by
    apply Spec.map_injective
    rw [Spec.map_comp, hs']
    exact hs)
  have hsr : sr ≫ r = 𝟙 A := by
    apply Under.UnderMorphism.ext
    apply Spec.map_injective
    show Spec.map (s' ≫ r.right) = Spec.map (𝟙 A.right)
    rw [Spec.map_comp, hs', Spec.map_id]
    exact hr
  let re : Retract A T := { i := sr, r := r, retract := hsr }
  have : IsFinitelyPresentable.{u} T :=
    ((CommRingCat.isFinitelyPresentable_under_tfae T).out 1 2).mp hT
  have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  exact ((CommRingCat.isFinitelyPresentable_under_tfae A).out 2 1).mp
    (re.isCardinalPresentable Cardinal.aleph0)

/-- A diagram of schemes over `S` all of whose objects lie below the cutoff of a site,
regarded as a diagram in the site. -/
private def liftOverDiagramToSite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over S)
    (hD : ∀ i, B.Contains (D.obj i).left) :
    I ⥤ BigFppfOver B S hS where
  obj i := Over.mk (ObjectProperty.homMk (X := B.obj (hD i))
    (Y := B.obj hS) (D.obj i).hom)
  map g := Over.homMk (ObjectProperty.homMk (D.map g).left)
    (by apply ObjectProperty.hom_ext; exact (D.map g).w)
  map_id i := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact congrArg Over.Hom.left (D.map_id i)
  map_comp g h := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact congrArg Over.Hom.left (D.map_comp g h)

/-- A cone over a diagram of schemes over `S`, regarded in the site when its apex and the
objects of the diagram lie below the cutoff. -/
private def liftOverConeToSite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] {D : I ⥤ Over S} (c : Cone D)
    (hD : ∀ i, B.Contains (D.obj i).left) (hpt : B.Contains c.pt.left) :
    Cone (liftOverDiagramToSite B S hS D hD) where
  pt := Over.mk (ObjectProperty.homMk (X := B.obj hpt) (Y := B.obj hS) c.pt.hom)
  π :=
    { app := fun i => Over.homMk (ObjectProperty.homMk (c.π.app i).left)
        (by apply ObjectProperty.hom_ext; exact (c.π.app i).w)
      naturality := by
        intro i j g
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        change (c.π.app j).left = (c.π.app i).left ≫ (D.map g).left
        exact (congrArg Over.Hom.left (c.w g)).symm }

/-- An open subscheme of an object of the site, as an object of the site. -/
private def openObjectOverSite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z : BigFppfOver B S hS) (W : Z.left.1.Opens) :
    BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk
    (X := B.obj (Scheme.size_lt_of_isOpenImmersion W.ι Z.left.2))
    (Y := B.obj hS) (W.ι ≫ B.inclusion.map Z.hom))

/-- The inclusion of an open subscheme of an object of the site, in the site. -/
private def openInclusionOverSite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z : BigFppfOver B S hS) (W : Z.left.1.Opens) :
    openObjectOverSite B S hS Z W ⟶ Z :=
  Over.homMk (ObjectProperty.homMk W.ι) (by rfl)

/-- A morphism of the underlying schemes of two objects of the site which commutes with
their structure morphisms, as a morphism of the site. -/
private def siteHomOfSchemeHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A C : BigFppfOver B S hS)
    (g : (BigFppfOver.toScheme B S hS).obj A ⟶ (BigFppfOver.toScheme B S hS).obj C)
    (hg : g ≫ B.inclusion.map C.hom = B.inclusion.map A.hom) :
    A ⟶ C :=
  Over.homMk (ObjectProperty.homMk g) (by apply ObjectProperty.hom_ext; exact hg)

/-- A section of a presheaf over a cofiltered limit of affine objects of the site which
lifts, over a stage, along a representable étale morphism of presheaves, lifts over a later
stage. This is Tag 04AK for a representable étale morphism. -/
private theorem exists_later_stage_lift_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : Jᵒᵖ ⥤ BigFppfOver B S hS) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    [∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j))]
    {W : BigFppfOver B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : yoneda.obj W ⟶ X)
    (hp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (i : J) (ξ : yoneda.obj (D.obj (Opposite.op i)) ⟶ X)
    (a : c.pt ⟶ W)
    (ha : yoneda.map a ≫ p = yoneda.map (c.π.app (Opposite.op i)) ≫ ξ) :
    ∃ (j : J) (g : i ⟶ j) (b : D.obj (Opposite.op j) ⟶ W),
      c.π.app (Opposite.op j) ≫ b = a ∧
      yoneda.map b ≫ p = yoneda.map (D.map g.op) ≫ ξ := by
  let T := BigFppfOver.toScheme B S hS
  let e := hp.rep
  let E := e.pullback ξ
  let aE : c.pt ⟶ E := e.lift' a (c.π.app (Opposite.op i)) ha
  have he : Etale (T.map (e.snd ξ)) := hp.property_snd ξ
  have : ∀ j, IsAffine ((D ⋙ T).obj j) := by
    intro j
    show IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j))
    infer_instance
  have hπ : (T.mapCone c).π.app (Opposite.op i) = T.map aE ≫ T.map (e.snd ξ) := by
    rw [← T.map_comp]
    exact (congrArg T.map (e.lift'_snd a (c.π.app (Opposite.op i)) ha)).symm
  obtain ⟨j, g, β, hβ, hβ'⟩ :=
    exists_later_stage_factorization_of_locallyOfFinitePresentation
      (D ⋙ T) (T.mapCone c) hc i (T.map (e.snd ξ)) (T.map aE) hπ
  have hβS : β ≫ B.inclusion.map E.hom =
      B.inclusion.map (D.obj (Opposite.op j)).hom := by
    calc
      β ≫ B.inclusion.map E.hom =
          β ≫ T.map (e.snd ξ) ≫ B.inclusion.map (D.obj (Opposite.op i)).hom := by
        congr 1
        exact (congrArg B.inclusion.map (e.snd ξ).w).symm
      _ = T.map (D.map g.op) ≫ B.inclusion.map (D.obj (Opposite.op i)).hom := by
        rw [← Category.assoc, hβ']
        rfl
      _ = B.inclusion.map (D.obj (Opposite.op j)).hom :=
        congrArg B.inclusion.map (D.map g.op).w
  let β' := siteHomOfSchemeHom B S hS (D.obj (Opposite.op j)) E β hβS
  have hβ₁ : c.π.app (Opposite.op j) ≫ β' = aE := T.map_injective hβ
  have hβ₂ : β' ≫ e.snd ξ = D.map g.op := T.map_injective hβ'
  refine ⟨j, g, β' ≫ e.fst' ξ, ?_, ?_⟩
  · rw [← Category.assoc, hβ₁]
    exact e.lift'_fst a (c.π.app (Opposite.op i)) ha
  · rw [yoneda.map_comp, Category.assoc, (e.isPullback' ξ).w,
      ← Category.assoc, ← yoneda.map_comp, hβ₂]

/-- If a property of morphisms of the site holds for the base change `b` of the relatively
representable `q`, and relatively on `p`, then it holds relatively on `yoneda.map b ≫ p`. -/
private theorem presheaf_yoneda_map_comp_of_isPullback
    {C : Type*} [Category C] [HasPullbacks C] (Q : MorphismProperty C)
    [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange] [Q.RespectsIso]
    {U V W : C} {X Y : Cᵒᵖ ⥤ Type _} {p : yoneda.obj W ⟶ X} {q : yoneda.obj V ⟶ Y}
    {g : X ⟶ Y} {a : U ⟶ V} {b : U ⟶ W}
    (hpb : IsPullback (yoneda.map a) (yoneda.map b) q (p ≫ g))
    (hq : Q.presheaf q) (hp : Q.presheaf p) : Q.presheaf (yoneda.map b ≫ p) :=
  MorphismProperty.comp_mem _ _ _
    (MorphismProperty.relative_map (F := yoneda) (hq.property (p ≫ g) (yoneda.map a) b hpb)) hp

/-- **Stacks 0CM6.** A morphism of algebraic spaces over `S` is locally of finite
presentation as soon as, for every cofiltered inverse limit of affine objects of the site,
the comparison map from the colimit of the sections of the source to the fibre product of
the sections over the limit with the colimit of the sections of the target is surjective. -/
@[stacks 0CM6]
theorem isLocallyOfFinitePresentation_of_affineLimit_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hsurj : ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ BigFppfOver B S hS) (c : Cone D),
      IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i))) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
      ∀ (x : X.obj (Opposite.op c.pt)) (y : colimit (D.op ⋙ Y)),
        f.app (Opposite.op c.pt) x = colimit.desc (D.op ⋙ Y) (Y.mapCocone c.op) y →
        ∃ z : colimit (D.op ⋙ X),
          colimit.desc (D.op ⋙ X) (X.mapCocone c.op) z = x ∧
          colimMap (Functor.whiskerLeft D.op f) z = y) :
    IsLocallyOfFinitePresentation B S hS f := by
  let T := BigFppfOver.toScheme B S hS
  let P : MorphismProperty Scheme.{u} := @LocallyOfFinitePresentation
  let hP := LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
  apply (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hX hY f).2
  obtain ⟨W, p, hpSurj, hpEtale⟩ := hX.exists_atlas
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hY.exists_atlas
  let e := hqEtale.rep
  let U := e.pullback (p ≫ f)
  let a : U ⟶ V := e.fst' (p ≫ f)
  let b : U ⟶ W := e.snd (p ≫ f)
  have : PreservesLimitsOfShape WalkingCospan T := by
    show PreservesLimitsOfShape WalkingCospan ((Over.forget (B.obj hS)) ⋙ B.inclusion)
    have : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
    apply comp_preservesLimitsOfShape
  let QEtale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  let QSurjective :=
    MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) T
  have : MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) := by
    refine ⟨?_⟩
    intro X Y Z g h hg hh
    exact ⟨hh.1.comp hg.1⟩
  have : QEtale.IsStableUnderBaseChange := by
    refine ⟨?_⟩
    intro X Y Y' Z g h g' h' sq hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) (sq.map T) hg
  have : QSurjective.IsStableUnderBaseChange := by
    refine ⟨?_⟩
    intro X Y Y' Z g h g' h' sq hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Surjective) (sq.map T) hg
  have : QEtale.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (F := T)
  have : QSurjective.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (F := T)
  have : QEtale.RespectsIso := inferInstance
  have : QSurjective.RespectsIso := inferInstance
  have hpb := e.isPullback' (p ≫ f)
  have hsrcEtale : QEtale.presheaf (yoneda.map b ≫ p) :=
    presheaf_yoneda_map_comp_of_isPullback QEtale hpb hqEtale hpEtale
  have hsrcSurj : QSurjective.presheaf (yoneda.map b ≫ p) :=
    presheaf_yoneda_map_comp_of_isPullback QSurjective hpb hqSurj hpSurj
  refine ⟨U, V, yoneda.map b ≫ p, q, a, hsrcEtale, hqEtale, hsrcSurj, ?_, ?_⟩
  · simpa only [a, b, e.map_fst', Functor.map_comp, Category.assoc] using e.w (p ≫ f)
  · show LocallyOfFinitePresentation (T.map a)
    refine LocallyOfFinitePresentation.mk ?_
    intro V₀ hV₀ U₀ hU₀ hVU
    let R : CommRingCat := CommRingCat.of Γ(T.obj V, V₀)
    let A : Under R := Under.mk ((T.map a).appLE V₀ U₀ hVU)
    obtain ⟨J, hJ, hFilt, pres, hFP⟩ := exists_small_finitePresentation_colimit A
    let F := pres.diag
    let cFP := pres.cocone
    have hcFP := pres.isColimit
    have hV₀small : V₀.toScheme.size < B.cutoff :=
      Scheme.size_lt_of_isOpenImmersion V₀.ι V.left.2
    have hU₀small : U₀.toScheme.size < B.cutoff :=
      Scheme.size_lt_of_isOpenImmersion U₀.ι U.left.2
    have hR : (Spec R).size < B.cutoff := by
      calc
        (Spec R).size = (Spec (CommRingCat.of Γ(T.obj V, V₀))).size := rfl
        _ = V₀.toScheme.size := (Scheme.size_congr hV₀.isoSpec).symm
        _ < B.cutoff := hV₀small
    have hA : (Spec A.right).size < B.cutoff := by
      show (Spec (CommRingCat.of Γ(T.obj U, U₀))).size < B.cutoff
      calc
        (Spec (CommRingCat.of Γ(T.obj U, U₀))).size = U₀.toScheme.size :=
          (Scheme.size_congr hU₀.isoSpec).symm
        _ < B.cutoff := hU₀small
    let overSpec := algDiagram F
    let vToS : T.obj V ⟶ S := B.inclusion.map V.hom
    let toS : Spec R ⟶ S := hV₀.fromSpec ≫ vToS
    let D : Jᵒᵖ ⥤ Over S := overSpec ⋙ Over.map toS
    let cSpec : Cone overSpec := specCone F cFP
    let cOver : Cone D := (Over.map toS).mapCone cSpec
    have hcSpec : IsLimit cSpec := specCone_isLimit F cFP hcFP
    have hcOver : IsLimit cOver := by
      apply isLimitOfReflects (Over.forget S)
      exact isLimitOfPreserves (Over.forget (Spec R)) hcSpec
    have hStages : ∀ j, B.Contains (D.obj j).left := by
      intro j
      show (Spec (F.obj j.unop).right).size < B.cutoff
      exact spec_size_lt_cutoff_of_finitePresentation B hR (F.obj j.unop) (hFP j.unop)
    let Dsite := liftOverDiagramToSite B S hS D hStages
    let cSite := liftOverConeToSite B S hS cOver hStages hA
    let U₀site := openObjectOverSite B S hS U U₀
    have hlimU₀Scheme :
        hU₀.isoSpec.inv ≫ B.inclusion.map U₀site.hom = B.inclusion.map cSite.pt.hom := by
      show hU₀.fromSpec ≫ B.inclusion.map U.hom =
        (Spec.map ((T.map a).appLE V₀ U₀ hVU) ≫ hV₀.fromSpec) ≫ vToS
      rw [IsAffineOpen.SpecMap_appLE_fromSpec (T.map a) hV₀ hU₀ hVU, Category.assoc]
      congr 1
      exact (congrArg B.inclusion.map a.w).symm
    let limU₀ : cSite.pt ⟶ U₀site :=
      siteHomOfSchemeHom B S hS cSite.pt U₀site hU₀.isoSpec.inv hlimU₀Scheme
    let chartToU := openInclusionOverSite B S hS U U₀
    let limToU := limU₀ ≫ chartToU
    let x : X.obj (Opposite.op cSite.pt) :=
      ((yoneda.map (limToU ≫ b)) ≫ p).app (Opposite.op cSite.pt) (𝟙 cSite.pt)
    let i₀ : J := Classical.choice IsFiltered.nonempty
    let oi₀ : Jᵒᵖ := Opposite.op i₀
    let stageToVScheme : (D.obj oi₀).left ⟶ T.obj V :=
      (overSpec.obj oi₀).hom ≫ hV₀.fromSpec
    have hstageToV :
        stageToVScheme ≫ B.inclusion.map V.hom = B.inclusion.map (Dsite.obj oi₀).hom := by
      show ((overSpec.obj oi₀).hom ≫ hV₀.fromSpec) ≫ vToS =
        (overSpec.obj oi₀).hom ≫ toS
      simp [toS, Category.assoc]
    let stageToV : Dsite.obj oi₀ ⟶ V :=
      siteHomOfSchemeHom B S hS (Dsite.obj oi₀) V stageToVScheme hstageToV
    let ystage : Y.obj (Opposite.op (Dsite.obj oi₀)) :=
      q.app (Opposite.op (Dsite.obj oi₀)) stageToV
    let y : colimit (Dsite.op ⋙ Y) :=
      colimit.ι (Dsite.op ⋙ Y) (Opposite.op oi₀) ystage
    have hcSiteScheme : IsLimit (T.mapCone cSite) := by
      show IsLimit ((Over.forget S).mapCone cOver)
      exact isLimitOfPreserves (Over.forget S) hcOver
    have hchart : yoneda.map b ≫ p ≫ f = yoneda.map a ≫ q := by
      simpa only [a, b, e.map_fst', Functor.map_comp, Category.assoc] using
        (e.w (p ≫ f)).symm
    have hlimToV : limToU ≫ a = cSite.π.app oi₀ ≫ stageToV := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      show hU₀.fromSpec ≫ T.map a =
        (cSpec.π.app oi₀).left ≫ (overSpec.obj oi₀).hom ≫ hV₀.fromSpec
      rw [← Category.assoc, (cSpec.π.app oi₀).w]
      exact (IsAffineOpen.SpecMap_appLE_fromSpec (T.map a) hV₀ hU₀ hVU).symm
    have hDsiteAffine : ∀ j, IsAffine (T.obj (Dsite.obj j)) := by
      intro j
      show IsAffine (Spec (F.obj j.unop).right)
      infer_instance
    have htarget : f.app (Opposite.op cSite.pt) x =
        colimit.desc (Dsite.op ⋙ Y) (Y.mapCocone cSite.op) y := by
      have hxchart : f.app (Opposite.op cSite.pt) x =
          q.app (Opposite.op cSite.pt) (limToU ≫ a) := by
        dsimp [x]
        have h := congrArg
          (fun g : yoneda.obj cSite.pt ⟶ Y => g.app (Opposite.op cSite.pt) (𝟙 cSite.pt))
          (congrArg (fun g => yoneda.map limToU ≫ g) hchart)
        simpa [Category.assoc] using h
      have hdesc := congrArg (fun k : Y.obj (Opposite.op (Dsite.obj oi₀)) ⟶
          Y.obj (Opposite.op cSite.pt) => k ystage)
        (colimit.ι_desc (Y.mapCocone cSite.op) (Opposite.op oi₀))
      change colimit.desc (Dsite.op ⋙ Y) (Y.mapCocone cSite.op) y =
        Y.map (cSite.π.app oi₀).op ystage at hdesc
      rw [hdesc, hxchart, hlimToV]
      simpa [ystage] using q.naturality_apply (cSite.π.app oi₀).op stageToV
    have hptAffine : IsAffine (T.obj cSite.pt) := by
      show IsAffine (Spec A.right)
      infer_instance
    obtain ⟨z, hzX, hzY⟩ :=
      hsurj Jᵒᵖ Dsite cSite hcSiteScheme hDsiteAffine hptAffine x y htarget
    let α := Functor.whiskerLeft Dsite.op f
    obtain ⟨i, zi, hzi⟩ :=
      Types.jointly_surjective_of_isColimit (colimit.isColimit (Dsite.op ⋙ X)) z
    change colimit.ι (Dsite.op ⋙ X) i zi = z at hzi
    have hiY : colimMap α (colimit.ι (Dsite.op ⋙ X) i zi) =
        colimit.ι (Dsite.op ⋙ Y) (Opposite.op oi₀) ystage := by
      rw [hzi]
      exact hzY
    obtain ⟨k, fik, fi₀k, hEq⟩ :=
      exists_common_stage_of_colimMap_eq α i zi (Opposite.op oi₀) ystage hiY
    let ok : Jᵒᵖ := k.unop
    let zik : X.obj (Opposite.op (Dsite.obj ok)) := X.map (Dsite.map fik.unop).op zi
    let vk : Dsite.obj ok ⟶ V := Dsite.map fi₀k.unop ≫ stageToV
    have hfactorAtK : f.app (Opposite.op (Dsite.obj ok)) zik =
        q.app (Opposite.op (Dsite.obj ok)) vk := by
      calc
        _ = Y.map (Dsite.map fik.unop).op (f.app _ zi) :=
          f.naturality_apply (Dsite.map fik.unop).op zi
        _ = Y.map (Dsite.map fi₀k.unop).op ystage := hEq
        _ = _ := (q.naturality_apply (Dsite.map fi₀k.unop).op stageToV).symm
    have hziAtLimit : X.map (cSite.π.app i.unop).op zi = x := by
      rw [← hzi] at hzX
      change ((colimit.ι (Dsite.op ⋙ X) i ≫
        colimit.desc (Dsite.op ⋙ X) (X.mapCocone cSite.op)) zi) = x at hzX
      rw [colimit.ι_desc] at hzX
      exact hzX
    have hzkAtLimit : X.map (cSite.π.app ok).op zik = x := by
      show ((X.map (Dsite.map fik.unop).op ≫ X.map (cSite.π.app ok).op) zi) = x
      rw [← X.map_comp, ← op_comp, cSite.w fik.unop]
      exact hziAtLimit
    let ξk : yoneda.obj (Dsite.obj ok) ⟶ X := yonedaEquiv.symm zik
    have hξk : yoneda.map (limToU ≫ b) ≫ p = yoneda.map (cSite.π.app ok) ≫ ξk := by
      apply yonedaEquiv.injective
      rw [← yonedaEquiv_naturality ξk, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      simpa [ξk, x] using hzkAtLimit.symm
    obtain ⟨j, g, wj, hwj, hwjX⟩ := exists_later_stage_lift_etale
      B S hS Dsite cSite hcSiteScheme p hpEtale ok.unop ξk (limToU ≫ b) hξk
    let vj : Dsite.obj (Opposite.op j) ⟶ V := Dsite.map g.op ≫ vk
    have hkY : ξk ≫ f = yoneda.map vk ≫ q := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      exact (by simpa only [ξk, Equiv.apply_symm_apply] using hfactorAtK)
    have hWj : yoneda.map vj ≫ q = yoneda.map wj ≫ (p ≫ f) := by
      rw [← Category.assoc, hwjX, Category.assoc, hkY]
      simp only [vj, Functor.map_comp, Category.assoc]
    let uj : Dsite.obj (Opposite.op j) ⟶ U := e.lift' vj wj hWj
    have hujV : uj ≫ a = vj := e.lift'_fst vj wj hWj
    have hlimVj : cSite.π.app (Opposite.op j) ≫ vj = limToU ≫ a := by
      dsimp only [vj, vk]
      rw [← Category.assoc, cSite.w g.op, ← Category.assoc, cSite.w fi₀k.unop]
      exact hlimToV.symm
    have hlimUj : cSite.π.app (Opposite.op j) ≫ uj = limToU := by
      apply e.hom_ext'
      · rw [Category.assoc, e.lift'_fst]
        exact hlimVj
      · rw [Category.assoc, e.lift'_snd]
        exact hwj
    have hopen : QEtale chartToU := by
      show Etale U₀.ι
      infer_instance
    have hlimOpen : yoneda.map limU₀ ≫ yoneda.map chartToU =
        yoneda.map (cSite.π.app (Opposite.op j)) ≫ yoneda.map uj := by
      rw [← yoneda.map_comp, ← yoneda.map_comp, hlimUj]
    obtain ⟨l, gjl, tl, htl, htlU⟩ := exists_later_stage_lift_etale
      B S hS Dsite cSite hcSiteScheme (yoneda.map chartToU)
      (MorphismProperty.relative_map (F := yoneda) hopen)
      j (yoneda.map uj) limU₀ hlimOpen
    have htlU' : tl ≫ chartToU = Dsite.map gjl.op ≫ uj := by
      apply yoneda.map_injective
      simpa only [Functor.map_comp] using htlU
    have hvjBase : T.map vj = (overSpec.obj (Opposite.op j)).hom ≫ hV₀.fromSpec := by
      show (overSpec.map g.op).left ≫ (overSpec.map fi₀k.unop).left ≫
        (overSpec.obj oi₀).hom ≫ hV₀.fromSpec = _
      rw [← Category.assoc (overSpec.map fi₀k.unop).left, (overSpec.map fi₀k.unop).w,
        ← Category.assoc, (overSpec.map g.op).w]
    have htlV : T.map tl ≫ U₀.ι ≫ T.map a =
        (overSpec.obj (Opposite.op l)).hom ≫ hV₀.fromSpec := by
      have hmap : T.map (Dsite.map gjl.op) = (overSpec.map gjl.op).left := rfl
      calc
        _ = T.map (tl ≫ chartToU) ≫ T.map a := by
          rw [T.map_comp, Category.assoc]
          rfl
        _ = T.map (Dsite.map gjl.op ≫ uj) ≫ T.map a := by rw [htlU']
        _ = T.map (Dsite.map gjl.op) ≫ T.map vj := by
          rw [T.map_comp, Category.assoc, ← T.map_comp, hujV]
        _ = _ := by
          rw [hmap, hvjBase]
          show (overSpec.map gjl.op).left ≫
            (overSpec.obj (Opposite.op j)).hom ≫ hV₀.fromSpec =
            (overSpec.obj (Opposite.op l)).hom ≫ hV₀.fromSpec
          simpa only [Category.assoc] using
            congrArg (· ≫ hV₀.fromSpec) (overSpec.map gjl.op).w
    have hsl : (T.map tl ≫ hU₀.isoSpec.hom) ≫ Spec.map ((T.map a).appLE V₀ U₀ hVU) =
        Spec.map (F.obj l).hom := by
      apply (cancel_mono hV₀.fromSpec).mp
      have h₁ : Spec.map ((T.map a).appLE V₀ U₀ hVU) ≫ hV₀.fromSpec =
          hU₀.fromSpec ≫ T.map a :=
        IsAffineOpen.SpecMap_appLE_fromSpec (T.map a) hV₀ hU₀ hVU
      refine Eq.trans ?_ htlV
      calc ((T.map tl ≫ hU₀.isoSpec.hom) ≫ Spec.map ((T.map a).appLE V₀ U₀ hVU)) ≫
            hV₀.fromSpec
          = (T.map tl ≫ hU₀.isoSpec.hom) ≫
              Spec.map ((T.map a).appLE V₀ U₀ hVU) ≫ hV₀.fromSpec := Category.assoc _ _ _
        _ = (T.map tl ≫ hU₀.isoSpec.hom) ≫ hU₀.fromSpec ≫ T.map a :=
            congrArg ((T.map tl ≫ hU₀.isoSpec.hom) ≫ ·) h₁
        _ = ((T.map tl ≫ hU₀.isoSpec.hom) ≫ hU₀.fromSpec) ≫ T.map a :=
            (Category.assoc _ _ _).symm
        _ = (T.map tl ≫ hU₀.isoSpec.hom ≫ hU₀.fromSpec) ≫ T.map a :=
            congrArg (· ≫ T.map a) (Category.assoc _ _ _)
        _ = (T.map tl ≫ U₀.ι) ≫ T.map a :=
            congrArg (fun z => (T.map tl ≫ z) ≫ T.map a) hU₀.isoSpec_hom_fromSpec
        _ = T.map tl ≫ U₀.ι ≫ T.map a := Category.assoc _ _ _
    have hrl : Spec.map (pres.ι.app l).right ≫ T.map tl ≫ hU₀.isoSpec.hom =
        𝟙 (Spec A.right) := by
      have hh := congrArg T.map htl
      change Spec.map (pres.ι.app l).right ≫ T.map tl = hU₀.isoSpec.inv at hh
      calc Spec.map (pres.ι.app l).right ≫ T.map tl ≫ hU₀.isoSpec.hom
          = (Spec.map (pres.ι.app l).right ≫ T.map tl) ≫ hU₀.isoSpec.hom :=
            (Category.assoc _ _ _).symm
        _ = hU₀.isoSpec.inv ≫ hU₀.isoSpec.hom :=
            congrArg (· ≫ hU₀.isoSpec.hom) hh
        _ = 𝟙 (Spec A.right) := hU₀.isoSpec.inv_hom_id
    exact finitePresentation_of_spec_retract A (F.obj l) (hFP l) (pres.ι.app l)
      (T.map tl ≫ hU₀.isoSpec.hom) hsl hrl

end AlgebraicGeometry.Space

end
