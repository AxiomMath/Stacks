module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcGluing
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSingletonCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSystemModuleColimitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Morphisms of finitely presented modules over a limit of algebraic spaces come from a stage

Let `X = lim Xᵢ` be the limit of a cofiltered system of quasi-compact and quasi-separated
algebraic spaces over `S` with affine transition morphisms, satisfying the chapter's convention of
Section 70.2 (tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.  This file proves
the faithfulness and the fullness clauses of the colimit assertion of Stacks 07V7 for this
system, for a source of finite presentation and a quasi-coherent target:

* two morphisms `E ⟶ G` of modules on a stage whose inverse images to the limit agree have equal
  inverse images at a later stage;
* a morphism between the inverse images to the limit of `E` and `G` is, through the comparisons
  `AlgebraicGeometry.Space.modulePullbackTriangle`, the inverse image of a morphism at a later
  stage.

## Main results

* `AlgebraicGeometry.Space.exists_stage_modulePullback_map_eq_of_siteContainsBaseChangeLimits`:
  faithfulness.
* `AlgebraicGeometry.Space.exists_stage_restrictPullbackHom_eq_of_siteContainsBaseChangeLimits`:
  fullness, in the calculus of restrictions `AlgebraicGeometry.Space.restrictPullbackHom`.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` on presheaves over the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_FinitePresentationModuleFullnessUnderConvention :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high)
    hasPullback_presheaf_FinitePresentationModuleFullnessUnderConvention
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

attribute [local irreducible] modulePullback modulePullbackTriangle

/-! ### Restriction and homTransport -/

section Calculus

variable {P Q R W : AlgebraicSpaces B S hS} {E G : Modules.{u, u} B S hS W.1 W.2}

/-- Restricting the inverse image of a morphism of modules is the inverse image of that
morphism. -/
private theorem restrict_map {p : P ⟶ W} {q : Q ⟶ W} (a : Q ⟶ P) (ha : a ≫ p = q) (φ : E ⟶ G) :
    restrictPullbackHom a ha ((modulePullback B S hS p).map φ) =
      (modulePullback B S hS q).map φ := by
  unfold restrictPullbackHom Functor.conjHom
  have h := (modulePullbackTriangle B S hS ha).hom.naturality φ
  simp only [Functor.comp_map] at h
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- A homomorphism of iterated inverse images `x^*p^*E ⟶ x^*p^*G`, read as a homomorphism
`y^*E ⟶ y^*G` through the comparison of `y = x ≫ p`. -/
private def homTransport {p : P ⟶ W} {x : Q ⟶ P} {y : Q ⟶ W} (hx : x ≫ p = y)
    (φ : (modulePullback B S hS x).obj ((modulePullback B S hS p).obj E) ⟶
      (modulePullback B S hS x).obj ((modulePullback B S hS p).obj G)) :
    (modulePullback B S hS y).obj E ⟶ (modulePullback B S hS y).obj G :=
  (modulePullbackTriangle B S hS hx).hom.app E ≫ φ ≫ (modulePullbackTriangle B S hS hx).inv.app G

/-- The inverse of `homTransport`. -/
private def homUntransport {p : P ⟶ W} {x : Q ⟶ P} {y : Q ⟶ W} (hx : x ≫ p = y)
    (β : (modulePullback B S hS y).obj E ⟶ (modulePullback B S hS y).obj G) :
    (modulePullback B S hS x).obj ((modulePullback B S hS p).obj E) ⟶
      (modulePullback B S hS x).obj ((modulePullback B S hS p).obj G) :=
  (modulePullbackTriangle B S hS hx).inv.app E ≫ β ≫ (modulePullbackTriangle B S hS hx).hom.app G

private theorem homTransport_homUntransport {p : P ⟶ W} {x : Q ⟶ P} {y : Q ⟶ W} (hx : x ≫ p = y)
    (β : (modulePullback B S hS y).obj E ⟶ (modulePullback B S hS y).obj G) :
    homTransport hx (homUntransport hx β) = β := by
  simp [homTransport, homUntransport]

private theorem homTransport_injective {p : P ⟶ W} {x : Q ⟶ P} {y : Q ⟶ W} (hx : x ≫ p = y)
    {φ ψ : (modulePullback B S hS x).obj ((modulePullback B S hS p).obj E) ⟶
      (modulePullback B S hS x).obj ((modulePullback B S hS p).obj G)}
    (h : homTransport hx φ = homTransport hx ψ) : φ = ψ := by
  simpa [homTransport] using congrArg (fun t => (modulePullbackTriangle B S hS hx).inv.app E ≫ t ≫
    (modulePullbackTriangle B S hS hx).hom.app G) h

/-- Conjugating by `T₄` the transport of `φ` along `T` is transporting along `T₃` the conjugate of
`φ` by `T₂`, for functors and comparisons satisfying the coherence `h`. -/
private theorem conj_coherence {C D₁ D₂ D₃ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    [Category* D₃] (Pp : C ⥤ D₁) (Px : D₁ ⥤ D₂) (Pa : D₂ ⥤ D₃) (Py : C ⥤ D₂) (Pz : C ⥤ D₃)
    (Px' : D₁ ⥤ D₃) (T : Py ≅ Pp ⋙ Px) (T₂ : Px' ≅ Px ⋙ Pa) (T₃ : Pz ≅ Pp ⋙ Px')
    (T₄ : Pz ≅ Py ⋙ Pa)
    (h : T₃ ≪≫ Functor.isoWhiskerLeft Pp T₂ =
      T₄ ≪≫ Functor.isoWhiskerRight T Pa ≪≫ Functor.associator Pp Px Pa)
    {E G : C} (φ : Px.obj (Pp.obj E) ⟶ Px.obj (Pp.obj G)) :
    Functor.conjHom T₄ (T.hom.app E ≫ φ ≫ T.inv.app G) =
      T₃.hom.app E ≫ Functor.conjHom T₂ φ ≫ T₃.inv.app G := by
  unfold Functor.conjHom
  have hE := congrArg (fun t => t.hom.app E) h
  have hG := congrArg (fun t => t.inv.app G) h
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id] at hE hG
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hE, hG]

/-- **Transport commutes with restriction**: the associativity coherence of the comparisons of
Stacks 03LU. -/
private theorem restrict_homTransport {p : P ⟶ W} {x : Q ⟶ P} {y : Q ⟶ W} {a : R ⟶ Q}
    {x' : R ⟶ P} {z : R ⟶ W} (ha : a ≫ x = x') (hx : x ≫ p = y) (hz : a ≫ y = z)
    (hx' : x' ≫ p = z)
    (φ : (modulePullback B S hS x).obj ((modulePullback B S hS p).obj E) ⟶
      (modulePullback B S hS x).obj ((modulePullback B S hS p).obj G)) :
    restrictPullbackHom a hz (homTransport hx φ) =
      homTransport hx' (restrictPullbackHom a ha φ) := by
  unfold restrictPullbackHom homTransport
  exact conj_coherence _ _ _ _ _ _ _ _ _ _ (modulePullbackTriangle_assoc B S hS ha hx hz hx') φ

/-- Restriction, read through `homTransport`. -/
private theorem restrict_eq_homTransport {p : P ⟶ W} {x : Q ⟶ P} {y : Q ⟶ W} {a : R ⟶ Q}
    {x' : R ⟶ P} {z : R ⟶ W} (ha : a ≫ x = x') (hx : x ≫ p = y) (hz : a ≫ y = z)
    (hx' : x' ≫ p = z)
    (γ : (modulePullback B S hS y).obj E ⟶ (modulePullback B S hS y).obj G) :
    restrictPullbackHom a hz γ =
      homTransport hx' (restrictPullbackHom a ha (homUntransport hx γ)) := by
  rw [← restrict_homTransport ha hx hz hx', homTransport_homUntransport]

/-- Restrictions of two homomorphisms with equal inverse images are equal. -/
private theorem restrict_eq_of_map_eq {p : P ⟶ W} {q : Q ⟶ W} (a : Q ⟶ P) (ha : a ≫ p = q)
    (α β : (modulePullback B S hS p).obj E ⟶ (modulePullback B S hS p).obj G)
    (h : (modulePullback B S hS a).map α = (modulePullback B S hS a).map β) :
    restrictPullbackHom a ha α = restrictPullbackHom a ha β := by
  unfold restrictPullbackHom Functor.conjHom
  rw [h]

/-- Two composites of restrictions along equal composites agree. -/
private theorem restrict_restrict {V V' V₁ Z : AlgebraicSpaces B S hS} {p : Z ⟶ W} {q : V ⟶ W}
    {q' : V₁ ⟶ W} {r : V' ⟶ W} (a : V ⟶ Z) (ha : a ≫ p = q) (b : V' ⟶ V) (hb : b ≫ q = r)
    (a' : V₁ ⟶ Z) (ha' : a' ≫ p = q') (b' : V' ⟶ V₁) (hb' : b' ≫ q' = r) (hab : b ≫ a = b' ≫ a')
    (α : (modulePullback B S hS p).obj E ⟶ (modulePullback B S hS p).obj G) :
    restrictPullbackHom b hb (restrictPullbackHom a ha α) =
      restrictPullbackHom b' hb' (restrictPullbackHom a' ha' α) := by
  rw [← restrictPullbackHom_comp a ha b hb (by rw [Category.assoc, ha, hb]),
    ← restrictPullbackHom_comp a' ha' b' hb' (by rw [Category.assoc, ha', hb'])]
  exact restrictPullbackHom_congr hab _ _ α

/-- A composite of restrictions is the restriction along the composite. -/
private theorem restrict_restrict_single {V V' Z : AlgebraicSpaces B S hS} {p : Z ⟶ W}
    {q : V ⟶ W} {r : V' ⟶ W} (a : V ⟶ Z) (ha : a ≫ p = q) (b : V' ⟶ V) (hb : b ≫ q = r)
    (a' : V' ⟶ Z) (ha' : a' ≫ p = r) (hab : b ≫ a = a')
    (α : (modulePullback B S hS p).obj E ⟶ (modulePullback B S hS p).obj G) :
    restrictPullbackHom b hb (restrictPullbackHom a ha α) = restrictPullbackHom a' ha' α := by
  rw [← restrictPullbackHom_comp a ha b hb (by rw [Category.assoc, ha, hb])]
  exact restrictPullbackHom_congr hab _ _ α

end Calculus

/-! ### Single-member coverings -/

/-- A surjective étale morphism of algebraic spaces is a one-member fpqc covering. -/
private theorem isFpqcCovering_of_etale_surjective {P W : AlgebraicSpaces B S hS} (a : P ⟶ W)
    (he : IsEtale B S hS a.hom)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a.hom) :
    IsFpqcCovering B S hS (fun _ : PUnit.{1} ↦ a.hom) :=
  isFpqcCovering_of_isFppfCovering B S hS _ _
    (isFppfCovering_singleton.{u, 0} B S hS a (isSurjective_of_presheafSurjective B S hS a.hom hs)
      (isFlat_of_isEtale B S hS he) (isLocallyOfFinitePresentation_of_isEtale B S hS he))

/-- Restriction along a surjective étale morphism is injective. -/
private theorem restrict_injective {P Q W : AlgebraicSpaces B S hS}
    {E G : Modules.{u, u} B S hS W.1 W.2} {p : P ⟶ W} {q : Q ⟶ W} (a : Q ⟶ P) (ha : a ≫ p = q)
    (he : IsEtale B S hS a.hom)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a.hom)
    {α β : (modulePullback B S hS p).obj E ⟶ (modulePullback B S hS p).obj G}
    (h : restrictPullbackHom a ha α = restrictPullbackHom a ha β) : α = β :=
  eq_of_restrictPullbackHom_eq_of_isFpqcCovering
    (QuasiCoherentDescent.reprFpqcHomInjective.{u, 0} B S hS) (fun _ : PUnit.{1} ↦ a)
    (fun _ ↦ ha) (isFpqcCovering_of_etale_surjective a he hs) α β fun _ ↦ h

/-- The base change of a surjective étale morphism along a pullback square of presheaves is
surjective étale. -/
private theorem isEtale_and_presheafSurjective_of_isPullback
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS}
    {g : yoneda.obj U ⟶ G} {f : F ⟶ G} {f' : yoneda.obj R ⟶ yoneda.obj U} {g' : yoneda.obj R ⟶ F}
    (sq : IsPullback f' g' g f) (he : IsEtale B S hS g)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    IsEtale B S hS g' ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g' := by
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact ⟨isEtale_of_isPullback_yoneda B S hS sq he, MorphismProperty.of_isPullback sq hs⟩

/-- A quasi-compact algebraic space has a surjective étale morphism from an affine scheme. -/
private theorem exists_affine_etale_presheafSurjective {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hq : IsQuasiCompactSpace B S hS X) :
    ∃ (U₀ : BigAffineFppf B S hS) (f : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ X),
      IsEtale B S hS f ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f := by
  obtain ⟨W₀, w₀, hW₀, hs₀, he₀⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).mp hq
  exact ⟨⟨W₀, hW₀⟩, w₀, he₀, hs₀⟩

/-! ### The affine case, for a system of affine charts with compatible maps to a space -/

section Affine

variable {J : Type u} [Category.{u} J] [IsCofiltered J] (V : J ⥤ BigFppfOver B S hS)
  (c : Cone V) (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
  (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
  {W : AlgebraicSpaces B S hS} (p : ∀ j, (schemeSpaceFunctor B S hS).obj (V.obj j) ⟶ W)
  (pc : (schemeSpaceFunctor B S hS).obj c.pt ⟶ W)
  (hp : ∀ {j j' : J} (e : j' ⟶ j), (schemeSpaceFunctor B S hS).map (V.map e) ≫ p j = p j')
  (hpc : ∀ j, (schemeSpaceFunctor B S hS).map (c.π.app j) ≫ p j = pc)
  {E G : Modules.{u, u} B S hS W.1 W.2} (hE : E.IsFinitePresentationOnSite)
  (hG : G.IsQuasicoherentOnSite)

include hc hV hpt hE hG hp in
/-- **The affine fullness clause, read on homomorphisms of inverse images of `E` and `G`.** -/
private theorem affine_exists_restrict_eq
    (α : (modulePullback B S hS pc).obj E ⟶ (modulePullback B S hS pc).obj G) :
    ∃ (j : J) (β : (modulePullback B S hS (p j)).obj E ⟶ (modulePullback B S hS (p j)).obj G),
      restrictPullbackHom ((schemeSpaceFunctor B S hS).map (c.π.app j)) (hpc j) β = α := by
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  have hM := isFinitePresentationOnSite_modulePullback B S hS (p j₀) E hE
  have hN := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (p j₀) G hG
  obtain ⟨j, e, φ', hφ'⟩ := (HomSituation.affineSpaceHomDescent (B := B) (S := S)
      (hS := hS) V c hc hV hpt j₀ _ _
    hM hN).1 (homUntransport (hpc j₀) α)
  refine ⟨j, homTransport (hp e) φ', ?_⟩
  rw [restrict_homTransport (HomSituation.schemeSpaceFunctor_map_cone_w V c j₀ e) (hp e) (hpc j)
      (hpc j₀)]
  unfold restrictPullbackHom
  rw [hφ', homTransport_homUntransport]

include hc hV hE hG hp in
/-- **The affine faithfulness clause, read on homomorphisms of inverse images of `E` and
`G`.** -/
private theorem affine_exists_restrict_eq_of_restrict_eq (j : J)
    (β β' : (modulePullback B S hS (p j)).obj E ⟶ (modulePullback B S hS (p j)).obj G)
    (h : restrictPullbackHom ((schemeSpaceFunctor B S hS).map (c.π.app j)) (hpc j) β =
      restrictPullbackHom ((schemeSpaceFunctor B S hS).map (c.π.app j)) (hpc j) β') :
    ∃ (j' : J) (e : j' ⟶ j),
      restrictPullbackHom ((schemeSpaceFunctor B S hS).map (V.map e)) (hp e) β =
        restrictPullbackHom ((schemeSpaceFunctor B S hS).map (V.map e)) (hp e) β' := by
  have hM := isFinitePresentationOnSite_modulePullback B S hS (p j) E hE
  have hN := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (p j) G hG
  have h₁ := modulePullback_map_eq_of_restrictPullbackHom_eq _ _ _ _ h
  obtain ⟨j', e', he'⟩ := affineSpacePullbackSystem_faithfulnessInto B S hS V c hV hc j _ _ hM hN
    β β' h₁
  exact ⟨j', e', restrict_eq_of_map_eq _ (hp e') _ _ he'⟩

end Affine

/-! ### The charts of a stage and their limit -/

section Charts

variable (B S hS) {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))

/-- A stage, as an algebraic space. -/
private abbrev stSp (i : I) : AlgebraicSpaces B S hS := ⟨D.obj i, hD i⟩

/-- A transition morphism, as a morphism of algebraic spaces. -/
private abbrev stTr {i j : I} (e : i ⟶ j) : stSp B S hS D hD i ⟶ stSp B S hS D hD j :=
  ObjectProperty.homMk (D.map e)

/-- The limit, as an algebraic space. -/
private abbrev limSpace (hXl : IsAlgebraicSpace B S hS (limit D)) : AlgebraicSpaces B S hS :=
  ⟨limit D, hXl⟩

/-- The projection of the limit to a stage. -/
private abbrev limProj (hXl : IsAlgebraicSpace B S hS (limit D)) (i : I) :
    limSpace B S hS D hXl ⟶ stSp B S hS D hD i :=
  ObjectProperty.homMk (limit.π D i)

variable {B S hS D} {a : I} {U₀ : BigAffineFppf B S hS}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj a}
  (C : AffineChartSystem B S hS a D U₀ g₀)

/-- A chart, as an algebraic space. -/
private abbrev chSp (r : Over a) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (C.siteDiagram.obj r), isAlgebraicSpace_yoneda B S hS _⟩

/-- The projection of a chart to its stage. -/
private abbrev stM (r : Over a) : yoneda.obj (C.siteDiagram.obj r) ⟶ D.obj r.left :=
  C.stageMap r

/-- The projection of a chart to the chosen point. -/
private abbrev bsM (r : Over a) :
    yoneda.obj (C.siteDiagram.obj r) ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) :=
  C.baseMap r

omit [IsCofiltered I] in
private theorem isPullback_stM (r : Over a) : IsPullback (stM C r) (bsM C r) (D.map r.hom) g₀ :=
  C.isPullback r

/-- A transition morphism of the charts, as a morphism of algebraic spaces. -/
private abbrev chMap {r r' : Over a} (d : r' ⟶ r) : chSp C r' ⟶ chSp C r :=
  ObjectProperty.homMk (yoneda.map (C.siteDiagram.map d))

omit [IsCofiltered I] in
private theorem bsM_naturality {r r' : Over a} (d : r' ⟶ r) :
    yoneda.map (C.siteDiagram.map d) ≫ bsM C r = bsM C r' := by
  have hnat : yoneda.map (C.siteDiagram.map d) ≫ C.iso.hom.app r =
      C.iso.hom.app r' ≫ (stageBaseChangeDiagram B S hS a D U₀ g₀).map d :=
    C.iso.hom.naturality d
  change yoneda.map (C.siteDiagram.map d) ≫ C.iso.hom.app r ≫
      stageBaseChangeSnd B S hS a D U₀ g₀ r =
    C.iso.hom.app r' ≫ stageBaseChangeSnd B S hS a D U₀ g₀ r'
  rw [← Category.assoc, hnat, Category.assoc, stageBaseChangeDiagram_map_comp_snd]

omit [IsCofiltered I] in
private theorem stM_naturality {r r' : Over a} (d : r' ⟶ r) :
    yoneda.map (C.siteDiagram.map d) ≫ stM C r = stM C r' ≫ D.map d.left := by
  have hnat : yoneda.map (C.siteDiagram.map d) ≫ C.iso.hom.app r =
      C.iso.hom.app r' ≫ (stageBaseChangeDiagram B S hS a D U₀ g₀).map d :=
    C.iso.hom.naturality d
  change yoneda.map (C.siteDiagram.map d) ≫ C.iso.hom.app r ≫
      stageBaseChangeFst B S hS a D U₀ g₀ r =
    (C.iso.hom.app r' ≫ stageBaseChangeFst B S hS a D U₀ g₀ r') ≫ D.map d.left
  rw [← Category.assoc, hnat, Category.assoc, stageBaseChangeDiagram_map_comp_fst,
    Category.assoc]

/-- The projection of a chart to its own stage, as a morphism of algebraic spaces. -/
private abbrev chartTo (r : Over a) : chSp C r ⟶ stSp B S hS D hD r.left :=
  ObjectProperty.homMk (stM C r)

omit [IsCofiltered I] in
private theorem chartTo_naturality {r r' : Over a} (d : r' ⟶ r) :
    chMap C d ≫ chartTo hD C r = chartTo hD C r' ≫ stTr B S hS D hD d.left :=
  ObjectProperty.hom_ext _ (stM_naturality C d)

omit [IsCofiltered I] in
private theorem stTr_comp {i j k : I} (e : i ⟶ j) (e' : j ⟶ k) :
    stTr B S hS D hD e ≫ stTr B S hS D hD e' = stTr B S hS D hD (e ≫ e') :=
  ObjectProperty.hom_ext _ (D.map_comp e e').symm

/-- The chart maps of a chart system to a space `W` through the stage `a`. -/
private abbrev chartToTarget {W : AlgebraicSpaces B S hS} (ρ : stSp B S hS D hD a ⟶ W)
    (r : Over a) : chSp C r ⟶ W :=
  chartTo hD C r ≫ stTr B S hS D hD r.hom ≫ ρ

omit [IsCofiltered I] in
private theorem chartToTarget_naturality {W : AlgebraicSpaces B S hS}
    (ρ : stSp B S hS D hD a ⟶ W) {r r' : Over a} (d : r' ⟶ r) :
    chMap C d ≫ chartToTarget hD C ρ r = chartToTarget hD C ρ r' := by
  simp only [chartToTarget]
  rw [← Category.assoc, chartTo_naturality, Category.assoc, ← Category.assoc
    (stTr B S hS D hD d.left), stTr_comp, Over.w d]

variable {C} (L : AffineChartSystem.LimitBridge C) (hXl : IsAlgebraicSpace B S hS (limit D))

/-- The limit of the charts, as an algebraic space. -/
private abbrev limChSp : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj L.cone.pt, isAlgebraicSpace_yoneda B S hS _⟩

/-- The projection of the limit of the charts to a chart. -/
private abbrev chCone (r : Over a) : limChSp L ⟶ chSp C r :=
  ObjectProperty.homMk (yoneda.map (L.cone.π.app r))

/-- The limit of the charts, mapping to the limit of the system. -/
private abbrev chartLim : limChSp L ⟶ limSpace B S hS D hXl :=
  ObjectProperty.homMk L.toLimit

omit [IsCofiltered I] in
private theorem toLimit_stM (r : Over a) :
    L.toLimit ≫ limit.π D r.left = yoneda.map (L.cone.π.app r) ≫ stM C r :=
  L.toLimit_comp_limitπ r

omit [IsCofiltered I] in
private theorem cone_bsM (r : Over a) : yoneda.map (L.cone.π.app r) ≫ bsM C r = L.toBase :=
  L.baseMap_comp r

omit [IsCofiltered I] in
private theorem chartLim_limProj (r : Over a) :
    chartLim L hXl ≫ limProj B S hS D hD hXl r.left = chCone L r ≫ chartTo hD C r :=
  ObjectProperty.hom_ext _ (toLimit_stM L r)

omit [IsCofiltered I] in
private theorem limProj_comp {i j : I} (e : i ⟶ j) :
    limProj B S hS D hD hXl i ≫ stTr B S hS D hD e = limProj B S hS D hD hXl j :=
  ObjectProperty.hom_ext _ (limit.w D e)

omit [IsCofiltered I] in
private theorem chCone_chMap {r r' : Over a} (d : r' ⟶ r) :
    chCone L r' ≫ chMap C d = chCone L r := by
  apply ObjectProperty.hom_ext
  change yoneda.map (L.cone.π.app r') ≫ yoneda.map (C.siteDiagram.map d) =
    yoneda.map (L.cone.π.app r)
  rw [← Functor.map_comp, L.cone.w d]

omit [IsCofiltered I] in
private theorem chartToTarget_cone {W : AlgebraicSpaces B S hS}
    (ρ : stSp B S hS D hD a ⟶ W) (r : Over a) :
    chCone L r ≫ chartToTarget hD C ρ r = chartLim L hXl ≫ limProj B S hS D hD hXl a ≫ ρ := by
  simp only [chartToTarget]
  rw [← Category.assoc, ← chartLim_limProj, Category.assoc, ← Category.assoc
    (limProj B S hS D hD hXl r.left), limProj_comp]

end Charts

/-! ### Faithfulness over the base changes of a quasi-compact space -/

section Faithful

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
  (hconv : SiteContainsBaseChangeLimits B S hS D) (hXl : IsAlgebraicSpace B S hS (limit D))

include hAffine hconv in
/-- **Faithfulness over the base changes of a quasi-compact space.** Let `τ : T ⟶ X_a` be a
morphism from a quasi-compact algebraic space to a stage and `ρ : X_a ⟶ W`. Two homomorphisms
`(τ ≫ ρ)^*E ⟶ (τ ≫ ρ)^*G` whose restrictions to `T ×_{X_a} X` agree have equal restrictions to
`T ×_{X_a} X_r` for some stage `r` over `a`. -/
private theorem eventually_restrict_eq {a : I} {T W : AlgebraicSpaces B S hS}
    (τ : T ⟶ stSp B S hS D hD a) (ρ : stSp B S hS D hD a ⟶ W)
    (hT : IsQuasiCompactSpace B S hS T.1) {E G : Modules.{u, u} B S hS W.1 W.2}
    (hE : E.IsFinitePresentationOnSite) (hG : G.IsQuasicoherentOnSite)
    (ζ ζ' : (modulePullback B S hS (τ ≫ ρ)).obj E ⟶ (modulePullback B S hS (τ ≫ ρ)).obj G)
    (h : restrictPullbackHom (fiberFst τ (limProj B S hS D hD hXl a))
        (rfl : fiberFst τ (limProj B S hS D hD hXl a) ≫ τ ≫ ρ = _) ζ =
      restrictPullbackHom (fiberFst τ (limProj B S hS D hD hXl a)) rfl ζ') :
    ∃ r : Over a,
      restrictPullbackHom (fiberFst τ (stTr B S hS D hD r.hom))
          (rfl : fiberFst τ (stTr B S hS D hD r.hom) ≫ τ ≫ ρ = _) ζ =
        restrictPullbackHom (fiberFst τ (stTr B S hS D hD r.hom)) rfl ζ' := by
  classical
  obtain ⟨U₀, w₀', he₀', hs₀'⟩ := exists_affine_etale_presheafSurjective T.2 hT
  let C := affineChartSystem B S hS a D U₀ (w₀' ≫ τ.hom) hAffine
  let L := C.limitBridgeOfLimitInSite (C.limitInSite_of_siteContainsBaseChangeLimits hconv)
  let m : ∀ r : Over a, chSp C r ⟶ T := fun r => ObjectProperty.homMk (bsM C r ≫ w₀')
  have hm : ∀ r, m r ≫ τ ≫ ρ = chartToTarget hD C ρ r := fun r => by
    apply ObjectProperty.hom_ext
    change (bsM C r ≫ w₀') ≫ τ.hom ≫ ρ.hom = stM C r ≫ D.map r.hom ≫ ρ.hom
    rw [← Category.assoc (stM C r), (isPullback_stM C r).w]
    simp only [Category.assoc]
  let r₀ : Over a := Over.mk (𝟙 a)
  have wl : (L.toBase ≫ w₀') ≫ τ.hom = L.toLimit ≫ (limProj B S hS D hD hXl a).hom := by
    rw [Category.assoc]
    exact L.isPullback.w.symm
  let κl : limChSp L ⟶
      AlgebraicSpaces.fiberProduct B S hS τ (limProj B S hS D hD hXl a) :=
    ObjectProperty.homMk (pullback.lift (L.toBase ≫ w₀') L.toLimit wl)
  have hκl : κl ≫ fiberFst τ (limProj B S hS D hD hXl a) ≫ τ ≫ ρ =
      chartLim L hXl ≫ limProj B S hS D hD hXl a ≫ ρ := by
    apply ObjectProperty.hom_ext
    change pullback.lift (L.toBase ≫ w₀') L.toLimit wl ≫ pullback.fst _ _ ≫ τ.hom ≫ ρ.hom =
      L.toLimit ≫ (limProj B S hS D hD hXl a).hom ≫ ρ.hom
    rw [pullback.condition_assoc, pullback.lift_snd_assoc]
  have habl : chCone L r₀ ≫ m r₀ =
      κl ≫ fiberFst τ (limProj B S hS D hD hXl a) := by
    apply ObjectProperty.hom_ext
    change yoneda.map (L.cone.π.app r₀) ≫ bsM C r₀ ≫ w₀' =
      pullback.lift (L.toBase ≫ w₀') L.toLimit wl ≫ pullback.fst _ _
    rw [pullback.lift_fst, ← Category.assoc, cone_bsM]
  have key₀ : ∀ ξ : (modulePullback B S hS (τ ≫ ρ)).obj E ⟶ (modulePullback B S hS (τ ≫ ρ)).obj G,
      restrictPullbackHom (chCone L r₀) (chartToTarget_cone hD L hXl ρ r₀) (restrictPullbackHom
          (m r₀) (hm r₀) ξ) =
        restrictPullbackHom κl hκl
          (restrictPullbackHom (fiberFst τ (limProj B S hS D hD hXl a)) rfl ξ) :=
    fun ξ => restrict_restrict _ _ _ _ _ _ _ _ habl ξ
  obtain ⟨r, e, he⟩ := affine_exists_restrict_eq_of_restrict_eq C.siteDiagram L.cone
    L.schemeIsLimit C.isAffine_obj (chartToTarget hD C ρ)
    (chartLim L hXl ≫ limProj B S hS D hD hXl a ≫ ρ)
    (fun d => chartToTarget_naturality hD C ρ d) (chartToTarget_cone hD L hXl ρ) hE hG r₀
    (restrictPullbackHom (m r₀) (hm r₀) ζ) (restrictPullbackHom (m r₀) (hm r₀) ζ')
    (by refine (key₀ ζ).trans ?_; rw [h]; exact (key₀ ζ').symm)
  refine ⟨r, ?_⟩
  have wr : (bsM C r ≫ w₀') ≫ τ.hom = stM C r ≫ (stTr B S hS D hD r.hom).hom := by
    rw [Category.assoc]
    exact (isPullback_stM C r).w.symm
  let κ : chSp C r ⟶
      AlgebraicSpaces.fiberProduct B S hS τ (stTr B S hS D hD r.hom) :=
    ObjectProperty.homMk (pullback.lift (bsM C r ≫ w₀') (stM C r) wr)
  have hpb : IsPullback κ.hom (bsM C r) (pullback.fst τ.hom
      (stTr B S hS D hD r.hom).hom) w₀' := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback τ.hom (stTr B S hS D hD r.hom).hom).flip
    rw [show κ.hom ≫ pullback.snd _ _ = stM C r from pullback.lift_snd _ _ _]
    exact isPullback_stM C r
  obtain ⟨hκet, hκs⟩ := isEtale_and_presheafSurjective_of_isPullback hpb.flip he₀' hs₀'
  have hκ : κ ≫ fiberFst τ (stTr B S hS D hD r.hom) ≫ τ ≫ ρ = chartToTarget hD C ρ r := by
    apply ObjectProperty.hom_ext
    change pullback.lift (bsM C r ≫ w₀') (stM C r) wr ≫ pullback.fst _ _ ≫ τ.hom ≫ ρ.hom =
      stM C r ≫ (stTr B S hS D hD r.hom).hom ≫ ρ.hom
    rw [pullback.condition_assoc, pullback.lift_snd_assoc]
  have habr : chMap C e ≫ m r₀ =
      κ ≫ fiberFst τ (stTr B S hS D hD r.hom) := by
    apply ObjectProperty.hom_ext
    change yoneda.map (C.siteDiagram.map e) ≫ bsM C r₀ ≫ w₀' =
      pullback.lift (bsM C r ≫ w₀') (stM C r) wr ≫ pullback.fst _ _
    rw [pullback.lift_fst, ← Category.assoc, bsM_naturality C e]
  refine restrict_injective κ hκ hκet hκs ?_
  rw [← restrict_restrict _ (hm r₀) _ (chartToTarget_naturality hD C ρ e) _ rfl _ hκ habr ζ,
    ← restrict_restrict _ (hm r₀) _ (chartToTarget_naturality hD C ρ e) _ rfl _ hκ habr ζ']
  exact he

end Faithful

/-! ### Faithfulness at a stage -/

section StageFaithful

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
  (hconv : SiteContainsBaseChangeLimits B S hS D) (hXl : IsAlgebraicSpace B S hS (limit D))

include hAffine hconv in
private theorem eventually_map_eq {k : I} (hQc : IsQuasiCompactSpace B S hS (D.obj k))
    {E G : Modules.{u, u} B S hS (stSp B S hS D hD k).1
      (stSp B S hS D hD k).2}
    (hE : E.IsFinitePresentationOnSite) (hG : G.IsQuasicoherentOnSite) (φ ψ : E ⟶ G)
    (h : (modulePullback B S hS (limProj B S hS D hD hXl k)).map φ =
      (modulePullback B S hS (limProj B S hS D hD hXl k)).map ψ) :
    ∃ (j : I) (e : j ⟶ k), (modulePullback B S hS (stTr B S hS D hD e)).map φ =
      (modulePullback B S hS (stTr B S hS D hD e)).map ψ := by
  let X := stSp B S hS D hD k
  have hsl : fiberSnd (𝟙 X) (limProj B S hS D hD hXl k) ≫ limProj B S hS D hD hXl k =
      fiberFst (𝟙 X) (limProj B S hS D hD hXl k) ≫ 𝟙 X ≫ 𝟙 X := by
    rw [Category.comp_id, Category.comp_id]
    exact (AlgebraicSpaces.isPullback_fiberProduct B S hS (𝟙 X)
      (limProj B S hS D hD hXl k)).w.symm.trans (Category.comp_id _)
  obtain ⟨r, hr⟩ := eventually_restrict_eq hD hAffine hconv hXl (𝟙 X) (𝟙 X) hQc hE hG
    ((modulePullback B S hS (𝟙 X ≫ 𝟙 X)).map φ) ((modulePullback B S hS (𝟙 X ≫ 𝟙 X)).map ψ)
    (by rw [restrict_map, restrict_map, ← restrict_map _ hsl φ, ← restrict_map _ hsl ψ, h])
  rw [restrict_map, restrict_map] at hr
  let σ : stSp B S hS D hD r.left ⟶
      AlgebraicSpaces.fiberProduct B S hS (𝟙 X) (stTr B S hS D hD r.hom) :=
    ObjectProperty.homMk (pullback.lift (stTr B S hS D hD r.hom).hom (𝟙 _)
      (by simp))
  have hσ : σ ≫ fiberFst (𝟙 X) (stTr B S hS D hD r.hom) ≫ 𝟙 X ≫ 𝟙 X =
      stTr B S hS D hD r.hom := by
    rw [Category.comp_id, Category.comp_id]
    exact ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)
  refine ⟨r.left, r.hom, ?_⟩
  rw [← restrict_map σ hσ φ, ← restrict_map σ hσ ψ, hr]

end StageFaithful

/-! ### Fullness -/

section Full

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
  (hconv : SiteContainsBaseChangeLimits B S hS D) (hXl : IsAlgebraicSpace B S hS (limit D))

include hAffine hconv in
/-- **Fullness**, in the calculus of restrictions: a homomorphism `π_k^*E ⟶ π_k^*G` over the
limit is the restriction of a homomorphism at a later stage. -/
private theorem exists_restrict_eq_of_stage (hZ : B.Contains (⊤_ Scheme.{u}))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) {k : I}
    {E G : Modules.{u, u} B S hS (stSp B S hS D hD k).1 (stSp B S hS D hD k).2}
    (hE : E.IsFinitePresentationOnSite) (hG : G.IsQuasicoherentOnSite)
    (φ : (modulePullback B S hS (limProj B S hS D hD hXl k)).obj E ⟶
      (modulePullback B S hS (limProj B S hS D hD hXl k)).obj G) :
    ∃ (j : I) (e : j ⟶ k) (ψ : (modulePullback B S hS (stTr B S hS D hD e)).obj E ⟶
        (modulePullback B S hS (stTr B S hS D hD e)).obj G),
      restrictPullbackHom (limProj B S hS D hD hXl j) (limProj_comp hD hXl e) ψ = φ := by
  classical
  obtain ⟨U₀, f₀', he₀', hs₀'⟩ := exists_affine_etale_presheafSurjective (hD k) (hQc k)
  let C := affineChartSystem B S hS k D U₀ f₀' hAffine
  let L := C.limitBridgeOfLimitInSite (C.limitInSite_of_siteContainsBaseChangeLimits hconv)
  let X := stSp B S hS D hD k
  have hu : chartLim L hXl ≫ limProj B S hS D hD hXl k =
      chartLim L hXl ≫ limProj B S hS D hD hXl k ≫ 𝟙 X := by
    rw [Category.comp_id]
  obtain ⟨huet, hus⟩ := isEtale_and_presheafSurjective_of_isPullback L.isPullback.flip
    he₀' hs₀'
  obtain ⟨s, β, hβ₀⟩ := affine_exists_restrict_eq C.siteDiagram L.cone L.schemeIsLimit
    C.isAffine_obj L.isAffine_pt (chartToTarget hD C (𝟙 X))
    (chartLim L hXl ≫ limProj B S hS D hD hXl k ≫ 𝟙 X)
    (fun d => chartToTarget_naturality hD C (𝟙 X) d) (chartToTarget_cone hD L hXl (𝟙 X)) hE hG
    (restrictPullbackHom (chartLim L hXl) hu φ)
  have hβ : restrictPullbackHom (chCone L s) (chartToTarget_cone hD L hXl (𝟙 X) s) β =
      restrictPullbackHom (chartLim L hXl) hu φ := hβ₀
  let cs := chartTo hD C s
  let ρ := stTr B S hS D hD s.hom ≫ 𝟙 X
  let τ := fiberFst cs cs ≫ cs
  have hw : fiberFst cs cs ≫ cs = fiberSnd cs cs ≫ cs :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS cs cs).w
  have h₁ : fiberFst cs cs ≫ chartToTarget hD C (𝟙 X) s = τ ≫ ρ := by
    simp only [τ, ρ, chartToTarget, cs, Category.assoc]
  have h₂ : fiberSnd cs cs ≫ chartToTarget hD C (𝟙 X) s = τ ≫ ρ := by
    have e₂ : fiberSnd cs cs ≫ chartToTarget hD C (𝟙 X) s = (fiberSnd cs cs ≫ cs) ≫ ρ := by
      simp only [ρ, chartToTarget, cs, Category.assoc]
    rw [e₂, ← hw]
  have hqcU : IsQuasiCompactSpace B S hS (yoneda.obj (C.siteDiagram.obj s)) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj s)) := C.isAffine_obj s
    exact isQuasiCompactSpace_yoneda_obj B S hS inferInstance
  have hTqc : IsQuasiCompactSpace B S hS (AlgebraicSpaces.fiberProduct B S hS cs cs).1 :=
    isQuasiCompactSpace_pullback B S hS hZ cs.hom cs.hom (isAlgebraicSpace_yoneda B S hS _)
      (hD s.left) hqcU hqcU (hQs s.left)
  let fl := fiberFst τ (limProj B S hS D hD hXl s.left)
  let sl := fiberSnd τ (limProj B S hS D hD hXl s.left)
  have hflsl : fl ≫ τ = sl ≫ limProj B S hS D hD hXl s.left :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS τ (limProj B S hS D hD hXl s.left)).w
  have hsl : sl ≫ limProj B S hS D hD hXl k = fl ≫ τ ≫ ρ := by
    rw [← Category.assoc, hflsl, Category.assoc]
    simp only [ρ]
    rw [← Category.assoc (limProj B S hS D hD hXl s.left), limProj_comp, Category.comp_id]
  have hlim : ∀ (o : AlgebraicSpaces.fiberProduct B S hS cs cs ⟶ chSp C s) (ho : o ≫ cs = τ)
      (h : o ≫ chartToTarget hD C (𝟙 X) s = τ ≫ ρ),
      restrictPullbackHom fl (rfl : fl ≫ τ ≫ ρ = _) (restrictPullbackHom o h β) =
        restrictPullbackHom sl hsl φ := by
    intro o ho h
    have e1 : bsM C s ≫ f₀' = stM C s ≫ D.map s.hom := (isPullback_stM C s).w.symm
    have e2 : o.hom ≫ stM C s = τ.hom := congrArg (fun t => t.hom) ho
    have e3 : fl.hom ≫ τ.hom = sl.hom ≫ limit.π D s.left := congrArg (fun t => t.hom) hflsl
    have wℓ : sl.hom ≫ limit.π D k = (fl.hom ≫ o.hom ≫ bsM C s) ≫ f₀' := by
      simp only [Category.assoc]
      rw [e1, ← Category.assoc o.hom, e2, ← Category.assoc, e3, Category.assoc, limit.w]
    let ℓ : AlgebraicSpaces.fiberProduct B S hS τ (limProj B S hS D hD hXl s.left) ⟶ limChSp L :=
      ObjectProperty.homMk (L.isPullback.lift sl.hom (fl.hom ≫ o.hom ≫ bsM C s) wℓ)
    have hℓu : ℓ ≫ chartLim L hXl = sl := ObjectProperty.hom_ext _ (L.isPullback.lift_fst _ _ _)
    have hℓc : fl ≫ o = ℓ ≫ chCone L s := by
      apply ObjectProperty.hom_ext
      change fl.hom ≫ o.hom = L.isPullback.lift sl.hom (fl.hom ≫ o.hom ≫ bsM C s) wℓ ≫
        yoneda.map (L.cone.π.app s)
      refine (isPullback_stM C s).hom_ext ?_ ?_
      · simp only [Category.assoc]
        rw [e2, e3, ← toLimit_stM L s, ← Category.assoc, IsPullback.lift_fst]
      · simp only [Category.assoc]
        rw [cone_bsM L s, IsPullback.lift_snd]
    have hℓ : ℓ ≫ chartLim L hXl ≫ limProj B S hS D hD hXl k ≫ 𝟙 X = fl ≫ τ ≫ ρ := by
      rw [← Category.assoc, hℓu, Category.comp_id, hsl]
    rw [restrict_restrict o h fl rfl _ (chartToTarget_cone hD L hXl (𝟙 X) s) ℓ hℓ hℓc β, hβ]
    exact restrict_restrict_single (chartLim L hXl) hu ℓ hℓ sl hsl hℓu φ
  obtain ⟨r, hr⟩ := eventually_restrict_eq hD hAffine hconv hXl τ ρ hTqc hE hG
    (restrictPullbackHom _ h₁ β) (restrictPullbackHom _ h₂ β)
    ((hlim _ rfl h₁).trans (hlim _ hw.symm h₂).symm)
  let s' : Over k := Over.mk (r.hom ≫ s.hom)
  let d : s' ⟶ s := Over.homMk r.hom rfl
  let cs' := chartTo hD C s'
  let c : PUnit.{1} → (chSp C s' ⟶ stSp B S hS D hD s'.left) := fun _ => cs'
  let q : PUnit.{1} → (chSp C s' ⟶ X) := fun _ => chartToTarget hD C (𝟙 X) s'
  have hq : ∀ i, c i ≫ (stTr B S hS D hD s'.hom ≫ 𝟙 X) = q i := fun _ => rfl
  obtain ⟨hcs'et, hcs's⟩ := isEtale_and_presheafSurjective_of_isPullback
    (isPullback_stM C s').flip he₀' hs₀'
  have hEq : E.IsQuasicoherentOnSite := by have := hE; infer_instance
  let o₁ := overlapFst c PUnit.unit PUnit.unit
  let o₂ := overlapSnd c PUnit.unit PUnit.unit
  have hnat : yoneda.map (C.siteDiagram.map d) ≫ stM C s = stM C s' ≫ D.map r.hom :=
    stM_naturality C d
  have hcond : o₁.hom ≫ stM C s' = o₂.hom ≫ stM C s' := pullback.condition
  have wμ₁ : (o₁.hom ≫ yoneda.map (C.siteDiagram.map d)) ≫ stM C s =
      (o₂.hom ≫ yoneda.map (C.siteDiagram.map d)) ≫ stM C s := by
    rw [Category.assoc, Category.assoc, hnat, ← Category.assoc, hcond, Category.assoc]
  let μT : overlapSpace c PUnit.unit PUnit.unit ⟶ AlgebraicSpaces.fiberProduct B S hS cs cs :=
    ObjectProperty.homMk (pullback.lift (o₁.hom ≫ yoneda.map (C.siteDiagram.map d))
      (o₂.hom ≫ yoneda.map (C.siteDiagram.map d)) wμ₁)
  have hμTfst : μT.hom ≫ (fiberFst cs cs).hom = o₁.hom ≫ yoneda.map (C.siteDiagram.map d) :=
    pullback.lift_fst _ _ _
  have hμTsnd : μT.hom ≫ (fiberSnd cs cs).hom = o₂.hom ≫ yoneda.map (C.siteDiagram.map d) :=
    pullback.lift_snd _ _ _
  have wμ₂ : μT.hom ≫ τ.hom = (o₁.hom ≫ stM C s') ≫ D.map r.hom := by
    change μT.hom ≫ (fiberFst cs cs).hom ≫ stM C s = _
    rw [← Category.assoc, hμTfst, Category.assoc, hnat, Category.assoc]
  let μ : overlapSpace c PUnit.unit PUnit.unit ⟶
      AlgebraicSpaces.fiberProduct B S hS τ (stTr B S hS D hD r.hom) :=
    ObjectProperty.homMk (pullback.lift μT.hom (o₁.hom ≫ stM C s') wμ₂)
  have hμfst : μ.hom ≫ (fiberFst τ (stTr B S hS D hD r.hom)).hom = μT.hom :=
    pullback.lift_fst _ _ _
  have hμsnd : μ.hom ≫ (fiberSnd τ (stTr B S hS D hD r.hom)).hom = o₁.hom ≫ stM C s' :=
    pullback.lift_snd _ _ _
  have hμsnd' : μ ≫ fiberSnd τ (stTr B S hS D hD r.hom) = o₁ ≫ cs' :=
    ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)
  have hμ : μ ≫ fiberFst τ (stTr B S hS D hD r.hom) ≫ τ ≫ ρ = o₁ ≫ q PUnit.unit := by
    have hsq := (AlgebraicSpaces.isPullback_fiberProduct B S hS τ (stTr B S hS D hD r.hom)).w
    rw [reassoc_of% hsq, ← Category.assoc, hμsnd']
    simp only [ρ, q, chartToTarget, cs', Category.assoc]
    rw [← Category.assoc (stTr B S hS D hD r.hom), stTr_comp]
    rfl
  have hμ₁ : o₁ ≫ chMap C d = μ ≫ fiberFst τ (stTr B S hS D hD r.hom) ≫ fiberFst cs cs := by
    apply ObjectProperty.hom_ext
    change o₁.hom ≫ yoneda.map (C.siteDiagram.map d) =
      μ.hom ≫ (fiberFst τ (stTr B S hS D hD r.hom)).hom ≫ (fiberFst cs cs).hom
    rw [← Category.assoc, hμfst, hμTfst]
  have hμ₂ : o₂ ≫ chMap C d = μ ≫ fiberFst τ (stTr B S hS D hD r.hom) ≫ fiberSnd cs cs := by
    apply ObjectProperty.hom_ext
    change o₂.hom ≫ yoneda.map (C.siteDiagram.map d) =
      μ.hom ≫ (fiberFst τ (stTr B S hS D hD r.hom)).hom ≫ (fiberSnd cs cs).hom
    rw [← Category.assoc, hμfst, hμTsnd]
  let β' := restrictPullbackHom (chMap C d) (chartToTarget_naturality hD C (𝟙 X) d) β
  have hagree : RestrictionsAgree (stTr B S hS D hD s'.hom ≫ 𝟙 X) c q hq (fun _ => β') := by
    rintro ⟨⟩ ⟨⟩
    have hba₁ : (fiberFst τ (stTr B S hS D hD r.hom) ≫ fiberFst cs cs) ≫
        chartToTarget hD C (𝟙 X) s = fiberFst τ (stTr B S hS D hD r.hom) ≫ τ ≫ ρ := by
      rw [Category.assoc, h₁]
    have hba₂ : (fiberFst τ (stTr B S hS D hD r.hom) ≫ fiberSnd cs cs) ≫
        chartToTarget hD C (𝟙 X) s = fiberFst τ (stTr B S hS D hD r.hom) ≫ τ ≫ ρ := by
      rw [Category.assoc, h₂]
    have hβ₁ := (restrict_restrict (chMap C d) (chartToTarget_naturality hD C (𝟙 X) d) o₁
      (rfl : o₁ ≫ q PUnit.unit = _) _ hba₁ μ hμ hμ₁ β).trans
      (congrArg (restrictPullbackHom μ hμ) (restrictPullbackHom_comp _ h₁ _ rfl hba₁ β))
    have hβ₂ := (restrict_restrict (chMap C d) (chartToTarget_naturality hD C (𝟙 X) d) o₂
      (overlapSnd_comp_eq _ c q hq PUnit.unit PUnit.unit) _ hba₂ μ hμ hμ₂ β).trans
      (congrArg (restrictPullbackHom μ hμ) (restrictPullbackHom_comp _ h₂ _ rfl hba₂ β))
    exact hβ₁.trans ((congrArg (restrictPullbackHom μ hμ) hr).trans hβ₂.symm)
  obtain ⟨χ, hχ, -⟩ := gluesModuleHomAlongFpqcCovering.{u, 0} (B := B) (S := S) (hS := hS) _ c q hq
    (isFpqcCovering_of_etale_surjective cs' hcs'et hcs's) E G
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ E hEq)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ G hG)
    (fun _ => β') hagree
  have hid : 𝟙 _ ≫ (stTr B S hS D hD s'.hom ≫ 𝟙 X) = stTr B S hS D hD s'.hom := by
    rw [Category.id_comp, Category.comp_id]
  refine ⟨s'.left, s'.hom, restrictPullbackHom (𝟙 _) hid χ, ?_⟩
  have hπ : limProj B S hS D hD hXl s'.left ≫ (stTr B S hS D hD s'.hom ≫ 𝟙 X) =
      limProj B S hS D hD hXl k := by
    rw [Category.comp_id, limProj_comp]
  refine restrict_injective (chartLim L hXl) hu huet hus ?_
  rw [restrict_restrict_single (𝟙 _) hid _ (limProj_comp hD hXl s'.hom) _ hπ
      (Category.comp_id _),
    restrict_restrict _ hπ _ hu _ (hq PUnit.unit) _ (chartToTarget_cone hD L hXl (𝟙 X) s')
      (chartLim_limProj hD L hXl s'), hχ PUnit.unit]
  exact (restrict_restrict_single (chMap C d) (chartToTarget_naturality hD C (𝟙 X) d) _
    (chartToTarget_cone hD L hXl (𝟙 X) s') _ (chartToTarget_cone hD L hXl (𝟙 X) s)
    (chCone_chMap L d) β).trans hβ

end Full

/-! ### The interface statements, proved in the private scope -/

section Interface

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

private theorem stage_map_eq_aux
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i)) {k : I}
    {E G : Modules.{u, u} B S hS (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS).1
      (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS).2}
    (hE : E.IsFinitePresentationOnSite) (hG : G.IsQuasicoherentOnSite) (φ ψ : E ⟶ G)
    (h : (modulePullback B S hS
        (ObjectProperty.homMk (limit.π D k) :
          (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
            hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).map φ =
      (modulePullback B S hS
        (ObjectProperty.homMk (limit.π D k) :
          (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
            hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).map ψ) :
    ∃ (j : I) (e : j ⟶ k),
      (modulePullback B S hS (ObjectProperty.homMk (D.map e) :
        (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).map φ =
      (modulePullback B S hS (ObjectProperty.homMk (D.map e) :
        (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).map ψ :=
  eventually_map_eq hD hAffine hconv _ (hQc k) hE hG φ ψ h

private theorem stage_map_eq_conj_aux
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) {k : I}
    {E G : Modules.{u, u} B S hS (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS).1
      (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS).2}
    (hE : E.IsFinitePresentationOnSite) (hG : G.IsQuasicoherentOnSite)
    (φ : (modulePullback B S hS
        (ObjectProperty.homMk (limit.π D k) :
          (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
            hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).obj E ⟶
      (modulePullback B S hS
        (ObjectProperty.homMk (limit.π D k) :
          (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
            hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).obj G) :
    ∃ (j : I) (e : j ⟶ k)
      (ψ : (modulePullback B S hS (ObjectProperty.homMk (D.map e) :
          (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).obj E ⟶
        (modulePullback B S hS (ObjectProperty.homMk (D.map e) :
          (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).obj G),
      restrictPullbackHom
        (ObjectProperty.homMk (limit.π D j) :
          (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
            hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS))
        (ObjectProperty.hom_ext _ (limit.w D e) :
          (ObjectProperty.homMk (limit.π D j) :
            (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
              hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS)) ≫
            (ObjectProperty.homMk (D.map e) : (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS)) =
            (ObjectProperty.homMk (limit.π D k) :
              (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
                hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))) ψ = φ :=
  exists_restrict_eq_of_stage hD hAffine hconv
    (isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD hAffine hQc)
    hZ hQc hQs hE hG φ

end Interface

end AlgebraicGeometry.Space

end

/-! ## The interface -/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Equality of morphisms of modules on a stage is detected at a later stage**, for a system
under the chapter's convention. Let `X = lim Xᵢ` be the limit of a cofiltered system of
quasi-compact algebraic spaces over `S` with affine transition morphisms satisfying the
convention of Section 70.2 (tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.
Two morphisms `E ⟶ G` of modules on a stage, `E` of finite presentation and `G` quasi-coherent,
whose inverse images to `X` agree, have equal inverse images to some later stage.

This is the faithfulness clause of the colimit assertion of Stacks 07V7 for such a system. -/
theorem exists_stage_modulePullback_map_eq_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i)) {k : I}
    {E G : Modules.{u, u} B S hS (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS).1
      (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS).2}
    (hE : E.IsFinitePresentationOnSite) (hG : G.IsQuasicoherentOnSite) (φ ψ : E ⟶ G)
    (h : (modulePullback B S hS
        (ObjectProperty.homMk (limit.π D k) :
          (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
            hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).map φ =
      (modulePullback B S hS
        (ObjectProperty.homMk (limit.π D k) :
          (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
            hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).map ψ) :
    ∃ (j : I) (e : j ⟶ k),
      (modulePullback B S hS (ObjectProperty.homMk (D.map e) :
        (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).map φ =
      (modulePullback B S hS (ObjectProperty.homMk (D.map e) :
        (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).map ψ :=
  stage_map_eq_aux B S hS D hconv hD hAffine hQc hE hG φ ψ h

/-- **A morphism of modules over the limit comes from a later stage**, for a system under the
chapter's convention. Let `X = lim Xᵢ` be the limit of a cofiltered system of quasi-compact and
quasi-separated algebraic spaces over `S` with affine transition morphisms satisfying the
convention of Section 70.2 (tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.
For modules `E`, `G` on a stage `Xₖ`, `E` of finite presentation and `G` quasi-coherent, every
morphism `φ : πₖ^*E ⟶ πₖ^*G` over `X` is the restriction
(`AlgebraicGeometry.Space.restrictPullbackHom`) along `πⱼ` of a morphism `ψ` between the inverse
images of `E` and `G` to some later stage `Xⱼ`. Unfolded, `restrictPullbackHom πⱼ _ ψ = φ` says
`πⱼ^*ψ` is `φ` read through the comparisons `AlgebraicGeometry.Space.modulePullbackTriangle` of
`πⱼ ≫ (Xⱼ ⟶ Xₖ) = πₖ`, which is the shape of `Stacks.ModuleColimit.PullbackSystem.Fullness`.

This is the fullness clause of the colimit assertion of Stacks 07V7 for such a system. -/
theorem exists_stage_restrictPullbackHom_eq_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) {k : I}
    {E G : Modules.{u, u} B S hS (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS).1
      (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS).2}
    (hE : E.IsFinitePresentationOnSite) (hG : G.IsQuasicoherentOnSite)
    (φ : (modulePullback B S hS
        (ObjectProperty.homMk (limit.π D k) :
          (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
            hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).obj E ⟶
      (modulePullback B S hS
        (ObjectProperty.homMk (limit.π D k) :
          (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
            hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).obj G) :
    ∃ (j : I) (e : j ⟶ k)
      (ψ : (modulePullback B S hS (ObjectProperty.homMk (D.map e) :
          (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).obj E ⟶
        (modulePullback B S hS (ObjectProperty.homMk (D.map e) :
          (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))).obj G),
      restrictPullbackHom
        (ObjectProperty.homMk (limit.π D j) :
          (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
            hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS))
        (ObjectProperty.hom_ext _ (limit.w D e) :
          (ObjectProperty.homMk (limit.π D j) :
            (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
              hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS)) ≫
            (ObjectProperty.homMk (D.map e) : (⟨D.obj j, hD j⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS)) =
            (ObjectProperty.homMk (limit.π D k) :
              (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
                hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                (⟨D.obj k, hD k⟩ : AlgebraicSpaces B S hS))) ψ = φ :=
  stage_map_eq_conj_aux B S hS D hconv hD hAffine hZ hQc hQs hE hG φ

end AlgebraicGeometry.Space

end
