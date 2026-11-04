module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparationLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# Open subspaces of a stage of an inverse system along monomorphisms

Let `D` be a directed inverse system of algebraic spaces with limit `lim D`, and `V` a subfunctor
of a stage `D_{i₀}`, for instance the open complement `D_{i₀} ∖ T` of a closed subspace.  Its
inverse images `V ×_{D_{i₀}} D_k`, `k ≥ i₀`, form an inverse system whose limit is the inverse
image `V ×_{D_{i₀}} lim D`; for `V = D_{i₀} ∖ T` the stages are the open complements
`D_k ∖ (T ×_{D_{i₀}} D_k)` and the limit is `lim D ∖ (T ×_{D_{i₀}} lim D)`.

The proof of Stacks 0GV1 uses this for the system `Y = lim Y_k` of Stacks 07VR, whose
transition morphisms are closed immersions, and the closed subspace `Z_k = V(ℐ_k)` descending
`Z = V(ℐ) ⊆ Y`: it needs the open `V_k = Y_k ∖ Z_k` to be affine, étale and surjective over the
base for `k` large (Stacks 07SQ, 07SL, 07SN).  Along monomorphic transition morphisms the
chapter's convention (Stacks 07SD) holds automatically, and more is true: if the limit is locally
of finite presentation over the base, it *is* a stage.

## Main definitions

* `AlgebraicGeometry.Space.limitTailToStage`: the transition morphisms from the stages at or
  beyond `i₀` to `D_{i₀}`; the system of inverse images of `V` is
  `CategoryTheory.Subfunctor.preimageDiagram (limitTailToStage D i₀) V`.

## Main results

* `AlgebraicGeometry.Space.isLimitPreimageConeLimitTail`: the inverse image of `V` in the limit
  is the limit of the system of inverse images.
* `AlgebraicGeometry.Space.preimageDiagram_limitTailToStage_openComplement_obj` and
  `AlgebraicGeometry.Space.preimageCone_limitTailToStage_openComplement_pt`: for an open
  complement, the stages and the limit are open complements.
* `AlgebraicGeometry.Space.exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_mono`
  and `AlgebraicGeometry.Space.exists_isAffineSpace_openComplement_preimage_of_mono`: Stacks 07SQ
  along monomorphisms.
* `AlgebraicGeometry.Space.exists_iso_preimage_of_isLocallyOfFinitePresentation_of_mono`: along
  monomorphisms, the inverse image in the limit is that in a stage, when both are locally of
  finite presentation over a base.
* `AlgebraicGeometry.Space.exists_isEtale_isSurjective_preimage_of_mono`: Stacks 07SL, 07SN (and
  07SQ) along monomorphisms, read off the previous result.

## Implementation notes

The system of inverse images, its limit and the convention for it are those of the base:
`CategoryTheory.Subfunctor.preimageDiagram`, `CategoryTheory.Subfunctor.isLimitPreimageCone` and
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.preimageDiagram`, over the tail
`AlgebraicGeometry.LimitTail` of the index set.  The convention for `D` itself comes from the
monomorphic transition morphisms,
`AlgebraicGeometry.Space.IsSiteSmall.siteContainsBaseChangeLimits`.

The statements for étale and surjective morphisms are not drawn from Stacks 07SL and 07SN in
the form of `AlgebraicGeometry.Space.MorphismDescentSituation`, which descends a morphism over a
varying base `B_k`: here the base `X` is fixed and the source varies, which is not of that form.
Instead the source is shown to be eventually equal to its limit, by the two halves of Stacks 0CP4
(`Space.exists_stage_map_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits`,
`Space.exists_stage_eq_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits`).

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07SL](https://stacks.math.columbia.edu/tag/07SL)
* [Stacks Project, Tag 07SN](https://stacks.math.columbia.edu/tag/07SN)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i₀ : I)

/-! ### The inverse images of a subspace of a stage, as a system -/

/-- **The transition morphisms from the stages at or beyond `i₀` to the stage `i₀`**, as a
natural transformation from the tail of `D` to the constant system at `D_{i₀}`.  The inverse
images of a subfunctor `V ⊆ D_{i₀}` along it form the system
`CategoryTheory.Subfunctor.preimageDiagram (limitTailToStage D i₀) V` of the `V ×_{D_{i₀}} D_k`,
`k ≥ i₀`. -/
def limitTailToStage :
    limitTailForget i₀ ⋙ D ⟶ (Functor.const (LimitTail I i₀)ᵒᵖ).obj (D.obj (op i₀)) where
  app j := D.map (homOfLE j.unop.2).op
  naturality j k φ :=
    ((D.map_comp ((limitTailForget i₀).map φ) ((homOfLE k.unop.2).op)).symm.trans
      (congrArg (fun x : (limitTailForget i₀).obj j ⟶ op i₀ => D.map x)
        (Subsingleton.elim _ _))).trans (Category.comp_id _).symm

/-- The component of `limitTailToStage D i₀` at a stage `D_k`, `k ≥ i₀`, is the transition
morphism `D_k ⟶ D_{i₀}`. -/
@[simp]
theorem limitTailToStage_app (j : (LimitTail I i₀)ᵒᵖ) :
    (limitTailToStage D i₀).app j = D.map (homOfLE j.unop.2).op :=
  rfl

variable {D} in
/-- The projections of a cone over `D` to the stages at or beyond `i₀`, followed by the
transitions to `D_{i₀}`, are the projection to `D_{i₀}`. -/
theorem whisker_limitTailForget_π_comp_limitTailToStage (c : Cone D)
    (j : (LimitTail I i₀)ᵒᵖ) :
    (c.whisker (limitTailForget i₀)).π.app j ≫ (limitTailToStage D i₀).app j = c.π.app (op i₀) :=
  c.w (homOfLE j.unop.2).op

variable {D} in
/-- The restriction of a limit cone of a directed system to the stages at or beyond `i₀` is a
limit cone. -/
def isLimitWhiskerLimitTailForget [IsDirected I (· ≤ ·)] {c : Cone D} (hc : IsLimit c) :
    IsLimit (c.whisker (limitTailForget i₀)) :=
  haveI : (limitTailForget i₀).Initial := by dsimp only [limitTailForget]; infer_instance
  (Functor.Initial.isLimitWhiskerEquiv (limitTailForget i₀) c).symm hc

variable {D} in
/-- **The inverse image of a subfunctor `V` of the stage `D_{i₀}` in the limit is the limit of
its inverse images in the stages at or beyond `i₀`.** -/
def isLimitPreimageConeLimitTail [IsDirected I (· ≤ ·)] {c : Cone D} (hc : IsLimit c)
    (V : Subfunctor (D.obj (op i₀))) :
    IsLimit (Subfunctor.preimageCone (limitTailToStage D i₀) V
      (whisker_limitTailForget_π_comp_limitTailToStage i₀ c)) :=
  haveI : Nonempty (LimitTail I i₀)ᵒᵖ := ⟨op ⟨i₀, le_rfl⟩⟩
  Subfunctor.isLimitPreimageCone _ V _ (isLimitWhiskerLimitTailForget i₀ hc)

/-- **The stages of the system of inverse images of an open complement are open complements.**
For a subfunctor `T ⊆ D_{i₀}` the inverse image of `D_{i₀} ∖ T` in the stage `D_k` is
`D_k ∖ (T ×_{D_{i₀}} D_k)`. -/
theorem preimageDiagram_limitTailToStage_openComplement_obj (T : Subfunctor (D.obj (op i₀)))
    (j : (LimitTail I i₀)ᵒᵖ) :
    (Subfunctor.preimageDiagram (limitTailToStage D i₀) (openComplement B S hS T)).obj j =
      (openComplement B S hS (T.preimage (D.map (homOfLE j.unop.2).op))).toFunctor :=
  congrArg Subfunctor.toFunctor (openComplement_preimage B S hS T _)

variable {D} in
/-- **The limit of the system of inverse images of an open complement is the open complement of
the inverse image.**  The point of the cone of inverse images of `D_{i₀} ∖ T` is
`lim D ∖ (T ×_{D_{i₀}} lim D)`. -/
theorem preimageCone_limitTailToStage_openComplement_pt (c : Cone D)
    (T : Subfunctor (D.obj (op i₀))) :
    (Subfunctor.preimageCone (limitTailToStage D i₀) (openComplement B S hS T)
        (whisker_limitTailForget_π_comp_limitTailToStage i₀ c)).pt =
      (openComplement B S hS (T.preimage (c.π.app (op i₀)))).toFunctor :=
  congrArg Subfunctor.toFunctor (openComplement_preimage B S hS T _)

/-! ### Along monomorphisms: the stages eventually agree with the limit -/

variable (B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 07SQ for the inverse images of a quasi-compact open subspace, along monomorphisms.**
Let `D` be a directed inverse system of algebraic spaces with affine monomorphic transition
morphisms (for instance closed immersions), quasi-separated stages and limit `c`, and let `V` be a
quasi-compact open subspace of the stage `D_{i₀}`.  If the inverse image of `V` in the limit is
affine, so is its inverse image in some stage `D_j`, `j ≥ i₀`.

This is
`exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_siteContainsBaseChangeLimits`,
the chapter's convention being discharged by the monomorphic transitions
(`AlgebraicGeometry.Space.IsSiteSmall.siteContainsBaseChangeLimits`). -/
theorem exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_mono
    [IsDirected I (· ≤ ·)] (c : Cone D) (hc : IsLimit c)
    (hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.obj a))
    (hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.map f))
    (hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj a))
    (hmono : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), Mono (D.map f))
    (V : Subfunctor (D.obj (op i₀))) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hW : IsAffineSpace B S hS (V.preimage (c.π.app (op i₀))).toFunctor) :
    ∃ (j : I) (hj : i₀ ≤ j),
      IsAffineSpace B S hS (V.preimage (D.map (homOfLE hj).op)).toFunctor :=
  have : Nonempty I := ⟨i₀⟩
  exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_siteContainsBaseChangeLimits
    B S hS hZ D c hc
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D (Or.inr fun _ _ f => hmono f))
    hD hAffine hQs i₀ V hV hVqc hW

/-- **The inverse image of a quasi-compact open subspace in the limit is reached at a stage, along
monomorphisms, once it is locally of finite presentation over a base.**  Let `D` be a directed
inverse system of quasi-separated algebraic spaces with affine monomorphic transition morphisms
(for instance closed immersions) and limit `c`, let `V` be a quasi-compact open subspace of the
stage `D_{i₀}`, and let `p : D_{i₀} ⟶ X` be a morphism to an algebraic space such that both
`V ⟶ X` and `W ⟶ X` are locally of finite presentation, where `W = V ×_{D_{i₀}} lim D`.  Then for
some `j ≥ i₀` the projection `W ⟶ V ×_{D_{i₀}} D_j` is an isomorphism.

The proof is Stacks 0CP4 for the system of inverse images of `V`, which satisfies the chapter's
convention because its transition morphisms are monomorphisms.  The surjectivity half
(`exists_stage_map_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits`)
retracts `W` off a stage over `X`; the injectivity half
(`exists_stage_eq_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits`),
read in `V`, makes the retraction a two-sided inverse after a further transition morphism, which
can be cancelled because it is a monomorphism.

In the proof of Stacks 0GV1 this is what makes the open complement of the ideal of the descended
closed subspace the chart `V` itself at a stage of the system of Stacks 07VR, so that it is
affine, étale and surjective over the base (Stacks 07SQ, 07SL, 07SN). -/
theorem exists_iso_preimage_of_isLocallyOfFinitePresentation_of_mono
    [IsDirected I (· ≤ ·)] (c : Cone D) (hc : IsLimit c)
    (hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.obj a))
    (hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.map f))
    (hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj a))
    (hmono : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), Mono (D.map f))
    (hc' : IsAlgebraicSpace B S hS c.pt)
    (V : Subfunctor (D.obj (op i₀))) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (p : D.obj (op i₀) ⟶ X) (hp : IsLocallyOfFinitePresentation B S hS (V.ι ≫ p))
    (hφ : IsLocallyOfFinitePresentation B S hS
      ((V.preimage (c.π.app (op i₀))).ι ≫ c.π.app (op i₀) ≫ p)) :
    ∃ (j : I) (hj : i₀ ≤ j) (e : (V.preimage (c.π.app (op i₀))).toFunctor ≅
        (V.preimage (D.map (homOfLE hj).op)).toFunctor),
      e.hom ≫ (V.preimage (D.map (homOfLE hj).op)).ι =
        (V.preimage (c.π.app (op i₀))).ι ≫ c.π.app (op j) := by
  classical
  have : Nonempty I := ⟨i₀⟩
  have : Nonempty (LimitTail I i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirected (LimitTail I i₀) (· ≤ ·) := ⟨fun x y => by
    obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) x.1 y.1
    exact ⟨⟨k, x.2.trans hxk⟩, hxk, hyk⟩⟩
  let G := limitTailForget i₀
  let τ := limitTailToStage D i₀
  let hσ := whisker_limitTailForget_π_comp_limitTailToStage i₀ c
  let E := Subfunctor.preimageDiagram τ V
  let cE := Subfunctor.preimageCone τ V hσ
  have hcE : IsLimit cE := isLimitPreimageConeLimitTail i₀ hc V
  have hpre : ∀ j, IsOpenSubspace B S hS (V.preimage (τ.app j)) := fun j =>
    isOpenSubspace_preimage B S hS (τ.app j) V (hD (op i₀)) (hD (G.obj j)) hV
  have hfrom : ∀ j, IsAffineHom B S hS (V.fromPreimage (τ.app j)) := fun j =>
    isAffineHom_of_isPullback' B S hS (Subfunctor.isPullback_fromPreimage V (τ.app j)).flip
      (hAffine (homOfLE j.unop.2).op)
  have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V.toFunctor :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hV.1 (hQs (op i₀))
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hV.2)))
  have hEalg : ∀ j, IsAlgebraicSpace B S hS (E.obj j) := fun j => (hpre j).1
  have hEqc : ∀ j, IsQuasiCompactSpace B S hS (E.obj j) := fun j =>
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hV.1 hVqc
      (isQuasiCompact_of_isAffineHom' B S hS (V.fromPreimage (τ.app j)) (hpre j).1 hV.1 (hfrom j))
  have hEqs : ∀ j, IsAbsolutelyQuasiSeparated B S hS hZ (E.obj j) := fun j =>
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (hpre j).1 hVqs
      (isQuasiSeparated_of_isAffineHom B S hS (V.fromPreimage (τ.app j)) (hpre j).1 hV.1
        (hfrom j))
  have hEaff : ∀ {j k : (LimitTail I i₀)ᵒᵖ} (φ : j ⟶ k), IsAffineHom B S hS (E.map φ) :=
    fun φ => isAffineHom_of_isPullback' B S hS
      (Subfunctor.isPullback_preimageDiagram_map τ V φ).flip (hAffine (G.map φ))
  have hEmono : ∀ {j k : (LimitTail I i₀)ᵒᵖ} (φ : j ⟶ k), Mono (E.map φ) := fun {j k} φ => by
    have := hmono (G.map φ)
    have : Mono (V.preimage (τ.app j)).ι := inferInstanceAs (Mono (Subfunctor.ι _))
    have : Mono (E.map φ ≫ (V.preimage (τ.app k)).ι) :=
      inferInstanceAs (Mono ((V.preimage (τ.app j)).ι ≫ D.map (G.map φ)))
    exact mono_of_mono _ (V.preimage (τ.app k)).ι
  have hconvE : SiteContainsBaseChangeLimits B S hS E :=
    SiteContainsBaseChangeLimits.preimageDiagram G τ V hAffine
      (IsSiteSmall.siteContainsBaseChangeLimits B S hS D (Or.inr fun _ _ f => hmono f))
  have hcEalg : IsAlgebraicSpace B S hS cE.pt :=
    (isOpenSubspace_preimage B S hS (c.π.app (op i₀)) V (hD _) hc' hV).1
  let ιW : cE.pt ⟶ c.pt := (V.preimage (c.π.app (op i₀))).ι
  have hπι : ∀ j, cE.π.app j ≫ (V.preimage (τ.app j)).ι = ιW ≫ c.π.app (G.obj j) := fun _ => rfl
  let j₀ : (LimitTail I i₀)ᵒᵖ := op ⟨i₀, le_rfl⟩
  let b : E.obj j₀ ⟶ X := (V.preimage (τ.app j₀)).ι ≫ τ.app j₀ ≫ p
  have hb : IsLocallyOfFinitePresentation B S hS b := by
    have : IsIso (τ.app j₀) := by
      change IsIso (D.map (𝟙 (op i₀)))
      infer_instance
    have : IsIso (V.fromPreimage (τ.app j₀)) :=
      (Subfunctor.isPullback_fromPreimage V (τ.app j₀)).isIso_fst_of_isIso
    have hb' : b = V.fromPreimage (τ.app j₀) ≫ V.ι ≫ p := by
      rw [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc]
      rfl
    rw [hb']
    exact isLocallyOfFinitePresentation_comp B S hS (hEalg j₀) hV.1 hX
      (V.fromPreimage (τ.app j₀)) (V.ι ≫ p)
      (isLocallyOfFinitePresentation_of_isOpenImmersion B S hS
        (isOpenImmersion_of_isIso B S hS (V.fromPreimage (τ.app j₀)))) hp
  have hsq : 𝟙 cE.pt ≫ (ιW ≫ c.π.app (op i₀) ≫ p) = cE.π.app j₀ ≫ b := by
    rw [Category.id_comp]
    change _ = (cE.π.app j₀ ≫ (V.preimage (τ.app j₀)).ι) ≫ τ.app j₀ ≫ p
    rw [hπι, Category.assoc, ← Category.assoc (c.π.app _) (τ.app j₀),
      show c.π.app (G.obj j₀) ≫ τ.app j₀ = c.π.app (op i₀) from hσ j₀]
  obtain ⟨j, t, k, a, a', ht1, ht2⟩ :=
    exists_stage_map_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B S hS hZ E cE
      hcE hconvE hEalg hEqc hEqs hEaff hcEalg hcEalg hX _ hφ (𝟙 _) j₀ b hsq
  obtain ⟨n, a2, hn⟩ :=
    exists_stage_eq_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B S hS hZ E cE
      hcE hconvE hEalg hEqc hEqs hEaff hcEalg (hEalg j₀) hX b hb k
      (((E.map a ≫ t) ≫ cE.π.app k) ≫ E.map a') (E.map a')
      (by
        rw [← Category.assoc, ← Category.assoc, ht1]
        exact congrArg (fun x => x ≫ E.map a') (Category.id_comp (cE.π.app k)))
      (calc (((E.map a ≫ t) ≫ cE.π.app k) ≫ E.map a') ≫ b
            = (E.map a ≫ t) ≫ (cE.π.app k ≫ E.map a') ≫ b := by simp only [Category.assoc]
          _ = (E.map a ≫ t) ≫ cE.π.app j₀ ≫ b := by rw [cE.w a']
          _ = (E.map a ≫ t) ≫ (ιW ≫ c.π.app (op i₀) ≫ p) := by
            rw [← hsq, Category.id_comp]
          _ = E.map a' ≫ b := ht2)
  have h1 : E.map a2 ≫ (E.map a ≫ t) ≫ cE.π.app k = E.map a2 := by
    have := hEmono a'
    rw [← cancel_mono (E.map a')]
    simpa only [Category.assoc] using hn
  have hn1 : cE.π.app n ≫ E.map a2 ≫ E.map a ≫ t = 𝟙 _ := by
    rw [← Category.assoc, cE.w a2]
    exact ht1
  have hn2 : (E.map a2 ≫ E.map a ≫ t) ≫ cE.π.app n = 𝟙 _ := by
    have := hEmono a2
    rw [← cancel_mono (E.map a2), Category.assoc, cE.w a2, Category.id_comp]
    simpa only [Category.assoc] using h1
  exact ⟨n.unop.1, n.unop.2,
    { hom := cE.π.app n
      inv := E.map a2 ≫ E.map a ≫ t
      hom_inv_id := hn1
      inv_hom_id := hn2 }, hπι n⟩

/-- **Stacks 07SQ, 07SL and 07SN for the inverse images of a quasi-compact open subspace, along
monomorphisms.**  In the setting of
`AlgebraicGeometry.Space.exists_iso_preimage_of_isLocallyOfFinitePresentation_of_mono`, if
`W = V ×_{D_{i₀}} lim D ⟶ X` is étale and surjective and `V ⟶ X` is locally of finite
presentation, then for some `j ≥ i₀` the morphism `V ×_{D_{i₀}} D_j ⟶ D_j ⟶ X` is étale and
surjective, and `V ×_{D_{i₀}} D_j` is affine if `W` is.  Indeed `W ⟶ V ×_{D_{i₀}} D_j` is an
isomorphism over `X` for some `j`. -/
theorem exists_isEtale_isSurjective_preimage_of_mono
    [IsDirected I (· ≤ ·)] (c : Cone D) (hc : IsLimit c)
    (hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.obj a))
    (hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.map f))
    (hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj a))
    (hmono : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), Mono (D.map f))
    (hc' : IsAlgebraicSpace B S hS c.pt)
    (V : Subfunctor (D.obj (op i₀))) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (p : D.obj (op i₀) ⟶ X) (hp : IsLocallyOfFinitePresentation B S hS (V.ι ≫ p))
    (het : IsEtale B S hS ((V.preimage (c.π.app (op i₀))).ι ≫ c.π.app (op i₀) ≫ p))
    (hsurj : IsSurjective B S hS ((V.preimage (c.π.app (op i₀))).ι ≫ c.π.app (op i₀) ≫ p)) :
    ∃ (j : I) (hj : i₀ ≤ j),
      IsEtale B S hS ((V.preimage (D.map (homOfLE hj).op)).ι ≫ D.map (homOfLE hj).op ≫ p) ∧
      IsSurjective B S hS
        ((V.preimage (D.map (homOfLE hj).op)).ι ≫ D.map (homOfLE hj).op ≫ p) ∧
      (IsAffineSpace B S hS (V.preimage (c.π.app (op i₀))).toFunctor →
        IsAffineSpace B S hS (V.preimage (D.map (homOfLE hj).op)).toFunctor) := by
  obtain ⟨j, hj, e, he⟩ := exists_iso_preimage_of_isLocallyOfFinitePresentation_of_mono B S hS D i₀
    hZ c hc hD hAffine hQs hmono hc' V hV hVqc hX p hp
    (isLocallyOfFinitePresentation_of_isEtale B S hS het)
  have hm : (V.preimage (D.map (homOfLE hj).op)).ι ≫ D.map (homOfLE hj).op ≫ p =
      e.inv ≫ ((V.preimage (c.π.app (op i₀))).ι ≫ c.π.app (op i₀) ≫ p) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, he, Category.assoc, ← Category.assoc (c.π.app _),
      c.w]
  exact ⟨j, hj, hm ▸ isEtale_comp B S hS (isEtale_of_isIso B S hS e.inv) het,
    hm ▸ isSurjective_comp B S hS (isSurjective_of_isIso B S hS e.inv) hsurj,
    fun hW => hW.of_iso e⟩

/-- **Stacks 07SQ for the open complements of a finitely presented closed subspace of a stage,
along monomorphisms.**  Let `D` be a directed inverse system of quasi-separated algebraic spaces
with affine monomorphic transition morphisms (for instance closed immersions) and limit `c`, let
the stage `D_{i₀}` be quasi-compact, and let `T ⊆ D_{i₀}` be a closed subspace of finite
presentation, for instance the zero locus `V(ℐ)` of a finite type quasi-coherent ideal
(`exists_closedSubspace_isFinitePresentation_ι_of_isFiniteTypeQuasicoherentIdeal`).
If `lim D ∖ (T ×_{D_{i₀}} lim D)` is affine, so is `D_j ∖ (T ×_{D_{i₀}} D_j)` for some
`j ≥ i₀`. -/
theorem exists_isAffineSpace_openComplement_preimage_of_mono
    [IsDirected I (· ≤ ·)] (c : Cone D) (hc : IsLimit c)
    (hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.obj a))
    (hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.map f))
    (hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj a))
    (hmono : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), Mono (D.map f))
    (hqc : IsQuasiCompactSpace B S hS (D.obj (op i₀)))
    (T : Subfunctor (D.obj (op i₀))) (hT : IsClosedSubspace B S hS T)
    (hTfp : IsFinitePresentation B S hS T.ι)
    (hW : IsAffineSpace B S hS
      (openComplement B S hS (T.preimage (c.π.app (op i₀)))).toFunctor) :
    ∃ (j : I) (hj : i₀ ≤ j), IsAffineSpace B S hS
      (openComplement B S hS (T.preimage (D.map (homOfLE hj).op))).toFunctor := by
  rw [← openComplement_preimage] at hW
  obtain ⟨j, hj, h⟩ := exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_mono
    B S hS D i₀ hZ c hc hD hAffine hQs hmono (openComplement B S hS T)
    (isOpenSubspace_openComplement B S hS (hD _) T hT)
    (isQuasiCompactSpace_openComplement_of_isFinitePresentation (hD _) hqc T hT hTfp) hW
  exact ⟨j, hj, by rwa [← openComplement_preimage]⟩

end AlgebraicGeometry.Space

end
