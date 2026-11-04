module

public import StacksFrontier.AlgebraicGeometry.Perfect.FinitePresentationGlobalSectionsModel
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsChainModel
public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyProperOverLimit
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Limits.SmallDominantIndex
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `RΓ` of a flat module along a proper morphism to an arbitrary affine base is perfect

Let `R` be a ring, `f : X ⟶ Spec R` a proper morphism of finite presentation and `G` an
`𝒪_X`-module of finite presentation, flat over `R`. This file proves that `RΓ(X, G)` is a perfect
object of `D(R)`, with no Noetherian hypothesis on `R`. Over an affine base this is the
perfection half of [Stacks, Tag 0B91] (2), equivalently of [Stacks, Tag 0A1H] at `E = 𝒪_X`, which
the library had only over a Noetherian base ([Stacks, Tag 07VK] (1)).

## Main results

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.isPerfect_of_isPullback`: perfection of
  `RΓ` travels along a cartesian base change `Spec A' ⟶ Spec A`, for a separated quasi-compact
  morphism and a quasi-coherent module flat over `A`; this is [Stacks, Tag 07VK] (2) applied to a
  finite projective model.
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_isPullback_model_of_isProper`: over
  the limit of a cofiltered system of quasi-compact quasi-separated schemes with affine
  transition morphisms, a proper morphism of finite presentation together with a module of
  finite presentation flat over the limit is the base change of such data at some stage
  ([Stacks, Tag 01ZM], [Stacks, Tag 081F], [Stacks, Tag 01ZR], [Stacks, Tag 05LY]).
* `ProperFlatGlobalSections.isPerfect_derivedGlobalSectionsOverBase_of_isProper`: the perfection
  statement, by descent to a finitely generated subring of `R`.

## Implementation notes

No `@[stacks]` attribute is attached. [Stacks, Tag 0B91] asserts perfection of `Rf_*G` in
`D(𝒪_S)` for an arbitrary base `S`, together with base change; what is proved here is the affine
case read in `D(R)` through `derivedGlobalSectionsOverBase`, which is the input the source's
uses of that tag over an affine open of the base consume.

As in `StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSections.lean`, everything runs
under `CategoryTheory.HasDerivedCategory.standard` at priority `10000`.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Perfection of `RΓ` is preserved by a cartesian affine base change.** For a separated
quasi-compact `f : X ⟶ Spec A`, a quasi-coherent `𝒪_X`-module `F` flat over `A` with `RΓ(X, F)`
perfect, and a cartesian square along `Spec A' ⟶ Spec A`, the object `RΓ(X', g^*F)` of `D(A')` is
perfect: by [Stacks, Tag 07VK] (2) it is `RΓ(X, F) ⊗^L_A A'`, and a finite projective model of
`RΓ(X, F)` extends to one of the base change. -/
theorem isPerfect_of_isPullback {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] [QuasiCompact f]
    {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) (F : X.Modules)
    [F.IsQuasicoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hF : StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase f F)) :
    StacksDraft.Perfect.IsPerfect
      (derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F)) := by
  obtain ⟨I, hI, hIlin, U, hU, hUaff, haff⟩ :=
    FinitePresentationGlobalSectionsModel.exists_finiteAffineCover_of_quasiCompact f
  have hbc := isIso_derivedGlobalSectionsBaseChangeMap φ hsq F U hU hUaff haff hflat
  obtain ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ := hF
  have := hLE
  have := hGE
  have hflatP : ∀ n : ℤ, Module.Flat A (P.X n) := fun n =>
    have := hproj n
    Module.Flat.of_projective
  refine ⟨((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P, a, b, inferInstance, inferInstance, fun i => ?_, fun i => ?_,
    ⟨(asIso (derivedGlobalSectionsBaseChangeMap φ hsq F U hU hUaff haff)).symm ≪≫
      (StacksDraft.PseudoCoherence.extendScalarsDerived φ).mapIso e ≪≫
      StacksDraft.PseudoCoherence.extendScalarsDerivedIsoOfFlat φ P b⟩⟩
  · let := φ.toAlgebra
    have := hfin i
    show Module.Finite A' (TensorProduct A A' (P.X i))
    infer_instance
  · let := φ.toAlgebra
    have := hproj i
    show Module.Projective A' (TensorProduct A A' (P.X i))
    infer_instance

/-- `RΓ` depends only on the isomorphism class of the module. -/
def derivedGlobalSectionsOverBaseMapIso {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) {F G : X.Modules} (e : F ≅ G) :
    derivedGlobalSectionsOverBase f F ≅ derivedGlobalSectionsOverBase f G :=
  (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory.mapIso
    (DerivedCategory.Plus.ι.mapIso
      ((derivedGlobalSectionsFunctor X.ringCatSheaf ⊤).mapIso e))

/-! ### Descent of a proper scheme with a flat module to a stage of a limit -/

section Descent

attribute [local instance] IsCofiltered.isConnected

/-- Flatness over the base is preserved by base change, in the `Scheme.Modules.pullback`
spelling. -/
theorem isFlatOver_schemePullback_of_isPullback {X S S' X' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} (h : IsPullback g' f' f g) (F : X.Modules)
    [F.IsQuasicoherent] (hF : IsFlatOver f.toLRSHom.toShHom F) :
    IsFlatOver f'.toLRSHom.toShHom ((Scheme.Modules.pullback g').obj F) :=
  (isFlatOver_iff_of_iso f' ((Stacks.ProjectiveBundleQuotients.pullbackIso g').app F)).2
    (@modulePullback_isFlatOver X S S' X' f g g' f' h F ‹F.IsQuasicoherent› hF)

/-- A base change of a proper morphism of finite presentation is proper of finite presentation. -/
private theorem isProper_and_finitePresentation_of_isPullback {P Q S T : Scheme.{u}}
    {fst : P ⟶ Q} {snd : P ⟶ S} {f : Q ⟶ T} {g : S ⟶ T} (h : IsPullback fst snd f g)
    [IsProper f] (hf : FinitePresentation f) : IsProper snd ∧ FinitePresentation snd :=
  ⟨MorphismProperty.of_isPullback (P := @IsProper) h inferInstance,
    ⟨MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h hf.1,
      MorphismProperty.of_isPullback (P := @QuasiCompact) h hf.2.1,
      MorphismProperty.of_isPullback (P := @QuasiSeparated) h hf.2.2⟩⟩

variable {I : Type u} [Category.{u} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
  (c : Cone D)

/-- A proper morphism of finite presentation to the limit of a cofiltered system of qcqs schemes
with affine transition morphisms is the base change of a proper morphism of finite presentation
at some stage. -/
theorem exists_isPullback_stage_of_isProper (hc : IsLimit c) {X : Scheme.{u}} (f : X ⟶ c.pt)
    [IsProper f] (hf : FinitePresentation f) :
    ∃ (j : I) (Z : Scheme.{u}) (q : Z ⟶ D.obj j) (g₀ : X ⟶ Z),
      IsProper q ∧ FinitePresentation q ∧ IsPullback f g₀ (c.π.app j) q := by
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  obtain ⟨j, Z, hZfp, hZp, ⟨e⟩⟩ :=
    exists_isProper_finitePresentation_overPullbackObj_of_isLimit D c hc (Over.mk f) hf
  have he : e.hom.left ≫ pullback.snd Z.hom (c.π.app j) = f := by
    simpa using Over.w e.hom
  refine ⟨j, Z.left, Z.hom, e.hom.left ≫ pullback.fst Z.hom (c.π.app j), hZp, hZfp,
    (IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso e) rfl he).flip⟩
  show (e.hom.left ≫ pullback.fst Z.hom (c.π.app j)) ≫ Z.hom = f ≫ c.π.app j
  rw [Category.assoc, pullback.condition, ← Category.assoc, he]

/-- A proper morphism of finite presentation to the limit of a cofiltered system of qcqs schemes
with affine transition morphisms, together with a module of finite presentation, is the base
change of such data at some stage. -/
theorem exists_isPullback_finitePresentation_model_of_isProper (hc : IsLimit c)
    {X : Scheme.{u}} (f : X ⟶ c.pt) [IsProper f] (hf : FinitePresentation f) (G : X.Modules)
    [G.IsFinitePresentation] :
    ∃ (k : I) (Y : Scheme.{u}) (hk : Y ⟶ D.obj k) (π : X ⟶ Y) (Gₖ : Y.Modules),
      IsProper hk ∧ FinitePresentation hk ∧ IsPullback π f hk (c.π.app k) ∧
        Gₖ.IsFinitePresentation ∧ Nonempty (G ≅ (Scheme.Modules.pullback π).obj Gₖ) := by
  obtain ⟨j, Z, q, g₀, hqp, hqfp, hsq₀⟩ := exists_isPullback_stage_of_isProper D c hc f hf
  have hpb : ∀ k : Over j, IsPullback (pullback.snd (D.map k.hom) q)
      (pullback.fst (D.map k.hom) q) q (D.map k.hom) := fun k =>
    (IsPullback.of_hasPullback (D.map k.hom) q).flip
  let E : Over j ⥤ Scheme.{u} := Over.post (X := j) D ⋙ Over.pullback q ⋙ Over.forget Z
  have hEmap : ∀ {k k' : Over j} (a : k' ⟶ k),
      IsPullback (pullback.fst (D.map k'.hom) q) (E.map a) (D.map a.left)
        (pullback.fst (D.map k.hom) q) := fun a =>
    overPullback_map_isPullback q ((Over.post D).map a)
  have : ∀ {k k' : Over j} (a : k' ⟶ k), IsAffineHom (E.map a) := fun a =>
    MorphismProperty.of_isPullback (P := @IsAffineHom) (hEmap a) inferInstance
  have : ∀ k : Over j, CompactSpace (E.obj k) := fun k => by
    have h : QuasiCompact (pullback.fst (D.map k.hom) q) :=
      (isProper_and_finitePresentation_of_isPullback (hpb k) hqfp).2.2.1
    exact @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.fst (D.map k.hom) q) h
      inferInstance
  have : ∀ k : Over j, QuasiSeparatedSpace (E.obj k) := fun k => by
    have h : QuasiSeparated (pullback.fst (D.map k.hom) q) :=
      (isProper_and_finitePresentation_of_isPullback (hpb k) hqfp).2.2.2
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst (D.map k.hom) q)
      inferInstance h
  let cE₀ : Cone E := (Over.forget Z).mapCone ((Over.pullback q).mapCone (c.overPost j))
  let hcE₀ : IsLimit cE₀ :=
    isLimitOfPreserves (Over.forget Z) (isLimitOfPreserves (Over.pullback q) (hc.overPost j))
  let isoX : X ≅ pullback (c.π.app j) q := hsq₀.isoPullback
  let cE : Cone E := cE₀.extend (isoX.hom : X ⟶ cE₀.pt)
  let hcE : IsLimit cE :=
    hcE₀.ofIsoLimit (Cone.ext isoX.symm (fun k => (Iso.inv_hom_id_assoc isoX _).symm))
  obtain ⟨k, Gₖ, hGₖ, ⟨eG⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
      E cE hcE G
  let hk : E.obj k ⟶ D.obj k.left := pullback.fst (D.map k.hom) q
  let π₀ : pullback (c.π.app j) q ⟶ E.obj k := cE₀.π.app k
  have hpbk := hpb k
  have hP : IsPullback (pullback.fst (c.π.app j) q) π₀ (c.π.app k.left) hk :=
    overPullback_map_isPullback q ((c.overPost j).π.app k)
  have hπ : cE.π.app k = isoX.hom ≫ π₀ := rfl
  have hw : cE.π.app k ≫ hk = f ≫ c.π.app k.left := by
    rw [hπ, Category.assoc, ← hP.w, ← Category.assoc, hsq₀.isoPullback_hom_fst]
  have hP₁ : IsPullback (cE.π.app k) f hk (c.π.app k.left) := by
    refine IsPullback.of_iso_pullback ⟨hw⟩ (isoX ≪≫ hP.flip.isoPullback) ?_ ?_
    · rw [Iso.trans_hom, Category.assoc, hP.flip.isoPullback_hom_fst, hπ]
    · rw [Iso.trans_hom, Category.assoc, hP.flip.isoPullback_hom_snd]
      exact hsq₀.isoPullback_hom_fst
  obtain ⟨hkp, hkfp⟩ := isProper_and_finitePresentation_of_isPullback hpbk hqfp
  exact ⟨k.left, E.obj k, hk, cE.π.app k, Gₖ, hkp, hkfp, hP₁, hGₖ, ⟨eG⟩⟩

/-- Flatness over the limit of a module pulled back from a proper morphism of finite presentation
at a stage holds after base change to some later stage. -/
theorem exists_isFlatOver_stage_of_isPullback (hc : IsLimit c) {i : I} {X Y : Scheme.{u}}
    (hk : Y ⟶ D.obj i) (hkfp : FinitePresentation hk) {f : X ⟶ c.pt} {π : X ⟶ Y}
    (hP₁ : IsPullback π f hk (c.π.app i)) (G : X.Modules) [G.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom G) (Gₖ : Y.Modules) [Gₖ.IsFinitePresentation]
    (eG : G ≅ (Scheme.Modules.pullback π).obj Gₖ) :
    ∃ (k' : I) (e' : k' ⟶ i), IsFlatOver (pullback.snd hk (D.map e')).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst hk (D.map e'))).obj Gₖ) := by
  let X₀ : Over (D.obj i) := Over.mk hk
  let Y₀ : Over (D.obj i) := Over.mk (𝟙 _)
  let fX : X₀ ⟶ Y₀ := Over.homMk hk
  have hY₀ : FinitePresentation Y₀.hom :=
    show FinitePresentation (𝟙 (D.obj i)) from ⟨inferInstance, inferInstance, inferInstance⟩
  have : Gₖ.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation Gₖ
  let τ : X ≅ pullback hk (c.π.app i) := hP₁.isoPullback
  let s₁ : pullback (𝟙 (D.obj i)) (c.π.app i) ⟶ c.pt := pullback.snd (𝟙 _) (c.π.app i)
  have hm : ∀ {T : Scheme.{u}} (t : T ⟶ D.obj i),
      ((Over.pullback t).map fX).left ≫ pullback.snd (𝟙 (D.obj i)) t = pullback.snd hk t :=
    fun t => by simpa [fX, X₀, Y₀, Over.pullback_map_left] using pullback.lift_snd _ _ _
  have hsq₁ : IsPullback τ.inv ((Over.pullback (c.π.app i)).map fX).left f s₁ :=
    IsPullback.of_horiz_isIso ⟨by rw [hm]; simp [τ]⟩
  have : G.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation G
  have hfl₁ := isFlatOver_schemePullback_of_isPullback hsq₁ G hflat
  let eM : (Scheme.Modules.pullback τ.inv).obj G ≅
      (modulePullback (pullback.fst X₀.hom (c.π.app i)).toLRSHom.toShHom).obj Gₖ :=
    (Scheme.Modules.pullback τ.inv).mapIso eG ≪≫
      (Scheme.Modules.pullbackComp τ.inv π).app Gₖ ≪≫
      (Scheme.Modules.pullbackCongr (by simp [τ, X₀])).app Gₖ ≪≫
      (Stacks.ProjectiveBundleQuotients.pullbackIso _).app Gₖ
  obtain ⟨k', e', hfl'⟩ := @eventually_isFlatOver_modulePullback _ _ _ _ D c hc _ _ _ i X₀ Y₀
    hkfp hY₀ fX Gₖ ‹_› ‹_› ((isFlatOver_iff_of_iso _ eM).1 hfl₁)
  refine ⟨k', e', ?_⟩
  have : ((Scheme.Modules.pullback (pullback.fst hk (D.map e'))).obj Gₖ).IsQuasicoherent :=
    isQuasicoherent_of_isFinitePresentation _
  rw [← hm (D.map e')]
  exact (isFlatOver_comp_iff_of_etale _ _ _).2 <|
    (isFlatOver_iff_of_iso _ ((Stacks.ProjectiveBundleQuotients.pullbackIso _).app Gₖ)).2 hfl'

/-- **A proper scheme of finite presentation over the limit of a cofiltered system, with a module
of finite presentation flat over the limit, is the base change of one over a stage.** Let `D` be
a cofiltered system of quasi-compact quasi-separated schemes with affine transition morphisms and
limit `c.pt`, let `f : X ⟶ c.pt` be proper and of finite presentation, and let `G` be an
`𝒪_X`-module of finite presentation flat over `c.pt`. Then there are a stage `k`, a proper
morphism of finite presentation `fₖ : Xₖ ⟶ D k`, a cartesian square exhibiting `f` as the base
change of `fₖ` along `c.pt ⟶ D k`, and an `𝒪_{Xₖ}`-module `Gₖ` of finite presentation, flat over
`D k`, whose pullback to `X` is `G`.

This is the descent the source performs at the start of the proof of
[Stacks, Tag 0A1H]: the scheme by [Stacks, Tag 01ZM] and [Stacks, Tag 081F], the module by
[Stacks, Tag 01ZR], and its flatness by [Stacks, Tag 05LY]. -/
@[ega "IV 8.1.1" "partial"]
theorem exists_isPullback_model_of_isProper (hc : IsLimit c) {X : Scheme.{u}} (f : X ⟶ c.pt)
    [IsProper f] (hf : FinitePresentation f) (G : X.Modules) [G.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom G) :
    ∃ (k : I) (Xₖ : Scheme.{u}) (fₖ : Xₖ ⟶ D.obj k) (g : X ⟶ Xₖ) (Gₖ : Xₖ.Modules),
      IsProper fₖ ∧ FinitePresentation fₖ ∧ IsPullback g f fₖ (c.π.app k) ∧
        Gₖ.IsFinitePresentation ∧ IsFlatOver fₖ.toLRSHom.toShHom Gₖ ∧
          Nonempty (G ≅ (Scheme.Modules.pullback g).obj Gₖ) := by
  obtain ⟨i, Y, hk, π, Gₖ, hkp, hkfp, hP₁, hGₖ, ⟨eG⟩⟩ :=
    exists_isPullback_finitePresentation_model_of_isProper D c hc f hf G
  obtain ⟨k', e', hfl⟩ := exists_isFlatOver_stage_of_isPullback D c hc hk hkfp hP₁ G hflat Gₖ eG
  let a := D.map e'
  let pk : pullback hk a ⟶ Y := pullback.fst hk a
  let fk : pullback hk a ⟶ D.obj k' := pullback.snd hk a
  have hwg : π ≫ hk = (f ≫ c.π.app k') ≫ a := by
    rw [hP₁.w, Category.assoc, c.w e']
  let g : X ⟶ pullback hk a := pullback.lift π (f ≫ c.π.app k') hwg
  have hgpk : g ≫ pk = π := pullback.lift_fst _ _ _
  have hgfk : g ≫ fk = f ≫ c.π.app k' := pullback.lift_snd _ _ _
  have hpb : IsPullback pk fk hk a := IsPullback.of_hasPullback hk a
  obtain ⟨hfkp, hfkfp⟩ := isProper_and_finitePresentation_of_isPullback hpb hkfp
  refine ⟨k', pullback hk a, fk, g, (Scheme.Modules.pullback pk).obj Gₖ, hfkp, hfkfp,
    ?_, inferInstance, hfl, ⟨eG ≪≫ (Scheme.Modules.pullbackCongr hgpk.symm).app Gₖ ≪≫
      ((Scheme.Modules.pullbackComp g pk).app Gₖ).symm⟩⟩
  refine IsPullback.of_right ?_ hgfk hpb
  rw [hgpk, c.w e']
  exact hP₁

/-- **`RΓ(X, G)` is perfect for a proper morphism of finite presentation to an affine scheme and a
module of finite presentation flat over the base.** Let `R` be a ring, let `f : X ⟶ Spec R` be
proper and of finite presentation, and let `G` be an `𝒪_X`-module of finite presentation, flat
over `R`. Then `RΓ(X, G)` is a perfect object of `D(R)`.

This is the perfection half of [Stacks, Tag 0B91] (2) over an affine base, which is the case of
[Stacks, Tag 0A1H] with `E = 𝒪_X`. The proof is the source's: write `R` as the filtered colimit
of its finitely generated subrings, descend `X`, `G` and the flatness of `G` to one of them
(`exists_isPullback_model_of_isProper`), apply the Noetherian case [Stacks, Tag 07VK] (1) there,
and come back by the base-change isomorphism of [Stacks, Tag 07VK] (2). -/
theorem isPerfect_derivedGlobalSectionsOverBase_of_isProper {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f]
    (G : X.Modules) [G.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom G) :
    StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase f G) := by
  let D := specAdjoinFinsetDiagram R
  let c := specAdjoinFinsetCone R
  have : ∀ i, CompactSpace (D.obj i) := fun i => inferInstance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => inferInstance
  let f' : X ⟶ c.pt := f
  have : IsProper f' := ‹IsProper f›
  have : LocallyOfFinitePresentation f' := ‹LocallyOfFinitePresentation f›
  obtain ⟨k, Xk, fk, g, Gk, hp, hfp, hsq, hGk, hflk, ⟨eG⟩⟩ :=
    exists_isPullback_model_of_isProper D c (isLimit_specAdjoinFinsetCone R) f'
      ⟨inferInstance, inferInstance, inferInstance⟩ G hflat
  let A := Algebra.adjoin ℤ ((k.unop : Finset R) : Set R)
  have : IsNoetherianRing A := isNoetherianRing_adjoinFinset_int R k.unop
  let φ : A →+* R := A.val.toRingHom
  let fk' : Xk ⟶ Spec (.of A) := fk
  have : IsProper fk' := hp
  have : LocallyOfFiniteType fk' := inferInstance
  have : IsLocallyNoetherian Xk := LocallyOfFiniteType.isLocallyNoetherian fk'
  have := hGk
  have : Gk.IsCoherent :=
    (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isFinitePresentation Gk).2 hGk
  have : Gk.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation Gk
  have hsq' : IsPullback g f fk' (Spec.map (CommRingCat.ofHom φ)) := hsq
  obtain ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ := isPerfect_of_isPullback φ hsq' Gk hflk
    (isPerfect_derivedGlobalSections fk' Gk hflk)
  exact ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨derivedGlobalSectionsOverBaseMapIso f eG ≪≫ e⟩⟩

/-- **A finite projective chain model of the Čech complex, over an arbitrary affine base.** For
`f : X ⟶ Spec R` proper and of finite presentation, `G` of finite presentation and flat over `R`,
and a finite affine open cover `U` of `X` with affine finite intersections, there is a bounded
complex `M` of finite projective `R`-modules with a quasi-isomorphism of complexes `M ⟶ K` to the
`R`-linear alternating Čech complex `K` of `U`. This is
`exists_finiteProjectiveModel_quasiIso` with the Noetherian hypothesis removed, the perfection
input being `isPerfect_derivedGlobalSectionsOverBase_of_isProper`. -/
theorem exists_finiteProjectiveModel_quasiIso_of_finitePresentation {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f]
    {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (G : X.Modules)
    [G.IsFinitePresentation] [Finite I] [LinearOrder I]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (hflat : IsFlatOver f.toLRSHom.toShHom G) :
    ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite R (M.X i)) ∧ (∀ i : ℤ, Module.Projective R (M.X i)) ∧
        ∃ u : M ⟶ baseAlternatingCechComplex f U hU G, QuasiIso u := by
  have : G.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation G
  obtain ⟨M, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ :=
    isPerfect_derivedGlobalSectionsOverBase_of_isProper f G hflat
  refine ⟨M, a, b, hGE, hLE, hfin, hproj, ?_⟩
  have hprojX : ∀ n : ℤ, CategoryTheory.Projective (M.X n) := fun n =>
    have := hproj n
    inferInstance
  have hKP : M.IsKProjective := CochainComplex.isKProjective_of_projective M b
  obtain ⟨u, hu⟩ := StacksDraft.PseudoCoherence.exists_chainMap_of_isKProjective M
    (baseAlternatingCechComplex f U hU G)
    (e.inv ≫ (alternatingCechIsoDerivedGlobalSectionsOverBase f U hU G haff).inv)
  refine ⟨u, (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 ?_⟩
  rw [hu]
  infer_instance

open CochainComplex.DerivedExtensionScalars in
/-- **Derived base change of `RΓ`, read through the total derived extension of scalars.** For
`f` proper and of finite presentation, `F` of finite presentation and flat over `A`, and a
cartesian square along `Spec A' ⟶ Spec A`, the total derived extension of scalars of
`RΓ(X, F)` is `RΓ(X', g^*F)`. The two derived extensions of scalars of the library agree on the
finite projective model of `RΓ(X, F)`, where both are termwise, and the second one is the
base-change isomorphism of [Stacks, Tag 07VK] (2). -/
theorem nonempty_totalDerived_derivedGlobalSectionsOverBase_iso
    {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} [IsProper f] [LocallyOfFinitePresentation f]
    {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) (F : X.Modules)
    [F.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    Nonempty ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
        (derivedGlobalSectionsOverBase f F) ≅
      derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F)) := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation F
  obtain ⟨I, hI, hIlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  obtain ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ :=
    isPerfect_derivedGlobalSectionsOverBase_of_isProper f F hflat
  have := hLE
  have hprojX : ∀ n : ℤ, CategoryTheory.Projective (P.X n) := fun n =>
    have := hproj n
    inferInstance
  have hflatP : ∀ n : ℤ, Module.Flat A (P.X n) := fun n =>
    have := hproj n
    Module.Flat.of_projective
  let D := totalDerivedExtensionScalars.{u, u, u} φ
  have hiso : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P b
  have hbc := isIso_derivedGlobalSectionsBaseChangeMap φ hsq F U hU hUaff haff hflat
  exact ⟨D.functor.mapIso e ≪≫ asIso (D.comparison.app P) ≪≫
    (StacksDraft.PseudoCoherence.extendScalarsDerivedIsoOfFlat φ P b).symm ≪≫
    (StacksDraft.PseudoCoherence.extendScalarsDerived φ).mapIso e.symm ≪≫
    asIso (derivedGlobalSectionsBaseChangeMap φ hsq F U hU hUaff haff)⟩

end Descent

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
