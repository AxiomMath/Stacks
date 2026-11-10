module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.RestrictionSupport
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.PerfectAnnihilator
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PseudoCoherentPushforwardLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.StructureSheafPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisted inverse image of a proper morphism commutes with restriction to opens

Let `Y` be a Noetherian scheme, `f : X ⟶ Y` a proper morphism and `V ⊆ Y` an open with inverse
image `U`. [Stacks, Tag 0A9P] (2) says that the canonical map `(j')^* ∘ a ⟶ a' ∘ j^*` of
[Stacks, Tag 0A9L] is invertible on `D^+_QCoh(𝒪_Y)`, where `a`, `a'` are the right adjoints of
`Rf_*`, `R(f|_U)_*`. Part (1), for `f` flat and of finite presentation, is in
`Duality/TwistedInverseImage/ProperFlatRestriction.lean`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality

open OpenImmersion

/-- **Killing a morphism into `E` on a neighbourhood suffices.** Let `j : U ⟶ X` be a quasi-compact
open immersion into a quasi-compact quasi-separated scheme. If every morphism `g : c ⟶ E` out of a
compact object of `D_QCoh(𝒪_X)` is killed by some `φ : M ⟶ c` invertible on `U`, then `E|_U = 0`.
-/
theorem isZero_restrict_of_forall_exists_comp_eq_zero {X U : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (j : U ⟶ X) [IsOpenImmersion j] [AlgebraicGeometry.QuasiCompact j]
    (E : quasiCoherentDerivedCategory X)
    (h : ∀ c : quasiCoherentDerivedCategory X, IsCompactObject.{u} c → ∀ g : c ⟶ E,
      ∃ (M : quasiCoherentDerivedCategory X) (φ : M ⟶ c),
        IsIso ((restrictedDerivedRestrict j).map φ) ∧ φ ≫ g = 0) :
    IsZero ((restrictedDerivedRestrict j).obj E) := by
  refine SupportedGeneration.isZero_restrict_of_forall_isCompactObject j E fun c hc g => ?_
  obtain ⟨M, φ, hφ, hφg⟩ := h c hc g
  rw [← cancel_epi ((restrictedDerivedRestrict j).map φ), ← Functor.map_comp, hφg,
    Functor.map_zero, comp_zero]

/-- **A morphism into `a(Q)` killed through a natural comparison.** Let `G ⊣ a`, let
`π : Ψ ⟶ Φ ⋙ G` be a natural transformation invertible at `J`, let `u : J ⟶ I`, `θ : Φ I ⟶ M`
and `g : M ⟶ a(Q)`. If the transpose `t : G M ⟶ Q` of `g` is killed by
`Ψ J ⟶ Ψ I ⟶ G (Φ I) ⟶ G M`, then `g` is killed by `Φ J ⟶ Φ I ⟶ M`.

This is the formal half of the proof of [Stacks, Tag 0A9P]: with `Ψ = - ⊗ Rf_*M`,
`Φ = M ⊗ Lf^*(-)` and `π` the projection formula, it moves the vanishing provided on the base by
[Stacks, Tag 0A9C] up to the source. -/
theorem _root_.CategoryTheory.Adjunction.comp_eq_zero_of_natTrans {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] {G : D ⥤ C} {a : C ⥤ D} (adj : G ⊣ a)
    {Ψ : C ⥤ C} {Φ : C ⥤ D} (π : Ψ ⟶ Φ ⋙ G) {J I : C} [IsIso (π.app J)] (u : J ⟶ I) {M : D}
    (θ : Φ.obj I ⟶ M) {Q : C} (g : M ⟶ a.obj Q)
    (h : Ψ.map u ≫ π.app I ≫ G.map θ ≫ (adj.homEquiv _ _).symm g = 0) :
    (Φ.map u ≫ θ) ≫ g = 0 := by
  have := adj.isLeftAdjoint
  have h0 : (adj.homEquiv (Φ.obj J) Q).symm 0 = 0 := by
    simp [Adjunction.homEquiv_counit]
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, h0, ← cancel_epi (π.app J), comp_zero,
    Functor.map_comp, ← Category.assoc, ← Category.assoc, ← Functor.comp_map, ← π.naturality,
    Category.assoc, Category.assoc, h]

section Noetherian

/-- An open subscheme of a Noetherian scheme is Noetherian. -/
@[ega "I 6.1.4" "special case"]
theorem isNoetherian_of_isOpenImmersion {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j]
    [IsNoetherian Y] : IsNoetherian V :=
  have := isLocallyNoetherian_of_isOpenImmersion j
  have : TopologicalSpace.NoetherianSpace V := (TopologicalSpace.noetherianSpace_iff_of_homeomorph
    j.isOpenEmbedding.isEmbedding.toHomeomorph).2 inferInstance
  ⟨⟩

/-- A scheme proper over a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsNoetherian Y] :
    IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

end Noetherian

section PseudoCoherentPushforward

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [CompactSpace Y] [QuasiSeparatedSpace Y] [AlgebraicGeometry.QuasiCompact f]
  [QuasiSeparated f] [AlgebraicGeometry.QuasiCompact j]

/-- **A map out of a compact object into `a(Q)` is killed on a neighbourhood.** Let `f : X ⟶ Y` be
quasi-compact and quasi-separated over a quasi-compact quasi-separated `Y`, let `V ⊆ Y` be a
quasi-compact open with inverse image `U`, and let `Q ∈ D^+_QCoh(𝒪_Y)` vanish on `V`. If `c` is an
object of `D_QCoh(𝒪_X)` with `Rf_*c` pseudo-coherent, every `g : c ⟶ a(Q)` is killed by some
`φ : M ⟶ c` invertible on `U`. -/
theorem exists_comp_eq_zero_twistedInverseImage_of_isPseudoCoherent (sq : IsPullback j' f' f j)
    (Q : quasiCoherentDerivedCategory Y) (hQb : DerivedCategoryB.IsBoundedBelow Q.obj)
    (hQ : IsZero ((derivedRestrict j).obj Q.obj)) (c : quasiCoherentDerivedCategory X)
    (hc : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) ((derivedPushforward f).obj c.obj)) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    ∀ g : c ⟶ (twistedInverseImage f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj Q,
      ∃ (M : quasiCoherentDerivedCategory X) (φ : M ⟶ c),
        IsIso ((restrictedDerivedRestrict j').map φ) ∧ φ ≫ g = 0 := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  intro g
  let hpush := isQuasicoherent_homology_derivedPushforward_of_qcqs f
  let G := quasiCoherentDerivedPushforward f hpush
  let adj := twistedInverseImageAdjunction f hpush
  let ιX := ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf))
  let ιY := ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf))
  let P := G.obj c
  let Φ : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X :=
    ObjectProperty.lift _ (ιY ⋙ derivedPullback f ⋙ (derivedTensor X).obj c.obj)
      (fun J i => isQuasicoherent_homology_derivedTensor X c
        ⟨_, isQuasicoherent_homology_derivedPullback' f J⟩ i)
  let πa := (ProjectionFormulaLocallySmall.tensorSwapIso Y P.obj).inv ≫
    ProjectionFormulaLocallySmall.natTrans f c.obj
  let π : MonoidalCategory.tensorRight P ⟶ Φ ⋙ G :=
    { app := fun J => ObjectProperty.homMk (πa.app J.obj)
      naturality := fun J J' h => by
        ext
        exact πa.naturality (ιY.map h) }
  let θa : (Φ.obj (𝟙_ _)).obj ≅ c.obj :=
    ((derivedTensor X).obj c.obj).mapIso
        ((derivedPullback f).mapIso (eqToIso (congrArg ObjectProperty.FullSubcategory.obj
          (tensorUnit_quasiCoherentDerivedCategory Y))) ≪≫
          derivedPullbackStructureSheafIso f) ≪≫
      (ιX.mapIso ((quasiCoherentDerivedTensorRightUnitor X).app c))
  let θ : Φ.obj (𝟙_ _) ≅ c := ObjectProperty.isoMk _ θa
  obtain ⟨I, u, -, hu, hz⟩ := exists_isPerfect_whiskerRight_comp_eq_zero j
    ((λ_ P).inv ≫ π.app _ ≫ G.map θ.hom ≫ (adj.homEquiv _ _).symm g) hQ (Or.inr ⟨hc, hQb⟩)
  have : IsIso (π.app I) := by
    have : IsIso (πa.app I.obj) := by
      have := ProjectionFormulaLocallySmall.isIso_natTrans_app f c.obj I.obj c.2 I.2
      exact (inferInstance : IsIso
        ((ProjectionFormulaLocallySmall.tensorSwapIso Y P.obj).inv.app I.obj ≫
          (ProjectionFormulaLocallySmall.natTrans f c.obj).app I.obj))
    have : IsIso (ιY.map (π.app I)) := this
    exact isIso_of_reflects_iso _ ιY
  simp only [Iso.hom_inv_id_assoc] at hz
  refine ⟨Φ.obj I, Φ.map u ≫ θ.hom, ?_, adj.comp_eq_zero_of_natTrans π u θ.hom g hz⟩
  have h3 := ProjectionFormulaLocallySmall.isIso_derivedRestrict_tensor_pullback_map f sq c.obj
    (ιY.map u) hu
  have : IsIso ((derivedRestrict j').map (ιX.map (Φ.map u ≫ θ.hom))) := by
    rw [Functor.map_comp, Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h3 (Functor.map_isIso _ (ιX.map θ.hom))
  have : IsIso ((ObjectProperty.ι _).map
      ((restrictedDerivedRestrict j').map (Φ.map u ≫ θ.hom))) := this
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

/-- **The support half of [Stacks, Tag 0A9P], in the generality of its footnote.** Let `Y` be
quasi-compact and quasi-separated, `f : X ⟶ Y` quasi-compact and quasi-separated such that `Rf_*`
carries compact (that is, perfect) objects of `D_QCoh(𝒪_X)` to pseudo-coherent objects, and let
`V ⊆ Y` be a quasi-compact open with inverse image `U`. If `Q ∈ D^+_QCoh(𝒪_Y)` vanishes on `V`,
then `a(Q)` vanishes on `U`, where `a` is the right adjoint of `Rf_*`.

Following the source: a map `g : c ⟶ a(Q)` out of a compact `c` is adjoint to `Rf_*c ⟶ Q`; as
`Rf_*c` is pseudo-coherent, [Stacks, Tag 0A9C] gives a perfect `u : I ⟶ 𝒪_Y`, invertible on `V`,
killing `I ⊗ Rf_*c ⟶ Q`; the projection formula ([Stacks, Tag 08EU]) carries this to
`c ⊗ Lf^*I ⟶ c ⟶ a(Q)` being zero, and `c ⊗ Lf^*I ⟶ c` is invertible on `U`. -/
theorem isZero_restrict_twistedInverseImage_of_isPseudoCoherent (sq : IsPullback j' f' f j)
    (hpc : ∀ c : quasiCoherentDerivedCategory X, IsCompactObject.{u} c →
      RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) ((derivedPushforward f).obj c.obj))
    (Q : quasiCoherentDerivedCategory Y) (hQb : DerivedCategoryB.IsBoundedBelow Q.obj)
    (hQ : IsZero ((derivedRestrict j).obj Q.obj)) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    IsZero ((derivedRestrict j').obj ((twistedInverseImage f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj Q).obj) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : AlgebraicGeometry.QuasiCompact j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact (ObjectProperty.ι _).map_isZero (isZero_restrict_of_forall_exists_comp_eq_zero j' _
    fun c hc => exists_comp_eq_zero_twistedInverseImage_of_isPseudoCoherent j' f' f j sq Q hQb hQ c
      (hpc c hc))

/-- **The conclusion of [Stacks, Tag 0A9P], in the generality of its footnote.** Let `Y` be
quasi-compact and quasi-separated, `f : X ⟶ Y` quasi-compact and quasi-separated such that `Rf_*`
carries compact objects of `D_QCoh(𝒪_X)` to pseudo-coherent objects, and `j : V ⟶ Y` a
quasi-compact open immersion with base change `j' : U ⟶ X`. The map `(j')^* ∘ a ⟶ a' ∘ j^*` of
[Stacks, Tag 0A9L] is invertible on `D^+_QCoh(𝒪_Y)`. -/
theorem isIso_twistedInverseImageRestrictionMap_app_of_isPseudoCoherent
    (sq : IsPullback j' f' f j)
    (hpc : ∀ c : quasiCoherentDerivedCategory X, IsCompactObject.{u} c →
      RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) ((derivedPushforward f).obj c.obj))
    (K : quasiCoherentDerivedCategory Y) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace j
    haveI : CompactSpace U := compactSpace_of_isPullback sq
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
    haveI : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
    IsIso ((twistedInverseImageRestrictionMap j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
      (isQuasicoherent_homology_derivedRestrict j) (isQuasicoherent_homology_derivedRestrict j')
      sq).app K) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace j
  have : CompactSpace U := compactSpace_of_isPullback sq
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
  have : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
  exact (isZero_restrict_twistedInverseImage_iff_isIso_restrictionMap_of_isBoundedBelow j' f' f j
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j) sq).1
    (isZero_restrict_twistedInverseImage_of_isPseudoCoherent j' f' f j sq hpc) K hK

end PseudoCoherentPushforward

section Proper

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [IsNoetherian Y] [IsProper f]

/-- For `f` proper over a Noetherian scheme, `Rf_*` carries compact objects to pseudo-coherent
objects. -/
private theorem isPseudoCoherent_derivedPushforward_of_isCompactObject {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsNoetherian Y] [IsProper f] (c : quasiCoherentDerivedCategory X)
    (hc : IsCompactObject.{u} c) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) ((derivedPushforward f).obj c.obj) :=
  have := isNoetherian_of_isProper f
  Stacks.AlgebraicGeometry.ProperSupportCoherent.isPseudoCoherent_derivedPushforward_of_isProper
    f c.obj (isPseudoCoherent_of_isCompactObject c hc)

/-- **The support half of [Stacks, Tag 0A9P] (2).** Let `Y` be Noetherian, `f : X ⟶ Y` proper and
`V ⊆ Y` open with inverse image `U`. If `Q ∈ D^+_QCoh(𝒪_Y)` vanishes on `V`, then `a(Q)` vanishes
on `U`, where `a` is the right adjoint of `Rf_*`.

Following the source: a map `g : c ⟶ a(Q)` out of a compact `c` is adjoint to `Rf_*c ⟶ Q`; as
`Rf_*c` is pseudo-coherent, [Stacks, Tag 0A9C] gives a perfect `u : I ⟶ 𝒪_Y`, invertible on `V`,
killing `I ⊗ Rf_*c ⟶ Q`; the projection formula ([Stacks, Tag 08EU]) carries this to
`c ⊗ Lf^*I ⟶ c ⟶ a(Q)` being zero, and `c ⊗ Lf^*I ⟶ c` is invertible on `U`. -/
theorem isZero_restrict_twistedInverseImage_of_isProper (sq : IsPullback j' f' f j)
    (Q : quasiCoherentDerivedCategory Y) (hQb : DerivedCategoryB.IsBoundedBelow Q.obj)
    (hQ : IsZero ((derivedRestrict j).obj Q.obj)) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI := isNoetherian_of_isProper f
    IsZero ((derivedRestrict j').obj ((twistedInverseImage f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj Q).obj) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := isNoetherian_of_isProper f
  exact isZero_restrict_twistedInverseImage_of_isPseudoCoherent j' f' f j sq
    (isPseudoCoherent_derivedPushforward_of_isCompactObject f) Q hQb hQ

/-- **[Stacks, Tag 0A9P] (2).** Let `Y` be Noetherian, `f : X ⟶ Y` proper and `j : V ⟶ Y` an open
immersion with base change `j' : U ⟶ X`. The map `(j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0A9L]
is invertible on `D^+_QCoh(𝒪_Y)`. Part (1) is
`Stacks.Duality.isIso_twistedInverseImageRestrictionMap_app_of_flat`. -/
@[stacks 0A9P "(2): Y Noetherian"]
theorem isIso_twistedInverseImageRestrictionMap_app_of_isProper (sq : IsPullback j' f' f j)
    (K : quasiCoherentDerivedCategory Y) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI := isNoetherian_of_isProper f
    haveI : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
    haveI := isNoetherian_of_isOpenImmersion j
    haveI := isNoetherian_of_isProper f'
    IsIso ((twistedInverseImageRestrictionMap j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
      (isQuasicoherent_homology_derivedRestrict j) (isQuasicoherent_homology_derivedRestrict j')
      sq).app K) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := isNoetherian_of_isProper f
  have := isNoetherian_of_isOpenImmersion j
  exact isIso_twistedInverseImageRestrictionMap_app_of_isPseudoCoherent j' f' f j sq
    (isPseudoCoherent_derivedPushforward_of_isCompactObject f) K hK

end Proper

end Stacks.Duality

end
