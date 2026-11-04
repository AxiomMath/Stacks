module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicate
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportModelComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicateSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedAtModel
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherentAnyModel

/-!
# Further results on `ClosedImmersionRightAdjointSheafHom`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHom` that need imports
beyond those of that module.
-/

@[expose] public noncomputable section

open StacksDraft.DerivedModel (modelEquiv)
universe w z u

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
  [instZ : HasDerivedCategory.{w} Z.Modules] [instW : HasDerivedCategory.{w} W.Modules]

/-! ### Three handles on the data of [Stacks, Tag 0A76] at the model of this section

The category of `𝒪_Z`-modules has three spellings — `AlgebraicGeometry.Scheme.Modules Z`,
`SheafOfModules Z.ringCatSheaf` and
`SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)` — which are one type but are *not*
interchanged by typeclass synthesis, the discrimination keys differing. The derived-category
model of this section is a binder over the first spelling, while derived sheaf Hom with exact
support and the adjunction of [Stacks, Tag 0A76] are stated at the third. The two meet by
*unification* in an `@`-application, so each of the three functors below names the model
positionally once, and the rest of the file is written in terms of them. -/

/-- The exact-functor model of `Ri_*` along the closed immersion `i`, at the derived-category
model of this section: the functor `D(𝒪_Z) ⥤ D(𝒪_W)` induced by the exact functor `i_*`. This is
the left adjoint of [Stacks, Tag 0A76]. -/
abbrev closedImmersionPushforward : DerivedCategory Z.Modules ⥤ DerivedCategory W.Modules :=
  @Functor.mapDerivedCategory _ _ _ instZ _ _ _ instW
    (modulePushforward (closedQuotient i).i) (modulePushforward_additive _)
    (Stacks.ClosedImmersion.preservesFiniteLimits_modulePushforward _)
    (closedQuotient i).preservesFiniteColimits_modulePushforward

/-- `R𝓗om_{𝒪_W}(𝒪_Z, -) : D(𝒪_W) ⥤ D(𝒪_Z)`, the right derived functor of sheaf Hom with exact
support along `i`, at the derived-category model of this section. This is the right adjoint of
[Stacks, Tag 0A76] and the functor [Stacks, Tag 0A9X] identifies a right adjoint of `Ri_*`
with. -/
abbrev closedImmersionDerivedSheafHom :
    DerivedCategory W.Modules ⥤ DerivedCategory Z.Modules :=
  @Stacks.Duality.AnyModel.derivedSheafHomExactSupport
    (closedQuotient i) instW instZ

open RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces in
/-- **[Stacks, Tag 0A76] at the derived-category model of this section:** derived pushforward
along a closed immersion is left adjoint to the right derived functor of sheaf Hom with exact
support. -/
abbrev closedImmersionSheafHomAdjunction :
    closedImmersionPushforward i ⊣ closedImmersionDerivedSheafHom i :=
  @derivedModulePushforwardSheafHomExactSupportAdjunctionAtModel
    (closedQuotient i) instW instZ

/-- **`R𝓗om_{𝒪_W}(𝒪_Z, -)` read at two models of the derived category**, in the spelling
`AlgebraicGeometry.Scheme.Modules` that the statements about a scheme use. This is
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`
`.derivedSheafHomExactSupportModelIso` with its four models named positionally. -/
def closedImmersionDerivedSheafHomModelIso {Z W : Scheme.{u}} (j : Z ⟶ W) [IsClosedImmersion j]
    (hZ₁ : HasDerivedCategory.{w} Z.Modules) (hW₁ : HasDerivedCategory.{w} W.Modules)
    (hZ₂ : HasDerivedCategory.{z} Z.Modules) (hW₂ : HasDerivedCategory.{z} W.Modules) :
    @closedImmersionDerivedSheafHom Z W j ‹_› hZ₁ hW₁ ⋙ (modelEquiv hZ₁ hZ₂).functor ≅
      (modelEquiv hW₁ hW₂).functor ⋙ @closedImmersionDerivedSheafHom Z W j ‹_› hZ₂ hW₂ :=
  @ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportModelIso
    (closedQuotient j) hW₁ hZ₁ hW₂ hZ₂

/-- **[Stacks, Tag 0E2K] for a closed immersion of schemes.** The comparison isomorphism
between the two models of `Ri_*` on unbounded derived categories of module sheaves: the functor
induced by the exact functor `i_*`, which is what the adjunction of [Stacks, Tag 0A76] uses, and
the total right derived functor, out of which `D_QCoh` is cut. -/
abbrev closedImmersionPushforwardIsoDerivedPushforward :
    closedImmersionPushforward i ≅ derivedPushforward i :=
  @Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived _ _ _ instZ _ _ _ instW
    (modulePushforward (closedQuotient i).i) (modulePushforward_additive _)
    (Stacks.ClosedImmersion.preservesFiniteLimits_modulePushforward _)
    (closedQuotient i).preservesFiniteColimits_modulePushforward

section

variable
    (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
      ((DerivedCategory.homologyFunctor W.Modules n).obj
        ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : quasiCoherentDerivedPushforward i hpush ⊣ a)

/-- The canonical comparison `a(K) ⟶ R𝓗om_{𝒪_W}(𝒪_Z, K)` in `D(𝒪_Z)`, natural in `K` in
`D_QCoh(𝒪_W)`: the mate, under the adjunction of [Stacks, Tag 0A76], of the counit of `a` read
through the comparison of the two models of `Ri_*`.

[Stacks, Tag 0A9X] says that this map is invertible on bounded-below complexes. -/
def closedImmersionRightAdjointToDerivedSheafHom :
    a ⋙ (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
          (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι ⟶
      (DerivedCategoryB.derivedCategoryB (A := W.Modules)
          (SheafOfModules.isQuasicoherent W.ringCatSheaf)).ι ⋙
        (closedImmersionDerivedSheafHom i) :=
  Functor.whiskerLeft
      (a ⋙ (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
        (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι)
      (closedImmersionSheafHomAdjunction i).unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft a
          (Functor.whiskerLeft (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
              (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι
            (closedImmersionPushforwardIsoDerivedPushforward i).hom) ≫
        Functor.whiskerRight adj.counit (DerivedCategoryB.derivedCategoryB (A := W.Modules)
          (SheafOfModules.isQuasicoherent W.ringCatSheaf)).ι)
      (closedImmersionDerivedSheafHom i)

/-- The comparison map of `closedImmersionRightAdjointToDerivedSheafHom` is the mate of the
counit of `a`: it is the image of `Ri_*(a K) ⟶ K` under the adjunction bijection of
[Stacks, Tag 0A76]. -/
theorem closedImmersionRightAdjointToDerivedSheafHom_app (K : quasiCoherentDerivedCategory W) :
    (closedImmersionRightAdjointToDerivedSheafHom i hpush a adj).app K =
      (closedImmersionSheafHomAdjunction i).homEquiv
        ((a.obj K).obj) K.obj
        ((closedImmersionPushforwardIsoDerivedPushforward i).hom.app ((a.obj K).obj) ≫
          (adj.counit.app K).hom) :=
  rfl

/-- Precomposing the comparison map of `closedImmersionRightAdjointToDerivedSheafHom` with a
morphism out of an object of `D_QCoh(𝒪_Z)` gives the adjunction bijection of [Stacks, Tag 0A76]
applied to the corresponding morphism `Ri_* M ⟶ K`. -/
theorem hom_comp_closedImmersionRightAdjointToDerivedSheafHom_app
    (K : quasiCoherentDerivedCategory W) (M : quasiCoherentDerivedCategory Z) (g : M ⟶ a.obj K) :
    g.hom ≫ (closedImmersionRightAdjointToDerivedSheafHom i hpush a adj).app K =
      (closedImmersionSheafHomAdjunction i).homEquiv
        M.obj K.obj
        ((closedImmersionPushforwardIsoDerivedPushforward i).hom.app M.obj ≫
          ((adj.homEquiv M K).symm g).hom) := by
  have hu : (closedImmersionPushforward i).map g.hom ≫
        ((closedImmersionPushforwardIsoDerivedPushforward i).hom.app ((a.obj K).obj) ≫
          (adj.counit.app K).hom) =
      (closedImmersionPushforwardIsoDerivedPushforward i).hom.app M.obj ≫
        ((adj.homEquiv M K).symm g).hom :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ (adj.counit.app K).hom)
        ((closedImmersionPushforwardIsoDerivedPushforward i).hom.naturality g.hom))).trans
      (Category.assoc _ _ _)
  rw [closedImmersionRightAdjointToDerivedSheafHom_app, ← hu]
  exact (Adjunction.homEquiv_naturality_left _ g.hom _).symm

/-- Composition with the comparison map of `closedImmersionRightAdjointToDerivedSheafHom` is a
bijection on morphisms out of any object of `D_QCoh(𝒪_Z)`: it is the composite of the adjunction
bijections of [Stacks, Tag 0A76] and of `a`, of full faithfulness of the inclusion of
`D_QCoh(𝒪_Z)`, and of composition with the comparison isomorphism of the two models of `Ri_*`. -/
theorem bijective_comp_closedImmersionRightAdjointToDerivedSheafHom_app
    (K : quasiCoherentDerivedCategory W) (M : quasiCoherentDerivedCategory Z) :
    Function.Bijective (fun g : M.obj ⟶ (a.obj K).obj =>
      g ≫ (closedImmersionRightAdjointToDerivedSheafHom i hpush a adj).app K) := by
  refine ⟨fun g₁ g₂ h => ?_, fun h => ?_⟩
  · replace h : (ObjectProperty.homMk g₁ : M ⟶ a.obj K).hom ≫
        (closedImmersionRightAdjointToDerivedSheafHom i hpush a adj).app K =
      (ObjectProperty.homMk g₂ : M ⟶ a.obj K).hom ≫
        (closedImmersionRightAdjointToDerivedSheafHom i hpush a adj).app K := h
    rw [hom_comp_closedImmersionRightAdjointToDerivedSheafHom_app i hpush a adj K M
        (ObjectProperty.homMk g₁),
      hom_comp_closedImmersionRightAdjointToDerivedSheafHom_app i hpush a adj K M
        (ObjectProperty.homMk g₂)] at h
    replace h := (cancel_epi _).1
      (((closedImmersionSheafHomAdjunction i).homEquiv M.obj K.obj).injective h)
    exact congrArg (·.hom) ((adj.homEquiv M K).symm.injective (ObjectProperty.hom_ext _ h))
  · obtain ⟨g, hg⟩ := (adj.homEquiv M K).symm.surjective (ObjectProperty.homMk
      ((closedImmersionPushforwardIsoDerivedPushforward i).inv.app M.obj ≫
        ((closedImmersionSheafHomAdjunction i).homEquiv M.obj K.obj).symm h))
    refine ⟨g.hom, ?_⟩
    beta_reduce
    rw [hom_comp_closedImmersionRightAdjointToDerivedSheafHom_app i hpush a adj K M g, hg]
    exact (congrArg _ (Iso.hom_inv_id_app_assoc _ _ _)).trans
      (((closedImmersionSheafHomAdjunction i).homEquiv M.obj K.obj).apply_symm_apply h)

end

/-- **Stacks Project, Tag 0A9X (Lemma 48.9.7).** Let `i : Z ⟶ W` be a pseudo-coherent closed
immersion of schemes and let `a` be a right adjoint of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`. Then
on bounded-below complexes with quasi-coherent cohomology `a` is derived sheaf Hom out of the
structure sheaf of the closed subscheme: `a(K) = R𝓗om_{𝒪_W}(𝒪_Z, K)` for `K` in
`D⁺_QCoh(𝒪_W)`. -/
@[stacks 0A9X "the quasi-compactness and quasi-separatedness of the target are dropped, \
the source using them only to produce the right adjoint a, which here is an explicit parameter \
together with its adjunction"]
theorem isDerivedSheafHomRightAdjointAtModel_of_pseudoCoherent
    (hpc : PseudoCoherent i)
    (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
      ((DerivedCategory.homologyFunctor W.Modules n).obj
        ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : quasiCoherentDerivedPushforward i hpush ⊣ a) :
    IsDerivedSheafHomRightAdjointAtModel i a := by
  have hiso : ∀ K : (isBoundedBelowQuasiCoherentAtModel W).FullSubcategory,
      IsIso ((closedImmersionRightAdjointToDerivedSheafHom i hpush a adj).app K.obj) := by
    intro K
    have hstd := AlgebraicGeometry.Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus
      i hpc ((modelEquiv instW (HasDerivedCategory.standard W.Modules)).functor.obj K.obj.obj)
      ((StacksDraft.DerivedModel.derivedCategoryBPlus_modelEquiv_functor_obj_iff
        (SheafOfModules.isQuasicoherent W.ringCatSheaf) instW
        (HasDerivedCategory.standard W.Modules) K.obj.obj).2 ⟨K.property, K.obj.property⟩)
    have hQC :=
      (@ClosedQuotientMorphismOfRingedSpaces.derivedCategoryBPlus_derivedSheafHom_modelEquiv_iff
        (closedQuotient i) instW instZ (HasDerivedCategory.standard W.Modules)
        (HasDerivedCategory.standard Z.Modules)
        (SheafOfModules.isQuasicoherent Z.ringCatSheaf)
        (inferInstanceAs
          (SheafOfModules.isQuasicoherent Z.ringCatSheaf).IsClosedUnderIsomorphisms)
        K.obj.obj).1 hstd
    obtain ⟨s, hs⟩ :=
      (bijective_comp_closedImmersionRightAdjointToDerivedSheafHom_app i hpush a adj K.obj
      ⟨(closedImmersionDerivedSheafHom i).obj K.obj.obj,
        hQC.2⟩).surjective (𝟙 _)
    refine ⟨s, ?_, hs⟩
    refine (bijective_comp_closedImmersionRightAdjointToDerivedSheafHom_app i hpush a adj K.obj
      (a.obj K.obj)).injective ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg ((closedImmersionRightAdjointToDerivedSheafHom i hpush a adj).app K.obj ≫ ·)
        hs).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  exact ⟨NatIso.ofComponents
    (fun K => @asIso _ _ _ _
      ((closedImmersionRightAdjointToDerivedSheafHom i hpush a adj).app K.obj) (hiso K))
    fun f => (closedImmersionRightAdjointToDerivedSheafHom i hpush a adj).naturality _⟩

/-- **Stacks Project, Tag 0A9X**, in uniform form: for *every* pseudo-coherent closed immersion
into a quasi-compact and quasi-separated scheme, any right adjoint of derived direct image on
complexes with quasi-coherent cohomology is derived sheaf Hom out of the structure sheaf of the
closed subscheme on bounded-below complexes.

The quasi-compactness and quasi-separatedness of the target are not used — they are what the
source needs in order to produce the right adjoint, which here is an explicit parameter — but
they are part of the statement of the tag and are therefore kept. -/
theorem isDerivedSheafHomRightAdjointAtModel_of_compactSpace :
    ∀ {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
      [HasDerivedCategory.{w} Z.Modules] [HasDerivedCategory.{w} W.Modules],
      CompactSpace W → QuasiSeparatedSpace W → PseudoCoherent i →
      ∀ (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
          ((DerivedCategory.homologyFunctor W.Modules n).obj
            ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
        (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z),
        (quasiCoherentDerivedPushforward i hpush ⊣ a) →
          IsDerivedSheafHomRightAdjointAtModel i a :=
  fun j _ _ _ _ _ hpc hq b bdj =>
    isDerivedSheafHomRightAdjointAtModel_of_pseudoCoherent j hpc hq b bdj

end Stacks.Duality

end
