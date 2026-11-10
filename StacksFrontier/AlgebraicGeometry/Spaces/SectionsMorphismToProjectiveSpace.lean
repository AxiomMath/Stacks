module

public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsGenerationOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProjectiveSpaceContracted
public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.BaseChange

/-!
# The morphism to projective space attached to generating sections on an algebraic space

Let `X` be an algebraic space over a scheme `S` of a big fppf site, `f : X ⟶ h_Y` a morphism to a
scheme `Y` of the site, `M` an invertible `𝒪_X`-module and `s₀, …, sᵣ` global sections of `M`.
On the open subspace `U ⊆ X` where the sections have no common zero
(`AlgebraicGeometry.Space.sectionsGenerationSubfunctor`) we define the morphism

`φ = φ_{M, (s₀, …, sᵣ)} : U ⟶ ℙʳ_Y`

over `Y` of Stacks 01ND for algebraic spaces. At a scheme point `t : h_T ⟶ U` the read module and
sections form an invertible module with `r + 1` generating sections on `T`, classified by a
morphism `T ⟶ ℙʳ_ℤ` (Stacks 01NE); paired with `f ∘ t` it is a morphism `T ⟶ ℙʳ_Y`, and these
morphisms are natural in `T`.

## Main definitions

* `AlgebraicGeometry.Space.projectiveSpaceOverSiteObject`: `ℙʳ_Y` as an object of the site.
* `AlgebraicGeometry.Space.pointGeneratingTuple`: the generating pair read at a scheme point of
  `U`.
* `AlgebraicGeometry.Space.sectionsMorphismToProjectiveSpace`: **the morphism `φ : U ⟶ ℙʳ_Y`.**

## Main results

* `AlgebraicGeometry.Space.sectionsMorphismToProjectiveSpace_app`: at a scheme point, `φ` is the
  morphism Stacks 01ND attaches to the read pair.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 0D3A](https://stacks.math.columbia.edu/tag/0D3A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Projective `r`-space over an object `Y` of the site, as an object of the site.** -/
def projectiveSpaceOverSiteObject (Y : BigFppfOver B S hS) (r : ℕ) : BigFppfOver B S hS :=
  siteObject B S hS (contains_projectiveSpaceOver B Y.left.1 Y.left.2 r)
    ((projectiveSpaceOver r Y.left.1 ↘ Y.left.1) ≫ Y.hom.1)

/-- The projection `ℙʳ_Y ⟶ Y`, as a morphism of the site. -/
def projectiveSpaceOverSiteObjectProj (Y : BigFppfOver B S hS) (r : ℕ) :
    projectiveSpaceOverSiteObject B S hS Y r ⟶ Y :=
  Over.homMk (ObjectProperty.homMk (projectiveSpaceOver r Y.left.1 ↘ Y.left.1)) rfl

/-- A morphism of schemes into `ℙʳ_Y` lying over a morphism of the site into `Y`, as a morphism
of the site. -/
def projectiveSpaceOverSiteHom {Y T : BigFppfOver B S hS} (r : ℕ) (a : T ⟶ Y)
    (g : (BigFppfOver.toScheme B S hS).obj T ⟶ projectiveSpaceAtUniverse.{u} r) :
    T ⟶ projectiveSpaceOverSiteObject B S hS Y r :=
  Over.homMk (ObjectProperty.homMk (Stacks.AmpleProjectiveImmersion.liftOver
    ((BigFppfOver.toScheme B S hS).map a) g)) (by
      apply ObjectProperty.hom_ext
      change Stacks.AmpleProjectiveImmersion.liftOver ((BigFppfOver.toScheme B S hS).map a) g ≫
        (projectiveSpaceOver r Y.left.1 ↘ Y.left.1) ≫ Y.hom.1 = T.hom.1
      rw [← Category.assoc]
      change (Stacks.AmpleProjectiveImmersion.liftOver ((BigFppfOver.toScheme B S hS).map a) g ≫
        pullback.fst (terminal.from Y.left.1)
          (terminal.from (projectiveSpaceAtUniverse.{u} r))) ≫ Y.hom.1 = T.hom.1
      rw [Stacks.AmpleProjectiveImmersion.liftOver_fst]
      exact congrArg (fun k ↦ k.1) (Over.w a))

/-- **`AlgebraicGeometry.Space.projectiveSpaceOverSiteHom` is natural in the source.** -/
theorem comp_projectiveSpaceOverSiteHom {Y T T' : BigFppfOver B S hS} (r : ℕ) (h : T' ⟶ T)
    (a : T ⟶ Y) (g : (BigFppfOver.toScheme B S hS).obj T ⟶ projectiveSpaceAtUniverse.{u} r) :
    h ≫ projectiveSpaceOverSiteHom B S hS r a g =
      projectiveSpaceOverSiteHom B S hS r (h ≫ a) ((BigFppfOver.toScheme B S hS).map h ≫ g) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change (BigFppfOver.toScheme B S hS).map h ≫
      Stacks.AmpleProjectiveImmersion.liftOver ((BigFppfOver.toScheme B S hS).map a) g =
    Stacks.AmpleProjectiveImmersion.liftOver ((BigFppfOver.toScheme B S hS).map (h ≫ a))
      ((BigFppfOver.toScheme B S hS).map h ≫ g)
  rw [← Stacks.AmpleProjectiveImmersion.liftOver_eq ((BigFppfOver.toScheme B S hS).map (h ≫ a))
    ((BigFppfOver.toScheme B S hS).map h ≫
      Stacks.AmpleProjectiveImmersion.liftOver ((BigFppfOver.toScheme B S hS).map a) g)
    (by rw [Category.assoc, Stacks.AmpleProjectiveImmersion.liftOver_fst, Functor.map_comp]),
    Category.assoc, Stacks.AmpleProjectiveImmersion.liftOver_snd]

/-- The sections map of a morphism of modules on a scheme is its value on sections. -/
theorem scheme_modules_hom_app_apply {Z : Scheme.{u}} {P Q : Z.Modules} (φ : P ⟶ Q)
    (U : Z.Opens) (x : Γ(P, U)) : Scheme.Modules.Hom.app φ U x = φ.val.app (op U) x :=
  rfl

/-- A value of a morphism out of a pullback on a pulled back section, read on its sections map. -/
theorem hom_app_pullbackGlobalSections_of_val {Z Z' : Scheme.{u}} (f : Z' ⟶ Z) (F : Z.Modules)
    (G : Z'.Modules) (c : (Scheme.Modules.pullback f).obj F ⟶ G) (x : Γ(F, ⊤)) (y : Γ(G, ⊤))
    (h : c.val.app (op ⊤) (pullbackGlobalSections f F x) = y) :
    Scheme.Modules.Hom.app c ⊤ (pullbackGlobalSections f F x) = y :=
  h

/-- The coordinates of the pullback of a generating pair. -/
theorem pullbackTuple_coord_eq {Z Z' : Scheme.{u}} {r : ℕ} (h : Z' ⟶ Z)
    (t : Stacks.ProjectiveSpaceModuli.GeneratingTuple Z r) (i : Fin (r + 1)) :
    (Stacks.ProjectiveSpaceModuli.pullbackTuple h t).coord i =
      pullbackGlobalSections h t.bundle (t.coord i) :=
  rfl

/-- **A comparison carrying pulled back coordinates to coordinates identifies two generating
pairs**, the pullback of the first and the second, in the sense of Stacks 01NE. -/
theorem isomorphic_pullbackTuple_of_comparison {Z Z' : Scheme.{u}} {r : ℕ} (h : Z' ⟶ Z)
    (t : Stacks.ProjectiveSpaceModuli.GeneratingTuple Z r)
    (t' : Stacks.ProjectiveSpaceModuli.GeneratingTuple Z' r)
    (c : (Scheme.Modules.pullback h).obj t.bundle ⟶ t'.bundle) (hc : IsIso c)
    (hcoord : ∀ i, Scheme.Modules.Hom.app c ⊤ (pullbackGlobalSections h t.bundle (t.coord i)) =
      t'.coord i) :
    Stacks.ProjectiveSpaceModuli.Isomorphic (Stacks.ProjectiveSpaceModuli.pullbackTuple h t) t' :=
  ⟨@asIso _ _ _ _ c hc, hcoord⟩

/-- `AlgebraicGeometry.Space.isomorphic_pullbackTuple_of_comparison` for pairs given by their
components. -/
theorem isomorphic_pullbackTuple_mk_of_comparison {Z Z' : Scheme.{u}} {r : ℕ} (h : Z' ⟶ Z)
    (P : Z.Modules) (hP : Stacks.Ample.IsInvertibleModule Z P) (σ : Fin (r + 1) → Γ(P, ⊤))
    (hσ : Stacks.ProjectiveFromSections.GeneratesStalks σ)
    (P' : Z'.Modules) (hP' : Stacks.Ample.IsInvertibleModule Z' P') (σ' : Fin (r + 1) → Γ(P', ⊤))
    (hσ' : Stacks.ProjectiveFromSections.GeneratesStalks σ')
    (c : (Scheme.Modules.pullback h).obj P ⟶ P') (hc : IsIso c)
    (hcoord : ∀ i, Scheme.Modules.Hom.app c ⊤ (pullbackGlobalSections h P (σ i)) = σ' i) :
    Stacks.ProjectiveSpaceModuli.Isomorphic
      (Stacks.ProjectiveSpaceModuli.pullbackTuple h ⟨P, hP, σ, hσ⟩) ⟨P', hP', σ', hσ'⟩ :=
  isomorphic_pullbackTuple_of_comparison h _ _ c hc hcoord

/-- **Moving a pulled back section across identifications of the two modules.** -/
theorem hom_app_comp_pullbackGlobalSections {Z Z' : Scheme.{u}} (f : Z' ⟶ Z)
    {A A₀ : Z.Modules} {A' A₀' : Z'.Modules} (e : A ≅ A₀) (e' : A' ≅ A₀')
    (c : (Scheme.Modules.pullback f).obj A₀ ⟶ A₀') (σ : Γ(A₀, ⊤)) (σ' : Γ(A₀', ⊤))
    (hc : Scheme.Modules.Hom.app c ⊤ (pullbackGlobalSections f A₀ σ) = σ') :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map e.hom ≫ c ≫ e'.inv) ⊤
        (pullbackGlobalSections f A (Scheme.Modules.Hom.app e.inv ⊤ σ)) =
      Scheme.Modules.Hom.app e'.inv ⊤ σ' := by
  have h1 := congrArg (fun φ ↦ φ (Scheme.Modules.Hom.app e.inv ⊤ σ))
    (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality_app f e.hom)
  simp only [ConcreteCategory.comp_apply] at h1
  have h2 : Scheme.Modules.Hom.app e.hom ⊤ (Scheme.Modules.Hom.app e.inv ⊤ σ) = σ := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, h1, h2, hc]

/-- An isomorphism of modules preserves the nonvanishing locus of a global section, on the sections
map of the isomorphism. -/
theorem nonvanishingLocus_hom_app_iso {Z : Scheme.{u}} {A A' : Z.Modules} (e : A ≅ A')
    (t : Γ(A, ⊤)) :
    Stacks.Ample.nonvanishingLocus A' (Scheme.Modules.Hom.app e.hom ⊤ t) =
      Stacks.Ample.nonvanishingLocus A t :=
  AlgebraicGeometry.Cube.nonvanishingLocus_hom_app_top_of_iso e t

/-! ### The generating pair at a scheme point -/

section Tuple

variable {X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)

/-- **The read module, as an opaque copy.** It is `AlgebraicGeometry.Space.pointModule`
(`AlgebraicGeometry.Space.pointBundle_def`). -/
noncomputable irreducible_def pointBundle (T : BigFppfOver B S hS)
    (k : representedAlgebraicSpace B S hS T ⟶ X) : ((BigFppfOver.toScheme B S hS).obj T).Modules :=
  pointModule B S hS M T k

/-- The opaque copy of the read module is the read module. -/
abbrev pointBundleIso (T : BigFppfOver B S hS) (k : representedAlgebraicSpace B S hS T ⟶ X) :
    pointBundle B S hS M T k ≅ pointModule B S hS M T k :=
  eqToIso (pointBundle_def B S hS M T k)

/-- The read global section, on the opaque copy of the read module, itself opaque. -/
noncomputable irreducible_def pointBundleSection (T : BigFppfOver B S hS)
    (k : representedAlgebraicSpace B S hS T ⟶ X)
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M) :
    Γ(pointBundle B S hS M T k, ⊤) :=
  Scheme.Modules.Hom.app (pointBundleIso B S hS M T k).inv ⊤ (pointGlobalSection B S hS M T k σ)

/-- The nonvanishing locus of the opaque read section is that of the read global section. -/
theorem nonvanishingLocus_pointBundleSection (T : BigFppfOver B S hS)
    (k : representedAlgebraicSpace B S hS T ⟶ X)
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M) :
    Stacks.Ample.nonvanishingLocus (pointBundle B S hS M T k) (pointBundleSection B S hS M T k σ) =
      Stacks.Ample.nonvanishingLocus (pointModule B S hS M T k)
        (pointGlobalSection B S hS M T k σ) := by
  rw [pointBundleSection_def]
  exact nonvanishingLocus_hom_app_iso (pointBundleIso B S hS M T k).symm _

/-- **The comparison of the opaque readings along `k` and along `k' = h ≫ k`**, itself opaque: it
is `AlgebraicGeometry.Space.pointModuleComparison` conjugated by the identifications of the opaque
copies with the readings (`AlgebraicGeometry.Space.pointBundleComparison_def`). -/
noncomputable irreducible_def pointBundleComparison {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (k : representedAlgebraicSpace B S hS T ⟶ X) (k' : representedAlgebraicSpace B S hS T' ⟶ X)
    (e : representedMap B S hS h ≫ k = k') :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
      (pointBundle B S hS M T k) ⟶ pointBundle B S hS M T' k' :=
  (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
      (pointBundleIso B S hS M T k).hom ≫ pointModuleComparison B S hS M h k k' e ≫
        (pointBundleIso B S hS M T' k').inv

/-- For `M` quasi-coherent the comparison of the opaque readings is an isomorphism. -/
theorem isIso_pointBundleComparison (hM : M.IsQuasicoherentOnSite) {T T' : BigFppfOver B S hS}
    (h : T' ⟶ T) (k : representedAlgebraicSpace B S hS T ⟶ X)
    (k' : representedAlgebraicSpace B S hS T' ⟶ X) (e : representedMap B S hS h ≫ k = k') :
    IsIso (pointBundleComparison B S hS M h k k' e) := by
  have := isIso_pointModuleComparison B S hS M hM h k k' e
  rw [pointBundleComparison_def]
  infer_instance

/-- `AlgebraicGeometry.Space.pointModuleComparison_pullbackGlobalSections` read on the sections
maps of the morphism. -/
theorem pointModuleComparison_app_pullbackGlobalSections
    {T T' : BigFppfOver B S hS} (h : T' ⟶ T) (k : representedAlgebraicSpace B S hS T ⟶ X)
    (k' : representedAlgebraicSpace B S hS T' ⟶ X) (e : representedMap B S hS h ≫ k = k')
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M) :
    Scheme.Modules.Hom.app (pointModuleComparison B S hS M h k k' e) ⊤
        (pullbackGlobalSections ((BigFppfOver.toScheme B S hS).map h)
          (pointModule B S hS M T k) (pointGlobalSection B S hS M T k σ)) =
      pointGlobalSection B S hS M T' k' σ :=
  hom_app_pullbackGlobalSections_of_val _ _ _ _ _ _
    (pointModuleComparison_pullbackGlobalSections B S hS M h k k' e σ)

/-- **The comparison of the opaque readings carries pulled back read sections to read
sections.** -/
theorem pointBundleComparison_app_pullbackGlobalSections
    {T T' : BigFppfOver B S hS} (h : T' ⟶ T) (k : representedAlgebraicSpace B S hS T ⟶ X)
    (k' : representedAlgebraicSpace B S hS T' ⟶ X) (e : representedMap B S hS h ≫ k = k')
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M) :
    Scheme.Modules.Hom.app (pointBundleComparison B S hS M h k k' e) ⊤
        (pullbackGlobalSections ((BigFppfOver.toScheme B S hS).map h) (pointBundle B S hS M T k)
          (pointBundleSection B S hS M T k σ)) =
      pointBundleSection B S hS M T' k' σ := by
  rw [pointBundleComparison_def, pointBundleSection_def, pointBundleSection_def]
  exact hom_app_comp_pullbackGlobalSections _ (pointBundleIso B S hS M T k)
    (pointBundleIso B S hS M T' k') (pointModuleComparison B S hS M h k k' e) _ _
    (pointModuleComparison_app_pullbackGlobalSections B S hS M h k k' e σ)

variable (hinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property M)
    {r : ℕ} (s : Fin (r + 1) → (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M)

include hinv in
/-- An invertible module on an algebraic space is quasi-coherent on the site. -/
theorem isQuasicoherentOnSite_of_isInvertible' : M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isInvertible B S hS X M hinv.toAlgebraicGeometry

include hinv in
/-- The opaque copy of the reading of an invertible module is invertible. -/
theorem isInvertibleModule_pointBundle (T : BigFppfOver B S hS)
    (k : representedAlgebraicSpace B S hS T ⟶ X) :
    Stacks.Ample.IsInvertibleModule _ (pointBundle B S hS M T k) := by
  have := isInvertibleModule_pointModule B S hS M hinv T k
  exact Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ (pointBundleIso B S hS M T k).symm

/-- The open subspace of `X` where the sections `s` have no common zero. -/
abbrev sectionsGenerationLocus : Subfunctor X.1 :=
  sectionsGenerationSubfunctor B S hS M s (isQuasicoherentOnSite_of_isInvertible' B S hS M hinv)

/-- The read sections at a scheme point of the generation locus generate the read module. -/
theorem generatesStalks_pointBundleSection (T : BigFppfOver B S hS)
    (x : (sectionsGenerationLocus B S hS M hinv s).toFunctor.obj (op T)) :
    Stacks.ProjectiveFromSections.GeneratesStalks
      (L := pointBundle B S hS M T (sectionPoint B S hS x.1))
      (fun i ↦ pointBundleSection B S hS M T (sectionPoint B S hS x.1) (s i)) := by
  have := isInvertibleModule_pointBundle B S hS M hinv T (sectionPoint B S hS x.1)
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun z ↦ ?_
  obtain ⟨i, hi⟩ := x.2 z
  refine ⟨i, ?_⟩
  change z ∈ Stacks.Ample.nonvanishingLocus _ _
  rwa [nonvanishingLocus_pointBundleSection]

/-- **The generating pair read at a scheme point of the generation locus**: the read module, which
is invertible, with the read sections, which have no common zero, hence generate. -/
abbrev pointGeneratingTuple (T : BigFppfOver B S hS)
    (x : (sectionsGenerationLocus B S hS M hinv s).toFunctor.obj (op T)) :
    Stacks.ProjectiveSpaceModuli.GeneratingTuple ((BigFppfOver.toScheme B S hS).obj T) r :=
  ⟨pointBundle B S hS M T (sectionPoint B S hS x.1),
    isInvertibleModule_pointBundle B S hS M hinv T (sectionPoint B S hS x.1),
    fun i ↦ pointBundleSection B S hS M T (sectionPoint B S hS x.1) (s i),
    generatesStalks_pointBundleSection B S hS M hinv s T x⟩

/-- **The morphism `T ⟶ ℙʳ_ℤ` classifying the generating pair read at a scheme point** (Stacks
01NE). -/
def pointClassifyingMap (T : BigFppfOver B S hS)
    (x : (sectionsGenerationLocus B S hS M hinv s).toFunctor.obj (op T)) :
    (BigFppfOver.toScheme B S hS).obj T ⟶ projectiveSpaceAtUniverse.{u} r :=
  (Stacks.ProjectiveSpaceModuli.pointsEquiv _ r).symm
    ⟦pointGeneratingTuple B S hS M hinv s T x⟧

/-- The scheme point of a section of the generation locus, moved along a morphism of the site. -/
theorem representedMap_comp_sectionPoint_map {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (x : (sectionsGenerationLocus B S hS M hinv s).toFunctor.obj (op T)) :
    representedMap B S hS h ≫ sectionPoint B S hS x.1 = sectionPoint B S hS
      ((sectionsGenerationLocus B S hS M hinv s).toFunctor.map h.op x).1 :=
  representedMap_comp_sectionPoint B S hS h x.1

/-- **The read pair at `h ≫ t` is the pullback along `h` of the read pair at `t`**, up to the
identification of Stacks 01NE. -/
theorem isomorphic_pullbackTuple_pointGeneratingTuple {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (x : (sectionsGenerationLocus B S hS M hinv s).toFunctor.obj (op T)) :
    Stacks.ProjectiveSpaceModuli.Isomorphic
      (Stacks.ProjectiveSpaceModuli.pullbackTuple ((BigFppfOver.toScheme B S hS).map h)
        (pointGeneratingTuple B S hS M hinv s T x))
      (pointGeneratingTuple B S hS M hinv s T'
        ((sectionsGenerationLocus B S hS M hinv s).toFunctor.map h.op x)) :=
  isomorphic_pullbackTuple_of_comparison ((BigFppfOver.toScheme B S hS).map h) _ _
    (pointBundleComparison B S hS M h (sectionPoint B S hS x.1)
      (sectionPoint B S hS ((sectionsGenerationLocus B S hS M hinv s).toFunctor.map h.op x).1)
      (representedMap_comp_sectionPoint_map B S hS M hinv s h x))
    (isIso_pointBundleComparison B S hS M (isQuasicoherentOnSite_of_isInvertible' B S hS M hinv)
      h (sectionPoint B S hS x.1)
      (sectionPoint B S hS ((sectionsGenerationLocus B S hS M hinv s).toFunctor.map h.op x).1)
      (representedMap_comp_sectionPoint_map B S hS M hinv s h x))
    (fun i ↦ pointBundleComparison_app_pullbackGlobalSections B S hS M h (sectionPoint B S hS x.1)
      (sectionPoint B S hS ((sectionsGenerationLocus B S hS M hinv s).toFunctor.map h.op x).1)
      (representedMap_comp_sectionPoint_map B S hS M hinv s h x) (s i))

/-- **The classifying maps are natural in the scheme point.** -/
theorem comp_pointClassifyingMap {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (x : (sectionsGenerationLocus B S hS M hinv s).toFunctor.obj (op T)) :
    (BigFppfOver.toScheme B S hS).map h ≫ pointClassifyingMap B S hS M hinv s T x =
      pointClassifyingMap B S hS M hinv s T'
        ((sectionsGenerationLocus B S hS M hinv s).toFunctor.map h.op x) := by
  apply Stacks.ProjectiveSpaceModuli.pointsOfHom_injective
  rw [Stacks.ProjectiveSpaceModuli.pointsOfHom_comp]
  have h1 : Stacks.ProjectiveSpaceModuli.pointsOfHom (pointClassifyingMap B S hS M hinv s T x) =
      ⟦pointGeneratingTuple B S hS M hinv s T x⟧ :=
    (Stacks.ProjectiveSpaceModuli.pointsEquiv _ r).apply_symm_apply _
  have h2 : Stacks.ProjectiveSpaceModuli.pointsOfHom (pointClassifyingMap B S hS M hinv s T'
      ((sectionsGenerationLocus B S hS M hinv s).toFunctor.map h.op x)) =
      ⟦pointGeneratingTuple B S hS M hinv s T'
        ((sectionsGenerationLocus B S hS M hinv s).toFunctor.map h.op x)⟧ :=
    (Stacks.ProjectiveSpaceModuli.pointsEquiv _ r).apply_symm_apply _
  rw [h1, h2, Stacks.ProjectiveSpaceModuli.pullbackPoints_mk]
  exact Quotient.sound (isomorphic_pullbackTuple_pointGeneratingTuple B S hS M hinv s h x)

/-- **Stacks 01ND for algebraic spaces: the morphism `φ = φ_{M, (s₀, …, sᵣ)} : U ⟶ ℙʳ_Y`** on the
open subspace `U` where the sections `s` generate, for a morphism `g : X ⟶ h_Y`.  At a scheme
point `t` of `U` over `T` it is the morphism `T ⟶ ℙʳ_Y` lying over `g ∘ t` whose component to
`ℙʳ_ℤ` classifies the pair read at `t` (Stacks 01NE). -/
def sectionsMorphismToProjectiveSpace {Y : BigFppfOver B S hS} (g : X.1 ⟶ yoneda.obj Y) :
    (sectionsGenerationLocus B S hS M hinv s).toFunctor ⟶
      yoneda.obj (projectiveSpaceOverSiteObject B S hS Y r) where
  app T := TypeCat.ofHom fun x ↦ projectiveSpaceOverSiteHom B S hS r (g.app T x.1)
    (pointClassifyingMap B S hS M hinv s T.unop x)
  naturality T T' h := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    change projectiveSpaceOverSiteHom B S hS r (g.app T' (X.1.map h x.1))
        (pointClassifyingMap B S hS M hinv s T'.unop
          ((sectionsGenerationLocus B S hS M hinv s).toFunctor.map h.unop.op x)) =
      h.unop ≫ projectiveSpaceOverSiteHom B S hS r (g.app T x.1)
        (pointClassifyingMap B S hS M hinv s T.unop x)
    rw [comp_projectiveSpaceOverSiteHom, comp_pointClassifyingMap]
    congr 1
    exact ConcreteCategory.congr_hom (g.naturality h) x.1

/-- The value of `φ` at a scheme point of the generation locus. -/
theorem sectionsMorphismToProjectiveSpace_app {Y : BigFppfOver B S hS} (g : X.1 ⟶ yoneda.obj Y)
    (T : BigFppfOver B S hS) (x : (sectionsGenerationLocus B S hS M hinv s).toFunctor.obj (op T)) :
    (sectionsMorphismToProjectiveSpace B S hS M hinv s g).app (op T) x =
      projectiveSpaceOverSiteHom B S hS r (g.app (op T) x.1)
        (pointClassifyingMap B S hS M hinv s T x) :=
  rfl

/-- **At a scheme point where the read pair is identified with a pair `t`, the component of `φ`
to `ℙʳ_ℤ` is the morphism classifying `t`.** -/
theorem pointClassifyingMap_eq_of_isomorphic (T : BigFppfOver B S hS)
    (x : (sectionsGenerationLocus B S hS M hinv s).toFunctor.obj (op T))
    (t : Stacks.ProjectiveSpaceModuli.GeneratingTuple ((BigFppfOver.toScheme B S hS).obj T) r)
    (ht : Stacks.ProjectiveSpaceModuli.Isomorphic (pointGeneratingTuple B S hS M hinv s T x) t) :
    pointClassifyingMap B S hS M hinv s T x =
      (Stacks.ProjectiveSpaceModuli.pointsEquiv _ r).symm ⟦t⟧ := by
  rw [pointClassifyingMap, Quotient.sound ht]

/-- **At a scheme point where the read pair is identified with an invertible module `N` with
generating sections `σ`, the component of `φ` to `ℙʳ_ℤ` is the morphism `φ_{(N, σ)}` of
Stacks 01ND.** -/
theorem pointClassifyingMap_eq_toProjectiveSpaceAtUniverse (T : BigFppfOver B S hS)
    (x : (sectionsGenerationLocus B S hS M hinv s).toFunctor.obj (op T))
    (N : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    [hN : Stacks.Ample.IsInvertibleModule _ N] (σ : Fin (r + 1) → Γ(N, ⊤))
    (hσ : Stacks.ProjectiveFromSections.GeneratesStalks σ)
    (ht : Stacks.ProjectiveSpaceModuli.Isomorphic (pointGeneratingTuple B S hS M hinv s T x)
      ⟨N, hN, σ, hσ⟩) :
    pointClassifyingMap B S hS M hinv s T x =
      Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse σ hσ := by
  rw [pointClassifyingMap_eq_of_isomorphic B S hS M hinv s T x _ ht]
  exact Stacks.ProjectiveSpaceModuli.pointsEquiv_symm_eq
    (fun j ↦ Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse σ hσ j)

end Tuple

end AlgebraicGeometry.Space

end
