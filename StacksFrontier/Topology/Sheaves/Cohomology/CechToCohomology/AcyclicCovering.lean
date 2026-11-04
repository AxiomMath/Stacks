module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Algebra.Homology.ShortComplex.DiscreteFunctorCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.ComparisonToDerivedSections

/-!
# Čech cohomology of an acyclic open covering

Let `(X, O)` be a ringed space, let `U` be an open subset covered by a family `Ui`, and let `F`
be a sheaf of `O`-modules whose higher cohomology vanishes on every nonempty finite intersection
of members of the covering.  Then the canonical comparison
`Stacks.Cohomology.CechDerived.cechCohomologyToCohomology` of [Stacks, Tag 01EQ], from the Čech
cohomology of the covering to the cohomology of `F` over `U`, is an isomorphism, as
`O(U)`-modules.

## Main results

* `isIso_cechCohomologyToCohomology_app`: **[Stacks, Tag 01ET]**.

## Implementation notes

The comparison is `Q(β) ≫ Q(α)⁻¹` followed by the identification of the sections of an injective
resolution with derived sections.  Two of the three factors are invertible for every covering and
every sheaf of modules, and are already proved with `Stacks 01EQ`: `α` because the *columns* of
the Čech bicomplex are the Čech complexes of injective sheaves, and the last factor by the
universal property of the right derived functor.  So the whole content of this tag is that the
remaining factor `β` is a quasi-isomorphism, i.e. that the *rows* of the Čech bicomplex of an
injective resolution are exact away from resolution degree zero -- and that is exactly where the
acyclicity hypothesis enters.

A row of the Čech bicomplex in Čech degree `n` is the product, over the tuples
`x : Fin (n + 1) → I`, of the sections of the resolution over the intersection selected by `x`.
Three facts make the row exact away from degree zero:

* sections over one intersection carry the resolution to a complex which is exact away from
  degree zero, because the higher right derived functors of that sections functor vanish on `F`
  -- this is the hypothesis, read through
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj` and the `ℕ`-to-`ℤ` bridge
  `CategoryTheory.Functor.mapExtendIso`;
* exactness in a category of functors out of a discrete category is exactness in each component,
  because evaluation preserves homology;
* products indexed by an arbitrary type are exact in `ModuleCat`, which is Mathlib's `AB4Star`
  instance -- so the limit functor carries the componentwise exactness to the product.

The kernel clause of [Stacks, Tag 0133] for the rows needs no hypothesis beyond left exactness:
the Čech cochain functor in a fixed degree preserves finite limits, being a product of sections
functors, and sections over an open subset preserve finite limits.

## References

* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.CechSheaf
open Stacks.Cohomology.CechDerived
open Stacks.Cohomology.CechTotalComparison (exactAt_mapHomologicalComplex extendXIso_naturality
  isIso_kernelLift_of_mono_of_exact mono_iso_hom resolutionAug
  resolutionAug_comp_d isIso_kernelLift_resolutionAug exactAt_cochainComplex)
open StacksDraft.TotalComplexQuasiIso

universe u

namespace Stacks.Cohomology.CechAcyclic

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction of scalars is exact -/

/-- **Restriction of scalars preserves finite limits**, being the identity on underlying abelian
groups. -/
theorem preservesFiniteLimits_restrictScalars {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) := by
  have heq : forget₂ (ModuleCat.{u} S) AddCommGrpCat =
      ModuleCat.restrictScalars.{u} f ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat := rfl
  have : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{u} f ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat) :=
    preservesFiniteLimits_of_natIso (eqToIso heq)
  exact preservesFiniteLimits_of_reflects_of_preserves
    (ModuleCat.restrictScalars.{u} f) (forget₂ (ModuleCat.{u} R) AddCommGrpCat)

/-- **Restriction of scalars preserves homology.**  It is exact: finite limits by
`preservesFiniteLimits_restrictScalars`, and finite colimits because it has a left adjoint. -/
theorem preservesHomology_restrictScalars {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars.{u} f).PreservesHomology := by
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) :=
    preservesFiniteLimits_restrictScalars f
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u} f) := by
    constructor
    intro J _ _
    constructor
    intro G
    infer_instance
  exact Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{u} f)

/-! ### Sections over one object of the slice category -/

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {I : Type u} (U : Opens X) (Ui : I → Opens X) (hU : U = ⨆ i, Ui i)

/-- **Sections over an object of the slice over `U`**, as a functor of the sheaf of modules and
as a module over `O(U)`.  The Čech cochains of the covering in a fixed degree are the product of
these over the tuples of members of the covering. -/
def overSectionsFunctor (Y : Over U) :
    SheafOfModules.{u} O ⥤ ModuleCat.{u} (SectionRing O U) :=
  sectionsPresheafFunctor (R := O) U ⋙
    (CategoryTheory.evaluation (Over U)ᵒᵖ (ModuleCat.{u} (SectionRing O U))).obj (op Y)

/-- **Sections over an object of the slice are sections over the underlying open subset**, with
the `O(U)`-action obtained by restriction of scalars along the structure morphism. -/
def overSectionsFunctorIso (Y : Over U) :
    overSectionsFunctor O U Y ≅
      SheafOfModules.evaluation.{u} O (op ((Over.forget U).obj Y)) ⋙
        ModuleCat.restrictScalars
          ((O.obj.map ((Over.forget U).op.map (Over.mkIdTerminal.op.to (op Y)))).hom) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by ext x; rfl)

/-- **Sections over an object of the slice preserve finite limits**, both factors of
`overSectionsFunctorIso` doing so. -/
instance preservesFiniteLimits_overSectionsFunctor (Y : Over U) :
    PreservesFiniteLimits (overSectionsFunctor O U Y) := by
  have := preservesFiniteLimits_restrictScalars
    ((O.obj.map ((Over.forget U).op.map (Over.mkIdTerminal.op.to (op Y)))).hom)
  exact preservesFiniteLimits_of_natIso (overSectionsFunctorIso O U Y).symm

instance preservesZeroMorphisms_overSectionsFunctor (Y : Over U) :
    (overSectionsFunctor O U Y).PreservesZeroMorphisms := by
  dsimp only [overSectionsFunctor]
  infer_instance

/-- **Restriction to the slice over `U` is additive.**  A morphism of sheaves of modules acts on
sections sectionwise, so it acts additively. -/
instance additive_sectionsPresheafFunctor : (sectionsPresheafFunctor (R := O) U).Additive := by
  constructor
  intro F G f g
  ext Y x
  rfl

instance additive_overSectionsFunctor (Y : Over U) : (overSectionsFunctor O U Y).Additive := by
  dsimp only [overSectionsFunctor]
  infer_instance

/-- Exactness of a complex mapped by `F` follows from exactness of the mapped short complex for an
isomorphic functor `G`. -/
private theorem exactAt_mapHomologicalComplex_of_iso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] {F G : C ⥤ D} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (e : F ≅ G) (K : CochainComplex C ℤ) (q : ℤ)
    (h : ((K.sc q).map G).Exact) :
    ((F.mapHomologicalComplex (up ℤ)).obj K).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_iso (ShortComplex.mapNatIso (K.sc q) e).symm h

/-- **The sections of an injective resolution over an object of the slice are exact away from
degree zero**, as soon as the higher cohomology of the resolved sheaf vanishes on the underlying
open subset. -/
lemma exactAt_overSections_cochainComplex (Y : Over U)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F : SheafOfModules.{u} O}
    (J : InjectiveResolution F)
    (hY : ∀ n : ℕ, 0 < n →
      IsZero (((SheafOfModules.evaluation.{u} O (op ((Over.forget U).obj Y))).rightDerived n).obj
        F))
    (q : ℤ) (hq : q ≠ 0) :
    (((overSectionsFunctor O U Y).mapHomologicalComplex (up ℤ)).obj J.cochainComplex).ExactAt q :=
  by
  have hrs : (ModuleCat.restrictScalars
        ((O.obj.map ((Over.forget U).op.map
          (Over.mkIdTerminal.op.to (op Y)))).hom)).PreservesHomology :=
    preservesHomology_restrictScalars _
  have h0 := InjectiveResolution.exactAt_mapHomologicalComplex_cochainComplex
    (SheafOfModules.evaluation.{u} O (op ((Over.forget U).obj Y))) J hY q hq
  rw [HomologicalComplex.exactAt_iff] at h0
  have h1 : (((J.cochainComplex.sc q).map
      (SheafOfModules.evaluation.{u} O (op ((Over.forget U).obj Y)))).map
      (ModuleCat.restrictScalars
        ((O.obj.map ((Over.forget U).op.map (Over.mkIdTerminal.op.to (op Y)))).hom))).Exact :=
    h0.map (ModuleCat.restrictScalars
      ((O.obj.map ((Over.forget U).op.map (Over.mkIdTerminal.op.to (op Y)))).hom))
  exact exactAt_mapHomologicalComplex_of_iso (overSectionsFunctorIso O U Y) _ q h1

/-! ### The Čech cochain functor in a fixed degree is a product -/

/-- **The Čech cochains of the covering in a fixed degree.** -/
def cechTermFunctor (n : ℕ) : SheafOfModules.{u} O ⥤ ModuleCat.{u} (SectionRing O U) :=
  cechComplexNatFunctor O U Ui hU ⋙
    HomologicalComplex.eval (ModuleCat.{u} (SectionRing O U)) (up ℕ) n

/-- The family, indexed by the tuples of members of the covering, whose product is the Čech
cochains in degree `n`. -/
def cechEvalFamily (n : ℕ) :
    SheafOfModules.{u} O ⥤
      (Discrete (Fin (n + 1) → I) ⥤ ModuleCat.{u} (SectionRing O U)) where
  obj F := Discrete.functor fun x =>
    (overSectionsFunctor O U (inter (coverObject Ui hU) x)).obj F
  map f := Discrete.natTrans fun x =>
    (overSectionsFunctor O U (inter (coverObject Ui hU) x.as)).map f

/-- **The Čech cochains in a fixed degree are the product of the sections over the
intersections.**  This is the degreewise description of the Čech complex of
`StacksFrontier/CategoryTheory/Sites/CechComplex.lean`, read as a limit over a discrete category so
that the exactness of products is available. -/
def cechTermFunctorIso (n : ℕ) :
    cechTermFunctor O U Ui hU n ≅ cechEvalFamily O U Ui hU n ⋙ lim :=
  NatIso.ofComponents
    (fun F => IsLimit.conePointUniqueUpToIso
      (isLimitFan (coverObject Ui hU) (sectionsPresheaf U F) n)
      (limit.isLimit ((cechEvalFamily O U Ui hU n).obj F))) (by
    intro F G f
    refine limit.hom_ext (F := (cechEvalFamily O U Ui hU n).obj G) fun j => ?_
    obtain ⟨x⟩ := j
    have hG : (IsLimit.conePointUniqueUpToIso
          (isLimitFan (coverObject Ui hU) (sectionsPresheaf U G) n)
          (limit.isLimit ((cechEvalFamily O U Ui hU n).obj G))).hom ≫
        limit.π ((cechEvalFamily O U Ui hU n).obj G) (Discrete.mk x) =
          π (coverObject Ui hU) (sectionsPresheaf U G) n x :=
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ _
    have hF : (IsLimit.conePointUniqueUpToIso
          (isLimitFan (coverObject Ui hU) (sectionsPresheaf U F) n)
          (limit.isLimit ((cechEvalFamily O U Ui hU n).obj F))).hom ≫
        limit.π ((cechEvalFamily O U Ui hU n).obj F) (Discrete.mk x) =
          π (coverObject Ui hU) (sectionsPresheaf U F) n x :=
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ _
    have hlim : (cechEvalFamily O U Ui hU n ⋙ lim).map f ≫
          limit.π ((cechEvalFamily O U Ui hU n).obj G) (Discrete.mk x) =
        limit.π ((cechEvalFamily O U Ui hU n).obj F) (Discrete.mk x) ≫
          (overSectionsFunctor O U (inter (coverObject Ui hU) x)).map f :=
      limMap_π _ _
    refine (congrArg (fun m => (cechTermFunctor O U Ui hU n).map f ≫ m) hG).trans ?_
    refine (cech_map_comp_π (coverObject Ui hU) ((sectionsPresheafFunctor U).map f) n x).trans ?_
    refine Eq.symm ((Category.assoc _ _ _).trans ?_)
    refine (congrArg (fun m => (IsLimit.conePointUniqueUpToIso
      (isLimitFan (coverObject Ui hU) (sectionsPresheaf U F) n)
      (limit.isLimit ((cechEvalFamily O U Ui hU n).obj F))).hom ≫ m) hlim).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun m => m ≫ (overSectionsFunctor O U (inter (coverObject Ui hU) x)).map f) hF))

instance preservesFiniteLimits_cechEvalFamily (n : ℕ) :
    PreservesFiniteLimits (cechEvalFamily O U Ui hU n) := by
  apply preservesFiniteLimits_of_evaluation
  intro j
  obtain ⟨x⟩ := j
  exact preservesFiniteLimits_overSectionsFunctor O U (inter (coverObject Ui hU) x)

/-- **The Čech cochain functor in a fixed degree preserves finite limits**: it is a product of
sections functors, and sections preserve finite limits. -/
instance preservesFiniteLimits_cechTermFunctor (n : ℕ) :
    PreservesFiniteLimits (cechTermFunctor O U Ui hU n) := by
  have := preservesFiniteLimits_cechEvalFamily O U Ui hU n
  exact preservesFiniteLimits_of_natIso (cechTermFunctorIso O U Ui hU n).symm

instance preservesZeroMorphisms_cechTermFunctor (n : ℕ) :
    (cechTermFunctor O U Ui hU n).PreservesZeroMorphisms := by
  dsimp only [cechTermFunctor]
  infer_instance

section Acyclic

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : SheafOfModules.{u} O}
  (J : InjectiveResolution F)

/-- **The Čech cochains of an injective resolution in a fixed degree form a complex exact away
from resolution degree zero.**  Each factor is exact away from degree zero by acyclicity on the
corresponding intersection, exactness over a discrete index is exactness in each component, and
products are exact in a category of modules. -/
lemma exactAt_cechTerm_cochainComplex (n : ℕ)
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj F))
    (q : ℤ) (hq : q ≠ 0) :
    (((cechTermFunctor O U Ui hU n).mapHomologicalComplex (up ℤ)).obj
      J.cochainComplex).ExactAt q := by
  have hfactor : ∀ x : Fin (n + 1) → I, ((J.cochainComplex.sc q).map
      (overSectionsFunctor O U (inter (coverObject Ui hU) x))).Exact := by
    intro x
    have hV : (Over.forget U).obj (inter (coverObject Ui hU) x) = ⨅ a, Ui (x a) := by
      change (inter (coverObject Ui hU) x).left = _
      rw [inter_coverObject_left, inter_eq_iInf]
    have hY : ∀ m : ℕ, 0 < m → IsZero (((SheafOfModules.evaluation.{u} O
        (op ((Over.forget U).obj (inter (coverObject Ui hU) x)))).rightDerived m).obj F) := by
      intro m hm
      rw [hV]
      exact hac n x m hm
    have hx := exactAt_overSections_cochainComplex O U (inter (coverObject Ui hU) x) J hY q hq
    rwa [HomologicalComplex.exactAt_iff] at hx
  have hfam : ((J.cochainComplex.sc q).map (cechEvalFamily O U Ui hU n)).Exact := by
    refine ShortComplex.exact_of_app_discrete _ fun j => ?_
    obtain ⟨x⟩ := j
    exact hfactor x
  have hlim : (((J.cochainComplex.sc q).map (cechEvalFamily O U Ui hU n)).map
      (lim : (Discrete (Fin (n + 1) → I) ⥤ ModuleCat.{u} (SectionRing O U)) ⥤
        ModuleCat.{u} (SectionRing O U))).Exact := hfam.map lim
  exact exactAt_mapHomologicalComplex_of_iso (cechTermFunctorIso O U Ui hU n) _ q hlim

/-! ### The hypotheses of Stacks 0133 for the rows of the Čech bicomplex -/

/-- In a Čech degree in the range of the embedding, the integer-indexed Čech complex is the Čech
cochain functor of that degree. -/
def cechEvalIso (i : ℕ) :
    cechComplexIntFunctor O U Ui hU ⋙
        HomologicalComplex.eval (ModuleCat.{u} (SectionRing O U)) (up ℤ) (i : ℤ) ≅
      cechTermFunctor O U Ui hU i :=
  NatIso.ofComponents
    (fun G => HomologicalComplex.extendXIso ((cechComplexNatFunctor O U Ui hU).obj G)
      embeddingUpNat (ComplexShape.embeddingUpNat_f i))
    (fun {_ _} f => extendXIso_naturality ((cechComplexNatFunctor O U Ui hU).map f)
      (ComplexShape.embeddingUpNat_f i))

/-- **The rows of the Čech bicomplex of an injective resolution are exact away from resolution
degree zero.**  Off the range of the embedding the row vanishes; on it the row is the Čech
cochains of the resolution in a fixed degree. -/
lemma exactAt_cechBicomplexFlip_X (hac : ∀ (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj F))
    (p q : ℤ) (hq : q ≠ 0) :
    (((cechBicomplex O U Ui hU J.cochainComplex).flip).X p).ExactAt q := by
  rcases lt_or_ge p 0 with hp | hp
  · exact HomologicalComplex.ExactAt.of_isZero
      (isZero_cechBicomplex_X_X O U Ui hU J.cochainComplex q p (Or.inr hp))
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
    have hiso : ((cechBicomplex O U Ui hU J.cochainComplex).flip).X (i : ℤ) ≅
        ((cechTermFunctor O U Ui hU i).mapHomologicalComplex (up ℤ)).obj J.cochainComplex :=
      (NatIso.mapHomologicalComplex (cechEvalIso O U Ui hU i) (up ℤ)).app J.cochainComplex
    exact (exactAt_cechTerm_cochainComplex O U Ui hU J i hac q hq).of_iso hiso.symm

/-- **The kernel clause of [Stacks, Tag 0133] for the rows of the Čech bicomplex**: the Čech
complex of the resolved sheaf is, in each Čech degree, a kernel of the first differential of the
row.  Off the range of the embedding both terms vanish; on it this is the image of the
corresponding clause for the resolution under the Čech cochain functor, which preserves finite
limits. -/
lemma inducesIsoKernel_cechBetaRow (p : ℤ) :
    ∃ hβ : ((cechComplexIntFunctor O U Ui hU).map (resolutionAug J)).f p ≫
        (((cechBicomplex O U Ui hU J.cochainComplex).flip).X p).d 0 1 = 0,
      IsIso (kernel.lift ((((cechBicomplex O U Ui hU J.cochainComplex).flip).X p).d 0 1)
        (((cechComplexIntFunctor O U Ui hU).map (resolutionAug J)).f p) hβ) := by
  have hz := resolutionAug_comp_d J
  have hβ : ((cechComplexIntFunctor O U Ui hU).map (resolutionAug J)).f p ≫
      (((cechBicomplex O U Ui hU J.cochainComplex).flip).X p).d 0 1 = 0 := by
    change ((cechComplexIntFunctor O U Ui hU).map (resolutionAug J)).f p ≫
      ((cechComplexIntFunctor O U Ui hU).map (J.cochainComplex.d 0 1)).f p = 0
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, hz, Functor.map_zero,
      HomologicalComplex.zero_f]
  refine ⟨hβ, ?_⟩
  have hker := isIso_kernelLift_resolutionAug J
  have hmonoξ : Mono (resolutionAug J) := by
    rw [← kernel.lift_ι (J.cochainComplex.d 0 1) (resolutionAug J) hz]
    infer_instance
  rcases lt_or_ge p 0 with hp | hp
  · refine isIso_of_isZero _ (isZero_cechComplexIntFunctor_X O U Ui hU F p hp) ?_
    exact IsZero.of_mono (kernel.ι _)
      (isZero_cechBicomplex_X_X O U Ui hU J.cochainComplex 0 p (Or.inr hp))
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
    have hS : (ShortComplex.mk (resolutionAug J) (J.cochainComplex.d 0 1) hz).Exact :=
      (ShortComplex.exact_iff_epi_kernel_lift _).2 inferInstance
    have hexT := hS.map_of_mono_of_preservesKernel (cechTermFunctor O U Ui hU i) hmonoξ
      inferInstance
    have hmono : Mono (((cechComplexIntFunctor O U Ui hU).map (resolutionAug J)).f (i : ℤ)) := by
      have hnat := (cechEvalIso O U Ui hU i).hom.naturality (resolutionAug J)
      exact mono_of_mono_fac (h := (cechEvalIso O U Ui hU i).hom.app F ≫
        (cechTermFunctor O U Ui hU i).map (resolutionAug J)) hnat
    have eiso : (ShortComplex.mk (resolutionAug J) (J.cochainComplex.d 0 1) hz).map
          (cechTermFunctor O U Ui hU i) ≅
        ShortComplex.mk (((cechComplexIntFunctor O U Ui hU).map (resolutionAug J)).f (i : ℤ))
          ((((cechBicomplex O U Ui hU J.cochainComplex).flip).X (i : ℤ)).d 0 1) hβ :=
      ShortComplex.isoMk ((cechEvalIso O U Ui hU i).app F).symm
        ((cechEvalIso O U Ui hU i).app (J.cochainComplex.X 0)).symm
        ((cechEvalIso O U Ui hU i).app (J.cochainComplex.X 1)).symm
        ((cechEvalIso O U Ui hU i).inv.naturality (resolutionAug J)).symm
        ((cechEvalIso O U Ui hU i).inv.naturality (J.cochainComplex.d 0 1)).symm
    exact @isIso_kernelLift_of_mono_of_exact _ _ _ _ _ _ _ _ _ hmono
      (ShortComplex.exact_of_iso eiso hexT)

/-- **The augmentation `β`**, as a morphism into the zeroth row of the flipped Čech bicomplex:
in Čech degree `p` it is the Čech `p`-cochains of the augmentation `F ⟶ J⁰`. -/
def cechBetaRow :
    (cechComplexIntFunctor O U Ui hU).obj F ⟶
      rowZero ((cechBicomplex O U Ui hU J.cochainComplex).flip) where
  f p := ((cechComplexIntFunctor O U Ui hU).map (resolutionAug J)).f p
  comm' p p' _ := ((cechComplexIntFunctor O U Ui hU).map (resolutionAug J)).comm p p'

/-- The components of `cechBetaRow`. -/
@[simp]
lemma cechBetaRow_f (p : ℤ) :
    (cechBetaRow O U Ui hU J).f p =
      ((cechComplexIntFunctor O U Ui hU).map (resolutionAug J)).f p := rfl

/-- **The antidiagonals of the flipped Čech bicomplex are finite.** -/
lemma diagonalFinite_cechBicomplexFlip :
    DiagonalFinite ((cechBicomplex O U Ui hU J.cochainComplex).flip) := by
  intro n
  refine (Set.finite_Icc (0 : ℤ) n).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hp (isZero_cechBicomplex_X_X O U Ui hU J.cochainComplex (n - p) p (Or.inr (by omega)))
  · by_contra h
    exact hp (isZero_cechBicomplex_X_X O U Ui hU J.cochainComplex (n - p) p
      (Or.inl (J.cochainComplex.isZero_of_isStrictlyGE 0 (n - p) (by omega))))

/-- **The hypotheses of [Stacks, Tag 0133] for the flipped Čech bicomplex of an injective
resolution of an acyclic sheaf**, with the augmentation by the Čech complex of the resolved
sheaf. -/
theorem hypotheses_cechBetaRow (hac : ∀ (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj F)) :
    Hypotheses ((cechComplexIntFunctor O U Ui hU).obj F)
      ((cechBicomplex O U Ui hU J.cochainComplex).flip) (cechBetaRow O U Ui hU J) where
  diagonalFinite := diagonalFinite_cechBicomplexFlip O U Ui hU J
  zero_of_neg p q hq := isZero_cechBicomplex_X_X O U Ui hU J.cochainComplex q p
    (Or.inl (J.cochainComplex.isZero_of_isStrictlyGE 0 q (by omega)))
  exactAt_of_ne_zero p q hq := exactAt_cechBicomplexFlip_X O U Ui hU J hac p q hq
  inducesIsoKernel p := inducesIsoKernel_cechBetaRow O U Ui hU J p

/-! ### The comparison is an isomorphism -/

/-- The components of the comparison map of [Stacks, Tag 0133] for the rows, read in the total
complex of the Čech bicomplex.  The sign that flipping a total complex introduces is
`(-1)^{0 · p}`, hence trivial. -/
lemma comparisonMapP_totalFlipIso_f (hac : ∀ (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj F))
    (p : ℤ) :
    (comparisonMapP ((cechComplexIntFunctor O U Ui hU).obj F)
          ((cechBicomplex O U Ui hU J.cochainComplex).flip) (cechBetaRow O U Ui hU J)
          (hypotheses_cechBetaRow O U Ui hU J hac) ≫
        ((cechBicomplex O U Ui hU J.cochainComplex).totalFlipIso (up ℤ)).hom).f p =
      ((cechComplexIntFunctor O U Ui hU).map (resolutionAug J)).f p ≫
        (cechBicomplex O U Ui hU J.cochainComplex).ιTotal (up ℤ) 0 p p (by simp) := by
  rw [HomologicalComplex.comp_f, comparisonMapP_f, Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  simp
  rfl

/-- **The augmentation `β` of [Stacks, Tag 01EQ] is the comparison map of [Stacks, Tag 0133] for
the rows.**  Both are given in Čech degree `p` by the `p`-cochains of `F ⟶ J⁰`, landing in the
`(0, p)` corner of the total complex. -/
lemma cechBetaRes_eq (hac : ∀ (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj F)) :
    cechBetaRes O U Ui hU J =
      comparisonMapP ((cechComplexIntFunctor O U Ui hU).obj F)
          ((cechBicomplex O U Ui hU J.cochainComplex).flip) (cechBetaRow O U Ui hU J)
          (hypotheses_cechBetaRow O U Ui hU J hac) ≫
        ((cechBicomplex O U Ui hU J.cochainComplex).totalFlipIso (up ℤ)).hom :=
  HomologicalComplex.hom_ext _ _ fun p =>
    (cechBeta_f O U Ui hU J.cochainComplex (resolutionAug J) (resolutionAug_comp_d J) p).trans
      (comparisonMapP_totalFlipIso_f O U Ui hU J hac p).symm

/-- **The augmentation `β` is a quasi-isomorphism** for an acyclic covering, by [Stacks, Tag
0133]: the rows of the Čech bicomplex of the resolution are exact away from resolution degree
zero and the Čech complex of `F` is their kernel in degree zero. -/
lemma quasiIso_cechBetaRes (hac : ∀ (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj F)) :
    QuasiIso (cechBetaRes O U Ui hU J) := by
  have hq := quasiIso_comparisonMapP ((cechComplexIntFunctor O U Ui hU).obj F)
    ((cechBicomplex O U Ui hU J.cochainComplex).flip) (cechBetaRow O U Ui hU J)
    (hypotheses_cechBetaRow O U Ui hU J hac)
  rw [cechBetaRes_eq O U Ui hU J hac]
  infer_instance

/-- **The comparison at an injective resolution is an isomorphism** for an acyclic covering.  Of
its three factors `Q(β)`, `Q(α)⁻¹` and the identification of the sections of the resolution with
derived sections, the last two are isomorphisms for every covering, and the first is one here
because `β` is a quasi-isomorphism. -/
lemma isIso_cechComparison (hac : ∀ (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj F)) :
    IsIso (cechComparison O U Ui hU J) := by
  have hβ := quasiIso_cechBetaRes O U Ui hU J hac
  have hQβ : IsIso (DerivedCategory.Q.map (cechBetaRes O U Ui hU J)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hβ
  dsimp only [cechComparison]
  infer_instance

end Acyclic

/-- **The Čech-to-derived-sections transformation is an isomorphism at a sheaf of modules which
is acyclic on the intersections of the covering.** -/
lemma isIso_cechToDerivedGlobalSections_app
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} O)
    (hac : ∀ (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived m).obj F)) :
    IsIso ((cechToDerivedGlobalSections O U Ui hU).app F) := by
  refine (ObjectProperty.isIso_hom_iff _).1 ?_
  exact isIso_cechComparison O U Ui hU (InjectiveResolution.of F) hac

/-- An open covering whose nonempty finite intersections are acyclic for a module sheaf
computes the cohomology of that sheaf by its Čech complex.

This is the whole of [Stacks, Tag 01ET]: the source's equality `Ȟᵖ(𝒰, ℱ) = Hᵖ(U, ℱ)` of
`𝒪_X(U)`-modules is read here as the canonical comparison of [Stacks, Tag 01EQ] being an
isomorphism, both sides living in the derived category of `𝒪_X(U)`-modules.  `hacyclic` is the
acyclicity of `ℱ` on the intersections `U_{i₀ … i_r}`, and the two instance binders are
synthesizable for any topological space. -/
@[stacks 01ET "the comparison of Tag 01EQ is an isomorphism in every degree"]
theorem isIso_cechCohomologyToCohomology_app
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} O)
    (hacyclic : ∀ (r : ℕ) (s : Fin (r + 1) → I) (q : ℕ), 0 < q →
      IsZero (((SheafOfModules.evaluation.{u} O (op (⨅ k, Ui (s k)))).rightDerived q).obj F))
    (p : ℕ) :
    IsIso ((cechCohomologyToCohomology O U Ui hU (p : ℤ)).app F) := by
  have hτ : IsIso ((cechToDerivedGlobalSections O U Ui hU).app F) :=
    isIso_cechToDerivedGlobalSections_app O U Ui hU F hacyclic
  simp only [cechCohomologyToCohomology, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app]
  infer_instance

end Stacks.Cohomology.CechAcyclic

end
