module

public import Mathlib.Data.Finsupp.Encodable
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveSpaceHilbertQuotRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotFunctorEquality
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSitePresheafCanonicalModel
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Sites.OverLocalRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic

/-!
# The Hilbert presheaf of `ℙⁿ_U ⟶ U` has a model which is an algebraic space

Let `U` be an object of the big fppf site over `Spec ℤ`. The Quot presheaf `Quot` of
`𝒪_{ℙⁿ_U}/ℙⁿ_U/U` is the union of its subfunctors `Quot^P`, `P ∈ ℚ[t]`: over a scheme `T` a
section reads as a quotient of `𝒪_{ℙⁿ_T}` flat over `T`, and the locus `T_P` of the points of
`T` over which its Hilbert polynomial is `P` is open, the `T_P` covering `T`
(`AlgebraicGeometry.C1590Private.isOpen_fibreHilbertLocus`). So each `Quot^P ⊆ Quot` is
representable by open immersions, and the induced morphism from the coproduct of the `Quot^P` is
locally surjective. Each `Quot^P` is represented by an object of the site
(`AlgebraicGeometry.C1590Private.exists_iso_hilbertSubfunctor`), and `ℚ[t]` is countable, so the
coproduct is an algebraic space (Stacks 02WQ), and hence so is `Quot` (Stacks 02WR). By Stacks 0D00
the Hilbert presheaf of `ℙⁿ_U ⟶ U` is `Quot`, which gives the model.

## Main definitions

* `AlgebraicGeometry.C1590Private.ProjectiveSpaceHilbertModels`: for every affine `U` and every
  `n`, the Hilbert presheaf of `ℙⁿ_U ⟶ U` has a model which is an algebraic space.

## Main results

* `AlgebraicGeometry.C1590Private.isAlgebraicSpace_projectiveSpaceQuotModel`: the canonical model
  of the Quot presheaf of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U` is an algebraic space.
* `AlgebraicGeometry.C1590Private.projectiveSpaceHilbertModels`: the proposition
  `ProjectiveSpaceHilbertModels` holds for every big fppf site `B` containing `Spec ℤ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.C1590Private

open ProjectiveQuot ProjectiveQuotOverSpace

universe u

variable {B : BigFppfSite.{u}} (n : ℕ) (U : BigFppfOver B integerBase B.contains_integerBase)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The canonical model of the Quot presheaf of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U`. -/
abbrev projectiveSpaceQuotModel : Space.QuotSitePresheafModel (projectiveSpaceQuotSituation n U) :=
  (projectiveSpaceQuotSituation n U).quotSitePresheafModel

/-- The subfunctor of the model corresponding to `Quot^P`. -/
def hilbertModelSubfunctor (P : Polynomial ℚ) :
    Subfunctor (projectiveSpaceQuotModel n U).presheaf where
  obj T := {z | (projectiveSpaceQuotModel n U).iso.hom.app T ⟨z⟩ ∈
    (hilbertSubfunctor (projectiveSpaceFrame n U) P).obj T}
  map {T T'} g z hz := by
    have h := types_congr_hom ((projectiveSpaceQuotModel n U).iso.hom.naturality g) ⟨z⟩
    change (projectiveSpaceQuotModel n U).iso.hom.app T' ⟨_⟩ ∈
      (hilbertSubfunctor (projectiveSpaceFrame n U) P).obj T'
    exact h ▸ (hilbertSubfunctor (projectiveSpaceFrame n U) P).map g hz

/-- The subfunctor of the model corresponding to `Quot^P` is a model of `Quot^P`. -/
def hilbertModelSubfunctorIso (P : Polynomial ℚ) :
    (hilbertModelSubfunctor n U P).toFunctor ⋙ uliftFunctor.{u + 1} ≅
      (hilbertSubfunctor (projectiveSpaceFrame n U) P).toFunctor :=
  NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun z => ⟨(projectiveSpaceQuotModel n U).iso.hom.app T ⟨z.down.1⟩, z.down.2⟩
      invFun := fun x => ⟨⟨((projectiveSpaceQuotModel n U).iso.inv.app T x.1).down, by
        change (projectiveSpaceQuotModel n U).iso.hom.app T
          ((projectiveSpaceQuotModel n U).iso.inv.app T x.1) ∈
            (hilbertSubfunctor (projectiveSpaceFrame n U) P).obj T
        rw [Iso.inv_hom_id_app_apply]
        exact x.2⟩⟩
      left_inv := fun z => ULift.ext _ _ (Subtype.ext (congrArg ULift.down
        (Iso.hom_inv_id_app_apply (projectiveSpaceQuotModel n U).iso T ⟨z.down.1⟩)))
      right_inv := fun x => Subtype.ext
        (Iso.inv_hom_id_app_apply (projectiveSpaceQuotModel n U).iso T x.1) }) fun {T T'} g => by
    ext z
    exact Subtype.ext (types_congr_hom ((projectiveSpaceQuotModel n U).iso.hom.naturality g)
      ⟨z.down.1⟩)

/-- **The subfunctor of the model corresponding to `Quot^P` is an algebraic space**, being
represented by an object of the site. -/
theorem isAlgebraicSpace_hilbertModelSubfunctor (P : Polynomial ℚ) :
    IsAlgebraicSpace B integerBase B.contains_integerBase
      (hilbertModelSubfunctor n U P).toFunctor := by
  obtain ⟨V, ⟨e⟩⟩ := exists_iso_hilbertSubfunctor (n := n) (U := U) P
  have e' := ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1, u}).whiskeringRight
    (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ).preimageIso
      (hilbertModelSubfunctorIso n U P ≪≫ e)
  exact (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase V).of_iso e'.symm

/-- The member of `Quot_{𝒪/ℙⁿ/ℤ}(T)` a section of the model reads as. -/
abbrev modelQuotient {T : BigFppfOver B integerBase B.contains_integerBase}
    (s : (projectiveSpaceQuotModel n U).presheaf.obj (op T)) : families n 1 ((𝒯).obj T) :=
  ((quotPairsIso (n := n) (U := U)).hom.app (op T)
    ((projectiveSpaceQuotModel n U).iso.hom.app (op T) ⟨s⟩)).2

/-- **The restriction of a section lies in `Quot^P` exactly when the morphism lands in the
Hilbert-polynomial locus of `P`.** -/
theorem map_mem_hilbertModelSubfunctor_iff (P : Polynomial ℚ)
    {T T' : BigFppfOver B integerBase B.contains_integerBase} (e : T' ⟶ T)
    (s : (projectiveSpaceQuotModel n U).presheaf.obj (op T)) :
    haveI := (modelQuotient n U s).2.1
    (projectiveSpaceQuotModel n U).presheaf.map e.op s ∈
        (hilbertModelSubfunctor n U P).obj (op T') ↔
      Set.range ((𝒯).map e) ⊆ fibreHilbertLocus P (quotient (modelQuotient n U s).1) := by
  have := (modelQuotient n U s).2.1
  have h₁ := types_congr_hom ((projectiveSpaceQuotModel n U).iso.hom.naturality e.op) ⟨s⟩
  have h₂ := congrArg (fun q => q.2.1)
    (types_congr_hom ((quotPairsIso (n := n) (U := U)).hom.naturality e.op)
      ((projectiveSpaceQuotModel n U).iso.hom.app (op T) ⟨s⟩))
  have key : ((quotPairsIso (n := n) (U := U)).hom.app (op T')
      ((projectiveSpaceQuotModel n U).iso.hom.app (op T')
        ⟨(projectiveSpaceQuotModel n U).presheaf.map e.op s⟩)).2.1 =
      baseChange ((𝒯).map e) (modelQuotient n U s).1 :=
    (congrArg (fun y => ((quotPairsIso (n := n) (U := U)).hom.app (op T') y).2.1) h₁).trans h₂
  refine (mem_hilbertSubfunctor_iff_quotPairsIso P (op T') _).trans ?_
  rw [key]
  exact baseChange_mem_hilbertFamilies_iff P _ (modelQuotient n U s).2

/-- The Hilbert-polynomial locus of a section of the model, as an open of its scheme. -/
def modelLocus (P : Polynomial ℚ) {T : BigFppfOver B integerBase B.contains_integerBase}
    (s : (projectiveSpaceQuotModel n U).presheaf.obj (op T)) : ((𝒯).obj T).Opens :=
  haveI := (modelQuotient n U s).2.1
  ⟨fibreHilbertLocus P (quotient (modelQuotient n U s).1),
    isOpen_fibreHilbertLocus P (modelQuotient n U s).2⟩

/-- The inclusion of an open subobject of an object of the site is an open immersion. -/
theorem isOpenImmersion_openSubHom {T : BigFppfOver B integerBase B.contains_integerBase}
    (V : T.left.obj.Opens) :
    IsOpenImmersion ((𝒯).map (BigFppfOver.openSubHom B integerBase B.contains_integerBase T V)) :=
  inferInstanceAs (IsOpenImmersion V.ι)

/-- The inclusion of an open subobject of an object of the site is a monomorphism. -/
theorem mono_openSubHom {T : BigFppfOver B integerBase B.contains_integerBase}
    (V : T.left.obj.Opens) :
    Mono (BigFppfOver.openSubHom B integerBase B.contains_integerBase T V) :=
  (𝒯).mono_of_mono_map (inferInstanceAs (Mono V.ι))

/-- The range of the inclusion of an open subobject is the open. -/
theorem range_openSubHom {T : BigFppfOver B integerBase B.contains_integerBase}
    (V : T.left.obj.Opens) :
    Set.range ((𝒯).map (BigFppfOver.openSubHom B integerBase B.contains_integerBase T V)) =
      (V : Set T.left.obj) :=
  Scheme.Opens.range_ι V

/-- A morphism of the site factors through an open subobject exactly when it lands in it. -/
theorem exists_comp_openSubHom_iff {T T' : BigFppfOver B integerBase B.contains_integerBase}
    (V : T.left.obj.Opens) (e : T' ⟶ T) :
    (∃ l : T' ⟶ BigFppfOver.openSubObj B integerBase B.contains_integerBase T V,
      l ≫ BigFppfOver.openSubHom B integerBase B.contains_integerBase T V = e) ↔
      Set.range ((𝒯).map e) ⊆ (V : Set T.left.obj) := by
  refine ⟨?_, fun h => BigFppfOver.exists_factor_of_range_le _ (isOpenImmersion_openSubHom V) e
    ((range_openSubHom V).symm ▸ h)⟩
  rintro ⟨l, rfl⟩
  rw [← range_openSubHom V, Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact Set.range_comp_subset_range _ _

/-- **`Quot^P ⊆ Quot` is representable by open immersions.** -/
theorem isOpenImmersion_hilbertModelSubfunctor_ι (P : Polynomial ℚ) :
    Space.IsOpenImmersion B integerBase B.contains_integerBase
      (hilbertModelSubfunctor n U P).ι := by
  refine Stacks.Sites.presheaf_subfunctor_ι_of_factor _ _ fun T s => ?_
  refine ⟨BigFppfOver.openSubObj B integerBase B.contains_integerBase T (modelLocus n U P s),
    BigFppfOver.openSubHom B integerBase B.contains_integerBase T (modelLocus n U P s),
    mono_openSubHom _, isOpenImmersion_openSubHom _, fun T' e => ?_⟩
  rw [exists_comp_openSubHom_iff]
  exact map_mem_hilbertModelSubfunctor_iff n U P e s

/-- `ℚ[t]` is countable. -/
instance countable_polynomial_rat : Countable (Polynomial ℚ) :=
  haveI : Countable (ℕ →₀ ℚ) := inferInstance
  Polynomial.toFinsupp_injective.countable

/-- **The model of the Quot presheaf is a sheaf** (Stacks 09TT). -/
theorem isSheaf_projectiveSpaceQuotModel :
    Presheaf.IsSheaf (BigFppfOver.topology B integerBase B.contains_integerBase)
      (projectiveSpaceQuotModel n U).presheaf := by
  have h : Presheaf.IsSheaf (BigFppfOver.topology B integerBase B.contains_integerBase)
      ((projectiveSpaceQuotModel n U).presheaf ⋙ uliftFunctor.{u + 1}) :=
    (Presheaf.isSheaf_of_iso_iff (projectiveSpaceQuotModel n U).iso).2
      (projectiveSpaceQuotSituation n U).quotSitePresheaf_isSheaf_fppf
  rw [isSheaf_iff_isSheaf_of_type] at h ⊢
  exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 h

/-- The subfunctors `Quot^P`, as sheaves. -/
abbrev hilbertModelSheaf (P : Polynomial ℚ) :
    Sheaf (BigFppfOver.topology B integerBase B.contains_integerBase) (Type u) :=
  ⟨(hilbertModelSubfunctor n U P).toFunctor,
    (isAlgebraicSpace_hilbertModelSubfunctor n U P).isSheaf⟩

/-- The subfunctors `Quot^P`, as sheaves indexed by `ULift ℚ[t]` (a type in the universe of the
site, as the bounded coproduct of Stacks 02WQ wants). -/
abbrev hilbertModelSheaves (P : ULift.{u} (Polynomial ℚ)) :
    Sheaf (BigFppfOver.topology B integerBase B.contains_integerBase) (Type u) :=
  hilbertModelSheaf n U P.down

/-- The model of the Quot presheaf, as a sheaf. -/
abbrev projectiveSpaceQuotModelSheaf :
    Sheaf (BigFppfOver.topology B integerBase B.contains_integerBase) (Type u) :=
  ⟨(projectiveSpaceQuotModel n U).presheaf, isSheaf_projectiveSpaceQuotModel n U⟩

/-- The morphism from the coproduct of the `Quot^P` to `Quot`. -/
abbrev hilbertModelCoproductDesc :
    ∐ hilbertModelSheaves n U ⟶ projectiveSpaceQuotModelSheaf n U :=
  Sigma.desc fun P => ObjectProperty.homMk (hilbertModelSubfunctor n U P.down).ι

/-- The morphism from the coproduct of the `Quot^P` restricts on the summand `Quot^P` to the
inclusion `Quot^P ⊆ Quot`. -/
theorem ι_hilbertModelCoproductDesc (P : ULift.{u} (Polynomial ℚ)) :
    (Sigma.ι (hilbertModelSheaves n U) P).hom ≫ (hilbertModelCoproductDesc n U).hom =
      (hilbertModelSubfunctor n U P.down).ι :=
  congrArg (fun f : hilbertModelSheaves n U P ⟶ projectiveSpaceQuotModelSheaf n U => f.hom)
    (Sigma.ι_desc (fun P => (ObjectProperty.homMk (hilbertModelSubfunctor n U P.down).ι :
      hilbertModelSheaves n U P ⟶ projectiveSpaceQuotModelSheaf n U)) P)

/-- **`Quot` is covered by the `Quot^P`**: the morphism from their coproduct is locally
surjective. -/
theorem isLocallySurjective_hilbertModelCoproductDesc :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B integerBase B.contains_integerBase)
      (hilbertModelCoproductDesc n U).hom := by
  refine ⟨@fun T s => ?_⟩
  have hcov := BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B integerBase
    B.contains_integerBase
    (fun P => BigFppfOver.openSubHom B integerBase B.contains_integerBase T (modelLocus n U P s))
    (fun P => isOpenImmersion_openSubHom _) fun x => by
      have := (modelQuotient n U s).2.1
      obtain ⟨P, hP⟩ := exists_mem_fibreHilbertLocus (quotient (modelQuotient n U s).1) x
      exact ⟨P, by rwa [range_openSubHom]⟩
  refine (BigFppfOver.topology B integerBase B.contains_integerBase).superset_covering ?_ hcov
  rintro Y f ⟨Z, a, g', ⟨P⟩, rfl⟩
  refine (Presheaf.imageSieve (hilbertModelCoproductDesc n U).hom s).downward_closed ?_ a
  have hmem := (map_mem_hilbertModelSubfunctor_iff n U P
    (BigFppfOver.openSubHom B integerBase B.contains_integerBase T (modelLocus n U P s)) s).2
    ((exists_comp_openSubHom_iff _ _).1 ⟨𝟙 _, Category.id_comp _⟩)
  exact ⟨(Sigma.ι (hilbertModelSheaves n U) ⟨P⟩).hom.app _ ⟨_, hmem⟩,
    types_congr_hom (congrArg (fun φ => NatTrans.app φ _) (ι_hilbertModelCoproductDesc n U ⟨P⟩)) _⟩

/-- **The model of the Quot presheaf of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U` is an algebraic space** (Stacks 02WQ and
02WR). -/
theorem isAlgebraicSpace_projectiveSpaceQuotModel :
    IsAlgebraicSpace B integerBase B.contains_integerBase
      (projectiveSpaceQuotModel n U).presheaf := by
  choose A a hsurj hetale using fun P : ULift.{u} (Polynomial ℚ) =>
    (isAlgebraicSpace_hilbertModelSubfunctor n U P.down).exists_atlas
  have hG : IsAlgebraicSpace B integerBase B.contains_integerBase (∐ hilbertModelSheaves n U).obj :=
    isAlgebraicSpace_coproduct B integerBase B.contains_integerBase
      (fun P : ULift.{u} (Polynomial ℚ) => (hilbertModelSubfunctor n U P.down).toFunctor)
      (fun P => isAlgebraicSpace_hilbertModelSubfunctor n U P.down) _
      (Sigma.ι (hilbertModelSheaves n U))
      (coproductIsCoproduct _) A a hsurj hetale (∐ A) (Sigma.ι A) (coproductIsCoproduct A)
  refine isAlgebraicSpace_of_open_cover B integerBase B.contains_integerBase _
    (isSheaf_projectiveSpaceQuotModel n U) (ULift.{u} (Polynomial ℚ)) (hilbertModelSheaves n U)
    (fun P => isAlgebraicSpace_hilbertModelSubfunctor n U P.down) _
    (Sigma.ι (hilbertModelSheaves n U))
    (coproductIsCoproduct _) (hilbertModelCoproductDesc n U).hom (fun P => ?_)
    (isLocallySurjective_hilbertModelCoproductDesc n U) hG
  rw [ι_hilbertModelCoproductDesc]
  exact isOpenImmersion_hilbertModelSubfunctor_ι n U P.down

/-- **The Hilbert presheaf of `ℙⁿ_U ⟶ U` has a model which is an algebraic space.** The model is
the canonical model of the Quot presheaf of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U`, identified with the Hilbert
presheaf by Stacks 0D00. -/
def projectiveSpaceHilbertModel : Space.HilbertPresheafModel (projectiveSpaceMap n U) where
  presheaf := (projectiveSpaceQuotModel n U).presheaf
  iso := (projectiveSpaceQuotModel n U).iso ≪≫
    (Space.hilbertPresheafIsoQuotSitePresheaf (projectiveSpaceMap n U)
      (isFinitePresentation_projectiveSpaceMap n U)).symm

/-- The model `projectiveSpaceHilbertModel` of the Hilbert presheaf of `ℙⁿ_U ⟶ U` is an
algebraic space. -/
theorem isAlgebraicSpace_projectiveSpaceHilbertModel :
    IsAlgebraicSpace B integerBase B.contains_integerBase
      (projectiveSpaceHilbertModel n U).presheaf :=
  isAlgebraicSpace_projectiveSpaceQuotModel n U

variable (B) in
/-- **Hilbert models of projective spaces.** For every object `U` of the big fppf site over
`Spec ℤ` and every `n`, the Hilbert presheaf of `ℙⁿ_U ⟶ U` (Stacks 0CZY) has a model in the
universe of the site which is an algebraic space. (Route: 0D00 `Hilb = Quot_{𝒪}`, the decomposition
into the open and closed `Quot^P`, and site-level `Quot^P_{𝒪/U × ℙⁿ/U}` from base's scheme-level
`ProjectiveQuot.exists_isProper_iso_hilbertFunctor`.) The source of the statement only needs it
for affine `U`. -/
def ProjectiveSpaceHilbertModels (hZ : B.Contains integerBase) : Prop :=
  ∀ (U : BigFppfOver B integerBase hZ),
    IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) →
    ∀ n : ℕ, ∃ M : Space.HilbertPresheafModel
        (schemeSpaceMap (ProjectiveQuot.projectiveSiteStructure B n U)),
      IsAlgebraicSpace B integerBase hZ M.presheaf

variable (B) in
/-- **The Hilbert presheaf of `ℙⁿ_U ⟶ U` has an algebraic model, for every `U` and `n`.** -/
theorem projectiveSpaceHilbertModels (hZ : B.Contains integerBase) :
    ProjectiveSpaceHilbertModels B hZ := fun U _ n =>
  ⟨projectiveSpaceHilbertModel n U, isAlgebraicSpace_projectiveSpaceHilbertModel n U⟩

end AlgebraicGeometry.C1590Private

end
