module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Category.TopCat.GrothendieckTopology
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Defs.Induced
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Zariski site of locally quasi-compact spaces and its comparison morphisms

Section 21.31 of the Stacks project equips the bounded category `LC_α` of Hausdorff, locally
quasi-compact spaces with two topologies: the quasi-compact one of
`Stacks.Topology.LocallyQuasiCompactQcSite`, and the *Zariski* one, whose coverings are the
families of open embeddings whose images cover the target. Both live on the same category, and
`Stacks.Topology.LocallyQuasiCompactZariskiSituation` packages that common choice.

The point of the Zariski topology is that each object `X` of `LC_Zar` has a *small* Zariski site
`X_Zar` of its own open subsets, and the two are compared: sending an open `U ⊆ X` to the open
immersion `U → X`, viewed as an object of the slice `LC_Zar/X`, is a continuous functor
`opensToSlice`, and so induces a morphism of topoi

`Sh(LC_Zar/X) → Sh(X_Zar)`.

Continuity is proved here by checking that `opensToSlice` is cover-preserving and representably
flat: cover-preserving because an open covering of `U` in `X_Zar` is literally a Zariski
covering of `U → X` in the slice; representably flat because any two opens `U, V` containing the
image of a map `Z → X` are refined by `U ⊓ V`, which still contains it, so the comma categories
are cofiltered. Flatness also makes the inverse image left exact, i.e. the comparison is a
genuine morphism of topoi, and the same computation on abelian sheaves gives
`abelianComparisonInverseImage_exact`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation`: the common category and quasi-compact
  site, from which the Zariski topology is built.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiTopology`: the Zariski topology.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice`: the open-subset functor
  `Opens X ⥤ LC_Zar/X`, together with the characterisation of its values as the open embeddings
  with the prescribed images.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonDirectImage`,
  `comparisonInverseImage`, `comparisonAdjunction`: the comparison morphism of topoi on sheaves
  of sets, and `abelianComparisonInverseImage`, `abelianComparisonAdjunction` on abelian
  sheaves.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiObjectCohomology`: cohomology over
  an object of the localized Zariski site.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_disjoint_isOpen_of_ne`: distinct
  points of a subset of a space of the site have disjoint open neighbourhoods in that space.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.essentiallySmall_over` and
  `hasSheafify_zariskiTopology_over`: the localized Zariski site is essentially small already in
  the universe of the spaces, so presheaves of types on it can be sheafified for coefficients in
  any universe containing that one.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice_isContinuous`: the
  open-subset functor is continuous, which is what produces the comparison morphism.
* `LocallyQuasiCompactZariskiSituation.comparisonInverseImage_preservesFiniteLimits` and
  `abelianComparisonInverseImage_exact`: the comparison inverse image is left exact, so the
  comparison really is a morphism of topoi.

## Implementation notes

The Zariski topology is pulled back from the open-embedding precoverage on `TopCat` along the
inclusion of the bounded subcategory, rather than defined from scratch; this is what makes
`opensToSlice_coverPreserving` a statement about open embeddings of topological spaces.

`opensToSlice` is returned as a subtype: the functor together with the property that pins down
its values. The property is what every later argument uses — commutativity in the slice category
then determines the action on morphisms, so nothing more about the construction is needed
downstream.

The coefficient universe of the topos adjunction on sheaves of sets is `max u t` with `t`
arbitrary: the only constraint is that it contain the universe `u` of the *spaces*, not the
universe `u + 1` of the objects of the site, because the site is essentially `u`-small
(`essentiallySmall_over`) and so its sheafification and Kan-extension side conditions are
`u`-small. In particular the case `t = u` is available, which is the universe at which sheaves
of sets on the underlying topological spaces — hence `TopCat.Presheaf.stalk` and the germ model
of an inverse image — live.

The coefficient universe for the abelian-sheaf adjunction is still of the form `max (u + 1) v`;
the smallness side conditions there are supplied explicitly rather than found by instance
search.

`lanCompEvaluationIsoColim` and `lan_preservesFiniteLimits_of_flat` are the universe-general
forms of `CategoryTheory.lanEvaluationIsoColim` and
`CategoryTheory.Functor.lan_preservesFiniteLimits_of_flat` of
`Mathlib/CategoryTheory/Functor/Flat.lean`. Mathlib's versions require the source and target to
be small and the value category to have morphisms in the universe of its objects; here the
category of opens of a space and the slice of `LC_α` have their objects and morphisms in
different universes, so the restriction has to go. The proofs are unchanged; generalizing the
universes upstream would delete both.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 09X2](https://stacks.math.columbia.edu/tag/09X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology

universe u w v a b t

/-- Evaluating the left Kan extension functor at an object of the target is, naturally in the
functor being extended, the colimit over the costructured-arrow category above that object.

This is `CategoryTheory.lanEvaluationIsoColim` with its restriction to small source and target
and to a value category whose morphisms live in the universe of its objects removed. -/
noncomputable def lanCompEvaluationIsoColim.{s₁, s₂, s₃, x₁, x₂, x₃}
    {A : Type x₁} [Category.{s₁} A] {D : Type x₂} [Category.{s₂} D]
    (E : Type x₃) [Category.{s₃} E] (F : A ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents
    (fun G => F.leftKanExtensionObjIsoColimit G X)
    (fun {G₁ G₂} φ => by
      apply (F.isPointwiseLeftKanExtensionLeftKanExtensionUnit G₁ X).hom_ext
      intro T
      simp [Functor.lan])

/-- A representably flat functor has a left exact left Kan extension on presheaves. This is
`CategoryTheory.Functor.lan_preservesFiniteLimits_of_flat` with the smallness restrictions on
the source and target replaced by hypotheses, so that it applies to sites whose objects and
morphisms live in different universes. -/
@[sga "4 I 5.2" "special case", sga "4 I 5.4" "more general", sga "4 I 5.8.3" "special case"]
theorem lan_preservesFiniteLimits_of_flat
    {C D E : Type*} [Category* C] [Category* D] [Category.{t} E]
    {FE : E → E → Type*} {CE : E → Type t}
    [∀ X Y, FunLike (FE X Y) (CE X) (CE Y)] [ConcreteCategory.{t} E FE]
    [HasLimits E] [HasColimits E] [ReflectsLimits (forget E)]
    [PreservesLimits (forget E)]
    (F : C ⥤ D)
    (hPres : ∀ X : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow F.op X) (forget E))
    [RepresentablyFlat F]
    [∀ X : Dᵒᵖ, Small.{t} (CostructuredArrow F.op X)]
    [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow F.op X) E] :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ (Dᵒᵖ ⥤ E)) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro X
  have hfiltered : IsFiltered (CostructuredArrow F.op X) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (Opposite.unop X))
  let := hfiltered
  let : PreservesColimitsOfShape (CostructuredArrow F.op X) (forget E) := hPres X
  have : PreservesLimitsOfShape J (colim : ((CostructuredArrow F.op X) ⥤ E) ⥤ E) :=
    inferInstance
  have : PreservesLimitsOfShape J
      ((Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F.op X) ⋙ colim) :=
    inferInstance
  exact preservesLimitsOfShape_of_natIso (lanCompEvaluationIsoColim E F.op X).symm

/-- The common category of the quasi-compact and the Zariski site of Hausdorff, locally
quasi-compact spaces: a choice of quasi-compact site in the sense of Stacks 09X2, from which
the Zariski topology on the same category is built. -/
structure LocallyQuasiCompactZariskiSituation
    (initialObjects : Set LocallyQuasiCompactHausdorff.{u})
    (bound : Cardinal.{u} → Cardinal.{u}) where
  /-- The chosen quasi-compact site, whose underlying bounded subcategory carries the Zariski
  topology as well. -/
  qcSite : LocallyQuasiCompactQcSite.{u, w} initialObjects bound

namespace LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}}
  {Bound : Cardinal.{u} → Cardinal.{u}}

/-- An open subset of an object of the site, as an object of `LC`: an open subspace of a
Hausdorff, locally quasi-compact space is again Hausdorff and locally quasi-compact. -/
noncomputable def openLocallyQuasiCompactHausdorff
    (X : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (Y : X.qcSite.category) (U : Opens Y.obj) : LocallyQuasiCompactHausdorff.{u} :=
  ⟨TopCat.of U, inferInstance, U.2.locallyCompactSpace⟩

/-- An open subspace has at most as many points as the whole space, so it stays below the size
cutoff of the bounded subcategory. -/
theorem openLocallyQuasiCompactHausdorff_size_le
    (X : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (Y : X.qcSite.category) (U : Opens Y.obj) :
    lcSize (openLocallyQuasiCompactHausdorff X Y U) ≤ lcSize Y.obj := by
  dsimp [openLocallyQuasiCompactHausdorff, lcSize]
  exact Cardinal.mk_subtype_le _

/-- The shared underlying category of the quasi-compact and the Zariski site. -/
abbrev category (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) :=
  S.qcSite.category

/-- The precoverage of Zariski coverings: families of open embeddings which are jointly
surjective, pulled back from `TopCat`. -/
def zariskiPrecoverage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) : Precoverage S.category :=
  TopCat.precoverage.comap (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop)

/-- The Zariski Grothendieck topology, on the same category as the quasi-compact site. -/
@[stacks 09WY "the topology of the site LC_Zar"]
def zariskiTopology
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) :
    GrothendieckTopology S.category :=
  S.zariskiPrecoverage.toGrothendieck

/-- The Zariski topology is coarser than the quasi-compact topology: a covering by open
embeddings whose images cover the target is a quasi-compact covering, because every point of a
locally compact space has a compact neighbourhood inside the member of the covering it lies in.

This is the comparison `Cov' ⊆ Cov` for the two topologies of the situation, which is what makes
the change-of-topology morphism `ε_X : Sh(LC_qc/X) → Sh(LC_Zar/X)` available: `ε_{X,*}` is
restriction of a quasi-compact sheaf along this inequality and `ε_X^{-1}` is quasi-compact
sheafification. -/
theorem zariskiTopology_le_qc
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) :
    S.zariskiTopology ≤ S.qcSite.grothendieckTopology := by
  classical
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
  intro T R hR
  let E := R.preZeroHypercover
  have hE : E.presieve₀ ∈ S.zariskiPrecoverage T := by simpa [E] using hR
  change _ ∧ _ at hE
  have hsurj : ∀ x : T.obj, ∃ i, x ∈ Set.range (E.f i : (E.X i).obj → T.obj) := by
    simpa [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      PreZeroHypercover.presieve₀] using! hE.1
  have hopen : ∀ i, Topology.IsOpenEmbedding (E.f i : (E.X i).obj → T.obj) := by
    simpa [Presieve.map_ofArrows, PreZeroHypercover.presieve₀,
      TopCat.isOpenEmbedding] using! hE.2
  have hqc : S.qcSite.IsQcCovering E := by
    intro x
    obtain ⟨i, y, rfl⟩ := hsurj x
    have _ : LocallyCompactSpace (E.X i).obj :=
      inferInstanceAs (LocallyCompactSpace (E.X i).obj.obj)
    obtain ⟨K, hK, hy⟩ := exists_compact_mem_nhds y
    refine ⟨{i}, fun j => if h : j = i then h ▸ K else ∅, ?_, ?_⟩
    · intro j hj
      have : j = i := Finset.mem_singleton.mp hj
      subst j
      simpa using hK
    · simpa using (hopen i).image_mem_nhds.mpr hy
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  exact (S.qcSite.pretopology.mem_toGrothendieck T _).mpr
    ⟨R, by
      simpa [LocallyQuasiCompactQcSite.IsCovering, E] using
        (S.qcSite.isCovering_iff_isQcCovering E).mpr hqc,
      Sieve.le_generate R⟩

/-- The comparison of the two topologies on a slice: a sieve covering for the localized Zariski
topology is covering for the localized quasi-compact topology, since both localizations test the
same sieve on the underlying object. -/
theorem zariskiTopology_over_le_qc
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    S.zariskiTopology.over X ≤ S.qcSite.grothendieckTopology.over X :=
  fun U _ hU => S.zariskiTopology_le_qc U.left hU

/-- Every space of the site is Hausdorff, so any two distinct points of any subset of it have
disjoint open neighbourhoods *in the ambient space*. This is the separation hypothesis of
Stacks 09V3 — it is therefore automatic in this situation. -/
theorem exists_disjoint_isOpen_of_ne
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (Z : Set X.obj) :
    ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X.obj, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B := by
  have _ : T2Space X.obj := X.obj.property.1
  intro x _ y _ hxy
  exact t2_separation hxy

/-- Cohomology of an abelian sheaf on the localized Zariski site `LC_Zar/X`, over an object `U`
over `X`. -/
@[stacks 09WY "the cohomology H^n_Zar(U, H) over an object U of LC_Zar/X"]
abbrev zariskiObjectCohomology
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (F : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})
    (U : Over X) (n : ℕ)
    [HasSheafify ((S.zariskiTopology.over X).over U) AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{a} (Sheaf ((S.zariskiTopology.over X).over U)
      AddCommGrpCat.{max (u + 1) v})] : Type a :=
  Sheaf.H (F.over U) n

/-- The open subsets of `X`, as objects over `X`: the functor `Opens X ⥤ LC_Zar/X` sending an
open `U` to the open immersion `U → X`. The accompanying property fixes the underlying map of
`U` as the open embedding with image exactly `U`, which determines the functor up to the unique
isomorphism over `X`. -/
@[stacks 09WY "the functor X_Zar → LC_Zar/X, U ↦ U"]
noncomputable def opensToSlice
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    {F : Opens X.obj ⥤ Over X // ∀ U : Opens X.obj,
      Topology.IsOpenEmbedding ((F.obj U).hom : ((F.obj U).left).obj → X.obj) ∧
      Set.range ((F.obj U).hom : ((F.obj U).left).obj → X.obj) = U.1} := by
  classical
  let G : Opens X.obj ⥤ S.category :=
    { obj := fun U => ⟨openLocallyQuasiCompactHausdorff S X U,
        (openLocallyQuasiCompactHausdorff_size_le S X U).trans_lt X.property⟩
      map := fun {U V} f => ⟨⟨(Opens.toTopCat (TopCat.of X.obj)).map f⟩⟩
      map_id := by intro U; ext x; rfl
      map_comp := by intro U V W f g; ext x; rfl }
  let i : G ⟶ (Functor.const _).obj X :=
    { app U := ⟨⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩⟩⟩
      naturality := by intro U V f; ext x; rfl }
  refine ⟨?_, ?_⟩
  · exact
      { obj := fun U => Over.mk (i.app U)
        map := fun f => Over.homMk (G.map f)
        map_id := by intro U; ext x; rfl
        map_comp := by intro U V W f g; ext x; rfl }
  · intro U
    refine ⟨U.2.isOpenEmbedding_subtypeVal, ?_⟩
    change Set.range (fun x : U => (x : X.obj)) = (U : Set X.obj)
    exact Subtype.range_val

/-- The open-subset functor is cover-preserving: an open covering of `U` in the small Zariski
site of `X` is, arrow by arrow, a Zariski covering of `U → X` in the localized Zariski site. -/
private theorem opensToSlice_coverPreserving
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    CoverPreserving (Opens.grothendieckTopology X.obj) (S.zariskiTopology.over X)
      (S.opensToSlice X).1 := by
  classical
  let G := (S.opensToSlice X).1
  let E := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  constructor
  intro U R hR
  rw [GrothendieckTopology.mem_over_iff]
  rw [Opens.mem_grothendieckTopology] at hR
  have hR' : ∀ x : U, ∃ (V : Opens X.obj) (f : V ⟶ U), R f ∧ x.1 ∈ V := by
    intro x
    obtain ⟨V, f, hf, hx⟩ := hR x x.2
    exact ⟨V, f, hf, by simpa using hx⟩
  let ι := {p : Σ V : Opens X.obj, V ⟶ U // R p.2}
  let V : ι → Opens X.obj := fun i => i.1.1
  let f : ∀ i, V i ⟶ U := fun i => i.1.2
  let T : Presieve (G.obj U).left := Presieve.ofArrows (fun i => (G.obj (V i)).left)
    (fun i => (G.map (f i)).left)
  have hmem : ∀ i, R (f i) := fun i => i.2
  have hT : T ∈ S.zariskiPrecoverage (G.obj U).left := by
    show T ∈ (TopCat.precoverage.comap E) ((G.obj U).left)
    rw [Precoverage.mem_comap_iff]
    simp only [T, Presieve.map_ofArrows]
    show _ ∧ _
    constructor
    · rw [Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
      intro y
      change ↥U at y
      have hy : (y : X.obj) ∈ U := y.2
      obtain ⟨W, g, hg, hw⟩ := hR' ⟨y, hy⟩
      refine ⟨⟨⟨W, g⟩, hg⟩, ?_⟩
      show y ∈ Set.range (E.map ((G.map (f ⟨⟨W, g⟩, hg⟩)).left))
      exact ⟨⟨(y : X.obj), hw⟩, rfl⟩
    · rw [MorphismProperty.ofArrows_mem_precoverage]
      intro i
      have hcomp : E.map ((G.map (f i)).left) ≫ E.map ((G.obj U).hom) =
          E.map ((G.obj (V i)).hom) :=
        congrArg E.map (Over.w (G.map (f i)))
      have hemb (W : Opens X.obj) : Topology.IsOpenEmbedding
          (E.map (G.obj W).hom : E.obj (G.obj W).left → X.obj) := by
        change Topology.IsOpenEmbedding ((G.obj W).hom : _ → _)
        exact ((S.opensToSlice X).2 W).1
      apply Topology.IsOpenEmbedding.of_comp _ (hemb U)
      have hcomp' := congrArg
        (fun k : E.obj ((G.obj (V i)).left) ⟶ E.obj X =>
          (k : E.obj ((G.obj (V i)).left) → E.obj X)) hcomp
      simp only [hom_comp] at hcomp'
      rw [hcomp']
      exact hemb (V i)
  have hle : Sieve.generate T ≤ Sieve.overEquiv (G.obj U) (R.functorPushforward G) := by
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    show Presieve.functorPushforward (Over.forget X)
      (R.functorPushforward G).arrows ((G.map (f i)).left)
    refine ⟨G.obj (V i), G.map (f i), 𝟙 _, ?_, by simp⟩
    exact Sieve.image_mem_functorPushforward G R (hmem i)
  have hGen : S.zariskiTopology ((G.obj U).left) (Sieve.generate T) :=
    S.zariskiPrecoverage.generate_mem_toGrothendieck hT
  exact S.zariskiTopology.superset_covering hle hGen

/-- A map `Z → X` whose image lands in an open `U` factors through `U → X`: the lift is the map
to the open subspace, which exists because the inclusion of `LC_α` into `TopCat` is fully
faithful. -/
private theorem opensToSlice_exists_lift
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (Z : Over X) (U : Opens X.obj) (hU : ∀ z : Z.left.obj, (Z.hom z) ∈ U) :
    ∃ l : Z.left ⟶ ((S.opensToSlice X).1.obj U).left,
      l ≫ ((S.opensToSlice X).1.obj U).hom = Z.hom := by
  let G := (S.opensToSlice X).1
  let E := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let hInc : S.qcSite.inclusion.FullyFaithful := by
    change (ObjectProperty.ι _).FullyFaithful
    exact ObjectProperty.fullyFaithfulι _
  let hTop : locallyQuasiCompactHausdorffToTop.FullyFaithful := by
    change (ObjectProperty.ι _).FullyFaithful
    exact ObjectProperty.fullyFaithfulι _
  let : E.FullyFaithful := hInc.comp hTop
  let q : E.obj Z.left ⟶ E.obj (G.obj U).left := by
    dsimp [E, G, openLocallyQuasiCompactHausdorff,
      LocallyQuasiCompactQcSite.inclusion, locallyQuasiCompactHausdorffToTop]
    exact TopCat.ofHom
      { toFun := fun z => ⟨Z.hom z, hU z⟩
        continuous_toFun := Continuous.subtype_mk
          (ConcreteCategory.hom (E.map Z.hom)).continuous hU }
  refine ⟨E.preimage q, E.map_injective ?_⟩
  rw [Functor.map_comp, Functor.map_preimage]
  apply TopCat.Hom.ext
  rfl

/-- The lift of `Z → X` through an open `U` containing its image. -/
private noncomputable def opensToSlice_lift
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (Z : Over X) (U : Opens X.obj)
    (hU : ∀ z : Z.left.obj, (Z.hom z) ∈ U) :
    Z.left ⟶ ((S.opensToSlice X).1.obj U).left :=
  (opensToSlice_exists_lift S X Z U hU).choose

/-- The lift of `Z → X` through an open `U` containing its image is a map over `X`. -/
private theorem opensToSlice_lift_commutes
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (Z : Over X) (U : Opens X.obj) (hU : ∀ z : Z.left.obj, (Z.hom z) ∈ U) :
    opensToSlice_lift S X Z U hU ≫ ((S.opensToSlice X).1.obj U).hom = Z.hom :=
  (opensToSlice_exists_lift S X Z U hU).choose_spec

/-- The open-subset functor is representably flat: the opens through which a given map `Z → X`
factors are closed under intersection, and `⊤` is one of them, so the comma category of such
factorizations is cofiltered.

Consequently the costructured-arrow categories `CostructuredArrow (S.opensToSlice X).1.op Z`
indexing the left Kan extension along `opensToSlice.op` are *filtered*, which is what lets a
functor preserving filtered colimits — such as `forget AddCommGrpCat` — be commuted past the
comparison inverse image. This statement is public for that use. -/
theorem opensToSlice_representablyFlat
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    RepresentablyFlat (S.opensToSlice X).1 := by
  let G := (S.opensToSlice X).1
  constructor
  intro Z
  refine { cone_objs := ?_, cone_maps := ?_, nonempty := ?_ }
  · intro A B
    let W : Opens X.obj := A.right ⊓ B.right
    have hmem (C : StructuredArrow Z G) (z : Z.left.obj) : Z.hom z ∈ C.right :=
      (Set.ext_iff.mp ((S.opensToSlice X).2 C.right).2 (Z.hom z)).mp
        ⟨C.hom.left z, ConcreteCategory.congr_hom (Over.w C.hom) z⟩
    have hW (z : Z.left.obj) : Z.hom z ∈ W := ⟨hmem A z, hmem B z⟩
    let h : Z ⟶ G.obj W := Over.homMk (opensToSlice_lift S X Z W hW)
      (opensToSlice_lift_commutes S X Z W hW)
    have hfac (C : StructuredArrow Z G) (hC : W ≤ C.right) :
        h ≫ G.map (homOfLE hC) = C.hom := by
      have : Mono (G.obj C.right).hom :=
        ConcreteCategory.mono_of_injective _ ((S.opensToSlice X).2 C.right).1.injective
      apply Over.OverMorphism.ext
      apply (cancel_mono (G.obj C.right).hom).1
      calc
        (h ≫ G.map (homOfLE hC)).left ≫ (G.obj C.right).hom = h.left ≫ (G.obj W).hom := by
          simp [Category.assoc, Over.w]
        _ = Z.hom := opensToSlice_lift_commutes S X Z W hW
        _ = C.hom.left ≫ (G.obj C.right).hom := (Over.w C.hom).symm
    exact ⟨StructuredArrow.mk h, StructuredArrow.homMk (homOfLE inf_le_left) (hfac A inf_le_left),
      StructuredArrow.homMk (homOfLE inf_le_right) (hfac B inf_le_right), trivial⟩
  · intro A B f g
    refine ⟨A, 𝟙 _, ?_⟩
    simp only [Category.id_comp]
    exact StructuredArrow.hom_ext f g (Subsingleton.elim _ _)
  · exact ⟨StructuredArrow.mk (Y := ⊤) (Over.homMk
      (opensToSlice_lift S X Z ⊤ (fun _ => by trivial))
      (opensToSlice_lift_commutes S X Z ⊤ (fun _ => by trivial)))⟩

/-- The open-subset functor is continuous from the small Zariski site of `X` to the localized
Zariski site of `LC`, so it induces the comparison morphism of topoi. -/
@[stacks 09WY "the functor X_Zar → LC_Zar/X is continuous"]
theorem opensToSlice_isContinuous
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (S.opensToSlice X).1.IsContinuous (Opens.grothendieckTopology X.obj)
      (S.zariskiTopology.over X) := by
  let : RepresentablyFlat (S.opensToSlice X).1 := opensToSlice_representablyFlat S X
  exact (Functor.isContinuous_iff_coverPreserving
    (F := (S.opensToSlice X).1) (J := Opens.grothendieckTopology X.obj)
    (K := S.zariskiTopology.over X)).2
    (opensToSlice_coverPreserving S X)

/-- Direct image for the comparison morphism `Sh(LC_Zar/X) → Sh(X_Zar)`. -/
noncomputable def comparisonDirectImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (A : Type a) [Category.{b} A] :
    Sheaf (S.zariskiTopology.over X) A ⥤ Sheaf (Opens.grothendieckTopology X.obj) A :=
  letI := S.opensToSlice_isContinuous X
  (S.opensToSlice X).1.sheafPushforwardContinuous A
    (Opens.grothendieckTopology X.obj) (S.zariskiTopology.over X)

/-- The slice of the site over an object is essentially small already in the universe `u` of the
spaces, because the bounded subcategory `LC_α` is: a slice of an essentially `u`-small category
with `u`-small hom-types is essentially `u`-small. A fortiori it is essentially small in any
universe containing `u`. -/
theorem essentiallySmall_over
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    EssentiallySmall.{max u t} (Over X) := by
  have h1 : EssentiallySmall.{u} S.category :=
    S.qcSite.boundedSubcategory.category_essentiallySmall
  have h2 : EssentiallySmall.{u} (Over X) :=
    inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (Functor.id S.category) X))
  rw [essentiallySmall_iff] at h2 ⊢
  exact ⟨small_lift.{u + 1, t, u} _ (hα := h2.1), inferInstance⟩

/-- Presheaves of types on the localized Zariski site can be sheafified, for coefficients in any
universe containing the universe `u` of the spaces, because the site is essentially `u`-small
(`essentiallySmall_over`). In particular this holds for coefficients in `Type u` itself, which
is the universe in which sheaves of sets on the underlying topological spaces live. -/
theorem hasSheafify_zariskiTopology_over
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    HasSheafify (S.zariskiTopology.over X) (Type (max u t)) :=
  have := essentiallySmall_over.{u, w, t} S X
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max u t} _ _

/-- The shapes indexing the left Kan extension along `opensToSlice` are small in the universe of
the spaces: an object of `CostructuredArrow (opensToSlice X)ᵒᵖ Y` is an open subset of `X`
together with a morphism, and both live in `Type u`. -/
theorem small_costructuredArrow_opensToSlice
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (Y : (Over X)ᵒᵖ) :
    Small.{max u t} (CostructuredArrow (S.opensToSlice X).1.op Y) :=
  small_lift.{u, t, u} _

/-- The direct image has the inverse-image left adjoint of the comparison morphism, for
coefficients in any universe containing the universe of the spaces. -/
theorem comparisonDirectImage_isRightAdjoint
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (S.comparisonDirectImage X (Type (max u t))).IsRightAdjoint := by
  let G := (S.opensToSlice X).1
  let A := Type (max u t)
  let _ : G.IsContinuous (Opens.grothendieckTopology X.obj) (S.zariskiTopology.over X) :=
    S.opensToSlice_isContinuous X
  let _ : HasSheafify (S.zariskiTopology.over X) A :=
    hasSheafify_zariskiTopology_over.{u, w, t} S X
  let _ : ∀ Y : (Over X)ᵒᵖ, Small.{max u t} (CostructuredArrow G.op Y) :=
    small_costructuredArrow_opensToSlice.{u, w, t} S X
  let _ : ∀ Y : (Over X)ᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op Y) A :=
    fun _ => inferInstance
  dsimp [comparisonDirectImage]
  infer_instance

/-- Inverse image for the comparison morphism `Sh(LC_Zar/X) → Sh(X_Zar)`, for coefficients in
any universe containing the universe of the spaces. -/
noncomputable def comparisonInverseImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t)) ⥤
      Sheaf (S.zariskiTopology.over X) (Type (max u t)) :=
  let : (S.comparisonDirectImage X (Type (max u t))).IsRightAdjoint :=
    comparisonDirectImage_isRightAdjoint.{u, w, t} S X
  (S.comparisonDirectImage X (Type (max u t))).leftAdjoint

/-- The comparison adjunction on sheaves of sets, for coefficients in any universe containing
the universe of the spaces. -/
noncomputable def comparisonAdjunction
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    comparisonInverseImage.{u, w, t} S X ⊣ S.comparisonDirectImage X (Type (max u t)) :=
  let : (S.comparisonDirectImage X (Type (max u t))).IsRightAdjoint :=
    comparisonDirectImage_isRightAdjoint.{u, w, t} S X
  Adjunction.ofIsRightAdjoint _

/-- The comparison adjunction is a morphism of topoi: its inverse image is left exact. -/
theorem comparisonInverseImage_preservesFiniteLimits
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    PreservesFiniteLimits (comparisonInverseImage.{u, w, t} S X :
      Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t)) ⥤
        Sheaf (S.zariskiTopology.over X) (Type (max u t))) := by
  let G := (S.opensToSlice X).1
  let J := Opens.grothendieckTopology X.obj
  let K := S.zariskiTopology.over X
  let A := Type (max u t)
  let : RepresentablyFlat G := opensToSlice_representablyFlat S X
  let : G.IsContinuous J K := S.opensToSlice_isContinuous X
  let : (G.sheafPushforwardContinuous A J K).IsRightAdjoint := by
    dsimp [G, A, J, K, comparisonDirectImage]
    exact comparisonDirectImage_isRightAdjoint.{u, w, t} S X
  let : HasSheafify J A := inferInstance
  let : HasSheafify K A := hasSheafify_zariskiTopology_over.{u, w, t} S X
  dsimp [comparisonInverseImage, comparisonDirectImage, G, J, K, A]
  let : ∀ Y : (Over X)ᵒᵖ, Small.{max u t} (CostructuredArrow G.op Y) :=
    small_costructuredArrow_opensToSlice.{u, w, t} S X
  let : ∀ Y : (Over X)ᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op Y) A :=
    fun _ => inferInstance
  let : PreservesFiniteLimits (G.op.lan : ((Opens X.obj)ᵒᵖ ⥤ A) ⥤ ((Over X)ᵒᵖ ⥤ A)) :=
    lan_preservesFiniteLimits_of_flat (F := G) (hPres := by
      intro Y
      infer_instance)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- The direct image on abelian sheaves has its inverse-image left adjoint, for coefficients in
any universe containing the universe `u` of the spaces.

The slice of the site is essentially `u`-small (`essentiallySmall_over`), so sheafification for
the localized Zariski topology is available already at coefficients `AddCommGrpCat.{u}`; the
comma categories indexing the left Kan extension along the open-subset functor are `u`-small by
`small_costructuredArrow_opensToSlice`, and abelian groups have colimits of those shapes. No
step of this needs the coefficients to contain the universe `u + 1` of the *objects* of the
site, even though the covering sieves of the slice do live there. -/
theorem abelianComparisonDirectImage_isRightAdjoint_ofSize
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (S.comparisonDirectImage X AddCommGrpCat.{max u t}).IsRightAdjoint := by
  let := S.opensToSlice_isContinuous X
  let : HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max u t} :=
    have := essentiallySmall_over.{u, w, t} S X
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u t} _ _
  let : ∀ Y : (Over X)ᵒᵖ, Small.{max u t} (CostructuredArrow (S.opensToSlice X).1.op Y) :=
    small_costructuredArrow_opensToSlice.{u, w, t} S X
  let : ∀ Y : (Over X)ᵒᵖ,
      HasColimitsOfShape (CostructuredArrow (S.opensToSlice X).1.op Y)
        AddCommGrpCat.{max u t} :=
    fun _ => inferInstance
  dsimp [comparisonDirectImage]
  infer_instance

/-- Inverse image of abelian sheaves for the comparison morphism, for coefficients in any
universe containing the universe of the spaces. -/
noncomputable def abelianComparisonInverseImageOfSize
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max u t} ⥤
      Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max u t} :=
  let : (S.comparisonDirectImage X AddCommGrpCat.{max u t}).IsRightAdjoint :=
    abelianComparisonDirectImage_isRightAdjoint_ofSize.{u, w, t} S X
  (S.comparisonDirectImage X AddCommGrpCat.{max u t}).leftAdjoint

/-- The comparison adjunction on abelian sheaves. -/
noncomputable def abelianComparisonAdjunctionOfSize
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    abelianComparisonInverseImageOfSize.{u, w, t} S X ⊣
      S.comparisonDirectImage X AddCommGrpCat.{max u t} :=
  let : (S.comparisonDirectImage X AddCommGrpCat.{max u t}).IsRightAdjoint :=
    abelianComparisonDirectImage_isRightAdjoint_ofSize.{u, w, t} S X
  Adjunction.ofIsRightAdjoint _

/-- Inverse image of abelian sheaves under the Zariski comparison morphism is exact: it is left
exact because the open-subset functor is representably flat, and right exact because it is a
left adjoint.

The coefficients are `AddCommGrpCat.{max u t}`, the whole universe range on which the functor
itself is defined, rather than the `AddCommGrpCat.{max (u + 1) v}` of the rest of the directory.
The two sheafifications the pullback construction needs are produced from `essentiallySmall_over`
and from the smallness of `Opens X.obj`, and the shapes indexing the left Kan extension are
`u`-small by `small_costructuredArrow_opensToSlice`, so no universe below `u + 1` has to be
excluded: at `t = u` this is exactness at `AddCommGrpCat.{u}`, the coefficient universe of a
small model of the site in `Type u`. Nothing here asks for the covering sieves of the slice to be
small, which is the one thing that genuinely lives in `Type (u + 1)`. -/
theorem abelianComparisonInverseImageOfSize_exact
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    exactFunctor _ _ (abelianComparisonInverseImageOfSize.{u, w, t} S X :
      Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max u t} ⥤
      Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max u t}) := by
  rw [exactFunctor_iff]
  constructor
  · let G := (S.opensToSlice X).1
    let J := Opens.grothendieckTopology X.obj
    let K := S.zariskiTopology.over X
    let A := AddCommGrpCat.{max u t}
    let : RepresentablyFlat G := opensToSlice_representablyFlat S X
    let : G.IsContinuous J K := S.opensToSlice_isContinuous X
    let : (G.sheafPushforwardContinuous A J K).IsRightAdjoint := by
      dsimp [G, A, J, K, comparisonDirectImage]
      exact abelianComparisonDirectImage_isRightAdjoint_ofSize.{u, w, t} S X
    let : HasSheafify J A :=
      have : EssentiallySmall.{max u t} (Opens X.obj) :=
        EssentiallySmall.mk' (AsSmall.equiv.{u, u, max u t} (C := Opens X.obj))
      hasSheafifyEssentiallySmallSite.{_, _, _, _, max u t} J A
    let : HasSheafify K A :=
      have := essentiallySmall_over.{u, w, t} S X
      hasSheafifyEssentiallySmallSite.{_, _, _, _, max u t} K A
    dsimp [abelianComparisonInverseImageOfSize, comparisonDirectImage, G, J, K, A]
    let : PreservesLimits (forget A) := AddCommGrpCat.forget_preservesLimits
    let : PreservesFilteredColimits (forget A) := inferInstance
    let : PreservesFilteredColimitsOfSize.{u, u} (forget A) :=
      preservesFilteredColimitsOfSize_of_univLE.{max u t, max u t, u, u} _
    let : ∀ Y : (Over X)ᵒᵖ, Small.{max u t} (CostructuredArrow G.op Y) :=
      small_costructuredArrow_opensToSlice.{u, w, t} S X
    let : ∀ Y : (Over X)ᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op Y) A :=
      fun _ => inferInstance
    let : ∀ Y : (Over X)ᵒᵖ,
        PreservesColimitsOfShape (CostructuredArrow G.op Y) (forget A) := by
      intro Y
      infer_instance
    let : PreservesFiniteLimits (G.op.lan : ((Opens X.obj)ᵒᵖ ⥤ A) ⥤ ((Over X)ᵒᵖ ⥤ A)) :=
      lan_preservesFiniteLimits_of_flat (F := G) (hPres := by
        intro Y
        let : IsFiltered (CostructuredArrow G.op Y) :=
          IsFiltered.of_equivalence (structuredArrowOpEquivalence G (Opposite.unop Y))
        infer_instance)
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  · let : (abelianComparisonInverseImageOfSize.{u, w, t} S X).IsLeftAdjoint :=
      (abelianComparisonAdjunctionOfSize.{u, w, t} S X).isLeftAdjoint
    infer_instance

/-- The direct image on abelian sheaves has its inverse-image left adjoint. -/
theorem abelianComparisonDirectImage_isRightAdjoint
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).IsRightAdjoint :=
  abelianComparisonDirectImage_isRightAdjoint_ofSize.{u, w, max (u + 1) v} S X

/-- Inverse image of abelian sheaves for the comparison morphism. -/
noncomputable def abelianComparisonInverseImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} :=
  let : (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).IsRightAdjoint :=
    S.abelianComparisonDirectImage_isRightAdjoint X
  (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).leftAdjoint

/-- The comparison adjunction on abelian sheaves. -/
noncomputable def abelianComparisonAdjunction
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    S.abelianComparisonInverseImage X ⊣
      S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v} :=
  let : (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).IsRightAdjoint :=
    S.abelianComparisonDirectImage_isRightAdjoint X
  Adjunction.ofIsRightAdjoint _

/-- Inverse image of abelian sheaves under the Zariski comparison morphism is exact: it is left
exact because the open-subset functor is representably flat, and right exact because it is a
left adjoint. -/
theorem abelianComparisonInverseImage_exact
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    exactFunctor _ _ (S.abelianComparisonInverseImage X :
      Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}) :=
  abelianComparisonInverseImageOfSize_exact.{u, w, max (u + 1) v} S X

/-- The abelian comparison inverse image preserves finite limits. -/
noncomputable instance abelianComparisonInverseImage_preservesFiniteLimits
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    PreservesFiniteLimits (S.abelianComparisonInverseImage X :
      Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⥤
        Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}) :=
  ((exactFunctor_iff _).1 (S.abelianComparisonInverseImage_exact X)).1

end LocallyQuasiCompactZariskiSituation

end Stacks.Topology

end
