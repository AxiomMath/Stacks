module

public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Limits
public import StacksCore.CategoryTheory.Sites.Limits
public import StacksCore.CategoryTheory.Sites.Representable.MapsFromRepresentable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.CategoryTheory.Sites.Sheafification.SurjectionCoequalizer
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial
public import StacksFrontier.Topology.Sheaves.Sheaf.Constant
public import StacksFrontier.Topology.Sheaves.Spectral.FiniteSoberPullback

/-!
# Sheaves of sets as filtered colimits of finite presentations

On a site carrying a distinguished collection of quasi-compact objects that covers every
object, every sheaf of sets is a filtered colimit of coequalizers between finite coproducts
of sheafified representables of distinguished objects.  Specialising the collection to a
basis of quasi-compact opens of a topological space turns those sheafified representables
into extensions by the initial object of finite constant sheaves, which is the form in which
the statement is consumed.

## Main definitions

* `Stacks.QuasiCompactObjectsSituation`: a site together with a distinguished collection of
  its objects, with `HasEnoughObjects`, `ObjectsAreQuasiCompact` and
  `CoverPullbacksAreQuasiCompact` recording the three conditions on that collection stated in
  Stacks 0937.  Only the first two are used in this file.
* `Stacks.HasFiniteRepresentableCoequalizerPresentation`: a sheaf is the coequalizer of two
  maps between finite coproducts of sheafified representables of distinguished objects.

## Main results

* `Stacks.exists_epi_coproduct_sheafifiedYoneda`: Stacks 093B (1), every sheaf of sets is
  covered by a coproduct of sheafified representables drawn from the distinguished collection.
* `Stacks.isFilteredColimit_of_hasEnoughQuasiCompactObjects`: the site-level statement, that
  every sheaf of sets is a filtered colimit of sheaves with a finite representable
  coequalizer presentation.
* `Stacks.isFilteredColimit_of_hasCompactBasis`: the statement for a topological space with a
  basis of quasi-compact opens, phrased with
  `Stacks.HasFiniteBasisCoequalizerPresentation`.
* `Stacks.isTopologicalBasis_image_isCompact` and
  `Stacks.isFilteredColimit_of_prespectralSpace`: on a prespectral space the basis hypotheses
  of the previous result are automatic, so each piece of the diagram satisfies the hypothesis
  of `Stacks.exists_pullback_from_finite_sober_of_hasFiniteBasisCoequalizerPresentation`.

## Implementation notes

The presentation predicate appearing in the conclusion of
`Stacks.isFilteredColimit_of_hasCompactBasis` is `Stacks.HasFiniteBasisCoequalizerPresentation`
imported from `StacksFrontier.Topology.Sheaves.Spectral.FiniteSoberPullback`, reused rather than
restated.  That is forced rather than chosen: it is the hypothesis of
`Stacks.exists_pullback_from_finite_sober_of_hasFiniteBasisCoequalizerPresentation`, so
reusing it is what lets the two results compose with no bridging isomorphism between two
spellings of one notion.

Universes are not specialised anywhere.  The site-level results are stated for `C : Type u`
with `Category.{v} C` and sheaves of `Type max u v`; the topological statement instantiates
`C := Opens X` for `X : Type u`, where `max u v` collapses to `u`.  The finite value sets of
the resulting presentations are `PUnit`: `extendedPUnitIsoSheafifiedYoneda` identifies the
extension by the initial object of the constant `PUnit` sheaf on a basis open with the
sheafified representable of that open, and `exists_coequalizer_iso_of_object_isos` transports
a coequalizer presentation across such identifications of its two coproducts.

Being a filtered colimit is recorded concretely, as a filtered small category together with a
diagram and a colimit cocone whose cone point is the given sheaf, rather than through a
predicate on the sheaf; the finite sets in a presentation are arbitrary types carrying a
`Finite` instance rather than chosen enumerations.

Two `local instance`es of high priority supply colimits of finite discrete diagrams and of
parallel pairs.  They are needed because `HasFiniteColimits` packages its
`HasColimitsOfShape` fields inside `HasFiniteColimits.out`, which instance search will not
unfold on its own.  For the same reason `relCocone_π` is stated with an ascribed type and
proved by `:=`, which is tolerant of definitional unfolding: the ambient `HasCoequalizer`
instance is the local high-priority one rather than the one that `coequalizer.π_desc` finds
by itself, so the equation has to be established before it can be rewritten with.

## References

* [Stacks Project, Tag 0937](https://stacks.math.columbia.edu/tag/0937)
* [Stacks Project, Lemma 18.30.5, Tag 093B](https://stacks.math.columbia.edu/tag/093B)
* [Stacks Project, Lemma 18.30.7, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
* [Stacks Project, Lemma 17.19.2, Tag 0CAI](https://stacks.math.columbia.edu/tag/0CAI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace Stacks

section Site

variable {C : Type u} [Category.{v} C]

/-- The standing data of a site and a distinguished collection
of its objects. -/
structure QuasiCompactObjectsSituation (C : Type u) [Category.{v} C] where
  /-- The Grothendieck topology defining the site. -/
  topology : GrothendieckTopology C
  /-- The distinguished collection of objects. -/
  objects : Set C

/-- Condition (1) of Stacks Project, Tag 0937: every object has a covering family whose
members belong to the distinguished collection. -/
def QuasiCompactObjectsSituation.HasEnoughObjects {C : Type u} [Category.{v} C]
    (S : QuasiCompactObjectsSituation C) : Prop :=
  ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
    𝒰.sieve₀ ∈ S.topology U ∧ ∀ i, 𝒰.X i ∈ S.objects

/-- Condition (2) of Stacks Project, Tag 0937: every object in the distinguished collection
is quasi-compact. -/
def QuasiCompactObjectsSituation.ObjectsAreQuasiCompact {C : Type u} [Category.{v} C]
    (S : QuasiCompactObjectsSituation C) : Prop :=
  ∀ U : C, U ∈ S.objects → S.topology.IsQuasiCompactObject U

/-- Condition (3) of Stacks Project, Tag 0937: for a cover whose source objects and target
belong to the distinguished collection, every pairwise fibre product is quasi-compact.

The `HasPullback` conjunct records the existence implicit in the source. The second conjunct
is quantified over the instance used to choose a pullback, so the condition does not depend
on a global choice of pullbacks. -/
@[stacks 0937 "condition (3)"]
def QuasiCompactObjectsSituation.CoverPullbacksAreQuasiCompact {C : Type u} [Category.{v} C]
    (S : QuasiCompactObjectsSituation C) : Prop :=
  ∀ (U : C) (𝒰 : PreZeroHypercover.{max u v} U),
    𝒰.sieve₀ ∈ S.topology U →
      U ∈ S.objects →
      (∀ i, 𝒰.X i ∈ S.objects) →
      ∀ i j,
        HasPullback (𝒰.f i) (𝒰.f j) ∧
          ∀ [HasPullback (𝒰.f i) (𝒰.f j)],
            S.topology.IsQuasiCompactObject (pullback (𝒰.f i) (𝒰.f j))

/-- **Stacks Project, Tag 093B (1).** Every sheaf of sets is covered by a coproduct of sheafified
representables from the distinguished collection: it is the target of a surjective map whose
source is a coproduct of the sheaves `h_{U_i}^#` with `U_i` distinguished. -/
@[stacks 093B "part (1), sheaves of sets"]
theorem exists_epi_coproduct_sheafifiedYoneda
    {C : Type u} [Category.{v} C]
    (S : QuasiCompactObjectsSituation C)
    (hEnough : S.HasEnoughObjects) (F : Sheaf S.topology (Type max u v)) :
    letI : HasColimitsOfSize.{max u v, max u v}
        (Sheaf S.topology (Type max u v)) := CategoryTheory.Sheaf.instHasColimitsOfSize
    ∃ (I : Type max u v) (U : I → C),
      (∀ i, U i ∈ S.objects) ∧
        ∃ (f : (∐ fun i ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i)) ⟶ F),
          Epi f := by
  let : HasColimitsOfSize.{max u v, max u v}
      (Sheaf S.topology (Type max u v)) := CategoryTheory.Sheaf.instHasColimitsOfSize
  let I : Type max u v := Σ U : {X : C // X ∈ S.objects}, F.obj.obj (op U.1)
  let U : I → C := fun i => i.1.1
  let f : (∐ fun i : I ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i)) ⟶ F :=
    Sigma.desc fun i => (Sheaf.sectionEquiv S.topology).symm i.2
  refine ⟨I, U, fun i => i.1.2, f, ?_⟩
  apply (Sheaf.isLocallySurjective_iff_epi f).mp
  refine ⟨?_⟩
  intro X s
  obtain ⟨𝒰, h𝒰, h𝒱⟩ := hEnough X
  let V := 𝒰.X
  let g := 𝒰.f
  have hg : Sieve.ofArrows V g ∈ S.topology X := by
    simpa [PreZeroHypercover.sieve₀, V, g] using h𝒰
  refine S.topology.superset_covering (fun Y k hk => ?_) hg
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  let j : I := ⟨⟨V i, h𝒱 i⟩, F.obj.map (g i).op s⟩
  refine (Presheaf.imageSieve f.hom s).downward_closed ?_ a
  refine ⟨(Sigma.ι (fun i : I ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i)) j).hom.app
    (op (V i)) (Sheaf.tautologicalSection S.topology (V i)), ?_⟩
  have hcomp :
      Sigma.ι (fun i : I ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i)) j ≫ f =
        (Sheaf.sectionEquiv S.topology).symm (F.obj.map (g i).op s) := by
    rw [Sigma.ι_comp_desc]
  have hι : Sheaf.sectionEquiv S.topology
      (Sigma.ι (fun i : I ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i)) j) =
      (Sigma.ι (fun i : I ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i)) j).hom.app
        (op (V i)) (Sheaf.tautologicalSection S.topology (V i)) := by
    rw [← Category.id_comp
      (Sigma.ι (fun i : I ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i)) j)]
    exact Sheaf.sectionEquiv_comp S.topology (𝟙 _) _
  have hval : f.hom.app (op (V i))
      ((Sigma.ι (fun i : I ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i)) j).hom.app
        (op (V i)) (Sheaf.tautologicalSection S.topology (V i))) =
      F.obj.map (g i).op s := by
    calc
      _ = Sheaf.sectionEquiv S.topology
          (Sigma.ι (fun i : I ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i)) j ≫ f) := by
            rw [← hι]
            exact (Sheaf.sectionEquiv_comp S.topology _ f).symm
      _ = F.obj.map (g i).op s := by
            rw [hcomp, Equiv.apply_symm_apply]
  rw [hval]

/-- A category with finite colimits has colimits of functors out of `Discrete (Fin n)`. -/
local instance (priority := 10000) {E : Type*} [Category E] [HasFiniteColimits E]
    (n : ℕ) (X : Fin n → E) : HasColimit (Discrete.functor X) :=
  (HasFiniteColimits.out (C := E) (Discrete (Fin n))).has_colimit _
/-- A category with finite colimits has coequalizers of parallel pairs. -/
local instance (priority := 10000) {E : Type*} [Category E] [HasFiniteColimits E]
    {X Y : E} (f g : X ⟶ Y) : HasColimit (parallelPair f g) :=
  (HasFiniteColimits.out (C := E) WalkingParallelPair).has_colimit _

attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
/-- A sheaf has a finite representable coequalizer presentation relative to `S` if it is
isomorphic to the coequalizer of two maps between finite coproducts of sheafified
representables of distinguished objects. -/
def HasFiniteRepresentableCoequalizerPresentation
    (S : QuasiCompactObjectsSituation C)
    (G : Sheaf S.topology (Type max u v)) : Prop :=
  letI : HasFiniteColimits (Sheaf S.topology (Type max u v)) :=
    CategoryTheory.Sheaf.instHasFiniteColimits
  ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
    (∀ i, U i ∈ S.objects) ∧ (∀ j, V j ∈ S.objects) ∧
      ∃ (f g : (∐ fun j ↦ (Sheaf.sheafifiedYoneda S.topology).obj (V j)) ⟶
          (∐ fun i ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i))),
        Nonempty (coequalizer f g ≅ G)

open Stacks.Sites.SurjectionCoequalizer in
private theorem exists_coproduct_coequalizer_presentation
    (S : QuasiCompactObjectsSituation C) (hEnough : S.HasEnoughObjects)
    (F : Sheaf S.topology (Type max u v)) :
    letI : HasColimitsOfSize.{max u v, max u v}
        (Sheaf S.topology (Type max u v)) := CategoryTheory.Sheaf.instHasColimitsOfSize
    ∃ (I J : Type max u v) (U : I → C) (V : J → C),
      (∀ i, U i ∈ S.objects) ∧ (∀ j, V j ∈ S.objects) ∧
      ∃ (f g : (∐ fun j ↦ (Sheaf.sheafifiedYoneda S.topology).obj (V j)) ⟶
          (∐ fun i ↦ (Sheaf.sheafifiedYoneda S.topology).obj (U i))),
        Nonempty (coequalizer f g ≅ F) := by
  classical
  let : HasColimitsOfSize.{max u v, max u v} (Sheaf S.topology (Type max u v)) :=
    CategoryTheory.Sheaf.instHasColimitsOfSize
  obtain ⟨I, U, hU, ⟨p, hp⟩⟩ :=
    exists_epi_coproduct_sheafifiedYoneda S hEnough F
  let G := ∐ fun i : I => (Sheaf.sheafifiedYoneda S.topology).obj (U i)
  let hsurj : IsSurjectiveSheafType S.topology p := by
    intro X s
    let q := (sheafToPresheaf S.topology (Type max u v)).map p
    let T := Presheaf.imageSieve q s
    refine ⟨T, ?_, fun _ _ hf => hf⟩
    let : Presheaf.IsLocallySurjective S.topology q :=
      (Sheaf.isLocallySurjective_iff_epi p).2 hp
    exact Presheaf.imageSieve_mem (J := S.topology) q s
  obtain ⟨hc⟩ := coequalizer_of_surjection S.topology p hsurj
  obtain ⟨I', V, hV, ⟨e, he⟩⟩ :=
    exists_epi_coproduct_sheafifiedYoneda S hEnough
      (pullback p p)
  let a := e ≫ pullback.fst p p
  let b := e ≫ pullback.snd p p
  let hc' := isCoequalizerEpiComp hc e
  exact ⟨I, I', U, V, hU, hV, a, b, ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc'⟩⟩

/-! A map from a quasi-compact sheaf to a coproduct has finite support. These are the
subsheaves used to turn quasi-compactness into that factorization. -/

private def localImagePreimage {J : GrothendieckTopology C}
    {X Y Z : Sheaf J (Type max u v)} (p : X ⟶ Y) (φ : Z ⟶ Y) : Subfunctor X.obj :=
  ((Subfunctor.range φ.hom).sheafify J).preimage p.hom

private alias mem_local_sheafified_range :=
  Stacks.Sites.ColimitGlobalSections.mem_sheafify_range_iff

private lemma localImagePreimage_isSheaf {J : GrothendieckTopology C}
    {X Y Z : Sheaf J (Type max u v)} (p : X ⟶ Y) (φ : Z ⟶ Y) :
    Presheaf.IsSheaf J (localImagePreimage p φ).toFunctor := by
  refine
    (isSheaf_iff_isSheaf_of_type J _).2
      ((Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type J X.obj).1 X.property)).2
        fun W x hx => ?_)
  have hle :
      (localImagePreimage p φ).sieveOfSection x ≤
        (((Subfunctor.range φ.hom).sheafify J).sieveOfSection (p.hom.app W x)) := by
    intro V g hg
    rw [Subfunctor.sieveOfSection_apply, ← NatTrans.naturality_apply p.hom g.op x]
    rw [Subfunctor.sieveOfSection_apply] at hg
    change X.obj.map g.op x ∈ (localImagePreimage p φ).obj (op V) at hg
    change p.hom.app (op V) (X.obj.map g.op x) ∈
      ((Subfunctor.range φ.hom).sheafify J).obj (op V) at hg
    exact hg
  have h : p.hom.app W x ∈
      (((Subfunctor.range φ.hom).sheafify J).sheafify J).obj W :=
    J.superset_covering hle hx
  rwa [((Subfunctor.range φ.hom).sheafify_sheafify
    ((isSheaf_iff_isSheaf_of_type J Y.obj).1 Y.property))] at h

private def localImagePreimageSheaf {J : GrothendieckTopology C}
    {X Y Z : Sheaf J (Type max u v)} (p : X ⟶ Y) (φ : Z ⟶ Y) : Sheaf J (Type max u v) :=
  ⟨(localImagePreimage p φ).toFunctor, localImagePreimage_isSheaf p φ⟩

private def localImagePreimageι {J : GrothendieckTopology C}
    {X Y Z : Sheaf J (Type max u v)} (p : X ⟶ Y) (φ : Z ⟶ Y) :
    localImagePreimageSheaf p φ ⟶ X :=
  ObjectProperty.homMk (localImagePreimage p φ).ι

private lemma localImagePreimage_mem_of_eq {J : GrothendieckTopology C}
    {X Y Z : Sheaf J (Type max u v)} (p : X ⟶ Y) (φ : Z ⟶ Y) {W : C}
    (x : X.obj.obj (op W)) (z : Z.obj.obj (op W))
    (h : φ.hom.app (op W) z = p.hom.app (op W) x) :
    x ∈ (localImagePreimage p φ).obj (op W) := by
  rw [localImagePreimage, Subfunctor.preimage_obj, Set.mem_preimage,
    mem_local_sheafified_range, ← h, Presheaf.imageSieve_app]
  exact J.top_mem W

private lemma isLocallySurjective_sigmaDesc_localImagePreimage
    {J : GrothendieckTopology C} {α : Type max u v}
    {X Y : Sheaf J (Type max u v)}
    [HasColimitsOfShape (Discrete α) (Sheaf J (Type max u v))]
    (f : X ⟶ Y) (G : α → Sheaf J (Type max u v))
    (g : ∀ i, G i ⟶ Y)
    (h : ∀ (W : C) (x : X.obj.obj (op W)),
      ∃ S ∈ J W, ∀ ⦃V : C⦄ (k : V ⟶ W), S k →
        ∃ (i : α) (z : (G i).obj.obj (op V)),
          (g i).hom.app (op V) z = f.hom.app (op V) (X.obj.map k.op x)) :
    Sheaf.IsLocallySurjective
      (Sigma.desc fun i => localImagePreimageι f (g i)) := by
  let : HasColimitsOfSize.{max u v, max u v} (Sheaf J (Type max u v)) :=
    CategoryTheory.Sheaf.instHasColimitsOfSize
  constructor
  intro W x
  obtain ⟨S, hS, hl⟩ := h W x
  refine J.superset_covering (fun V k hk => ?_) hS
  obtain ⟨i, z, hz⟩ := hl k hk
  let G' := fun i => localImagePreimageSheaf f (g i)
  let t : (G' i).obj.obj (op V) := ⟨X.obj.map k.op x,
    localImagePreimage_mem_of_eq f (g i) _ z hz⟩
  refine ⟨(Sigma.ι G' i).hom.app (op V) t, ?_⟩
  change ((Sigma.ι G' i ≫ Sigma.desc (fun i => localImagePreimageι f (g i))).hom.app
    (op V) t) = X.obj.map k.op x
  rw [Sigma.ι_comp_desc]
  rfl

private noncomputable def coproductColimitEval {J : GrothendieckTopology C}
    {α : Type max u v} [HasColimitsOfShape (Discrete α) (Sheaf J (Type max u v))]
    (G : α → Sheaf J (Type max u v)) (W : C) :
    IsColimit (((evaluation Cᵒᵖ (Type max u v)).obj (op W)).mapCocone
      (colimit.cocone (Discrete.functor G ⋙ sheafToPresheaf J (Type max u v)))) :=
  isColimitOfPreserves _ (colimit.isColimit _)

private noncomputable def coproductColimitSheafifyIso {J : GrothendieckTopology C}
    {α : Type max u v} [HasColimitsOfShape (Discrete α) (Sheaf J (Type max u v))]
    (G : α → Sheaf J (Type max u v)) :
    CategoryTheory.sheafify J (colimit (Discrete.functor G ⋙ sheafToPresheaf J
      (Type max u v))) ≅ (colimit (Discrete.functor G)).obj :=
  (sheafToPresheaf J (Type max u v)).mapIso
    (IsColimit.coconePointUniqueUpToIso
      (Sheaf.isColimitSheafifyCocone
        (colimit.cocone (Discrete.functor G ⋙ sheafToPresheaf J (Type max u v)))
        (colimit.isColimit _))
      (colimit.isColimit (Discrete.functor G)))

private lemma toSheafify_comp_coproductPost {J : GrothendieckTopology C}
    {α : Type max u v} [HasColimitsOfShape (Discrete α) (Sheaf J (Type max u v))]
    (G : α → Sheaf J (Type max u v)) :
    CategoryTheory.toSheafify J (colimit (Discrete.functor G ⋙
      sheafToPresheaf J (Type max u v))) ≫ (coproductColimitSheafifyIso G).hom =
      colimit.post (Discrete.functor G) (sheafToPresheaf J (Type max u v)) := by
  refine colimit.hom_ext fun i => ?_
  have h1 :
      ((Sheaf.sheafifyCocone
        (colimit.cocone (Discrete.functor G ⋙ sheafToPresheaf J (Type max u v)))).ι.app i).hom =
        colimit.ι (Discrete.functor G ⋙ sheafToPresheaf J (Type max u v)) i ≫
          CategoryTheory.toSheafify J (colimit (Discrete.functor G ⋙
            sheafToPresheaf J (Type max u v))) :=
    Sheaf.sheafifyCocone_ι_app_val _ i
  have h2 :
      (Sheaf.sheafifyCocone
        (colimit.cocone (Discrete.functor G ⋙ sheafToPresheaf J (Type max u v)))).ι.app i ≫
          (IsColimit.coconePointUniqueUpToIso
            (Sheaf.isColimitSheafifyCocone
              (colimit.cocone (Discrete.functor G ⋙ sheafToPresheaf J (Type max u v)))
              (colimit.isColimit _))
            (colimit.isColimit (Discrete.functor G))).hom =
        colimit.ι (Discrete.functor G) i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ i
  rw [colimit.ι_post, ← Category.assoc, ← h1]
  exact congrArg (fun k : _ ⟶ colimit (Discrete.functor G) => k.hom) h2

private lemma isLocallySurjective_coproductPost {J : GrothendieckTopology C}
    {α : Type max u v} [HasColimitsOfShape (Discrete α) (Sheaf J (Type max u v))]
    (G : α → Sheaf J (Type max u v)) :
    Presheaf.IsLocallySurjective J
      (colimit.post (Discrete.functor G) (sheafToPresheaf J (Type max u v))) :=
  (Presheaf.isLocallySurjective_iff_of_fac J (toSheafify_comp_coproductPost G)).2 inferInstance

private lemma exists_local_summand {J : GrothendieckTopology C}
    {α : Type max u v} [HasColimitsOfShape (Discrete α) (Sheaf J (Type max u v))]
    (G : α → Sheaf J (Type max u v)) (W : C)
    (z : (∐ G).obj.obj (op W)) :
    ∃ S ∈ J W, ∀ ⦃V : C⦄ (f : V ⟶ W), S f →
      ∃ (i : α) (t : (G i).obj.obj (op V)),
        (Sigma.ι G i).hom.app (op V) t = (∐ G).obj.map f.op z := by
  let p := colimit.post (Discrete.functor G) (sheafToPresheaf J (Type max u v))
  have hp : Presheaf.IsLocallySurjective J p := isLocallySurjective_coproductPost G
  refine ⟨Presheaf.imageSieve p z, Presheaf.imageSieve_mem J p z, fun V f hf => ?_⟩
  obtain ⟨x, hx⟩ := hf
  obtain ⟨i, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (coproductColimitEval G V) x
  refine ⟨i.as, t, ?_⟩
  have ht' : (colimit.ι (Discrete.functor G ⋙ sheafToPresheaf J (Type max u v)) i).app
      (op V) t = x := ht
  have hpost : p.app (op V)
      ((colimit.ι (Discrete.functor G ⋙ sheafToPresheaf J (Type max u v)) i).app (op V) t) =
      (colimit.ι (Discrete.functor G) i).hom.app (op V) t :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (colimit.ι_post (Discrete.functor G)
        (sheafToPresheaf J (Type max u v)) i) (op V)) t
  have htarget : (colimit (Discrete.functor G)).obj.map f.op z =
      (∐ G).obj.map f.op z := rfl
  simpa [p, ← htarget] using
    hpost.symm.trans ((congrArg (fun w => p.app (op V) w) ht').trans hx)

private alias imageSieve_mem_of_local :=
  Stacks.Sites.ColimitGlobalSections.imageSieve_mem_of_local

private def FactorsThroughFiniteSubcoproduct {J : GrothendieckTopology C}
    {α : Type max u v} {X : Sheaf J (Type max u v)} {G : α → Sheaf J (Type max u v)}
    [HasColimitsOfShape (Discrete α) (Sheaf J (Type max u v))]
    (f : X ⟶ ∐ G) : Prop :=
  letI : HasColimitsOfSize.{max u v, max u v} (Sheaf J (Type max u v)) :=
    CategoryTheory.Sheaf.instHasColimitsOfSize
  letI : HasFiniteColimits (Sheaf J (Type max u v)) := CategoryTheory.Sheaf.instHasFiniteColimits
  ∃ (T : Set α), T.Finite ∧ ∃ (g : X ⟶ ∐ fun i : T => G i.1),
    g ≫ Sigma.desc (fun i : T => Sigma.ι G i.1) = f

private theorem exists_factor_through_finite_subcoproduct {J : GrothendieckTopology C}
    {α : Type max u v} {X : Sheaf J (Type max u v)} {G : α → Sheaf J (Type max u v)}
    [HasColimitsOfShape (Discrete α) (Sheaf J (Type max u v))]
    (hX : Sheaf.IsQuasiCompact X) (f : X ⟶ ∐ G) :
    FactorsThroughFiniteSubcoproduct f := by
  classical
  let : HasColimitsOfSize.{max u v, max u v} (Sheaf J (Type max u v)) :=
    CategoryTheory.Sheaf.instHasColimitsOfSize
  let : HasFiniteColimits (Sheaf J (Type max u v)) := CategoryTheory.Sheaf.instHasFiniteColimits
  let B : α → Sheaf J (Type max u v) := fun i =>
    localImagePreimageSheaf f (Sigma.ι G i)
  let b : ∀ i, B i ⟶ X := fun i => localImagePreimageι f (Sigma.ι G i)
  have hlocal : ∀ (W : C) (x : X.obj.obj (op W)),
      ∃ S ∈ J W, ∀ ⦃V : C⦄ (k : V ⟶ W), S k →
        ∃ (i : α) (z : (G i).obj.obj (op V)),
          (Sigma.ι G i).hom.app (op V) z = f.hom.app (op V) (X.obj.map k.op x) := by
    intro W x
    obtain ⟨S, hS, hl⟩ := exists_local_summand G W (f.hom.app (op W) x)
    refine ⟨S, hS, fun V k hk => ?_⟩
    obtain ⟨i, z, hz⟩ := hl k hk
    exact ⟨i, z, hz.trans (NatTrans.naturality_apply f.hom k.op x).symm⟩
  have hcover : Sheaf.IsLocallySurjective (Sigma.desc b) :=
    isLocallySurjective_sigmaDesc_localImagePreimage
      (f := f) (G := G) (g := fun i => Sigma.ι G i) hlocal
  obtain ⟨T, hTfin, hT⟩ := hX α B b hcover
  let e : (∐ fun i : T => G i.1) ⟶ ∐ G := Sigma.desc (fun i : T => Sigma.ι G i.1)
  have heLocal : ∀ (W : C) (x : X.obj.obj (op W)),
      Presheaf.imageSieve e.hom (f.hom.app (op W) x) ∈ J W := by
    intro W x
    let d := Sigma.desc (fun i : T => b i.1)
    let : Presheaf.IsLocallySurjective J d.hom := hT
    refine imageSieve_mem_of_local (J := J) e.hom (f.hom.app (op W) x)
      (Presheaf.imageSieve_mem J d.hom x) fun V k hk => ?_
    obtain ⟨s, hs⟩ := hk
    obtain ⟨S, hS, hl⟩ := exists_local_summand (fun i : T => B i.1) V s
    refine imageSieve_mem_of_local (J := J) e.hom
      ((∐ G).obj.map k.op (f.hom.app (op W) x)) hS fun Z q hq => ?_
    obtain ⟨⟨i, hi⟩, z, hz⟩ := hl q hq
    let j : T := ⟨i, hi⟩
    let y : X.obj.obj (op Z) := (b j.1).hom.app (op Z) z
    have hy : y = X.obj.map (q ≫ k).op x := by
      change (b j).hom.app (op Z) z = X.obj.map (q ≫ k).op x
      calc
        (b j).hom.app (op Z) z =
            d.hom.app (op Z) ((Sigma.ι (fun i : T => B i.1) j).hom.app (op Z) z) := by
          change (b j).hom.app (op Z) z =
            ((Sigma.ι (fun i : T => B i.1) j ≫ d).hom.app (op Z)) z
          exact (congrArg (fun h : B j ⟶ X => h.hom.app (op Z) z)
            (Sigma.ι_comp_desc (fun i : T => b i.1) j)).symm
        _ = d.hom.app (op Z) ((∐ fun i : T => B i.1).obj.map q.op s) :=
          congrArg (d.hom.app (op Z)) hz
        _ = X.obj.map q.op (d.hom.app (op V) s) := by
          rw [← NatTrans.naturality_apply d.hom q.op s]
        _ = X.obj.map q.op (X.obj.map k.op x) := congrArg (X.obj.map q.op) hs
        _ = X.obj.map (q ≫ k).op x := by
          rw [← Functor.map_comp_apply, op_comp]
    have hmem : y ∈ (localImagePreimage f (Sigma.ι G j.1)).obj (op Z) := z.2
    have hrel : Presheaf.imageSieve (Sigma.ι G j.1).hom
        (f.hom.app (op Z) y) ∈ J Z := by
      change f.hom.app (op Z) y ∈
        ((Subfunctor.range (Sigma.ι G j.1).hom).sheafify J).obj (op Z) at hmem
      exact (mem_local_sheafified_range _ _).1 hmem
    have hrel' : Presheaf.imageSieve e.hom (f.hom.app (op Z) y) ∈ J Z := by
      refine J.superset_covering (fun Z' r hr => ?_) hrel
      obtain ⟨t, ht⟩ := hr
      refine ⟨(Sigma.ι (fun j' : T => G j'.1) j).hom.app (op Z') t, ?_⟩
      change ((Sigma.ι (fun j' : T => G j'.1) j ≫ e).hom.app (op Z') t) = _
      rwa [Sigma.ι_comp_desc]
    have heq : f.hom.app (op Z) y =
        (∐ G).obj.map q.op ((∐ G).obj.map k.op (f.hom.app (op W) x)) := by
      rw [hy, NatTrans.naturality_apply f.hom (q ≫ k).op x, op_comp, Functor.map_comp_apply]
    rwa [← heq]
  refine ⟨T, hTfin, ?_⟩
  -- The finite subcoproduct is a subobject of the full coproduct. Its image is a sheaf,
  -- so local membership of `f` gives the required lift.
  have heMono : Mono e := by
    change Mono (Sigma.map' (fun i : T => i.1) (fun i => 𝟙 (G i.1)))
    exact MonoCoprod.mono_map'_of_injective G (fun i : T => i.1) Subtype.val_injective
  have heHomMono : Mono e.hom := (Sheaf.Hom.mono_iff_presheaf_mono J _ e).mp heMono
  have hRangeSheaf : Presieve.IsSheaf J (Subfunctor.range e.hom).toFunctor :=
    Presieve.isSheaf_iso J (asIso (Subfunctor.toRange e.hom))
      ((isSheaf_iff_isSheaf_of_type J (∐ fun i : T => G i.1).obj).1
        (∐ fun i : T => G i.1).property)
  have hRangeMem : ∀ (W : C) (x : X.obj.obj (op W)),
      f.hom.app (op W) x ∈ (Subfunctor.range e.hom).obj (op W) := by
    intro W x
    have hcover :
        (Subfunctor.range e.hom).sieveOfSection (f.hom.app (op W) x) ∈ J W := heLocal W x
    exact (Subfunctor.isSheaf_iff (Subfunctor.range e.hom)
      ((isSheaf_iff_isSheaf_of_type J (∐ G).obj).1 (∐ G).property)).1 hRangeSheaf
        (op W) (f.hom.app (op W) x) hcover
  let hfRange : Subfunctor.range f.hom ≤ Subfunctor.range e.hom := by
    rintro W y ⟨x, rfl⟩
    exact hRangeMem W.unop x
  let lift : X.obj ⟶ (Subfunctor.range e.hom).toFunctor := Subfunctor.lift f.hom hfRange
  let g0 : X.obj ⟶ (∐ fun i : T => G i.1).obj :=
    lift ≫ inv (Subfunctor.toRange e.hom)
  let g : X ⟶ ∐ fun i : T => G i.1 := ObjectProperty.homMk g0
  refine ⟨g, ?_⟩
  apply Sheaf.hom_ext
  change g0 ≫ e.hom = f.hom
  dsimp [g0, lift]
  calc
    Subfunctor.lift f.hom hfRange ≫ inv (Subfunctor.toRange e.hom) ≫ e.hom =
        Subfunctor.lift f.hom hfRange ≫ inv (Subfunctor.toRange e.hom) ≫
          (Subfunctor.toRange e.hom ≫ (Subfunctor.range e.hom).ι) := by
            rw [Subfunctor.toRange_ι]
    _ = Subfunctor.lift f.hom hfRange ≫ (Subfunctor.range e.hom).ι := by
      rw [IsIso.inv_hom_id_assoc]
    _ = f.hom := Subfunctor.lift_ι f.hom hfRange


universe w v' u'
namespace FiniteSupport
noncomputable section
variable {D : Type u'} [Category.{v'} D] [HasColimitsOfSize.{w, w} D]
  {I K : Type w}

/-- A category with colimits of size `w` has colimits of functors out of small categories
`L : Type w`. -/
local instance (priority := 9000) {L : Type w} [SmallCategory L] (F : L ⥤ D) :
    HasColimit F :=
  (HasColimitsOfSize.has_colimits_of_shape (C := D) L).has_colimit F

private abbrev sumObj (U : I → D) (t : Finset I) := ∐ fun i : t => U i.1
private def sumMap (U : I → D) {s t : Finset I} (h : s ⊆ t) : sumObj U s ⟶ sumObj U t :=
  Sigma.desc fun i => Sigma.ι (fun j : t => U j.1) ⟨i.1, h i.2⟩
private def sumι (U : I → D) (t : Finset I) : sumObj U t ⟶ ∐ U :=
  Sigma.desc fun i => Sigma.ι U i.1
private lemma sumMap_ι (U : I → D) {s t : Finset I} (h : s ⊆ t) (i : s) :
    Sigma.ι (fun j : s => U j.1) i ≫ sumMap U h =
      Sigma.ι (fun j : t => U j.1) ⟨i.1, h i.2⟩ := by simp [sumMap]
private lemma sumMap_sumι (U : I → D) {s t : Finset I} (h : s ⊆ t) :
    sumMap U h ≫ sumι U t = sumι U s :=
  Sigma.hom_ext _ _ fun _ => by simp [sumMap, sumι]
private lemma sumMap_id (U : I → D) (s : Finset I) :
    sumMap U (Finset.Subset.refl s) = 𝟙 _ :=
  Sigma.hom_ext _ _ fun _ => by simp [sumMap]
private lemma sumMap_comp (U : I → D) {s t r : Finset I} (h : s ⊆ t) (h' : t ⊆ r) :
    sumMap U h ≫ sumMap U h' = sumMap U (h.trans h') :=
  Sigma.hom_ext _ _ fun _ => by simp [sumMap]

variable (U : I → D) (V : K → D) (f g : (∐ V) ⟶ ∐ U)
private def Supported (t : Finset I) (r : Finset K) : Prop :=
  ∃ a b : sumObj V r ⟶ sumObj U t,
    a ≫ sumι U t = sumι V r ≫ f ∧ b ≫ sumι U t = sumι V r ≫ g
private abbrev SupportIndex := {p : Finset I × Finset K // Supported U V f g p.1 p.2}

private lemma exists_support_above
    (hf : ∀ r, ∃ t, Supported U V f g t r) (t : Finset I) (r : Finset K) :
    ∃ x : SupportIndex U V f g, t ⊆ x.1.1 ∧ r ⊆ x.1.2 := by
  classical
  obtain ⟨s, a, b, ha, hb⟩ := hf r
  refine ⟨⟨(t ∪ s, r), a ≫ sumMap U Finset.subset_union_right,
    b ≫ sumMap U Finset.subset_union_right, ?_, ?_⟩,
    Finset.subset_union_left, le_rfl⟩ <;>
  simp only [Category.assoc, sumMap_sumι] <;> assumption

private lemma supportIndex_directed (hf : ∀ r, ∃ t, Supported U V f g t r) :
    IsDirectedOrder (SupportIndex U V f g) := by
  classical
  refine ⟨fun x y => ?_⟩
  obtain ⟨z, ht, hr⟩ := exists_support_above U V f g hf (x.1.1 ∪ y.1.1) (x.1.2 ∪ y.1.2)
  exact ⟨z, ⟨Finset.subset_union_left.trans ht, Finset.subset_union_left.trans hr⟩,
    ⟨Finset.subset_union_right.trans ht, Finset.subset_union_right.trans hr⟩⟩

private def relF (x : SupportIndex U V f g) : sumObj V x.1.2 ⟶ sumObj U x.1.1 :=
  x.2.choose
private def relG (x : SupportIndex U V f g) : sumObj V x.1.2 ⟶ sumObj U x.1.1 :=
  x.2.choose_spec.choose
private lemma relF_fac (x : SupportIndex U V f g) :
    relF U V f g x ≫ sumι U x.1.1 = sumι V x.1.2 ≫ f :=
  x.2.choose_spec.choose_spec.1
private lemma relG_fac (x : SupportIndex U V f g) :
    relG U V f g x ≫ sumι U x.1.1 = sumι V x.1.2 ≫ g :=
  x.2.choose_spec.choose_spec.2

variable [MonoCoprod D]
private lemma sumι_mono (t : Finset I) : Mono (sumι U t) := by
  simpa only [Sigma.map', Category.id_comp, sumι, Function.comp_def] using
    (MonoCoprod.mono_map'_of_injective U (fun i : t => i.1) Subtype.val_injective)
/-- Two finitely supported factorizations of the same map are compatible with the inclusions of
the supports. -/
private lemma comp_sumMap_comm {t t' : Finset I} {r r' : Finset K} (k : ∐ V ⟶ ∐ U)
    {a : sumObj V r ⟶ sumObj U t} {a' : sumObj V r' ⟶ sumObj U t'}
    (ha : a ≫ sumι U t = sumι V r ≫ k) (ha' : a' ≫ sumι U t' = sumι V r' ≫ k)
    (ht : t ⊆ t') (hr : r ⊆ r') : a ≫ sumMap U ht = sumMap V hr ≫ a' := by
  let := sumι_mono U t'
  apply (cancel_mono (sumι U t')).1
  rw [Category.assoc, sumMap_sumι, ha, Category.assoc, ha', ← Category.assoc, sumMap_sumι]
private lemma relF_square {x y : SupportIndex U V f g} (h : x ≤ y) :
    relF U V f g x ≫ sumMap U h.1 = sumMap V h.2 ≫ relF U V f g y :=
  comp_sumMap_comm U V f (relF_fac U V f g x) (relF_fac U V f g y) h.1 h.2
private lemma relG_square {x y : SupportIndex U V f g} (h : x ≤ y) :
    relG U V f g x ≫ sumMap U h.1 = sumMap V h.2 ≫ relG U V f g y :=
  comp_sumMap_comm U V g (relG_fac U V f g x) (relG_fac U V f g y) h.1 h.2

variable [HasFiniteColimits D]

private def relDiagram : SupportIndex U V f g ⥤ D where
  obj x := coequalizer (relF U V f g x) (relG U V f g x)
  map {x y} h := coequalizer.desc (f := relF U V f g x) (g := relG U V f g x)
    (sumMap U (leOfHom h).1 ≫ coequalizer.π (relF U V f g y) (relG U V f g y)) (by
    rw [← Category.assoc, ← Category.assoc, relF_square U V f g (leOfHom h),
      relG_square U V f g (leOfHom h), Category.assoc, Category.assoc, coequalizer.condition])
  map_id x := by
    apply coequalizer.hom_ext
    simp [sumMap_id]
  map_comp {x y z} h k := by
    apply coequalizer.hom_ext
    simp only [coequalizer.π_desc, coequalizer.π_desc_assoc, Category.assoc]
    rw [← Category.assoc, sumMap_comp]

private def relCocone : Cocone (relDiagram U V f g) where
  pt := coequalizer f g
  ι := {
    app x := coequalizer.desc (f := relF U V f g x) (g := relG U V f g x)
      (sumι U x.1.1 ≫ coequalizer.π f g) (by
      rw [← Category.assoc, ← Category.assoc, relF_fac, relG_fac, Category.assoc,
        Category.assoc, coequalizer.condition])
    naturality {x y} h := by
      apply coequalizer.hom_ext
      simp only [Functor.const_obj_map, relDiagram,
        coequalizer.π_desc, coequalizer.π_desc_assoc, Category.assoc]
      rw [← Category.assoc, sumMap_sumι]
      dsimp
      simp only [Category.comp_id] }

/-- The defining factorization of a leg of `relCocone` through the coequalizer projection.

Stated with an ascribed type and proved by `:=` so that the equation is available for
rewriting even though the ambient `HasCoequalizer` instance is the local high-priority one
rather than the one `coequalizer.π_desc` picks up on its own. -/
private lemma relCocone_π (x : SupportIndex U V f g) :
    coequalizer.π (relF U V f g x) (relG U V f g x) ≫ (relCocone U V f g).ι.app x =
      sumι U x.1.1 ≫ coequalizer.π f g :=
  coequalizer.π_desc _ _

omit [MonoCoprod D] [HasFiniteColimits D] in
private lemma glue_summands {N : Type w} [Preorder N] [IsDirectedOrder N]
    (t : N → Finset I) (ht : Monotone t) (hc : ∀ i, ∃ x, i ∈ t x)
    {Z : D} (d : ∀ x, sumObj U (t x) ⟶ Z)
    (hd : ∀ x y (h : x ≤ y), sumMap U (ht h) ≫ d y = d x) :
    ∃! p : (∐ U) ⟶ Z, ∀ x, sumι U (t x) ≫ p = d x := by
  classical
  choose st hst using hc
  let p : (∐ U) ⟶ Z := Sigma.desc fun i =>
    Sigma.ι (fun j : t (st i) => U j.1) ⟨i, hst i⟩ ≫ d (st i)
  have hp (x : N) : sumι U (t x) ≫ p = d x := by
    refine Sigma.hom_ext _ _ fun i => ?_
    obtain ⟨z, hx, hs⟩ := exists_ge_ge x (st i.1)
    have h1 := congrArg (fun k => Sigma.ι (fun j : t x => U j.1) i ≫ k) (hd x z hx)
    have h2 := congrArg (fun k =>
      Sigma.ι (fun j : t (st i.1) => U j.1) ⟨i.1, hst i.1⟩ ≫ k) (hd (st i.1) z hs)
    simp only [← Category.assoc, sumMap_ι] at h1 h2
    simpa [sumι, p] using h2.symm.trans h1
  refine ⟨p, hp, fun q hq => Sigma.hom_ext _ _ fun i => ?_⟩
  simpa [sumι, p] using congrArg (fun k =>
    Sigma.ι (fun j : t (st i) => U j.1) ⟨i, hst i⟩ ≫ k) (hq (st i))

private def relCoconeIsColimit
    (hf : ∀ r, ∃ t, Supported U V f g t r) : IsColimit (relCocone U V f g) := by
  classical
  letI := supportIndex_directed U V f g hf
  have ht (i : I) : ∃ x : SupportIndex U V f g, i ∈ x.1.1 := by
    obtain ⟨x, hx, _⟩ := exists_support_above U V f g hf {i} ∅
    exact ⟨x, hx (Finset.mem_singleton_self i)⟩
  have hr (j : K) : ∃ x : SupportIndex U V f g, j ∈ x.1.2 := by
    obtain ⟨x, _, hx⟩ := exists_support_above U V f g hf ∅ {j}
    exact ⟨x, hx (Finset.mem_singleton_self j)⟩
  have ex (c : Cocone (relDiagram U V f g)) :
      ∃! k : coequalizer f g ⟶ c.pt,
        ∀ x, (relCocone U V f g).ι.app x ≫ k = c.ι.app x := by
    let d (x : SupportIndex U V f g) :=
      coequalizer.π (relF U V f g x) (relG U V f g x) ≫ c.ι.app x
    have hd (x y : SupportIndex U V f g) (h : x ≤ y) :
        sumMap U h.1 ≫ d y = d x := by
      have hc := congrArg (fun k =>
        coequalizer.π (relF U V f g x) (relG U V f g x) ≫ k) (c.w (homOfLE h))
      simpa [relDiagram, d] using hc
    obtain ⟨p, hp, hu⟩ := glue_summands U (fun x : SupportIndex U V f g => x.1.1)
      (show Monotone (fun x : SupportIndex U V f g => x.1.1) from fun _ _ h => h.1) ht d hd
    have heq : f ≫ p = g ≫ p := by
      refine Sigma.hom_ext _ _ fun j => ?_
      obtain ⟨x, hj⟩ := hr j
      have h : sumι V x.1.2 ≫ f ≫ p = sumι V x.1.2 ≫ g ≫ p := by
        rw [← Category.assoc, ← Category.assoc,
          ← relF_fac U V f g x, ← relG_fac U V f g x,
          Category.assoc, Category.assoc, hp]
        exact coequalizer.condition_assoc (relF U V f g x) (relG U V f g x) (c.ι.app x)
      simpa [sumι] using congrArg (fun k => Sigma.ι (fun j : x.1.2 => V j.1) ⟨j, hj⟩ ≫ k) h
    let k := coequalizer.desc p heq
    have hkπ : coequalizer.π f g ≫ k = p := coequalizer.π_desc p heq
    have hk (x) : (relCocone U V f g).ι.app x ≫ k = c.ι.app x := by
      apply coequalizer.hom_ext
      calc coequalizer.π (relF U V f g x) (relG U V f g x) ≫
            (relCocone U V f g).ι.app x ≫ k
          = (coequalizer.π (relF U V f g x) (relG U V f g x) ≫
              (relCocone U V f g).ι.app x) ≫ k := (Category.assoc _ _ _).symm
        _ = (sumι U x.1.1 ≫ coequalizer.π f g) ≫ k :=
              congrArg (· ≫ k) (relCocone_π U V f g x)
        _ = sumι U x.1.1 ≫ coequalizer.π f g ≫ k := Category.assoc _ _ _
        _ = sumι U x.1.1 ≫ p := congrArg (sumι U x.1.1 ≫ ·) hkπ
        _ = coequalizer.π (relF U V f g x) (relG U V f g x) ≫ c.ι.app x := hp x
    refine ⟨k, hk, fun q hq => coequalizer.hom_ext ?_⟩
    change coequalizer.π f g ≫ q = coequalizer.π f g ≫ k
    rw [coequalizer.π_desc]
    refine hu _ fun x => ?_
    calc sumι U x.1.1 ≫ coequalizer.π f g ≫ q
        = (sumι U x.1.1 ≫ coequalizer.π f g) ≫ q := (Category.assoc _ _ _).symm
      _ = (coequalizer.π (relF U V f g x) (relG U V f g x) ≫
            (relCocone U V f g).ι.app x) ≫ q :=
            congrArg (· ≫ q) (relCocone_π U V f g x).symm
      _ = coequalizer.π (relF U V f g x) (relG U V f g x) ≫
            (relCocone U V f g).ι.app x ≫ q := Category.assoc _ _ _
      _ = coequalizer.π (relF U V f g x) (relG U V f g x) ≫ c.ι.app x :=
            congrArg (coequalizer.π (relF U V f g x) (relG U V f g x) ≫ ·) (hq x)
  choose desc hdesc huniq using ex
  exact { desc := desc, fac := hdesc, uniq := fun c m hm => huniq c m hm }

omit [MonoCoprod D] [HasFiniteColimits D] in
private lemma supported_of_finite_factors
    (hf : ∀ j, ∃ t, ∃ a : V j ⟶ sumObj U t, a ≫ sumι U t = Sigma.ι V j ≫ f)
    (hg : ∀ j, ∃ t, ∃ b : V j ⟶ sumObj U t, b ≫ sumι U t = Sigma.ι V j ≫ g)
    (r : Finset K) : ∃ t, Supported U V f g t r := by
  classical
  choose tf af haf using hf
  choose tg ag hag using hg
  let t := r.biUnion (fun j => tf j ∪ tg j)
  have htf (j : r) : tf j.1 ⊆ t := fun i hi =>
    Finset.mem_biUnion.mpr ⟨j.1, j.2, Finset.mem_union_left _ hi⟩
  have htg (j : r) : tg j.1 ⊆ t := fun i hi =>
    Finset.mem_biUnion.mpr ⟨j.1, j.2, Finset.mem_union_right _ hi⟩
  refine ⟨t, Sigma.desc (fun j : r => af j.1 ≫ sumMap U (htf j)),
    Sigma.desc (fun j : r => ag j.1 ≫ sumMap U (htg j)),
    Sigma.hom_ext _ _ fun j => ?_, Sigma.hom_ext _ _ fun j => ?_⟩
  · rw [Sigma.ι_comp_desc_assoc, Category.assoc, sumMap_sumι, haf]
    simp [sumι]
  · rw [Sigma.ι_comp_desc_assoc, Category.assoc, sumMap_sumι, hag]
    simp [sumι]

private def finiteSumIso (U : I → D) (t : Finset I) :
    (∐ fun i : Fin (Fintype.card t) => U ((Fintype.equivFin t).symm i).1) ≅ sumObj U t :=
  Sigma.reindex (Fintype.equivFin t).symm (fun i : t => U i.1)

private def finiteCoequalizerIso (t : Finset I) (r : Finset K)
    (a b : sumObj V r ⟶ sumObj U t) :
    coequalizer ((finiteSumIso V r).hom ≫ a ≫ (finiteSumIso U t).inv)
      ((finiteSumIso V r).hom ≫ b ≫ (finiteSumIso U t).inv) ≅ coequalizer a b :=
  HasColimit.isoOfNatIso (parallelPairIso _ _ a b (finiteSumIso V r) (finiteSumIso U t)
    (by simp) (by simp))

end
end FiniteSupport

private theorem finite_factor
    {J : GrothendieckTopology C} {I : Type max u v}
    [HasColimitsOfSize.{max u v, max u v} (Sheaf J (Type max u v))]
    [HasFiniteColimits (Sheaf J (Type max u v))]
    (A : I → Sheaf J (Type max u v)) {X : Sheaf J (Type max u v)}
    (hX : Sheaf.IsQuasiCompact X) (f : X ⟶ ∐ A) :
    ∃ t : Finset I, ∃ a : X ⟶ FiniteSupport.sumObj A t,
      a ≫ FiniteSupport.sumι A t = f := by
  classical
  obtain ⟨T, hT, a, ha⟩ := exists_factor_through_finite_subcoproduct hX f
  obtain ⟨t, ht⟩ := hT.exists_finset
  obtain rfl : (↑t : Set I) = T := Set.ext ht
  exact ⟨t, a, ha⟩

attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
/-- **Stacks Project, Tag 093C (1).** Under conditions (1) and (2) of Situation 0937,
every sheaf of sets is a filtered colimit of coequalizers between finite coproducts of
sheafified representables of distinguished objects. -/
@[stacks 093C "part (1), sheaves of sets"]
theorem isFilteredColimit_of_hasEnoughQuasiCompactObjects
    (S : QuasiCompactObjectsSituation C)
    (hEnough : S.HasEnoughObjects) (hqc : S.ObjectsAreQuasiCompact)
    (F : Sheaf S.topology (Type max u v)) :
    ∃ (I : Type max u v) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf S.topology (Type max u v))
      (ι : D ⟶ (Functor.const I).obj F),
      ∃ (_ : IsColimit (Cocone.mk F ι)),
        ∀ i, HasFiniteRepresentableCoequalizerPresentation S (D.obj i) := by
  classical
  let : HasColimitsOfSize.{max u v, max u v} (Sheaf S.topology (Type max u v)) :=
    CategoryTheory.Sheaf.instHasColimitsOfSize
  let : HasFiniteColimits (Sheaf S.topology (Type max u v)) :=
    CategoryTheory.Sheaf.instHasFiniteColimits
  obtain ⟨I₀, J₀, U, V, hU, hV, f, g, ⟨e⟩⟩ :=
    exists_coproduct_coequalizer_presentation S hEnough F
  let A := fun i => (Sheaf.sheafifiedYoneda S.topology).obj (U i)
  let B := fun j => (Sheaf.sheafifiedYoneda S.topology).obj (V j)
  have hc (j) : Sheaf.IsQuasiCompact (B j) :=
    (GrothendieckTopology.isQuasiCompactObject_iff_isQuasiCompact_sheafifiedYoneda
      S.topology (V j)).mp (hqc _ (hV j))
  have hf (r) : ∃ t, FiniteSupport.Supported A B f g t r :=
    FiniteSupport.supported_of_finite_factors A B f g
      (fun j => finite_factor A (hc j) (Sigma.ι B j ≫ f))
      (fun j => finite_factor A (hc j) (Sigma.ι B j ≫ g)) r
  let I := FiniteSupport.SupportIndex A B f g
  let : IsDirectedOrder I := FiniteSupport.supportIndex_directed A B f g hf
  let : Nonempty I := by
    obtain ⟨x, _, _⟩ := FiniteSupport.exists_support_above A B f g hf ∅ ∅
    exact ⟨x⟩
  let D := FiniteSupport.relDiagram A B f g
  let c₀ := FiniteSupport.relCocone A B f g
  let ι : D ⟶ (Functor.const I).obj F := {
    app := fun x => c₀.ι.app x ≫ e.hom
    naturality := by
      intro x y h
      dsimp [D]
      simp only [Category.comp_id]
      exact congrArg (fun k => k ≫ e.hom) (c₀.w h) }
  refine ⟨I, inferInstance, inferInstance, D, ι,
    (FiniteSupport.relCoconeIsColimit A B f g hf).ofIsoColimit (Cocone.ext e fun _ => rfl),
    fun x => ?_⟩
  let t := x.1.1
  let r := x.1.2
  exact ⟨Fintype.card t, Fintype.card r,
    (fun i => U ((Fintype.equivFin t).symm i).1),
    (fun j => V ((Fintype.equivFin r).symm j).1),
    (fun i => hU _), (fun j => hV _), _, _, ⟨FiniteSupport.finiteCoequalizerIso A B t r
      (FiniteSupport.relF A B f g x) (FiniteSupport.relG A B f g x)⟩⟩


end Site

section Space

variable {X : Type u} [TopologicalSpace X]

private lemma opensSite_isQuasiCompactObject_of_isCompact (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    (Opens.grothendieckTopology (TopCat.of X)).IsQuasiCompactObject U := by
  intro 𝒰 h𝒰
  obtain ⟨F, hF⟩ := hU.elim_finite_subcover (fun i => (𝒰.X i : Set X))
    (fun i => (𝒰.X i).isOpen) (by
      intro x hx
      change ∀ y ∈ U, ∃ (V : Opens X) (f : V ⟶ U), 𝒰.sieve₀ f ∧ y ∈ V at h𝒰
      obtain ⟨V, f, hf, hxV⟩ := h𝒰 x hx
      obtain ⟨i, g, hi⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
      exact Set.mem_iUnion.mpr ⟨i, g.le hxV⟩)
  let 𝒱 := 𝒰.restrictIndex (fun i : F => i.1)
  refine ⟨𝒱,
    ⟨fun i => i.1, fun _ => 𝟙 _, ?_⟩, ?_, ?_⟩
  · intro i
    change 𝟙 _ ≫ 𝒰.f i.1 = 𝒰.f i.1
    simp
  · change ∀ x ∈ U, ∃ (V : Opens X) (f : V ⟶ U), 𝒱.sieve₀ f ∧ x ∈ V
    intro x hx
    obtain ⟨i, hiF, hxi⟩ := Set.mem_iUnion₂.mp (hF hx)
    exact ⟨𝒰.X i, 𝒰.f i, 𝒱.sieve₀_f ⟨i, hiF⟩, hxi⟩
  · exact Set.Finite.subset (Set.toFinite F) (by rintro i ⟨j, rfl⟩; exact j.2)

private lemma opensSite_hasEnoughBasisObjects (B : Set (Opens X))
    (hBasis : IsTopologicalBasis ((fun U : Opens X ↦ (U : Set X)) '' B)) :
    (⟨Opens.grothendieckTopology (TopCat.of X), B⟩ :
      QuasiCompactObjectsSituation (Opens X)).HasEnoughObjects := by
  intro U
  let I := {V : Opens X // V ∈ B ∧ V ≤ U}
  let 𝒰 : PreZeroHypercover U :=
    ⟨I, fun i => i.1, fun i => homOfLE i.2.2⟩
  refine ⟨𝒰, ?_, fun i => i.2.1⟩
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨W, ⟨V, hVB, rfl⟩, hxW, hWU⟩ := hBasis.exists_subset_of_mem_open hx U.2
  exact ⟨V, homOfLE hWU, 𝒰.sieve₀_f ⟨V, hVB, hWU⟩, hxW⟩

private noncomputable def opensRepresentableIsoExtendedPUnit (U : Opens X) :
    (TopCat.Presheaf.extendByInitial (X := TopCat.of X) (C := Type u) U
      ((Functor.const (Opens (TopCat.Presheaf.ExtensionByInitial.sp
        (X := TopCat.of X) U))ᵒᵖ).obj PUnit)) ≅
      (CategoryTheory.uliftYoneda.{u, u, u} (C := Opens X)).obj U := by
  classical
  letI : Category.{u, u} (Opens X) := inferInstance
  refine NatIso.ofComponents (fun V => ?_) ?_
  · let e : (if h : V.unop ≤ U then PUnit.{u + 1} else ⊥_ (Type u)) ≃
        ULift.{u, u} (V.unop ⟶ U) := by
      by_cases h : V.unop ≤ U
      · letI : Subsingleton (V.unop ⟶ U) := inferInstance
        letI : Unique (ULift.{u, u} (V.unop ⟶ U)) := {
          toInhabited := ⟨ULift.up.{u, u} (homOfLE h)⟩
          uniq := fun a => congrArg (ULift.up.{u, u})
            (Subsingleton.elim a.down (homOfLE h)) }
        simp only [dite_eq_left h]
        exact Equiv.ofUnique PUnit (ULift (V.unop ⟶ U))
      · haveI : IsEmpty (ULift (V.unop ⟶ U)) := ⟨fun f => h f.down.le⟩
        haveI : IsEmpty (⊥_ (Type u)) := ⟨fun z => by
          have hi : IsInitial (⊥_ (Type u)) := initialIsInitial
          exact PEmpty.elim ((hi.to PEmpty.{u + 1}) z)⟩
        simp only [dite_eq_right h]
        exact (Equiv.equivEmpty _).trans (Equiv.equivEmpty _).symm
    simpa [TopCat.Presheaf.extendByInitial, TopCat.Presheaf.ExtensionByInitial.obj,
      CategoryTheory.uliftYoneda, CategoryTheory.yoneda, Functor.comp_obj,
      Functor.const_obj_obj] using Equiv.toIso e
  · intro V W f
    ext x
    let : Subsingleton (ULift.{u, u} (W.unop ⟶ U)) := inferInstance
    exact Subsingleton.elim _ _

private noncomputable def extendedPUnitIsoSheafifiedYoneda (U : Opens X) :
    extendedConstantSheaf U PUnit ≅
      (CategoryTheory.Sheaf.sheafifiedYoneda
        (Opens.grothendieckTopology (TopCat.of X))).obj U := by
  letI : Category (TopCat.Sheaf (Type u) (TopCat.of X)) :=
    (inferInstance : Category (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of X)) (Type u)))
  let XU := TopCat.Presheaf.ExtensionByInitial.sp (X := TopCat.of X) U
  let JU := Opens.grothendieckTopology XU
  let Q : TopCat.Sheaf (Type u) XU :=
    CategoryTheory.Sheaf.terminal JU Types.isTerminalPUnit
  have hQ : Q ≅ constantSheafOnSpace XU (Type u) PUnit :=
    CategoryTheory.sheafificationIso Q
  let hpre := (CategoryTheory.sheafToPresheaf JU (Type u)).mapIso hQ
  let hext := (TopCat.Presheaf.extendByInitialFunctor (X := TopCat.of X) U).mapIso hpre.symm
  let hrep := opensRepresentableIsoExtendedPUnit U
  let h :=
    (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology (TopCat.of X))
      (Type u)).mapIso (hext ≪≫ hrep)
  refine ⟨h.hom, h.inv, ?_, ?_⟩ <;> apply (TopCat.Sheaf.forget (Type u) (TopCat.of X)).map_injective
  · exact congrArg (fun f => f.hom) h.hom_inv_id
  · exact congrArg (fun f => f.hom) h.inv_hom_id

private theorem exists_coequalizer_iso_of_object_isos {C : Type*} [Category C]
    [HasColimitsOfShape WalkingParallelPair C]
    {X Y X' Y' G : C} {f g : X ⟶ Y} (eX : X' ≅ X) (eY : Y' ≅ Y)
    (h : Nonempty (coequalizer f g ≅ G)) :
    ∃ f' g' : X' ⟶ Y', Nonempty (coequalizer f' g' ≅ G) := by
  classical
  obtain ⟨eG⟩ := h
  let f' := eX.hom ≫ f ≫ eY.inv
  let g' := eX.hom ≫ g ≫ eY.inv
  let cOld : Cofork f g := Cofork.ofπ (coequalizer.π f g) (coequalizer.condition f g)
  let hcOld : IsColimit cOld := coequalizerIsCoequalizer f g
  let cNew : Cofork f' g' :=
    Cofork.ofπ (eY.hom ≫ coequalizer.π f g) (by
      dsimp [f', g']
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
        congrArg (fun k => eX.hom ≫ k) (coequalizer.condition f g))
  have hcNew : IsColimit cNew :=
    Cofork.isColimitOfIsos cOld hcOld cNew eX.symm eY.symm (Iso.refl _)
  exact ⟨f', g', ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hcNew ≪≫ eG⟩⟩

/-- Every sheaf of sets on a space admitting a basis of quasi-compact opens is
a filtered colimit of sheaves with finite basis coequalizer presentations. -/
@[stacks 0CAI]
theorem isFilteredColimit_of_hasCompactBasis (B : Set (Opens X))
    (hBasis : IsTopologicalBasis ((fun U : Opens X ↦ (U : Set X)) '' B))
    (hB : ∀ U ∈ B, IsCompact (U : Set X))
    (F : TopCat.Sheaf (Type u) (TopCat.of X)) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ TopCat.Sheaf (Type u) (TopCat.of X))
      (ι : D ⟶ (Functor.const J).obj F),
      ∃ (_ : IsColimit (Cocone.mk F ι)),
        ∀ j, HasFiniteBasisCoequalizerPresentation B (D.obj j) := by
  let S : QuasiCompactObjectsSituation (Opens X) :=
    ⟨Opens.grothendieckTopology (TopCat.of X), B⟩
  obtain ⟨J, hJ, hFiltered, D, ι, hColim, hPresentation⟩ :=
    isFilteredColimit_of_hasEnoughQuasiCompactObjects S
      (opensSite_hasEnoughBasisObjects B hBasis)
      (fun U hU => opensSite_isQuasiCompactObject_of_isCompact U (hB U hU)) F
  refine ⟨J, hJ, hFiltered, D, ι, hColim, fun j => ?_⟩
  let : HasFiniteColimits (TopCat.Sheaf (Type u) (TopCat.of X)) :=
    CategoryTheory.Sheaf.instHasFiniteColimits
  obtain ⟨n, m, U, V, hU, hV, ⟨f, g, hG⟩⟩ := hPresentation j
  obtain ⟨f', g', hIso⟩ :=
    exists_coequalizer_iso_of_object_isos
      (Sigma.mapIso (fun b : Fin m => (extendedPUnitIsoSheafifiedYoneda (V b)).symm)).symm
      (Sigma.mapIso (fun a : Fin n => (extendedPUnitIsoSheafifiedYoneda (U a)).symm)).symm hG
  exact ⟨n, m, U, V, fun _ => PUnit, fun _ => PUnit, hU, hV,
    fun _ => inferInstance, fun _ => inferInstance, f', g', hIso⟩

/-- On a prespectral space the quasi-compact opens form a basis, in the form in which
`isFilteredColimit_of_hasCompactBasis` asks for one: as the image of a set of `Opens X`
under the coercion to `Set X`. -/
theorem isTopologicalBasis_image_isCompact [PrespectralSpace X] :
    IsTopologicalBasis
      ((fun U : Opens X ↦ (U : Set X)) '' {U : Opens X | IsCompact (U : Set X)}) := by
  have he : (fun U : Opens X ↦ (U : Set X)) '' {U : Opens X | IsCompact (U : Set X)} =
      {U : Set X | IsOpen U ∧ IsCompact U} := by
    ext V
    refine ⟨?_, ?_⟩
    · rintro ⟨U, hU, rfl⟩
      exact ⟨U.2, hU⟩
    · rintro ⟨hopen, hcomp⟩
      exact ⟨⟨V, hopen⟩, hcomp, rfl⟩
  exact he ▸ PrespectralSpace.isTopologicalBasis

/-- On a prespectral space every sheaf of sets is a filtered colimit of sheaves presented by
the quasi-compact opens.  This is `isFilteredColimit_of_hasCompactBasis` with its basis
hypotheses discharged, so the pieces of the diagram satisfy the hypothesis of
`exists_pullback_from_finite_sober_of_hasFiniteBasisCoequalizerPresentation` verbatim. -/
theorem isFilteredColimit_of_prespectralSpace [PrespectralSpace X]
    (F : TopCat.Sheaf (Type u) (TopCat.of X)) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ TopCat.Sheaf (Type u) (TopCat.of X))
      (ι : D ⟶ (Functor.const J).obj F),
      ∃ (_ : IsColimit (Cocone.mk F ι)),
        ∀ j, HasFiniteBasisCoequalizerPresentation
          {U : Opens X | IsCompact (U : Set X)} (D.obj j) :=
  isFilteredColimit_of_hasCompactBasis _ isTopologicalBasis_image_isCompact
    (fun _ hU => hU) F

end Space

end Stacks
