module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.Topology.Order
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksFrontier.CategoryTheory.Sites.Continuous

/-!
# The inverse image of an étale sheaf on the small pro-étale site

Let `S` be a scheme.  The inclusion `u : S_étale → S_proétale` of the small étale category into
the small pro-étale category is a continuous functor of sites, so it defines a morphism of sites
`ε : S_proétale → S_étale`, whose inverse image `ε⁻¹ = u^s` is the sheafification of the left Kan
extension along `u`.  This file computes `ε⁻¹` by a formula: for a sheaf `ℱ` on `S_étale` the rule
sending a pro-étale object `f : Y → S` to `Γ(Y_étale, f_étale⁻¹ℱ)` is a sheaf on `S_proétale`, and
it is `ε⁻¹ℱ`.

The rule is realized as the restriction to `S_proétale` of the inverse image of `ℱ` on *all*
`S`-schemes for the big étale topology localized at `S`.

## Main definitions

* `AlgebraicGeometry.Scheme.bigEtaleInverseImage` is the inverse image of a sheaf on the small
  étale site of `S` along the inclusion of the small étale category into all `S`-schemes.
* `AlgebraicGeometry.Scheme.etaleSectionsPresheaf` is the rule of the title, as a presheaf on the
  small pro-étale category: the restriction of `AlgebraicGeometry.Scheme.bigEtaleInverseImage`
  along the forgetful functor of the small pro-étale site.
* `AlgebraicGeometry.Scheme.etaleSectionsSheaf` is that rule with its pro-étale sheaf structure.
* `CategoryTheory.Functor.sheafPullbackRestriction` is the abstract form of this construction: for
  `a : C ⥤ D` and a fully faithful cocontinuous `i : D ⥤ E` with `a ⋙ i` continuous, it is the
  functor `Sh(C) ⥤ Sh(D)` restricting the inverse image along `a ⋙ i` back along `i`, available
  once that restriction is known to be a sheaf.

## Main results

* `AlgebraicGeometry.Scheme.etaleSectionsPresheaf_isSheaf`: the rule is a sheaf on the small
  pro-étale site.
* `AlgebraicGeometry.Scheme.etaleSectionsSheafAdjunction`: the rule is left adjoint to `ε_*`.
* `AlgebraicGeometry.Scheme.proetaleInverseImageIsoEtaleSectionsSheaf`: the canonical isomorphism
  `ε⁻¹ ≅` the rule.
* `AlgebraicGeometry.Scheme.etaleSectionsFormulaIso` and
  `AlgebraicGeometry.Scheme.proetaleInverseImageSectionsIso`: the sections of the rule, and hence
  of `ε⁻¹ℱ`, at a pro-étale object `f : Y → S` are `Γ(Y_étale, f_étale⁻¹ℱ)`.
* `AlgebraicGeometry.Scheme.bigEtaleInverseImage_isSheaf_fpqc`: the big étale inverse image of an
  étale sheaf is an fpqc sheaf on `S`-schemes.
* `CategoryTheory.Functor.sheafPullbackRestrictionAdjunction` and
  `CategoryTheory.Functor.sheafPullbackCompRestrictionIso`: the abstract adjunction and the
  resulting identification of the inverse image along `a` with
  `CategoryTheory.Functor.sheafPullbackRestriction`.

## Implementation notes

The small sites are Mathlib's: `AlgebraicGeometry.Scheme.Etale` with
`AlgebraicGeometry.Scheme.smallEtaleTopology`, and `AlgebraicGeometry.Scheme.ProEt` with
`AlgebraicGeometry.Scheme.ProEt.topology`.  The coefficient universe is independent of the
universe of the scheme and large enough for the Kan extensions: sheaves of types valued in
`Type (max (u + 1) v)`, the objects of both small categories living in `Type (u + 1)`.

## References

* [Stacks Project, Tag 0GLZ](https://stacks.math.columbia.edu/tag/0GLZ)
* [Stacks Project, Tag 098A](https://stacks.math.columbia.edu/tag/098A)
* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

/-! ### Generic plumbing on sites -/

namespace CategoryTheory

/-- Evaluating the left Kan extension of type valued presheaves at an object of the target
is the colimit over the costructured arrows above that object, naturally in the presheaf. -/
private def lanCompEvaluationIsoColimOfTypes.{s₁, s₂, x₁, x₂, y}
    {A : Type x₁} [Category.{s₁} A] {D : Type x₂} [Category.{s₂} D]
    (F : A ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) (Type y)] :
    F.lan ⋙ (evaluation D (Type y)).obj X ≅
      (Functor.whiskeringLeft _ _ (Type y)).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G => F.leftKanExtensionObjIsoColimit G X)
    (fun {G₁ G₂} φ => by
      apply (F.isPointwiseLeftKanExtensionLeftKanExtensionUnit G₁ X).hom_ext
      intro T
      simp [Functor.lan])

/-- A representably flat functor has a left exact left Kan extension on presheaves of types.
This is `CategoryTheory.Functor.lan_preservesFiniteLimits_of_flat` with the smallness
restrictions on source and target replaced by hypotheses. -/
private lemma lanPreservesFiniteLimitsOfTypes.{s₁, s₂, x₁, x₂, y}
    {A : Type x₁} [Category.{s₁} A] {D : Type x₂} [Category.{s₂} D] (F : A ⥤ D)
    [RepresentablyFlat F]
    [∀ X : Dᵒᵖ, Small.{y} (CostructuredArrow F.op X)]
    [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow F.op X) (Type y)] :
    PreservesFiniteLimits (F.op.lan : (Aᵒᵖ ⥤ Type y) ⥤ (Dᵒᵖ ⥤ Type y)) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{y}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro X
  have hfiltered : IsFiltered (CostructuredArrow F.op X) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (Opposite.unop X))
  exact preservesLimitsOfShape_of_natIso
    (lanCompEvaluationIsoColimOfTypes F.op X).symm

/-- A morphism from `X` into the equalizer of two maps out of a terminal object exists exactly
when the two composites with the unique map `X ⟶ T` agree. -/
private lemma nonempty_hom_equalizer_iff {C : Type*} [Category* C]
    {T F : C} (hT : IsTerminal T) (s t : T ⟶ F) [HasEqualizer s t] (X : C) :
    Nonempty (X ⟶ equalizer s t) ↔ hT.from X ≫ s = hT.from X ≫ t := by
  constructor
  · rintro ⟨f⟩
    rw [← hT.hom_ext (f ≫ equalizer.ι s t) (hT.from X), Category.assoc,
      equalizer.condition, ← Category.assoc]
  · intro h
    exact ⟨equalizer.lift (hT.from X) h⟩

/-- The unit of sheafification is a locally surjective map of presheaves. -/
private lemma locallySurjective_toSheafify.{x₁, s₁, y}
    {C : Type x₁} [Category.{s₁} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type y)] (R : Cᵒᵖ ⥤ Type y) :
    Presheaf.IsLocallySurjective J (toSheafify J R) := by
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  set G := Subfunctor.sheafify J (Subfunctor.range (toSheafify J R))
  have hFsheaf : Presheaf.IsSheaf J (sheafify J R) :=
    ((presheafToSheaf J (Type y)).obj R).property
  have hGsheaf : Presheaf.IsSheaf J G.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      ((Subfunctor.range (toSheafify J R)).sheafify_isSheaf
        ((isSheaf_iff_isSheaf_of_type J _).mp hFsheaf))
  have hfac : Subfunctor.toRangeSheafify J (toSheafify J R) ≫ G.ι = toSheafify J R := by
    ext X x
    rfl
  rw [Subfunctor.eq_top_iff_isIso]
  have : IsSplitEpi G.ι := by
    refine IsSplitEpi.mk
      ⟨⟨sheafifyLift J (Subfunctor.toRangeSheafify J (toSheafify J R)) hGsheaf, ?_⟩⟩
    refine sheafify_hom_ext J _ _ hFsheaf ?_
    rw [Category.comp_id, ← Category.assoc, toSheafify_sheafifyLift, hfac]
  exact isIso_of_mono_of_isSplitEpi G.ι

/-- Two members of a family of elements indexed by equal arrows agree. -/
private lemma family_apply_eq {C : Type*} [Category* C] {T Z : C}
    {P : Cᵒᵖ ⥤ Type*} {R : Presieve T} (x : Presieve.FamilyOfElements P R)
    {f g : Z ⟶ T} (h : f = g) (hf : R f) (hg : R g) : x f hf = x g hg := by
  subst g
  rfl

/-- Restriction along a cocontinuous functor followed by sheafification is left adjoint to the
cocontinuous pushforward. -/
public def Functor.restrictionSheafificationAdjunction
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (i : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (A : Type*) [Category* A] [i.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ A, i.op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify J A] :
    (sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj i.op ⋙
      presheafToSheaf J A) ⊣ i.sheafPushforwardCocontinuous A J K :=
  ((i.op.ranAdjunction A).comp (sheafificationAdjunction J A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K A) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

section PullbackRestriction

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  (a : C ⥤ D) (i : D ⥤ E) [i.Full] [i.Faithful]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (A : Type*) [Category* A]
  [i.IsCocontinuous K L] [(a ⋙ i).IsContinuous J L]
  [∀ F : Dᵒᵖ ⥤ A, i.op.HasPointwiseRightKanExtension F]
  [∀ F : Cᵒᵖ ⥤ A, a.op.HasLeftKanExtension F]
  [∀ F : Cᵒᵖ ⥤ A, (a ⋙ i).op.HasLeftKanExtension F]
  [HasWeakSheafify K A] [HasWeakSheafify L A]
  (h : ∀ F : Sheaf J A, Presheaf.IsSheaf K
    (i.op ⋙ ((Functor.sheafPullbackConstruction.sheafPullback (a ⋙ i) A J L).obj F).obj))

/-- The functor on sheaves sending `F` to the restriction along `i` of the inverse image of `F`
along `a ⋙ i`, under the hypothesis `h` that this restriction is a `K`-sheaf. -/
public def Functor.sheafPullbackRestriction : Sheaf J A ⥤ Sheaf K A :=
  ObjectProperty.lift (Presheaf.IsSheaf K (A := A))
    (Functor.sheafPullbackConstruction.sheafPullback (a ⋙ i) A J L ⋙
      sheafToPresheaf L A ⋙ (Functor.whiskeringLeft _ _ _).obj i.op) h

/-- The right adjoint shared by the two descriptions of the inverse image along `a`. -/
public abbrev Functor.sheafPullbackRestrictionRightAdjoint : Sheaf K A ⥤ Sheaf J A :=
  i.sheafPushforwardCocontinuous A K L ⋙ (a ⋙ i).sheafPushforwardContinuous A J L

include h in
/-- `Functor.sheafPullbackRestriction` is left adjoint to
`Functor.sheafPullbackRestrictionRightAdjoint`. -/
public def Functor.sheafPullbackRestrictionAdjunctionAux :
    Functor.sheafPullbackRestriction a i J K L A h ⊣
      Functor.sheafPullbackRestrictionRightAdjoint a i J K L A :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (a ⋙ i) A J L).comp
      (Functor.restrictionSheafificationAdjunction i K L A)).ofNatIsoLeft
    (Functor.isoWhiskerLeft (Functor.sheafPullbackRestriction a i J K L A h)
      (asIso (sheafificationAdjunction K A).counit))

/-- Full faithfulness of `i` identifies `Functor.sheafPullbackRestrictionRightAdjoint` with
restriction along `a`, the `ε_*` of the morphism of sites. -/
public def Functor.sheafPullbackRestrictionRightAdjointIso [a.IsContinuous J K] :
    Functor.sheafPullbackRestrictionRightAdjoint a i J K L A ≅
      a.sheafPushforwardContinuous A J K :=
  Functor.fullyFaithfulCancelRight (sheafToPresheaf J A)
    (Functor.isoWhiskerLeft (sheafToPresheaf K A)
      (Functor.isoWhiskerRight (asIso (i.op.ranAdjunction A).counit)
        ((Functor.whiskeringLeft _ _ _).obj a.op)))

include h in
/-- **The adjunction.** `Functor.sheafPullbackRestriction` is left adjoint to restriction along
`a`. -/
public def Functor.sheafPullbackRestrictionAdjunction [a.IsContinuous J K] :
    Functor.sheafPullbackRestriction a i J K L A h ⊣ a.sheafPushforwardContinuous A J K :=
  (Functor.sheafPullbackRestrictionAdjunctionAux a i J K L A h).ofNatIsoRight
    (Functor.sheafPullbackRestrictionRightAdjointIso a i J K L A)

include h in
/-- The inverse image along `a` is isomorphic to `Functor.sheafPullbackRestriction`, through the
canonical comparison of two left adjoints of restriction along `a`. -/
public def Functor.sheafPullbackCompRestrictionIso [a.IsContinuous J K] :
    Functor.sheafPullbackConstruction.sheafPullback a A J K ≅
      Functor.sheafPullbackRestriction a i J K L A h :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous a A J K).leftAdjointUniq
    (Functor.sheafPullbackRestrictionAdjunction a i J K L A h)

end PullbackRestriction

end CategoryTheory

/-! ### The two forgetful functors of the small sites -/

namespace AlgebraicGeometry

/-- The forgetful functor from the small étale category to `S`-schemes is continuous. -/
public lemma Scheme.Etale.forget_isContinuous (S : Scheme.{u}) :
    (Scheme.Etale.forget S).IsContinuous S.smallEtaleTopology (Scheme.etaleTopology.over S) := by
  let : RepresentablyFlat (Scheme.Etale.forget S) :=
    flat_of_preservesFiniteLimits (Scheme.Etale.forget S)
  rw [Functor.isContinuous_iff_coverPreserving]
  exact (Scheme.Etale.forget S).coverPreserving_restrictedTopology _

attribute [local instance] Scheme.Etale.forget_isContinuous

/-- The forgetful functor from the small étale category to `S`-schemes is cocontinuous. -/
public lemma Scheme.Etale.forget_isCocontinuous (S : Scheme.{u}) :
    (Scheme.Etale.forget S).IsCocontinuous S.smallEtaleTopology
      (Scheme.etaleTopology.over S) := by
  let : (Scheme.Etale.forget S).IsContinuous
      ((Scheme.Etale.forget S).restrictedTopology (Scheme.etaleTopology.over S))
      (Scheme.etaleTopology.over S) := Scheme.Etale.forget_isContinuous S
  show (Scheme.Etale.forget S).IsCocontinuous
    ((Scheme.Etale.forget S).restrictedTopology (Scheme.etaleTopology.over S)) _
  infer_instance

attribute [local instance] Scheme.Etale.forget_isCocontinuous

/-- The forgetful functor from the small pro-étale category to `S`-schemes is cocontinuous for
the big étale topology localized at `S`: an étale covering is a pro-étale covering. -/
public lemma Scheme.ProEt.forget_isCocontinuous (S : Scheme.{u}) :
    (Scheme.ProEt.forget S).IsCocontinuous (Scheme.ProEt.topology S)
      (Scheme.etaleTopology.over S) := by
  have hle : Scheme.etaleTopology.over S ≤ Scheme.proetaleTopology.over S :=
    GrothendieckTopology.over_mono Scheme.etaleTopology_le_proetaleTopology S
  let : (Scheme.ProEt.forget S).IsContinuous
      ((Scheme.ProEt.forget S).restrictedTopology (Scheme.proetaleTopology.over S))
      (Scheme.proetaleTopology.over S) := by
    rw [Functor.isContinuous_iff_coverPreserving]
    exact (Scheme.ProEt.forget S).coverPreserving_restrictedTopology _
  constructor
  intro X R hR
  rw [Scheme.ProEt.topology_eq_inducedTopology,
    ← Functor.restrictedTopology_eq_inducedTopology]
  exact Functor.IsCocontinuous.cover_lift (hle _ hR)

attribute [local instance] Scheme.ProEt.forget_isCocontinuous

/-- An fpqc sheaf on `S`-schemes restricts to a sheaf on the small pro-étale site. -/
private theorem proetale_restrict_fpqc_sheaf (S : Scheme.{u})
    (P : (Over S)ᵒᵖ ⥤ Type (max (u + 1) v))
    (hP : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) P) :
    Presheaf.IsSheaf (Scheme.ProEt.topology S)
      ((Scheme.ProEt.forget S).op ⋙ P) := by
  have hle : Scheme.proetaleTopology.over S ≤ Scheme.fpqcTopology.over S :=
    GrothendieckTopology.over_mono Scheme.proetaleTopology_le_fpqcTopology S
  have hP' : Presheaf.IsSheaf (Scheme.proetaleTopology.over S) P :=
    Presheaf.IsSheaf.of_le hle hP
  exact (Scheme.ProEt.forget S).op_comp_isSheaf_of_isSheaf
    (Scheme.ProEt.topology S) (Scheme.proetaleTopology.over S) P hP'

/-! ### Subterminal étale sheaves are representable by opens -/

/-- A sheaf on the small étale site all of whose values are subsingletons is nonempty exactly
on the étale objects whose image lies in a fixed open of `S`. -/
private lemma subterminal_etale_open (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type v))
    (hF : ∀ U, Subsingleton (F.obj.obj (Opposite.op U))) :
    ∃ W : S.Opens, ∀ U : S.Etale,
      Nonempty (F.obj.obj (Opposite.op U)) ↔ Set.range U.hom ⊆ (W : Set S) := by
  classical
  let I := {U : S.Etale // Nonempty (F.obj.obj (Opposite.op U))}
  let W : S.Opens := ⨆ i : I, ⟨Set.range i.1.hom, (i.1.hom.isOpenMap).isOpen_range⟩
  refine ⟨W, fun U => ⟨?_, ?_⟩⟩
  · intro h
    exact fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, h⟩, hx⟩
  · intro hU
    let V (i : I) : S.Etale :=
      MorphismProperty.Over.mk ⊤ (pullback.fst U.hom i.1.hom ≫ U.hom) inferInstance
    let a (i : I) : V i ⟶ U := MorphismProperty.Over.homMk (pullback.fst _ _) (by rfl)
    let b (i : I) : V i ⟶ i.1 := MorphismProperty.Over.homMk
      (pullback.snd _ _) (by
        simp only [V]
        exact (pullback.condition (f := U.hom) (g := i.1.hom)).symm)
    have hcover : Sieve.ofArrows V a ∈ S.smallEtaleTopology U := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU (Set.mem_range_self x))
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      show x ∈ Set.range (pullback.fst U.hom i.1.hom)
      rw [Scheme.Pullback.range_fst]
      exact hi
    let s (i : I) := F.obj.map (b i).op (Classical.choice i.2)
    have hs : Presieve.Arrows.Compatible F.obj a s := by
      intro i j Z p q hpq
      exact @Subsingleton.elim _ (hF Z) _ _
    have H : Presieve.IsSheafFor F.obj (Presieve.ofArrows V a) :=
      (Presieve.isSheafFor_iff_generate _).mpr (F.property.isSheafFor _ hcover)
    obtain ⟨s, _, _⟩ := (Presieve.isSheafFor_arrows_iff F.obj a).mp H s hs
    exact ⟨s⟩

/-- A subterminal sheaf on the small étale site has subsingleton values. -/
private lemma etale_subterminal_values (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (hF : IsSubterminal F)
    (U : S.Etale) : Subsingleton (F.obj.obj (Opposite.op U)) := by
  let e : ((presheafToSheaf S.smallEtaleTopology (Type (max (u + 1) v))).obj
      (uliftYoneda.{max (u + 1) v}.obj U) ⟶ F) ≃ F.obj.obj (Opposite.op U) :=
    ((sheafificationAdjunction _ _).homEquiv _ _).trans uliftYonedaEquiv
  exact ⟨fun x y => e.symm.injective (hF _ _)⟩

/-- An `S`-scheme admits a morphism to an open of `S` exactly when its image lies in that
open. -/
private lemma over_open_hom_iff (S : Scheme.{u}) (W : S.Opens) (U : Over S) :
    Nonempty (U ⟶ Over.mk W.ι) ↔ Set.range U.hom ⊆ (W : Set S) := by
  constructor
  · rintro ⟨f⟩ x ⟨y, rfl⟩
    have h := congrArg (fun k : U.left ⟶ S => k y) f.w
    change W.ι (f.left y) = U.hom y at h
    rw [← h]
    exact (f.left y).property
  · intro h
    have h' : Set.range U.hom ⊆ Set.range W.ι := by simpa using h
    let g : U.left ⟶ (W : Scheme.{u}) := IsOpenImmersion.lift W.ι U.hom h'
    have hg : g ≫ W.ι = U.hom := IsOpenImmersion.lift_fac _ _ _
    exact ⟨CategoryTheory.Over.homMk g hg⟩

/-- An étale object admits a morphism to an open of `S` exactly when its image lies in that
open. -/
private lemma etale_open_hom_iff (S : Scheme.{u}) (W : S.Opens) (U : S.Etale) :
    Nonempty (U ⟶ MorphismProperty.Over.mk ⊤ W.ι inferInstance) ↔
      Set.range U.hom ⊆ (W : Set S) :=
  Iff.trans ⟨fun ⟨f⟩ => ⟨(Scheme.Etale.forget S).map f⟩,
    fun ⟨g⟩ => ⟨MorphismProperty.Over.homMk g.left g.w⟩⟩
    (over_open_hom_iff S W ((Scheme.Etale.forget S).obj U))

/-- A subterminal sheaf on the small étale site is represented by an open of `S`. -/
private lemma etale_subterminal_representation (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (hF : IsSubterminal F) :
    ∃ W : S.Opens, Nonempty (F.obj ≅ uliftYoneda.{max (u + 1) v}.obj
      (MorphismProperty.Over.mk ⊤ W.ι inferInstance)) := by
  classical
  obtain ⟨W, hW⟩ := subterminal_etale_open S F (etale_subterminal_values S F hF)
  let V : S.Etale := MorphismProperty.Over.mk ⊤ W.ι inferInstance
  have hV (U : S.Etale) : Subsingleton (U ⟶ V) :=
    ⟨fun f g => MorphismProperty.Over.Hom.ext ((cancel_mono W.ι).mp (f.w.trans g.w.symm))⟩
  let e (U : S.Etaleᵒᵖ) : F.obj.obj U ≃ ULift.{max (u + 1) v} (U.unop ⟶ V) := by
    let := etale_subterminal_values S F hF U.unop
    let := hV U.unop
    have h : Nonempty (F.obj.obj U) ↔ Nonempty (ULift.{max (u + 1) v} (U.unop ⟶ V)) :=
      (hW U.unop).trans ((etale_open_hom_iff S W U.unop).symm.trans
        nonempty_ulift.symm)
    exact { toFun := fun x => Classical.choice (h.mp ⟨x⟩)
            invFun := fun x => Classical.choice (h.mpr ⟨x⟩)
            left_inv := fun _ => Subsingleton.elim _ _
            right_inv := fun _ => Subsingleton.elim _ _ }
  refine ⟨W, ⟨NatIso.ofComponents (fun U => (e U).toIso) ?_⟩⟩
  intro U U' f
  ext x
  apply ULift.ext
  exact @Subsingleton.elim _ (hV U'.unop) _ _

/-! ### The inverse image of an étale sheaf on the big étale slice -/

/-- The inverse image of a sheaf on the small étale site of `S` along the inclusion of the
small étale category into all `S`-schemes, carrying the big étale topology localized at `S`. -/
public abbrev Scheme.bigEtaleInverseImage (S : Scheme.{u}) :
    Sheaf S.smallEtaleTopology (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.etaleTopology.over S) (Type (max (u + 1) v)) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.Etale.forget S)
    (Type (max (u + 1) v)) S.smallEtaleTopology (Scheme.etaleTopology.over S)

/-- The inverse image of a subterminal étale sheaf is represented by an open of `S`. -/
private lemma Scheme.bigEtaleInverseImage_subterminal (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (hF : IsSubterminal F) :
    ∃ W : S.Opens, Nonempty (((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj ≅
      uliftYoneda.{max (u + 1) v}.obj (Over.mk W.ι)) := by
  obtain ⟨W, ⟨e⟩⟩ := etale_subterminal_representation S F hF
  let U : S.Etale := MorphismProperty.Over.mk ⊤ W.ι inferInstance
  let J := Scheme.etaleTopology.over S
  let A := Type (max (u + 1) v)
  let Q := uliftYoneda.{max (u + 1) v}.obj (Over.mk W.ι)
  have hQ : Presheaf.IsSheaf J Q := by
    apply Presheaf.IsSheaf.of_le (GrothendieckTopology.over_mono
      (Scheme.etaleTopology_le_proetaleTopology.trans Scheme.proetaleTopology_le_fpqcTopology) S)
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  let := isIso_toSheafify J hQ
  let e' : (Scheme.Etale.forget S).op.lan.obj F.obj ≅ Q :=
    (Scheme.Etale.forget S).op.lan.mapIso e ≪≫
      ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{max (u + 1) v}
        (Scheme.Etale.forget S)).app U).symm
  exact ⟨W, ⟨(sheafToPresheaf J A).mapIso ((presheafToSheaf J A).mapIso e') ≪≫
    (asIso (toSheafify J Q)).symm⟩⟩

/-- Base change of the big étale inverse image: restricting the inverse image of `F` along
`Over.map f` is the big étale inverse image on `X` of the small étale inverse image of `F`. -/
public def Scheme.bigEtaleInverseImage_baseChangeIso {X S : Scheme.{u}} (f : X ⟶ S) :
    Scheme.bigEtaleInverseImage.{u, v} S ⋙
      (Over.map f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S) ≅
    Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} f ⋙
      Scheme.bigEtaleInverseImage.{u, v} X := by
  let A := Type (max (u + 1) v)
  let a := Scheme.Etale.forget S
  let b := Scheme.Etale.forget X
  let c := Stacks.EtaleCohomology.smallEtaleBaseChange f
  let r := Over.pullback f
  let L := Scheme.etaleTopology.over X
  let K := Scheme.etaleTopology.over S
  let : (a ⋙ r).IsContinuous S.smallEtaleTopology L :=
    Functor.isContinuous_comp a r S.smallEtaleTopology K L
  let adjA := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous a A
    S.smallEtaleTopology K
  let adjB := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b A
    X.smallEtaleTopology L
  let adjC := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous c A
    S.smallEtaleTopology X.smallEtaleTopology
  let adjU := (Over.mapPullbackAdj f).sheafPushforwardContinuous (E := A) L K
  letI : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let es : c ⋙ b ≅ a ⋙ r :=
    MorphismProperty.Over.pullbackCompForgetIso (P := @Etale) (Q := ⊤) f
  let e := Functor.sheafPushforwardContinuousComp a r A S.smallEtaleTopology K L ≪≫
    (Functor.sheafPushforwardContinuousComp' es
      A S.smallEtaleTopology X.smallEtaleTopology L).symm
  exact ((adjA.comp adjU).ofNatIsoRight e).leftAdjointUniq (adjC.comp adjB)

/-- Two global sections of the big étale inverse image agree exactly over the `S`-schemes
whose image lies in a fixed open of `S`. -/
private lemma bigEtaleInverseImage_openEq (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (s t : ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.obj (Opposite.op (Over.mk (𝟙 S)))) :
    ∃ W : S.Opens, ∀ X : Over S,
      ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.map (Over.homMk X.hom (by simp)).op s =
        ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.map (Over.homMk X.hom (by simp)).op t ↔
      Set.range X.hom ⊆ (W : Set S) := by
  classical
  let A := Type (max (u + 1) v)
  let J := Scheme.etaleTopology.over S
  let L := Scheme.bigEtaleInverseImage.{u, v} S
  let : J.Subcanonical := GrothendieckTopology.Subcanonical.of_le
    (GrothendieckTopology.over_mono (Scheme.etaleTopology_le_proetaleTopology.trans
      Scheme.proetaleTopology_le_fpqcTopology) S)
  let : RepresentablyFlat (Scheme.Etale.forget S) :=
    flat_of_preservesFiniteLimits (Scheme.Etale.forget S)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.Etale.forget S) A S.smallEtaleTopology J
  let : IsIso adj.unit := Functor.isIso_unit_of_sheafPushforwardContinuous
    (Scheme.Etale.forget S) A S.smallEtaleTopology J adj
  let FF := adj.fullyFaithfulLOfIsIsoUnit
  have : PreservesFiniteLimits L := by
    have : PreservesFiniteLimits ((Scheme.Etale.forget S).op.lan :
        (S.Etaleᵒᵖ ⥤ A) ⥤ _) := lanPreservesFiniteLimitsOfTypes _
    dsimp [L, Scheme.bigEtaleInverseImage]
    infer_instance
  let T := terminal (Sheaf S.smallEtaleTopology A)
  let hT : IsTerminal (L.obj T) := terminalIsTerminal.isTerminalObj L T
  let Y := J.uliftYoneda.{max (u + 1) v}
  let hY : IsTerminal (Y.obj (Over.mk (𝟙 S))) := by
    apply IsTerminal.isTerminalOfObj (sheafToPresheaf J A)
    apply Functor.isTerminal
    intro X
    show IsTerminal (ULift.{max (u + 1) v} (X.unop ⟶ Over.mk (𝟙 S)))
    refine (Types.isTerminalEquivUnique _).symm ?_
    exact { default := ⟨Over.homMk X.unop.hom (by simp)⟩
            uniq := fun x => ULift.ext _ _ (Over.mkIdTerminal.hom_ext _ _) }
  let e := hT.uniqueUpToIso hY
  let s' : T ⟶ F := FF.preimage (e.hom ≫ J.uliftYonedaEquiv.{max (u + 1) v}.symm s)
  let t' : T ⟶ F := FF.preimage (e.hom ≫ J.uliftYonedaEquiv.{max (u + 1) v}.symm t)
  have hE : IsSubterminal (equalizer s' t') := fun Z f g =>
    (cancel_mono (equalizer.ι s' t')).mp (terminal.hom_ext _ _)
  obtain ⟨W, ⟨eW⟩⟩ := Scheme.bigEtaleInverseImage_subterminal S (equalizer s' t') hE
  refine ⟨W, fun X => ?_⟩
  let p : X ⟶ Over.mk (𝟙 S) := Over.homMk X.hom (by simp)
  have hp : hT.from (Y.obj X) ≫ e.hom = Y.map p := hY.hom_ext _ _
  have hnat : ∀ x : (L.obj F).obj.obj (Opposite.op (Over.mk (𝟙 S))),
      Y.map p ≫ J.uliftYonedaEquiv.{max (u + 1) v}.symm x =
        J.uliftYonedaEquiv.{max (u + 1) v}.symm ((L.obj F).obj.map p.op x) :=
    fun x => J.uliftYonedaEquiv_symm_naturality_left p (L.obj F) x
  have heq : hT.from (Y.obj X) ≫ L.map s' = hT.from (Y.obj X) ≫ L.map t' ↔
      (L.obj F).obj.map p.op s = (L.obj F).obj.map p.op t := by
    show hT.from (Y.obj X) ≫ L.map (FF.preimage _) =
      hT.from (Y.obj X) ≫ L.map (FF.preimage _) ↔ _
    rw [FF.map_preimage, FF.map_preimage, ← Category.assoc, ← Category.assoc, hp, hnat, hnat,
      Equiv.apply_eq_iff_eq]
  rw [← heq, ← nonempty_hom_equalizer_iff hT]
  constructor
  · rintro ⟨q⟩
    let q' := q ≫ (PreservesEqualizer.iso L s' t').inv
    have x : ((L.obj (equalizer s' t')).obj.obj (Opposite.op X)) :=
      J.uliftYonedaEquiv.{max (u + 1) v} q'
    exact (over_open_hom_iff S W X).mp ⟨((eW.app (Opposite.op X)).hom x).down⟩
  · intro h
    obtain ⟨q⟩ := (over_open_hom_iff S W X).mpr h
    let x := (eW.app (Opposite.op X)).inv (ULift.up q)
    exact ⟨J.uliftYonedaEquiv.{max (u + 1) v}.symm x ≫ (PreservesEqualizer.iso L s' t').hom⟩

/-! ### fpqc descent for the big étale inverse image -/

/-- Every section of the big étale inverse image is, étale locally, pulled back from a section
over an object of the small étale category. -/
private lemma bigEtaleInverseImage_local_sections (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (T : Over S)
    (s : ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.obj (Opposite.op T)) :
    ∃ E : Scheme.Cover.{u, u} Scheme.etalePrecoverage T.left, ∀ i : E.I₀,
      ∃ (U : S.Etale)
        (k : Over.mk (E.f i ≫ T.hom) ⟶ (Scheme.Etale.forget S).obj U)
        (t : ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.obj
          (Opposite.op ((Scheme.Etale.forget S).obj U))),
        ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.map k.op t =
          ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.map (Over.homMk (E.f i) rfl).op s := by
  let J := Scheme.etaleTopology.over S
  let j := Scheme.Etale.forget S
  let G := j.op.lan.obj F.obj
  let P := ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj
  let η : G ⟶ P := toSheafify J G
  let : Presheaf.IsLocallySurjective J η := locallySurjective_toSheafify J G
  have hcov := Presheaf.imageSieve_mem J η s
  rw [GrothendieckTopology.mem_over_iff] at hcov
  obtain ⟨E, hE⟩ := Scheme.mem_grothendieckTopology_iff.mp hcov
  refine ⟨E, fun i => ?_⟩
  have hi := hE _ _ (Presieve.ofArrows.mk i)
  rw [Sieve.overEquiv_iff] at hi
  obtain ⟨x, hx⟩ := hi
  obtain ⟨U, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit j.op F.obj
      (Opposite.op (Over.mk (E.f i ≫ T.hom)))) x
  refine ⟨U.left.unop, U.hom.unop,
    η.app _ (((j.op.lanUnit.app F.obj).app U.left) t), ?_⟩
  rw [← hx, ← ht]
  exact (NatTrans.naturality_apply η U.hom
    (((j.op.lanUnit.app F.obj).app U.left) t)).symm

/-- Relative form of `bigEtaleInverseImage_openEq`: two sections over an `S`-scheme `T` agree
exactly over the `T`-schemes whose image lies in a fixed open of `T`. -/
public lemma Scheme.bigEtaleInverseImage_openEq_over (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (T : Over S)
    (s t : ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.obj (Opposite.op T)) :
    ∃ W : T.left.Opens, ∀ (X : Over S) (g : X ⟶ T),
      ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.map g.op s =
        ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.map g.op t ↔
      Set.range g.left ⊆ (W : Set T.left) := by
  let P := ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj
  let B := Over.map T.hom
  let G := (Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} T.hom).obj F
  let Q := ((Scheme.bigEtaleInverseImage.{u, v} T.left).obj G).obj
  let e : B.op ⋙ P ≅ Q := (sheafToPresheaf (Scheme.etaleTopology.over T.left)
    (Type (max (u + 1) v))).mapIso ((Scheme.bigEtaleInverseImage_baseChangeIso.{u, v} T.hom).app F)
  let e₀ : B.obj (Over.mk (𝟙 T.left)) ≅ T := Over.isoMk (Iso.refl _) (by simp [B])
  let f₀ := P.map e₀.hom.op ≫ e.hom.app (Opposite.op (Over.mk (𝟙 T.left)))
  obtain ⟨W, hW⟩ := bigEtaleInverseImage_openEq T.left G (f₀ s) (f₀ t)
  refine ⟨W, fun X g => ?_⟩
  let V : Over T.left := Over.mk g.left
  let p : V ⟶ Over.mk (𝟙 T.left) := Over.homMk g.left (by simp [V])
  let eX : B.obj V ≅ X := Over.isoMk (Iso.refl _) (by simp [B, V, g.w])
  let φ := P.map eX.hom.op ≫ e.hom.app (Opposite.op V)
  have hφ : Function.Injective φ := (ConcreteCategory.bijective_of_isIso φ).injective
  have hx (x : P.obj (Opposite.op T)) : Q.map p.op (f₀ x) = φ (P.map g.op x) := by
    have hk : B.map p ≫ e₀.hom = eX.hom ≫ g := by
      apply Over.OverMorphism.ext
      simp [B, p, e₀, eX]
    show Q.map p.op (e.hom.app _ (P.map e₀.hom.op x)) = _
    rw [← NatTrans.naturality_apply]
    show e.hom.app _ (P.map (B.map p).op (P.map e₀.hom.op x)) = _
    rw [← Functor.map_comp_apply, ← CategoryTheory.op_comp, hk]
    simp only [CategoryTheory.op_comp, Functor.map_comp, types_comp_apply]
    rfl
  exact hφ.eq_iff.symm.trans ((by rw [← hx, ← hx]; exact hW V) : _ ↔ _)

/-- Two opens of `T.left` with the same containment behaviour against all `S`-morphisms into
`T` are equal. -/
private lemma opens_ext_over {S : Scheme.{u}} (T : Over S) (U V : T.left.Opens)
    (h : ∀ (Z : Over S) (g : Z ⟶ T),
      Set.range g.left ⊆ (U : Set T.left) ↔ Set.range g.left ⊆ (V : Set T.left)) : U = V := by
  apply le_antisymm
  · have H := (h (Over.mk (U.ι ≫ T.hom)) (Over.homMk U.ι rfl)).mp (by simp)
    simpa using H
  · have H := (h (Over.mk (V.ι ≫ T.hom)) (Over.homMk V.ι rfl)).mpr (by simp)
    simpa using H

/-- The locus where a compatible family agrees with a given section descends: the opens of the
members of an fpqc cover glue. -/
private lemma bigEtaleInverseImage_descent_open (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (T : Over S) (R : Sieve T) (hR : R ∈ (Scheme.fpqcTopology.over S) T)
    (x : Presieve.FamilyOfElements ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj R.arrows)
    (hx : x.Compatible)
    (t : ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.obj (Opposite.op T)) :
    ∃ W : T.left.Opens, ∀ (Z : Over S) (g : Z ⟶ T) (hg : R g),
      ∀ (Y : Over S) (k : Y ⟶ Z),
      ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.map k.op (x g hg) =
        ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.map (k ≫ g).op t ↔
      Set.range (k ≫ g).left ⊆ (W : Set T.left) := by
  classical
  let P := ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj
  choose W hW using fun (Z : Over S) (g : Z ⟶ T) (hg : R g) =>
    Scheme.bigEtaleInverseImage_openEq_over S F Z (x g hg) (P.map g.op t)
  let C := (Over.forget S).op ⋙ continuousMapPresheaf Prop
  let y : Presieve.FamilyOfElements C R.arrows := fun Z g hg =>
    ⟨fun z => z ∈ W Z g hg, continuous_Prop.mpr (W Z g hg).isOpen⟩
  have hy : y.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z Y g k hg
    have e : W Y (k ≫ g) (R.downward_closed hg k) =
        TopologicalSpace.Opens.comap k.left.base.hom (W Z g hg) := by
      apply opens_ext_over
      intro A a
      rw [← hW]
      have H := hW Z g hg A (a ≫ k)
      rw [hx.to_sieveCompatible g k hg]
      show P.map a.op (P.map k.op (x g hg)) =
        P.map a.op (P.map (k ≫ g).op t) ↔ _
      simp only [CategoryTheory.op_comp, Functor.map_comp_apply] at H ⊢
      refine H.trans ⟨?_, ?_⟩ <;> rintro h z ⟨b, rfl⟩ <;> exact h (Set.mem_range_self b)
    exact ContinuousMap.ext fun z => congrArg (fun U : Y.left.Opens => z ∈ U) e
  have hC : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) C :=
    (Over.forget S).op_comp_isSheaf_of_isSheaf _ _ _
      (isSheaf_fpqcTopology_continuousMapPresheaf Prop)
  obtain ⟨s, hs, _⟩ := ((isSheaf_iff_isSheaf_of_type _ _).mp hC R hR) y hy
  change ContinuousMap T.left Prop at s
  refine ⟨⟨{z | s z}, continuous_Prop.mp s.continuous⟩, fun Z g hg Y k => ?_⟩
  have H := hW Z g hg Y k
  simp only [CategoryTheory.op_comp, Functor.map_comp, types_comp_apply]
  rw [H]
  have he : ∀ z, s (g.left z) = (z ∈ W Z g hg) :=
    fun z => congrArg (fun f : ContinuousMap Z.left Prop => f z) (hs g hg)
  constructor
  · rintro h z ⟨a, rfl⟩
    show s (g.left (k.left a))
    rw [he]
    exact h (Set.mem_range_self a)
  · rintro h z ⟨a, rfl⟩
    show k.left a ∈ W Z g hg
    rw [← he]
    exact h (Set.mem_range_self a)

/-- An fpqc covering sieve is jointly surjective. -/
private lemma fpqc_sieve_covers {S : Scheme.{u}} (T : Over S) (R : Sieve T)
    (hR : R ∈ (Scheme.fpqcTopology.over S) T) (t : T.left) :
    ∃ (Z : Over S) (g : Z ⟶ T), R g ∧ t ∈ Set.range g.left := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  have hle : Scheme.fpqcTopology ≤ Scheme.jointlySurjectiveTopology := by
    rw [Scheme.jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology]
    show Scheme.fpqcTopology ≤
      Scheme.jointlySurjectivePrecoverage.toPretopology.toGrothendieck
    rw [Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
    exact Precoverage.toGrothendieck_mono
      ((Scheme.propQCPrecoverage_le_precoverage (P := @Flat)).trans inf_le_left)
  have hcov := hle _ hR
  rw [Scheme.mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology] at hcov
  change (Sieve.overEquiv T R).arrows ∈ Scheme.jointlySurjectivePrecoverage T.left at hcov
  rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hcov
  obtain ⟨Z, g, hg, ht⟩ := hcov t
  exact ⟨Over.mk (g ≫ T.hom), Over.homMk g rfl,
    (Sieve.overEquiv_iff R g).mp hg, ht⟩

/-- The big étale inverse image is separated for the fpqc topology: an amalgamation of a
compatible family is unique. -/
private lemma bigEtaleInverseImage_separated (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    Presieve.IsSeparated (Scheme.fpqcTopology.over S)
      ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj := by
  intro T R hR x s t hs ht
  obtain ⟨W, hW⟩ := Scheme.bigEtaleInverseImage_openEq_over S F T s t
  have htop : Set.range (𝟙 T : T ⟶ T).left ⊆ (W : Set T.left) := by
    intro z hz
    obtain ⟨Z, g, hg, a, rfl⟩ := fpqc_sieve_covers T R hR z
    exact (hW Z g).mp ((hs g hg).trans (ht g hg).symm) (Set.mem_range_self a)
  simpa using (hW T (𝟙 T)).mpr htop

/-- Every section over an `S`-scheme `Z` with a map to `T` is, étale locally on `Z`, pulled
back from a section over an `S`-scheme étale over `T`. -/
private lemma bigEtaleInverseImage_local_sections_relative (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (T Z : Over S) (g : Z ⟶ T)
    (s : ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.obj (Opposite.op Z)) :
    ∃ E : Scheme.Cover.{u, u} Scheme.etalePrecoverage Z.left, ∀ i : E.I₀,
      ∃ (V : Over S) (f : V ⟶ T) (_ : Etale f.left)
        (k : Over.mk (E.f i ≫ Z.hom) ⟶ V)
        (t : ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.obj (Opposite.op V)),
        k ≫ f = Over.homMk (E.f i) rfl ≫ g ∧
        ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.map k.op t =
          ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj.map (Over.homMk (E.f i) rfl).op s := by
  let P := ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj
  let B := Over.map T.hom
  let G := (Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} T.hom).obj F
  let Q := ((Scheme.bigEtaleInverseImage.{u, v} T.left).obj G).obj
  let e : B.op ⋙ P ≅ Q := (sheafToPresheaf (Scheme.etaleTopology.over T.left)
    (Type (max (u + 1) v))).mapIso ((Scheme.bigEtaleInverseImage_baseChangeIso.{u, v} T.hom).app F)
  clear_value e
  let Z' : Over T.left := Over.mk g.left
  let eZ : B.obj Z' ≅ Z := Over.isoMk (Iso.refl _) (by simp [B, Z', g.w])
  obtain ⟨E, hE⟩ := bigEtaleInverseImage_local_sections T.left G Z'
    (e.hom.app _ (P.map eZ.hom.op s))
  refine ⟨E, fun i => ?_⟩
  obtain ⟨U, k, t, ht⟩ := hE i
  let V := B.obj ((Scheme.Etale.forget T.left).obj U)
  let f : V ⟶ T := Over.homMk U.hom rfl
  let A : Over T.left := Over.mk (E.f i ≫ g.left)
  let eA : B.obj A ≅ Over.mk (E.f i ≫ Z.hom) :=
    Over.isoMk (Iso.refl _) (by simp [B, A, Category.assoc, g.w])
  let k' := eA.inv ≫ B.map k
  refine ⟨V, f, inferInstanceAs (Etale U.hom), k', e.inv.app _ t, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    have hw : Over.Hom.left k ≫ U.hom = E.f i ≫ Z'.hom := k.w
    show 𝟙 _ ≫ Over.Hom.left k ≫ U.hom = E.f i ≫ Z'.hom
    rw [Category.id_comp]
    exact hw
  · let j : A ⟶ Z' := Over.homMk (E.f i) rfl
    have hn := NatTrans.naturality_apply e.inv k.op t
    have hp := NatTrans.naturality_apply e.inv j.op
      (e.hom.app _ (P.map eZ.hom.op s))
    have h : P.map (B.map k).op (e.inv.app _ t) =
        P.map (B.map j).op (P.map eZ.hom.op s) := by
      refine hn.symm.trans ((congrArg (e.inv.app (Opposite.op A)) ht).trans ?_)
      exact hp.trans (congrArg (P.map (B.map j).op)
        (Iso.hom_inv_id_app_apply e (Opposite.op Z') (P.map eZ.hom.op s)))
    show P.map k'.op (e.inv.app _ t) = _
    dsimp only [k']
    rw [CategoryTheory.op_comp, Functor.map_comp, types_comp_apply]
    refine (congrArg (P.map eA.inv.op) h).trans ?_
    simp only [← Functor.map_comp_apply, ← CategoryTheory.op_comp]
    congr 2

/-- Around every point of `T` there is an `S`-scheme étale over `T` on which the compatible
family has an amalgamation. -/
private lemma bigEtaleInverseImage_matching_neighborhood (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (T : Over S) (R : Sieve T) (hR : R ∈ (Scheme.fpqcTopology.over S) T)
    (x : Presieve.FamilyOfElements ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj R.arrows)
    (hx : x.Compatible) (p : T.left) :
    ∃ (V : Over S) (f : V ⟶ T), Etale f.left ∧ p ∈ Set.range f.left ∧
      ∃ t, (x.pullback f).IsAmalgamation t := by
  classical
  let P := ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj
  obtain ⟨Z, g, hg, z, hz⟩ := fpqc_sieve_covers T R hR p
  obtain ⟨E, hE⟩ := bigEtaleInverseImage_local_sections_relative S F T Z g (x g hg)
  let : Scheme.JointlySurjective Scheme.etalePrecoverage.{u} :=
    Scheme.instJointlySurjectivePrecoverage (P := @Etale)
  obtain ⟨a, ha⟩ := E.covers z
  change E.f (E.idx z) a = z at ha
  obtain ⟨V, f, hf, k, t, hkf, ht⟩ := hE (E.idx z)
  let j : Over.mk (E.f (E.idx z) ≫ Z.hom) ⟶ Z := Over.homMk (E.f (E.idx z)) rfl
  have hk : (R.pullback f) k := by
    show R (k ≫ f)
    rw [hkf]
    exact R.downward_closed hg j
  obtain ⟨W, hW⟩ := bigEtaleInverseImage_descent_open S F V (R.pullback f)
    ((Scheme.fpqcTopology.over S).pullback_stable f hR) (x.pullback f) (hx.pullback f) t
  have hkrange : Set.range k.left ⊆ (W : Set V.left) := by
    have h := (hW _ k hk _ (𝟙 _)).mp (by
      simp only [op_id, Functor.map_id_apply, Category.id_comp]
      show x (k ≫ f) hk = P.map k.op t
      exact (family_apply_eq x hkf hk (R.downward_closed hg j)).trans
        ((x.comp_of_compatible R hx hg j).trans ht.symm))
    simpa using h
  let V' : Over S := Over.mk (W.ι ≫ V.hom)
  let w : V' ⟶ V := Over.homMk W.ι rfl
  let f' := w ≫ f
  let : Etale f.left := hf
  refine ⟨V', f', inferInstanceAs (Etale (W.ι ≫ f.left)), ?_, P.map w.op t, ?_⟩
  · refine ⟨⟨k.left a, hkrange (Set.mem_range_self a)⟩, ?_⟩
    have hc := congrArg (fun q => q.left a) hkf
    show f.left (k.left a) = p
    change f.left (k.left a) = g.left (E.f (E.idx z) a) at hc
    exact hc.trans ((congrArg g.left ha).trans hz)
  · intro Y l hl
    have hl' : (R.pullback f) (l ≫ w) := by simpa [f', Category.assoc] using hl
    have H := (hW Y (l ≫ w) hl' Y (𝟙 Y)).mpr (by
      intro b hb
      obtain ⟨c, rfl⟩ := hb
      exact (l.left c).property)
    simp only [op_id, Functor.map_id_apply, Category.id_comp] at H
    change x ((l ≫ w) ≫ f) hl' = P.map (l ≫ w).op t at H
    show P.map l.op (P.map w.op t) = x (l ≫ f') hl
    rw [← Functor.map_comp_apply, ← CategoryTheory.op_comp]
    exact H.symm.trans (family_apply_eq x (Category.assoc l w f) _ _)

/-- **Stacks 09XN, the sheaf clause.** The inverse image of
a sheaf on the small étale site of `S`, taken on all `S`-schemes for the big étale topology, is
a sheaf for the fpqc topology. -/
public lemma Scheme.bigEtaleInverseImage_isSheaf_fpqc (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj := by
  classical
  let P := ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).obj
  let J := Scheme.fpqcTopology.over S
  have hsep := bigEtaleInverseImage_separated.{u, v} S F
  rw [isSheaf_iff_isSheaf_of_type]
  apply hsep.isSheaf
  intro T R hR x hx
  let A : Sieve T :=
    { arrows := fun V f => ∃ t, (x.pullback f).IsAmalgamation t
      downward_closed := by
        intro V Y f hf k
        obtain ⟨t, ht⟩ := hf
        refine ⟨P.map k.op t, ?_⟩
        intro Z l hl
        have H := ht (l ≫ k) (by simpa [Category.assoc] using hl)
        change P.map (l ≫ k).op t = x ((l ≫ k) ≫ f) _ at H
        show P.map l.op (P.map k.op t) = x (l ≫ k ≫ f) _
        rw [← Functor.map_comp_apply, ← CategoryTheory.op_comp]
        exact H.trans (family_apply_eq x (Category.assoc l k f) _ _) }
  have hA : A ∈ (Scheme.etaleTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff]
    let Q : Presieve T.left := fun V f => Etale f ∧ (Sieve.overEquiv T A) f
    have hQ : Q ∈ Scheme.etalePrecoverage T.left := by
      constructor
      · rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff]
        intro p
        obtain ⟨V, f, hf, hp, t, ht⟩ :=
          bigEtaleInverseImage_matching_neighborhood S F T R hR x hx p
        refine ⟨V.left, f.left, ⟨hf, ?_⟩, hp⟩
        rw [Sieve.overEquiv_iff]
        let e : Over.mk (f.left ≫ T.hom) ⟶ V := Over.homMk (𝟙 _) (by simp)
        have he : e ≫ f =
            (Over.homMk f.left rfl : Over.mk (f.left ≫ T.hom) ⟶ T) := by
          ext; simp [e]
        rw [← he]
        exact A.downward_closed ⟨t, ht⟩ e
      · intro V f hf
        exact hf.1
    exact (Scheme.etaleTopology).superset_covering
      ((Sieve.generate_le_iff _ _).mpr (fun V f hf => hf.2))
      (Precoverage.generate_mem_toGrothendieck hQ)
  choose a ha using fun V f (hf : A f) => hf
  let y : Presieve.FamilyOfElements P A.arrows := a
  have hy : y.Compatible := by
    intro V W Y k l f g hf hg hfg
    apply (hsep (R.pullback (k ≫ f)) (J.pullback_stable _ hR)).ext
    intro Z m hm
    have H₁ := ha V f hf (m ≫ k) (by simpa [Category.assoc] using hm)
    have H₂ := ha W g hg (m ≫ l) (by simpa [Category.assoc, hfg] using hm)
    change P.map (m ≫ k).op (a V f hf) = x ((m ≫ k) ≫ f) _ at H₁
    change P.map (m ≫ l).op (a W g hg) = x ((m ≫ l) ≫ g) _ at H₂
    have he : (m ≫ k) ≫ f = (m ≫ l) ≫ g := by simp only [Category.assoc, hfg]
    exact (by simpa only [CategoryTheory.op_comp, Functor.map_comp, types_comp_apply] using
      H₁.trans ((family_apply_eq x he _ _).trans H₂.symm))
  obtain ⟨s, hs, _⟩ := ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).property A hA) y hy
  refine ⟨s, ?_⟩
  intro V g hg
  have hA' := (Scheme.etaleTopology.over S).pullback_stable g hA
  have hsep' := ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((Scheme.bigEtaleInverseImage.{u, v} S).obj F).property).isSeparated
  apply (hsep' (A.pullback g) hA').ext
  intro W k hk
  have H := ha W (k ≫ g) hk (𝟙 W) (by simpa using R.downward_closed hg k)
  have H' := hs (k ≫ g) hk
  simp only [Presieve.FamilyOfElements.pullback, op_id, Functor.map_id_apply] at H
  rw [← Functor.map_comp_apply, ← CategoryTheory.op_comp, H']
  exact H.trans (x.comp_of_compatible R hx hg k)

/-! ### The rule is a sheaf on the small pro-étale site, and it is `ε⁻¹` -/

/-- The rule on the small pro-étale category of `S` obtained by restricting the inverse image
of an étale sheaf on the big étale slice. -/
public def Scheme.etaleSectionsPresheaf (S : Scheme.{u}) :
    Sheaf S.smallEtaleTopology (Type (max (u + 1) v)) ⥤
      (S.ProEt)ᵒᵖ ⥤ Type (max (u + 1) v) :=
  Scheme.bigEtaleInverseImage.{u, v} S ⋙
    sheafToPresheaf (Scheme.etaleTopology.over S) (Type (max (u + 1) v)) ⋙
    (Functor.whiskeringLeft _ _ _).obj (Scheme.ProEt.forget S).op

/-- For a sheaf `ℱ` on the small étale site of `S`, the rule
`(f : Y → S) ↦ Γ(Y_étale, f_étale⁻¹ℱ)` is a sheaf on the small pro-étale site of `S`. -/
@[stacks 0GLZ "the formula is a sheaf"]
public theorem Scheme.etaleSectionsPresheaf_isSheaf (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    Presheaf.IsSheaf (Scheme.ProEt.topology S)
      ((Scheme.etaleSectionsPresheaf.{u, v} S).obj F) :=
  proetale_restrict_fpqc_sheaf S _ (Scheme.bigEtaleInverseImage_isSheaf_fpqc S F)

section Comparison

variable (S : Scheme.{u})

/-- Including the small étale category into the small pro-étale category and then forgetting
to `S`-schemes is continuous. -/
public instance Scheme.etaleToProetale_comp_forget_isContinuous :
    (S.etaleToProetale ⋙ Scheme.ProEt.forget S).IsContinuous S.smallEtaleTopology
      (Scheme.etaleTopology.over S) :=
  Scheme.Etale.forget_isContinuous S

/-- The sheaf on the small pro-étale site defined by the rule of Stacks 0GLZ, with its
canonical restriction maps. -/
public def Scheme.etaleSectionsSheaf :
    Sheaf S.smallEtaleTopology (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.ProEt.topology S) (Type (max (u + 1) v)) :=
  Functor.sheafPullbackRestriction S.etaleToProetale (Scheme.ProEt.forget S)
    S.smallEtaleTopology (Scheme.ProEt.topology S) (Scheme.etaleTopology.over S)
    (Type (max (u + 1) v)) (Scheme.etaleSectionsPresheaf_isSheaf.{u, v} S)

/-- The underlying presheaf of `AlgebraicGeometry.Scheme.etaleSectionsSheaf` is the rule. -/
public theorem Scheme.etaleSectionsSheaf_comp_sheafToPresheaf :
    Scheme.etaleSectionsSheaf.{u, v} S ⋙
        sheafToPresheaf (Scheme.ProEt.topology S) (Type (max (u + 1) v)) =
      Scheme.etaleSectionsPresheaf.{u, v} S := rfl

/-- **Stacks 0GLZ, the adjunction.** The functor given by the rule of Stacks 0GLZ is left
adjoint to `ε_*`, the restriction of a pro-étale sheaf to the small étale site. -/
public def Scheme.etaleSectionsSheafAdjunction :
    Scheme.etaleSectionsSheaf.{u, v} S ⊣
      S.etaleToProetale.sheafPushforwardContinuous (Type (max (u + 1) v))
        S.smallEtaleTopology (Scheme.ProEt.topology S) :=
  Functor.sheafPullbackRestrictionAdjunction S.etaleToProetale (Scheme.ProEt.forget S)
    S.smallEtaleTopology (Scheme.ProEt.topology S) (Scheme.etaleTopology.over S)
    (Type (max (u + 1) v)) (Scheme.etaleSectionsPresheaf_isSheaf.{u, v} S)

/-- The sheaf defined by the rule is the inverse image `ε⁻¹ℱ` of the morphism of sites
`ε : S_proétale → S_étale`, through the canonical comparison of two left adjoints of `ε_*`. -/
@[stacks 0GLZ "the identification with ε⁻¹"]
public def Scheme.proetaleInverseImageIsoEtaleSectionsSheaf :
    Functor.sheafPullbackConstruction.sheafPullback S.etaleToProetale
        (Type (max (u + 1) v)) S.smallEtaleTopology (Scheme.ProEt.topology S) ≅
      Scheme.etaleSectionsSheaf.{u, v} S :=
  Functor.sheafPullbackCompRestrictionIso S.etaleToProetale (Scheme.ProEt.forget S)
    S.smallEtaleTopology (Scheme.ProEt.topology S) (Scheme.etaleTopology.over S)
    (Type (max (u + 1) v)) (Scheme.etaleSectionsPresheaf_isSheaf.{u, v} S)

end Comparison

/-! ### The values of the rule are small étale global sections -/

/-- Restricting the big étale inverse image of `F` along `Over.map f` and then along the
forgetful functor of the small étale site of `X` gives the small étale inverse image of `F`
along `f`. -/
public def Scheme.smallEtalePullbackRestrictionIso {X S : Scheme.{u}} (f : X ⟶ S) :
    Scheme.bigEtaleInverseImage.{u, v} S ⋙
      (Over.map f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S) ⋙
      (Scheme.Etale.forget X).sheafPushforwardContinuous (Type (max (u + 1) v))
        X.smallEtaleTopology (Scheme.etaleTopology.over X) ≅
    Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} f := by
  let A := Type (max (u + 1) v)
  let adjB := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.Etale.forget X) A X.smallEtaleTopology (Scheme.etaleTopology.over X)
  let : IsIso adjB.unit := Functor.isIso_unit_of_sheafPushforwardContinuous
    (Scheme.Etale.forget X) A X.smallEtaleTopology (Scheme.etaleTopology.over X) adjB
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.bigEtaleInverseImage_baseChangeIso.{u, v} f)
      ((Scheme.Etale.forget X).sheafPushforwardContinuous A X.smallEtaleTopology
        (Scheme.etaleTopology.over X)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} f)
      (asIso adjB.unit).symm ≪≫
    Functor.rightUnitor _

/-- The sections of the big étale inverse image of `F` over `X`, regarded as an `S`-scheme
through `f`, are the global sections on the small étale site of `X` of the small étale inverse
image of `F` along `f`. -/
public def Scheme.bigEtaleInverseImageSectionsIso {X S : Scheme.{u}} (f : X ⟶ S) :
    Scheme.bigEtaleInverseImage.{u, v} S ⋙
      (sheafSections (Scheme.etaleTopology.over S)
        (Type (max (u + 1) v))).obj (Opposite.op (Over.mk f)) ≅
    Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} f ⋙
      Sheaf.Γ X.smallEtaleTopology (Type (max (u + 1) v)) := by
  let A := Type (max (u + 1) v)
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let e : (Over.map f).obj ((Scheme.Etale.forget X).obj T) ≅ Over.mk f :=
    Over.isoMk (Iso.refl _) (by simp [T])
  let L := Scheme.bigEtaleInverseImage.{u, v} S
  exact Functor.isoWhiskerLeft L
      ((sheafSections (Scheme.etaleTopology.over S) A).mapIso e.op).symm ≪≫
    Functor.isoWhiskerRight (Scheme.smallEtalePullbackRestrictionIso.{u, v} f)
      ((sheafSections X.smallEtaleTopology A).obj (Opposite.op T)) ≪≫
    Functor.isoWhiskerLeft (Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} f)
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A hT).symm

/-- At a pro-étale object `f : Y → S`, the sheaf defined by the rule has as its sections the
global sections on the small étale site of `Y` of the inverse image `f_étale⁻¹ℱ`, naturally in
the étale sheaf `ℱ`. -/
@[stacks 0GLZ "the formula for sections"]
public def Scheme.etaleSectionsFormulaIso (S : Scheme.{u}) (Y : S.ProEt) :
    Scheme.etaleSectionsSheaf.{u, v} S ⋙
        (sheafSections (Scheme.ProEt.topology S)
          (Type (max (u + 1) v))).obj (Opposite.op Y) ≅
      Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} Y.hom ⋙
        Sheaf.Γ Y.left.smallEtaleTopology (Type (max (u + 1) v)) :=
  Scheme.bigEtaleInverseImageSectionsIso.{u, v} Y.hom

/-- The sections of `ε⁻¹ℱ` at a pro-étale object `f : Y → S` are the global
sections on the small étale site of `Y` of `f_étale⁻¹ℱ`. -/
@[stacks 0GLZ "the formula for sections"]
public def Scheme.proetaleInverseImageSectionsIso (S : Scheme.{u}) (Y : S.ProEt) :
    Functor.sheafPullbackConstruction.sheafPullback S.etaleToProetale
          (Type (max (u + 1) v)) S.smallEtaleTopology (Scheme.ProEt.topology S) ⋙
        (sheafSections (Scheme.ProEt.topology S)
          (Type (max (u + 1) v))).obj (Opposite.op Y) ≅
      Stacks.EtaleCohomology.smallEtaleInverseImage.{u, v} Y.hom ⋙
        Sheaf.Γ Y.left.smallEtaleTopology (Type (max (u + 1) v)) :=
  Functor.isoWhiskerRight (Scheme.proetaleInverseImageIsoEtaleSectionsSheaf.{u, v} S)
      ((sheafSections (Scheme.ProEt.topology S)
        (Type (max (u + 1) v))).obj (Opposite.op Y)) ≪≫
    Scheme.etaleSectionsFormulaIso.{u, v} S Y

end AlgebraicGeometry

end
