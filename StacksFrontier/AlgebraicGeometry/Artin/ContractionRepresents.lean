module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRepresentsCounterexample
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionWitnessComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModificationExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
import all StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModification

/-!
# A solution of Artin's contraction problem represents Artin's functor

In the situation of Stacks 0GH8, recorded by `AlgebraicGeometry.Artin.ContractionSituation`,
**Stacks 0GHB** says that a solution `(f : X' ⟶ X, T, a)` gives a functorial bijection
`F(V) = Mor_S(V, X)` on locally Noetherian schemes `V` over `S`, where `F` is Artin's functor of
Stacks 0GHA (`AlgebraicGeometry.Artin.contractionFunctor`).

As printed this is false for the notion of solution of the prose after Situation 0GH8, whose
condition (2) only asks for *some* open subspace `U ⊆ X` onto which `f` maps `U'`
isomorphically: see `StacksFrontier.AlgebraicGeometry.Artin.ContractionRepresentsCounterexample`.
The source's proof uses `u' : V ∖ Z → U' = U` as the restriction of `x` to
`V ∖ Z = x⁻¹(|X| ∖ T)`, that is, it reads `U` as the open subspace with `|U| = |X| ∖ T`. This
file proves the lemma with that condition added, following the source's proof.

* A morphism `x : V ⟶ X` gives the triple `(Z, u', x̂)` with `Z = x⁻¹T`, `u'` the restriction of
  `x` to `V ∖ Z ⟶ X ∖ T = U ≅ U'`, and `x̂ = a ∘ x_{/Z}`
  (`AlgebraicGeometry.Artin.ContractionSituation.Solution.tripleOfHom`). The compatibility is
  witnessed by `V' = V ×_{x, X} X'` with `x' = pr₂`
  (`AlgebraicGeometry.Artin.ContractionSituation.Solution.witness`).
* The construction is natural in `V`
  (`AlgebraicGeometry.Artin.ContractionSituation.Solution.tripleOfHom_comp`) and injective for
  locally Noetherian `V`, by the uniqueness statement of Stacks 0GI1
  (`AlgebraicGeometry.Artin.ContractionSituation.Solution.tripleOfHom_injective`).
* Conversely a triple `(Z, u', x̂)` with witness `V' ⟶ V`, `x̂'`, `x'` gives the pair
  `(f ∘ x', a⁻¹ ∘ x̂)` of a morphism `V' ⟶ X` and a morphism `V_{/Z} ⟶ X` compatible over
  `V'_{/Z}`
  (`AlgebraicGeometry.Artin.ContractionSituation.Solution.completionMap_comp_formalOfTriple`),
  and a morphism `x : V ⟶ X` inducing that pair has `(Z, u', x̂)` as its triple
  (`Artin.ContractionSituation.Solution.tripleOfHom_eq_of_morToModificationCompletion_eq`).
  The existence of `x` is the existence half of Stacks 0GI3
  (`AlgebraicGeometry.Space.exists_morToModificationCompletion_eq`).

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.Solution.homToTriple`: the natural
  transformation `Mor_S(-, X) ⟶ F` on locally Noetherian schemes over `S`.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.contractionFunctorIso`: **Stacks 0GHB**,
  corrected: the functorial bijection `F(V) = Mor_S(V, X)` for a solution with `|U| = |X| ∖ T`.

## References

* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHB](https://stacks.math.columbia.edu/tag/0GHB)
* [Stacks Project, Tag 0GI1](https://stacks.math.columbia.edu/tag/0GI1)
* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c : ContractionSituation B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

namespace Solution

variable (s : Solution c X)
    (hU : Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ)

/-! ### The open subspace `U` is `X ∖ T` -/

include hU in
/-- When `|U| = |X| ∖ T`, the open subspace `U` of a solution is the open subspace cut out by
`|X| ∖ T`, by Stacks 03BZ. -/
theorem U_eq_openSubspaceOfPoints : s.U = Space.openSubspaceOfPoints B S hS X s.Tᶜ :=
  le_antisymm
    (Space.le_of_range_pointsMap_ι_subset B S hS
      (Space.isOpenSubspace_openSubspaceOfPoints B S hS s.isAlgebraicSpace_X _
        s.isClosed_T.isOpen_compl)
      (by rw [Space.range_pointsMap_ι_openSubspaceOfPoints, hU]))
    (Space.le_of_range_pointsMap_ι_subset B S hS s.isOpenSubspace_U
      (by rw [Space.range_pointsMap_ι_openSubspaceOfPoints, hU]))

/-- The morphism `X ∖ T ⟶ U'` inverse to `f` restricted to `U' ≅ U = X ∖ T`. -/
noncomputable def complToSituationOpen :
    (Space.openSubspaceOfPoints B S hS X s.Tᶜ).toFunctor ⟶ c.U'.toFunctor :=
  Subfunctor.homOfLe (s.U_eq_openSubspaceOfPoints hU).ge ≫ s.isoU.inv

/-- The composite of `complToSituationOpen` with `U' ⟶ X' ⟶ X` is the inclusion of `X ∖ T`. -/
theorem complToSituationOpen_comp_ι_comp_f :
    s.complToSituationOpen hU ≫ c.U'.ι ≫ s.f = (Space.openSubspaceOfPoints B S hS X s.Tᶜ).ι := by
  rw [complToSituationOpen, Category.assoc, ← s.isoU_comp_ι, Iso.inv_hom_id_assoc,
    Subfunctor.homOfLe_ι]

/-- The composite `U' ⟶ X' ⟶ X` of the inclusion of `U'` with `f` is a monomorphism. -/
instance mono_U'_ι_comp_f : Mono (c.U'.ι ≫ s.f) := by
  rw [← s.isoU_comp_ι]
  infer_instance

include hU in
/-- When `|U| = |X| ∖ T`, the open subspace `U'` is the inverse image of `U` under `f`: the
square formed by `U' ≅ U`, the two inclusions and `f` is cartesian. -/
theorem isPullback_isoU : IsPullback s.isoU.hom c.U'.ι s.U.ι s.f := by
  have hpre : s.U.preimage s.f = c.U' := by
    rw [s.U_eq_openSubspaceOfPoints hU, Space.preimage_openSubspaceOfPoints_compl, s.preimage_T]
    rfl
  let e : (s.U.preimage s.f).toFunctor ≅ c.U'.toFunctor :=
    { hom := Subfunctor.homOfLe hpre.le
      inv := Subfunctor.homOfLe hpre.ge
      hom_inv_id := by
        rw [← cancel_mono (Subfunctor.ι _), Category.assoc, Subfunctor.homOfLe_ι,
          Subfunctor.homOfLe_ι, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono (Subfunctor.ι _), Category.assoc, Subfunctor.homOfLe_ι,
          Subfunctor.homOfLe_ι, Category.id_comp] }
  refine (Subfunctor.isPullback_fromPreimage s.U s.f).of_iso e (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id, ← cancel_mono s.U.ι, Category.assoc, s.isoU_comp_ι,
      Subfunctor.fromPreimage_ι]
    exact (Subfunctor.homOfLe_ι_assoc hpre.le s.f).symm
  · rw [Iso.refl_hom, Category.comp_id]
    exact (Subfunctor.homOfLe_ι hpre.le).symm

/-! ### The triple of a morphism `V ⟶ X` -/

/-- The Yoneda image of a locally Noetherian scheme has the étale-local Noetherian property. -/
private theorem hasEtaleLocalProperty_yoneda (V : BigFppfOver B S hS)
    (hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)) :
    Space.HasEtaleLocalProperty B S hS (yoneda.obj V)
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) :=
  FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian
    (isAlgebraicSpace_yoneda B S hS V) (Space.isLocallyNoetherian_yoneda B S hS V hV)

variable (V : BigFppfOver B S hS) (x : yoneda.obj V ⟶ X)

/-- The closed subset `Z = x⁻¹T ⊆ |V|` of the triple of `x : V ⟶ X`. -/
abbrev preT : Set (Space.points B S hS (yoneda.obj V)) :=
  Space.pointsMap B S hS (yoneda.obj V) x ⁻¹' s.T

/-- The restriction `V ∖ Z ⟶ X ∖ T` of `x : V ⟶ X`. -/
noncomputable def restrictCompl :
    (Space.openSubspaceOfPoints B S hS (yoneda.obj V) (s.preT V x)ᶜ).toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS X s.Tᶜ).toFunctor :=
  Space.openSubspaceOfPointsRestrict B S hS x (s.preT V x)ᶜ s.Tᶜ Set.preimage_compl.symm.subset

/-- The restriction `V ∖ Z ⟶ X ∖ T` of `x` commutes with the inclusions into `V` and `X`. -/
theorem restrictCompl_ι :
    s.restrictCompl V x ≫ (Space.openSubspaceOfPoints B S hS X s.Tᶜ).ι =
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V) (s.preT V x)ᶜ).ι ≫ x :=
  rfl

/-- The second component `u' : V ∖ Z ⟶ U'` of the triple of `x : V ⟶ X`: the restriction
`V ∖ Z ⟶ X ∖ T` of `x` followed by `X ∖ T = U ≅ U'`. -/
noncomputable def restrictU :
    (Space.openSubspaceOfPoints B S hS (yoneda.obj V) (s.preT V x)ᶜ).toFunctor ⟶
      c.U'.toFunctor :=
  s.restrictCompl V x ≫ s.complToSituationOpen hU

/-- The composite of `u' : V ∖ Z ⟶ U'` with `U' ⟶ X' ⟶ X` is the restriction of `x` to `V ∖ Z`. -/
theorem restrictU_comp_ι_comp_f :
    s.restrictU hU V x ≫ c.U'.ι ≫ s.f =
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V) (s.preT V x)ᶜ).ι ≫ x := by
  rw [restrictU, Category.assoc, complToSituationOpen_comp_ι_comp_f, restrictCompl_ι]

/-- The third component `x̂ = a ∘ x_{/Z} : V_{/Z} ⟶ W` of the triple of `x : V ⟶ X`. -/
noncomputable def restrictW : Space.completionSheaf B S hS (yoneda.obj V) (s.preT V x) ⟶ c.W :=
  Space.completionSheafRestrict B S hS x (s.preT V x) s.T subset_rfl ≫ s.a.hom

/-- The composite of `x̂ : V_{/Z} ⟶ W` with `a⁻¹` and the inclusion `X_{/T} ⟶ X` is the inclusion
`V_{/Z} ⟶ V` followed by `x`. -/
theorem restrictW_comp :
    s.restrictW V x ≫ s.a.inv ≫ Space.completionSheafInclusion B S hS X s.T =
      Space.completionSheafInclusion B S hS (yoneda.obj V) (s.preT V x) ≫
        Space.sheafifiedULiftMap B S hS x := by
  rw [restrictW, Category.assoc, Iso.hom_inv_id_assoc,
    Space.completionSheafRestrict_comp_inclusion]

/-- **The compatibility of the triple of `x : V ⟶ X`**, the witness of the proof of Stacks 0GHB:
`V' = V ×_{x, X} X'`, which is proper over `V` as a base change of `f` and an isomorphism over
`V ∖ Z` since `f` is one over `U = X ∖ T`, with `x' = pr₂` and `x̂'` its completion. -/
noncomputable def witness :
    CompatibilityWitness c V (s.preT V x) (s.restrictU hU V x) (s.restrictW V x) :=
  have hpb : IsPullback (pullback.fst x s.f) (pullback.snd x s.f) x s.f :=
    IsPullback.of_hasPullback _ _
  have halg : IsAlgebraicSpace B S hS (pullback x s.f) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS V)
      c.isAlgebraicSpace_X' s.isAlgebraicSpace_X
  have hsub : Space.pointsMap B S hS (pullback x s.f) (pullback.fst x s.f) ⁻¹' s.preT V x ⊆
      Space.pointsMap B S hS (pullback x s.f) (pullback.snd x s.f) ⁻¹' c.T' := by
    intro z hz
    rw [Set.mem_preimage, ← s.preimage_T, Set.mem_preimage, ← Space.pointsMap_comp_apply,
      ← hpb.w, Space.pointsMap_comp_apply]
    exact hz
  have hw : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) (s.preT V x)ᶜ).ι ≫ x =
      (s.restrictU hU V x ≫ c.U'.ι) ≫ s.f := by
    rw [Category.assoc, s.restrictU_comp_ι_comp_f]
  { V' := pullback x s.f
    isAlgebraicSpace_V' := halg
    p := pullback.fst x s.f
    isProper_p := by
      have hsq : IsPullback
          (ObjectProperty.homMk (pullback.fst x s.f) :
            (⟨pullback x s.f, halg⟩ : AlgebraicSpaces B S hS) ⟶
              schemeSpace V)
          (ObjectProperty.homMk (pullback.snd x s.f) :
            (⟨pullback x s.f, halg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨c.X', c.isAlgebraicSpace_X'⟩)
          (ObjectProperty.homMk x :
            (schemeSpace V : AlgebraicSpaces B S hS) ⟶
              ⟨X, s.isAlgebraicSpace_X⟩)
          (ObjectProperty.homMk s.f :
            (⟨c.X', c.isAlgebraicSpace_X'⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨X, s.isAlgebraicSpace_X⟩) :=
        IsPullback.of_map_of_faithful
          (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
            IsAlgebraicSpace B S hS F)) hpb
      exact (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback hsq.flip s.isProper_f
    j := pullback.lift _ _ hw
    isPullback_j := by
      refine IsPullback.of_bot ?_ (by rw [pullback.lift_fst, Category.id_comp]) hpb
      have h1 : IsPullback (𝟙 _)
          (s.restrictCompl V x ≫ Subfunctor.homOfLe (s.U_eq_openSubspaceOfPoints hU).ge ≫
            s.isoU.inv)
          (s.restrictCompl V x ≫ Subfunctor.homOfLe (s.U_eq_openSubspaceOfPoints hU).ge)
          s.isoU.hom :=
        IsPullback.of_horiz_isIso ⟨by simp⟩
      have h2 := h1.paste_vert (s.isPullback_isoU hU)
      have e1 : (s.restrictCompl V x ≫ Subfunctor.homOfLe (s.U_eq_openSubspaceOfPoints hU).ge ≫
            s.isoU.inv) ≫ c.U'.ι = pullback.lift _ _ hw ≫ pullback.snd x s.f := by
        rw [pullback.lift_snd, restrictU, complToSituationOpen]
      have e2 : (s.restrictCompl V x ≫ Subfunctor.homOfLe (s.U_eq_openSubspaceOfPoints hU).ge) ≫
            s.U.ι = (Space.openSubspaceOfPoints B S hS (yoneda.obj V) (s.preT V x)ᶜ).ι ≫ x := by
        rw [Category.assoc, Subfunctor.homOfLe_ι, restrictCompl_ι]
      rwa [e1, e2] at h2
    xhat' := Space.completionSheafRestrict B S hS (pullback.snd x s.f) _ c.T' hsub
    isPullback_xhat' := by
      have h := Space.isPullback_completionSheafRestrict B S hS _ _ _ _ hpb s.T _ (s.preT V x) _
        rfl s.preimage_T.symm rfl subset_rfl hsub subset_rfl s.preimage_T.symm.subset
      refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) s.a (by simp) (by simp)
        (by rw [Iso.refl_hom, Category.id_comp]; rfl) ?_
      rw [Iso.refl_hom, Category.id_comp]
      exact s.completion_comp_a
    x' := pullback.snd x s.f
    restrict_x' := pullback.lift_snd _ _ _
    completion_x' := (Space.completionSheafRestrict_comp_inclusion B S hS _ _ _ _).symm }

/-- **The triple of a morphism `x : V ⟶ X`**, the first construction of the proof of Stacks
0GHB: `Z = x⁻¹T`, `u'` the restriction of `x` to `V ∖ Z ⟶ X ∖ T = U ≅ U'`, and
`x̂ = a ∘ x_{/Z}`, with the compatibility witnessed by `V ×_{x, X} X'`. -/
noncomputable def tripleOfHom : Triple c V where
  Z := s.preT V x
  isClosed_Z := s.isClosed_T.preimage (Space.continuous_pointsMap B S hS x)
  u := s.restrictU hU V x
  xhat := s.restrictW V x
  adic_xhat := Space.isRepresentableByAlgebraicSpacesULift_of_iso B S hS (Iso.refl _)
    ((sheafToPresheaf _ _).mapIso s.a) (by rw [Iso.refl_hom, Category.id_comp]; rfl)
    (Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS
      (isAlgebraicSpace_yoneda B S hS V) s.isAlgebraicSpace_X x s.T)
  compatible := ⟨s.witness hU V x⟩

/-- **The triple of a morphism is natural**: the triple of `x ∘ φ` is the triple of `x` moved
along `φ` by Artin's functor. -/
theorem tripleOfHom_comp {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (x : yoneda.obj V₁ ⟶ X) :
    s.tripleOfHom hU V₂ (yoneda.map φ ≫ x) = mapTriple c φ (s.tripleOfHom hU V₁ x) := by
  have hZ : Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ ≫ x) ⁻¹' s.T =
      Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj V₁) x ⁻¹' s.T) := by
    rw [Space.pointsMap_comp, Set.preimage_comp]
  exact Triple.mk_congr hZ
    (heq_openSubspaceOfPointsRestrict_comp (yoneda.map φ) x rfl hZ _ (fun _ hz => hz)
      (fun _ hz => hz) (s.complToSituationOpen hU))
    (heq_completionSheafRestrict_comp (yoneda.map φ) x rfl hZ _ (fun _ hz => hz)
      (fun _ hz => hz) s.a.hom)

/-- The second component of a triple equal to the triple of `x` restricts `x`. -/
theorem u_comp_eq_of_tripleOfHom_eq {t : Triple c V} (ht : s.tripleOfHom hU V x = t) :
    t.u ≫ c.U'.ι ≫ s.f = (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).ι ≫ x := by
  subst ht
  exact s.restrictU_comp_ι_comp_f hU V x

/-- The third component of a triple equal to the triple of `x` is the completion of `x`. -/
theorem xhat_comp_eq_of_tripleOfHom_eq {t : Triple c V} (ht : s.tripleOfHom hU V x = t) :
    t.xhat ≫ s.a.inv ≫ Space.completionSheafInclusion B S hS X s.T =
      Space.completionSheafInclusion B S hS (yoneda.obj V) t.Z ≫
        Space.sheafifiedULiftMap B S hS x := by
  subst ht
  exact s.restrictW_comp V x

/-- **The triple determines the morphism**, for `V` locally Noetherian: two morphisms
`V ⟶ X` with the same triple agree on `V ∖ Z` (both are `f ∘ u'`) and on `V_{/Z}` (both are
`a⁻¹ ∘ x̂`), hence are equal by the uniqueness statement of Stacks 0GI1. -/
theorem tripleOfHom_injective (hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)) :
    Function.Injective (s.tripleOfHom hU V) := by
  intro x y h
  refine Space.eq_of_eq_on_compl_of_eq_on_completion B S hS (isAlgebraicSpace_yoneda B S hS V)
    s.isAlgebraicSpace_X (hasEtaleLocalProperty_yoneda V hV)
    (s.tripleOfHom hU V y).isClosed_Z x y ?_ ?_
  · rw [← s.u_comp_eq_of_tripleOfHom_eq hU V x h, ← s.u_comp_eq_of_tripleOfHom_eq hU V y rfl]
  · refine Space.completionSubfunctor_ι_whiskerRight_eq B S hS s.isAlgebraicSpace_X _ _ _ ?_
    rw [← s.xhat_comp_eq_of_tripleOfHom_eq hU V x h, ← s.xhat_comp_eq_of_tripleOfHom_eq hU V y rfl]

/-! ### From a triple to a pair `(V' ⟶ X, V_{/Z} ⟶ X)` -/

variable {V}

/-- The morphism of completion subfunctors `V_{/Z} ⟶ X_{/T}` attached to a triple `(Z, u', x̂)`:
`a⁻¹ ∘ x̂`, read on the subfunctors of sections with image in `Z` and in `T` (the latter is a
sheaf, so it is its own completion). -/
noncomputable def formalAux (t : Triple c V) :
    (Space.completionSubfunctor B S hS (yoneda.obj V) t.Z).toFunctor ⟶
      (Space.completionSubfunctor B S hS X s.T).toFunctor :=
  (BigFppfOver.topology B S hS).toSheafify _ ≫ (t.xhat ≫ s.a.inv).hom ≫
    ((BigFppfOver.topology B S hS).isoSheafify
      (Space.isSheaf_completionSubfunctor B S hS s.isAlgebraicSpace_X.isSheaf s.T)).inv

/-- The morphism `V_{/Z} ⟶ X` attached to a triple `(Z, u', x̂)`: `a⁻¹ ∘ x̂`, read on the
completion subfunctor of sections of `V` with image in `Z` and with values in `X`. This is the
morphism along which Stacks 0GI3 extends. -/
noncomputable def formalOfTriple (t : Triple c V) :
    (Space.completionSubfunctor B S hS (yoneda.obj V) t.Z).toFunctor ⟶
      X ⋙ uliftFunctor.{u + 1} :=
  s.formalAux t ≫ (Space.completionSubfunctor B S hS X s.T).ι

/-- `formalOfTriple` followed by sheafification is `a⁻¹ ∘ x̂` followed by the inclusion of
`X_{/T}`. -/
theorem formalOfTriple_comp_toSheafify (t : Triple c V) :
    s.formalOfTriple t ≫ (BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1}) =
      (BigFppfOver.topology B S hS).toSheafify _ ≫
        (t.xhat ≫ s.a.inv ≫ Space.completionSheafInclusion B S hS X s.T).hom := by
  have hnat : ((BigFppfOver.topology B S hS).isoSheafify
      (Space.isSheaf_completionSubfunctor B S hS s.isAlgebraicSpace_X.isSheaf s.T)).hom ≫
        (Space.completionSheafInclusion B S hS X s.T).hom =
      (Space.completionSubfunctor B S hS X s.T).ι ≫
        (BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1}) :=
    ((BigFppfOver.topology B S hS).toSheafify_naturality _).symm
  have hiso : ((BigFppfOver.topology B S hS).isoSheafify
      (Space.isSheaf_completionSubfunctor B S hS s.isAlgebraicSpace_X.isSheaf s.T)).inv ≫
        (Space.completionSubfunctor B S hS X s.T).ι ≫
          (BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1}) =
      (Space.completionSheafInclusion B S hS X s.T).hom :=
    (Iso.inv_comp_eq _).2 hnat.symm
  simp only [formalOfTriple, formalAux, Category.assoc]
  exact congrArg (fun k => (BigFppfOver.topology B S hS).toSheafify _ ≫
    (t.xhat ≫ s.a.inv).hom ≫ k) hiso

/-- The sheafification of `ι ≫ x` is the inclusion of the completion followed by `x`. -/
theorem toSheafify_comp_completionSheafInclusion {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Z : Set (Space.points B S hS Y)) (y : Y ⟶ X) :
    (BigFppfOver.topology B S hS).toSheafify _ ≫
        (Space.completionSheafInclusion B S hS Y Z ≫ Space.sheafifiedULiftMap B S hS y).hom =
      (Space.completionSubfunctor B S hS Y Z).ι ≫ Functor.whiskerRight y uliftFunctor.{u + 1} ≫
        (BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1}) := by
  have h1 : (BigFppfOver.topology B S hS).toSheafify
      (Space.completionSubfunctor B S hS Y Z).toFunctor ≫
        (Space.completionSheafInclusion B S hS Y Z).hom =
      (Space.completionSubfunctor B S hS Y Z).ι ≫
        (BigFppfOver.topology B S hS).toSheafify (Y ⋙ uliftFunctor.{u + 1}) :=
    ((BigFppfOver.topology B S hS).toSheafify_naturality _).symm
  have h2 : (BigFppfOver.topology B S hS).toSheafify (Y ⋙ uliftFunctor.{u + 1}) ≫
        (Space.sheafifiedULiftMap B S hS y).hom =
      Functor.whiskerRight y uliftFunctor.{u + 1} ≫
        (BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1}) :=
    ((BigFppfOver.topology B S hS).toSheafify_naturality _).symm
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (Space.sheafifiedULiftMap B S hS y).hom) h1)).trans
    ((Category.assoc _ _ _).trans (congrArg ((Space.completionSubfunctor B S hS Y Z).ι ≫ ·) h2))

/-- The sheaf-level compatibility of a triple: `a⁻¹ ∘ x̂` restricted to `V'_{/Z}` is the
completion of `f ∘ x'`. -/
theorem completionSheafMap_comp_xhat (t : Triple c V)
    (ω : CompatibilityWitness c V t.Z t.u t.xhat) :
    Space.completionSheafMap B S hS ω.p t.Z ≫ t.xhat ≫ s.a.inv ≫
        Space.completionSheafInclusion B S hS X s.T =
      Space.completionSheafInclusion B S hS ω.V' (Space.pointsMap B S hS ω.V' ω.p ⁻¹' t.Z) ≫
        Space.sheafifiedULiftMap B S hS (ω.x' ≫ s.f) := by
  rw [← Space.completionSheafRestrict_self B S hS ω.p t.Z le_rfl, ← Category.assoc,
    ω.isPullback_xhat'.w, Category.assoc, ← Category.assoc c.g, ← s.completionSheafRestrict_eq,
    Space.completionSheafRestrict_comp_inclusion, ← Category.assoc, ← ω.completion_x',
    Category.assoc, Space.sheafifiedULiftMap_comp]

/-- **The pair attached to a triple is compatible**, the hypothesis of Stacks 0GI3: the
morphism `f ∘ x' : V' ⟶ X` and the morphism `a⁻¹ ∘ x̂ : V_{/Z} ⟶ X` induce the same morphism
`V'_{/p⁻¹Z} ⟶ X`. -/
theorem completionMap_comp_formalOfTriple (t : Triple c V)
    (ω : CompatibilityWitness c V t.Z t.u t.xhat) :
    Space.completionMap B S hS ω.p t.Z ≫ s.formalOfTriple t =
      (Space.completionSubfunctor B S hS ω.V' (Space.pointsMap B S hS ω.V' ω.p ⁻¹' t.Z)).ι ≫
        Functor.whiskerRight (ω.x' ≫ s.f) uliftFunctor.{u + 1} := by
  have : IsIso ((BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1})) :=
    (BigFppfOver.topology B S hS).isIso_toSheafify
      (FormalSpace.isSheaf_comp_uliftFunctor B S hS s.isAlgebraicSpace_X)
  rw [← cancel_mono ((BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1})),
    Category.assoc, formalOfTriple_comp_toSheafify, Category.assoc,
    ← toSheafify_comp_completionSheafInclusion, ← completionSheafMap_comp_xhat s t ω]
  exact (reassoc_of% ((BigFppfOver.topology B S hS).toSheafify_naturality
    (Space.completionMap B S hS ω.p t.Z))) _

/-- `V ∖ Z ⟶ V ⟶ X` for a morphism `x` restricting to `f ∘ x'` on a witness: it is `f ∘ u'`. -/
theorem ι_comp_eq_of_comp_eq (t : Triple c V) (ω : CompatibilityWitness c V t.Z t.u t.xhat)
    (x : yoneda.obj V ⟶ X) (h1 : ω.p ≫ x = ω.x' ≫ s.f) :
    (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).ι ≫ x = t.u ≫ c.U'.ι ≫ s.f := by
  have hj : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).ι = ω.j ≫ ω.p := by
    have hw := ω.isPullback_j.w
    rwa [Category.id_comp] at hw
  rw [hj, Category.assoc, h1, ← Category.assoc, ω.restrict_x', Category.assoc]

include hU in
/-- If `x : V ⟶ X` restricts to `f ∘ u'` on `V ∖ Z`, then `x⁻¹T ⊆ Z`. -/
theorem preT_subset_of_ι_comp_eq {Z : Set (Space.points B S hS (yoneda.obj V))}
    (u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor)
    (x : yoneda.obj V ⟶ X)
    (hι : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι ≫ x = u ≫ c.U'.ι ≫ s.f) :
    s.preT V x ⊆ Z := by
  intro v hv
  by_contra hvZ
  obtain ⟨w, rfl⟩ : v ∈ Set.range (Space.pointsMap B S hS
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι) := by
    rwa [Space.range_pointsMap_ι_openSubspaceOfPoints]
  have hmem : Space.pointsMap B S hS _ (u ≫ s.isoU.hom ≫ s.U.ι) w ∈ s.Tᶜ := by
    rw [← hU]
    exact ⟨_, (Space.pointsMap_comp_apply B S hS _ _ _).symm.trans
      (by rw [← Category.assoc, Space.pointsMap_comp_apply])⟩
  rw [s.isoU_comp_ι, ← hι, Space.pointsMap_comp_apply] at hmem
  exact hmem hv

/-- If `x : V ⟶ X` restricted to `V_{/Z}` factors through `X_{/T}`, then `Z ⊆ x⁻¹T`. -/
theorem subset_preT_of_ι_whiskerRight_eq {Z : Set (Space.points B S hS (yoneda.obj V))}
    (x : yoneda.obj V ⟶ X)
    (φ : (Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor ⟶
      (Space.completionSubfunctor B S hS X s.T).toFunctor)
    (h : (Space.completionSubfunctor B S hS (yoneda.obj V) Z).ι ≫
        Functor.whiskerRight x uliftFunctor.{u + 1} =
      φ ≫ (Space.completionSubfunctor B S hS X s.T).ι) :
    Z ⊆ s.preT V x := by
  intro v hv
  obtain ⟨q, rfl⟩ := Quot.exists_rep v
  let N := q.siteObject
  have hn : Space.HasImageIn B S hS (yoneda.obj V) Z N q.value := by
    rw [Space.hasImageIn_iff_range_subset]
    rintro _ ⟨z, rfl⟩
    rwa [Space.FieldValuedPoint.pointsMap_eq_class]
  have happ : ULift.up (x.app (op N) q.value) = (φ.app (op N) ⟨ULift.up q.value, hn⟩).1 :=
    congrArg (fun ψ => ψ.app (op N) ⟨ULift.up q.value, hn⟩) h
  have hmem : Space.HasImageIn B S hS X s.T N (x.app (op N) q.value) := by
    have hprop := (φ.app (op N) ⟨ULift.up q.value, hn⟩).2
    rwa [← happ] at hprop
  rw [Space.hasImageIn_iff_range_subset, ← yonedaEquiv_symm_naturality_right] at hmem
  let z : Space.points B S hS (yoneda.obj N) :=
    Space.FieldValuedPoint.class B S hS _ ⟨q.carrier, q.contained, q.toBase, 𝟙 N⟩
  have hz := hmem ⟨z, rfl⟩
  rwa [Space.pointsMap_comp_apply, Space.FieldValuedPoint.pointsMap_eq_class] at hz

/-- **A morphism inducing the pair of a triple has that triple**, the converse construction of
the proof of Stacks 0GHB: if `x : V ⟶ X` restricts to `f ∘ x'` on `V'` and to `a⁻¹ ∘ x̂` on
`V_{/Z}`, then `x⁻¹T = Z`, `x` restricts to `u'` on `V ∖ Z`, and `a ∘ x_{/Z} = x̂`. -/
theorem tripleOfHom_eq_of_morToModificationCompletion_eq (t : Triple c V)
    (ω : CompatibilityWitness c V t.Z t.u t.xhat) (x : yoneda.obj V ⟶ X)
    (hx : Space.morToModificationCompletion B S hS ω.p t.Z X x =
      (ω.x' ≫ s.f, s.formalOfTriple t)) :
    s.tripleOfHom hU V x = t := by
  have h2 : (Space.completionSubfunctor B S hS (yoneda.obj V) t.Z).ι ≫
      Functor.whiskerRight x uliftFunctor.{u + 1} = s.formalOfTriple t := congrArg Prod.snd hx
  have hι := s.ι_comp_eq_of_comp_eq t ω x (congrArg Prod.fst hx)
  -- the closed subsets agree
  have hZ : s.preT V x = t.Z := (s.preT_subset_of_ι_comp_eq hU t.u x hι).antisymm
    (s.subset_preT_of_ι_whiskerRight_eq x (s.formalAux t) h2)
  -- the remaining components agree
  obtain ⟨Z, hc, u, xh, adic, comp⟩ := t
  dsimp only at hZ hι h2 ⊢
  subst hZ
  refine Triple.mk_congr rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · rwa [← cancel_mono (c.U'.ι ≫ s.f), s.restrictU_comp_ι_comp_f]
  · have := Space.mono_completionSheafInclusion B S hS X s.T
    rw [← cancel_mono (s.a.inv ≫ Space.completionSheafInclusion B S hS X s.T), s.restrictW_comp]
    refine Sheaf.hom_ext ((BigFppfOver.topology B S hS).sheafify_hom_ext _ _
      (Space.sheafifiedULift B S hS X).property ?_)
    rw [toSheafify_comp_completionSheafInclusion, ← Category.assoc, h2]
    exact s.formalOfTriple_comp_toSheafify (Triple.mk _ hc u xh adic comp)

/-- The proper morphism `p : V' ⟶ V` of a compatibility witness is an isomorphism over
`V ∖ Z`, in the form of Stacks 0GI3: the second projection of `p⁻¹(V ∖ Z) ⟶ V ∖ Z` is an
isomorphism. -/
theorem
    _root_.AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.isIso_pullback_snd_p
    {V : BigFppfOver B S hS} {Z : Set (Space.points B S hS (yoneda.obj V))}
    {u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    (ω : CompatibilityWitness c V Z u xhat) :
    IsIso (pullback.snd ω.p (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι) := by
  have h := ω.isPullback_j.flip.isoPullback_hom_snd
  rw [← Iso.eq_inv_comp, Category.comp_id] at h
  rw [h]
  infer_instance

/-! ### The natural transformation `Mor_S(-, X) ⟶ F` -/

/-- **The natural transformation `Mor_S(-, X) ⟶ F`** of Stacks 0GHB on locally Noetherian
schemes over `S`, sending `x : V ⟶ X` to its triple
`AlgebraicGeometry.Artin.ContractionSituation.Solution.tripleOfHom`. -/
noncomputable def homToTriple : morOnLocallyNoetherian B S hS X ⟶ contractionFunctor c where
  app V := ↾fun y => s.tripleOfHom hU V.unop.obj (yonedaEquiv.symm y.down)
  naturality V₁ V₂ φ := by
    ext y
    change s.tripleOfHom hU V₂.unop.obj (yonedaEquiv.symm (X.map φ.unop.hom.op y.down)) =
      mapTriple c φ.unop.hom (s.tripleOfHom hU V₁.unop.obj (yonedaEquiv.symm y.down))
    exact (congrArg (s.tripleOfHom hU V₂.unop.obj)
      (yonedaEquiv_symm_map φ.unop.hom.op y.down)).trans (s.tripleOfHom_comp hU φ.unop.hom _)

/-- For `V` locally Noetherian, distinct morphisms `V ⟶ X` have distinct triples. -/
theorem homToTriple_app_injective (V : (LocallyNoetherianOver B S hS)ᵒᵖ) :
    Function.Injective ((s.homToTriple hU).app V) := by
  intro y₁ y₂ h
  exact ULift.ext _ _ (yonedaEquiv.symm.injective
    (s.tripleOfHom_injective hU V.unop.obj V.unop.property
      (h : s.tripleOfHom hU V.unop.obj (yonedaEquiv.symm y₁.down) =
        s.tripleOfHom hU V.unop.obj (yonedaEquiv.symm y₂.down))))

/-- **Every triple comes from a morphism**, for `V` locally Noetherian: for a triple
`(Z, u', x̂)` with witness `V' ⟶ V`, `x̂'`, `x'`, the existence half of Stacks 0GI3 gives
`x : V ⟶ X` agreeing with `x̂` over `V_{/Z}` and with `x'` over `V'`, and its triple is
`(Z, u', x̂)`. -/
theorem homToTriple_app_surjective (V : (LocallyNoetherianOver B S hS)ᵒᵖ) :
    Function.Surjective ((s.homToTriple hU).app V) := by
  intro t
  obtain ⟨ω⟩ := t.compatible
  obtain ⟨x, hx⟩ := Space.exists_morToModificationCompletion_eq B S hS
    (isAlgebraicSpace_yoneda B S hS V.unop.obj) ω.isAlgebraicSpace_V' s.isAlgebraicSpace_X
    (hasEtaleLocalProperty_yoneda V.unop.obj V.unop.property) t.isClosed_Z ω.p ω.isProper_p
    ω.isIso_pullback_snd_p (ω.x' ≫ s.f) (s.formalOfTriple t)
    (s.completionMap_comp_formalOfTriple t ω)
  refine ⟨ULift.up (yonedaEquiv x), ?_⟩
  have h := s.tripleOfHom_eq_of_morToModificationCompletion_eq hU t ω x hx
  rwa [← Equiv.symm_apply_apply yonedaEquiv x] at h

/-- The natural transformation `Mor_S(-, X) ⟶ F` is an isomorphism. -/
instance isIso_homToTriple : IsIso (s.homToTriple hU) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun V => ?_)
  rw [isIso_iff_bijective]
  exact ⟨s.homToTriple_app_injective hU V, s.homToTriple_app_surjective hU V⟩

/-- **Stacks 0GHB, corrected.** In the situation of Stacks 0GH8, a solution
`(f : X' ⟶ X, T, a)` whose open subspace `U` is the complement of `T`, `|U| = |X| ∖ T`, gives a
functorial bijection `F(V) = Mor_S(V, X)` on the category of locally Noetherian schemes `V` over
`S`, where `F` is Artin's functor of Stacks 0GHA: `x : V ⟶ X` corresponds to
`(x⁻¹T, x|_{V ∖ Z}, a ∘ x_{/Z})`.

The source states this for every solution, but its notion of solution (the prose after
Situation 0GH8, `AlgebraicGeometry.Artin.ContractionSituation.Solution`) does not ask
`|U| = |X| ∖ T`, and without that the statement is false:
`AlgebraicGeometry.Artin.ContractionSituation.not_forall_nonempty_iso_of_solution`. The source's
proof uses `u' : V ∖ Z ⟶ U' = U` as the restriction of `x` to `V ∖ Z = x⁻¹(|X| ∖ T)`, which is
the condition added here. -/
@[stacks 0GHB "corrected: the solution is assumed to satisfy |U| = |X| ∖ T (the open subspace U \
of condition (2) is the complement of T), as the source's proof uses (u' : V ∖ Z → U' = U is \
the restriction of x to V ∖ Z = x⁻¹(X ∖ T)); for the literal notion of solution of Situation \
0GH8 the printed statement is false, see \
AlgebraicGeometry.Artin.ContractionSituation.not_forall_nonempty_iso_of_solution"]
noncomputable def contractionFunctorIso :
    contractionFunctor c ≅ morOnLocallyNoetherian B S hS X :=
  (asIso (s.homToTriple hU)).symm

end Solution

end AlgebraicGeometry.Artin.ContractionSituation

end
