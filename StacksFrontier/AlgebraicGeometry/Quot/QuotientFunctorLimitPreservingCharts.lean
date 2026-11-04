module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimitPreservingStages
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorSourceSheafUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSingletonCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Stacks 082Q: the functor of quotients as an equalizer over two charts

In the proof of Stacks 082Q the source chooses an affine scheme `U` surjective and étale over
`X` (Stacks 03H6) and checks the conditions of a quotient after pulling back to `U`.  On the
level of functors this is Stacks 08IV: for `a : U ⟶ X` surjective and étale and
`b : V ⟶ U ×_X U` surjective and étale, the restriction

`Q^{fp}_{F/X/Y}(T) ⟶ Q^{fp}_{F_U/U/Y}(T) ⇉ Q^{fp}_{F_V/V/Y}(T)`

presents the first set as the equalizer of the other two, naturally in `T`.  Limit preservation
passes to such an equalizer (`AlgebraicGeometry.limitPreserving_of_isEqualizer`), so `Q^{fp}` is
limit preserving as soon as the functors of finitely presented quotients of the two charts are.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsToMember`: restriction of
  finitely presented quotients to a flat `a : W ⟶ X`, as a morphism of functors.
* `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsBetweenMembers`:
  restriction of finitely presented quotients along a flat morphism of members, as a morphism of
  functors.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.restrictQuotientToMember_quotientPullback` and
  `AlgebraicGeometry.Space.QuotientSituation.restrictQuotientBetweenMembers_quotientPullback`:
  the arrows of the diagram of Stacks 08IV are natural in the test scheme.
* `QuotientSituation.limitPreserving_finitePresentationQuotientsFunctor_of_charts`:
  **the chart step of the proof of Stacks 082Q.**

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
* [Stacks Project, Tag 08IV](https://stacks.math.columbia.edu/tag/08IV)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-! ### The arrows of Stacks 08IV are natural in the test scheme -/

/-- The base change of a morphism over `Y` commutes with the morphisms of base changes induced
by a morphism of test schemes. -/
theorem baseChangeMap_comp_baseChangeAlong {Y W W' : AlgebraicSpaces B S hS} {c : W ⟶ Y}
    {c' : W' ⟶ Y} (b : W' ⟶ W) (hb : b ≫ c = c') {T' T : SchemesOver Y} (h : T' ⟶ T) :
    baseChangeMap c' h ≫ baseChangeAlong b hb T = baseChangeAlong b hb T' ≫ baseChangeMap c h :=
  baseChange_hom_ext c (by simp) (by simp)

/-- **The first arrow of Stacks 08IV is natural in the test scheme.**  Restricting to a member
`a : W ⟶ X` the pullback of a quotient along `h : T' ⟶ T` is pulling back its restriction. -/
theorem restrictQuotientToMember_quotientPullback {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X)
    {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) :
    D.restrictQuotientToMember a T' (D.quotientPullback h K) =
      (D.sourceRestricted a).quotientPullback h (D.restrictQuotientToMember a T K) :=
  eq_quotientRestrictOver_of_quotientTransport_eq (a := a) (baseChangeMap (a ≫ D.f) h)
    (baseChangeMap_comp_projection _ h) (D.relativeMap h) (baseChangeMap_comp_projection _ h)
    rfl rfl (D.baseChangeAlong_comp_sourceProjection a T)
    (D.baseChangeAlong_comp_sourceProjection a T')
    (baseChangeMap_comp_baseChangeAlong a rfl h) D.F K
    (D.quotientTransport_sourceNodeIso_symm_restrictQuotientToMember a T K)
    (D.quotientTransport_sourceNodeIso_symm_restrictQuotientToMember a T'
      (D.quotientPullback h K))

/-- The morphism of base changes induced by a morphism of test schemes commutes with the
canonical morphisms of a node of a covering diagram of the source to `X`. -/
theorem baseChangeMap_comp_sourceNodeMap {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X)
    {T' T : SchemesOver D.Y} (h : T' ⟶ T) :
    baseChangeMap (a ≫ D.f) h ≫ D.sourceNodeMap a T = D.sourceNodeMap a T' := by
  simp only [sourceNodeMap, baseChangeMap_comp_projection_assoc]

/-- **The two other arrows of Stacks 08IV are natural in the test scheme.**  Restricting along a
morphism `b : W' ⟶ W` of members the pullback of a quotient along `h : T' ⟶ T` is pulling back
its restriction. -/
theorem restrictQuotientBetweenMembers_quotientPullback {W W' : AlgebraicSpaces B S hS}
    {a : W ⟶ D.X} {a' : W' ⟶ D.X} (b : W' ⟶ W) (hb : b ≫ a = a') {T' T : SchemesOver D.Y}
    (h : T' ⟶ T)
    (K : Subobject ((D.sourceRestricted a).baseChangeModule T)) :
    D.restrictQuotientBetweenMembers b hb T'
        ((D.sourceRestricted a).quotientPullback h K) =
      (D.sourceRestricted a').quotientPullback h
        (D.restrictQuotientBetweenMembers b hb T K) := by
  have hρ := D.baseChangeMap_comp_sourceNodeMap a h
  have hg := quotientTransport_quotientRestrictOver_modulePullback (a := a)
    (baseChangeMap (a ≫ D.f) h) (baseChangeMap_comp_projection _ h)
    (rfl : baseChangeProjection (a ≫ D.f) T ≫ a = D.sourceNodeMap a T)
    (rfl : baseChangeProjection (a ≫ D.f) T' ≫ a = D.sourceNodeMap a T') hρ D.F K
  exact eq_quotientRestrictOver_of_quotientTransport_eq (a := a') (baseChangeMap (a' ≫ D.f) h)
    (baseChangeMap_comp_projection _ h) (baseChangeMap (a ≫ D.f) h) hρ rfl rfl
    (D.baseChangeAlong_comp_sourceNodeMap b hb T) (D.baseChangeAlong_comp_sourceNodeMap b hb T')
    (baseChangeMap_comp_baseChangeAlong b _ h) D.F
    (quotientTransport (D.sourceNodeIso a T).symm K)
    (D.quotientTransport_sourceNodeIso_symm_restrictQuotientBetweenMembers b hb T K)
    ((D.quotientTransport_sourceNodeIso_symm_restrictQuotientBetweenMembers b hb T'
      ((D.sourceRestricted a).quotientPullback h K)).trans
        (congrArg (quotientRestrictOver (baseChangeAlong b (D.sourceRestricted_comp_f b hb) T')
          (D.baseChangeAlong_comp_sourceNodeMap b hb T') D.F) hg))

/-! ### The arrows of Stacks 08IV as morphisms of functors -/

/-- **The two other arrows of Stacks 08IV are well defined for `Q^{fp}`.**  The restriction
along a flat morphism `b : W' ⟶ W` of members of an element of `Q^{fp}_{F_W/W/Y}(T)` is an
element of `Q^{fp}_{F_{W'}/W'/Y}(T)`. -/
theorem restrictQuotientBetweenMembers_mem_finitePresentationQuotients_of_isFlat
    {W W' : AlgebraicSpaces B S hS} {a : W ⟶ D.X} {a' : W' ⟶ D.X} (b : W' ⟶ W)
    (hb : b ≫ a = a') (hbf : IsFlat B S hS b.hom) (T : SchemesOver D.Y)
    {K : Subobject ((D.sourceRestricted a).baseChangeModule T)}
    (hK : K ∈ (D.sourceRestricted a).finitePresentationQuotients T) :
    D.restrictQuotientBetweenMembers b hb T K ∈
      (D.sourceRestricted a').finitePresentationQuotients T := by
  let e := D.restrictQuotientBetweenMembersCokernelIso b hb T K
  refine ⟨⟨SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hK.1.1), ?_⟩,
    SheafOfModules.IsFinitePresentationOnSite.of_iso e.symm
      (isFinitePresentationOnSite_modulePullback B S hS _ _ hK.2)⟩
  exact IsFlatOver.of_iso B S hS _ e.symm
    (isFlatOver_modulePullback_of_isFlat B S hS
      (baseChangeAlong b (D.sourceRestricted_comp_f b hb) T)
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback
        (isPullback_baseChangeAlong b (D.sourceRestricted_comp_f b hb) T) hbf)
      (baseChangeAlong_comp_inclusion b _ T) _ hK.1.1 hK.1.2)

/-- **The first arrow of Stacks 08IV for `Q^{fp}`, as a morphism of functors**: restriction of
finitely presented quotients to a flat `a : W ⟶ X`. -/
def finitePresentationQuotientsToMember {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X)
    (ha : IsFlat B S hS a.hom) :
    D.finitePresentationQuotientsFunctor ⟶
      (D.sourceRestricted a).finitePresentationQuotientsFunctor where
  app T := ↾fun K ↦ ⟨D.restrictQuotientToMember a T.unop K.1,
    D.restrictQuotientToMember_mem_finitePresentationQuotients a ha T.unop K.2⟩
  naturality T T' m := by
    ext K
    exact Subtype.ext (D.restrictQuotientToMember_quotientPullback a m.unop K.1)

/-- **The two other arrows of Stacks 08IV for `Q^{fp}`, as morphisms of functors**: restriction
of finitely presented quotients along a flat morphism `b : W' ⟶ W` of members. -/
def finitePresentationQuotientsBetweenMembers {W W' : AlgebraicSpaces B S hS} {a : W ⟶ D.X}
    {a' : W' ⟶ D.X} (b : W' ⟶ W) (hb : b ≫ a = a') (hbf : IsFlat B S hS b.hom) :
    (D.sourceRestricted a).finitePresentationQuotientsFunctor ⟶
      (D.sourceRestricted a').finitePresentationQuotientsFunctor where
  app T := ↾fun K ↦ ⟨D.restrictQuotientBetweenMembers b hb T.unop K.1,
    D.restrictQuotientBetweenMembers_mem_finitePresentationQuotients_of_isFlat b hb hbf
      T.unop K.2⟩
  naturality T T' m := by
    ext K
    exact Subtype.ext (D.restrictQuotientBetweenMembers_quotientPullback b hb m.unop K.1)

/-- The restriction of a finitely presented quotient to a member, read on subobjects. -/
theorem finitePresentationQuotientsToMember_app_val {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X)
    (ha : IsFlat B S hS a.hom) (T : (SchemesOver D.Y)ᵒᵖ)
    (K : D.finitePresentationQuotientsFunctor.obj T) :
    ((D.finitePresentationQuotientsToMember a ha).app T K).1 =
      D.restrictQuotientToMember a T.unop K.1 :=
  rfl

/-- The restriction of a finitely presented quotient along a morphism of members, read on
subobjects. -/
theorem finitePresentationQuotientsBetweenMembers_app_val {W W' : AlgebraicSpaces B S hS}
    {a : W ⟶ D.X} {a' : W' ⟶ D.X} (b : W' ⟶ W) (hb : b ≫ a = a') (hbf : IsFlat B S hS b.hom)
    (T : (SchemesOver D.Y)ᵒᵖ)
    (K : (D.sourceRestricted a).finitePresentationQuotientsFunctor.obj T) :
    ((D.finitePresentationQuotientsBetweenMembers b hb hbf).app T K).1 =
      D.restrictQuotientBetweenMembers b hb T.unop K.1 := by
  dsimp only [finitePresentationQuotientsBetweenMembers]
  rfl

/-! ### The chart step -/

/-- **The chart step of the proof of Stacks 082Q.**  Let `a : U ⟶ X` be surjective and étale and
let `b : V ⟶ U ×_X U` be surjective and étale.  If the functors of finitely presented quotients
of the restrictions of the situation to `U` and to `V` are limit preserving, so is
`Q^{fp}_{F/X/Y}`. -/
theorem limitPreserving_finitePresentationQuotientsFunctor_of_charts
    {U V : AlgebraicSpaces B S hS} (a : U ⟶ D.X)
    (b : V ⟶ AlgebraicSpaces.fiberProduct B S hS a a)
    (ha : IsEtale B S hS a.hom) (ha' : IsSurjective B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hb' : IsSurjective B S hS b.hom)
    (hU : LimitPreserving.{u, u + 1, u, u}
      (D.sourceRestricted a).testScheme
      (D.sourceRestricted a).finitePresentationQuotientsFunctor)
    (hV : LimitPreserving.{u, u + 1, u, u}
      (D.sourceRestricted ((b ≫ fiberFst a a) ≫ a)).testScheme
      (D.sourceRestricted ((b ≫ fiberFst a a) ≫ a)).finitePresentationQuotientsFunctor) :
    LimitPreserving.{u, u + 1, u, u} D.testScheme D.finitePresentationQuotientsFunctor := by
  have haf : IsFlat B S hS a.hom := isFlat_of_isEtale B S hS ha
  have hbf : IsFlat B S hS b.hom := isFlat_of_isEtale B S hS hb
  have hP := AlgebraicSpaces.isPullback_fiberProduct B S hS a a
  have hfstf : IsFlat B S hS (fiberFst a a).hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hP.flip haf
  have hsndf : IsFlat B S hS (fiberSnd a a).hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hP haf
  have h₁f : IsFlat B S hS (b ≫ fiberFst a a).hom :=
    isFlat_comp B S hS V.property (AlgebraicSpaces.fiberProduct B S hS a a).property U.property
      _ _ hbf hfstf
  have h₂f : IsFlat B S hS (b ≫ fiberSnd a a).hom :=
    isFlat_comp B S hS V.property (AlgebraicSpaces.fiberProduct B S hS a a).property U.property
      _ _ hbf hsndf
  have hcomm : (b ≫ fiberSnd a a) ≫ a = (b ≫ fiberFst a a) ≫ a := by
    rw [Category.assoc, Category.assoc, hP.w]
  have hcovU : IsFpqcCovering B S hS (fun _ : PUnit.{1} ↦ a.hom) :=
    isFpqcCovering_of_isFppfCovering B S hS _ _
      (isFppfCovering_singleton.{u, 0} B S hS a ha' haf
        (isLocallyOfFinitePresentation_of_isEtale B S hS ha))
  have hcovV : ∀ _ _ : PUnit.{1}, IsFpqcCovering B S hS (fun _ : PUnit.{1} ↦ b.hom) :=
    fun _ _ ↦ isFpqcCovering_of_isFppfCovering B S hS _ _
      (isFppfCovering_singleton.{u, 0} B S hS b hb' hbf
        (isLocallyOfFinitePresentation_of_isEtale B S hS hb))
  have key := fun (T : SchemesOver D.Y) ↦
    D.bijOn_restrictQuotientToMember_finitePresentation_of_isFpqcCovering
      (I := PUnit.{1}) (κ := fun _ _ ↦ PUnit.{1}) (W := fun _ ↦ U)
      (P := fun _ _ ↦ AlgebraicSpaces.fiberProduct B S hS a a) (Z := fun _ _ _ ↦ V)
      (fun _ ↦ a) (c₀ := fun _ _ ↦ fiberFst a a) (c₁ := fun _ _ ↦ fiberSnd a a)
      (d := fun _ _ ↦ fiberFst a a ≫ a) (fun _ _ _ ↦ b)
      (e := fun _ _ _ ↦ (b ≫ fiberFst a a) ≫ a) hcovU (fun _ _ ↦ hP) (fun _ _ ↦ rfl)
      (fun _ _ ↦ hP.w.symm) hcovV (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ hcomm) T
  have hinj : ∀ (T : SchemesOver D.Y) (K K' : Subobject (D.baseChangeModule T)),
      K ∈ D.finitePresentationQuotients T → K' ∈ D.finitePresentationQuotients T →
      D.restrictQuotientToMember a T K =
        D.restrictQuotientToMember a T K' →
      K = K' :=
    fun T K K' hK hK' h ↦ (key T).injOn hK hK' (funext fun _ ↦ h)
  have heq : ∀ (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)),
      K ∈ D.finitePresentationQuotients T →
      D.restrictQuotientBetweenMembers (b ≫ fiberFst a a) rfl T
          (D.restrictQuotientToMember a T K) =
        D.restrictQuotientBetweenMembers (b ≫ fiberSnd a a) hcomm T
          (D.restrictQuotientToMember a T K) :=
    fun T K hK ↦ ((key T).mapsTo hK).2 PUnit.unit PUnit.unit PUnit.unit
  have hsurj : ∀ (T : SchemesOver D.Y)
      (Q : Subobject ((D.sourceRestricted a).baseChangeModule T)),
      Q ∈ (D.sourceRestricted a).finitePresentationQuotients T →
      D.restrictQuotientBetweenMembers (b ≫ fiberFst a a) rfl T Q =
        D.restrictQuotientBetweenMembers (b ≫ fiberSnd a a) hcomm T Q →
      ∃ K ∈ D.finitePresentationQuotients T,
        D.restrictQuotientToMember a T K = Q := by
    intro T Q hQ h
    obtain ⟨K, hK, hKQ⟩ := (key T).surjOn (show (fun _ : PUnit.{1} ↦ Q) ∈ _ from
      ⟨fun _ ↦ hQ, fun _ _ _ ↦ h⟩)
    exact ⟨K, hK, congrFun hKQ PUnit.unit⟩
  refine limitPreserving_of_isEqualizer D.testScheme (D.finitePresentationQuotientsToMember a haf)
    (D.finitePresentationQuotientsBetweenMembers (b ≫ fiberFst a a) rfl h₁f)
    (D.finitePresentationQuotientsBetweenMembers (b ≫ fiberSnd a a) hcomm h₂f) ?_ ?_ ?_ hU hV
  · intro T x y hxy
    exact Subtype.ext (hinj T.unop x.1 y.1 x.2 y.2 (congrArg Subtype.val hxy))
  · intro T x
    apply Subtype.ext
    rw [finitePresentationQuotientsBetweenMembers_app_val,
      finitePresentationQuotientsBetweenMembers_app_val,
      finitePresentationQuotientsToMember_app_val]
    exact heq T.unop x.1 x.2
  · intro T q hq
    have hq' := congrArg Subtype.val hq
    rw [finitePresentationQuotientsBetweenMembers_app_val,
      finitePresentationQuotientsBetweenMembers_app_val] at hq'
    obtain ⟨K, hK, hKq⟩ := hsurj T.unop q.1 q.2 hq'
    exact ⟨⟨K, hK⟩, Subtype.ext hKq⟩

end QuotientSituation

end AlgebraicGeometry.Space

end
