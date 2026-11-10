module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionStageNaturality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallEtaleSite.StageEtaleSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom

/-!
# A representable étale chart of a formal spectrum is the formal spectrum of an étale algebra

Let `S` be a scheme of a big fppf site, let `R` be a weakly admissible linearly topologized
ring over `S` presented by a quotient system `D`, and let `v : V ⟶ Spf R` be a morphism from an
affine formal algebraic space which is representable by algebraic spaces and étale. This file
proves that `V` is `Spf A^∧` for an étale `R`-algebra `A`, compatibly with the morphisms to
`Spf R`: that is the **essential-surjectivity clause of Stacks 0AN8**.

The argument has two halves. The geometric half,
`AlgebraicGeometry.FormalSpace.StageEtale.exists_etale_algebra_of_isRepresentableEtale`,
produces the étale `R`-algebra `A` together with ring isomorphisms

`θ J : A ⧸ JA ≅ Γ(Spec (R ⧸ J) ×_{Spf R} V)` over `R ⧸ J`,

natural in the weak ideal of definition `J` of `R`. The colimit half,
`AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIso`, turns an isomorphism of
*diagrams of sheaves* between the stage base changes of `V` and the quotient stages of `A^∧`
into an isomorphism `V ≅ Spf A^∧`. This file joins them: it lifts the family
`θ` to that isomorphism of diagrams, and records the compatibility with the morphisms to
`Spf R` which the colimit half does not state.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.isoOfSchemeIso`: an isomorphism of the underlying schemes of
  two objects of the big fppf category over `S` which commutes with their structure morphisms,
  as an isomorphism of that category.
* `AlgebraicGeometry.FormalSpace.StageEtale.stageRingEquiv` and `…stageSchemeIso`: the family
  `θ` composed with the identification `A^∧ ⧸ ker (A^∧ → A ⧸ JA) ≅ A ⧸ JA`, as a ring
  isomorphism and as an isomorphism of affine schemes.
* `AlgebraicGeometry.FormalSpace.StageEtale.stageOverIso` and `…stageNatIso`: the same
  isomorphism over `S`, and the resulting isomorphism of diagrams of objects of the site.
* `AlgebraicGeometry.FormalSpace.StageEtale.stageBaseChangeNatIso`: the chosen models of the
  stage base changes are the stage base changes.
* `AlgebraicGeometry.FormalSpace.StageEtale.assemblyNatIso`: the isomorphism of diagrams of
  sheaves which `AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIso` consumes.

## Main results

* `AlgebraicGeometry.FormalSpace.hom_isoFormalSpectrumOfStageNatIso_comp`: the isomorphism
  produced by the colimit half commutes with the morphisms to `Spf R`, provided the given
  identification of diagrams does so stagewise.
* `AlgebraicGeometry.FormalSpace.exists_etale_completionOver_isoFormalSpectrum`: the
  essential-surjectivity clause of Stacks 0AN8, which is
  `AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf`.

## Implementation notes

The one step with content is the lift of a ring isomorphism to an isomorphism *over `S`*. A
quotient stage of `Spf A^∧` and the chosen model of a stage base change of `V` are objects of
the big fppf category over `S`, and `θ J` only identifies their rings of global sections; the
structure morphisms to `S` have to be matched as well. They match because both factor through
the stage `Spec (R ⧸ J)`: the projection of the chosen model is
`AlgebraicGeometry.FormalSpace.StageEtale.proj` and the projection of the quotient stage is
`AlgebraicGeometry.FormalSpace.ContinuousHom.stageMap`, the compatibility of `θ J` with the two
structure homomorphisms over `R ⧸ J` makes the scheme isomorphism commute with those two
projections, and a morphism over `Spec (R ⧸ J)` is a morphism over `S` because the stage itself
lies over `S`. That is
`AlgebraicGeometry.FormalSpace.StageEtale.stageSchemeIso_hom_comp_specMap`, whose geometric
consequence is `AlgebraicGeometry.FormalSpace.StageEtale.stageOverIso`.

The naturality of the lifted family in `J` is the naturality of `θ` together with the
compatibility condition defining `TopologicalRing.CompletionOver`, which is
`AlgebraicGeometry.FormalSpace.transitionMap_quotientKerProjectionRingEquiv`; both are read on
schemes through `AlgebraicGeometry.Scheme.isoSpec` and transported to the site by the
faithfulness of `AlgebraicGeometry.BigFppfOver.toScheme`.

The identification of the chosen models with the fibre products themselves is the uniqueness
of a fibre product: `AlgebraicGeometry.FormalSpace.StageEtale.isPullback` exhibits the chosen
model as `Spec (R ⧸ J) ×_{Spf R} V`, so
`CategoryTheory.IsPullback.isoPullback` compares it with the chosen pullback that
`AlgebraicGeometry.FormalSpace.stageBaseChangeDiagram` is built from, and the transition
morphisms agree because both squares project to the same two legs
(`AlgebraicGeometry.FormalSpace.StageEtale.trans_fst` and `…trans_proj`).

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An isomorphism of the underlying schemes of two objects of the big fppf category over `S`
which commutes with their structure morphisms, as an isomorphism of that category. This is the
isomorphism form of `AlgebraicGeometry.BigFppfOver.homOfCompEq`. -/
def BigFppfOver.isoOfSchemeIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (BigFppfOver.toScheme B S hS).obj W)
    (he : e.hom ≫ B.inclusion.map W.hom = B.inclusion.map T.hom) : T ≅ W where
  hom := BigFppfOver.homOfCompEq B S hS e.hom he
  inv := BigFppfOver.homOfCompEq B S hS e.inv (by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp])
  hom_inv_id := BigFppfOver.map_toScheme_injective B S hS (by
    change (BigFppfOver.toScheme B S hS).map (_ ≫ _) = (BigFppfOver.toScheme B S hS).map (𝟙 T)
    simp only [Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq]
    exact e.hom_inv_id)
  inv_hom_id := BigFppfOver.map_toScheme_injective B S hS (by
    change (BigFppfOver.toScheme B S hS).map (_ ≫ _) = (BigFppfOver.toScheme B S hS).map (𝟙 W)
    simp only [Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq]
    exact e.inv_hom_id)

/-- On underlying schemes, the forward map of `BigFppfOver.isoOfSchemeIso e he` is `e.hom`. -/
@[simp]
theorem BigFppfOver.toScheme_map_isoOfSchemeIso_hom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {T W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (BigFppfOver.toScheme B S hS).obj W)
    (he : e.hom ≫ B.inclusion.map W.hom = B.inclusion.map T.hom) :
    (BigFppfOver.toScheme B S hS).map (BigFppfOver.isoOfSchemeIso B S hS e he).hom = e.hom :=
  BigFppfOver.toScheme_map_homOfCompEq B S hS e.hom he

end AlgebraicGeometry

namespace AlgebraicGeometry.FormalSpace

/-! ### The compatibility of the colimit assembly with the morphisms to `Spf R` -/

section Compatibility

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R A : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
  [CommRing A] (f : R →+* A)

/-- **The isomorphism `V ≅ Spf A^∧` of the colimit assembly lies over `Spf R`.** Let
`v : V ⟶ Spf R` be a morphism of fppf sheaves and let `α` identify the stage base changes of
`v` with the quotient stages of the relative completion `A^∧`. If at every weak ideal of
definition `J` of `R` the component of `α` carries the projection of the quotient stage to
`Spec (R ⧸ J)` to the projection of the stage base change, then the isomorphism
`V ≅ Spf A^∧` produced by
`AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIso` composed with `Spf` of the
canonical map is `v`.

Both sides are morphisms out of a colimit, so it suffices to check them on each stage, where
the claim is the hypothesis together with the defining effect of `Spf` of the canonical map on
quotient stages (`AlgebraicGeometry.FormalSpace.formalSpectrumMap_spec`) and the cartesian
square defining the stage base change. -/
theorem hom_isoFormalSpectrumOfStageNatIso_comp
    (hR : TopologicalRing.IsWeaklyAdmissible R) (D : QuotientSystem B S hS R)
    {V : FppfSheaf B S hS} (v : V ⟶ formalSpectrum D)
    {E : QuotientSystem B S hS (TopologicalRing.CompletionOver f)}
    (c : ContinuousHom D E)
    (hc : c.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (α : stageBaseChangeDiagram D v ≅ kerProjectionDiagram f ⋙ formalSpectrumDiagram E)
    (hα : ∀ J : WeakIdeals R, α.hom.app J ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (c.stageMap (OrderDual.ofDual J)
            (kerProjectionIdeal f (OrderDual.ofDual J))
            (le_comap_kerProjectionIdeal f c hc (OrderDual.ofDual J)))) =
        pullback.fst (formalSpectrumInclusion D J) v) :
    (isoFormalSpectrumOfStageNatIso f hR.1 D v E α).hom ≫ formalSpectrumMap hR c = v := by
  have key : ((HasColimit.isoOfNatIso α).hom ≫
        (colimitIsoFormalSpectrumOfCompletion f hR.1 E).hom) ≫ formalSpectrumMap hR c =
      (isoColimitStageBaseChange D v hR.1).inv ≫ v := by
    refine colimit.hom_ext fun J ↦ ?_
    rw [Category.assoc, HasColimit.ι_isoOfNatIso_hom_assoc,
      ι_colimitIsoFormalSpectrumOfCompletion_hom_assoc]
    refine (congrArg _ (formalSpectrumMap_spec hR c (OrderDual.ofDual J)
      (kerProjectionIdeal f (OrderDual.ofDual J))
      (le_comap_kerProjectionIdeal f c hc (OrderDual.ofDual J)))).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hα J))).trans
      (pullback.condition.trans ?_)
    rw [← Category.assoc, ι_isoColimitStageBaseChange_inv]
    rfl
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ (isoColimitStageBaseChange D v hR.1).hom ≫ z) key).trans
      (Iso.hom_inv_id_assoc _ _))

end Compatibility

/-! ### The lift of the stage isomorphisms -/

namespace StageEtale

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
  (D : QuotientSystem B S hS R)
  (hX : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
  (Y : AffineEtaleFormalCharts B S hS (formalSpectrum D))
  {A : Type u} [CommRing A] [Algebra R A]
  (θ : ∀ J : WeakIdeals R,
    (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) ≃+*
      (system D hX Y).B.obj (Opposite.op J))

/-- The identification of the quotient stage `A^∧ ⧸ ker (A^∧ → A ⧸ JA)` of the relative
completion with the ring of global sections of the chosen model of the stage base change at
`J`: the identification of that quotient with `A ⧸ JA` followed by the given isomorphism. -/
def stageRingEquiv (J : WeakIdeals R) :
    (TopologicalRing.CompletionOver (algebraMap R A) ⧸
      (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J)).1) ≃+*
        (system D hX Y).B.obj (Opposite.op J) :=
  (quotientKerProjectionRingEquiv (algebraMap R A) (OrderDual.ofDual J)).trans (θ J)

/-- The chosen model of the stage base change at `J` and the quotient stage of the relative
completion at the kernel of the projection at `J` have isomorphic underlying schemes. -/
def stageSchemeIso (J : WeakIdeals R) :
    (schemeDiagram D hX Y).obj J ≅
      Spec (.of (TopologicalRing.CompletionOver (algebraMap R A) ⧸
        (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J)).1)) :=
  ((schemeDiagram D hX Y).obj J).isoSpec ≪≫
    Scheme.Spec.mapIso (stageRingEquiv D hX Y θ J).toCommRingCatIso.op

/-- The forward map of `stageSchemeIso` unfolds to `isoSpec` followed by `Spec` of the stage
ring isomorphism. -/
theorem stageSchemeIso_hom (J : WeakIdeals R) :
    (stageSchemeIso D hX Y θ J).hom =
      ((schemeDiagram D hX Y).obj J).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (stageRingEquiv D hX Y θ J).toRingHom) := rfl

/-- The identification of the quotient stage with the sections of the chosen model is an
identification of `R ⧸ J`-algebras. -/
theorem stageRingEquiv_comp_quotientMap
    (hθ1 : ∀ J : WeakIdeals R,
      (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
          (system D hX Y).B.obj (Opposite.op J)).comp
        (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map) = (system D hX Y).algebraMap J)
    (J : WeakIdeals R) (ψ : R →+* TopologicalRing.CompletionOver (algebraMap R A))
    (hψ : ψ = TopologicalRing.CompletionOver.canonicalMap (algebraMap R A))
    (h : (OrderDual.ofDual J).1 ≤ Ideal.comap ψ
      (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J)).1) :
    (stageRingEquiv D hX Y θ J).toRingHom.comp
        (Ideal.quotientMap (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J)).1 ψ h) =
      (system D hX Y).algebraMap J := by
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have := RingHom.congr_fun (hθ1 J) (Ideal.Quotient.mk _ b)
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe] at this ⊢
  rw [hψ]
  exact this

/-- **The isomorphism of underlying schemes lies over the quotient stage `Spec (R ⧸ J)`.** This
is what makes it an isomorphism over `S`. -/
theorem stageSchemeIso_hom_comp_specMap
    (hθ1 : ∀ J : WeakIdeals R,
      (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
          (system D hX Y).B.obj (Opposite.op J)).comp
        (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map) = (system D hX Y).algebraMap J)
    (J : WeakIdeals R) (ψ : R →+* TopologicalRing.CompletionOver (algebraMap R A))
    (hψ : ψ = TopologicalRing.CompletionOver.canonicalMap (algebraMap R A))
    (h : (OrderDual.ofDual J).1 ≤ Ideal.comap ψ
      (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J)).1) :
    (stageSchemeIso D hX Y θ J).hom ≫ Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J)).1 ψ h)) =
      stageProj D hX Y J := by
  rw [stageSchemeIso_hom, Category.assoc, ← Spec.map_comp]
  change _ ≫ Spec.map (CommRingCat.ofHom ((stageRingEquiv D hX Y θ J).toRingHom.comp
    (Ideal.quotientMap _ ψ h))) = _
  rw [stageRingEquiv_comp_quotientMap D hX Y θ hθ1 J ψ hψ h]
  exact (congrArg _ (specMap_system_algebraMap D hX Y J)).trans (Iso.hom_inv_id_assoc _ _)

omit [IsTopologicalRing R] [IsLinearTopology R R] in
/-- The transition morphism of the diagram of chosen models, read on global sections, is `Spec`
of the transition of the system of stage rings. -/
theorem specMap_system_B_map {J K : WeakIdeals R} (g : J ⟶ K) :
    Spec.map ((system D hX Y).B.map g.op) =
      ((schemeDiagram D hX Y).obj J).isoSpec.inv ≫ (schemeDiagram D hX Y).map g ≫
        ((schemeDiagram D hX Y).obj K).isoSpec.hom := by
  change Spec.map ((schemeDiagram D hX Y).map g).appTop = _
  have h := congrArg (fun k ↦ ((schemeDiagram D hX Y).obj J).isoSpec.inv ≫ k)
    (Scheme.toSpecΓ_naturality ((schemeDiagram D hX Y).map g))
  simpa only [Category.assoc, ← Scheme.isoSpec_hom, Iso.inv_hom_id_assoc] using h.symm

/-- The kernels of the projections of the relative completion increase along a morphism of the
index of weak ideals of definition of the base. -/
theorem kerProjectionIdeal_le_of_hom {J K : WeakIdeals R} (g : J ⟶ K) :
    (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual K)).1 ≤
      (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J)).1 :=
  kerProjectionIdeal_mono (algebraMap R A)
    (show ((OrderDual.ofDual K).1 : Ideal R) ≤ (OrderDual.ofDual J).1 from leOfHom g)

/-- **The identifications of the quotient stages with the sections of the chosen models are
natural.** This is the naturality of the given family together with the compatibility condition
defining the relative completion. -/
theorem stageRingEquiv_naturality
    (hθ2 : ∀ (J K : WeakIdeals R) (h : J ≤ K),
      ((system D hX Y).B.map (homOfLE h).op).hom.comp
          (θ K : (A ⧸ ((weakIdealsBasis R).ideal K).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op K)) =
        (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op J)).comp
          (Ideal.Quotient.factor (Ideal.map_mono ((weakIdealsBasis R).antitone h))))
    {J K : WeakIdeals R} (g : J ⟶ K) :
    (((schemeDiagram D hX Y).map g).appTop).hom.comp (stageRingEquiv D hX Y θ K).toRingHom =
      (stageRingEquiv D hX Y θ J).toRingHom.comp (Ideal.Quotient.factor
        (kerProjectionIdeal_le_of_hom (A := A) g)) := by
  refine RingHom.ext fun x ↦ ?_
  have h2 := transitionMap_quotientKerProjectionRingEquiv (algebraMap R A)
    (show ((OrderDual.ofDual K).1 : Ideal R) ≤ (OrderDual.ofDual J).1 from leOfHom g) x
  have h1 := RingHom.congr_fun (hθ2 J K (leOfHom g))
    (quotientKerProjectionRingEquiv (algebraMap R A) (OrderDual.ofDual K) x)
  simp only [RingEquiv.toRingHom_eq_coe] at h1 h2 ⊢
  exact h1.trans (congrArg _ h2)

/-- The isomorphisms of underlying schemes are natural in the weak ideal of definition. -/
theorem stageSchemeIso_naturality
    (hθ2 : ∀ (J K : WeakIdeals R) (h : J ≤ K),
      ((system D hX Y).B.map (homOfLE h).op).hom.comp
          (θ K : (A ⧸ ((weakIdealsBasis R).ideal K).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op K)) =
        (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op J)).comp
          (Ideal.Quotient.factor (Ideal.map_mono ((weakIdealsBasis R).antitone h))))
    {J K : WeakIdeals R} (g : J ⟶ K) :
    (schemeDiagram D hX Y).map g ≫ (stageSchemeIso D hX Y θ K).hom =
      (stageSchemeIso D hX Y θ J).hom ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (kerProjectionIdeal_le_of_hom (A := A) g))) := by
  rw [stageSchemeIso_hom, stageSchemeIso_hom, ← Category.assoc, ← Scheme.isoSpec_hom_naturality,
    Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun t ↦ _ ≫ Spec.map (CommRingCat.ofHom t))
    (stageRingEquiv_naturality D hX Y θ hθ2 g)

variable {E : QuotientSystem B S hS (TopologicalRing.CompletionOver (algebraMap R A))}
  (c : ContinuousHom D E)
  (hc : c.toRingHom = TopologicalRing.CompletionOver.canonicalMap (algebraMap R A))

/-- **The chosen model of the stage base change at `J` and the quotient stage of `Spf A^∧` at
the kernel of the projection at `J` are isomorphic over `S`.** The isomorphism of underlying
schemes lies over `Spec (R ⧸ J)` by
`AlgebraicGeometry.FormalSpace.StageEtale.stageSchemeIso_hom_comp_specMap`, and both structure
morphisms to `S` factor through that stage. -/
def stageOverIso
    (hθ1 : ∀ J : WeakIdeals R,
      (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
          (system D hX Y).B.obj (Opposite.op J)).comp
        (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map) = (system D hX Y).algebraMap J)
    (J : WeakIdeals R) :
    obj D hX Y J ≅ (BigAffineFppf.inclusion B S hS).obj
      (E.stage (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J))) :=
  BigFppfOver.isoOfSchemeIso B S hS (stageSchemeIso D hX Y θ J) (by
    have hT := congrArg B.inclusion.map (Over.w (proj D hX Y J))
    rw [Functor.map_comp] at hT
    refine Eq.trans ?_ hT
    exact ((congrArg (fun z ↦ z ≫ D.overS (OrderDual.ofDual J))
        (stageSchemeIso_hom_comp_specMap D hX Y θ hθ1 J c.toRingHom hc
          (le_comap_kerProjectionIdeal (algebraMap R A) c hc (OrderDual.ofDual J))).symm).trans
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (stageSchemeIso D hX Y θ J).hom ≫ z)
        (c.overS (OrderDual.ofDual J)
          (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J))
          (le_comap_kerProjectionIdeal (algebraMap R A) c hc (OrderDual.ofDual J)))))).symm)

/-- On underlying schemes, the isomorphism over `S` at `J` is `stageSchemeIso` at `J`. -/
theorem toScheme_map_stageOverIso_hom
    (hθ1 : ∀ J : WeakIdeals R,
      (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
          (system D hX Y).B.obj (Opposite.op J)).comp
        (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map) = (system D hX Y).algebraMap J)
    (J : WeakIdeals R) :
    (BigFppfOver.toScheme B S hS).map (stageOverIso D hX Y θ c hc hθ1 J).hom =
      (stageSchemeIso D hX Y θ J).hom :=
  BigFppfOver.toScheme_map_isoOfSchemeIso_hom B S hS _ _

/-- The isomorphism over `S` commutes with the projections to the quotient stage
`Spec (R ⧸ J)`. -/
theorem stageOverIso_hom_comp
    (hθ1 : ∀ J : WeakIdeals R,
      (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
          (system D hX Y).B.obj (Opposite.op J)).comp
        (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map) = (system D hX Y).algebraMap J)
    (J : WeakIdeals R) :
    (stageOverIso D hX Y θ c hc hθ1 J).hom ≫ (BigAffineFppf.inclusion B S hS).map
        (c.stageMap (OrderDual.ofDual J)
          (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J))
          (le_comap_kerProjectionIdeal (algebraMap R A) c hc (OrderDual.ofDual J))) =
      proj D hX Y J := by
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  beta_reduce
  rw [Functor.map_comp, toScheme_map_stageOverIso_hom D hX Y θ c hc hθ1 J]
  exact stageSchemeIso_hom_comp_specMap D hX Y θ hθ1 J c.toRingHom hc
    (le_comap_kerProjectionIdeal (algebraMap R A) c hc (OrderDual.ofDual J))

/-- The isomorphisms over `S` commute with the transition maps of the two diagrams. -/
theorem stageOverIso_naturality
    (hθ1 : ∀ J : WeakIdeals R,
      (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
          (system D hX Y).B.obj (Opposite.op J)).comp
        (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map) = (system D hX Y).algebraMap J)
    (hθ2 : ∀ (J K : WeakIdeals R) (h : J ≤ K),
      ((system D hX Y).B.map (homOfLE h).op).hom.comp
          (θ K : (A ⧸ ((weakIdealsBasis R).ideal K).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op K)) =
        (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op J)).comp
          (Ideal.Quotient.factor (Ideal.map_mono ((weakIdealsBasis R).antitone h))))
    {J K : WeakIdeals R} (g : J ⟶ K) :
    trans D hX Y g ≫ (stageOverIso D hX Y θ c hc hθ1 K).hom =
      (stageOverIso D hX Y θ c hc hθ1 J).hom ≫ (BigAffineFppf.inclusion B S hS).map
          (E.transition (kerProjectionIdeal_le_of_hom (A := A) g)) := by
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  beta_reduce
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_stageOverIso_hom D hX Y θ c hc hθ1 K,
    toScheme_map_stageOverIso_hom D hX Y θ c hc hθ1 J]
  exact stageSchemeIso_naturality D hX Y θ hθ2 g

/-- **The chosen models of the stage base changes form a diagram isomorphic to the quotient
stages of `Spf A^∧` at the kernels of the projections.** -/
def stageNatIso
    (hθ1 : ∀ J : WeakIdeals R,
      (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
          (system D hX Y).B.obj (Opposite.op J)).comp
        (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map) = (system D hX Y).algebraMap J)
    (hθ2 : ∀ (J K : WeakIdeals R) (h : J ≤ K),
      ((system D hX Y).B.map (homOfLE h).op).hom.comp
          (θ K : (A ⧸ ((weakIdealsBasis R).ideal K).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op K)) =
        (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op J)).comp
          (Ideal.Quotient.factor (Ideal.map_mono ((weakIdealsBasis R).antitone h)))) :
    diagram D hX Y ≅
      kerProjectionDiagram (algebraMap R A) ⋙ E.diagram ⋙ BigAffineFppf.inclusion B S hS :=
  NatIso.ofComponents (stageOverIso D hX Y θ c hc hθ1)
    (stageOverIso_naturality D hX Y θ c hc hθ1 hθ2)

/-! ### The chosen models are the stage base changes -/

omit [IsTopologicalRing R] [IsLinearTopology R R] in
/-- The transition maps of the stage base-change diagram commute with the first projections. -/
theorem stageBaseChangeDiagram_map_comp_fst {J K : WeakIdeals R} (g : J ⟶ K) :
    (stageBaseChangeDiagram D Y.obj.hom).map g ≫
        pullback.fst (formalSpectrumInclusion D K) Y.obj.hom =
      pullback.fst (formalSpectrumInclusion D J) Y.obj.hom ≫ (formalSpectrumDiagram D).map g :=
  baseChangeDiagram_map_fst _ _ g

omit [IsTopologicalRing R] [IsLinearTopology R R] in
/-- The transition maps of the stage base-change diagram commute with the second projections
to the chart. -/
theorem stageBaseChangeDiagram_map_comp_snd {J K : WeakIdeals R} (g : J ⟶ K) :
    (stageBaseChangeDiagram D Y.obj.hom).map g ≫
        pullback.snd (formalSpectrumInclusion D K) Y.obj.hom =
      pullback.snd (formalSpectrumInclusion D J) Y.obj.hom :=
  baseChangeDiagram_map_snd _ _ g

/-- The chosen model of the stage base change at `J` represents that base change: both are
fibre products of the chart with the stage inclusion. -/
def stageBaseChangeIso (J : WeakIdeals R) :
    (stageBaseChangeDiagram D Y.obj.hom).obj J ≅
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (obj D hX Y J) :=
  (isPullback D hX Y J).flip.isoPullback.symm

omit [IsTopologicalRing R] [IsLinearTopology R R] in
/-- `stageBaseChangeIso` followed by the projection to the stage is the first pullback
projection. -/
theorem stageBaseChangeIso_hom_comp_proj (J : WeakIdeals R) :
    (stageBaseChangeIso D hX Y J).hom ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (proj D hX Y J) =
      pullback.fst (formalSpectrumInclusion D J) Y.obj.hom :=
  (isPullback D hX Y J).flip.isoPullback_inv_fst

omit [IsTopologicalRing R] [IsLinearTopology R R] in
/-- `stageBaseChangeIso` followed by the map to the chart is the second pullback projection. -/
theorem stageBaseChangeIso_hom_comp_fst (J : WeakIdeals R) :
    (stageBaseChangeIso D hX Y J).hom ≫ fst D hX Y J =
      pullback.snd (formalSpectrumInclusion D J) Y.obj.hom :=
  (isPullback D hX Y J).flip.isoPullback_inv_snd

omit [IsTopologicalRing R] [IsLinearTopology R R] in
/-- The isomorphisms `stageBaseChangeIso` commute with the transition maps of the two
diagrams. -/
theorem stageBaseChangeIso_naturality {J K : WeakIdeals R} (g : J ⟶ K) :
    (stageBaseChangeDiagram D Y.obj.hom).map g ≫ (stageBaseChangeIso D hX Y K).hom =
      (stageBaseChangeIso D hX Y J).hom ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (trans D hX Y g) := by
  refine (isPullback D hX Y K).flip.hom_ext ?_ ?_
  · rw [Category.assoc, stageBaseChangeIso_hom_comp_proj,
      stageBaseChangeDiagram_map_comp_fst, Category.assoc,
      ← (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp, trans_proj,
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp,
      ← Category.assoc, stageBaseChangeIso_hom_comp_proj]
    rfl
  · rw [Category.assoc, stageBaseChangeIso_hom_comp_fst,
      stageBaseChangeDiagram_map_comp_snd, Category.assoc, trans_fst,
      stageBaseChangeIso_hom_comp_fst]

/-- **The stage base changes of a chart form a diagram isomorphic to the diagram of chosen
models.** -/
def stageBaseChangeNatIso :
    stageBaseChangeDiagram D Y.obj.hom ≅
      diagram D hX Y ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) :=
  NatIso.ofComponents (stageBaseChangeIso D hX Y) (stageBaseChangeIso_naturality D hX Y)

/-! ### The isomorphism of diagrams the colimit assembly consumes -/

/-- **The stage base changes of a representable étale chart of `Spf R` are the quotient stages
of `Spf A^∧`.** This is the isomorphism of diagrams of sheaves which
`AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIso` consumes. -/
def assemblyNatIso
    (hθ1 : ∀ J : WeakIdeals R,
      (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
          (system D hX Y).B.obj (Opposite.op J)).comp
        (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map) = (system D hX Y).algebraMap J)
    (hθ2 : ∀ (J K : WeakIdeals R) (h : J ≤ K),
      ((system D hX Y).B.map (homOfLE h).op).hom.comp
          (θ K : (A ⧸ ((weakIdealsBasis R).ideal K).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op K)) =
        (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op J)).comp
          (Ideal.Quotient.factor (Ideal.map_mono ((weakIdealsBasis R).antitone h)))) :
    stageBaseChangeDiagram D Y.obj.hom ≅
      kerProjectionDiagram (algebraMap R A) ⋙ formalSpectrumDiagram E :=
  stageBaseChangeNatIso D hX Y ≪≫
    Functor.isoWhiskerRight (stageNatIso D hX Y θ c hc hθ1 hθ2)
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))

/-- The isomorphism of diagrams commutes with the projections to the quotient stages of
`Spf R`, which is the hypothesis of
`AlgebraicGeometry.FormalSpace.hom_isoFormalSpectrumOfStageNatIso_comp`. -/
theorem assemblyNatIso_hom_app_comp
    (hθ1 : ∀ J : WeakIdeals R,
      (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
          (system D hX Y).B.obj (Opposite.op J)).comp
        (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
          (algebraMap R A) Ideal.le_comap_map) = (system D hX Y).algebraMap J)
    (hθ2 : ∀ (J K : WeakIdeals R) (h : J ≤ K),
      ((system D hX Y).B.map (homOfLE h).op).hom.comp
          (θ K : (A ⧸ ((weakIdealsBasis R).ideal K).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op K)) =
        (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op J)).comp
          (Ideal.Quotient.factor (Ideal.map_mono ((weakIdealsBasis R).antitone h))))
    (J : WeakIdeals R) :
    (assemblyNatIso D hX Y θ c hc hθ1 hθ2).hom.app J ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (c.stageMap (OrderDual.ofDual J)
            (kerProjectionIdeal (algebraMap R A) (OrderDual.ofDual J))
            (le_comap_kerProjectionIdeal (algebraMap R A) c hc (OrderDual.ofDual J)))) =
      pullback.fst (formalSpectrumInclusion D J) Y.obj.hom := by
  rw [← stageBaseChangeIso_hom_comp_proj D hX Y J, ← stageOverIso_hom_comp D hX Y θ c hc hθ1 J]
  exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)

end StageEtale

/-! ### The essential-surjectivity clause -/

section Main

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The essential-surjectivity clause of Stacks 0AN8.** For a weakly admissible linearly
topologized ring `R` over `S` whose quotient system is carried by the site, every morphism
`v : V ⟶ Spf R` from an affine formal algebraic space which is representable by algebraic
spaces and étale is `Spf` of the canonical map `R → A^∧` for an étale `R`-algebra `A`,
compatibly with the morphisms to `Spf R`.

The étale algebra and the stagewise identifications come from
`AlgebraicGeometry.FormalSpace.StageEtale.exists_etale_algebra_of_isRepresentableEtale`, the
quotient system of `A^∧` and the continuous map into it from
`AlgebraicGeometry.FormalSpace.exists_completionOver_quotientSystem` (Stacks 0ANM), the
identification of diagrams from
`AlgebraicGeometry.FormalSpace.StageEtale.assemblyNatIso`, the isomorphism from
`AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIso` and its compatibility with the
morphisms to `Spf R` from
`AlgebraicGeometry.FormalSpace.hom_isoFormalSpectrumOfStageNatIso_comp`.

This is `AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf`. -/
theorem exists_etale_completionOver_isoFormalSpectrum
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R) (hRcard : Cardinal.mk R < B.cutoff)
    (D : QuotientSystem B S hS R) (V : FppfSheaf B S hS) (v : V ⟶ formalSpectrum D)
    (hV : IsAffineFormalAlgebraicSpace B S hS V) (hv : IsRepresentableEtale B S hS v) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
      (E : QuotientSystem B S hS (TopologicalRing.CompletionOver (algebraMap R A)))
      (c : ContinuousHom D E) (ε : V ≅ formalSpectrum E),
      c.toRingHom = TopologicalRing.CompletionOver.canonicalMap (algebraMap R A) ∧
        ε.hom ≫ formalSpectrumMap hR c = v := by
  obtain ⟨A, _, _, hAet, θ, hθ1, hθ2⟩ :=
    StageEtale.exists_etale_algebra_of_isRepresentableEtale D hR
      (hasLargeSite_of_mk_lt_cutoff D hRcard) v hV hv
  have hft : let _ : Algebra R A := (algebraMap R A).toAlgebra; Algebra.FiniteType R A :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨E, c, hc⟩ := exists_completionOver_quotientSystem B S hS (algebraMap R A) hft hR D
    (hasLargeSite_of_mk_lt_cutoff D hRcard)
  refine ⟨A, inferInstance, inferInstance, hAet, E, c,
    isoFormalSpectrumOfStageNatIso (algebraMap R A) hR.1 D v E
      (StageEtale.assemblyNatIso D
        (isAffineFormalAlgebraicSpace_formalSpectrum hR D
          (hasLargeSite_of_mk_lt_cutoff D hRcard))
        (StageEtale.chartOf D v hV hv) θ c hc hθ1 hθ2), hc, ?_⟩
  exact hom_isoFormalSpectrumOfStageNatIso_comp (algebraMap R A) hR D v c hc _
    (StageEtale.assemblyNatIso_hom_app_comp D _ _ θ c hc hθ1 hθ2)

end Main

end AlgebraicGeometry.FormalSpace

end
