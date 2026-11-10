module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallEtaleSite.EssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocalRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassificationRefined
import all StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification

/-!
# The étale system of stage rings of a representable étale morphism to a formal spectrum

Let `S` be a scheme of a big fppf site, let `R` be a linearly topologized ring over `S`
presented by a quotient system `D`, and let `u : U ⟶ Spf R` be a morphism from an affine formal
algebraic space which is representable by algebraic spaces and étale — an object of the category
of **Stacks 0DEE** over `Spf R`. For each weak ideal of definition `J` of `R` the fibre product

`Spec (R ⧸ J) ×_{Spf R} U`

is represented by an affine object of the site whose projection to the stage `Spec (R ⧸ J)` is
étale (**Stacks 0AKN** together with the étale half of the chart condition, which is
`AlgebraicGeometry.FormalSpace.affineEtaleBaseChangeData`). This file assembles a *choice* of
such models into a diagram indexed by the weak ideals of definition of `R` ordered by reverse
inclusion, shows its transition squares are cartesian, and reads the diagram on rings: the
result is an inverse system of the kind **Stacks 0AL1** attaches to a finite type morphism of
affine formal algebraic spaces, all of whose structure maps `R ⧸ J → \bar A` are étale.

Feeding that system to the ring-theoretic half,
`AlgebraicGeometry.FormalSpace.exists_etale_algebra_of_etaleSystem`, produces an étale
`R`-algebra `A` with isomorphisms `A ⧸ JA ≅ \bar A` over `R ⧸ J` for every `J`, compatible with
the transitions. This is the **geometric half of the essential-surjectivity clause of
Stacks 0AN8**: the step of the source's proof which writes `Spec (B ⧸ J) ×_Y X` as `Spec(\bar A)`
and feeds it to Stacks 04D1 and Stacks 0ALI.

## Main definitions

* `AlgebraicGeometry.FormalSpace.StageEtale.data`, `…obj`, `…proj`, `…fst`: the chosen affine
  model of the stage base change at `J`, its projection to the stage and its projection to the
  source of the chart.
* `AlgebraicGeometry.FormalSpace.StageEtale.diagram`: the chosen models as a diagram of objects
  of the site, indexed by the weak ideals of definition of `R` ordered by reverse inclusion.
* `AlgebraicGeometry.FormalSpace.StageEtale.system`: the inverse system of their rings of global
  sections, as a `AlgebraicGeometry.FormalSpace.FiniteTypeAlgebraSystem`.

## Main results

* `AlgebraicGeometry.FormalSpace.StageEtale.isPullback_trans` and
  `…isPullback_toScheme_trans`: the transition square of the chosen models is cartesian, in the
  sheaf category, in the site and on underlying schemes.
* `AlgebraicGeometry.FormalSpace.StageEtale.etale_system_algebraMap`: every structure
  homomorphism of the system of stage rings is étale.
* `AlgebraicGeometry.FormalSpace.StageEtale.exists_etale_algebra_stageSystem` and
  `…exists_etale_algebra_of_isRepresentableEtale`: the geometric half of the
  essential-surjectivity clause of Stacks 0AN8, as described above — the second form assembles
  the chart data from the morphism and discharges that `Spf R` is an affine formal algebraic
  space.

## Implementation notes

The choice of affine model is `AlgebraicGeometry.FormalSpace.affineEtaleBaseChangeData`, which
is a `Nonempty.some`; naturality in `J` is *not* a property of that choice but is supplied by
the universal property of the chosen cartesian square together with the full faithfulness of
the sheafified Yoneda embedding, which is what
`AlgebraicGeometry.FormalSpace.StageEtale.trans_unique` records. This is why no canonical model
is needed: the transition morphism between two chosen models is unique once its two projections
are prescribed, so the functor laws hold on the nose.

The stage inclusion `Spec (R ⧸ J) ⟶ Spf R` is used through the abbreviation
`AlgebraicGeometry.FormalSpace.StageEtale.stageInclusion`, which ascribes to it the type the
base change data is stated at. Without that ascription the colimit's `(formalSpectrumDiagram
D).obj J` and the base change data's `sheafifiedYoneda.obj (inclusion.obj (D.diagram.obj J))`
are definitionally but not syntactically equal, and `rw` cannot act across the difference —
`AlgebraicGeometry.FormalSpace.formalSpectrum` is a `def`, not an `abbrev`.

Passing from the cartesian squares of schemes to the pushout squares of rings is
`AlgebraicGeometry.FormalSpace.FiniteTypeAlgebraSystem.ofAffineSchemeDiagram`; its structure
homomorphism is identified by
`AlgebraicGeometry.FormalSpace.FiniteTypeAlgebraSystem.specMap_algebraMap_ofAffineSchemeDiagram`,
through which the étaleness of the structure map is read from the geometry.

The base index of the ring-theoretic half is the maximal weak ideal of definition — the
topological nilradical, `TopologicalRing.nilIdx`, which is a weak ideal of definition by
`TopologicalRing.isWeakIdealOfDefinition_topologicalNilradical` and contains every other one by
`TopologicalRing.le_topologicalNilradical_of_isWeakIdealOfDefinition` — so the isomorphisms
`A ⧸ JA ≅ \bar A` are obtained for every weak ideal of definition `J` and not only for those
below a chosen one.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AL1](https://stacks.math.columbia.edu/tag/0AL1)
* [Stacks Project, Tag 0AMW](https://stacks.math.columbia.edu/tag/0AMW)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {R : Type u} [CommRing R] [TopologicalSpace R]

/-- The underlying scheme of a quotient stage is the spectrum of the quotient, so it is
affine. -/
theorem isAffine_toScheme_quotientSystemStage (D : QuotientSystem B S hS R)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex R) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.stage J))) := by
  change IsAffine (Spec (.of (R ⧸ J.1)))
  infer_instance

namespace StageEtale

variable {B S hS}
variable (D : QuotientSystem B S hS R)
  (hX : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
  (Y : AffineEtaleFormalCharts B S hS (formalSpectrum D))

/-- The inclusion of the quotient stage at `J` into the formal spectrum, read at the type the
base change data of a chart uses. -/
abbrev stageInclusion (J : WeakIdeals R) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.diagram.obj J)) ⟶ formalSpectrum D :=
  formalSpectrumInclusion D J

/-- The stage inclusions of a formal spectrum are compatible with the transitions of its
quotient stages. -/
theorem map_comp_stageInclusion {J K : WeakIdeals R} (g : J ⟶ K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D.diagram.map g)) ≫ stageInclusion D K =
      stageInclusion D J :=
  colimit.w (formalSpectrumDiagram D) g

/-- The chosen affine model of the stage base change `Spec (R ⧸ J) ×_{Spf R} U` of a chart
`U ⟶ Spf R`, with its cartesian square, its affineness and the étaleness of its projection to
the stage. -/
def data (J : WeakIdeals R) :
    AffineEtaleBaseChange B S hS (formalSpectrum D)
      ((BigAffineFppf.inclusion B S hS).obj (D.diagram.obj J)) (stageInclusion D J) Y :=
  affineEtaleBaseChangeData B S hS hX _ (isAffine_toScheme_quotientSystemStage B S hS D _)
    (stageInclusion D J) Y

/-- The object of the site modelling the stage base change at `J`. -/
abbrev obj (J : WeakIdeals R) : BigFppfOver B S hS := (data D hX Y J).obj

/-- The projection of the chosen model at `J` to the source of the chart. -/
abbrev fst (J : WeakIdeals R) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (obj D hX Y J) ⟶ Y.obj.left :=
  (data D hX Y J).fst

/-- The projection of the chosen model at `J` to the quotient stage at `J`. -/
abbrev proj (J : WeakIdeals R) :
    obj D hX Y J ⟶ (BigAffineFppf.inclusion B S hS).obj (D.diagram.obj J) :=
  (data D hX Y J).proj

/-- The chosen model at `J` is the fibre product of the chart with the stage inclusion. -/
theorem isPullback (J : WeakIdeals R) :
    IsPullback (fst D hX Y J)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (proj D hX Y J))
      Y.obj.hom (stageInclusion D J) :=
  (data D hX Y J).isPullback

/-- The square over which the transition of the chosen stage models is induced. -/
theorem transSquare {J K : WeakIdeals R} (g : J ⟶ K) :
    fst D hX Y J ≫ Y.obj.hom =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (proj D hX Y J ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map g)) ≫
        stageInclusion D K := by
  rw [(Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp, Category.assoc,
    map_comp_stageInclusion D g]
  exact (isPullback D hX Y J).w

/-- The transition of the chosen stage models, induced by the universal property of the
cartesian square at `K` and the full faithfulness of the sheafified Yoneda embedding. -/
def trans {J K : WeakIdeals R} (g : J ⟶ K) : obj D hX Y J ⟶ obj D hX Y K :=
  (sheafifiedYonedaFF B S hS).preimage
    ((isPullback D hX Y K).lift (fst D hX Y J)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (proj D hX Y J ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map g)))
      (transSquare D hX Y g))

/-- The image of the transition under the sheafified Yoneda embedding is the morphism induced
by the cartesian square at `K`. -/
theorem map_trans {J K : WeakIdeals R} (g : J ⟶ K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (trans D hX Y g) =
      (isPullback D hX Y K).lift (fst D hX Y J)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (proj D hX Y J ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map g)))
        (transSquare D hX Y g) :=
  (sheafifiedYonedaFF B S hS).map_preimage _

/-- The transition of the chosen stage models commutes with the projections to the chart. -/
theorem trans_fst {J K : WeakIdeals R} (g : J ⟶ K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (trans D hX Y g) ≫
        fst D hX Y K = fst D hX Y J := by
  rw [map_trans, IsPullback.lift_fst]

/-- The transition of the chosen stage models lies over the transition of the quotient
stages. -/
theorem trans_proj {J K : WeakIdeals R} (g : J ⟶ K) :
    trans D hX Y g ≫ proj D hX Y K =
      proj D hX Y J ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map g) := by
  apply (sheafifiedYonedaFF B S hS).map_injective
  rw [(Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp, map_trans,
    IsPullback.lift_snd]

/-- A morphism of chosen stage models compatible with the projections to the chart and to the
quotient stages is the transition. -/
theorem trans_unique {J K : WeakIdeals R} (g : J ⟶ K) (m : obj D hX Y J ⟶ obj D hX Y K)
    (hfst : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m ≫ fst D hX Y K =
      fst D hX Y J)
    (hproj : m ≫ proj D hX Y K =
      proj D hX Y J ≫ (BigAffineFppf.inclusion B S hS).map (D.diagram.map g)) :
    m = trans D hX Y g := by
  apply (sheafifiedYonedaFF B S hS).map_injective
  refine (isPullback D hX Y K).hom_ext ?_ ?_
  · rw [hfst, trans_fst]
  · simp only [← Functor.map_comp, hproj, trans_proj]

/-- The chosen stage models form a diagram of objects of the site indexed by the weak ideals of
definition of `R` ordered by reverse inclusion. -/
def diagram : WeakIdeals R ⥤ BigFppfOver B S hS where
  obj J := obj D hX Y J
  map g := trans D hX Y g
  map_id J := by
    refine (trans_unique D hX Y (𝟙 J) (𝟙 _) ?_ ?_).symm
    · rw [(Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_id]
      exact Category.id_comp _
    · simp
  map_comp {J K L} g h := by
    refine (trans_unique D hX Y (g ≫ h) _ ?_ ?_).symm
    · rw [(Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp, Category.assoc,
        trans_fst, trans_fst]
    · rw [Category.assoc, trans_proj, ← Category.assoc, trans_proj, Category.assoc,
        ← (BigAffineFppf.inclusion B S hS).map_comp, ← D.diagram.map_comp]

/-- The transition square of the chosen stage models is cartesian: the model at `J` is the
fibre product of the model at `K` with the stage transition. -/
theorem isPullback_trans {J K : WeakIdeals R} (g : J ⟶ K) :
    IsPullback ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (trans D hX Y g))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (proj D hX Y J))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (proj D hX Y K))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D.diagram.map g))) := by
  refine IsPullback.of_right ?_ ?_ (isPullback D hX Y K)
  · rw [trans_fst, map_comp_stageInclusion]
    exact isPullback D hX Y J
  · simp only [← Functor.map_comp, trans_proj]

/-- The transition square of the chosen stage models is cartesian in the site. -/
theorem isPullback_site_trans {J K : WeakIdeals R} (g : J ⟶ K) :
    IsPullback (trans D hX Y g) (proj D hX Y J) (proj D hX Y K)
      ((BigAffineFppf.inclusion B S hS).map (D.diagram.map g)) := by
  let := bigFppfOver_subcanonical B S hS
  let : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Faithful :=
    (sheafifiedYonedaFF B S hS).faithful
  let : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Full :=
    (sheafifiedYonedaFF B S hS).full
  exact IsPullback.of_map_of_faithful _ (isPullback_trans D hX Y g)

/-- The transition square of the chosen stage models is cartesian on underlying schemes. -/
theorem isPullback_toScheme_trans {J K : WeakIdeals R} (g : J ⟶ K) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (trans D hX Y g))
      ((BigFppfOver.toScheme B S hS).map (proj D hX Y J))
      ((BigFppfOver.toScheme B S hS).map (proj D hX Y K))
      ((BigFppfOver.toScheme B S hS).map
        ((BigAffineFppf.inclusion B S hS).map (D.diagram.map g))) :=
  (isPullback_site_trans D hX Y g).map (BigFppfOver.toScheme B S hS)

/-- On underlying schemes the transition of the quotient stages is the spectrum of the
canonical quotient homomorphism. -/
theorem toScheme_map_stage_transition {J K : WeakIdeals R} (g : J ⟶ K) :
    (BigFppfOver.toScheme B S hS).map
        ((BigAffineFppf.inclusion B S hS).map (D.diagram.map g)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (show ((OrderDual.ofDual K).1 : Ideal R) ≤ (OrderDual.ofDual J).1 from leOfHom g))) :=
  rfl

/-! ### The inverse system of stage rings -/

/-- The diagram of affine schemes underlying the chosen stage models. -/
abbrev schemeDiagram : WeakIdeals R ⥤ Scheme.{u} :=
  diagram D hX Y ⋙ BigFppfOver.toScheme B S hS

/-- The stages of the diagram of schemes underlying the chosen stage models are affine. -/
instance isAffine_schemeDiagram_obj (J : WeakIdeals R) :
    IsAffine ((schemeDiagram D hX Y).obj J) := (data D hX Y J).isAffine

/-- The projection of the chosen stage model at `J` to the quotient stage, as a morphism of
affine schemes over the spectrum of `R ⧸ J`. -/
abbrev stageProj (J : WeakIdeals R) :
    (schemeDiagram D hX Y).obj J ⟶
      Spec (CommRingCat.of (R ⧸ (weakIdealsBasis R).ideal J)) :=
  (BigFppfOver.toScheme B S hS).map (proj D hX Y J)

/-- The projection of a chosen stage model to its quotient stage is étale. -/
theorem etale_stageProj (J : WeakIdeals R) : Etale (stageProj D hX Y J) :=
  (data D hX Y J).etale

/-- The projection of a chosen stage model to its quotient stage is locally of finite type,
being étale. -/
theorem locallyOfFiniteType_stageProj (J : WeakIdeals R) :
    LocallyOfFiniteType (stageProj D hX Y J) := by
  have := etale_stageProj D hX Y J
  infer_instance

/-- The transition square of the chosen stage models, read on affine schemes over the quotient
stages, is cartesian. -/
theorem isPullback_stageProj {J K : WeakIdeals R} (h : J ≤ K) :
    IsPullback (stageProj D hX Y J) ((schemeDiagram D hX Y).map (homOfLE h))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        ((weakIdealsBasis R).antitone h))))
      (stageProj D hX Y K) :=
  (isPullback_toScheme_trans D hX Y (homOfLE h)).flip

/-- **The system of stage rings of a representable étale chart of a formal spectrum.** The
rings of global sections of the chosen affine models of the stage base changes
`Spec (R ⧸ J) ×_{Spf R} U` form an inverse system of the kind Stacks 0AL1 attaches to a finite
type morphism of affine formal algebraic spaces, over the fundamental system of all weak ideals
of definition of `R`. -/
def system : FiniteTypeAlgebraSystem R (WeakIdeals R) (weakIdealsBasis R) :=
  FiniteTypeAlgebraSystem.ofAffineSchemeDiagram (weakIdealsBasis R)
    (schemeDiagram D hX Y) (fun J ↦ isAffine_schemeDiagram_obj D hX Y J) (stageProj D hX Y)
    (locallyOfFiniteType_stageProj D hX Y) fun {_J _K} h ↦ isPullback_stageProj D hX Y h

/-- The members of the system of stage rings are the rings of global sections of the chosen
affine models of the stage base changes. -/
theorem system_B_obj (J : WeakIdeals R) :
    (system D hX Y).B.obj (Opposite.op J) =
      Scheme.Γ.obj (Opposite.op ((schemeDiagram D hX Y).obj J)) := rfl

/-- The spectrum of the structure homomorphism of the system of stage rings at `J` is the
projection of the chosen stage model to the quotient stage, precomposed with the inverse of
its identification with the spectrum of its global sections. -/
theorem specMap_system_algebraMap (J : WeakIdeals R) :
    Spec.map (CommRingCat.ofHom ((system D hX Y).algebraMap J)) =
      ((schemeDiagram D hX Y).obj J).isoSpec.inv ≫ stageProj D hX Y J :=
  FiniteTypeAlgebraSystem.specMap_algebraMap_ofAffineSchemeDiagram
    (weakIdealsBasis R) (schemeDiagram D hX Y) (fun J ↦ isAffine_schemeDiagram_obj D hX Y J)
    (stageProj D hX Y) (locallyOfFiniteType_stageProj D hX Y)
    (fun {_J _K} h ↦ isPullback_stageProj D hX Y h) J

/-- **Every structure homomorphism of the system of stage rings is étale.** This is the
étaleness of the base change of a representable étale chart to a quotient stage, read on
rings through the affine anti-equivalence. -/
theorem etale_system_algebraMap (J : WeakIdeals R) :
    ((system D hX Y).algebraMap J).Etale := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (HasRingHomProperty.Spec_iff (P := @Etale.{u})
    (φ := CommRingCat.ofHom ((system D hX Y).algebraMap J))).mp ?_
  rw [specMap_system_algebraMap]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Etale.{u})
    ((schemeDiagram D hX Y).obj J).isoSpec.inv (stageProj D hX Y J)).mpr
      (etale_stageProj D hX Y J)

/-! ### The étale algebra produced by the system -/

variable [IsTopologicalRing R] [IsLinearTopology R R]

/-- **The geometric half of the essential-surjectivity clause of Stacks 0AN8.** Let `Spf R` be
the formal spectrum of a linearly topologized ring over `S` and let `U ⟶ Spf R` be a morphism
from an affine formal algebraic space which is representable by algebraic spaces and étale.
Then there is an étale `R`-algebra `A` together with isomorphisms

`A ⧸ JA ≅ Γ(Spec (R ⧸ J) ×_{Spf R} U)` over `R ⧸ J`,

for **every** weak ideal of definition `J` of `R`, compatible with the transitions of the two
systems.

The rings on the right are the members of
`AlgebraicGeometry.FormalSpace.StageEtale.system`, whose stages are the chosen affine models of
the stage base changes of `U` — the family `Spec (\bar A)` of the source's proof — and whose
structure maps `R ⧸ J → \bar A` are étale by
`AlgebraicGeometry.FormalSpace.StageEtale.etale_system_algebraMap`. The algebra `A` and the
isomorphisms are then produced by the ring-theoretic half,
`AlgebraicGeometry.FormalSpace.exists_etale_algebra_of_etaleSystem`, whose base index is taken
to be the maximal weak ideal of definition `TopologicalRing.nilIdx`, so that no weak ideal of
definition is excluded. -/
theorem exists_etale_algebra_stageSystem
    (hR : TopologicalRing.IsWeaklyPreAdmissible R) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
      (θ : ∀ J : WeakIdeals R,
        (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) ≃+*
          (system D hX Y).B.obj (Opposite.op J)),
      (∀ J : WeakIdeals R,
        (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
            (system D hX Y).B.obj (Opposite.op J)).comp
          (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
            (algebraMap R A) Ideal.le_comap_map) = (system D hX Y).algebraMap J) ∧
      ∀ (J K : WeakIdeals R) (h : J ≤ K),
        ((system D hX Y).B.map (homOfLE h).op).hom.comp
            (θ K : (A ⧸ ((weakIdealsBasis R).ideal K).map (algebraMap R A)) →+*
              (system D hX Y).B.obj (Opposite.op K)) =
          (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
              (system D hX Y).B.obj (Opposite.op J)).comp
            (Ideal.Quotient.factor
              (Ideal.map_mono ((weakIdealsBasis R).antitone h))) := by
  have hmax : ∀ J : WeakIdeals R, OrderDual.toDual (TopologicalRing.nilIdx hR) ≤ J := fun J ↦
    TopologicalRing.le_topologicalNilradical_of_isWeakIdealOfDefinition (OrderDual.ofDual J).2
  obtain ⟨A, _, _, hAet, θ, hθ1, hθ2⟩ :=
    exists_etale_algebra_of_etaleSystem (weakIdealsBasis R) (system D hX Y)
      (etale_system_algebraMap D hX Y) (OrderDual.toDual (TopologicalRing.nilIdx hR))
  exact ⟨A, inferInstance, inferInstance, hAet, fun J ↦ θ J (hmax J),
    fun J ↦ hθ1 J (hmax J), fun J K h ↦ hθ2 J K (hmax J) h⟩

/-- A morphism to a formal spectrum from an affine formal algebraic space which is
representable by algebraic spaces and étale, as an object of the category of **Stacks 0DEE**
over that formal spectrum. -/
def chartOf {V : FppfSheaf B S hS} (v : V ⟶ formalSpectrum D)
    (hV : IsAffineFormalAlgebraicSpace B S hS V) (hv : IsRepresentableEtale B S hS v) :
    AffineEtaleFormalCharts B S hS (formalSpectrum D) := ⟨Over.mk v, hV, hv⟩

/-- **The geometric half of the essential-surjectivity clause of Stacks 0AN8, with the chart
data assembled from the morphism itself.** For a weakly admissible `R` whose quotient system is
carried by the site, every morphism `v : V ⟶ Spf R` from an affine formal algebraic space which
is representable by algebraic spaces and étale gives an étale `R`-algebra `A` with
isomorphisms `A ⧸ JA ≅ Γ(Spec (R ⧸ J) ×_{Spf R} V)` over `R ⧸ J`, for every weak ideal of
definition `J` of `R`, compatible with the transitions of the two systems.

Compared with `AlgebraicGeometry.FormalSpace.StageEtale.exists_etale_algebra_stageSystem` the
two pieces of data this discharges are that `Spf R` is an affine formal algebraic space
(**Stacks 0AIF**, `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum`)
and the packaging of `v` as an object of the category of Stacks 0DEE. -/
theorem exists_etale_algebra_of_isRepresentableEtale
    (hR : TopologicalRing.IsWeaklyAdmissible R) (hD : D.HasLargeSite)
    {V : FppfSheaf B S hS} (v : V ⟶ formalSpectrum D)
    (hV : IsAffineFormalAlgebraicSpace B S hS V) (hv : IsRepresentableEtale B S hS v) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
      (θ : ∀ J : WeakIdeals R,
        (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) ≃+*
          (system D (isAffineFormalAlgebraicSpace_formalSpectrum hR D hD)
            (chartOf D v hV hv)).B.obj (Opposite.op J)),
      (∀ J : WeakIdeals R,
        (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
            (system D (isAffineFormalAlgebraicSpace_formalSpectrum hR D hD)
              (chartOf D v hV hv)).B.obj (Opposite.op J)).comp
          (Ideal.quotientMap (((weakIdealsBasis R).ideal J).map (algebraMap R A))
            (algebraMap R A) Ideal.le_comap_map) =
          (system D (isAffineFormalAlgebraicSpace_formalSpectrum hR D hD)
            (chartOf D v hV hv)).algebraMap J) ∧
      ∀ (J K : WeakIdeals R) (h : J ≤ K),
        ((system D (isAffineFormalAlgebraicSpace_formalSpectrum hR D hD)
              (chartOf D v hV hv)).B.map (homOfLE h).op).hom.comp
            (θ K : (A ⧸ ((weakIdealsBasis R).ideal K).map (algebraMap R A)) →+*
              (system D (isAffineFormalAlgebraicSpace_formalSpectrum hR D hD)
                (chartOf D v hV hv)).B.obj (Opposite.op K)) =
          (θ J : (A ⧸ ((weakIdealsBasis R).ideal J).map (algebraMap R A)) →+*
              (system D (isAffineFormalAlgebraicSpace_formalSpectrum hR D hD)
                (chartOf D v hV hv)).B.obj (Opposite.op J)).comp
            (Ideal.Quotient.factor
              (Ideal.map_mono ((weakIdealsBasis R).antitone h))) :=
  exists_etale_algebra_stageSystem D (isAffineFormalAlgebraicSpace_formalSpectrum hR D hD)
    (chartOf D v hV hv) hR.1

end StageEtale

end AlgebraicGeometry.FormalSpace

end
