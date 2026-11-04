module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# The affine étale site of an affine formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `X` be an affine formal algebraic
space over `S`. Stacks 0DEE describes the affine étale site of `X` — which by Stacks 0DEA *is*
the affine étale site of the reduction `X_red` — as the category whose objects are the morphisms
`φ : U ⟶ X` of formal algebraic spaces with `U` an affine formal algebraic space and `φ`
representable by algebraic spaces and étale. The comparison functor sends `φ : U ⟶ X` to the
fibre product `U ×_X X_red`.

This file builds that category and that functor. The functor goes the way the source
constructs it: an object of the category is base changed along a morphism to `X` from the
sheaf represented by an affine object `V` of the site, and the result is an affine scheme
étale over `V`. Taking `V` to be the reduction of `X`, which for an affine formal algebraic
space is an affine scheme, this is the comparison functor of Stacks 0DEE.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsAffineEtaleFormalChart` and
  `AlgebraicGeometry.FormalSpace.AffineEtaleFormalCharts`: the category of conditions (1) and
  (2) of Stacks 0DEE, as a full subcategory of the morphisms to `X` of fppf sheaves.
* `AlgebraicGeometry.FormalSpace.AffineEtaleBaseChange`: the datum of a representing affine
  object for the base change of such a chart along a morphism to `X` from an affine object of
  the site, together with the cartesian square, the affineness and the étaleness.
* `AlgebraicGeometry.FormalSpace.affineEtaleComparison`: the comparison functor from that
  category to the affine étale site of the affine object, on objects the base change.
* `AlgebraicGeometry.FormalSpace.reductionAffineEtaleComparison`: **Stacks 0DEE**, the
  comparison functor into `X_affine,étale = X_red,affine,étale`.

## Main results

* `AlgebraicGeometry.FormalSpace.nonempty_affineEtaleBaseChange`: the base change of an object
  of the category along a morphism from an affine object of the site exists as an affine scheme
  étale over that object. This is the part of the proof of Stacks 0DEE that makes the
  comparison functor well defined.
* `AlgebraicGeometry.FormalSpace.isEtaleChart_yoneda_map`: an étale morphism of the site is an
  étale chart of the Yoneda presheaf of its target.
* `AlgebraicGeometry.FormalSpace.nonempty_affineEtale_yoneda` and
  `AlgebraicGeometry.FormalSpace.nonempty_affineEtaleFormalCharts`: both categories compared by
  Stacks 0DEE are inhabited, by the identity chart of `V` and the identity chart of `X`.
* `AlgebraicGeometry.FormalSpace.AffineEtaleBaseChange.isIso_proj_of_isIso` and
  `AlgebraicGeometry.FormalSpace.isIso_hom_affineEtaleComparison_obj`: the comparison functor
  carries the identity chart of `X` to the identity chart of `V`, up to isomorphism, so it is
  not valued in a degenerate object.

## Implementation notes

The reduction enters as a given rather than a choice — Stacks 0AIN,
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`, gives existence
— namely as the datum of an affine object `V` of the site, a morphism
`i : V ⟶ X` of fppf sheaves out of the sheaf it represents, and a proof that `i` exhibits `V`
as the reduction of `X`. That `V` may be taken affine is the statement, for an affine formal
algebraic space, that its reduction is an affine scheme; it is carried as a hypothesis for the
same reason. With the reduction represented by an affine object of the site, the affine étale
site of `X_red` in the sense of Stacks 0DEA is literally
`AlgebraicGeometry.Space.AffineEtale` of the Yoneda presheaf of `V`, which is a presheaf of
`Type u` and needs no universe descent.

Affineness of the base change is Stacks 0AKN, in the form proved in
`StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/MorphismOfAffines.lean` over the test objects
of the site whose underlying scheme is affine — which is exactly the generality needed here,
since the reduction is such a test object. Étaleness of the base change is extracted from the
étale half of `AlgebraicGeometry.FormalSpace.IsRepresentableEtale`: the represented base change
of the chart over the reduction is, as a morphism of algebraic spaces, étale in the sense of
`AlgebraicGeometry.Space.IsEtaleULift`, and feeding it the isomorphism of the representing
object with the fibre product — an isomorphism is an étale chart — turns that into étaleness of
the morphism of the site, by `CategoryTheory.MorphismProperty.of_relative_map`.

The cartesian square of Stacks 0AKN lives in fppf sheaves while the étaleness condition is
stated for the underlying presheaves and the universe-lifted Yoneda embedding; the comparison
`AlgebraicGeometry.FormalSpace.sheafifiedYonedaCompForgetIso` of the two embeddings, which
exists because the big fppf site is subcanonical, transports the square between them.

The comparison functor chooses a representing object for each chart, which is why it is
noncomputable: the choice is `Nonempty.some` of the proved existence. Its action on morphisms
needs no further choice, being the unique morphism the universal property of the chosen
cartesian square produces, and functoriality is the uniqueness half of that property.

Only the comparison functor is constructed here, not an equivalence: the quasi-inverse of
Stacks 0DEE lifts an étale affine scheme over `X_red` to a compatible system over the
thickening stages of a presentation of `X` and takes the colimit, and the étale lifting along
the stages is available in this library only in its ring-theoretic form (Stacks 0ALI,
`etaleBaseChange_isEquivalence_and_henselianRing_of_le_nilradical`), not for the stages of a
presentation of an affine formal algebraic space.

## References

* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks Project, Tag 0H01](https://stacks.math.columbia.edu/tag/0H01)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The category of affine formal algebraic spaces representable étale over `X` -/

/-- The property of a morphism of fppf sheaves into `X` that cuts out the objects of the
category of Stacks 0DEE: its source is an affine formal algebraic space, and it is
representable by algebraic spaces and étale. -/
abbrev IsAffineEtaleFormalChart (X : FppfSheaf B S hS) : ObjectProperty (Over X) :=
  fun U ↦ IsAffineFormalAlgebraicSpace B S hS U.left ∧ IsRepresentableEtale B S hS U.hom

/-- **Stacks 0DEE**, the category on the right-hand side: the morphisms `φ : U ⟶ X` of formal
algebraic spaces with `U` an affine formal algebraic space and `φ` representable by algebraic
spaces and étale, with the morphisms of fppf sheaves over `X` between them. -/
@[stacks 0DEE "the category of the morphisms satisfying (1) and (2)"]
abbrev AffineEtaleFormalCharts (X : FppfSheaf B S hS) :=
  (IsAffineEtaleFormalChart B S hS X).FullSubcategory

/-! ### The comparison of the two Yoneda embeddings -/

/-- The underlying presheaf of a sheafified representable is the universe-lifted Yoneda
presheaf, because the big fppf site of `S` is subcanonical. -/
noncomputable def sheafifiedYonedaCompForgetIso :
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⋙
        sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
  letI := bigFppfOver_subcanonical B S hS
  Functor.isoWhiskerRight
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)) _ ≪≫
    (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf

/-- The sheafified Yoneda embedding of the big fppf site of `S` is fully faithful, the site
being subcanonical. -/
noncomputable def sheafifiedYonedaFF :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).FullyFaithful :=
  letI := bigFppfOver_subcanonical B S hS
  Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)

/-- A morphism whose image under a fully faithful functor is the projection of a cartesian
square with an invertible parallel side is invertible. -/
private theorem isIso_of_isPullback_map_of_isIso {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} (hF : F.FullyFaithful) {P Q : C} {A T : D} {fst : F.obj P ⟶ A}
    {snd : P ⟶ Q} {f : A ⟶ T} {g : F.obj Q ⟶ T} (h : IsPullback fst (F.map snd) f g)
    [IsIso f] : IsIso snd :=
  have := h.isIso_snd_of_isIso
  hF.isIso_of_isIso_map snd

/-- A property of morphisms of the big fppf site of `S` which holds for isomorphisms holds
relative to the universe-lifted Yoneda embedding for every isomorphism of presheaves: a
represented base change of an isomorphism is an isomorphism, and the Yoneda embedding reflects
them. -/
theorem relative_of_isIso (P : MorphismProperty (BigFppfOver B S hS))
    (hP : ∀ ⦃X Y : BigFppfOver B S hS⦄ (f : X ⟶ Y), IsIso f → P f)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (ψ : F ⟶ G) [IsIso ψ] :
    P.relative (uliftYoneda.{u + 1}) ψ := by
  refine ⟨Functor.relativelyRepresentable.of_isIso (uliftYoneda.{u + 1}) ψ, ?_⟩
  intro A C g fst snd hpb
  exact hP snd (isIso_of_isPullback_map_of_isIso (ULiftYoneda.fullyFaithful _) hpb)

/-- An étale morphism of the big fppf site of `S` is an étale chart of the Yoneda presheaf of
its target: the Yoneda embedding preserves the fibre products of the site, which it has, and
étaleness of schemes is stable under base change. -/
theorem isEtaleChart_yoneda_map {V W : BigFppfOver B S hS} (q : W ⟶ V)
    (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    Space.IsEtaleChart B S hS (yoneda.obj V) (CostructuredArrow.mk (yoneda.map q)) := by
  let _ := B.hasPullbacks_schemes
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.forget B S hS) := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  let _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    { of_isPullback := fun h hg ↦ by
        change Etale ((BigFppfOver.toScheme B S hS).map _) at hg ⊢
        exact MorphismProperty.of_isPullback (h.map (BigFppfOver.toScheme B S hS)) hg }
  exact MorphismProperty.relative_map (F := yoneda) hq

/-- The affine étale site of an object of the big fppf site of `S` with affine underlying
scheme is not empty: the identity is an affine étale chart. -/
theorem nonempty_affineEtale_yoneda (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    Nonempty (Space.AffineEtale B S hS (yoneda.obj V)) := by
  refine ⟨⟨⟨CostructuredArrow.mk (yoneda.map (𝟙 V)), isEtaleChart_yoneda_map B S hS (𝟙 V) ?_⟩,
    hV⟩⟩
  rw [CategoryTheory.Functor.map_id]
  infer_instance

/-- The category of Stacks 0DEE is not empty: the identity of an affine formal algebraic space
is an object of it, being representable by algebraic spaces and étale. -/
theorem nonempty_affineEtaleFormalCharts {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    Nonempty (AffineEtaleFormalCharts B S hS X) :=
  ⟨⟨Over.mk (𝟙 X), hX, isRepresentableEtale_id B S hS X⟩⟩

/-! ### The base change of a chart to an affine object of the site -/

/-- The base change of an object `φ : U ⟶ X` of
`AlgebraicGeometry.FormalSpace.AffineEtaleFormalCharts` along a morphism `i` to `X` from the
sheaf represented by an object `V` of the site: a representing object of the site, the
cartesian square exhibiting it as the fibre product, and the affineness and étaleness of the
projection to `V`. -/
structure AffineEtaleBaseChange (X : FppfSheaf B S hS) (V : BigFppfOver B S hS)
    (i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X)
    (Y : AffineEtaleFormalCharts B S hS X) where
  /-- The object of the site representing the fibre product. -/
  obj : BigFppfOver B S hS
  /-- The projection to `V`. -/
  proj : obj ⟶ V
  /-- The projection to the source of the chart. -/
  fst : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj obj ⟶ Y.obj.left
  /-- The square is cartesian. -/
  isPullback : IsPullback fst
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map proj) Y.obj.hom i
  /-- The representing object is affine. -/
  isAffine : IsAffine ((BigFppfOver.toScheme B S hS).obj obj)
  /-- The projection to `V` is étale. -/
  etale : Etale ((BigFppfOver.toScheme B S hS).map proj)

/-- **The base change of a chart to an affine object of the site is an affine scheme étale over
it.** Let `X` be an affine formal algebraic space over `S`, let `V` be an object of the site
with affine underlying scheme and let `i` be a morphism to `X` from the sheaf represented by
`V`. Then the fibre product of `i` with an object of
`AlgebraicGeometry.FormalSpace.AffineEtaleFormalCharts B S hS X` is represented by an object of
the site whose underlying scheme is affine, and whose projection to `V` is étale.

Affineness is Stacks 0AKN. Étaleness comes from the étale half of the chart condition: the
represented base change over `V` is an étale morphism of algebraic spaces, and an isomorphism
of the representing object with the fibre product is an étale chart of it, so the projection is
étale relative to the Yoneda embedding, hence étale. -/
theorem nonempty_affineEtaleBaseChange {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X)
    (Y : AffineEtaleFormalCharts B S hS X) :
    Nonempty (AffineEtaleBaseChange B S hS X V i Y) := by
  classical
  obtain ⟨hU, hrep, hetale⟩ := Y.property
  obtain ⟨W, p, q, hpb, hWaff, -⟩ :=
    exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces B S hS Y.obj.hom hU hX hrep
      V hV i
  refine ⟨⟨W, q, p, hpb, hWaff, ?_⟩⟩
  -- the two Yoneda embeddings and the étaleness property of morphisms of the site
  let J := BigFppfOver.topology B S hS
  let L := sheafToPresheaf J (Type (u + 1))
  let e := sheafifiedYonedaCompForgetIso B S hS
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  -- the cartesian square of Stacks 0AKN, transported to presheaves and to `uliftYoneda`
  have hpre : IsPullback ((Sheaf.sheafifiedYoneda J).map q).hom p.hom i.hom Y.obj.hom.hom :=
    (hpb.map L).flip
  have hnat : ((Sheaf.sheafifiedYoneda J).map q).hom ≫ (e.app V).hom
      = (e.app W).hom ≫ (uliftYoneda.{u + 1}).map q := e.hom.naturality q
  have hu : IsPullback ((uliftYoneda.{u + 1}).map q) ((e.app W).inv ≫ p.hom)
      ((e.app V).inv ≫ i.hom) Y.obj.hom.hom :=
    hpre.of_iso (e.app W) (e.app V) (Iso.refl _) (Iso.refl _) hnat
      (by rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
      (by rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]) (by simp)
  -- the representing object is the fibre product, by a canonical isomorphism
  have hcan : IsPullback (pullback.fst ((e.app V).inv ≫ i.hom) Y.obj.hom.hom)
      (pullback.snd ((e.app V).inv ≫ i.hom) Y.obj.hom.hom) ((e.app V).inv ≫ i.hom)
      Y.obj.hom.hom := IsPullback.of_hasPullback _ _
  let ψ := hu.isoIsPullback _ _ hcan
  have hψfst : ψ.hom ≫ pullback.fst ((e.app V).inv ≫ i.hom) Y.obj.hom.hom
      = (uliftYoneda.{u + 1}).map q := hu.isoIsPullback_hom_fst _ _ hcan
  -- an isomorphism is an étale chart, so the projection is étale relative to Yoneda
  have hψ : P.relative (uliftYoneda.{u + 1}) ψ.hom := by
    refine relative_of_isIso B S hS P (fun _ _ f hf ↦ ?_) ψ.hom
    have _ : IsIso f := hf
    show Etale ((BigFppfOver.toScheme B S hS).map f)
    infer_instance
  have hcomp : P.relative (uliftYoneda.{u + 1})
      (ψ.hom ≫ pullback.fst ((e.app V).inv ≫ i.hom) Y.obj.hom.hom) :=
    hetale V ((e.app V).inv ≫ i.hom) W ψ.hom hψ
  rw [hψfst] at hcomp
  exact (MorphismProperty.of_relative_map hcomp : P q)

/-- A choice of base change of a chart to an affine object of the site, from
`AlgebraicGeometry.FormalSpace.nonempty_affineEtaleBaseChange`. -/
noncomputable def affineEtaleBaseChangeData {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X)
    (Y : AffineEtaleFormalCharts B S hS X) :
    AffineEtaleBaseChange B S hS X V i Y :=
  (nonempty_affineEtaleBaseChange B S hS hX V hV i Y).some

/-! ### The morphism induced on base changes -/

section Lift

variable {B S hS}
variable {X : FppfSheaf B S hS} {V : BigFppfOver B S hS}
    {i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    {Y Z : AffineEtaleFormalCharts B S hS X}

/-- The square used to induce a morphism of base changes: the projection of the base change of
`Y` to the source of the chart, followed by a morphism `Y ⟶ Z` of charts, sits over the
projection to `V`. -/
theorem AffineEtaleBaseChange.lift_w (dY : AffineEtaleBaseChange B S hS X V i Y) (f : Y ⟶ Z) :
    (dY.fst ≫ f.hom.left) ≫ Z.obj.hom
      = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map dY.proj ≫ i := by
  rw [Category.assoc, Over.w f.hom]
  exact dY.isPullback.w

/-- The morphism of the site induced on chosen base changes by a morphism of charts: the
unique morphism to the base change of `Z` through which the base change of `Y` maps, given by
the universal property of the cartesian square and the full faithfulness of the sheafified
Yoneda embedding. -/
noncomputable def AffineEtaleBaseChange.lift (dY : AffineEtaleBaseChange B S hS X V i Y)
    (dZ : AffineEtaleBaseChange B S hS X V i Z) (f : Y ⟶ Z) : dY.obj ⟶ dZ.obj :=
  (sheafifiedYonedaFF B S hS).preimage (dZ.isPullback.lift (dY.fst ≫ f.hom.left)
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map dY.proj) (dY.lift_w f))

/-- The sheafified Yoneda image of the induced morphism is the morphism the universal property
of the cartesian square produces. -/
theorem AffineEtaleBaseChange.map_lift (dY : AffineEtaleBaseChange B S hS X V i Y)
    (dZ : AffineEtaleBaseChange B S hS X V i Z) (f : Y ⟶ Z) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (dY.lift dZ f)
      = dZ.isPullback.lift (dY.fst ≫ f.hom.left)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map dY.proj) (dY.lift_w f) :=
  (sheafifiedYonedaFF B S hS).map_preimage _

/-- The induced morphism lies over `V`. -/
theorem AffineEtaleBaseChange.lift_proj (dY : AffineEtaleBaseChange B S hS X V i Y)
    (dZ : AffineEtaleBaseChange B S hS X V i Z) (f : Y ⟶ Z) :
    dY.lift dZ f ≫ dZ.proj = dY.proj :=
  (sheafifiedYonedaFF B S hS).map_injective <| by
    rw [Functor.map_comp, dY.map_lift dZ f, dZ.isPullback.lift_snd]

/-- The induced morphism is compatible with the projections to the sources of the charts. -/
theorem AffineEtaleBaseChange.lift_fst (dY : AffineEtaleBaseChange B S hS X V i Y)
    (dZ : AffineEtaleBaseChange B S hS X V i Z) (f : Y ⟶ Z) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (dY.lift dZ f) ≫ dZ.fst
      = dY.fst ≫ f.hom.left := by
  rw [dY.map_lift dZ f, dZ.isPullback.lift_fst]

/-- The induced morphism is the unique morphism of the site over `V` compatible with the
projections to the sources of the charts. -/
theorem AffineEtaleBaseChange.lift_uniq (dY : AffineEtaleBaseChange B S hS X V i Y)
    (dZ : AffineEtaleBaseChange B S hS X V i Z) (f : Y ⟶ Z) (m : dY.obj ⟶ dZ.obj)
    (hproj : m ≫ dZ.proj = dY.proj)
    (hfst : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m ≫ dZ.fst
      = dY.fst ≫ f.hom.left) :
    m = dY.lift dZ f := by
  apply (sheafifiedYonedaFF B S hS).map_injective
  refine dZ.isPullback.hom_ext ?_ ?_
  · rw [hfst, dY.lift_fst dZ f]
  · rw [← Functor.map_comp, ← Functor.map_comp, hproj, dY.lift_proj dZ f]

/-- The base change of a chart whose structure morphism is an isomorphism — the identity chart,
for instance — is `V` itself: the projection is an isomorphism, being a base change of one. -/
theorem AffineEtaleBaseChange.isIso_proj_of_isIso (hY : IsIso Y.obj.hom)
    (dY : AffineEtaleBaseChange B S hS X V i Y) : IsIso dY.proj := by
  have _ := hY
  exact isIso_of_isPullback_map_of_isIso (sheafifiedYonedaFF B S hS) dY.isPullback

end Lift

/-! ### The comparison functor -/

section Comparison

variable {X : FppfSheaf B S hS} (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X)

/-- The projection to `V` of the chosen base change of a chart is an étale chart of the Yoneda
presheaf of `V`, so it is an object of the small étale site of `V`; its source is affine, so it
is an object of the affine étale site of `V`. -/
theorem isEtaleChart_affineEtaleBaseChangeData (Y : AffineEtaleFormalCharts B S hS X) :
    Space.IsEtaleChart B S hS (yoneda.obj V)
      (CostructuredArrow.mk
        (yoneda.map (affineEtaleBaseChangeData B S hS hX V hV i Y).proj)) :=
  isEtaleChart_yoneda_map B S hS _ (affineEtaleBaseChangeData B S hS hX V hV i Y).etale

/-- **Stacks 0DEE**, the comparison functor, for an arbitrary object `V` of the site with
affine underlying scheme and an arbitrary morphism `i` to `X` from the sheaf it represents. On
objects it is the base change along `i`, which is an affine scheme étale over `V` by
`AlgebraicGeometry.FormalSpace.nonempty_affineEtaleBaseChange`; on morphisms it is the morphism
the universal property of the chosen cartesian square produces. -/
noncomputable def affineEtaleComparison :
    AffineEtaleFormalCharts B S hS X ⥤ Space.AffineEtale B S hS (yoneda.obj V) where
  obj Y :=
    ⟨⟨CostructuredArrow.mk
        (yoneda.map (affineEtaleBaseChangeData B S hS hX V hV i Y).proj),
      isEtaleChart_affineEtaleBaseChangeData B S hS hX V hV i Y⟩,
      (affineEtaleBaseChangeData B S hS hX V hV i Y).isAffine⟩
  map {Y Z} f :=
    ObjectProperty.homMk (ObjectProperty.homMk (CostructuredArrow.homMk
      ((affineEtaleBaseChangeData B S hS hX V hV i Y).lift
        (affineEtaleBaseChangeData B S hS hX V hV i Z) f)
      (by rw [CostructuredArrow.mk_hom_eq_self, CostructuredArrow.mk_hom_eq_self,
            ← Functor.map_comp,
            (affineEtaleBaseChangeData B S hS hX V hV i Y).lift_proj
              (affineEtaleBaseChangeData B S hS hX V hV i Z) f])))
  map_id Y := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    refine CostructuredArrow.hom_ext _ _ ?_
    exact (((affineEtaleBaseChangeData B S hS hX V hV i Y).lift_uniq
      (affineEtaleBaseChangeData B S hS hX V hV i Y) (𝟙 Y)
      (𝟙 (affineEtaleBaseChangeData B S hS hX V hV i Y).obj) (by simp)
      (by have h : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
              (𝟙 (affineEtaleBaseChangeData B S hS hX V hV i Y).obj) = 𝟙 _ :=
            CategoryTheory.Functor.map_id _ _
          rw [h, Category.id_comp]
          exact (Category.comp_id _).symm)).symm)
  map_comp {Y Z W} f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    refine CostructuredArrow.hom_ext _ _ ?_
    change (affineEtaleBaseChangeData B S hS hX V hV i Y).lift
        (affineEtaleBaseChangeData B S hS hX V hV i W) (f ≫ g) =
      (affineEtaleBaseChangeData B S hS hX V hV i Y).lift
        (affineEtaleBaseChangeData B S hS hX V hV i Z) f ≫
        (affineEtaleBaseChangeData B S hS hX V hV i Z).lift
          (affineEtaleBaseChangeData B S hS hX V hV i W) g
    refine ((affineEtaleBaseChangeData B S hS hX V hV i Y).lift_uniq
      (affineEtaleBaseChangeData B S hS hX V hV i W) (f ≫ g) _ ?_ ?_).symm
    · rw [Category.assoc, (affineEtaleBaseChangeData B S hS hX V hV i Z).lift_proj,
        (affineEtaleBaseChangeData B S hS hX V hV i Y).lift_proj]
    · rw [Functor.map_comp, Category.assoc,
        (affineEtaleBaseChangeData B S hS hX V hV i Z).lift_fst, ← Category.assoc,
        (affineEtaleBaseChangeData B S hS hX V hV i Y).lift_fst, Category.assoc]
      rfl

/-- The comparison functor carries a chart whose structure morphism is an isomorphism — the
identity chart of `X`, for instance — to the identity chart of `V`, up to isomorphism: the
chart it produces has an invertible structure morphism. -/
theorem isIso_hom_affineEtaleComparison_obj (Y : AffineEtaleFormalCharts B S hS X)
    (hY : IsIso Y.obj.hom) :
    IsIso (((affineEtaleComparison B S hS hX V hV i).obj Y).obj.obj.hom) := by
  have _ := (affineEtaleBaseChangeData B S hS hX V hV i Y).isIso_proj_of_isIso hY
  exact inferInstanceAs (IsIso (yoneda.map (affineEtaleBaseChangeData B S hS hX V hV i Y).proj))

end Comparison

/-- **Stacks 0DEE**, the comparison functor into the affine étale site of `X`. Let `X` be an
affine formal algebraic space over `S` whose reduction is the sheaf represented by an object
`V` of the site with affine underlying scheme, by a morphism `i`. By Stacks 0DEA the affine
étale site of `X` is the affine étale site of its reduction, that is of `V`, and this is the
functor to it from the category of the morphisms `φ : U ⟶ X` with `U` an affine formal
algebraic space and `φ` representable by algebraic spaces and étale, sending `φ` to
`U ×_X X_red`.

The reduction is carried as data, with its affineness, rather than chosen from Stacks 0AIN;
for an affine formal algebraic space the reduction is an affine scheme, which is why the datum
is not a restriction. Stacks 0DEE asserts that this functor is an equivalence; the
quasi-inverse is not constructed here. -/
@[stacks 0DEE "the comparison functor from the category of the morphisms satisfying (1) and \
(2) to the affine étale site of `X`, carrying the reduction of `X` and its affineness as data \
rather than chosen from Stacks 0AIN; the functor is not shown to be an equivalence"]
noncomputable def reductionAffineEtaleComparison {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X)
    (_hred : IsReduction B S hS X
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V) i) :
    AffineEtaleFormalCharts B S hS X ⥤ Space.AffineEtale B S hS (yoneda.obj V) :=
  affineEtaleComparison B S hS hX V hV i

end AlgebraicGeometry.FormalSpace

end
