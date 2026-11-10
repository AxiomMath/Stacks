module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousMorphismDerivedPushforward
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousMorphismBaseChange
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousMorphism

/-!
# The morphism of total topoi of a morphism between simplicial sites, continuous case

Let `h` be a morphism between simplicial sites in the continuous case, Stacks 0D95 case (A). Its
degreewise functors assemble to a continuous functor between the total categories, so there is an
inverse image `h_total^{-1}` on sheaves of sets, the sheafified left Kan extension along that
functor. This module proves that `h_total^{-1}` is degreewise `h_n^{-1}` — the last assertion of
Stacks 0D96 read on inverse images — and that it is therefore left exact, and it identifies the
direct and inverse images of the morphism `totalMorphism` between the total topoi.

The names below are in the namespace `CategoryTheory.SimplicialSite.Morphism`, except
`CategoryTheory.sheafPullbackContinuousSquareIso`.

## Main definitions

* `CategoryTheory.sheafPullbackContinuousSquareIso`: the comparison of inverse images around a
  commuting square of continuous site functors whose right-hand vertical is also cocontinuous, for
  a Guitart exact square.
* `inclusionSquare`: the square formed by the two component inclusions of a simplicial degree, the
  degreewise functor and the functor between the total categories.
* `totalInverseImage` and `componentInverseImage`: the inverse images of sheaves of sets along the
  total morphism and along the morphism of simplicial degree `n`.
* `totalInverseImageRestrictIso`: **Stacks 0D96** in case (A), on inverse images:
  `g_n^{-1} h_total^{-1} = h_n^{-1} g_n^{-1}`.

## Main results

* `guitartExact_inclusionSquare`: the square of the component inclusions is Guitart exact.
* `preservesFiniteLimits_totalInverseImage`: the inverse image on sheaves of sets along the total
  morphism is left exact.
* `totalMorphism_pushforward`, `totalMorphism_inverseImage`: the direct and inverse images of the
  morphism of total topoi are the direct image and the sheafified left Kan extension along the
  functor between the total categories.

## Implementation notes

The restriction formula is a base change for left Kan extensions, dual to the base change for right
Kan extensions that gives the corresponding formula for direct images in case (B). It holds because
the square of the component inclusions and the functor between the total categories is Guitart
exact, and that is proved here by exhibiting, for every arrow of the total category out of an
object of one component, a terminal factorization of it through that component: the arrow inside
the component given by its fibre component, followed by the Cartesian lift of its base. This is the
fibration property of the contravariant Grothendieck construction, read on the Hom sets. The
transport from presheaves to sheaves uses that the component inclusion is cocontinuous as well as
continuous, which is what makes restriction along it commute with sheafification.

Left exactness is then degreewise, which is where the description of sheaves on a total site as
systems of sheaves on the components (Stacks 09WF) enters: in the weak form needed here, a functor
into sheaves on the total site preserves finite limits as soon as all its degreewise restrictions
do, because a limit of sheaves is computed sectionwise and every object of the total category lies
in the component of its simplicial degree. Degreewise, left exactness is exactly the substantive
half of the hypothesis that each degreewise functor represents a morphism of sites, so nothing
further is needed.

Several instances are restated here with the simplicial site as an explicit argument
(`isContinuous_componentFunctor_inl`, `isCocontinuous_componentFunctor_inl`,
`isRightAdjoint_componentPushforward`, `isRightAdjoint_totalPushforward`). A situation of case (A)
keeps its component and total categories behind a `match` on the two cases, and instance search
does not reliably see through it, not even to the `SmallCategory` instances that the general
construction of the left adjoint needs.

## References

* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 00XC](https://stacks.math.columbia.edu/tag/00XC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite

universe v₁ u₁ v₂ u₂ u

namespace CategoryTheory

attribute [local simp] PrelaxFunctor.map₂_eqToHom

attribute [local implicit_reducible] CoGrothendieck.ι Quiver.Hom.toLoc
  CategoryTheory.SimplicialSite.totalPseudofunctor CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  CategoryTheory.SimplicialSite.Morphism.totalFunctor

/-- An arrow inside one fibre of a contravariant Grothendieck construction, followed by an
arbitrary arrow out of that fibre, is the arrow with the same base and the composite fibre
component. This is the form of
`CategoryTheory.Pseudofunctor.CoGrothendieck.ι_map_comp_ιNatTrans_app` in which the second factor
is not required to be a Cartesian lift. -/
private theorem coGrothendieck_ι_map_comp_mk {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) {m : 𝒮} {Y : CoGrothendieck F}
    {x z : F.obj ⟨op m⟩} (a : x ⟶ z) (f : m ⟶ Y.base)
    (b : z ⟶ (F.map f.op.toLoc).toFunctor.obj Y.fiber) :
    (CoGrothendieck.ι F m).map a ≫ (⟨f, b⟩ : (CoGrothendieck.ι F m).obj z ⟶ Y) =
      (⟨f, a ≫ b⟩ : (CoGrothendieck.ι F m).obj x ⟶ Y) := by
  apply CoGrothendieck.Hom.ext _ _ (Category.id_comp f)
  simp [CoGrothendieck.ι, CoGrothendieck.categoryStruct_comp_fiber,
    F.mapComp_id_right_inv_app, ← NatTrans.naturality_assoc, ← Cat.Hom₂.comp_app,
    Bicategory.Strict.rightUnitor_eqToIso]

/-- The comparison of inverse images around a commuting square of continuous site functors whose
right-hand vertical is in addition cocontinuous: the sheafified left Kan extension along the
bottom, followed by restriction along that vertical, is restriction along the left-hand vertical
followed by the sheafified left Kan extension along the top, for a Guitart exact square. -/
def sheafPullbackContinuousSquareIso {A₁ A₂ A₃ A₄ : Type u} [SmallCategory A₁]
    [SmallCategory A₂] [SmallCategory A₃] [SmallCategory A₄]
    (v : A₁ ⥤ A₂) (i : A₁ ⥤ A₃) (j : A₂ ⥤ A₄) (w : A₃ ⥤ A₄)
    (J₁ : GrothendieckTopology A₁) (J₂ : GrothendieckTopology A₂)
    (J₃ : GrothendieckTopology A₃) (J₄ : GrothendieckTopology A₄)
    [iv : v.IsContinuous J₁ J₂] [ii : i.IsContinuous J₁ J₃] [ij : j.IsContinuous J₂ J₄]
    [ijc : j.IsCocontinuous J₂ J₄] [iw : w.IsContinuous J₃ J₄]
    (q : TwoSquare v i j w) [hq : q.GuitartExact] :
    w.sheafPullback (Type u) J₃ J₄ ⋙ j.sheafPushforwardContinuous (Type u) J₂ J₄ ≅
      i.sheafPushforwardContinuous (Type u) J₁ J₃ ⋙ v.sheafPullback (Type u) J₁ J₂ :=
  haveI : q.op.GuitartExact := inferInstance
  calc
    _ ≅ sheafToPresheaf J₃ (Type u) ⋙ w.op.lan ⋙ presheafToSheaf J₄ (Type u) ⋙
        j.sheafPushforwardContinuous (Type u) J₂ J₄ :=
      Functor.isoWhiskerRight
        (Functor.sheafPullbackConstruction.sheafPullbackIso w (Type u) J₃ J₄) _
    _ ≅ sheafToPresheaf J₃ (Type u) ⋙ w.op.lan ⋙
        (Functor.whiskeringLeft A₂ᵒᵖ A₄ᵒᵖ (Type u)).obj j.op ⋙ presheafToSheaf J₂ (Type u) :=
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (j.pushforwardContinuousSheafificationCompatibility (Type u) J₂ J₄).symm)
    _ ≅ sheafToPresheaf J₃ (Type u) ⋙
        (Functor.whiskeringLeft A₁ᵒᵖ A₃ᵒᵖ (Type u)).obj i.op ⋙ v.op.lan ⋙
          presheafToSheaf J₂ (Type u) :=
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (asIso (q.op.lanBaseChange (D := Type u))).symm _)
    _ ≅ i.sheafPushforwardContinuous (Type u) J₁ J₃ ⋙ v.sheafPullback (Type u) J₁ J₂ :=
      Functor.isoWhiskerLeft (i.sheafPushforwardContinuous (Type u) J₁ J₃)
        (Functor.sheafPullbackConstruction.sheafPullbackIso v (Type u) J₁ J₂).symm

namespace SimplicialSite.Morphism

open SimplicialSiteSituation

variable {C C' : SimplicialSite.{u}}

/-- The inclusion of a component of a situation of case (A) is continuous. -/
instance isContinuous_componentFunctor_inl (D : SimplicialSite.{u}) (n : SimplexCategory) :
    (componentFunctor (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}) n).IsContinuous
      ((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).totalTopology :=
  componentFunctor_isContinuous _ n

/-! ### The functor between the total categories, typed by the situations -/

/-- The functor between the total categories, with its source and target written as the total
categories of the two simplicial-site situations of case (A) rather than as contravariant
Grothendieck constructions. The two spellings are definitionally equal. -/
def totalFunctorOfSituation (h : SimplicialSite.Morphism C C') :
    (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalCategory ⥤
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalCategory :=
  h.totalFunctor

/-- The functor between the total categories is continuous for the total topologies. -/
instance isContinuous_totalFunctorOfSituation (h : SimplicialSite.Morphism C C') :
    h.totalFunctorOfSituation.IsContinuous
      (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology :=
  h.totalFunctor_isContinuous

/-- The degreewise functor in simplicial degree `n` is continuous. -/
instance isContinuous_component (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    (h.hom.app n).toFunctor.IsContinuous
      ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) :=
  (h.isMorphismOfSites n).isContinuous

/-- The inclusion of the component of degree `n` followed by the functor between the total
categories is the degreewise functor followed by the inclusion of the component of degree `n`. -/
theorem componentFunctor_comp_totalFunctorOfSituation (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    componentFunctor (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n ⋙
        h.totalFunctorOfSituation =
      (h.hom.app n).toFunctor ⋙
        componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n :=
  h.ι_comp_totalFunctor (Opposite.op n)

/-- The inclusion of a component followed by the functor between the total categories is
continuous. -/
instance isContinuous_componentFunctor_comp_totalFunctorOfSituation
    (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    (componentFunctor (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n ⋙
      h.totalFunctorOfSituation).IsContinuous
      ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology :=
  Functor.isContinuous_comp
    (componentFunctor (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n)
    h.totalFunctorOfSituation
    ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n)
    (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology

/-- The degreewise functor followed by the inclusion of a component is continuous. -/
instance isContinuous_component_comp_componentFunctor (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    ((h.hom.app n).toFunctor ⋙
      componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).IsContinuous
      ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology := by
  rw [← h.componentFunctor_comp_totalFunctorOfSituation n]
  exact h.isContinuous_componentFunctor_comp_totalFunctorOfSituation n

/-! ### The direct images on sheaves of sets -/

/-- The direct image of sheaves of sets along the total morphism of a morphism between simplicial
sites in the continuous case. -/
def totalPushforward (h : SimplicialSite.Morphism C C') :
    Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u) ⥤
      Sheaf (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u) :=
  h.totalFunctorOfSituation.sheafPushforwardContinuous (Type u)
    (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology

/-- The direct image of sheaves of sets in simplicial degree `n`. -/
def componentPushforward (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) (Type u) ⥤
      Sheaf ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n) (Type u) :=
  (h.hom.app n).toFunctor.sheafPushforwardContinuous (Type u)
    ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n)
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)

/-- The square formed by the two component inclusions of simplicial degree `n`, the degreewise
functor and the functor between the total categories. It commutes on the nose, so its 2-cell is the
transport along that equality, whose components are identities. -/
def inclusionSquare (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    TwoSquare (h.hom.app n).toFunctor
      (CoGrothendieck.ι C'.totalPseudofunctor (op n))
      (CoGrothendieck.ι C.totalPseudofunctor (op n)) h.totalFunctor :=
  TwoSquare.mk _ _ _ _ (eqToHom (h.ι_comp_totalFunctor (op n)).symm)

/-- The components of the 2-cell of the square of the component inclusions are identities. -/
@[simp]
theorem inclusionSquare_app (h : SimplicialSite.Morphism C C') (n : SimplexCategory)
    (V : C'.underlying.obj n) : (h.inclusionSquare n).app V = 𝟙 _ :=
  (eqToHom_app (h.ι_comp_totalFunctor (op n)).symm V).trans (eqToHom_refl _ _)

/-- The 2-cell of the square of the component inclusions is an identity, so it drops out of any
composite. -/
theorem inclusionSquare_app_comp (h : SimplicialSite.Morphism C C') (n : SimplexCategory)
    (V : C'.underlying.obj n) {W : CoGrothendieck C.totalPseudofunctor}
    (k : h.totalFunctor.obj ((CoGrothendieck.ι C'.totalPseudofunctor (op n)).obj V) ⟶ W) :
    (h.inclusionSquare n).app V ≫ k = k :=
  (congrArg (fun t => t ≫ k) (h.inclusionSquare_app n V)).trans (Category.id_comp k)

/-- The factorization of an arrow of the total category out of a component of simplicial degree
`n`: it is the arrow inside that component given by its fibre component, followed by the Cartesian
lift of its base. -/
private theorem inclusionSquare_factor (h : SimplicialSite.Morphism C C') (n : SimplexCategory)
    {X : C.underlying.obj n} {Y : CoGrothendieck C'.totalPseudofunctor}
    {Z : C'.underlying.obj n} (a : X ⟶ (h.hom.app n).toFunctor.obj Z)
    (b : (CoGrothendieck.ι C'.totalPseudofunctor (op n)).obj Z ⟶ Y) :
    (CoGrothendieck.ι C.totalPseudofunctor (op n)).map a ≫
        (h.inclusionSquare n).app Z ≫ h.totalFunctor.map b =
      (⟨b.base, a ≫ (h.hom.app n).toFunctor.map b.fiber ≫
          eqToHom (h.app_obj_map b.base.unop Y.fiber)⟩ :
        (CoGrothendieck.ι C.totalPseudofunctor (op n)).obj X ⟶ h.totalFunctor.obj Y) :=
  (congrArg (fun t => (CoGrothendieck.ι C.totalPseudofunctor (op n)).map a ≫ t)
      (h.inclusionSquare_app_comp n Z (h.totalFunctor.map b))).trans
    (coGrothendieck_ι_map_comp_mk C.totalPseudofunctor (Y := h.totalFunctor.obj Y)
      (m := op n) (x := X) (z := (h.hom.app n).toFunctor.obj Z) a b.base
      ((h.hom.app n).toFunctor.map b.fiber ≫ eqToHom (h.app_obj_map b.base.unop Y.fiber)))

/-- The square of the component inclusions of simplicial degree `n` is Guitart exact. -/
instance guitartExact_inclusionSquare (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    (h.inclusionSquare n).GuitartExact := by
  constructor
  intro X Y g
  have comm : (CoGrothendieck.ι C.totalPseudofunctor (op n)).map
        (g.fiber ≫ eqToHom (h.app_obj_map g.base.unop Y.fiber).symm) ≫
      (h.inclusionSquare n).app _ ≫
      h.totalFunctor.map (⟨g.base, 𝟙 ((C'.underlying.map g.base.unop).toFunctor.obj Y.fiber)⟩ :
        (CoGrothendieck.ι C'.totalPseudofunctor (op n)).obj
          ((C'.underlying.map g.base.unop).toFunctor.obj Y.fiber) ⟶ Y) = g := by
    rw [h.inclusionSquare_factor n _ _]
    refine CoGrothendieck.Hom.ext _ _ rfl ?_
    simp
  have hterminal : ∀ Q : (h.inclusionSquare n).StructuredArrowRightwards g,
      Nonempty (Q ⟶
        TwoSquare.StructuredArrowRightwards.mk (h.inclusionSquare n) g _ _ _ comm) := by
    intro Q
    obtain ⟨Z, a, b, hcomm, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective Q
    rw [h.inclusionSquare_factor n a b] at hcomm
    have hbase : b.base = g.base := congrArg CoGrothendieck.Hom.base hcomm
    obtain ⟨f, β⟩ := b
    dsimp only at hbase
    subst hbase
    have hfiber := CoGrothendieck.Hom.congr hcomm
    simp only [eqToHom_refl, Category.comp_id] at hfiber
    refine ⟨StructuredArrow.homMk (CostructuredArrow.homMk β ?_) ?_⟩
    · refine (coGrothendieck_ι_map_comp_mk C'.totalPseudofunctor (Y := Y) (m := op n) (x := Z)
        (z := (C'.underlying.map g.base.unop).toFunctor.obj Y.fiber) β g.base
        (𝟙 ((C'.underlying.map g.base.unop).toFunctor.obj Y.fiber))).trans ?_
      exact congrArg (fun t => (⟨g.base, t⟩ :
        (CoGrothendieck.ι C'.totalPseudofunctor (op n)).obj Z ⟶ Y)) (Category.comp_id β)
    · have ha : a ≫ (h.hom.app n).toFunctor.map β =
          g.fiber ≫ eqToHom (h.app_obj_map g.base.unop Y.fiber).symm := by
        rw [← hfiber]
        simp
      exact CostructuredArrow.hom_ext _ _ ha
  have : Nonempty ((h.inclusionSquare n).StructuredArrowRightwards g) :=
    ⟨TwoSquare.StructuredArrowRightwards.mk (h.inclusionSquare n) g _ _ _ comm⟩
  exact zigzag_isConnected fun Q₁ Q₂ ↦
    (Zigzag.of_hom (hterminal Q₁).some).trans (Zigzag.of_inv (hterminal Q₂).some)

/-! ### The inverse image on sheaves of sets, and the morphism of total topoi -/

/-- The inclusion of a component of a situation of case (A) is cocontinuous. -/
instance isCocontinuous_componentFunctor_inl (D : SimplicialSite.{u}) (n : SimplexCategory) :
    (componentFunctor (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}) n).IsCocontinuous
      ((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).totalTopology :=
  componentFunctor_isCocontinuous _ n

/-- The direct image in simplicial degree `n` has a left adjoint, in the spelling of the situations
of case (A). -/
instance isRightAdjoint_componentPushforward (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    ((h.hom.app n).toFunctor.sheafPushforwardContinuous (Type u)
        ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)).IsRightAdjoint :=
  haveI := (h.isMorphismOfSites n).isContinuous
  inferInstanceAs (((h.hom.app n).toFunctor.sheafPushforwardContinuous (Type u)
    (C'.coverage n).toGrothendieck (C.coverage n).toGrothendieck).IsRightAdjoint)

/-- The direct image along the total morphism has a left adjoint, in the spelling of the situations
of case (A). -/
instance isRightAdjoint_totalPushforward (h : SimplicialSite.Morphism C C') :
    (h.totalFunctorOfSituation.sheafPushforwardContinuous (Type u)
        (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology).IsRightAdjoint :=
  haveI := h.totalFunctor_isContinuous
  inferInstanceAs ((h.totalFunctor.sheafPushforwardContinuous (Type u)
    C'.totalTopology C.totalTopology).IsRightAdjoint)

/-- The inverse image of sheaves of sets along the total morphism of a morphism between simplicial
sites in the continuous case: the sheafified left Kan extension along the functor between the total
categories. -/
def totalInverseImage (h : SimplicialSite.Morphism C C') :
    Sheaf (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u) ⥤
      Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u) :=
  h.totalFunctorOfSituation.sheafPullback (Type u)
    (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology

/-- The inverse image of sheaves of sets in simplicial degree `n`, which is the inverse image of
the morphism of topoi of the degreewise morphism of sites. -/
def componentInverseImage (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    Sheaf ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n) (Type u) ⥤
      Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) (Type u) :=
  (h.hom.app n).toFunctor.sheafPullback (Type u)
    ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n)
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)

/-- The inverse image in simplicial degree `n` is the inverse image of the morphism of topoi
attached to the degreewise morphism of sites, which is the component morphism of Stacks 0D95. -/
theorem morphismOfTopoi_inverseImage (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    (h.isMorphismOfSites n).morphismOfTopoi.inverseImage = h.componentInverseImage n :=
  rfl

/-- **Stacks 0D96**, case (A). Restriction to the component of simplicial degree `n`, applied to
the inverse image along the total morphism, is the inverse image in degree `n` applied to
restriction to the component of that degree: `h_total^{-1}` is degreewise `h_n^{-1}`. -/
@[stacks 0D96 "case (A), restriction of the inverse image",
  sga "4 VI 7.4.9" "simplicial, f^{-1}"]
def totalInverseImageRestrictIso (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    h.totalInverseImage ⋙ restrict (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n ≅
      restrict (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n ⋙ h.componentInverseImage n :=
  sheafPullbackContinuousSquareIso
    (h.hom.app n).toFunctor
    (componentFunctor (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n)
    (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
    h.totalFunctorOfSituation
    ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n)
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
    (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
    (iv := h.isContinuous_component n)
    (ii := isContinuous_componentFunctor_inl C' n)
    (ij := isContinuous_componentFunctor_inl C n)
    (ijc := isCocontinuous_componentFunctor_inl C n)
    (iw := h.isContinuous_totalFunctorOfSituation)
    (h.inclusionSquare n) (hq := h.guitartExact_inclusionSquare n)

/-- A functor into sheaves of sets on the total site of a case (A) simplicial site preserves finite
limits as soon as its composite with restriction to every simplicial degree does. -/
theorem preservesFiniteLimits_of_restrict {E : Type u₁} [Category.{v₁} E]
    (D : SimplicialSite.{u})
    (L : E ⥤ Sheaf (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u))
    (hL : ∀ n, PreservesFiniteLimits
      (L ⋙ restrict (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}) n)) :
    PreservesFiniteLimits L := by
  have : PreservesFiniteLimits (L ⋙ sheafToPresheaf
      (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u)) := by
    apply preservesFiniteLimits_of_evaluation
    intro Z
    have := hL Z.unop.base.unop
    exact comp_preservesFiniteLimits
      (L ⋙ restrict (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}) Z.unop.base.unop)
      (sheafToPresheaf ((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).componentTopology
          Z.unop.base.unop) (Type u) ⋙
        (evaluation ((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).component
          Z.unop.base.unop)ᵒᵖ (Type u)).obj (op Z.unop.fiber))
  exact preservesFiniteLimits_of_reflects_of_preserves L
    (sheafToPresheaf (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u))

/-- The inverse image in simplicial degree `n` is left exact. -/
instance preservesFiniteLimits_componentInverseImage (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) : PreservesFiniteLimits (h.componentInverseImage n) :=
  (h.isMorphismOfSites n).preservesFiniteLimits

/-- **Left exactness of the inverse image on sheaves of sets for the total functor of a morphism
between simplicial sites in the continuous case.** -/
instance preservesFiniteLimits_totalInverseImage (h : SimplicialSite.Morphism C C') :
    PreservesFiniteLimits h.totalInverseImage :=
  preservesFiniteLimits_of_restrict C h.totalInverseImage fun n ↦
    preservesFiniteLimits_of_natIso (h.totalInverseImageRestrictIso n).symm

/-- The direct image of the total morphism of topoi is the direct image along the functor between
the total categories. -/
theorem totalMorphism_pushforward (h : SimplicialSite.Morphism C C') :
    h.totalMorphism.pushforward = h.totalPushforward :=
  rfl

/-- The inverse image of the total morphism of topoi is the sheafified left Kan extension along the
functor between the total categories. -/
theorem totalMorphism_inverseImage (h : SimplicialSite.Morphism C C') :
    h.totalMorphism.inverseImage = h.totalInverseImage :=
  rfl

end SimplicialSite.Morphism

end CategoryTheory

end
