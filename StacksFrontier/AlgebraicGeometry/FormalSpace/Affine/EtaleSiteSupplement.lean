module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSiteChart
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Further results on `StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite`

Results of this development stated next to
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite` but kept in a module of their own,
so that that module stays as it is on the base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Lift

variable {B S hS}

variable {X : FppfSheaf B S hS} {V : BigFppfOver B S hS}
    {i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    {Y Z : AffineEtaleFormalCharts B S hS X}

end Lift

section Comparison

variable {X : FppfSheaf B S hS} (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X)

end Comparison

/-! ### The affine case of thickening invariance of the étale site -/

/-- **An affine scheme étale over the thinner of two objects of the site related by a thickening
lifts to an affine scheme étale over the thicker one.** This is the affine case of the
thickening invariance of the étale site, the lifting step of the quasi-inverse the source of
Stacks 0DEE writes down: let `j : W₀ ⟶ W` be a morphism of the big fppf category over `S`
whose underlying morphism of schemes is a thickening, and let `p` be an étale morphism of
schemes from the affine scheme underlying an object `U` of the category to the scheme
underlying `W₀`. Then
there is an object `V` of the category with affine underlying scheme and a morphism `q : V ⟶ W`
whose underlying morphism of schemes is étale, whose base change along `j` is `U` over `W₀`.

The lift and its étaleness are Stacks 039R for objects of a big fppf site,
`Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective`. Its
affineness is Stacks 06AD, `Stacks.Thickenings.isAffine_of_isThickening`: the base change of
`j` along `q` is a thickening, thickenings being stable under base change, and its source is
`U`, which is affine. -/
theorem exists_affine_etale_lift_of_isThickening {W₀ W : BigFppfOver B S hS} (j : W₀ ⟶ W)
    (hj : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map j))
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (p : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj W₀)
    (hp : Etale p) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ W),
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
          ∃ e : pullback ((BigFppfOver.toScheme B S hS).map q)
              ((BigFppfOver.toScheme B S hS).map j) ≅ (BigFppfOver.toScheme B S hS).obj U,
            e.hom ≫ p = pullback.snd ((BigFppfOver.toScheme B S hS).map q)
              ((BigFppfOver.toScheme B S hS).map j) := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j) := hj.1
  obtain ⟨V, q, hq, e, he⟩ :=
    Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective
      B S hS j hj.2 U p hp
  refine ⟨V, q, hq, ?_, e, he⟩
  let : MorphismProperty.IsStableUnderBaseChange
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) :=
    isThickening_isStableUnderBaseChange
  have _ : IsAffine (pullback ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map j)) := IsAffine.of_isIso e.hom
  exact Stacks.Thickenings.isAffine_of_isThickening
    (MorphismProperty.of_isPullback (P := @Stacks.Thickenings.IsThickening)
      (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map j)).flip hj)

/-- **A jointly surjective family of affine schemes étale over the thinner of two objects of
the site related by a thickening lifts to a jointly surjective family of affine schemes étale
over the thicker one.** This is the covering form of
`AlgebraicGeometry.FormalSpace.exists_affine_etale_lift_of_isThickening`, which lifts a single
chart: each member of the family is lifted separately by that theorem, and the lifted family is
again jointly surjective. Surjectivity is where the thickening is used a second time. A point
`t` of the thick end `W` is the image of a point `t₀` of the thin end `W₀`, because a
thickening is surjective; `t₀` is the image of a point `x` of some member `U m` of the given
family; and the image of `x` in the lift `V m`, taken through the identification of `U m` with
`V m ×_W W₀` and the first projection, has image `t` in `W`, because that square commutes. No
finiteness or smallness is asked of the index type. -/
theorem exists_affine_etale_cover_lift_of_isThickening {W₀ W : BigFppfOver B S hS} (j : W₀ ⟶ W)
    (hj : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map j))
    {I : Type*} (U : I → BigFppfOver B S hS)
    (hU : ∀ m, IsAffine ((BigFppfOver.toScheme B S hS).obj (U m)))
    (p : ∀ m, (BigFppfOver.toScheme B S hS).obj (U m) ⟶
      (BigFppfOver.toScheme B S hS).obj W₀)
    (hp : ∀ m, Etale (p m))
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj W₀, ∃ m x, p m x = t) :
    ∃ (V : I → BigFppfOver B S hS) (q : ∀ m, V m ⟶ W),
      (∀ m, Etale ((BigFppfOver.toScheme B S hS).map (q m))) ∧
        (∀ m, IsAffine ((BigFppfOver.toScheme B S hS).obj (V m))) ∧
          (∀ m, ∃ e : pullback ((BigFppfOver.toScheme B S hS).map (q m))
              ((BigFppfOver.toScheme B S hS).map j) ≅
                (BigFppfOver.toScheme B S hS).obj (U m),
              e.hom ≫ p m = pullback.snd ((BigFppfOver.toScheme B S hS).map (q m))
                ((BigFppfOver.toScheme B S hS).map j)) ∧
            ∀ t : (BigFppfOver.toScheme B S hS).obj W,
              ∃ m x, (BigFppfOver.toScheme B S hS).map (q m) x = t := by
  choose V q hq hV e he using fun m =>
    exists_affine_etale_lift_of_isThickening B S hS j hj (U m) (hU m) (p m) (hp m)
  refine ⟨V, q, hq, hV, fun m => ⟨e m, he m⟩, fun t => ?_⟩
  obtain ⟨t₀, rfl⟩ := hj.2 t
  obtain ⟨m, x, rfl⟩ := hcov t₀
  have hcomp : (e m).inv ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map (q m))
        ((BigFppfOver.toScheme B S hS).map j) ≫ (BigFppfOver.toScheme B S hS).map (q m)
      = p m ≫ (BigFppfOver.toScheme B S hS).map j := by
    rw [pullback.condition, ← he m, Category.assoc, Iso.inv_hom_id_assoc]
  refine ⟨m, pullback.fst ((BigFppfOver.toScheme B S hS).map (q m))
    ((BigFppfOver.toScheme B S hS).map j) ((e m).inv x), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]

/-! ### The reduction of an affine formal algebraic space, as an affine object of the site -/

/-- A reduction stays a reduction after precomposition with an isomorphism of its source: the
source of the new inclusion is again a reduced algebraic space, the new inclusion is again a
representable thickening, and the unique factorization property follows from these by
`AlgebraicGeometry.FormalSpace.isReduction_of_isRepresentableThickening`. -/
theorem isReduction_comp_iso {X Xred Xred' : FppfSheaf B S hS} (e : Xred' ≅ Xred)
    {i : Xred ⟶ X} (h : IsReduction B S hS X Xred i) :
    IsReduction B S hS X Xred' (e.hom ≫ i) := by
  let eP : Xred.obj ≅ Xred'.obj :=
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso e).symm
  refine isReduction_of_isRepresentableThickening B S hS (e.hom ≫ i) ?_ ?_ ?_
  · exact Space.isAlgebraicSpaceULift_of_iso B S hS eP h.algebraic
  · obtain ⟨W, atlas, hsurj, hetale, hWred⟩ := h.reduced
    exact ⟨W, atlas ≫ eP.hom, MorphismProperty.RespectsIso.postcomp _ eP.hom atlas hsurj,
      MorphismProperty.RespectsIso.postcomp _ eP.hom atlas hetale, hWred⟩
  · exact MorphismProperty.RespectsIso.precomp _ eP.inv i.hom h.isRepresentableThickening

/-- The reduction of an fppf sheaf `X`, exhibited by an object of the big fppf site of `S`
whose underlying scheme is affine: the object, its affineness, the inclusion of the sheaf it
represents into `X`, and the proof that the inclusion exhibits that sheaf as the reduction
`X_red`. This is the shape in which the comparison functor of Stacks 0DEE consumes the
reduction, and for an affine formal algebraic space it always exists, by
`AlgebraicGeometry.FormalSpace.nonempty_affineReductionChart`. -/
structure AffineReductionChart (X : FppfSheaf B S hS) where
  /-- The object of the site representing the reduction. -/
  obj : BigFppfOver B S hS
  /-- Its underlying scheme is affine. -/
  isAffine : IsAffine ((BigFppfOver.toScheme B S hS).obj obj)
  /-- The inclusion of the reduction into `X`. -/
  inclusion : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj obj ⟶ X
  /-- The inclusion exhibits the represented sheaf as the reduction of `X`. -/
  isReduction : IsReduction B S hS X
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj obj) inclusion

/-- **The reduction of an affine formal algebraic space is an affine object of the site.** This
is Stacks 0AIN for an affine formal algebraic space, in the shape the comparison functor of
Stacks 0DEE consumes: the reduction exists by
`AlgebraicGeometry.FormalSpace.exists_isReduction_reduced_affine_siteObject_of_isAffineFormal`
as a reduced affine object `T` of the site with a representable thickening out of the
universe-lifted Yoneda sheaf of `T`, and
`AlgebraicGeometry.FormalSpace.yonedaSheafIsoSheafifiedYoneda` moves that inclusion to the
sheafified Yoneda embedding, the site being subcanonical. -/
theorem nonempty_affineReductionChart {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    Nonempty (AffineReductionChart B S hS X) := by
  obtain ⟨T, g, -, hTaff, -, hg⟩ :=
    exists_isReduction_reduced_affine_siteObject_of_isAffineFormal B S hS X hX
  exact ⟨⟨T, hTaff, (yonedaSheafIsoSheafifiedYoneda B S hS T).symm.hom ≫ g,
    isReduction_comp_iso B S hS (yonedaSheafIsoSheafifiedYoneda B S hS T).symm hg⟩⟩

/-- The chosen reduction of an affine formal algebraic space as an affine object of the site,
from `AlgebraicGeometry.FormalSpace.nonempty_affineReductionChart`. Which reduction is chosen is
immaterial: any two are canonically isomorphic over `X`, by
`AlgebraicGeometry.FormalSpace.AffineReductionChart.iso`. -/
noncomputable def affineReductionChart {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) : AffineReductionChart B S hS X :=
  Classical.choice (nonempty_affineReductionChart B S hS hX)

namespace AffineReductionChart

variable {B S hS} {X : FppfSheaf B S hS}

/-- The morphism of the site induced by the universal property of a reduction between the
objects representing two reductions of `X` by affine objects of the site. -/
noncomputable def map (c c' : AffineReductionChart B S hS X) : c.obj ⟶ c'.obj :=
  (sheafifiedYonedaFF B S hS).preimage
    (c'.isReduction.universal _ c.isReduction.algebraic c.isReduction.reduced
      c.inclusion).exists.choose

/-- The induced morphism is compatible with the inclusions of the two reductions. -/
theorem map_inclusion (c c' : AffineReductionChart B S hS X) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (c.map c') ≫ c'.inclusion
      = c.inclusion := by
  rw [map, (sheafifiedYonedaFF B S hS).map_preimage]
  exact (c'.isReduction.universal _ c.isReduction.algebraic c.isReduction.reduced
    c.inclusion).exists.choose_spec

/-- A morphism of the site compatible with the inclusions of two reductions of `X` is the
induced one: the universal property of a reduction determines it uniquely. -/
theorem eq_map (c c' : AffineReductionChart B S hS X) (m : c.obj ⟶ c'.obj)
    (hm : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m ≫ c'.inclusion
      = c.inclusion) : m = c.map c' :=
  (sheafifiedYonedaFF B S hS).map_injective
    ((c'.isReduction.universal _ c.isReduction.algebraic c.isReduction.reduced
      c.inclusion).unique hm (c.map_inclusion c'))

/-- **Which reduction is taken is immaterial.** The objects of the site representing two
reductions of `X` by affine objects are canonically isomorphic, by the morphisms the universal
property of a reduction induces in the two directions. -/
noncomputable def iso (c c' : AffineReductionChart B S hS X) : c.obj ≅ c'.obj where
  hom := c.map c'
  inv := c'.map c
  hom_inv_id := by
    refine (c.eq_map c _ (by
      rw [Functor.map_comp, Category.assoc, c'.map_inclusion c, c.map_inclusion c'])).trans
      (c.eq_map c (𝟙 c.obj) ?_).symm
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  inv_hom_id := by
    refine (c'.eq_map c' _ (by
      rw [Functor.map_comp, Category.assoc, c.map_inclusion c', c'.map_inclusion c])).trans
      (c'.eq_map c' (𝟙 c'.obj) ?_).symm
    rw [CategoryTheory.Functor.map_id, Category.id_comp]

end AffineReductionChart

/-- **Stacks 0DEE**, the comparison functor into the affine étale site of `X`. Let `X` be an
affine formal algebraic space over `S`. Its reduction `X_red` is the sheaf represented by an
object of the site with affine underlying scheme — this is Stacks 0AIN for an affine formal
algebraic space, in the form
`AlgebraicGeometry.FormalSpace.nonempty_affineReductionChart` — and by Stacks 0DEA the affine
étale site of `X` is the affine étale site of `X_red`. This is the functor to it from the
category of the morphisms `φ : U ⟶ X` with `U` an affine formal algebraic space and `φ`
representable by algebraic spaces and étale, sending `φ` to `U ×_X X_red`.

Nothing is carried as a hypothesis beyond `X` being an affine formal algebraic space: the
reduction and its affineness are constructed, and which reduction is chosen is immaterial by
`AlgebraicGeometry.FormalSpace.AffineReductionChart.iso`. Stacks 0DEE asserts that this functor
is an equivalence; that is
`AlgebraicGeometry.FormalSpace.reductionAffineEtaleComparison_isEquivalence`, in
`StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/EtaleSiteEquivalence.lean`. -/
@[stacks 0DEE "the comparison functor from the category of the morphisms satisfying (1) and \
(2) to the affine étale site of `X`; that it is an equivalence is \
AlgebraicGeometry.FormalSpace.reductionAffineEtaleComparison_isEquivalence"]
noncomputable def reductionAffineEtaleComparison' {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    AffineEtaleFormalCharts B S hS X ⥤
      Space.AffineEtale B S hS (yoneda.obj (affineReductionChart B S hS hX).obj) :=
  affineEtaleComparison B S hS hX _ (affineReductionChart B S hS hX).isAffine
    (affineReductionChart B S hS hX).inclusion

end AlgebraicGeometry.FormalSpace

end
