module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp

/-!
# The étale local ring is unchanged by an étale morphism

Let `φ : Y ⟶ X` be an étale morphism of algebraic spaces over `S` and let `ȳ` be a geometric
point of `Y`, with image `x̄ = φ ∘ ȳ`.  The étale local ring of `Y` at `ȳ` is canonically
isomorphic to the étale local ring of `X` at `x̄`.  Specialized to the structure morphism of an
étale scheme chart this is the first equality of Stacks 04KF: for an étale neighbourhood
`(U, ū)` of `x̄` with `U` a scheme, `𝒪_{U, ū} = 𝒪_{X, x̄}`.

The comparison is a cofinality statement.  The étale local ring at a geometric point is a
colimit over the small étale neighbourhoods of that point, and postcomposition with `φ` is a
functor from the neighbourhoods of `ȳ` to those of `x̄` along which the two diagrams of
sections agree *on the nose*, because postcomposition leaves the underlying object of the big
fppf site — hence the ring of global regular functions — unchanged.  So the only thing to
prove is that the postcomposition functor is initial, and then the colimit comparison of
`CategoryTheory.Functor.Final.colimitIso` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.EtaleNeighborhood.postcomp` and
  `AlgebraicGeometry.Space.SmallEtaleNeighborhood.postcomp` are postcomposition with `φ` on
  the general étale neighbourhoods of Stacks 04JV and on the small étale neighbourhoods of
  Stacks 04JY.
* `AlgebraicGeometry.Space.chartPresheafGeometricPoint` reads the lift of a geometric point
  carried by a small étale neighbourhood as a geometric point of the presheaf represented by the
  chart.

## Main results

* `AlgebraicGeometry.Space.EtaleNeighborhood.initial_ofSmallEtale`: the comparison from the
  small étale neighbourhoods to all étale neighbourhoods is initial.
* `AlgebraicGeometry.Space.EtaleNeighborhood.initial_postcomp` and
  `AlgebraicGeometry.Space.SmallEtaleNeighborhood.initial_postcomp`: postcomposition with an
  étale morphism is initial on étale neighbourhoods, and on small étale neighbourhoods.
* `AlgebraicGeometry.Space.etaleLocalRingIsoOfIsEtale`: the étale local ring is unchanged by
  an étale morphism of algebraic spaces.
* `AlgebraicGeometry.Space.etaleLocalRingChartIso` is the first equality of Stacks 04KF: the
  étale local ring of an algebraic space at a geometric point is the étale local ring of any
  étale scheme chart at a lift of that point.

## Implementation notes

Initiality is proved for the *general* étale neighbourhoods first and transported to the small
ones, rather than the other way round.  The general neighbourhoods are closed under the two
constructions the criterion
`CategoryTheory.Functor.initial_of_exists_of_isCofiltered` asks for — a neighbourhood of `x̄`
with a map to a given one and to `Y`, and a refinement equalizing two maps — because
cofilteredness of the general neighbourhoods
(`AlgebraicGeometry.Space.EtaleNeighborhood.instIsCofiltered`) produces both, and Stacks 03FV
(`AlgebraicGeometry.Space.isEtale_of_isEtale_over`) turns the resulting map to `Y` into an
étale structure morphism, which is exactly what makes the result a neighbourhood of `ȳ`.  No
fibre product is constructed by hand here.

Transporting to the small neighbourhoods uses that
`AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale` is fully faithful and initial, that
the square of the two postcomposition functors with the two comparisons *commutes strictly*,
and `CategoryTheory.Functor.initial_of_comp_full_faithful`.  Strict commutativity holds
because `AlgebraicGeometry.Space.smallEtalePostcomp` changes nothing but the structure arrow
of a chart, and the comparison to general neighbourhoods changes nothing at all.

The same strictness is what makes the diagrams of sections literally equal, so no
`CategoryTheory.eqToHom` enters the colimit comparison beyond the single
`CategoryTheory.eqToIso` identifying `φ ∘ ū` with the given geometric point in the chart
statement; there the two geometric points differ only in their section, and they agree by the
compatibility `point_comp` carried by the neighbourhood.

## References

* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04JV](https://stacks.math.columbia.edu/tag/04JV)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The small étale neighbourhoods are initial among all étale neighbourhoods -/

/-- The comparison from the small étale neighbourhoods of a geometric point to all its étale
neighbourhoods is initial: it is fully faithful into a cofiltered category every object of
which is refined by one in its image, which is Stacks 04JW. -/
theorem EtaleNeighborhood.initial_ofSmallEtale
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) :
    (EtaleNeighborhood.ofSmallEtale hF x).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
    (EtaleNeighborhood.ofSmallEtale hF x)
    (fun U => by
      obtain ⟨V, hV⟩ := EtaleNeighborhood.exists_smallEtaleNeighborhood_refinement U
      exact ⟨V, hV⟩)

/-! ### Postcomposition on the general étale neighbourhoods -/

/-- Postcomposition with an étale morphism `φ : Y ⟶ X` of algebraic spaces over `S`, as a
functor from the étale neighbourhoods of a geometric point `ȳ` of `Y` to the étale
neighbourhoods of its image in `X`.  Only the structure morphism to the base changes: the
neighbourhood, and the lift of the geometric point to it, are unchanged. -/
def EtaleNeighborhood.postcomp
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (φ : Y ⟶ X) (hφ : IsEtale B S hS φ)
    (y : GeometricPoint B S hS Y) :
    EtaleNeighborhood B S hS Y hY y ⥤
      EtaleNeighborhood B S hS X hX (geometricPointMap φ y) where
  obj A :=
    { space := A.space
      isAlgebraicSpace := A.isAlgebraicSpace
      toBase := A.toBase ≫ φ
      etale_toBase := isEtale_comp B S hS A.etale_toBase hφ
      point := A.point
      point_comp := congrArg (φ.app (Opposite.op y.val.siteObject)) A.point_comp }
  map f :=
    { hom := f.hom
      over := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) f.over)
      point_comp := f.point_comp }
  map_id _ := EtaleNeighborhood.Hom.ext rfl
  map_comp _ _ := EtaleNeighborhood.Hom.ext rfl

/-- The source of an étale morphism `φ : Y ⟶ X` of algebraic spaces over `S`, read as an étale
neighbourhood of the image in `X` of a geometric point of `Y`.  It is the terminal object of
the étale neighbourhoods of that geometric point *in* `Y`, pushed to `X`. -/
def EtaleNeighborhood.ofSource
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (φ : Y ⟶ X) (hφ : IsEtale B S hS φ)
    (y : GeometricPoint B S hS Y) :
    EtaleNeighborhood B S hS X hX (geometricPointMap φ y) where
  space := Y
  isAlgebraicSpace := hY
  toBase := φ
  etale_toBase := hφ
  point := y.val.value
  point_comp := rfl

/-- A neighbourhood of the image of `ȳ` in `X` with a map `g` to `Y` compatible with the
structure morphisms and with the lifts is a neighbourhood of `ȳ`, by Stacks 03FV. -/
private def EtaleNeighborhood.ofHomToSource
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (φ : Y ⟶ X) (hφ : IsEtale B S hS φ)
    (y : GeometricPoint B S hS Y) (W : EtaleNeighborhood B S hS X hX (geometricPointMap φ y))
    (g : W.space ⟶ Y) (hg : g ≫ φ = W.toBase)
    (hp : g.app (Opposite.op y.val.siteObject) W.point = y.val.value) :
    EtaleNeighborhood B S hS Y hY y where
  space := W.space
  isAlgebraicSpace := W.isAlgebraicSpace
  toBase := g
  etale_toBase := isEtale_of_isEtale_over B S hS W.isAlgebraicSpace hY hX g W.toBase φ
    W.etale_toBase hφ hg
  point := W.point
  point_comp := hp

/-- Postcomposition with an étale morphism is initial on étale neighbourhoods.

Given a neighbourhood `M` of the image point, cofilteredness of the étale neighbourhoods of
that point gives a common refinement `W` of `M` and of `Y` itself; the map `W ⟶ Y` is étale by
Stacks 03FV, so `W` is a neighbourhood of `ȳ` whose image maps to `M`.  Two maps out of the
image of a neighbourhood are equalized the same way, by the refinement that cofilteredness
produces for them. -/
theorem EtaleNeighborhood.initial_postcomp
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (φ : Y ⟶ X) (hφ : IsEtale B S hS φ)
    (y : GeometricPoint B S hS Y) :
    (EtaleNeighborhood.postcomp B S hS hY hX φ hφ y).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered _ (fun M => ?_) (fun {_ A} s s' => ?_)
  · obtain ⟨W, a, b, -⟩ :=
      IsCofilteredOrEmpty.cone_objs M (EtaleNeighborhood.ofSource B S hS hY hX φ hφ y)
    exact ⟨EtaleNeighborhood.ofHomToSource B S hS hY hX φ hφ y W b.hom b.over b.point_comp,
           ⟨{ hom := a.hom
              over := a.over.trans b.over.symm
              point_comp := a.point_comp }⟩⟩
  · obtain ⟨W, e, he⟩ := IsCofilteredOrEmpty.cone_maps s s'
    exact ⟨EtaleNeighborhood.ofHomToSource B S hS hY hX φ hφ y W (e.hom ≫ A.toBase)
             ((Category.assoc _ _ _).trans e.over)
             ((congrArg (A.toBase.app (Opposite.op y.val.siteObject)) e.point_comp).trans
               A.point_comp),
           { hom := e.hom
             over := rfl
             point_comp := e.point_comp },
           EtaleNeighborhood.Hom.ext
             (congrArg EtaleNeighborhood.Hom.hom he :
               e.hom ≫ s.hom = e.hom ≫ s'.hom)⟩

/-! ### Postcomposition on the small étale neighbourhoods -/

/-- Postcomposition with an étale morphism `φ : Y ⟶ X` of algebraic spaces over `S`, as a
functor from the small étale neighbourhoods of a geometric point `ȳ` of `Y` to the small étale
neighbourhoods of its image in `X`.  On charts it is
`AlgebraicGeometry.Space.smallEtalePostcomp`, and the lift of the geometric point is
unchanged. -/
def SmallEtaleNeighborhood.postcomp {Y X : AlgebraicSpaces B S hS} (φ : Y ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (y : GeometricPoint B S hS Y.1) :
    SmallEtaleNeighborhood y ⥤ SmallEtaleNeighborhood (geometricPointMap φ.hom y) where
  obj A :=
    { chart := (smallEtalePostcomp B S hS φ hφ).obj A.chart
      point := A.point
      point_comp :=
        congrArg (φ.hom.app (Opposite.op y.val.siteObject)) A.point_comp }
  map f :=
    { hom := (smallEtalePostcomp B S hS φ hφ).map f.hom
      point_comp := f.point_comp }
  map_id A := SmallEtaleNeighborhood.Hom.ext
    ((smallEtalePostcomp B S hS φ hφ).map_id A.chart)
  map_comp f g := SmallEtaleNeighborhood.Hom.ext
    ((smallEtalePostcomp B S hS φ hφ).map_comp f.hom g.hom)

/-- The square of the two postcomposition functors and the two comparisons with the general
étale neighbourhoods commutes strictly: postcomposition changes nothing but the structure
arrow of a chart, and the comparison changes nothing at all. -/
theorem SmallEtaleNeighborhood.postcomp_comp_ofSmallEtale {Y X : AlgebraicSpaces B S hS}
    (φ : Y ⟶ X) (hφ : IsEtale B S hS φ.hom) (y : GeometricPoint B S hS Y.1) :
    SmallEtaleNeighborhood.postcomp B S hS φ hφ y ⋙
        EtaleNeighborhood.ofSmallEtale X.2 (geometricPointMap φ.hom y) =
      EtaleNeighborhood.ofSmallEtale Y.2 y ⋙
        EtaleNeighborhood.postcomp B S hS Y.2 X.2 φ.hom hφ y :=
  rfl

/-- Postcomposition with an étale morphism is initial on small étale neighbourhoods: it is so
after composing with the fully faithful comparison to the general étale neighbourhoods, by
`AlgebraicGeometry.Space.EtaleNeighborhood.initial_postcomp` and
`AlgebraicGeometry.Space.EtaleNeighborhood.initial_ofSmallEtale`. -/
theorem SmallEtaleNeighborhood.initial_postcomp {Y X : AlgebraicSpaces B S hS} (φ : Y ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (y : GeometricPoint B S hS Y.1) :
    (SmallEtaleNeighborhood.postcomp B S hS φ hφ y).Initial := by
  have h₁ := EtaleNeighborhood.initial_ofSmallEtale B S hS Y.2 y
  have h₂ := EtaleNeighborhood.initial_postcomp B S hS Y.2 X.2 φ.hom hφ y
  have h₃ : (SmallEtaleNeighborhood.postcomp B S hS φ hφ y ⋙
      EtaleNeighborhood.ofSmallEtale X.2 (geometricPointMap φ.hom y)).Initial := by
    rw [SmallEtaleNeighborhood.postcomp_comp_ofSmallEtale]
    infer_instance
  exact Functor.initial_of_comp_full_faithful _
    (EtaleNeighborhood.ofSmallEtale X.2 (geometricPointMap φ.hom y))

/-! ### The étale local ring is unchanged -/

/-- Postcomposition carries the diagram of sections of the structure presheaf of `X` to the
diagram of sections of the structure presheaf of `Y`, on the nose. -/
theorem SmallEtaleNeighborhood.postcomp_op_comp_sections {Y X : AlgebraicSpaces B S hS}
    (φ : Y ⟶ X) (hφ : IsEtale B S hS φ.hom) (y : GeometricPoint B S hS Y.1) :
    (SmallEtaleNeighborhood.postcomp B S hS φ hφ y).op ⋙
        SmallEtaleNeighborhood.sections (x := geometricPointMap φ.hom y)
          (liftedStructurePresheaf B S hS X.1) =
      SmallEtaleNeighborhood.sections (x := y) (liftedStructurePresheaf B S hS Y.1) :=
  rfl

/-- The étale local ring of an algebraic space at a geometric point is unchanged by an étale
morphism: the stalk of the structure sheaf of `Y` at `ȳ` is the stalk of the structure sheaf of
`X` at the image of `ȳ`.

This is the first equality of Stacks 04KF, before the restriction to scheme charts; it is also
the remark opening the proof of Stacks 08IQ. -/
noncomputable def etaleLocalRingIsoOfIsEtale {Y X : AlgebraicSpaces B S hS} (φ : Y ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (y : GeometricPoint B S hS Y.1) :
    etaleLocalRing B S hS Y.1 y ≅
      etaleLocalRing B S hS X.1 (geometricPointMap φ.hom y) :=
  have := SmallEtaleNeighborhood.initial_postcomp B S hS φ hφ y
  HasColimit.isoOfNatIso
      (eqToIso (SmallEtaleNeighborhood.postcomp_op_comp_sections B S hS φ hφ y).symm) ≪≫
    Functor.Final.colimitIso (SmallEtaleNeighborhood.postcomp B S hS φ hφ y).op
      (SmallEtaleNeighborhood.sections (x := geometricPointMap φ.hom y)
        (liftedStructurePresheaf B S hS X.1))

/-! ### Stacks 04KF, the first equality -/

/-- The lift of a geometric point carried by a small étale neighbourhood, read as a geometric
point of the presheaf represented by the chart.  Its field, and its structure morphism to the
base, are those of the original point; only the section changes.

`AlgebraicGeometry.Space.chartGeometricPoint` is the unrelated construction which reads the same
lift as a geometric point of the *scheme* underlying the chart. -/
noncomputable def chartPresheafGeometricPoint {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : GeometricPoint B S hS F) (N : SmallEtaleNeighborhood x) :
    GeometricPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj N.chart)) :=
  ⟨{ x.val with value := N.point }, x.property⟩

/-- The image of `AlgebraicGeometry.Space.chartPresheafGeometricPoint` under the structure
morphism of the chart is the original geometric point: that is the compatibility `point_comp`
carried by the neighbourhood. -/
theorem geometricPointMap_chartPresheafGeometricPoint {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : GeometricPoint B S hS F) (N : SmallEtaleNeighborhood x) :
    geometricPointMap N.chart.obj.hom (chartPresheafGeometricPoint B S hS x N) = x :=
  Subtype.ext
    (congrArg (fun v => ({ x.val with value := v } : FieldValuedPoint B S hS F))
      N.point_comp)

/-- **Stacks 04KF, first equality.** Let `X` be an algebraic space over `S`, let `x̄` be a
geometric point of `X` and let `(U, ū)` be an étale neighbourhood of `x̄` with `U` a scheme.
Then the étale local ring of `U` at `ū` is the étale local ring of `X` at `x̄`.

Only the first of the two equalities of Stacks 04KF is proved here.  The second,
`𝒪_{U, ū} = 𝒪_{U, u}^{sh}`, is Étale Cohomology, Lemma 04HX, which is not in the library. -/
@[stacks 04KF "O_{X, xbar} = O_{U, ubar}"]
noncomputable def etaleLocalRingChartIso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F)
    (N : SmallEtaleNeighborhood x) :
    etaleLocalRing B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj N.chart))
        (chartPresheafGeometricPoint B S hS x N) ≅ etaleLocalRing B S hS F x :=
  etaleLocalRingIsoOfIsEtale B S hS
      (Y := ⟨yoneda.obj ((SmallEtale.toOver B S hS F).obj N.chart),
        isAlgebraicSpace_yoneda B S hS _⟩)
      (X := ⟨F, hF⟩) (ObjectProperty.homMk N.chart.obj.hom)
      (isEtale_of_presheaf_etale B S hS N.chart.property)
      (chartPresheafGeometricPoint B S hS x N) ≪≫
    eqToIso (congrArg (fun z => etaleLocalRing B S hS F z)
      (geometricPointMap_chartPresheafGeometricPoint B S hS x N))

end AlgebraicGeometry.Space

end
