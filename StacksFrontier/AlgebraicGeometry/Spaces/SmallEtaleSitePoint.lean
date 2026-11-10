module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.CategoryTheory.Sites.Point.OfPrecoverage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A geometric point as a point of the small étale site

A geometric point `x` of an algebraic space `F` over `S` has a functor of lifts into the
étale scheme charts of `F`, `AlgebraicGeometry.Space.geometricFiber`. This functor is a point
of the small étale site of `F` in the sense of `CategoryTheory.GrothendieckTopology.Point`: its
category of elements is cofiltered and initially small, and a lift of the geometric point exists
through every covering family. The stalk at this point is the geometric stalk.

## Main definitions

* `AlgebraicGeometry.Space.etaleSitePoint` is the point of the small étale site of `F`
  determined by a geometric point of `F`.
* `AlgebraicGeometry.Space.etaleSitePointStalkIsoComponent` and
  `AlgebraicGeometry.Space.etaleSitePointStalkIso` are the comparison of its stalk with the
  geometric stalk, at one presheaf and as an isomorphism of functors.

## Main results

* `AlgebraicGeometry.Space.isCofiltered_smallEtaleNeighborhood` and
  `AlgebraicGeometry.Space.isCofiltered_geometricFiber_elements`: the small étale
  neighbourhoods of a geometric point, and equivalently the elements of its geometric fibre,
  are cofiltered.
* `AlgebraicGeometry.Space.initiallySmall_geometricFiber_elements`: those elements admit a
  weakly initial family in the universe of the schemes.
* `AlgebraicGeometry.Space.geometricFiber_jointly_surjective`: a lift of a geometric point
  into an étale chart lifts further through every chosen covering family of that chart.
* `AlgebraicGeometry.Space.etaleSitePoint_fiber`: the fibre functor of the point is the
  geometric-fibre functor, on the nose.

## References

* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The small étale neighbourhoods of a geometric point of an algebraic space form a cofiltered
category. -/
@[sga "4 IV 6.8.2" "filteredness clause"]
theorem isCofiltered_smallEtaleNeighborhood (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) : IsCofiltered (SmallEtaleNeighborhood x) :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
    (EtaleNeighborhood.ofSmallEtale hF x)
    EtaleNeighborhood.exists_smallEtaleNeighborhood_refinement

/-- The category of elements of the geometric fibre functor of a geometric point of an algebraic
space is cofiltered. -/
theorem isCofiltered_geometricFiber_elements (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) : IsCofiltered (geometricFiber B S hS F x).Elements :=
  have := isCofiltered_smallEtaleNeighborhood B S hS F hF x
  IsCofiltered.of_equivalence (neighborhoodFiberElementsEquiv B S hS F x)

/-! ### Joint surjectivity over the chosen covering families -/

/-- A morphism of schemes between the underlying schemes of two objects of the big fppf category
over `S` that factors a morphism of the category through another one is a morphism of the
category. -/
private theorem exists_hom_of_comp_eq {X Y Z : BigFppfOver B S hS} (f : Y ⟶ Z) (p : X ⟶ Z)
    (q : B.inclusion.obj X.left ⟶ B.inclusion.obj Y.left)
    (h : q ≫ B.inclusion.map f.left = B.inclusion.map p.left) : ∃ q' : X ⟶ Y, q' ≫ f = p := by
  have hq := B.inclusion.map_preimage q
  refine ⟨Over.homMk (B.inclusion.preimage q) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hq, ← f.w, Functor.map_comp, ← Category.assoc, h, ← Functor.map_comp,
      p.w]), ?_⟩
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  rw [Over.comp_left, Functor.map_comp]
  exact hq.symm ▸ h

/-- A lift of a geometric point into an étale chart of `F` lifts further through some member of
every chosen covering family of that chart. -/
theorem geometricFiber_jointly_surjective
    (x : GeometricPoint B S hS F) {U : SmallEtale B S hS F} (R : Presieve U)
    (hR : R ∈ SmallEtale.precoverage B S hS F U)
    (p : (geometricFiber B S hS F x).obj U) :
    ∃ (V : SmallEtale B S hS F) (f : V ⟶ U) (_ : R f)
      (q : (geometricFiber B S hS F x).obj V),
      (geometricFiber B S hS F x).map f q = p := by
  obtain ⟨E, rfl, hCover⟩ := hR
  obtain ⟨-, hEt⟩ := hCover
  let E' := (E.map (SmallEtale.toSchemes B S hS F)).map B.inclusion
  let T := B.inclusion.obj ((SmallEtale.toSchemes B S hS F).obj U)
  have hEt' : E'.presieve₀ ∈ Scheme.etalePrecoverage T := hEt
  have hTop : E'.sieve₀ ∈ Scheme.etaleTopology T :=
    Precoverage.mem_toGrothendieck_iff.2 (.of _ _ hEt')
  have : IsAlgClosed x.val.carrier := x.property
  have : IsSepClosed x.val.carrier := inferInstance
  let ψ : Spec (.of x.val.carrier) ⟶ T := (BigFppfOver.toScheme B S hS).map p.1
  obtain ⟨Y, g, hg, q, hq⟩ :=
    (Scheme.geometricFiber x.val.carrier).jointly_surjective E'.sieve₀ hTop ψ
  obtain ⟨i, a, hfac⟩ := Sieve.ofArrows.exists hg
  let qhom : Spec (.of x.val.carrier) ⟶ Y := q
  let q' := qhom ≫ a
  have hq' : q' ≫ E'.f i = ψ := by
    change qhom ≫ (a ≫ E'.f i) = ψ
    rw [← hfac]
    exact hq
  let fOver := (SmallEtale.toOver B S hS F).map (E.f i)
  obtain ⟨qOver, hpoint⟩ := exists_hom_of_comp_eq B S hS fOver p.val q' hq'
  refine ⟨E.X i, E.f i, E.presieve₀_f i, ⟨qOver, ?_⟩, Subtype.ext hpoint⟩
  have hchart := CostructuredArrow.w ((SmallEtale.inclusion B S hS F).map (E.f i))
  have hchartApp := congrArg (fun k => k.app (Opposite.op x.val.siteObject) qOver) hchart
  simp only [NatTrans.comp_app, types_comp_apply, yoneda_map_app] at hchartApp
  have hchartApp' : (U.obj.hom.app (Opposite.op x.val.siteObject)) (qOver ≫ fOver) =
      ((E.X i).obj.hom.app (Opposite.op x.val.siteObject)) qOver := by
    convert hchartApp using 1 <;> rfl
  rw [hpoint] at hchartApp'
  exact hchartApp'.symm.trans p.property

/-! ### Initial smallness through bounded affine charts -/

/-- The affine étale charts of an étale chart `U` of `F` whose source is small enough to be
an object of the chosen big fppf site. -/
private abbrev boundedAffineCharts (U : SmallEtale B S hS F) :=
  ObjectProperty.FullSubcategory
    (fun A : (B.inclusion.obj U.obj.left.left).AffineEtale =>
      B.Contains ((Scheme.AffineEtale.Spec _).obj A).left)

/-- A bounded affine étale chart of `U`, read as an object of the big fppf site over `S`. -/
private noncomputable def affineChartOver (U : SmallEtale B S hS F)
    (A : boundedAffineCharts B S hS F U) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk
    (((Scheme.AffineEtale.Spec _).obj A.obj).hom ≫ B.inclusion.map U.obj.left.hom) :
      (⟨((Scheme.AffineEtale.Spec _).obj A.obj).left, A.property⟩ : B.Schemes) ⟶ B.obj hS)

/-- The structure morphism of a bounded affine étale chart of `U`, as a morphism of the big
fppf site over `S`. -/
private noncomputable def affineChartToBase (U : SmallEtale B S hS F)
    (A : boundedAffineCharts B S hS F U) : affineChartOver B S hS F U A ⟶ U.obj.left :=
  Over.homMk (ObjectProperty.homMk ((Scheme.AffineEtale.Spec _).obj A.obj).hom) (by
    apply ObjectProperty.hom_ext
    rfl)

/-- The functor sending a bounded affine étale chart of `U` to the étale chart of `F` obtained
by composing with the chart `U`. -/
private noncomputable def affineChartsToSmallEtale (U : SmallEtale B S hS F) :
    boundedAffineCharts B S hS F U ⥤ SmallEtale B S hS F where
  obj A := ⟨CostructuredArrow.mk
    (yoneda.map (affineChartToBase B S hS F U A) ≫ U.obj.hom),
    etale_comp_of_scheme B S hS _ _
      ((Scheme.AffineEtale.Spec _).obj A.obj).prop U.property⟩
  map {A A'} f := by
    let m : affineChartOver B S hS F U A ⟶ affineChartOver B S hS F U A' :=
      Over.homMk (ObjectProperty.homMk ((Scheme.AffineEtale.Spec _).map f.hom).left)
        (by
          apply ObjectProperty.hom_ext
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ B.inclusion.map U.obj.left.hom)
              ((Scheme.AffineEtale.Spec _).map f.hom).w))
    have hm : m ≫ affineChartToBase B S hS F U A' = affineChartToBase B S hS F U A := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact ((Scheme.AffineEtale.Spec _).map f.hom).w
    refine ObjectProperty.homMk (CostructuredArrow.homMk m ?_)
    change yoneda.map m ≫ (yoneda.map (affineChartToBase B S hS F U A') ≫ U.obj.hom) =
      yoneda.map (affineChartToBase B S hS F U A) ≫ U.obj.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ U.obj.hom)
        (yoneda.map_comp m (affineChartToBase B S hS F U A')).symm).trans
          (congrArg (fun k => yoneda.map k ≫ U.obj.hom) hm))
  map_id A := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change ((Scheme.AffineEtale.Spec _).map (𝟙 A.obj)).left = 𝟙 _
    exact congrArg (fun k => k.left) ((Scheme.AffineEtale.Spec _).map_id A.obj)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change ((Scheme.AffineEtale.Spec _).map (f.hom ≫ g.hom)).left =
      ((Scheme.AffineEtale.Spec _).map f.hom).left ≫
        ((Scheme.AffineEtale.Spec _).map g.hom).left
    exact congrArg (fun k => k.left) ((Scheme.AffineEtale.Spec _).map_comp f.hom g.hom)

/-- Every refinement `W ⟶ U` of small étale neighbourhoods of a geometric point is itself
refined by a bounded affine étale chart of `U` carrying a lift of the point. -/
private theorem exists_affine_refinement (x : GeometricPoint B S hS F)
    (U W : SmallEtaleNeighborhood x) (f : W ⟶ U) :
    ∃ (A : boundedAffineCharts B S hS F U.chart)
      (a : (geometricFiber B S hS F x).obj
        ((affineChartsToSmallEtale B S hS F U.chart).obj A))
      (g : (affineChartsToSmallEtale B S hS F U.chart).obj A ⟶ W.chart),
      (geometricFiber B S hS F x).map g a = ⟨W.point, W.point_comp⟩ := by
  let T := BigFppfOver.toScheme B S hS
  let fw := (SmallEtale.toOver B S hS F).map f.hom
  let w : Spec (.of x.val.carrier) ⟶ T.obj W.chart.obj.left := T.map W.point
  have : Etale (T.map fw) :=
    etale_of_comp_etale_chart B S hS W.chart.property U.chart.property
      (CostructuredArrow.w f.hom.hom)
  obtain ⟨R, j, hj, hrange, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := w default) (U := ⊤) (by simp)
  have : _root_.AlgebraicGeometry.IsOpenImmersion j := hj
  have hw : Set.range w ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    simpa only [Subsingleton.elim a default] using hrange
  let q := _root_.AlgebraicGeometry.IsOpenImmersion.lift j w hw
  have hq : q ≫ j = w := _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac j w hw
  let A₀ := Scheme.AffineEtale.mk (j ≫ T.map fw)
  have hsize : B.Contains (Spec R) :=
    Scheme.size_lt_of_isOpenImmersion j W.chart.obj.left.left.property
  let A : boundedAffineCharts B S hS F U.chart := ⟨A₀, hsize⟩
  let V := affineChartOver B S hS F U.chart A
  let jOver : V ⟶ W.chart.obj.left := Over.homMk (ObjectProperty.homMk j) (by
    apply ObjectProperty.hom_ext
    change j ≫ B.inclusion.map W.chart.obj.left.hom =
      (j ≫ T.map fw) ≫ B.inclusion.map U.chart.obj.left.hom
    rw [Category.assoc]
    congr 1
    exact (congrArg B.inclusion.map fw.w).symm)
  have hjOver : jOver ≫ fw = affineChartToBase B S hS F U.chart A := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    rfl
  let g : (affineChartsToSmallEtale B S hS F U.chart).obj A ⟶ W.chart :=
    ObjectProperty.homMk (CostructuredArrow.homMk jOver (by
      change yoneda.map jOver ≫ W.chart.obj.hom =
        yoneda.map (affineChartToBase B S hS F U.chart A) ≫ U.chart.obj.hom
      rw [← hjOver, Functor.map_comp, Category.assoc]
      exact congrArg (yoneda.map jOver ≫ ·) (CostructuredArrow.w f.hom.hom).symm))
  obtain ⟨qOver, hqOver⟩ := exists_hom_of_comp_eq B S hS jOver W.point q hq
  have hpoint : ((affineChartsToSmallEtale B S hS F U.chart).obj A).obj.hom.app
      (Opposite.op x.val.siteObject) qOver = x.val.value := by
    rw [← CostructuredArrow.w g.hom]
    change W.chart.obj.hom.app (Opposite.op x.val.siteObject) (qOver ≫ jOver) = _
    rw [hqOver]
    exact W.point_comp
  exact ⟨A, ⟨qOver, hpoint⟩, g, Subtype.ext hqOver⟩

/-- The category of elements of the geometric fibre functor of a geometric point of an algebraic
space is initially small in the universe of the schemes. -/
theorem initiallySmall_geometricFiber_elements (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) :
    InitiallySmall.{u} (geometricFiber B S hS F x).Elements := by
  have hcof := isCofiltered_smallEtaleNeighborhood B S hS F hF x
  have := isCofiltered_geometricFiber_elements B S hS F hF x
  obtain ⟨U⟩ := hcof.nonempty
  have : EssentiallySmall.{u} (boundedAffineCharts B S hS F U.chart) :=
    essentiallySmall_of_fully_faithful
      (ObjectProperty.ι (fun A : (B.inclusion.obj U.chart.obj.left.left).AffineEtale =>
        B.Contains ((Scheme.AffineEtale.Spec _).obj A).left))
  apply initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
    (Functor.Elements.precomp (affineChartsToSmallEtale B S hS F U.chart)
      (geometricFiber B S hS F x)).essImage
  rintro @⟨V, p⟩
  let V' : SmallEtaleNeighborhood x := ⟨V, p.1, p.2⟩
  obtain ⟨W, f, g, -⟩ := IsCofilteredOrEmpty.cone_objs U V'
  obtain ⟨A, a, j, hj⟩ := exists_affine_refinement B S hS F x U W f
  refine ⟨_, ⟨Functor.elementsMk _ A a, ⟨Iso.refl _⟩⟩, ⟨⟨j ≫ g.hom, ?_⟩⟩⟩
  change (geometricFiber B S hS F x).map g.hom
    ((geometricFiber B S hS F x).map j a) = p
  rw [hj]
  exact Subtype.ext g.point_comp

/-! ### The point of the site -/

/-- The point of the small étale site of an algebraic space determined by
a geometric point of it: its fibre functor is the functor of lifts of the geometric point
into the étale scheme charts. -/
@[stacks 04K0 "the point of the site"]
noncomputable def etaleSitePoint (x : GeometricPoint B S hS F)
    (hF : IsAlgebraicSpace B S hS F) : (SmallEtale.topology B S hS F).Point.{u} :=
  have := isCofiltered_geometricFiber_elements B S hS F hF x
  have := initiallySmall_geometricFiber_elements B S hS F hF x
  GrothendieckTopology.Point.ofPrecoverage (geometricFiber B S hS F x)
    (fun R hR p => geometricFiber_jointly_surjective B S hS F x R hR p)

/-- The fibre functor of the point of the small étale site determined by a geometric point is
the geometric fibre functor. -/
@[simp, stacks 04K0 "the fibre functor"]
theorem etaleSitePoint_fiber (x : GeometricPoint B S hS F)
    (hF : IsAlgebraicSpace B S hS F) :
    (etaleSitePoint B S hS F x hF).fiber = geometricFiber B S hS F x := rfl

/-- The stalk of a presheaf of sets at the point of the small étale site determined by a
geometric point is isomorphic to its geometric stalk. -/
noncomputable def etaleSitePointStalkIsoComponent (x : GeometricPoint B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type (u + 1)) :
    ((etaleSitePoint B S hS F x hF).presheafFiber (A := Type (u + 1))).obj P ≅
      stalkSet x P :=
  Equiv.toIso ((Types.colimitEquivColimitType
    ((Functor.Elements.π (geometricFiber B S hS F x)).op ⋙ P)).trans
      (fiberColimitEquiv B S hS F x P))

/-- The stalk comparison sends the germ at a lift of the geometric point of a section over
an étale chart to the germ of that section over the corresponding neighbourhood. -/
theorem etaleSitePointStalkIsoComponent_toPresheafFiber (x : GeometricPoint B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type (u + 1))
    (U : SmallEtale B S hS F) (p : GeometricFiber B S hS F x U) (a : P.obj (Opposite.op U)) :
    (etaleSitePointStalkIsoComponent B S hS F x hF P).hom
        ((etaleSitePoint B S hS F x hF).toPresheafFiber U p P a) =
      (SmallEtaleNeighborhood.sections (x := x) P).ιColimitType
        (Opposite.op ⟨U, p.1, p.2⟩) a := by
  let D := (Functor.Elements.π (geometricFiber B S hS F x)).op ⋙ P
  change fiberColimitEquiv B S hS F x P
    ((Types.colimitEquivColimitType D)
      (colimit.ι D (Opposite.op ((geometricFiber B S hS F x).elementsMk U p)) a)) = _
  exact (congrArg (fiberColimitEquiv B S hS F x P)
    (Types.colimitEquivColimitType_apply D
      (Opposite.op ((geometricFiber B S hS F x).elementsMk U p)) a)).trans rfl

/-- The stalk at the point of the small étale site determined by a geometric point is
isomorphic to the geometric stalk, naturally in the presheaf. -/
@[stacks 04K0 "the stalk comparison"]
noncomputable def etaleSitePointStalkIso (x : GeometricPoint B S hS F)
    (hF : IsAlgebraicSpace B S hS F) :
    (etaleSitePoint B S hS F x hF).presheafFiber (A := Type (u + 1)) ≅
      stalkSetFunctor x :=
  NatIso.ofComponents (fun P => etaleSitePointStalkIsoComponent B S hS F x hF P) (by
    intro P Q α
    apply (etaleSitePoint B S hS F x hF).presheafFiber_hom_ext
    intro U p
    apply ConcreteCategory.hom_ext
    intro a
    have hnat := ConcreteCategory.congr_hom
      ((etaleSitePoint B S hS F x hF).toPresheafFiber_naturality α U p) a
    simp only [types_comp_apply] at hnat
    change (etaleSitePointStalkIsoComponent B S hS F x hF Q).hom
        ((etaleSitePoint B S hS F x hF).presheafFiber.map α
          ((etaleSitePoint B S hS F x hF).toPresheafFiber U p P a)) =
      (stalkSetFunctor x).map α
        ((etaleSitePointStalkIsoComponent B S hS F x hF P).hom
          ((etaleSitePoint B S hS F x hF).toPresheafFiber U p P a))
    rw [hnat, etaleSitePointStalkIsoComponent_toPresheafFiber B S hS F x hF Q U
        (show GeometricFiber B S hS F x U from p),
      etaleSitePointStalkIsoComponent_toPresheafFiber B S hS F x hF P U
        (show GeometricFiber B S hS F x U from p)]
    rfl)

end AlgebraicGeometry.Space

end
