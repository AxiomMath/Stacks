module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChangeOpen
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryHomGluing
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# The space of points of the stack of curves

The points `|Curves|` of the stack of curves are the classes of its field-valued points
(Stacks 04XG), with the topology of Stacks 04Y8: the finest one for which every chart by an
algebraic space is continuous on points. Both are defined for every category fibred in groupoids
over the big fppf site, and are read here on the small model `AlgebraicGeometry.curvesSmall` of
the stack of curves, whose morphisms live in the universe of the site. For a property `P` of
families of curves, `|Curves^P| ⊆ |Curves|` is the set of points represented by a field-valued
point whose family of curves has `P`; when `Curves^P` is an open substack this is its image on
points.

For `P` with condition (o) of Stacks 0E0E:

* membership of a point in `|Curves^P|` does not depend on the representative: `P` passes to
  the common refinement of two representatives, and back from it, because the open of the base
  of a family over a one-point scheme cut out by `P` is everything as soon as it is nonempty;
* `|Curves^P|` is open: along a chart by an algebraic space and a scheme-valued point `U` of it,
  the preimage of `|Curves^P|` is the open subscheme of `U` of condition (o).

Finally, a family of curves over a scheme `V` turns specializations of points of `V` into
specializations in `|Curves|`, the chart of the stack of curves by `V` it classifies being
continuous (Stacks 04XL).

## Main definitions

* `AlgebraicGeometry.CurvesPoints`: the topological space `|Curves|`.
* `AlgebraicGeometry.curvesPointSet`: the subset `|Curves^P|` of points of the substack cut out
  by a property `P` of families of curves.

## Main results

* `AlgebraicGeometry.pointClass_mem_curvesPointSet_iff`: for `P` with condition (o), a
  field-valued point represents a point of `|Curves^P|` exactly when its family has `P`.
* `AlgebraicGeometry.isOpen_curvesPointSet`: for `P` with condition (o), `|Curves^P|` is open.
* `AlgebraicGeometry.pointClass_specializes_of_isHomLift`: specializations along a family of
  curves.

## References

* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04Y8](https://stacks.math.columbia.edu/tag/04Y8)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The family of curves classified by an object of the small model of the stack of curves. -/
abbrev curvesSmallFamily : (curvesSmall B hZ).val.obj ⥤ CurveFamily B hZ :=
  (curvesSmallEquivalenceOver B hZ).inv.functor

/-- The space `|Curves|` of points of the stack of curves (Stacks 04XG), read on its small model
`AlgebraicGeometry.curvesSmall`. -/
abbrev CurvesPoints : Type (u + 1) :=
  Stack.points B integerBase hZ (curvesSmall B hZ).val (curvesSmall B hZ).property

/-- The topology of Stacks 04Y8 on `|Curves|`. -/
instance : TopologicalSpace (CurvesPoints B hZ) :=
  Stack.pointTopology B integerBase hZ (curvesSmall B hZ)

/-- The image `|Curves^P| ⊆ |Curves|` of the points of the substack of families of curves with
the property `P`: the points represented by a field-valued point whose family has `P`. -/
def curvesPointSet (P : ObjectProperty (CurveFamily B hZ)) : Set (CurvesPoints B hZ) :=
  {x | ∃ p : Stack.FieldValuedPoint B integerBase hZ (curvesSmall B hZ).val,
    P ((curvesSmallFamily B hZ).obj p.obj) ∧
      Stack.pointClass B integerBase hZ _ (curvesSmall B hZ).property p = x}

variable {B hZ}

/-- `|Curves^P| ⊆ |Curves^Q|` when `P` implies `Q`. -/
theorem curvesPointSet_mono {P Q : ObjectProperty (CurveFamily B hZ)} (h : ∀ F, P F → Q F) :
    curvesPointSet B hZ P ⊆ curvesPointSet B hZ Q := by
  rintro x ⟨p, hp, rfl⟩
  exact ⟨p, h _ hp, rfl⟩

/-- The base of the family of curves classified by the object of a field-valued point of the
small model is a one-point scheme. -/
theorem subsingleton_base_curvesSmallFamily
    (p : Stack.FieldValuedPoint B integerBase hZ (curvesSmall B hZ).val) :
    Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj
      ((curvesSmallFamily B hZ).obj p.obj).base) := by
  rw [show ((curvesSmallFamily B hZ).obj p.obj).base = p.base from p.over]
  exact p.isSpec.hom.homeomorph.injective.subsingleton

/-- The base of the family of curves classified by the object of a field-valued point of the
small model is nonempty. -/
theorem nonempty_base_curvesSmallFamily
    (p : Stack.FieldValuedPoint B integerBase hZ (curvesSmall B hZ).val) :
    Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj
      ((curvesSmallFamily B hZ).obj p.obj).base) := by
  rw [show ((curvesSmallFamily B hZ).obj p.obj).base = p.base from p.over]
  exact ⟨p.isSpec.inv.base (IsLocalRing.closedPoint _)⟩

/-- **Descent of a property with condition (o) along a morphism to a family over a point.** Let
`P` satisfy condition (o) of Stacks 0E0E and let `F ⟶ G` be a morphism of families of curves
whose target lies over a one-point scheme and whose source has a nonempty base. If `F` has `P`,
so does `G`: the open of the base of `G` cut out by `P` receives the base of `F`, hence is
everything. -/
theorem IsOpenCurvesLocus.prop_of_hom_of_subsingleton {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) {F G : CurveFamily B hZ} (φ : F ⟶ G)
    (hG : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj G.base))
    (hF : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj F.base)) (hPF : P F) : P G := by
  obtain ⟨W, hW, hchar⟩ := hP G
  have h1 := (Space.factorsThrough_openSubspace_iff_points B integerBase hZ
    (schemeSpace G.base).property (schemeSpace F.base).property W hW _).1 ((hchar F φ).1 hPF)
  refine (hchar G (𝟙 G)).2 ((Space.factorsThrough_openSubspace_iff_points B integerBase hZ
    (schemeSpace G.base).property (schemeSpace G.base).property W hW _).2 ?_)
  rintro x -
  obtain ⟨s⟩ := hF
  obtain ⟨y, -⟩ := Space.surjective_pointsToScheme B integerBase hZ F.base s
  rw [(Space.injective_pointsToScheme B integerBase hZ G.base).subsingleton.elim x
    (Space.pointsMap B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom y)]
  exact h1 ⟨y, rfl⟩

/-- **The points of `|Curves^P|`, for `P` with condition (o).** A field-valued point represents a
point of `|Curves^P|` exactly when its family of curves has `P`: two field-valued points
representing the same point have a common refinement, and `P` passes to it and back. -/
theorem pointClass_mem_curvesPointSet_iff {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P)
    (p : Stack.FieldValuedPoint B integerBase hZ (curvesSmall B hZ).val) :
    Stack.pointClass B integerBase hZ _ (curvesSmall B hZ).property p ∈
        curvesPointSet B hZ P ↔ P ((curvesSmallFamily B hZ).obj p.obj) := by
  refine ⟨fun ⟨q, hq, hqp⟩ => ?_, fun h => ⟨p, h, rfl⟩⟩
  obtain ⟨r, ⟨a⟩, ⟨b⟩⟩ :=
    (Stack.class_eq_class_iff_hasCommonExtension B integerBase hZ _ _ q p).1 hqp
  exact hP.prop_of_hom_of_subsingleton ((curvesSmallFamily B hZ).map b)
    (subsingleton_base_curvesSmallFamily p) (nonempty_base_curvesSmallFamily r)
    (hP.prop_of_hom ((curvesSmallFamily B hZ).map a) hq)

/-! ### Openness of `|Curves^P|` -/

section Openness

variable {F : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}

/-- A morphism `a : U ⟶ F` from a scheme of the site to a presheaf, read as a functor from the
big fppf site of `U` to the category of elements of `F`: an object `T ⟶ U` goes to the
restriction of `a` along it. -/
def siteToElements {U : BigFppfOver B integerBase hZ} (a : yoneda.obj U ⟶ F) :
    BigFppfOver B U.left.1 U.left.2 ⥤ (Stack.fibredCategory B integerBase hZ F).val.obj where
  obj T := ⟨(Over.map U.hom).obj T, Discrete.mk (a.app (op _) (Over.homMk T.hom))⟩
  map {T T'} φ :=
    { base := (Over.map U.hom).map φ
      fiber := Discrete.eqToHom (by
        have hn := congrFun (congrArg (fun q => TypeCat.homEquiv q)
          (a.naturality ((Over.map U.hom).map φ).op)) (Over.homMk T'.hom)
        simp only [TypeCat.homEquiv_apply, ConcreteCategory.comp_apply] at hn
        refine Eq.trans ?_ hn
        have he : ((Over.map U.hom).map φ ≫ Over.homMk T'.hom (by simp) :
            (Over.map U.hom).obj T ⟶ U) = Over.homMk T.hom (by simp) := by
          ext; simp [Over.w φ]
        change _ = (a.app (op ((Over.map U.hom).obj T))) ((Over.map U.hom).map φ ≫ _)
        rw [he]) }
  map_id T := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (by simp; rfl) ?_
    apply Discrete.hom_eq
  map_comp f₁ f₂ := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (by simp; rfl) ?_
    apply Discrete.hom_eq

/-- The families of curves over the big fppf site of `U` classified by a chart `f` of the stack of
curves by `F` along a scheme-valued point `a` of `F`. -/
abbrev chartCurveFamilies
    (f : (Stack.fibredCategory B integerBase hZ F).val ⥤ᵇ (curvesSmall B hZ).val)
    {U : BigFppfOver B integerBase hZ} (a : yoneda.obj U ⟶ F) :
    BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ :=
  siteToElements a ⋙ f.toFunctor ⋙ curvesSmallFamily B hZ

/-- The families of curves of `AlgebraicGeometry.chartCurveFamilies` lie over the big fppf site
of `U`. -/
theorem chartCurveFamilies_comp_projection
    (f : (Stack.fibredCategory B integerBase hZ F).val ⥤ᵇ (curvesSmall B hZ).val)
    {U : BigFppfOver B integerBase hZ} (a : yoneda.obj U ⟶ F) :
    chartCurveFamilies f a ⋙ curvesProjectionOver B hZ = Over.map U.hom :=
  (congrArg (fun G => siteToElements a ⋙ f.toFunctor ⋙ G)
    (curvesSmallEquivalenceOver B hZ).inv.w).trans
    ((congrArg (fun G => siteToElements a ⋙ G) f.w).trans rfl)

/-- A morphism from a field-valued point of the site of `U` factors through an open subscheme
`V ⟶ U` exactly when its point lies in the image of `V`. -/
theorem nonempty_hom_iff_schemePoint_mem_range {U : BigFppfOver B integerBase hZ}
    (p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U))
    (V : BigFppfOver B U.left.1 U.left.2) (hV : IsOpenImmersion V.hom.hom) :
    Nonempty ((Over.mk p.value.left : BigFppfOver B U.left.1 U.left.2) ⟶ V) ↔
      Space.schemePoint B integerBase hZ U p ∈ Set.range V.hom.hom.base := by
  constructor
  · rintro ⟨t⟩
    refine ⟨t.left.hom.base (IsLocalRing.closedPoint p.carrier), ?_⟩
    have ht' : t.left.hom ≫ V.hom.hom = p.value.left.hom := congrArg (fun m => m.hom) (Over.w t)
    show (t.left.hom ≫ V.hom.hom).base _ = _
    rw [ht']
    rfl
  · intro hmem
    have hsub : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj p.siteObject) :=
      inferInstanceAs (Subsingleton (Spec (.of p.carrier)))
    have hrange : Set.range p.value.left.hom.base ⊆ Set.range V.hom.hom.base := by
      rintro _ ⟨x, rfl⟩
      rw [hsub.elim x (IsLocalRing.closedPoint p.carrier)]
      exact hmem
    let l := IsOpenImmersion.lift V.hom.hom p.value.left.hom hrange
    refine ⟨Over.homMk (ObjectProperty.homMk l) ?_⟩
    apply ObjectProperty.hom_ext
    exact IsOpenImmersion.lift_fac V.hom.hom p.value.left.hom hrange

variable {P : ObjectProperty (CurveFamily B hZ)}

/-- **`|Curves^P|` is open, for `P` with condition (o) of Stacks 0E0E.** Along every chart of
`|Curves|` by an algebraic space, and every scheme-valued point of that space, the preimage of
`|Curves^P|` is cut out by the open subscheme of condition (o). -/
theorem isOpen_curvesPointSet (hP : IsOpenCurvesLocus B hZ P) :
    IsOpen (curvesPointSet B hZ P) := by
  refine (Stack.isOpen_pointTopology_iff B integerBase hZ (curvesSmall B hZ) _).2 fun c => ?_
  refine (Space.isOpen_pointTopology_iff B integerBase hZ _).2 fun U a => ?_
  obtain ⟨V, hV, hchar⟩ := hP.exists_open_over U (chartCurveFamilies c.2 a)
    (chartCurveFamilies_comp_projection c.2 a)
  refine ⟨Set.range V.hom.hom.base, hV.base_open.isOpen_range, fun p => ?_⟩
  rw [Set.mem_preimage, Set.mem_preimage, Space.pointsMap_class, Stack.spacePointMap_class,
    pointClass_mem_curvesPointSet_iff hP, ← nonempty_hom_iff_schemePoint_mem_range p V hV,
    hchar]
  let T : BigFppfOver B U.left.1 U.left.2 := Over.mk p.value.left
  have hw : p.value.left ≫ U.hom = p.siteObject.hom := Over.w p.value
  let b₁ : p.siteObject ⟶ (Over.map U.hom).obj T := Over.homMk (𝟙 _) (by simp [T, hw])
  let b₂ : (Over.map U.hom).obj T ⟶ p.siteObject := Over.homMk (𝟙 _) (by simp [T, hw])
  have hb₁ : b₁ ≫ (Over.homMk T.hom (by simp) : (Over.map U.hom).obj T ⟶ U) = p.value := by
    ext; simp [b₁, T]
  have hb₂ : b₂ ≫ p.value = (Over.homMk T.hom (by simp) : (Over.map U.hom).obj T ⟶ U) := by
    ext; simp [b₂, T]
  have mor : ∀ {X Y : BigFppfOver B integerBase hZ} (g : X ⟶ Y) (x : X ⟶ U) (y : Y ⟶ U),
      g ≫ y = x → ((⟨X, Discrete.mk (a.app (op X) x)⟩ :
        (Stack.fibredCategory B integerBase hZ c.1.1).val.obj) ⟶
          (⟨Y, Discrete.mk (a.app (op Y) y)⟩ :
        (Stack.fibredCategory B integerBase hZ c.1.1).val.obj)) :=
    fun g x y h => Stack.fibredCategoryHomOfEq g ((congrArg (a.app _) h.symm).trans
      (congrFun (congrArg (fun q => TypeCat.homEquiv q) (a.naturality g.op)) y))
  exact ⟨hP.prop_of_hom ((curvesSmallFamily B hZ).map (c.2.map (mor b₂ _ _ hb₂))),
    hP.prop_of_hom ((curvesSmallFamily B hZ).map (c.2.map (mor b₁ _ _ hb₁)))⟩

end Openness

/-! ### Specialization of points of `|Curves|` -/

section Specialization

/-- The field-valued point of the scheme `V` given by a field-valued point `q` of the stack of
curves and a morphism `a` from its base to `V`. -/
def spacePointOfHom (q : Stack.FieldValuedPoint B integerBase hZ (curvesSmall B hZ).val)
    {V : BigFppfOver B integerBase hZ} (a : q.base ⟶ V) :
    Space.FieldValuedPoint B integerBase hZ (yoneda.obj V) where
  carrier := q.carrier
  contained := Stack.contains_spectrum_fieldValuedPoint B integerBase hZ q
  toBase := Stack.spectrumStructureMorphism B integerBase hZ q
  value := (Stack.spectrumSiteObjectIso B integerBase hZ q).hom ≫ a

/-- **Specialization along a family of curves.** Let `y₀` be an object of the stack of curves
over `V` and let `q₁`, `q₂` be field-valued points with morphisms to `y₀` lying over morphisms
`a₁`, `a₂` from their bases to `V`. If the point of `V` of `a₂` is a specialization of that of
`a₁`, then the point of `|Curves|` of `q₂` is a specialization of that of `q₁`: the chart of the
stack of curves by `V` that `y₀` classifies is continuous (Stacks 04XL). -/
theorem pointClass_specializes_of_isHomLift {V : BigFppfOver B integerBase hZ}
    {y₀ : (curvesSmall B hZ).val.obj} (hy₀ : (curvesSmall B hZ).val.p.obj y₀ = V)
    (q₁ q₂ : Stack.FieldValuedPoint B integerBase hZ (curvesSmall B hZ).val)
    (a₁ : q₁.base ⟶ V) (a₂ : q₂.base ⟶ V) (m₁ : q₁.obj ⟶ y₀) (m₂ : q₂.obj ⟶ y₀)
    [(curvesSmall B hZ).val.p.IsHomLift a₁ m₁] [(curvesSmall B hZ).val.p.IsHomLift a₂ m₂]
    (hsp : Space.schemePoint B integerBase hZ V (spacePointOfHom q₁ a₁) ⤳
      Space.schemePoint B integerBase hZ V (spacePointOfHom q₂ a₂)) :
    Stack.pointClass B integerBase hZ _ (curvesSmall B hZ).property q₁ ⤳
      Stack.pointClass B integerBase hZ _ (curvesSmall B hZ).property q₂ := by
  obtain ⟨G, hGq, ξ, hξ⟩ :=
    Stacks.RepresentableMorphism.ClassifyingFunctor.exists_classifying_functor
      (curvesSmall B hZ).val.p (curvesSmall B hZ).property V y₀ hy₀
  let c : (Stack.fibredCategory B integerBase hZ (yoneda.obj V)).val ⥤ᵇ (curvesSmall B hZ).val :=
    (Stack.elementsToSlice B integerBase hZ V).comp ⟨G, hGq⟩
  have hcont := Stack.continuous_spacePointMap B integerBase hZ (yoneda.obj V)
    (isAlgebraicSpace_yoneda B integerBase hZ V) (curvesSmall B hZ) c
  have key : ∀ (q : Stack.FieldValuedPoint B integerBase hZ (curvesSmall B hZ).val)
      (a : q.base ⟶ V) (m : q.obj ⟶ y₀) [(curvesSmall B hZ).val.p.IsHomLift a m],
      Stack.spacePointMap B integerBase hZ (yoneda.obj V) (curvesSmall B hZ) c
          ((spacePointOfHom q a).class B integerBase hZ (yoneda.obj V)) =
        Stack.pointClass B integerBase hZ _ (curvesSmall B hZ).property q := by
    intro q a m _
    rw [Stack.spacePointMap_class]
    refine (Stack.class_eq_class_iff_hasCommonExtension B integerBase hZ _ _ _ _).2 ⟨q, ?_, ⟨𝟙 _⟩⟩
    let P := (curvesSmall B hZ).val.p
    let β : (Over.mk a : Over V) ⟶ Over.mk (𝟙 V) := Over.homMk a
    have hβ : P.IsHomLift a (G.map β) := by
      refine IsHomLift.of_fac _ _ _ (Functor.congr_obj hGq _) (Functor.congr_obj hGq _) ?_
      have e := Functor.congr_hom hGq β
      simp only [Functor.comp_map] at e
      show a = _
      rw [e]
      simp [β]
    have hψ : P.IsHomLift a (G.map β ≫ ξ.hom) := by
      simpa using (inferInstance : P.IsHomLift (a ≫ 𝟙 V) (G.map β ≫ ξ.hom))
    let e := Stacks.RepresentableMorphism.ClassifyingFunctor.vertIso P (curvesSmall B hZ).property
      a m (G.map β ≫ ξ.hom) inferInstance hψ
    let γ : (Over.mk a : Over V) ⟶ Over.mk (spacePointOfHom q a).value :=
      Over.homMk (Stack.spectrumSiteObjectIso B integerBase hZ q).inv
        (Iso.inv_hom_id_assoc (Stack.spectrumSiteObjectIso B integerBase hZ q) a)
    exact ⟨e.hom ≫ G.map γ⟩
  let := Space.pointTopology B integerBase hZ (yoneda.obj V)
  have hsp' : (spacePointOfHom q₁ a₁).class B integerBase hZ (yoneda.obj V) ⤳
      (spacePointOfHom q₂ a₂).class B integerBase hZ (yoneda.obj V) :=
    (Space.schemePointsHomeomorph B integerBase hZ V).isInducing.specializes_iff.1 hsp
  have := hsp'.map hcont
  rwa [key q₁ a₁ m₁, key q₂ a₂ m₂] at this

end Specialization

end AlgebraicGeometry

end
