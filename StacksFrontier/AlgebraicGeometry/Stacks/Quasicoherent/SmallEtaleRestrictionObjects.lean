module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorSmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# The objects of `𝒳` underlying the small étale site of an object

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `x` an object of `𝒳` over a
scheme `U`.  The restriction `F|_{U_étale}` of a presheaf `F` on `𝒳` to the small étale site of
`U` (Stacks 06W1, `AlgebraicGeometry.Stack.restrictToSmallEtale`) is `F` composed with the
functor `U_étale ⥤ 𝒳` sending an étale `V ⟶ U` to the pullback of `x` to `V`, through the
localization equivalence `𝒳/x ≌ (Sch/U)` of Stacks 06W0.  This file names that functor and
records, for the functor `AlgebraicGeometry.Stack.smallEtaleToStack` of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorSmallEtaleRestriction`, what is
needed to compare a property of a map of presheaves on `𝒳` at the objects it
hits with the same property on `U_étale`:

* the restriction of a map of presheaves is the whiskering by that functor;
* the scheme underlying the image of `V` is isomorphic to `V`, compatibly with the morphisms of
  `U_étale` and with the structure morphisms to `U`;
* so the image of an affine `V` is an object over an affine scheme, the image of any `V` is flat
  when `x` is, and the images of the affine opens of `U` cover `x`.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleToStackArrow`: the arrow to `x` from the image of `V`.
* `AlgebraicGeometry.Stack.smallEtaleToStackSchemeIso`: the identification of underlying
  schemes.
* `AlgebraicGeometry.Stack.restrictMapToSmallEtale`: the restriction `φ|_{U_étale}` of a map of
  presheaves on `𝒳`.

## References

* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (x : 𝒳)

/-- **The restriction `φ|_{U_étale}` of a map of presheaves on `𝒳` to the small étale site of
the scheme below `x`.** -/
noncomputable def restrictMapToSmallEtale {A : Type t} [Category.{s} A] {F G : 𝒳ᵒᵖ ⥤ A}
    (φ : F ⟶ G) :
    restrictToSmallEtale B E h S hS p hp x F ⟶ restrictToSmallEtale B E h S hS p hp x G :=
  Functor.whiskerLeft (smallEtaleToStack B E h S hS p hp x).op φ

/-- The component of `φ|_{U_étale}` at `V` is the component of `φ` at the image of `V` in `𝒳`. -/
@[simp]
theorem restrictMapToSmallEtale_app {A : Type t} [Category.{s} A] {F G : 𝒳ᵒᵖ ⥤ A}
    (φ : F ⟶ G) (V) :
    (restrictMapToSmallEtale B E h S hS p hp x φ).app V =
      φ.app (op ((smallEtaleToStack B E h S hS p hp x).obj V.unop)) :=
  rfl

/-- The arrow from the image of `V` to `x`. -/
noncomputable def smallEtaleToStackArrow
    (V : SmallEtale E (p.obj x).left.1
      (contains_base B E h S hS p x)) :
    (smallEtaleToStack B E h S hS p hp x).obj V ⟶ x :=
  letI := isEquivalence_overPost B S hS p hp x
  ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
    ((smallEtaleInclusion B E h (p.obj x).left.1
      (contains_base B E h S hS p x)).obj V)).hom

/-- **The scheme underlying the image of `V` is `V`.** -/
noncomputable def smallEtaleToStackSchemeIso
    (V : SmallEtale E (p.obj x).left.1
      (contains_base B E h S hS p x)) :
    (BigFppfOver.toScheme B S hS).obj (p.obj ((smallEtaleToStack B E h S hS p hp x).obj V)) ≅
      (SmallEtale.toScheme E _ _).obj V :=
  letI := isEquivalence_overPost B S hS p hp x
  B.inclusion.mapIso ((Over.forget _).mapIso
    ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.app
      ((smallEtaleInclusion B E h (p.obj x).left.1
        (contains_base B E h S hS p x)).obj V)))

/-- The arrow to `x` lies over the structure morphism of `V`, under the identification of
underlying schemes. -/
theorem toScheme_map_smallEtaleToStackArrow
    (V : SmallEtale E (p.obj x).left.1
      (contains_base B E h S hS p x)) :
    (BigFppfOver.toScheme B S hS).map (p.map (smallEtaleToStackArrow B E h S hS p hp x V)) =
      (smallEtaleToStackSchemeIso B E h S hS p hp x V).hom ≫ E.inclusion.map V.obj.hom := by
  let := isEquivalence_overPost B S hS p hp x
  have := Over.w ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.hom.app
      ((smallEtaleInclusion B E h (p.obj x).left.1
        (contains_base B E h S hS p x)).obj V))
  exact (congrArg B.inclusion.map this).symm.trans (B.inclusion.map_comp _ _)

/-- The identification of underlying schemes is compatible with the morphisms of the small étale
site. -/
theorem toScheme_map_smallEtaleToStack_map
    {V' V : SmallEtale E (p.obj x).left.1
      (contains_base B E h S hS p x)} (g : V' ⟶ V) :
    (BigFppfOver.toScheme B S hS).map (p.map ((smallEtaleToStack B E h S hS p hp x).map g)) ≫
        (smallEtaleToStackSchemeIso B E h S hS p hp x V).hom =
      (smallEtaleToStackSchemeIso B E h S hS p hp x V').hom ≫
        (SmallEtale.toScheme E _ _).map g := by
  let := isEquivalence_overPost B S hS p hp x
  have := (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.hom.naturality
    ((smallEtaleInclusion B E h (p.obj x).left.1
      (contains_base B E h S hS p x)).map g)
  have := congrArg (fun k => B.inclusion.map k.left) this
  simp only [Over.comp_left, Functor.map_comp] at this
  exact this

/-- The arrow to `x` from the image of `V` is étale on underlying schemes. -/
theorem etale_toScheme_map_smallEtaleToStackArrow (V : SmallEtale E (p.obj x).left.1
      (contains_base B E h S hS p x)) :
    Etale ((BigFppfOver.toScheme B S hS).map
      (p.map (smallEtaleToStackArrow B E h S hS p hp x V))) := by
  rw [toScheme_map_smallEtaleToStackArrow]
  infer_instance

/-- The image of an affine object of the small étale site lies over an affine scheme. -/
theorem isAffineOver_smallEtaleToStack (V : SmallEtale E (p.obj x).left.1
      (contains_base B E h S hS p x))
    (hV : IsAffine ((SmallEtale.toScheme E _ _).obj V)) :
    IsAffineOver B S hS (p.obj ((smallEtaleToStack B E h S hS p hp x).obj V)) :=
  have := hV
  IsAffine.of_isIso (smallEtaleToStackSchemeIso B E h S hS p hp x V).hom

/-- The object of the small étale site given by an open of the scheme below `x`. -/
noncomputable abbrev smallEtaleOpen (W : ((p.obj x).left.1).Opens) :
    SmallEtale E (p.obj x).left.1
      (contains_base B E h S hS p x) :=
  SmallEtale.openSubObj E _ _ (SmallEtale.final E _ _) W

/-- The arrow to `x` from the image of an open is an open immersion with that open as image. -/
theorem isOpenImmersion_toScheme_map_smallEtaleToStackArrow_open
    (W : ((p.obj x).left.1).Opens) :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (p.map (smallEtaleToStackArrow B E h S hS p hp x (smallEtaleOpen B E h S hS p x W)))) := by
  rw [toScheme_map_smallEtaleToStackArrow]
  have : _root_.AlgebraicGeometry.IsOpenImmersion
      (E.inclusion.map (smallEtaleOpen B E h S hS p x W).obj.hom) := by
    show _root_.AlgebraicGeometry.IsOpenImmersion (W.ι ≫ 𝟙 _)
    infer_instance
  infer_instance

/-- On underlying schemes, the arrow to `x` from the image of an open `W` has range `W`. -/
theorem range_toScheme_map_smallEtaleToStackArrow_open (W : ((p.obj x).left.1).Opens) :
    Set.range ((BigFppfOver.toScheme B S hS).map
      (p.map (smallEtaleToStackArrow B E h S hS p hp x (smallEtaleOpen B E h S hS p x W)))) =
      (W : Set (p.obj x).left.1) := by
  rw [toScheme_map_smallEtaleToStackArrow]
  have hW : Set.range (E.inclusion.map (smallEtaleOpen B E h S hS p x W).obj.hom) =
      (W : Set (p.obj x).left.1) := by
    show Set.range (W.ι ≫ 𝟙 _) = _
    rw [Category.comp_id, Scheme.Opens.range_ι]
  rw [← hW, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso _).2, Set.image_univ]

/-- **The images of the affine opens of the scheme below `x` cover `x`.** -/
theorem ofArrows_smallEtaleToStackArrow_affineOpens_mem :
    Sieve.ofArrows
        (fun W : ((p.obj x).left.1).affineOpens =>
          (smallEtaleToStack B E h S hS p hp x).obj (smallEtaleOpen B E h S hS p x W.1))
        (fun W => smallEtaleToStackArrow B E h S hS p hp x (smallEtaleOpen B E h S hS p x W.1)) ∈
      BigFppfOver.associatedTopology B S hS p .fppf x := by
  refine FibredSite.ofArrows_mem_associatedTopology B S hS p hp _ _
    (BigFppfOver.ofArrows_mem_baseOverTopology B S hS _ _ ?_)
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun t => ?_, fun W => ?_⟩
  · obtain ⟨W, hW, htW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := t) trivial
    refine ⟨⟨W, hW⟩, ?_⟩
    show t ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      (p.map (smallEtaleToStackArrow B E h S hS p hp x (smallEtaleOpen B E h S hS p x W))))
    rw [range_toScheme_map_smallEtaleToStackArrow_open]
    exact htW
  · have := etale_toScheme_map_smallEtaleToStackArrow B E h S hS p hp x
      (V := smallEtaleOpen B E h S hS p x W.1)
    exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Stack

end
