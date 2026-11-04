module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverSchemeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OverSchemeLocus

/-!
# The points of an algebraic space over a base, after base change

For an algebraic space `H` over `Y` the functor of points over the base,
`AlgebraicGeometry.Space.spacePointsOver`, is compatible with isomorphisms over `Y` and with base
change along a morphism `Y' ⟶ Y`: the points over `Y'` of `H ×_Y Y'` are the points over `Y` of
`H`, read on the test schemes over `Y'` through `Y' ⟶ Y`.  Over a scheme `T` of the site, an
algebraic space affine and of finite presentation over `T` is a scheme affine and of finite
presentation over `T` (Stacks 03WG), so an algebraic space affine and of finite presentation over
`Y` becomes, over every test scheme `T ⟶ Y`, the functor of points of a scheme affine and of
finite presentation over `T`.

## Main definitions

* `AlgebraicGeometry.Space.spacePointsOverIsoOfIso`: the points over `Y` of two algebraic spaces
  isomorphic over `Y` agree.
* `AlgebraicGeometry.Space.spacePointsOverBaseChangeIsoOfIsPullback`: the points over `Y'` of a
  base change `H' = H ×_Y Y'` are the points over `Y` of `H` on the test schemes over `Y'`.

## Main results

* `AlgebraicGeometry.Space.exists_scheme_spacePointsOver_iso`: an algebraic space affine and of
  finite presentation over a scheme `T` of the site has the points over `T` of a scheme affine and
  of finite presentation over `T`.
* `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.exists_baseChange`: a
  functor on the test schemes over `Y` which is an algebraic space affine and of finite
  presentation over `Y` is, over every test scheme `T ⟶ Y`, the functor of points of a scheme
  affine and of finite presentation over `T`.

## References

* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Iso

variable {Y H H' : AlgebraicSpaces B S hS}

/-- **The points over `Y` of two algebraic spaces isomorphic over `Y` agree.** -/
def spacePointsOverIsoOfIso (e : H ≅ H') {p : H ⟶ Y} {p' : H' ⟶ Y} (he : e.hom ≫ p' = p) :
    spacePointsOver p ≅ spacePointsOver p' :=
  have hinv : e.inv ≫ p = p' := by rw [← he, Iso.inv_hom_id_assoc]
  NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := fun x => ⟨e.hom.hom.app (op T.unop.left) x.1,
          (congrArg (fun k => k.hom.app (op T.unop.left) x.1) he).trans x.2⟩
        invFun := fun x => ⟨e.inv.hom.app (op T.unop.left) x.1,
          (congrArg (fun k => k.hom.app (op T.unop.left) x.1) hinv).trans x.2⟩
        left_inv := fun x => Subtype.ext
          (congrArg (fun k => k.hom.app (op T.unop.left) x.1) e.hom_inv_id)
        right_inv := fun x => Subtype.ext
          (congrArg (fun k => k.hom.app (op T.unop.left) x.1) e.inv_hom_id) })
    (fun {T T'} g => by
      refine ConcreteCategory.hom_ext _ _ fun (x : spacePointsOverObj p T.unop) => Subtype.ext ?_
      exact NatTrans.naturality_apply e.hom.hom g.unop.left.op x.1)

/-- The isomorphism of points over `Y` acts on sections through the isomorphism of spaces. -/
theorem spacePointsOverIsoOfIso_hom_app_coe (e : H ≅ H') {p : H ⟶ Y} {p' : H' ⟶ Y}
    (he : e.hom ≫ p' = p) (T : SchemesOver Y) (x : spacePointsOverObj p T) :
    (((spacePointsOverIsoOfIso e he).hom.app (op T)) x).1 = e.hom.hom.app (op T.left) x.1 :=
  rfl

end Iso

section BaseChange

variable {Y Y' H H' : AlgebraicSpaces B S hS} {q : Y' ⟶ Y} {p : H ⟶ Y} {a : H' ⟶ H}
  {p' : H' ⟶ Y'}

/-- A section of `H'` over a test scheme over `Y'` lying over its section of `Y'` maps to a
section of `H` lying over the section of `Y` that the test scheme is. -/
theorem spacePointsOver_baseChange_fst (sq : IsPullback a.hom p'.hom p.hom q.hom)
    (T : SchemesOver Y') (x : spacePointsOverObj p' T) :
    p.hom.app _ (a.hom.app _ x.1) = testPoint ((CostructuredArrow.map q).obj T) :=
  (congrArg (fun k => k.app (op T.left) x.1) sq.w).trans
    ((congrArg (q.hom.app (op T.left)) x.2).trans (testPoint_map q T).symm)

/-- The morphism of presheaves to `H'` attached to a section of `H` lying over the section of
`Y` that a test scheme over `Y'` is. -/
def spacePointsOverBaseChangeLift (sq : IsPullback a.hom p'.hom p.hom q.hom) (T : SchemesOver Y')
    (y : spacePointsOverObj p ((CostructuredArrow.map q).obj T)) :
    yoneda.obj T.left ⟶ H'.1 :=
  sq.lift (yonedaEquiv.symm y.1) T.hom.hom (yonedaEquiv.injective (by
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact y.2))

/-- The lift of a section `y` of `H`, followed by `H' ⟶ H`, is the morphism from the Yoneda
presheaf of the test scheme to `H` given by `y`. -/
@[reassoc (attr := simp)]
theorem spacePointsOverBaseChangeLift_fst (sq : IsPullback a.hom p'.hom p.hom q.hom)
    (T : SchemesOver Y') (y : spacePointsOverObj p ((CostructuredArrow.map q).obj T)) :
    spacePointsOverBaseChangeLift sq T y ≫ a.hom = yonedaEquiv.symm y.1 :=
  sq.lift_fst _ _ _

/-- The lift of a section of `H`, followed by `H' ⟶ Y'`, is the structure morphism of the test
scheme over `Y'`. -/
@[reassoc (attr := simp)]
theorem spacePointsOverBaseChangeLift_snd (sq : IsPullback a.hom p'.hom p.hom q.hom)
    (T : SchemesOver Y') (y : spacePointsOverObj p ((CostructuredArrow.map q).obj T)) :
    spacePointsOverBaseChangeLift sq T y ≫ p'.hom = T.hom.hom :=
  sq.lift_snd _ _ _

/-- **The points over `Y'` of a base change `H' = H ×_Y Y'` are the points over `Y` of `H` on
the test schemes over `Y'`**, read through `Y' ⟶ Y`. -/
def spacePointsOverBaseChangeIsoOfIsPullback (sq : IsPullback a.hom p'.hom p.hom q.hom) :
    spacePointsOver p' ≅ (CostructuredArrow.map q).op ⋙ spacePointsOver p :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := fun (x : spacePointsOverObj p' T.unop) =>
          ⟨a.hom.app (op T.unop.left) x.1, spacePointsOver_baseChange_fst sq T.unop x⟩
        invFun := fun (y : spacePointsOverObj p ((CostructuredArrow.map q).obj T.unop)) =>
          ⟨yonedaEquiv (spacePointsOverBaseChangeLift sq T.unop y), by
          rw [← yonedaEquiv_comp, spacePointsOverBaseChangeLift_snd]
          rfl⟩
        left_inv := fun (x : spacePointsOverObj p' T.unop) => Subtype.ext (by
          change yonedaEquiv (spacePointsOverBaseChangeLift sq T.unop _) = x.1
          refine (congrArg yonedaEquiv (sq.hom_ext (l := yonedaEquiv.symm x.1) ?_ ?_)).trans
            (yonedaEquiv.apply_symm_apply x.1)
          · rw [spacePointsOverBaseChangeLift_fst, yonedaEquiv_symm_naturality_right]
          · rw [spacePointsOverBaseChangeLift_snd]
            exact yonedaEquiv.injective (by
              rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
              exact x.2.symm))
        right_inv := fun (y : spacePointsOverObj p ((CostructuredArrow.map q).obj T.unop)) =>
          Subtype.ext (by
          change a.hom.app _ (yonedaEquiv (spacePointsOverBaseChangeLift sq T.unop y)) = y.1
          rw [← yonedaEquiv_comp, spacePointsOverBaseChangeLift_fst,
            Equiv.apply_symm_apply]) })
    (fun {T T'} g => by
      refine ConcreteCategory.hom_ext _ _ fun (x : spacePointsOverObj p' T.unop) => Subtype.ext ?_
      exact NatTrans.naturality_apply a.hom g.unop.left.op x.1)

end BaseChange

section Scheme

/-- **An algebraic space affine and of finite presentation over a scheme `T` of the site has the
points over `T` of a scheme affine and of finite presentation over `T`.**  The algebraic space is
a scheme by Stacks 03WG, and finite presentation of the morphism of algebraic spaces between
schemes is finite presentation of the morphism of schemes (Stacks 03XP). -/
theorem exists_scheme_spacePointsOver_iso {T : BigFppfOver B S hS} {H : AlgebraicSpaces B S hS}
    (p : H ⟶ (schemeSpaceFunctor B S hS).obj T) (hp : IsAffineHom B S hS p.hom)
    (hfp : IsFinitePresentation B S hS p.hom) :
    ∃ (W : BigFppfOver B S hS) (w : W ⟶ T),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map w) ∧
          Nonempty (spacePointsOver ((schemeSpaceFunctor B S hS).map w) ≅ spacePointsOver p) := by
  obtain ⟨W, e, P, he, hP⟩ := exists_representing_over_of_isAffineHom B S hS H.2 p.hom hp
  have hsq : IsPullback e.inv (yoneda.map P) p.hom (𝟙 ((schemeSpaceFunctor B S hS).obj T).1) :=
    @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id _)
      ⟨he.trans (Category.comp_id _).symm⟩
  have hPfp : IsFinitePresentation B S hS (yoneda.map P) :=
    IsFinitePresentation.of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS W) H.2
      (isAlgebraicSpace_yoneda B S hS T) (isAlgebraicSpace_yoneda B S hS T) hsq hfp
  have hPlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map P) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget P).1 hPfp.1
  let eS : (schemeSpaceFunctor B S hS).obj W ≅ H :=
    { hom := ObjectProperty.homMk e.inv
      inv := ObjectProperty.homMk e.hom
      hom_inv_id := ObjectProperty.hom_ext _ e.inv_hom_id
      inv_hom_id := ObjectProperty.hom_ext _ e.hom_inv_id }
  exact ⟨W, P, hP, hPlfp,
    ⟨spacePointsOverIsoOfIso eS (p := (schemeSpaceFunctor B S hS).map P) (p' := p)
      (ObjectProperty.hom_ext _ he)⟩⟩

end Scheme

/-- **Over a scheme `T` of the site, an algebraic space affine and of finite presentation over
`T` is a scheme affine and of finite presentation over `T`**, read on the functors of points over
`T` (Stacks 03WG, Stacks 03XP). -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.exists_scheme {T : BigFppfOver B S hS}
    {R : (SchemesOver ((schemeSpaceFunctor B S hS).obj T))ᵒᵖ ⥤ Type (u + 1)}
    (h : IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T) R) :
    ∃ (W : BigFppfOver B S hS) (w : W ⟶ T),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map w) ∧
          Nonempty (spacePointsOver ((schemeSpaceFunctor B S hS).map w) ⋙
              uliftFunctor.{u + 1, u} ≅ R) := by
  obtain ⟨H, p, hp, hfp, ⟨c⟩⟩ := h
  obtain ⟨W, w, hw, hwfp, ⟨ψ⟩⟩ := exists_scheme_spacePointsOver_iso p hp hfp
  exact ⟨W, w, hw, hwfp, ⟨Functor.isoWhiskerRight ψ _ ≪≫ c⟩⟩

/-- **A functor which is an algebraic space affine and of finite presentation over `Y` is, over
every test scheme `T ⟶ Y`, the functor of points of a scheme affine and of finite presentation
over `T`.** -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.exists_baseChange {Y : AlgebraicSpaces B S hS}
    {R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)} (h : IsAffineFinitePresentationAlgebraicSpaceOver Y R)
    {T : BigFppfOver B S hS} (q : (schemeSpaceFunctor B S hS).obj T ⟶ Y) :
    ∃ (W : BigFppfOver B S hS) (w : W ⟶ T),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map w) ∧
          Nonempty (spacePointsOver ((schemeSpaceFunctor B S hS).map w) ⋙
              uliftFunctor.{u + 1, u} ≅ (CostructuredArrow.map q).op ⋙ R) :=
  (h.baseChange q).exists_scheme

namespace HomSituation

/-- **Base change of the base preserves representability of the relative Hom functor.**  If
`Hom(F, G)` is an algebraic space affine and of finite presentation over the base, so is the
relative Hom functor of the situation base changed along `p : base' ⟶ base` (Stacks 08JW): it
is the restriction of `Hom(F, G)` along `p`. -/
theorem IsAffineFinitePresentationAlgebraicSpaceOverBase.baseChangedSituation
    {s : HomSituation B S hS} {base' : AlgebraicSpaces B S hS} (p : base' ⟶ s.base)
    (h : s.IsAffineFinitePresentationAlgebraicSpaceOverBase (modulePushforwardCoherence B S hS)) :
    (s.baseChangedSituation p).IsAffineFinitePresentationAlgebraicSpaceOverBase
      (modulePushforwardCoherence B S hS) :=
  (h.baseChange p).of_iso (s.homFunctorBaseChange p).symm

end HomSituation

end AlgebraicGeometry.Space

end
