module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementFiberDense

/-!
# Direct images commute with enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` for `B` and let `f' : X' ⟶ Y'` be its inverse image on the enlarged
site. Write `R_X` and `R_Y` for restriction of sheaves along the transport of étale charts, which
are equivalences of small étale topoi. Then

`R_Y ∘ f'_* ≅ f_* ∘ R_X`

as functors from sheaves of sets on the small étale site of `X'` to sheaves of sets on the small
étale site of `Y`, and this identification carries the structure map of `f'` to the structure
map of `f`.

## Main definitions

* `AlgebraicGeometry.SiteEnlargement.pushforwardComparison`: the natural isomorphism.

## Main results

* `AlgebraicGeometry.SiteEnlargement.pushforwardComparison_structureSharp`: the structure maps
  `𝒪_Y ⟶ f_*𝒪_X` and `𝒪_{Y'} ⟶ f'_*𝒪_{X'}` correspond.

## Implementation notes

Sections of a direct image over a chart `V` are families of sections over the diagrams of charts
with lower chart `V` (`AlgebraicGeometry.SiteEnlargement.pushforwardSectionEquiv`), and the
families over the transported diagrams are the families over the diagrams of the smaller site
(`AlgebraicGeometry.SiteEnlargement.fiberRestrictEquiv`). The comparison is the composite of
these bijections; its naturality and the compatibility with the structure maps are checked on
families.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SiteEnlargement

open Space

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') {S : Scheme.{u}}
  {hS : B.Contains S} (hS' : B'.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Restriction of sheaves of sets along the transport of étale charts. -/
abbrev restrictSheaf (X : AlgebraicSpaces B S hS) :
    Sheaf (Space.SmallEtale.topology B' S hS'
      ((changeBigSite B B' h S hS).obj X).obj) (Type u) ⥤
      Sheaf (Space.SmallEtale.topology B S hS X.obj) (Type u) :=
  (chartTransport B B' h S hS X).sheafPushforwardContinuous (Type u)
    (Space.SmallEtale.topology B S hS X.obj)
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)

/-- The comparison of the sections over a chart of `Y`. -/
def pushforwardComparisonApp
    (F' : Sheaf (Space.SmallEtale.topology B' S hS'
      ((changeBigSite B B' h S hS).obj X).obj) (Type u)) (V : Space.SmallEtale B S hS Y.obj) :
    ((smallEtaleRingedToposHom B' S hS'
        ((changeBigSite B B' h S hS).map f)).toToposHom.pushforward.obj F').obj.obj
        (op ((chartTransport B B' h S hS Y).obj V)) ≃
      ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj
        ((restrictSheaf h hS' X).obj F')).obj.obj (op V) :=
  (pushforwardSectionEquiv ((changeBigSite B B' h S hS).map f) F'
      ((chartTransport B B' h S hS Y).obj V)).trans
    ((fiberRestrictEquiv h f F' V).trans
      (pushforwardSectionEquiv f ((restrictSheaf h hS' X).obj F') V).symm)

/-- The family of sections attached to the comparison of a section `s` over a chart of `Y` is the
restriction to the smaller site of the family attached to `s`. -/
theorem pushforwardSectionEquiv_pushforwardComparisonApp
    (F' : Sheaf (Space.SmallEtale.topology B' S hS'
      ((changeBigSite B B' h S hS).obj X).obj) (Type u)) (V : Space.SmallEtale B S hS Y.obj) s :
    pushforwardSectionEquiv f ((restrictSheaf h hS' X).obj F') V
        (pushforwardComparisonApp h hS' f F' V s) =
      restrictFiber h f F' V (pushforwardSectionEquiv ((changeBigSite B B' h S hS).map f) F'
        ((chartTransport B B' h S hS Y).obj V) s) :=
  Equiv.apply_symm_apply _ _

/-- The comparison of sections, as a morphism of presheaves on the small étale site of `Y`. -/
def pushforwardComparisonPresheafHom
    (F' : Sheaf (Space.SmallEtale.topology B' S hS'
      ((changeBigSite B B' h S hS).obj X).obj) (Type u)) :
    ((restrictSheaf h hS' Y).obj ((smallEtaleRingedToposHom B' S hS'
        ((changeBigSite B B' h S hS).map f)).toToposHom.pushforward.obj F')).obj ⟶
      ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj
        ((restrictSheaf h hS' X).obj F')).obj where
  app V := TypeCat.ofHom (pushforwardComparisonApp h hS' f F' V.unop)
  naturality V₁ V₂ j := by
    apply TypeCat.homEquiv.injective
    funext s
    apply (pushforwardSectionEquiv f ((restrictSheaf h hS' X).obj F') V₂.unop).injective
    ext U g hg
    change (pushforwardSectionEquiv f ((restrictSheaf h hS' X).obj F') V₂.unop
      (pushforwardComparisonApp h hS' f F' V₂.unop _)).app U g hg =
        (pushforwardSectionEquiv f ((restrictSheaf h hS' X).obj F') V₂.unop
          (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj
            ((restrictSheaf h hS' X).obj F')).obj.map j
              (pushforwardComparisonApp h hS' f F' V₁.unop s))).app U g hg
    refine Eq.trans ?_ (pushforwardSectionEquiv_restrict f _ j.unop _ U g hg).symm
    refine (congrArg (fun x => FiberFamily.app x U g hg)
      (pushforwardSectionEquiv_pushforwardComparisonApp h hS' f F' V₂.unop _)).trans ?_
    refine Eq.trans ?_ (congrArg (fun x => FiberFamily.app x U _ _)
      (pushforwardSectionEquiv_pushforwardComparisonApp h hS' f F' V₁.unop s)).symm
    refine (pushforwardSectionEquiv_restrict ((changeBigSite B B' h S hS).map f) F'
      ((chartTransport B B' h S hS Y).map j.unop) s _ _ _).trans ?_
    exact FiberFamily.app_congr _ ((inclusionOver h S hS).map_comp _ _).symm _ _

/-- The comparison of sections is an isomorphism of presheaves, being a bijection over each
chart. -/
instance isIso_pushforwardComparisonPresheafHom
    (F' : Sheaf (Space.SmallEtale.topology B' S hS'
      ((changeBigSite B B' h S hS).obj X).obj) (Type u)) :
    IsIso (pushforwardComparisonPresheafHom h hS' f F') := by
  have : ∀ V, IsIso ((pushforwardComparisonPresheafHom h hS' f F').app V) := fun V =>
    (isIso_iff_bijective _).mpr (pushforwardComparisonApp h hS' f F' V.unop).bijective
  exact NatIso.isIso_of_isIso_app _

/-- **Direct images commute with enlarging the big fppf site**: the comparison
`f'_* ⋙ R_Y ⟶ R_X ⋙ f_*` of functors of sheaves of sets, which is an isomorphism. -/
def pushforwardComparisonHom :
    (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f)).toToposHom.pushforward ⋙
        restrictSheaf h hS' Y ⟶
      restrictSheaf h hS' X ⋙ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward where
  app F' := ObjectProperty.homMk (pushforwardComparisonPresheafHom h hS' f F')
  naturality F'₁ F'₂ α := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
    apply TypeCat.homEquiv.injective
    funext s
    apply (pushforwardSectionEquiv f ((restrictSheaf h hS' X).obj F'₂) V.unop).injective
    ext U g hg
    change (pushforwardSectionEquiv f ((restrictSheaf h hS' X).obj F'₂) V.unop
      (pushforwardComparisonApp h hS' f F'₂ V.unop _)).app U g hg =
        (pushforwardSectionEquiv f ((restrictSheaf h hS' X).obj F'₂) V.unop
          (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
            ((restrictSheaf h hS' X).map α)).hom.app V
              (pushforwardComparisonApp h hS' f F'₁ V.unop s))).app U g hg
    refine Eq.trans ?_ (pushforwardSectionEquiv_map f V.unop ((restrictSheaf h hS' X).map α)
      _ U g hg).symm
    refine (congrArg (fun x => FiberFamily.app x U g hg)
      (pushforwardSectionEquiv_pushforwardComparisonApp h hS' f F'₂ V.unop _)).trans ?_
    refine Eq.trans ?_ (congrArg (fun x => α.hom.app _ (FiberFamily.app x U g hg))
      (pushforwardSectionEquiv_pushforwardComparisonApp h hS' f F'₁ V.unop s)).symm
    exact pushforwardSectionEquiv_map ((changeBigSite B B' h S hS).map f) _ α s _ _ _

/-- The comparison `f'_* ⋙ R_Y ⟶ R_X ⋙ f_*` of direct images is an isomorphism, since it is one on
underlying presheaves. -/
instance isIso_pushforwardComparisonHom : IsIso (pushforwardComparisonHom h hS' f) := by
  have : ∀ F', IsIso ((pushforwardComparisonHom h hS' f).app F') := fun F' => by
    have : IsIso ((sheafToPresheaf _ (Type u)).map ((pushforwardComparisonHom h hS' f).app F')) :=
      isIso_pushforwardComparisonPresheafHom h hS' f F'
    exact isIso_of_fully_faithful (sheafToPresheaf _ _) _
  exact NatIso.isIso_of_isIso_app _

/-- **Direct images commute with enlarging the big fppf site**, as a natural isomorphism. -/
def pushforwardComparison :
    (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f)).toToposHom.pushforward ⋙
        restrictSheaf h hS' Y ≅
      restrictSheaf h hS' X ⋙ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward :=
  asIso (pushforwardComparisonHom h hS' f)



/-- **The comparison of direct images carries the structure map of `f'` to the structure map of
`f`.** Both send a regular function on a chart of `Y` to the family of its pullbacks along the
morphisms of schemes lying over the morphism of algebraic spaces. -/
theorem pushforwardComparison_structureSharp :
    ((restrictSheaf h hS' Y).map (RingedToposHom.forgetFSharp
        (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f))) ≫
      (pushforwardComparisonHom h hS' f).app
        ((smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).forgetRing.obj
          (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).O) :
      (smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O ⟶
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O)) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f) := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
  apply TypeCat.homEquiv.injective
  funext s
  apply (pushforwardSectionEquiv f ((restrictSheaf h hS' X).obj
    ((smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).forgetRing.obj
      (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).O)) V.unop).injective
  ext U g hg
  have e1 : TypeCat.homEquiv (((restrictSheaf h hS' Y).map (RingedToposHom.forgetFSharp
        (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f))) ≫
      (pushforwardComparisonHom h hS' f).app
        ((smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).forgetRing.obj
          (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).O)).hom.app V) s =
      pushforwardComparisonApp h hS' f
        ((smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).forgetRing.obj
          (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).O) V.unop
        ((RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B' S hS'
          ((changeBigSite B B' h S hS).map f))).hom.app
            (op ((chartTransport B B' h S hS Y).obj V.unop)) s) := rfl
  refine (congrArg (fun x => (pushforwardSectionEquiv f ((restrictSheaf h hS' X).obj
    ((smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).forgetRing.obj
      (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).O)) V.unop x).app
        U g hg) e1).trans ?_
  rw [pushforwardSectionEquiv_pushforwardComparisonApp, restrictFiber_app]
  have e2 := pushforwardSectionEquiv_structureSharp ((changeBigSite B B' h S hS).map f)
    ((chartTransport B B' h S hS Y).obj V.unop) s ((chartTransport B B' h S hS X).obj U)
    ((inclusionOver h S hS).map g) (comm_transport h f hg)
  have e3 := pushforwardSectionEquiv_structureSharp f V.unop s U g hg
  exact e2.trans e3.symm

end AlgebraicGeometry.SiteEnlargement

end
