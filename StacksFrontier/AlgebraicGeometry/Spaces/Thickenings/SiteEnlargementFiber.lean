module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondenceRingUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleStructureSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart

/-!
# Sections of a direct image as families over diagrams of charts

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `F` be a sheaf of sets on the
small étale site of `X` and let `V` be an étale chart of `Y`. A section of the direct image
`f_*F` over `V` is the same thing as a family of sections of `F`, one over every étale chart
`U` of `X` equipped with a morphism of schemes `U ⟶ V` lying over `f`, compatible with
restriction along morphisms of charts of `X`. This is the chart correspondence of Stacks 03G8
applied to the sheaf represented by `V`, with the Yoneda reduction that a map of sections over
every diagram with lower chart mapping to `V` is determined by its value at the identity of `V`.

## Main definitions

* `AlgebraicGeometry.SiteEnlargement.FiberFamily`: the families.
* `AlgebraicGeometry.SiteEnlargement.fMapFiberEquiv`: `f`-maps into the presheaf represented by
  `V` are the families over diagrams with lower chart `V`.
* `AlgebraicGeometry.SiteEnlargement.pushforwardSectionEquiv`: the sections of `f_*F` over `V`
  are the families.

## Main results

* `AlgebraicGeometry.SiteEnlargement.pushforwardSectionEquiv_restrict`: the identification is
  natural in `V`.
* `AlgebraicGeometry.SiteEnlargement.pushforwardSectionEquiv_map`: it is natural in `F`.
* `AlgebraicGeometry.SiteEnlargement.pushforwardSectionEquiv_structureSharp`: the structure map
  `𝒪_Y ⟶ f_*𝒪_X` sends a regular function to the family of its pullbacks.

## References

* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SiteEnlargement

open Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **A family over the diagrams of étale charts over `f` with lower chart `V`**: a section of
`F` over every étale chart `U` of `X` with a morphism `U ⟶ V` of schemes over `S` lying over
`f`, compatible with restriction along morphisms of charts of `X`. -/
structure FiberFamily (F : (Space.SmallEtale B S hS X.obj)ᵒᵖ ⥤ Type v)
    (V : Space.SmallEtale B S hS Y.obj) where
  /-- The section over a chart lying over `V`. -/
  app (U : Space.SmallEtale B S hS X.obj)
    (g : (Space.SmallEtale.toOver B S hS X.obj).obj U ⟶
      (Space.SmallEtale.toOver B S hS Y.obj).obj V)
    (hg : U.obj.hom ≫ f.hom = yoneda.map g ≫ V.obj.hom) : F.obj (op U)
  /-- The sections are compatible with restriction along morphisms of charts of `X`. -/
  naturality {U₁ U₂ : Space.SmallEtale B S hS X.obj} (i : U₁ ⟶ U₂)
    (g : (Space.SmallEtale.toOver B S hS X.obj).obj U₂ ⟶
      (Space.SmallEtale.toOver B S hS Y.obj).obj V)
    (hg : U₂.obj.hom ≫ f.hom = yoneda.map g ≫ V.obj.hom)
    (h₁ : U₁.obj.hom ≫ f.hom =
      yoneda.map ((Space.SmallEtale.toOver B S hS X.obj).map i ≫ g) ≫ V.obj.hom) :
    app U₁ ((Space.SmallEtale.toOver B S hS X.obj).map i ≫ g) h₁ = F.map i.op (app U₂ g hg)

namespace FiberFamily

variable {f} {F : (Space.SmallEtale B S hS X.obj)ᵒᵖ ⥤ Type v} {V : Space.SmallEtale B S hS Y.obj}

/-- Two families with the same sections are equal. -/
@[ext]
theorem ext {x y : FiberFamily f F V} (h : ∀ U g hg, x.app U g hg = y.app U g hg) : x = y := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  have : x = y := funext fun U => funext fun g => funext fun hg => h U g hg
  subst this
  rfl

/-- The section of a family depends on the morphism of schemes and not on the proof that it lies
over `f`. -/
theorem app_congr (x : FiberFamily f F V) {U : Space.SmallEtale B S hS X.obj}
    {g g' : (Space.SmallEtale.toOver B S hS X.obj).obj U ⟶
      (Space.SmallEtale.toOver B S hS Y.obj).obj V}
    (e : g = g') (hg : U.obj.hom ≫ f.hom = yoneda.map g ≫ V.obj.hom)
    (hg' : U.obj.hom ≫ f.hom = yoneda.map g' ≫ V.obj.hom) :
    x.app U g hg = x.app U g' hg' := by
  subst e
  rfl

end FiberFamily

/-- A morphism of schemes into a chart of `Y` followed by a morphism of charts lies over `f` as
soon as the first one does. -/
theorem comm_comp_toOver {U : Space.SmallEtale B S hS X.obj} {V W : Space.SmallEtale B S hS Y.obj}
    (g : (Space.SmallEtale.toOver B S hS X.obj).obj U ⟶
      (Space.SmallEtale.toOver B S hS Y.obj).obj W)
    (hg : U.obj.hom ≫ f.hom = yoneda.map g ≫ W.obj.hom) (j : W ⟶ V) :
    U.obj.hom ≫ f.hom =
      yoneda.map (g ≫ (Space.SmallEtale.toOver B S hS Y.obj).map j) ≫ V.obj.hom := by
  rw [hg, Functor.map_comp, Category.assoc]
  exact congrArg (yoneda.map g ≫ ·) (CostructuredArrow.w j.hom).symm

/-- A morphism of schemes out of a chart of `X` lying over `f`, precomposed with a morphism of
charts of `X`, lies over `f`. -/
theorem comm_precomp {W U : Space.SmallEtale B S hS X.obj} {V : Space.SmallEtale B S hS Y.obj}
    (n : W ⟶ U)
    (g : (Space.SmallEtale.toOver B S hS X.obj).obj U ⟶
      (Space.SmallEtale.toOver B S hS Y.obj).obj V)
    (hg : U.obj.hom ≫ f.hom = yoneda.map g ≫ V.obj.hom) :
    W.obj.hom ≫ f.hom =
      yoneda.map ((Space.SmallEtale.toOver B S hS X.obj).map n ≫ g) ≫ V.obj.hom :=
  (congrArg (· ≫ f.hom) (CostructuredArrow.w n.hom).symm).trans ((Category.assoc _ _ _).trans
    ((congrArg (yoneda.map ((Space.SmallEtale.toOver B S hS X.obj).map n) ≫ ·) hg).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ V.obj.hom) (yoneda.map_comp _ _).symm))))

/-- **`f`-maps into the presheaf represented by a chart `V` of `Y` are the families over the
diagrams with lower chart `V`**: an `f`-map is determined by its values at the identity of `V`,
by its compatibility with restriction of the lower chart. -/
def fMapFiberEquiv (F : (Space.SmallEtale B S hS X.obj)ᵒᵖ ⥤ Type v)
    (V : Space.SmallEtale B S hS Y.obj) :
    FMap B S hS X.obj Y.obj f.hom F (yoneda.obj V) ≃ FiberFamily f F V where
  toFun ξ :=
    { app := fun U g hg => ξ.app ⟨U, V, g, hg⟩ (𝟙 V)
      naturality := fun {U₁ U₂} i g hg h₁ => by
        have e := ξ.naturality ⟨U₂, V, g, hg⟩
          ⟨U₁, V, (Space.SmallEtale.toOver B S hS X.obj).map i ≫ g, h₁⟩ i (𝟙 V)
          (by rw [CategoryTheory.Functor.map_id, Category.comp_id]) (𝟙 V)
        refine Eq.trans ?_ e
        exact congrArg _ (Category.comp_id _).symm }
  invFun x :=
    { app := fun d s => x.app d.U (d.g ≫ (Space.SmallEtale.toOver B S hS Y.obj).map s)
        (comm_comp_toOver f d.g d.comm s)
      naturality := fun d d' i j hij s => by
        have e : d'.g ≫ (Space.SmallEtale.toOver B S hS Y.obj).map ((yoneda.obj V).map j.op s) =
            (Space.SmallEtale.toOver B S hS X.obj).map i ≫ d.g ≫
              (Space.SmallEtale.toOver B S hS Y.obj).map s := by
          change d'.g ≫ (Space.SmallEtale.toOver B S hS Y.obj).map (j ≫ s) = _
          rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← hij, Category.assoc]
        exact (x.app_congr e _ (e ▸ comm_comp_toOver f d'.g d'.comm _)).trans
          (x.naturality i _ (comm_comp_toOver f d.g d.comm s) _) }
  left_inv ξ := by
    refine FMap.ext_app B S hS f (funext fun d => funext fun s => ?_)
    obtain ⟨U, W, g, hc⟩ := d
    have e := ξ.naturality ⟨U, V, g ≫ (Space.SmallEtale.toOver B S hS Y.obj).map s,
        comm_comp_toOver f g hc s⟩ ⟨U, W, g, hc⟩ (𝟙 U) s
      (by rw [CategoryTheory.Functor.map_id, Category.id_comp]) (𝟙 V)
    refine ((FunctorToTypes.map_id_apply F _).symm.trans e.symm).trans ?_
    exact congrArg _ (Category.comp_id s)
  right_inv x := by
    ext U g hg
    exact x.app_congr (by simp) _ _

/-- The value of an `f`-map into a presheaf represented by a chart `V` at a morphism `s : W ⟶ V`
is its value at the identity of `V`, on the diagram with lower chart `V` obtained by composing
with `s`. -/
theorem FMap.app_eq_app_id (F : (Space.SmallEtale B S hS X.obj)ᵒᵖ ⥤ Type v)
    {V : Space.SmallEtale B S hS Y.obj} (ξ : FMap B S hS X.obj Y.obj f.hom F (yoneda.obj V))
    (d : ChartDiagram B S hS X.obj Y.obj f.hom) (s : d.V ⟶ V) :
    ξ.app d s = ξ.app ⟨d.U, V, d.g ≫ (Space.SmallEtale.toOver B S hS Y.obj).map s,
      comm_comp_toOver f d.g d.comm s⟩ (𝟙 V) :=
  (congrFun (congrFun (congrArg FMap.app ((fMapFiberEquiv f F V).left_inv ξ)) d) s).symm

section Pushforward

variable (F : Sheaf (Space.SmallEtale.topology B S hS X.obj) (Type u))
  (V : Space.SmallEtale B S hS Y.obj)

attribute [local instance] smallEtaleTopology_subcanonical

/-- **The sections of a direct image over a chart `V` are the families over the diagrams of charts
with lower chart `V`.** This is the sheaf-theoretic Yoneda lemma at the sheaf represented by `V`,
the chart correspondence of Stacks 03G8, and `AlgebraicGeometry.SiteEnlargement.fMapFiberEquiv`. -/
def pushforwardSectionEquiv :
    ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F).obj.obj (op V) ≃
      FiberFamily f F.obj V :=
  (Space.SmallEtale.topology B S hS Y.obj).yonedaEquiv.symm.trans
    ((fMapEquivPushforwardHom_ringUniverse B S hS f F
      ((Space.SmallEtale.topology B S hS Y.obj).yoneda.obj V)).symm.trans
      (fMapFiberEquiv f F.obj V))

/-- The family attached to a section of the direct image, at a morphism `U ⟶ V` lying over `f`: the
value at the identity of `V` of the corresponding `f`-map. -/
theorem pushforwardSectionEquiv_app
    (s : ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F).obj.obj (op V))
    (U : Space.SmallEtale B S hS X.obj) g hg :
    (pushforwardSectionEquiv f F V s).app U g hg =
      ((fMapEquivPushforwardHom_ringUniverse B S hS f F
        ((Space.SmallEtale.topology B S hS Y.obj).yoneda.obj V)).symm
          ((Space.SmallEtale.topology B S hS Y.obj).yonedaEquiv.symm s)).app ⟨U, V, g, hg⟩ (𝟙 V) :=
  rfl

/-- **The identification of the sections of a direct image with families is natural in the
chart of `Y`**: restricting a section along a morphism of charts `j : V₁ ⟶ V₂` restricts its
family by composing with `j`. -/
theorem pushforwardSectionEquiv_restrict {V₁ V₂ : Space.SmallEtale B S hS Y.obj} (j : V₁ ⟶ V₂)
    (s : ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F).obj.obj (op V₂))
    (U : Space.SmallEtale B S hS X.obj) g hg :
    (pushforwardSectionEquiv f F V₁
        (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F).obj.map j.op s)).app
        U g hg =
      (pushforwardSectionEquiv f F V₂ s).app U
        (g ≫ (Space.SmallEtale.toOver B S hS Y.obj).map j) (comm_comp_toOver f g hg j) := by
  rw [pushforwardSectionEquiv_app, pushforwardSectionEquiv_app,
    GrothendieckTopology.yonedaEquiv_symm_map]
  refine Eq.trans ?_ (FMap.app_eq_app_id f F.obj _ ⟨U, V₁, g, hg⟩ j)
  show ((fMapEquivPushforwardHom_ringUniverse B S hS f F
      ((Space.SmallEtale.topology B S hS Y.obj).yoneda.obj V₂)).symm
        ((Space.SmallEtale.topology B S hS Y.obj).yonedaEquiv.symm s)).app ⟨U, V₁, g, hg⟩
      (𝟙 V₁ ≫ j) = _
  rw [Category.id_comp]

/-- **The identification of the sections of a direct image with families is natural in the
sheaf**: the direct image of a morphism of sheaves acts on families sectionwise. -/
theorem pushforwardSectionEquiv_map {F₁ F₂ : Sheaf (Space.SmallEtale.topology B S hS X.obj)
      (Type u)} (α : F₁ ⟶ F₂)
    (s : ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F₁).obj.obj (op V))
    (U : Space.SmallEtale B S hS X.obj) g hg :
    (pushforwardSectionEquiv f F₂ V
        (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map α).hom.app (op V) s)).app
        U g hg =
      α.hom.app (op U) ((pushforwardSectionEquiv f F₁ V s).app U g hg) := by
  rw [pushforwardSectionEquiv_app, pushforwardSectionEquiv_app,
    ← GrothendieckTopology.yonedaEquiv_symm_naturality_right]
  exact fMapEquivPushforwardHom_ringUniverse_symm_app_map B S hS f F₁ F₂
    ((Space.SmallEtale.topology B S hS Y.obj).yoneda.obj V) α _ ⟨U, V, g, hg⟩ (𝟙 V)

/-- **The structure map `𝒪_Y ⟶ f_*𝒪_X` read on families**: it sends a regular function on a chart
`V` of `Y` to the family of its pullbacks along the morphisms of schemes `U ⟶ V` lying over `f`.
This is the chartwise formula of Stacks 03G8. -/
theorem pushforwardSectionEquiv_structureSharp
    (s : ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
      (smallEtaleRingedTopos B S hS Y).O).obj.obj
      (op V)) (U : Space.SmallEtale B S hS X.obj) g hg :
    (pushforwardSectionEquiv f
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O) V
        ((RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.app (op V) s)).app
        U g hg =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op s := by
  let θ := RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)
  have e := GrothendieckTopology.yonedaEquiv_symm_naturality_right
    (J := Space.SmallEtale.topology B S hS Y.obj) V θ s
  refine (pushforwardSectionEquiv_app f _ V _ U g hg).trans ?_
  refine (congrArg (fun m => ((fMapEquivPushforwardHom_ringUniverse B S hS f
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O)
    ((Space.SmallEtale.topology B S hS Y.obj).yoneda.obj V)).symm m).app ⟨U, V, g, hg⟩ (𝟙 V))
    e.symm).trans ?_
  refine (structureFMap_app B S hS f ⟨U, V, g, hg⟩ _).trans ?_
  exact congrArg _ (FunctorToTypes.map_id_apply _ s)

end Pushforward

end AlgebraicGeometry.SiteEnlargement

end
