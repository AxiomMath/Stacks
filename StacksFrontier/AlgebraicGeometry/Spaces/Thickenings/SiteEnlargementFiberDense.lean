module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementFiber
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementSheaves

/-!
# Families over diagrams of charts after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` for `B` and let `f' : X' ⟶ Y'` be its inverse image on the enlarged
site. Fix an étale chart `V` of `Y` and a sheaf `F'` of sets on the small étale site of `X'`. A
family of sections of `F'` over the diagrams of charts over `f'` with lower chart the transport
of `V` (`AlgebraicGeometry.SiteEnlargement.FiberFamily`) is determined by its values on the
transported charts of `X`: the transported charts are dense
(`AlgebraicGeometry.SiteEnlargement.chartTransport_isCoverDense`), and every family over the
diagrams of `X` glues to a family over the diagrams of `X'`.

## Main definitions

* `AlgebraicGeometry.SiteEnlargement.restrictFiber`: restriction of a family to the transported
  diagrams.
* `AlgebraicGeometry.SiteEnlargement.glueFiber`: gluing of a family over the diagrams of `X`.
* `AlgebraicGeometry.SiteEnlargement.fiberRestrictEquiv`: the two are inverse bijections.

## References

* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SiteEnlargement

open Space

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') {S : Scheme.{u}}
  {hS : B.Contains S}

/-- The localized inclusion of big fppf sites is fully faithful. -/
def inclusionOverFullyFaithful : (inclusionOver h S hS).FullyFaithful :=
  @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ (inclusionOver h S hS)
    (inclusionOver_full (τ := .fppf) h S hS) (inclusionOver_faithful (τ := .fppf) h S hS)

/-- The preimage of a morphism between images under the localized inclusion of big fppf sites. -/
def descendMap {A A' : BigFppfOver B S hS}
    (m : (inclusionOver h S hS).obj A ⟶ (inclusionOver h S hS).obj A') : A ⟶ A' :=
  (inclusionOverFullyFaithful h).preimage m

/-- The localized inclusion sends a descended morphism back to the morphism it was descended
from. -/
theorem map_descendMap {A A' : BigFppfOver B S hS}
    (m : (inclusionOver h S hS).obj A ⟶ (inclusionOver h S hS).obj A') :
    (inclusionOver h S hS).map (descendMap h m) = m :=
  (inclusionOverFullyFaithful h).map_preimage m

/-- Descending the image of a morphism under the localized inclusion recovers the morphism. -/
theorem descendMap_map {A A' : BigFppfOver B S hS} (g : A ⟶ A') :
    descendMap h ((inclusionOver h S hS).map g) = g :=
  (inclusionOverFullyFaithful h).preimage_map g

/-- Descent of morphisms along the localized inclusion is compatible with composition. -/
theorem descendMap_comp {A A' A'' : BigFppfOver B S hS}
    (m : (inclusionOver h S hS).obj A ⟶ (inclusionOver h S hS).obj A')
    (m' : (inclusionOver h S hS).obj A' ⟶ (inclusionOver h S hS).obj A'') :
    descendMap h (m ≫ m') = descendMap h m ≫ descendMap h m' :=
  (inclusionOverFullyFaithful h).preimage_comp m m'

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- A diagram of charts over `f` transports to a diagram of charts over the inverse image of `f`. -/
theorem comm_transport {U : Space.SmallEtale B S hS X.obj} {V : Space.SmallEtale B S hS Y.obj}
    {g : (Space.SmallEtale.toOver B S hS X.obj).obj U ⟶
      (Space.SmallEtale.toOver B S hS Y.obj).obj V}
    (hg : U.obj.hom ≫ f.hom = yoneda.map g ≫ V.obj.hom) :
    ((chartTransport B B' h S hS X).obj U).obj.hom ≫ ((changeBigSite B B' h S hS).map f).hom =
      yoneda.map ((inclusionOver h S hS).map g) ≫ ((chartTransport B B' h S hS Y).obj V).obj.hom :=
  (chartHom_map B B' h S hS X f U.obj.hom).symm.trans
    ((congrArg (chartHom B B' h S hS Y) hg).trans (chartHom_comp B B' h S hS Y g V.obj.hom))

/-- A diagram of transported charts over the inverse image of `f` whose morphism of schemes
descends comes from a diagram of charts over `f`. -/
theorem comm_descend {U : Space.SmallEtale B S hS X.obj} {V : Space.SmallEtale B S hS Y.obj}
    {g : (Space.SmallEtale.toOver B S hS X.obj).obj U ⟶
      (Space.SmallEtale.toOver B S hS Y.obj).obj V}
    (hg : ((chartTransport B B' h S hS X).obj U).obj.hom ≫ ((changeBigSite B B' h S hS).map f).hom =
      yoneda.map ((inclusionOver h S hS).map g) ≫
        ((chartTransport B B' h S hS Y).obj V).obj.hom) :
    U.obj.hom ≫ f.hom = yoneda.map g ≫ V.obj.hom :=
  chartHom_injective B B' h S hS Y ((chartHom_map B B' h S hS X f U.obj.hom).trans
    (hg.trans (chartHom_comp B B' h S hS Y g V.obj.hom).symm))

variable (F' : Sheaf (Space.SmallEtale.topology B' S (largerContains h hS)
    ((changeBigSite B B' h S hS).obj X).obj) (Type u)) (V : Space.SmallEtale B S hS Y.obj)

/-- **Restriction of a family to the transported diagrams.** -/
def restrictFiber
    (x : FiberFamily ((changeBigSite B B' h S hS).map f) F'.obj
      ((chartTransport B B' h S hS Y).obj V)) :
    FiberFamily f ((chartTransport B B' h S hS X).op ⋙ F'.obj) V where
  app U g hg := x.app ((chartTransport B B' h S hS X).obj U) ((inclusionOver h S hS).map g)
    (comm_transport h f hg)
  naturality {U₁ U₂} i g hg h₁ := by
    refine Eq.trans ?_ (x.naturality ((chartTransport B B' h S hS X).map i)
      ((inclusionOver h S hS).map g) (comm_transport h f hg) ?_)
    · exact x.app_congr ((inclusionOver h S hS).map_comp _ _) _ _
    · exact (congrArg (fun m => yoneda.map m ≫ ((chartTransport B B' h S hS Y).obj V).obj.hom)
        ((inclusionOver h S hS).map_comp _ _).symm).symm ▸ comm_transport h f h₁

/-- The restricted family at a diagram of charts of `X` is the value of the family at the
transported diagram. -/
@[simp]
theorem restrictFiber_app
    (x : FiberFamily ((changeBigSite B B' h S hS).map f) F'.obj
      ((chartTransport B B' h S hS Y).obj V)) (U : Space.SmallEtale B S hS X.obj) g hg :
    (restrictFiber h f F' V x).app U g hg =
      x.app ((chartTransport B B' h S hS X).obj U) ((inclusionOver h S hS).map g)
        (comm_transport h f hg) :=
  rfl

section Glue

variable {h f F' V}

/-- A sheaf on the small étale site of `X'` satisfies the sheaf condition for the sieve of arrows
factoring through a transported chart. -/
private theorem isSheafFor_coverByImage
    (U' : Space.SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj) :
    Presieve.IsSheafFor F'.obj (Sieve.coverByImage (chartTransport B B' h S hS X) U').arrows :=
  (isSheaf_iff_isSheaf_of_type _ F'.obj).mp F'.property _
    ((chartTransport_isCoverDense B B' h S hS X).is_cover U')

/-- Restricting a restricted section amounts to restricting along the composite. -/
private theorem map_op_map_op_apply {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type u) {a b c : C}
    (g : a ⟶ b) (n : c ⟶ a) (x : P.obj (op b)) : P.map n.op (P.map g.op x) = P.map (n ≫ g).op x :=
  by rw [← types_comp_apply (P.map g.op) (P.map n.op), ← P.map_comp, ← op_comp]

/-- Two sections of a sheaf on the small étale site of `X'` agree as soon as their restrictions to
all transported charts mapping to it agree. -/
theorem section_ext {U' : Space.SmallEtale B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj} {a b : F'.obj.obj (op U')}
    (hab : ∀ (U₃ : Space.SmallEtale B S hS X.obj)
      (n : (chartTransport B B' h S hS X).obj U₃ ⟶ U'), F'.obj.map n.op a = F'.obj.map n.op b) :
    a = b := by
  refine (isSheafFor_coverByImage U').isSeparatedFor.ext ?_
  rintro W k ⟨c⟩
  rw [← c.fac, op_comp, F'.obj.map_comp, types_comp_apply, types_comp_apply, hab]

variable (x : FiberFamily f ((chartTransport B B' h S hS X).op ⋙ F'.obj) V)
  {U' : Space.SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj}
  (g' : (Space.SmallEtale.toOver B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj).obj U' ⟶
    (Space.SmallEtale.toOver B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj Y).obj).obj ((chartTransport B B' h S hS Y).obj V))

/-- The morphism of schemes of the smaller site underlying a transported chart mapping to `U'`,
composed with `g'`. -/
def glueMap {U₀ : Space.SmallEtale B S hS X.obj}
    (n : (chartTransport B B' h S hS X).obj U₀ ⟶ U') :
    (Space.SmallEtale.toOver B S hS X.obj).obj U₀ ⟶ (Space.SmallEtale.toOver B S hS Y.obj).obj V :=
  descendMap h ((Space.SmallEtale.toOver B' S (largerContains h hS)
    ((changeBigSite B B' h S hS).obj X).obj).map n ≫ g')

/-- The morphism `glueMap g' n` lies over `f` as soon as `g'` lies over the inverse image of `f`. -/
theorem glueMap_comm (hg' : U'.obj.hom ≫ ((changeBigSite B B' h S hS).map f).hom =
    yoneda.map g' ≫ ((chartTransport B B' h S hS Y).obj V).obj.hom)
    {U₀ : Space.SmallEtale B S hS X.obj}
    (n : (chartTransport B B' h S hS X).obj U₀ ⟶ U') :
    U₀.obj.hom ≫ f.hom = yoneda.map (glueMap g' n) ≫ V.obj.hom := by
  refine comm_descend h f ?_
  refine (congrArg (· ≫ ((changeBigSite B B' h S hS).map f).hom)
    (CostructuredArrow.w n.hom).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (yoneda.map ((Space.SmallEtale.toOver B' S (largerContains h hS)
    ((changeBigSite B B' h S hS).obj X).obj).map n) ≫ ·) hg').trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg (· ≫ ((chartTransport B B' h S hS Y).obj V).obj.hom) ?_
  exact (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (map_descendMap h _).symm)

/-- `glueMap` is compatible with precomposition by a morphism of charts of `X`. -/
theorem glueMap_comp {U₀ U₁ : Space.SmallEtale B S hS X.obj} (p : U₁ ⟶ U₀)
    (n : (chartTransport B B' h S hS X).obj U₀ ⟶ U') :
    glueMap g' ((chartTransport B B' h S hS X).map p ≫ n) =
      (Space.SmallEtale.toOver B S hS X.obj).map p ≫ glueMap g' n := by
  refine (congrArg (fun m => descendMap h (m ≫ g'))
    ((Space.SmallEtale.toOver B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj).map_comp _ _)).trans ?_
  refine (congrArg (descendMap h) (Category.assoc
    ((inclusionOver h S hS).map ((Space.SmallEtale.toOver B S hS X.obj).map p)) _ _)).trans ?_
  exact (descendMap_comp h _ _).trans (congrArg (· ≫ _) (descendMap_map h _))

/-- The local section of the glued family over an arrow factoring through a transported chart. -/
def glueValue (hg' : U'.obj.hom ≫ ((changeBigSite B B' h S hS).map f).hom =
    yoneda.map g' ≫ ((chartTransport B B' h S hS Y).obj V).obj.hom)
    {W : Space.SmallEtale B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj} (k : W ⟶ U')
    (hk : Sieve.coverByImage (chartTransport B B' h S hS X) U' k) : F'.obj.obj (op W) :=
  F'.obj.map hk.some.lift.op (x.app hk.some.obj (glueMap g' hk.some.map)
    (glueMap_comm g' hg' hk.some.map))

/-- The local section `glueValue` restricts, on a transported chart mapping to its domain, to the
value of the family there. -/
theorem glueValue_restrict (hg' : U'.obj.hom ≫ ((changeBigSite B B' h S hS).map f).hom =
    yoneda.map g' ≫ ((chartTransport B B' h S hS Y).obj V).obj.hom)
    {W : Space.SmallEtale B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj} (k : W ⟶ U')
    (hk : Sieve.coverByImage (chartTransport B B' h S hS X) U' k)
    (U₃ : Space.SmallEtale B S hS X.obj) (n : (chartTransport B B' h S hS X).obj U₃ ⟶ W) :
    F'.obj.map n.op (glueValue x g' hg' k hk) =
      x.app U₃ (glueMap g' (n ≫ k)) (glueMap_comm g' hg' (n ≫ k)) := by
  let c := hk.some
  let p := (chartTransportFullyFaithful B B' h S hS X).preimage (n ≫ c.lift)
  have hp : (chartTransport B B' h S hS X).map p = n ≫ c.lift :=
    (chartTransportFullyFaithful B B' h S hS X).map_preimage _
  show F'.obj.map n.op (F'.obj.map c.lift.op _) = _
  rw [map_op_map_op_apply, ← hp]
  refine (x.naturality p _ _ (by
    rw [← glueMap_comp]; exact glueMap_comm g' hg' _)).symm.trans ?_
  refine x.app_congr ?_ _ _
  rw [← glueMap_comp, hp, Category.assoc, c.fac]

/-- The local sections `glueValue` form a compatible family on the sieve generated by the
transported charts mapping to `U'`. -/
theorem glueValue_compatible (hg' : U'.obj.hom ≫ ((changeBigSite B B' h S hS).map f).hom =
    yoneda.map g' ≫ ((chartTransport B B' h S hS Y).obj V).obj.hom) :
    Presieve.FamilyOfElements.Compatible (P := F'.obj)
      (R := (Sieve.coverByImage (chartTransport B B' h S hS X) U').arrows)
      (fun _ k hk => glueValue x g' hg' k hk) := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  refine section_ext fun U₃ n => ?_
  rw [map_op_map_op_apply, map_op_map_op_apply, glueValue_restrict, glueValue_restrict]
  exact x.app_congr (by rw [Category.assoc, Category.assoc, e]) _ _

/-- The section of the glued family over a chart `U'` of `X'` with a morphism to the transport
of `V`: the amalgamation of the local sections over the transported charts. -/
def glueSection (hg' : U'.obj.hom ≫ ((changeBigSite B B' h S hS).map f).hom =
    yoneda.map g' ≫ ((chartTransport B B' h S hS Y).obj V).obj.hom) : F'.obj.obj (op U') :=
  ((isSheaf_iff_isSheaf_of_type _ F'.obj).mp F'.property _
    ((chartTransport_isCoverDense B B' h S hS X).is_cover U')).amalgamate
    (fun _ k hk => glueValue x g' hg' k hk) (glueValue_compatible x g' hg')

/-- The glued section restricts, on each transported chart mapping to `U'`, to the value of the
family there. -/
theorem glueSection_restrict (hg' : U'.obj.hom ≫ ((changeBigSite B B' h S hS).map f).hom =
    yoneda.map g' ≫ ((chartTransport B B' h S hS Y).obj V).obj.hom)
    (U₃ : Space.SmallEtale B S hS X.obj)
    (n : (chartTransport B B' h S hS X).obj U₃ ⟶ U') :
    F'.obj.map n.op (glueSection x g' hg') = x.app U₃ (glueMap g' n) (glueMap_comm g' hg' n) := by
  have hv := Presieve.IsSheafFor.valid_glue (isSheafFor_coverByImage U')
    (glueValue_compatible x g' hg') n (Presieve.in_coverByImage _ n)
  have e := glueValue_restrict x g' hg' n (Presieve.in_coverByImage _ n) U₃ (𝟙 _)
  exact hv.trans ((F'.obj.map_id_apply _ _).symm.trans
    (e.trans (x.app_congr (congrArg (glueMap g') (Category.id_comp n)) _ _)))

end Glue

/-- **Gluing of a family over the transported diagrams.** -/
def glueFiber (x : FiberFamily f ((chartTransport B B' h S hS X).op ⋙ F'.obj) V) :
    FiberFamily ((changeBigSite B B' h S hS).map f) F'.obj
      ((chartTransport B B' h S hS Y).obj V) where
  app U' g' hg' := glueSection x g' hg'
  naturality {U₁ U₂} i g hg h₁ := by
    refine section_ext fun U₃ n => ?_
    rw [glueSection_restrict, ← types_comp_apply (F'.obj.map i.op) (F'.obj.map n.op),
      ← F'.obj.map_comp, ← op_comp, glueSection_restrict]
    exact x.app_congr (congrArg (descendMap h) ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ g) (Functor.map_comp _ n i).symm))) _ _

/-- **A family over the transported diagrams is the same as a family over the diagrams of `X`.**
-/
def fiberRestrictEquiv :
    FiberFamily ((changeBigSite B B' h S hS).map f) F'.obj
        ((chartTransport B B' h S hS Y).obj V) ≃
      FiberFamily f ((chartTransport B B' h S hS X).op ⋙ F'.obj) V where
  toFun := restrictFiber h f F' V
  invFun := glueFiber h f F' V
  left_inv x' := by
    ext U' g' hg'
    refine section_ext fun U₃ n => ?_
    change F'.obj.map n.op (glueSection _ g' hg') = _
    rw [glueSection_restrict, restrictFiber_app, ← x'.naturality n g' hg' (comm_precomp _ n g' hg')]
    exact x'.app_congr (map_descendMap h _) _ _
  right_inv x := by
    ext U g hg
    have e := glueSection_restrict (U' := (chartTransport B B' h S hS X).obj U) x
      ((inclusionOver h S hS).map g) (comm_transport h f hg) U (𝟙 _)
    refine (F'.obj.map_id_apply _ _).symm.trans (e.trans (x.app_congr ?_ _ _))
    exact (congrArg (descendMap h) (Category.id_comp _)).trans (descendMap_map h g)

end AlgebraicGeometry.SiteEnlargement

end
