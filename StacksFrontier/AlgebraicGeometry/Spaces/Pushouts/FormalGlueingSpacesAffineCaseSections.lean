module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFMapCompChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme

/-!
# Sections of a direct image over a chart representing the target

Let `h : P ⟶ X` be a morphism of algebraic spaces and let `Z₀` be an étale scheme chart of `X`
whose structure morphism is an isomorphism, so that `X` is represented by the scheme of `Z₀`.
Every étale scheme chart `E` of `P` then lies over `Z₀` in exactly one way, and the sections of a
direct image `h_*F` over `Z₀` are the compatible families of sections of `F` over all the étale
scheme charts of `P`: the global sections of `F`.  For `F = 𝒪_P` these are the global regular
functions on `P`.

## Main definitions

* `AlgebraicGeometry.Space.isoChartDiagram`: the unique chart diagram from a chart of `P` to
  `Z₀` over `h`.
* `AlgebraicGeometry.Space.pushforwardUnitGlobal`: a section of `h_*𝒪_P` over `Z₀`, read as a
  global regular function on `P` through its chart projections.

## Main results

* `AlgebraicGeometry.Space.bijective_pushforwardUnitGlobal`: that reading is a bijection.
* `AlgebraicGeometry.Space.modulePushforwardCounitApp_compIso`: the chart projection of the
  composition comparison of direct images is the iterated chart projection, on a composite chart
  diagram.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P X : AlgebraicSpaces B S hS}

/-- The chart diagram over `h` from an étale scheme chart `E` of `P` to a chart `Z₀` of `X`
whose structure morphism is an isomorphism. -/
abbrev isoChartDiagram (h : P ⟶ X) (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    (E : SmallEtale B S hS P.1) : ChartDiagram B S hS P.1 X.1 h.hom where
  U := E
  V := Z₀
  g := yoneda.preimage (E.1.hom ≫ h.hom ≫ inv Z₀.1.hom)
  comm := by rw [Functor.map_preimage, Category.assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

/-- A vertical morphism of a chart diagram over `h` into `Z₀` is the canonical one. -/
private theorem eq_preimage_of_comm (h : P ⟶ X) (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    {U : SmallEtale B S hS P.1}
    (g : (SmallEtale.toOver B S hS P.1).obj U ⟶ (SmallEtale.toOver B S hS X.1).obj Z₀)
    (c : U.1.hom ≫ h.hom = yoneda.map g ≫ Z₀.1.hom) :
    g = yoneda.preimage (U.1.hom ≫ h.hom ≫ inv Z₀.1.hom) := by
  apply yoneda.map_injective
  rw [Functor.map_preimage, ← Category.assoc, c, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- Every chart diagram over `h` into `Z₀` is the canonical one. -/
theorem eq_isoChartDiagram (h : P ⟶ X) (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    (d : ChartDiagram B S hS P.1 X.1 h.hom) (hd : d.V = Z₀) :
    d = isoChartDiagram B S hS h Z₀ d.U := by
  obtain ⟨U, V, g, c⟩ := d
  subst hd
  exact ChartDiagram.ext B S hS _ _ rfl rfl (heq_of_eq (eq_preimage_of_comm B S hS h V g c))

/-- Scalar multiplication on the sections of the unit module is multiplication of regular
functions. -/
theorem unitModule_smul_eq_mul' (P : AlgebraicSpaces B S hS) (W : SmallEtale B S hS P.1)
    (r : chartRing B S hS P.1 P.2 W)
    (y : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS P.1 P.2).O)).val.obj (op W)) :
    (show (structureSheaf B S hS P.1 P.2).obj.obj (op W) from r • y) =
      (show (structureSheaf B S hS P.1 P.2).obj.obj (op W) from r) *
        (show (structureSheaf B S hS P.1 P.2).obj.obj (op W) from y) :=
  rfl

/-- The chart projection of a direct image of the structure sheaf is semilinear, with the scalar
action written as multiplication of regular functions. -/
theorem modulePushforwardCounitApp_unit_smul (h : P ⟶ X)
    (d : ChartDiagram B S hS P.1 X.1 h.hom) (r : chartRing B S hS X.1 X.2 d.V)
    (x : ((modulePushforward B S hS h).obj
      (SheafOfModules.unit (structureRingSheaf B S hS P))).val.obj (op d.V)) :
    (show (structureSheaf B S hS P.1 P.2).obj.obj (op d.U) from
      modulePushforwardCounitApp B S hS h _ d (r • x)) =
      (show (structureSheaf B S hS P.1 P.2).obj.obj (op d.U) from
        chartDiagramRestrict B S hS h d r) *
        (show (structureSheaf B S hS P.1 P.2).obj.obj (op d.U) from
          modulePushforwardCounitApp B S hS h _ d x) :=
  (congrArg (fun z => (show (structureSheaf B S hS P.1 P.2).obj.obj (op d.U) from z))
    (modulePushforwardCounitApp_smul B S hS h _ d r x)).trans
    (unitModule_smul_eq_mul' B S hS P d.U _ _)

/-- A section of `h_*𝒪_P` over `Z₀`, read as a global regular function on `P`: its chart
projection at every étale scheme chart of `P`. -/
def pushforwardUnitGlobal (h : P ⟶ X) (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    (x : ((modulePushforward B S hS h).obj
      (SheafOfModules.unit (structureRingSheaf B S hS P))).val.obj (op Z₀)) :
    globalFunctions B S hS P.1 :=
  ⟨fun E => modulePushforwardCounitApp B S hS h _ (isoChartDiagram B S hS h Z₀ E.unop) x,
    fun {E E'} φ => by
      refine (modulePushforwardCounitApp_naturality B S hS h _
        (isoChartDiagram B S hS h Z₀ E.unop) (isoChartDiagram B S hS h Z₀ E'.unop) φ.unop
        (𝟙 Z₀) ?_ x).symm.trans ?_
      · apply yoneda.map_injective
        simp only [isoChartDiagram, Functor.map_comp, Functor.map_preimage]
        rw [← Category.assoc]
        exact congrArg (· ≫ h.hom ≫ inv Z₀.1.hom) (CostructuredArrow.w φ.unop.hom)
      · exact congrArg (modulePushforwardCounitApp B S hS h _
          (isoChartDiagram B S hS h Z₀ E'.unop)) (PresheafOfModules.map_id_apply _ _ _)⟩

/-- The value of the reading `pushforwardUnitGlobal` at a chart is the chart projection at any
chart diagram into `Z₀` with that source. -/
theorem pushforwardUnitGlobal_apply (h : P ⟶ X) (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    (x : ((modulePushforward B S hS h).obj
      (SheafOfModules.unit (structureRingSheaf B S hS P))).val.obj (op Z₀))
    (U : SmallEtale B S hS P.1)
    (g : (SmallEtale.toOver B S hS P.1).obj U ⟶ (SmallEtale.toOver B S hS X.1).obj Z₀)
    (c : U.1.hom ≫ h.hom = yoneda.map g ≫ Z₀.1.hom) :
    @Eq ((structurePresheaf B S hS P.1 ⋙ forget CommRingCat).obj (op U))
      ((pushforwardUnitGlobal B S hS h Z₀ x).1 (op U))
      (modulePushforwardCounitApp B S hS h (SheafOfModules.unit (structureRingSheaf B S hS P))
        ⟨U, Z₀, g, c⟩ x) := by
  obtain rfl := eq_preimage_of_comm B S hS h Z₀ g c
  rfl

/-- **The reading of sections of `h_*𝒪_P` over `Z₀` as global functions on `P` is bijective.** -/
theorem bijective_pushforwardUnitGlobal (h : P ⟶ X) (Z₀ : SmallEtale B S hS X.1)
    [IsIso Z₀.1.hom] : Function.Bijective (pushforwardUnitGlobal B S hS h Z₀) := by
  have key : ∀ (x : ((modulePushforward B S hS h).obj
      (SheafOfModules.unit (structureRingSheaf B S hS P))).val.obj (op Z₀)) j,
      directImageChartSection B S hS h _ Z₀ j x = (pushforwardUnitGlobal B S hS h Z₀ x).1 j.right :=
    fun x j => (directImageChartSection_eq_counitApp B S hS h _ Z₀ j x).trans
      (pushforwardUnitGlobal_apply B S hS h Z₀ x _ _ _).symm
  refine ⟨fun x y hxy => directImageChartSection_ext B S hS h _ Z₀ fun j => ?_, fun a => ?_⟩
  · rw [key, key, hxy]
  · refine ⟨(directImageChartSectionsEquiv B S hS h _ Z₀).symm
      ⟨fun j => a.1 j.right, fun {j j'} φ => a.2 φ.right⟩, ?_⟩
    refine Subtype.ext (funext fun E => ?_)
    have h1 := key ((directImageChartSectionsEquiv B S hS h _ Z₀).symm
      ⟨fun j => a.1 j.right, fun {j j'} φ => a.2 φ.right⟩)
      (indexOfChartDiagram B S hS h (isoChartDiagram B S hS h Z₀ E.unop))
    refine h1.symm.trans ((directImageChartSectionsEquiv_apply B S hS h _ Z₀ _ _).symm.trans ?_)
    rw [Equiv.apply_symm_apply]
    rfl

/-- **The reading of sections as global functions is semilinear**: the scalar action of
`Γ(Z₀)` becomes multiplication by the pulled-back function. -/
theorem pushforwardUnitGlobal_smul (h : P ⟶ X) (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    (r : chartRing B S hS X.1 X.2 Z₀)
    (x : ((modulePushforward B S hS h).obj
      (SheafOfModules.unit (structureRingSheaf B S hS P))).val.obj (op Z₀)) :
    pushforwardUnitGlobal B S hS h Z₀ (r • x) =
      pullbackToGlobalFunctions B S hS P ((SmallEtale.toOver B S hS X.1).obj Z₀)
          (ObjectProperty.homMk (h.hom ≫ (asIso Z₀.1.hom).inv)) r *
        pushforwardUnitGlobal B S hS h Z₀ x :=
  Subtype.ext <| funext fun E =>
    modulePushforwardCounitApp_unit_smul B S hS h (isoChartDiagram B S hS h Z₀ E.unop) r x

/-! ### The chart projection of the composition comparison -/

section Comp

variable {X' Y' Z' : AlgebraicSpaces B S hS} (f : X' ⟶ Y') (g : Y' ⟶ Z')
    {U : SmallEtale B S hS X'.1} {V : SmallEtale B S hS Y'.1} {W : SmallEtale B S hS Z'.1}
    (a : (SmallEtale.toOver B S hS X'.1).obj U ⟶ (SmallEtale.toOver B S hS Y'.1).obj V)
    (b : (SmallEtale.toOver B S hS Y'.1).obj V ⟶ (SmallEtale.toOver B S hS Z'.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)

/-- **The chart projection of the composition comparison `g_* f_* ≅ (f ≫ g)_*` is the iterated
chart projection**, at a composite chart diagram. -/
theorem modulePushforwardCounitApp_compIso (F : Modules.{u, u} B S hS X'.1 X'.2)
    (s : ((modulePushforward B S hS g).obj ((modulePushforward B S hS f).obj F)).val.obj (op W)) :
    modulePushforwardCounitApp B S hS (f ≫ g) F (ChartDiagram.comp B S hS f g a b ha hb)
        (((modulePushforwardCompIso B S hS f g).hom.app F).val.app (op W) s) =
      modulePushforwardCounitApp B S hS f F ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS g _ ⟨V, W, b, hb⟩ s) := by
  have h := ModuleFMap.compOfIso_app B S hS f g a b ha hb F ((modulePushforward B S hS f).obj F)
    ((modulePushforward B S hS g).obj ((modulePushforward B S hS f).obj F))
    (modulePushforwardCounit B S hS g _) (modulePushforwardCounit B S hS f F)
    (modulePushforwardCompIso B S hS f g)
    (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS f g F) s
  rw [ModuleFMap.compOfIso, moduleFMapCompHom_eq, moduleFMapHom_modulePushforwardCounit,
    moduleFMapHom_modulePushforwardCounit, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp] at h
  have e1 : ∀ (H : Modules.{u, u} B S hS Z'.1 Z'.2)
      (q : H ⟶ (modulePushforward B S hS (f ≫ g)).obj F) (x : H.val.obj (op W)),
      (modulePushforwardHomFMap B S hS (f ≫ g) F H q).app
          (ChartDiagram.comp B S hS f g a b ha hb) x =
        modulePushforwardCounitApp B S hS (f ≫ g) F (ChartDiagram.comp B S hS f g a b ha hb)
          (q.val.app (op W) x) := fun _ _ _ => rfl
  rwa [e1] at h

/-- The same at a chart diagram over `f ≫ g` whose vertical morphism is equal to `a ≫ b`. -/
theorem modulePushforwardCounitApp_compIso' (F : Modules.{u, u} B S hS X'.1 X'.2)
    (k : (SmallEtale.toOver B S hS X'.1).obj U ⟶ (SmallEtale.toOver B S hS Z'.1).obj W)
    (hk : U.1.hom ≫ (f ≫ g).hom = yoneda.map k ≫ W.1.hom) (hab : k = a ≫ b)
    (s : ((modulePushforward B S hS g).obj ((modulePushforward B S hS f).obj F)).val.obj (op W)) :
    modulePushforwardCounitApp B S hS (f ≫ g) F ⟨U, W, k, hk⟩
        (((modulePushforwardCompIso B S hS f g).hom.app F).val.app (op W) s) =
      modulePushforwardCounitApp B S hS f F ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS g _ ⟨V, W, b, hb⟩ s) := by
  subst hab
  exact modulePushforwardCounitApp_compIso B S hS f g a b ha hb F s

/-- **The global function of a section of a composite direct image, at a chart**: the iterated
chart projection, through any chart diagram over the first morphism. -/
theorem pushforwardUnitGlobal_compIso_apply (Z₀ : SmallEtale B S hS Z'.1) [IsIso Z₀.1.hom]
    (s : ((modulePushforward B S hS g).obj ((modulePushforward B S hS f).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X')))).val.obj (op Z₀))
    (U₁ : SmallEtale B S hS X'.1) (V₁ : SmallEtale B S hS Y'.1)
    (a₁ : (SmallEtale.toOver B S hS X'.1).obj U₁ ⟶ (SmallEtale.toOver B S hS Y'.1).obj V₁)
    (ha₁ : U₁.1.hom ≫ f.hom = yoneda.map a₁ ≫ V₁.1.hom) :
    @Eq ((structurePresheaf B S hS X'.1 ⋙ forget CommRingCat).obj (op U₁))
      ((pushforwardUnitGlobal B S hS (f ≫ g) Z₀
        (((modulePushforwardCompIso B S hS f g).hom.app _).val.app (op Z₀) s)).1 (op U₁))
      (modulePushforwardCounitApp B S hS f _ ⟨U₁, V₁, a₁, ha₁⟩
        (modulePushforwardCounitApp B S hS g _ (isoChartDiagram B S hS g Z₀ V₁) s)) :=
  (pushforwardUnitGlobal_apply B S hS (f ≫ g) Z₀
    (((modulePushforwardCompIso B S hS f g).hom.app _).val.app (op Z₀) s) U₁
    (a₁ ≫ yoneda.preimage (V₁.1.hom ≫ g.hom ≫ inv Z₀.1.hom))
    (ChartDiagram.comp B S hS f g (W := Z₀) a₁
      (yoneda.preimage (V₁.1.hom ≫ g.hom ≫ inv Z₀.1.hom)) ha₁
      (isoChartDiagram B S hS g Z₀ V₁).comm).comm).trans
    (modulePushforwardCounitApp_compIso B S hS f g (U := U₁) (V := V₁) (W := Z₀) a₁
      (yoneda.preimage (V₁.1.hom ≫ g.hom ≫ inv Z₀.1.hom)) ha₁
      (isoChartDiagram B S hS g Z₀ V₁).comm _ s)

end Comp

end AlgebraicGeometry.Space
