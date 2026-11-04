module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackRigidification
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting
public import StacksFrontier.CategoryTheory.Comma.CostructuredArrowIsoTerminal

/-!
# Endomorphisms of the structure module of a scheme regarded as an algebraic space

Let `V` be a scheme of the big fppf site over `S`, regarded as the algebraic space
`schemeSpace V`.  The endomorphisms of the structure module `𝒪_V` on the small étale site of
that algebraic space are the global regular functions `Γ(V, 𝒪_V)`, the endomorphism `f`
corresponding to its value `f(1)` over the identity chart.  This identification turns composition
into multiplication, identifies the automorphisms of `𝒪_V` with the units of `Γ(V, 𝒪_V)`, and is
compatible with inverse image along a morphism `g : V' ⟶ V` of schemes, which acts on global
functions by `g^♯ : Γ(V, 𝒪_V) ⟶ Γ(V', 𝒪_{V'})`.

## Main definitions

* `AlgebraicGeometry.Space.idEtaleChartIsTerminal`: the identity chart of a scheme is a terminal
  object of the small étale site of the algebraic space it represents.
* `AlgebraicGeometry.Space.structureModuleHomEquiv`: morphisms `𝒪_V ⟶ M` are the sections of
  `M` over the identity chart.
* `AlgebraicGeometry.Space.structureModuleEndEquiv`: **endomorphisms of `𝒪_V` are the global
  functions `Γ(V, 𝒪_V)`**, with its multiplicative form
  `AlgebraicGeometry.Space.structureModuleEndMulEquiv`.
* `AlgebraicGeometry.Space.structureModuleAutEquiv`: **automorphisms of `𝒪_V` are the units of
  `Γ(V, 𝒪_V)`**.

## Main results

* `AlgebraicGeometry.Space.structureModule_hom_ext`: a morphism out of `𝒪_V` is determined by
  its value at `1` over the identity chart; hence the instances
  `AlgebraicGeometry.Space.small_structureModule_hom` and
  `AlgebraicGeometry.Space.small_structureModule_iso`.
* `AlgebraicGeometry.Space.structureModuleEndEquiv_comp` and
  `AlgebraicGeometry.Space.structureModuleEndEquiv_id`: composition is multiplication.
* `AlgebraicGeometry.Space.structureModuleEndEquiv_conj`: **the inverse image along
  `g : V' ⟶ V`, conjugated by the identifications `𝒪_{V'} ≅ g^*𝒪_V`, acts on global functions
  by `g^♯`**; `AlgebraicGeometry.Space.structureModuleAutEquiv_conj` is its form for
  automorphisms and units.

## Implementation notes

The identification of morphisms out of `𝒪_V` with sections over the identity chart is Mathlib's
`SheafOfModules.unitHomEquiv` (morphisms out of the free module of rank one are global
sections) followed by `PresheafOfModules.sectionsEquivObjOfIsTerminal`: the identity chart
`CostructuredArrow.mk (𝟙 (yoneda.obj V))` is terminal, so a global section is its value there.
The structure ring over the identity chart is `Γ(V, ⊤)` by definition, so
`AlgebraicGeometry.Space.structureModuleEndEquiv` lands in `Γ(V, ⊤)` with no transport.

The compatibility with inverse image is computed at the diagram
`AlgebraicGeometry.Space.idEtaleChartDiagram` of the two identity charts with vertical morphism
`g`, where restriction of functions is `g^♯` by definition.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0D2A](https://stacks.math.columbia.edu/tag/0D2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- The identity chart of a scheme is terminal in the small étale site of the algebraic space it
represents. -/
def idEtaleChartIsTerminal (V : BigFppfOver B S hS) : IsTerminal (idEtaleChart B S hS V) :=
  ObjectProperty.isTerminal_of_isTerminal_obj _
    (CostructuredArrow.mkIdTerminal (S := yoneda) (Y := V))

/-- **Morphisms out of the structure module of a scheme are the sections over the identity
chart**: a morphism `f : 𝒪_V ⟶ M` corresponds to `f(1)` over the identity chart. -/
def structureModuleHomEquiv (V : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj V).1
      ((schemeSpaceFunctor B S hS).obj V).2) :
    (structureModule ((schemeSpaceFunctor B S hS).obj V) ⟶ M) ≃
      M.val.obj (op (idEtaleChart B S hS V)) :=
  (SheafOfModules.unitHomEquiv M).trans
    (PresheafOfModules.sectionsEquivObjOfIsTerminal M.val (idEtaleChartIsTerminal B S hS V))

/-- `AlgebraicGeometry.Space.structureModuleHomEquiv` is evaluation at `1` over the identity
chart. -/
theorem structureModuleHomEquiv_apply (V : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj V).1
      ((schemeSpaceFunctor B S hS).obj V).2)
    (f : structureModule ((schemeSpaceFunctor B S hS).obj V) ⟶ M) :
    structureModuleHomEquiv V M f = f.val.app (op (idEtaleChart B S hS V))
      (1 : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :=
  rfl

/-- **Endomorphisms of the structure module of a scheme are its global regular functions**: an
endomorphism `f` of `𝒪_V` corresponds to its value `f(1) ∈ Γ(V, ⊤)` over the identity chart,
whose ring of functions is `Γ(V, ⊤)` by definition. -/
def structureModuleEndEquiv (V : BigFppfOver B S hS) :
    (structureModule ((schemeSpaceFunctor B S hS).obj V) ⟶
      structureModule ((schemeSpaceFunctor B S hS).obj V)) ≃
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  structureModuleHomEquiv V (structureModule ((schemeSpaceFunctor B S hS).obj V))

/-- `AlgebraicGeometry.Space.structureModuleEndEquiv` is evaluation at `1` over the identity
chart. -/
theorem structureModuleEndEquiv_apply (V : BigFppfOver B S hS)
    (f : structureModule ((schemeSpaceFunctor B S hS).obj V) ⟶
      structureModule ((schemeSpaceFunctor B S hS).obj V)) :
    structureModuleEndEquiv V f = f.val.app (op (idEtaleChart B S hS V))
      (1 : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :=
  rfl

/-- Composition of endomorphisms of `𝒪_V` is multiplication of global functions:
`(f ≫ g)(1) = f(1) • g(1)`. -/
theorem structureModuleEndEquiv_comp (V : BigFppfOver B S hS)
    (f g : structureModule ((schemeSpaceFunctor B S hS).obj V) ⟶
      structureModule ((schemeSpaceFunctor B S hS).obj V)) :
    structureModuleEndEquiv V (f ≫ g) =
      structureModuleEndEquiv V f * structureModuleEndEquiv V g := by
  have h := (g.val.app (op (idEtaleChart B S hS V))).hom.map_smul
    (structureModuleEndEquiv V f) (1 : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  exact (congrArg (g.val.app (op (idEtaleChart B S hS V))).hom
    (mul_one (structureModuleEndEquiv V f)).symm).trans h

/-- The identity of `𝒪_V` corresponds to the global function `1`. -/
theorem structureModuleEndEquiv_id (V : BigFppfOver B S hS) :
    structureModuleEndEquiv V (𝟙 _) = 1 :=
  rfl

/-- **A morphism out of the structure module of a scheme is determined by its value at `1` over
the identity chart.** -/
theorem structureModule_hom_ext {V : BigFppfOver B S hS}
    {M : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj V).1
      ((schemeSpaceFunctor B S hS).obj V).2}
    {f g : structureModule ((schemeSpaceFunctor B S hS).obj V) ⟶ M}
    (h : f.val.app (op (idEtaleChart B S hS V)) (1 : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) =
      g.val.app (op (idEtaleChart B S hS V)) (1 : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :
    f = g :=
  (structureModuleHomEquiv V M).injective h

/-- The morphisms out of the structure module of a scheme form a `u`-small type. -/
instance small_structureModule_hom (V : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj V).1
      ((schemeSpaceFunctor B S hS).obj V).2) :
    Small.{u} (structureModule ((schemeSpaceFunctor B S hS).obj V) ⟶ M) :=
  small_of_injective (structureModuleHomEquiv V M).injective

/-- The isomorphisms out of the structure module of a scheme form a `u`-small type. -/
instance small_structureModule_iso (V : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj V).1
      ((schemeSpaceFunctor B S hS).obj V).2) :
    Small.{u} (structureModule ((schemeSpaceFunctor B S hS).obj V) ≅ M) :=
  small_of_injective (f := fun e : structureModule ((schemeSpaceFunctor B S hS).obj V) ≅ M ↦ e.hom)
    fun _ _ h ↦ Iso.ext h

/-- The diagram of étale charts formed by the identity charts of `V'` and `V` with vertical
morphism `g : V' ⟶ V`, over the morphism of algebraic spaces
`(schemeSpaceFunctor B S hS).map g`. -/
abbrev idEtaleChartDiagram {V V' : BigFppfOver B S hS} (g : V' ⟶ V) :
    ChartDiagram B S hS ((schemeSpaceFunctor B S hS).obj V').1
      ((schemeSpaceFunctor B S hS).obj V).1 ((schemeSpaceFunctor B S hS).map g).hom where
  U := idEtaleChart B S hS V'
  V := idEtaleChart B S hS V
  g := g
  comm := (Category.id_comp _).trans (Category.comp_id _).symm

/-- **Inverse image of endomorphisms of the structure module is pullback of global functions.**
For `g : V' ⟶ V`, the inverse image along `g` of an endomorphism `f` of `𝒪_V`, conjugated by the
identification `𝒪_{V'} ≅ g^*𝒪_V`, is the endomorphism of `𝒪_{V'}` given by `g^♯` of the global
function of `f`. -/
theorem structureModuleEndEquiv_conj {V V' : BigFppfOver B S hS} (g : V' ⟶ V)
    (f : structureModule ((schemeSpaceFunctor B S hS).obj V) ⟶
      structureModule ((schemeSpaceFunctor B S hS).obj V)) :
    structureModuleEndEquiv V'
        ((structureModulePullbackIso ((schemeSpaceFunctor B S hS).map g)).hom ≫
          (modulePullback B S hS ((schemeSpaceFunctor B S hS).map g)).map f ≫
          (structureModulePullbackIso ((schemeSpaceFunctor B S hS).map g)).inv) =
      ((BigFppfOver.toScheme B S hS).map g).appTop (structureModuleEndEquiv V f) := by
  let d := idEtaleChartDiagram g
  have h1 := modulePullbackUnitIso_inv_val_app_one B S hS ((schemeSpaceFunctor B S hS).map g) d
  have h2 := modulePullbackChartSection_map B S hS ((schemeSpaceFunctor B S hS).map g) _ f d
    (1 : chartRing B S hS ((schemeSpaceFunctor B S hS).obj V).1
      ((schemeSpaceFunctor B S hS).obj V).2 d.V)
  have h3 := modulePullbackChartSection_unit B S hS ((schemeSpaceFunctor B S hS).map g) d
    (structureModuleEndEquiv V f)
  have h4 := ((modulePullbackUnitIso B S hS ((schemeSpaceFunctor B S hS).map g)).hom.val.app
    (op d.U)).hom.map_smul
    (chartDiagramRestrict B S hS ((schemeSpaceFunctor B S hS).map g) d
      (structureModuleEndEquiv V f))
    ((modulePullbackUnitIso B S hS ((schemeSpaceFunctor B S hS).map g)).inv.val.app (op d.U)
      (1 : chartRing B S hS ((schemeSpaceFunctor B S hS).obj V').1
        ((schemeSpaceFunctor B S hS).obj V').2 d.U))
  have h5 : (modulePullbackUnitIso B S hS ((schemeSpaceFunctor B S hS).map g)).hom.val.app (op d.U)
      ((modulePullbackUnitIso B S hS ((schemeSpaceFunctor B S hS).map g)).inv.val.app (op d.U)
        (1 : chartRing B S hS ((schemeSpaceFunctor B S hS).obj V').1
          ((schemeSpaceFunctor B S hS).obj V').2 d.U)) =
      (1 : chartRing B S hS ((schemeSpaceFunctor B S hS).obj V').1
        ((schemeSpaceFunctor B S hS).obj V').2 d.U) :=
    congrArg (fun m : structureModule ((schemeSpaceFunctor B S hS).obj V') ⟶
      structureModule ((schemeSpaceFunctor B S hS).obj V') ↦
      m.val.app (op d.U) (1 : chartRing B S hS ((schemeSpaceFunctor B S hS).obj V').1
        ((schemeSpaceFunctor B S hS).obj V').2 d.U))
      (modulePullbackUnitIso B S hS ((schemeSpaceFunctor B S hS).map g)).inv_hom_id
  let H := modulePullbackUnitIso B S hS ((schemeSpaceFunctor B S hS).map g)
  exact (congrArg (fun x ↦ H.hom.val.app (op d.U)
      (((modulePullback B S hS ((schemeSpaceFunctor B S hS).map g)).map f).val.app
        (op d.U) x)) h1).trans
    ((congrArg (fun x ↦ H.hom.val.app (op d.U) x) h2).trans
      ((congrArg (fun x ↦ H.hom.val.app (op d.U) x) h3).trans
        (h4.trans ((congrArg (fun x ↦
          chartDiagramRestrict B S hS ((schemeSpaceFunctor B S hS).map g) d
            (structureModuleEndEquiv V f) • x)
          h5).trans (mul_one
            (chartDiagramRestrict B S hS ((schemeSpaceFunctor B S hS).map g) d
              (structureModuleEndEquiv V f)))))))

/-- The endomorphism of `𝒪_V` given by a product of global functions is the composite of the
endomorphisms given by the factors. -/
theorem structureModuleEndEquiv_symm_mul (V : BigFppfOver B S hS)
    (a b : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (structureModuleEndEquiv V).symm (a * b) =
      (structureModuleEndEquiv V).symm a ≫ (structureModuleEndEquiv V).symm b :=
  (structureModuleEndEquiv V).injective (by
    simp only [structureModuleEndEquiv_comp, Equiv.apply_symm_apply])

/-- The endomorphism of `𝒪_V` given by the global function `1` is the identity. -/
theorem structureModuleEndEquiv_symm_one (V : BigFppfOver B S hS) :
    (structureModuleEndEquiv V).symm 1 = 𝟙 _ :=
  (structureModuleEndEquiv V).symm_apply_eq.2 (structureModuleEndEquiv_id V).symm

/-- `AlgebraicGeometry.Space.structureModuleEndEquiv` as an isomorphism of monoids from the
endomorphism monoid `End 𝒪_V`, whose multiplication is composition in the reverse order;
`Γ(V, ⊤)` being commutative, the order does not matter. -/
def structureModuleEndMulEquiv (V : BigFppfOver B S hS) :
    End (structureModule ((schemeSpaceFunctor B S hS).obj V)) ≃*
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  { structureModuleEndEquiv V with
    map_mul' f g := (structureModuleEndEquiv_comp V g f).trans (mul_comm _ _) }

/-- `AlgebraicGeometry.Space.structureModuleEndMulEquiv` is
`AlgebraicGeometry.Space.structureModuleEndEquiv`. -/
theorem structureModuleEndMulEquiv_apply (V : BigFppfOver B S hS)
    (f : End (structureModule ((schemeSpaceFunctor B S hS).obj V))) :
    structureModuleEndMulEquiv V f = structureModuleEndEquiv V f :=
  rfl

/-- **Automorphisms of the structure module of a scheme are the units of its global regular
functions**: `AlgebraicGeometry.Space.structureModuleEndMulEquiv` on units, the automorphisms of
an object being the units of its endomorphism monoid (`CategoryTheory.Aut.unitsEndEquivAut`). -/
def structureModuleAutEquiv (V : BigFppfOver B S hS) :
    (structureModule ((schemeSpaceFunctor B S hS).obj V) ≅
      structureModule ((schemeSpaceFunctor B S hS).obj V)) ≃
      (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))ˣ :=
  (Aut.unitsEndEquivAut _).symm.toEquiv.trans
    (Units.mapEquiv (structureModuleEndMulEquiv V)).toEquiv

/-- The unit attached to an automorphism `e` of `𝒪_V` is the global function of `e.hom`. -/
@[simp]
theorem val_structureModuleAutEquiv (V : BigFppfOver B S hS)
    (e : structureModule ((schemeSpaceFunctor B S hS).obj V) ≅
      structureModule ((schemeSpaceFunctor B S hS).obj V)) :
    ((structureModuleAutEquiv V e : (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))ˣ) :
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) =
      structureModuleEndEquiv V e.hom :=
  rfl

/-- The inverse of the unit attached to an automorphism `e` of `𝒪_V` is the global function of
`e.inv`. -/
@[simp]
theorem val_inv_structureModuleAutEquiv (V : BigFppfOver B S hS)
    (e : structureModule ((schemeSpaceFunctor B S hS).obj V) ≅
      structureModule ((schemeSpaceFunctor B S hS).obj V)) :
    (((structureModuleAutEquiv V e)⁻¹ : (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))ˣ) :
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) =
      structureModuleEndEquiv V e.inv :=
  rfl

/-- The automorphism of `𝒪_V` attached to a unit `a` has the endomorphism of `a` as its
underlying morphism. -/
@[simp]
theorem structureModuleAutEquiv_symm_apply_hom (V : BigFppfOver B S hS)
    (a : (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))ˣ) :
    ((structureModuleAutEquiv V).symm a).hom = (structureModuleEndEquiv V).symm a :=
  rfl

/-- Composition of automorphisms of `𝒪_V` is multiplication of units. -/
theorem structureModuleAutEquiv_trans (V : BigFppfOver B S hS)
    (e e' : structureModule ((schemeSpaceFunctor B S hS).obj V) ≅
      structureModule ((schemeSpaceFunctor B S hS).obj V)) :
    structureModuleAutEquiv V (e ≪≫ e') =
      structureModuleAutEquiv V e * structureModuleAutEquiv V e' :=
  Units.ext (structureModuleEndEquiv_comp V e.hom e'.hom)

/-- The identity automorphism of `𝒪_V` corresponds to the unit `1`. -/
theorem structureModuleAutEquiv_refl (V : BigFppfOver B S hS) :
    structureModuleAutEquiv V (Iso.refl _) = 1 :=
  Units.ext (structureModuleEndEquiv_id V)

/-- **Inverse image of automorphisms of the structure module is pullback of units**: the form of
`AlgebraicGeometry.Space.structureModuleEndEquiv_conj` for automorphisms, the conjugated inverse
image of `e` corresponding to the image of its unit under `g^♯`. -/
theorem structureModuleAutEquiv_conj {V V' : BigFppfOver B S hS} (g : V' ⟶ V)
    (e : structureModule ((schemeSpaceFunctor B S hS).obj V) ≅
      structureModule ((schemeSpaceFunctor B S hS).obj V)) :
    structureModuleAutEquiv V'
        (structureModulePullbackIso ((schemeSpaceFunctor B S hS).map g) ≪≫
          (modulePullback B S hS ((schemeSpaceFunctor B S hS).map g)).mapIso e ≪≫
          (structureModulePullbackIso ((schemeSpaceFunctor B S hS).map g)).symm) =
      Units.map ((BigFppfOver.toScheme B S hS).map g).appTop.hom.toMonoidHom
        (structureModuleAutEquiv V e) :=
  Units.ext (structureModuleEndEquiv_conj g e.hom)

end AlgebraicGeometry.Space

end
