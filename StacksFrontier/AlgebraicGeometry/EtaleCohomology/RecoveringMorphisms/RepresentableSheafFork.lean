module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Faithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RepresentableEqualizer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability

/-!
# The representable sheaf of an affine étale chart, as a fork of the structure sheaf

Let `Y = Spec B` be an affine scheme of a big étale site, let `V` be an affine object of the
small étale site of `Y` and let `Γ(V, ⊤) = B[x₁, …, x_n]/(P₁, …, P_n)` be a standard
presentation.  Step (2) of the proof of [Stacks Project, Tag 04I6] reads the representable
sheaf `h_V` on `Y_étale` as the equalizer

`h_V ⟶ ∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y`,

the two maps being `a ↦ (Pⱼ(a))ⱼ` and the zero section.  This file states that presentation at
the level of *sheaves* on `Y_étale`.  The equalizer is written through its universal property,
with the `n`-fold product `∏ᵢ 𝒪_Y` replaced by an `n`-tuple of morphisms into `𝒪_Y`:
`AlgebraicGeometry.existsUnique_hom_smallEtaleYoneda_of_isSolution` says that a sheaf `F` on
`Y_étale` equipped with `n` morphisms `F ⟶ 𝒪_Y` whose values are everywhere a solution of the
system admits a unique morphism `F ⟶ h_V` inducing them.  That is exactly the "unique dotted
arrow" of the source, and it avoids naming a product object.

The underlying bijection is `Stacks.EtaleCohomology.homOverEquivSolutions`, transported from
morphisms of schemes over `Y` to morphisms of the small étale site along the full faithfulness
of `AlgebraicGeometry.SmallEtale.toScheme` on the slice over `Y`.

## Main definitions

* `AlgebraicGeometry.smallEtaleHomEquivSchemeHomOver` — a morphism of the small étale site of
  `Y` is a morphism of schemes over `Y`.
* `AlgebraicGeometry.smallEtaleHomEquivSolutions` — the sections of `h_V` over an étale chart
  `U` are the solutions over `Γ(U, ⊤)` of the presented system.
* `AlgebraicGeometry.smallEtaleYonedaCoordinate` — the `i`-th coordinate of a chart-valued
  point of `V`, as a morphism of sheaves `h_V ⟶ 𝒪_Y`.

## Main results

* `AlgebraicGeometry.isSolution_smallEtaleYonedaCoordinate` — the `n` coordinates of a
  chart-valued point of `V` are a solution of the system; i.e. the fork
  `h_V ⟶ ∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y` commutes.
* `AlgebraicGeometry.existsUnique_hom_smallEtaleYoneda_of_isSolution` — **step (2) of the
  proof of [Stacks Project, Tag 04I6] at the level of sheaves**: that fork is a limit.
* `AlgebraicGeometry.hom_smallEtaleYoneda_ext` — two morphisms into `h_V` agreeing on all `n`
  coordinates are equal, the separated half of the universal property on its own.

## Implementation notes

The representable sheaf is `AlgebraicGeometry.smallEtaleYoneda`, a sheaf because the small
étale topology is subcanonical (`AlgebraicGeometry.SmallEtale.topology_subcanonical`), and the
structure sheaf of sets is `AlgebraicGeometry.setStructureSheaf`.  Both take values in `Type u`
for a scheme universe `u`, so no universe lifting appears.

Étaleness of `V ⟶ Y` is not used, exactly as in `Stacks.EtaleCohomology.homOverEquivSolutions`:
what is used is affineness of `Y` and of `V` together with the supplied presentation.  For `V`
étale over `Y` the presentation exists by [Stacks Project, Tag 00U9].

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}} {Y : B.Scheme}

/-- A morphism `U ⟶ V` of the small étale site of `Y` is the same thing as a morphism of
schemes `U ⟶ V` commuting with the two structure morphisms to `Y`: the small étale site is a
full subcategory of the slice over `Y`, and the big étale site is a full subcategory of
schemes. -/
def smallEtaleHomEquivSchemeHomOver (U V : SmallEtale B Y.obj Y.property) :
    (U ⟶ V) ≃
      {f : (SmallEtale.toScheme B Y.obj Y.property).obj U ⟶
          (SmallEtale.toScheme B Y.obj Y.property).obj V //
        f ≫ B.inclusion.map V.obj.hom = B.inclusion.map U.obj.hom} where
  toFun f := ⟨(SmallEtale.toScheme B Y.obj Y.property).map f,
    (B.inclusion.map_comp f.hom.left V.obj.hom).symm.trans
      (congrArg B.inclusion.map (Over.w f.hom))⟩
  invFun f := ObjectProperty.homMk (Over.homMk (B.inclusion.preimage f.1)
    (B.inclusion.map_injective
      ((B.inclusion.map_comp _ V.obj.hom).trans
        ((congrArg (· ≫ B.inclusion.map V.obj.hom) (B.inclusion.map_preimage f.1)).trans f.2))))
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact B.inclusion.preimage_map f.hom.left
  right_inv f := Subtype.ext (B.inclusion.map_preimage f.1)

/-- The scheme morphism underlying `smallEtaleHomEquivSchemeHomOver U V f` is the image of `f`
under `AlgebraicGeometry.SmallEtale.toScheme`. -/
@[simp]
theorem smallEtaleHomEquivSchemeHomOver_apply_coe {U V : SmallEtale B Y.obj Y.property}
    (f : U ⟶ V) :
    (smallEtaleHomEquivSchemeHomOver U V f).1 =
      (SmallEtale.toScheme B Y.obj Y.property).map f :=
  rfl

/-- Two morphisms of sheaves of sets are equal if they agree on every section. -/
private theorem sheaf_hom_ext_of_apply_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type u)} {φ ψ : F ⟶ G}
    (h : ∀ (U : Cᵒᵖ) (t : F.obj.obj U), φ.hom.app U t = ψ.hom.app U t) : φ = ψ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => TypeCat.homEquiv.injective (funext (h U))))

/-- Equal morphisms of sheaves of sets take equal values on every section. -/
private theorem sheaf_hom_apply_congr {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type u)} {φ ψ : F ⟶ G} (h : φ = ψ) (U : Cᵒᵖ) (t : F.obj.obj U) :
    φ.hom.app U t = ψ.hom.app U t :=
  congrArg (fun α : F ⟶ G => α.hom.app U t) h

section Presentation

variable [IsAffine (B.inclusion.obj Y)] (V : SmallEtale B Y.obj Y.property)
  [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)] {n : ℕ}
  (P : Fin n → MvPolynomial (Fin n) Γ(B.inclusion.obj Y, ⊤))
  (pres : Stacks.EtaleCohomology.StandardPresentationOver
    ((SmallEtale.toScheme B Y.obj Y.property).obj V) (B.inclusion.map V.obj.hom) P)

/-- **The sections of `h_V` over an étale chart are the solutions of the presented system.**
This is `Stacks.EtaleCohomology.homOverEquivSolutions` read on the small étale site of `Y`. -/
def smallEtaleHomEquivSolutions (U : SmallEtale B Y.obj Y.property) :
    (U ⟶ V) ≃
      {a : Fin n → Γ((SmallEtale.toScheme B Y.obj Y.property).obj U, ⊤) //
        MvPolynomial.IsSolution P (B.inclusion.map U.obj.hom).appTop.hom a} :=
  (smallEtaleHomEquivSchemeHomOver U V).trans
    (Stacks.EtaleCohomology.homOverEquivSolutions _ _ _ _ P pres)

/-- The identification of the sections of `h_V` with solutions is natural in the chart: the
solution naming `k ≫ f` is the restriction along `k` of the solution naming `f`. -/
theorem smallEtaleHomEquivSolutions_naturality {U U' : SmallEtale B Y.obj Y.property}
    (k : U' ⟶ U) (f : U ⟶ V) (i : Fin n) :
    (smallEtaleHomEquivSolutions V P pres U' (k ≫ f)).1 i =
      ((SmallEtale.toScheme B Y.obj Y.property).map k).appTop
        ((smallEtaleHomEquivSolutions V P pres U f).1 i) :=
  Stacks.EtaleCohomology.homOverEquivSolutions_naturality pres
    ((SmallEtale.toScheme B Y.obj Y.property).map k)
    ((B.inclusion.map_comp k.hom.left U.obj.hom).symm.trans
      (congrArg B.inclusion.map (Over.w k.hom)))
    (smallEtaleHomEquivSchemeHomOver U V f) i

/-- **The `i`-th coordinate of a chart-valued point of `V`, as a morphism of sheaves
`h_V ⟶ 𝒪_Y`.**  Over an étale chart `U` it sends a `Y`-morphism `U ⟶ V` to the `i`-th entry of
the solution of the presented system that names it; this is the `i`-th component of the map
`h_V ⟶ ∏ᵢ 𝒪_Y` of step (2) of the proof of [Stacks Project, Tag 04I6]. -/
def smallEtaleYonedaCoordinate (i : Fin n) :
    (smallEtaleYoneda B Y.obj Y.property).obj V ⟶ setStructureSheaf B Y.obj Y.property where
  hom :=
    { app := fun U => TypeCat.ofHom fun f => (smallEtaleHomEquivSolutions V P pres U.unop f).1 i
      naturality := fun _ _ k => TypeCat.homEquiv.injective (funext fun f =>
        smallEtaleHomEquivSolutions_naturality V P pres k.unop f i) }

/-- Over a chart `U`, the `i`-th coordinate sends `f : U ⟶ V` to the `i`-th entry of
`smallEtaleHomEquivSolutions V P pres U f`. -/
@[simp]
theorem smallEtaleYonedaCoordinate_hom_app (i : Fin n)
    (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) (f : U.unop ⟶ V) :
    (smallEtaleYonedaCoordinate V P pres i).hom.app U f =
      (smallEtaleHomEquivSolutions V P pres U.unop f).1 i :=
  rfl

/-- **The fork `h_V ⟶ ∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y` commutes.**  The `n` coordinates of a chart-valued point
of `V` are a solution of the presented system, so the two maps of step (2) of the proof of
[Stacks Project, Tag 04I6] — evaluation of the `Pⱼ` and the zero section — agree on `h_V`. -/
theorem isSolution_smallEtaleYonedaCoordinate
    (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) (f : U.unop ⟶ V) :
    MvPolynomial.IsSolution P (B.inclusion.map U.unop.obj.hom).appTop.hom
      (fun i => (smallEtaleYonedaCoordinate V P pres i).hom.app U f) :=
  (smallEtaleHomEquivSolutions V P pres U.unop f).2

/-- Two morphisms of sheaves into `h_V` which agree on all `n` coordinates are equal: the
coordinates jointly determine a chart-valued point of `V`. -/
theorem hom_smallEtaleYoneda_ext {F : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type u)}
    (φ ψ : F ⟶ (smallEtaleYoneda B Y.obj Y.property).obj V)
    (h : ∀ i, φ ≫ smallEtaleYonedaCoordinate V P pres i =
      ψ ≫ smallEtaleYonedaCoordinate V P pres i) :
    φ = ψ := by
  refine sheaf_hom_ext_of_apply_eq fun U t => ?_
  refine (smallEtaleHomEquivSolutions V P pres U.unop).injective
    (Subtype.ext (funext fun i => ?_))
  exact sheaf_hom_apply_congr (h i) U t

/-- **Step (2) of the proof of [Stacks Project, Tag 04I6], at the level of sheaves: the fork
`h_V ⟶ ∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y` is a limit.**  Let `Y` be an affine scheme of a big étale site, let
`V` be an affine object of the small étale site of `Y` with a standard presentation
`Γ(V, ⊤) = Γ(Y, ⊤)[x₁, …, x_n]/(P₁, …, P_n)`, and let `F` be a sheaf of sets on `Y_étale`
equipped with `n` morphisms `s₁, …, s_n : F ⟶ 𝒪_Y` whose values over every chart are a solution
of the presented system.  Then there is exactly one morphism `F ⟶ h_V` whose `i`-th coordinate
is `sᵢ`. -/
theorem existsUnique_hom_smallEtaleYoneda_of_isSolution
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type u))
    (s : Fin n → (F ⟶ setStructureSheaf B Y.obj Y.property))
    (hs : ∀ (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) (t : F.obj.obj U),
      MvPolynomial.IsSolution P (B.inclusion.map U.unop.obj.hom).appTop.hom
        (fun i => (s i).hom.app U t)) :
    ∃! φ : F ⟶ (smallEtaleYoneda B Y.obj Y.property).obj V,
      ∀ i, φ ≫ smallEtaleYonedaCoordinate V P pres i = s i := by
  let a : ∀ U : (SmallEtale B Y.obj Y.property)ᵒᵖ, F.obj.obj U → (U.unop ⟶ V) :=
    fun U t => (smallEtaleHomEquivSolutions V P pres U.unop).symm
      ⟨fun i => (s i).hom.app U t, hs U t⟩
  have hcoord : ∀ (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) (t : F.obj.obj U) (i : Fin n),
      (smallEtaleHomEquivSolutions V P pres U.unop (a U t)).1 i = (s i).hom.app U t :=
    fun U t i => congrFun (congrArg Subtype.val
      ((smallEtaleHomEquivSolutions V P pres U.unop).apply_symm_apply
        ⟨fun j => (s j).hom.app U t, hs U t⟩)) i
  have hnat : ∀ (U U' : (SmallEtale B Y.obj Y.property)ᵒᵖ) (k : U ⟶ U') (t : F.obj.obj U),
      a U' (F.obj.map k t) = k.unop ≫ a U t := by
    intro U U' k t
    refine (smallEtaleHomEquivSolutions V P pres U'.unop).injective
      (Subtype.ext (funext fun i => ?_))
    exact ((hcoord U' (F.obj.map k t) i).trans
      (ConcreteCategory.congr_hom ((s i).hom.naturality k) t)).trans
      ((smallEtaleHomEquivSolutions_naturality V P pres k.unop (a U t) i).trans
        (congrArg ((SmallEtale.toScheme B Y.obj Y.property).map k.unop).appTop
          (hcoord U t i))).symm
  refine ⟨⟨{ app := fun U => TypeCat.ofHom (a U)
             naturality := fun U U' k =>
               TypeCat.homEquiv.injective (funext fun t => hnat U U' k t) }⟩, fun i => ?_, ?_⟩
  · exact sheaf_hom_ext_of_apply_eq fun U t => hcoord U t i
  · intro ψ hψ
    refine sheaf_hom_ext_of_apply_eq fun U t => ?_
    refine Eq.trans ((smallEtaleHomEquivSolutions V P pres U.unop).symm_apply_apply
      (ψ.hom.app U t)).symm ?_
    refine congrArg (smallEtaleHomEquivSolutions V P pres U.unop).symm
      (Subtype.ext (funext fun i => ?_))
    exact sheaf_hom_apply_congr (hψ i) U t

end Presentation

end AlgebraicGeometry

end
