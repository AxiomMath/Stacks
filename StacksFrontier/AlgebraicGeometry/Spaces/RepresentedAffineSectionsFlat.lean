module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleEtaleChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentSelfChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness

/-!
# Flatness over the base of the sections over an affine étale chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `𝒢` a quasi-coherent `𝒪_X`-module flat
over `Y` (Stacks 05VV). For étale morphisms `a : U ⟶ X` and `b : V ⟶ Y` from affine schemes and
`f₀ : U ⟶ V` over `f`, the `Γ(U, 𝒪)`-module `Γ(U, a^*𝒢)` is flat over `Γ(V, 𝒪)`.

## Main results

* `AlgebraicGeometry.Space.flat_representedAffineSections_modulePullback_of_isFlatOver`
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Sections over an affine étale chart of a module flat over the target are flat.** For a
quasi-coherent `𝒪_X`-module `𝒢` flat over `Y` along `f`, étale `a : U ⟶ X`, `b : V ⟶ Y` with
`U`, `V` affine and `f₀ : U ⟶ V` over `f`, the sections `Γ(U, a^*𝒢)` are a flat
`Γ(V, 𝒪)`-module. -/
theorem flat_representedAffineSections_modulePullback_of_isFlatOver
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (G : Modules.{u, u} B S hS X.1 X.2)
    (hGq : G.IsQuasicoherentOnSite) (hG : IsFlatOver B S hS X.2 f.hom G)
    {U V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (ha : IsEtale B S hS a.hom)
    (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (hb : IsEtale B S hS b.hom) (f₀ : U ⟶ V) (hf₀ : representedSpaceMap B S hS f₀ ≫ b = a ≫ f) :
    Module.Flat Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((ModuleCat.restrictScalars.{u} (representedAffineCommRingCatHom B S hS f₀).hom).obj
        ((representedAffineSections B S hS U).obj ((modulePullback B S hS a).obj G))) := by
  let d : ChartDiagram B S hS X.1 Y.1 f.hom :=
    { U := etaleChartOfIsEtale B S hS a.hom ha
      V := etaleChartOfIsEtale B S hS b.hom hb
      g := f₀
      comm := (congrArg (fun k => k.hom) hf₀).symm }
  let P := (modulePullback B S hS a).obj G
  have h2 := (AlgebraicGeometry.isFlatOver_iff_of_moduleIso _
    (restrictToChartIsoRepresentedZariskiRestrictionPullback B S hS a.hom ha G hGq)).1
    (hG d : IsFlatOverOnChartDiagram B S hS X.2 G d)
  have := isQuasicoherent_representedZariskiRestriction B S hS U P
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a G hGq)
  have h3 := (AlgebraicGeometry.isFlatOver_iff_flat_sections
    ((BigFppfOver.toScheme B S hS).map f₀)
    (representedZariskiRestriction B S hS U (isAlgebraicSpace_yoneda B S hS U) P)).1 h2
  let : Module Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ(representedZariskiRestriction B S hS U (isAlgebraicSpace_yoneda B S hS U) P, ⊤) :=
    Module.compHom _ ((BigFppfOver.toScheme B S hS).map f₀).appTop.hom
  let i := restrictToChartSelfChartIsoRestrictModule B S hS U P
  refine Module.Flat.of_semilinearEquiv (RingEquiv.refl _)
    (show ((ModuleCat.restrictScalars.{u} (representedAffineCommRingCatHom B S hS f₀).hom).obj
        ((representedAffineSections B S hS U).obj P) : Type u) ≃+
      Γ(representedZariskiRestriction B S hS U (isAlgebraicSpace_yoneda B S hS U) P, ⊤) from
      { toFun := fun x => (i.inv.val.app (op ⊤)).hom x
        invFun := fun y => (i.hom.val.app (op ⊤)).hom y
        left_inv := fun x => congrArg (fun φ => (φ.val.app (op ⊤)).hom x) i.inv_hom_id
        right_inv := fun y => congrArg (fun φ => (φ.val.app (op ⊤)).hom y) i.hom_inv_id
        map_add' := fun x y => map_add _ x y }) (fun r m => ?_)
  have hx : ∀ t : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤),
      (((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.appTop).hom
        ((Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).inv.hom t) = t := fun t => by
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    exact congrArg (fun φ => φ.hom t)
      (Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).inv_hom_id
  refine ((i.inv.val.app (op ⊤)).hom.map_smul
    (show ((etaleChartScheme B S hS (selfChart B S hS U)).ringCatSheaf.obj.obj (op ⊤) : Type u) from
      (((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.appTop).hom
        ((Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).inv.hom
          ((representedAffineCommRingCatHom B S hS f₀).hom r))) m).trans ?_
  exact congrArg (fun t : ((etaleChartScheme B S hS (selfChart B S hS U)).ringCatSheaf.obj.obj
    (op ⊤) : Type u) => t • (i.inv.val.app (op ⊤)).hom m) (hx _)

end AlgebraicGeometry.Space
