module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChangeIso

/-!
# The chart computation behind the affine case of Stacks 0AF4

Let `q : Q ⟶ X` be a morphism of algebraic spaces, where `X` is represented by the scheme of an
étale chart `Z₀` with `R = Γ(Z₀)`, and let `g : Q' ⟶ Q` be representable.  Suppose a
quasi-coherent `𝒪_X`-module `M` has an isomorphism `c : q^*M ≅ g_*𝒪_{Q'}`, and that an
`R`-algebra `A` is identified with the global sections `M(Z₀)` compatibly with a ring map
`α : A ⟶ Γ(Q')`.  Then over every affine étale chart `W` of `Q` the map
`Γ(W) ⊗_R A ⟶ Γ(W ×_Q Q')`, `w ⊗ a ↦ w · α(a)`, is bijective: it is the chart formula of
Stacks 083K for `q^*M`, followed by `c` and by the identification of the sections of
`g_*𝒪_{Q'}` over `W` with `Γ(W ×_Q Q')`.

## Main results

* `AlgebraicGeometry.Space.exists_tensorChartEquiv`: the statement above.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Q Q' : AlgebraicSpaces B S hS}

/-- **The chart computation**, on the sections of `M` over `Z₀`.  For a quasi-coherent `M` with
an isomorphism `c : q^*M ≅ g_*𝒪_{Q'}` and an affine étale chart `W` of `Q`, the map
`Γ(W) ⊗_{Γ(Z₀)} M(Z₀) ⟶ Γ(W ×_Q Q')`, `w ⊗ m ↦ w · c(m)`, is an additive bijection. -/
theorem exists_tensorChartEquiv (q : Q ⟶ X) (g : Q' ⟶ Q)
    (hg : yoneda.relativelyRepresentable g.hom) (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (c : (modulePullback B S hS q).obj M ⟶
      (modulePushforward B S hS g).obj (SheafOfModules.unit (structureRingSheaf B S hS Q')))
    [IsIso c] (W : SmallEtale B S hS Q.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS Q.1 ⋙ BigFppfOver.toScheme B S hS).obj W))
    (hZ : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)) :
    letI : Algebra (chartRing B S hS X.1 X.2 Z₀) (chartRing B S hS Q.1 Q.2 W) :=
      chartDiagramAlgebra B S hS q (isoChartDiagram B S hS q Z₀ W)
    ∃ e : TensorProduct (chartRing B S hS X.1 X.2 Z₀) (chartRing B S hS Q.1 Q.2 W)
        (M.val.obj (op Z₀)) ≃+
        chartRing B S hS Q'.1 Q'.2 ((smallBaseChange B S hS g hg).obj W),
      ∀ w m, e (w ⊗ₜ m) =
        (show (structureSheaf B S hS Q'.1 Q'.2).obj.obj
            (op ((smallBaseChange B S hS g hg).obj W)) from
          chartDiagramRestrict B S hS g (smallBaseChangeDiagram g hg W) w) *
          (show (structureSheaf B S hS Q'.1 Q'.2).obj.obj
              (op ((smallBaseChange B S hS g hg).obj W)) from
            modulePushforwardCounitApp B S hS g _ (smallBaseChangeDiagram g hg W)
              (modulePushforwardCounitApp B S hS q _ (isoChartDiagram B S hS q Z₀ W)
                (((modulePullbackAdjunction B S hS q).homEquiv M _ c).val.app (op Z₀) m))) := by
  let : Algebra (chartRing B S hS X.1 X.2 Z₀) (chartRing B S hS Q.1 Q.2 W) :=
    chartDiagramAlgebra B S hS q (isoChartDiagram B S hS q Z₀ W)
  have hψ := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS q M hM
    (isoChartDiagram B S hS q Z₀ W) hW hZ
  have hc : Function.Bijective (c.val.app (op W)).hom :=
    SheafOfModules.bijective_iso_hom_val_app (asIso c) (op W)
  have h₄ := bijective_modulePushforwardCounitApp_smallBaseChangeDiagram g hg
    (SheafOfModules.unit (structureRingSheaf B S hS Q')) W
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk'
      (fun z => modulePushforwardCounitApp B S hS g _ (smallBaseChangeDiagram g hg W)
        ((c.val.app (op W)).hom
          (modulePullbackChartBaseChange B S hS q M (isoChartDiagram B S hS q Z₀ W) z)))
      (fun z₁ z₂ => by
        simp only [map_add]
        exact modulePushforwardCounitApp_add B S hS g _ _ _ _))
    (h₄.comp (hc.comp hψ)), fun w m => ?_⟩
  refine (congrArg (fun z => modulePushforwardCounitApp B S hS g _ (smallBaseChangeDiagram g hg W)
    ((c.val.app (op W)).hom z))
    (modulePullbackChartBaseChange_tmul B S hS q M (isoChartDiagram B S hS q Z₀ W) w m)).trans ?_
  refine (congrArg (modulePushforwardCounitApp B S hS g _ (smallBaseChangeDiagram g hg W))
    ((c.val.app (op W)).hom.map_smul w
      (modulePullbackChartSection B S hS q M (isoChartDiagram B S hS q Z₀ W) m))).trans ?_
  refine (modulePushforwardCounitApp_unit_smul B S hS g (smallBaseChangeDiagram g hg W) w
    _).trans ?_
  exact congrArg₂ (· * ·) rfl
    (congrArg (modulePushforwardCounitApp B S hS g _ (smallBaseChangeDiagram g hg W))
      ((congrArg (c.val.app (op W)).hom
        (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS q M
          (isoChartDiagram B S hS q Z₀ W) m)).symm.trans
        (modulePullbackHomFMap_app B S hS q M _ c (isoChartDiagram B S hS q Z₀ W) m).symm))

end AlgebraicGeometry.Space
