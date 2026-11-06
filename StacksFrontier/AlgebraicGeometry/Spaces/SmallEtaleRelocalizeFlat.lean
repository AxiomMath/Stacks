module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeChartRestriction

/-!
# Flatness of modules on an algebraic space and on its lower-shriek extension

Let `h : W ⟶ S` be a morphism of a big fppf site and `f : X ⟶ Y` a morphism of algebraic spaces
over `W`.  The lower-shriek extensions `Λ_h X`, `Λ_h Y` are algebraic spaces over `S` with the
same étale charts, and `Λ_h f` has the same commuting squares of charts as `f`.  Flatness over
the target (Stacks 05VV) is a condition on those squares and on the restrictions of a module to
the source charts, so it is invariant under the equivalence `Mod(𝒪_X) ≌ Mod(𝒪_{Λ_h X})`.

## Main definitions

* `AlgebraicGeometry.Space.ChartDiagram.relocalizeSE` and
  `AlgebraicGeometry.Space.ChartDiagram.derelocalizeSE`: the commuting squares of étale charts of
  `f` and of `Λ_h f` correspond, with the same vertical morphisms of schemes.

## Main results

* `AlgebraicGeometry.Space.relocalizeChartBase_eq`: the factorization through `W` that a chart of
  `Λ_h X` descends along is the one carried by its section.
* `AlgebraicGeometry.Space.isFlatOver_relocalizeModulesEquivalence_functor_iffSE` and
  `AlgebraicGeometry.Space.isFlatOver_relocalizeModulesEquivalence_inverse_iffSE`: flatness over
  the target is preserved and reflected by the equivalence of module categories.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}

/-- The factorization carried by the value of a chart of `Λ_h X` on a morphism into its object
is that morphism followed by the factorization carried by the chart. -/
theorem relocalize_chart_app_fst_fst
    (V : CostructuredArrow yoneda ((OverShriek.relocalizePresheafFunctor h).obj X))
    {Z : BigFppfOver B S hS} (k : Z ⟶ V.left) :
    (V.hom.app (op Z) k).1.1 = k.left ≫ (yonedaEquiv V.hom).1.1 := by
  have e : V.hom.app (op Z) k =
      ((OverShriek.relocalizePresheafFunctor h).obj X).map k.op (yonedaEquiv V.hom) := by
    rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [e]
  rfl

/-- **The factorization through `W` that a chart of `Λ_h X` descends along is the one carried by
its section.** -/
theorem relocalizeChartBase_eq
    (V : CostructuredArrow yoneda ((OverShriek.relocalizePresheafFunctor h).obj X)) :
    relocalizeChartBase B W S hW hS h V = (yonedaEquiv V.hom).1.1 := by
  have e := congrArg
    (fun a : yoneda.obj V.left ⟶ (OverShriek.relocalizePresheafFunctor h).obj X =>
      (yonedaEquiv a).1.1) (relocalizeChartDescent_spec B W S hW hS h V)
  refine Eq.trans ?_ e.symm
  change _ = (𝟙 _ ≫ 𝟙 _) ≫ relocalizeChartBase B W S hW hS h V
  rw [Category.comp_id, Category.id_comp]

variable (f : X ⟶ Y)

/-- **A commuting square of étale charts of `f` is one of `Λ_h f`**: the charts are relocalized
and the vertical morphism of schemes is unchanged. -/
def ChartDiagram.relocalizeSE (d : ChartDiagram B W hW X Y f) :
    ChartDiagram B S hS ((OverShriek.relocalizePresheafFunctor h).obj X)
      ((OverShriek.relocalizePresheafFunctor h).obj Y)
      ((OverShriek.relocalizePresheafFunctor h).map f) where
  U := (SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj d.U
  V := (SmallEtale.relocalizeEquivalence B W S hW hS h Y).functor.obj d.V
  g := (Over.map h).map d.g
  comm := by
    change relocalizeChart B W S hW hS h d.U.obj.hom ≫
        (OverShriek.relocalizePresheafFunctor h).map f =
      yoneda.map ((Over.map h).map d.g) ≫ relocalizeChart B W S hW hS h d.V.obj.hom
    rw [relocalizeChart_comp, relocalizeChart_naturality, d.comm]

/-- The underlying morphism of the vertical morphism of a square of charts of `Λ_h f` factors
the descended structure morphisms. -/
theorem ChartDiagram.g_left_comp_relocalizeChartBase
    (d : ChartDiagram B S hS ((OverShriek.relocalizePresheafFunctor h).obj X)
      ((OverShriek.relocalizePresheafFunctor h).obj Y)
      ((OverShriek.relocalizePresheafFunctor h).map f)) :
    d.g.left ≫ relocalizeChartBase B W S hW hS h d.V.obj =
      relocalizeChartBase B W S hW hS h d.U.obj := by
  rw [relocalizeChartBase_eq, relocalizeChartBase_eq]
  have e := congrArg
    (fun a : yoneda.obj d.U.obj.left ⟶ (OverShriek.relocalizePresheafFunctor h).obj Y =>
      (yonedaEquiv a).1.1) d.comm
  simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at e
  rw [relocalize_chart_app_fst_fst] at e
  exact e.symm

/-- **A commuting square of étale charts of `Λ_h f` is one of `f`**: the charts are read back
over `W` and the vertical morphism of schemes is unchanged. -/
def ChartDiagram.derelocalizeSE
    (d : ChartDiagram B S hS ((OverShriek.relocalizePresheafFunctor h).obj X)
      ((OverShriek.relocalizePresheafFunctor h).obj Y)
      ((OverShriek.relocalizePresheafFunctor h).map f)) :
    ChartDiagram B W hW X Y f where
  U := (SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj d.U
  V := (SmallEtale.relocalizeEquivalence B W S hW hS h Y).inverse.obj d.V
  g := Over.homMk d.g.left (d.g_left_comp_relocalizeChartBase B W S hW hS h f)
  comm := by
    change relocalizeChartDescent B W S hW hS h d.U.obj ≫ f =
      yoneda.map (Over.homMk d.g.left (d.g_left_comp_relocalizeChartBase B W S hW hS h f) :
        Over.mk (relocalizeChartBase B W S hW hS h d.U.obj) ⟶
          Over.mk (relocalizeChartBase B W S hW hS h d.V.obj)) ≫
        relocalizeChartDescent B W S hW hS h d.V.obj
    apply relocalizeChart_injective B W S hW hS h
    rw [← relocalizeChart_comp, ← relocalizeChart_naturality]
    have sU := relocalizeChartDescent_spec B W S hW hS h d.U.obj
    have sV := relocalizeChartDescent_spec B W S hW hS h d.V.obj
    have : Epi (yoneda.map (relocalizeBaseHom B W S hW hS h
        (relocalizeChartBase_comp B W S hW hS h d.U.obj))) :=
      @IsIso.epi_of_iso _ _ _ _ _ (Functor.map_isIso _ _)
    rw [← cancel_epi (yoneda.map (relocalizeBaseHom B W S hW hS h
      (relocalizeChartBase_comp B W S hW hS h d.U.obj))), ← Category.assoc, ← sU, d.comm]
    have hsq : relocalizeBaseHom B W S hW hS h (relocalizeChartBase_comp B W S hW hS h d.U.obj) ≫
        (Over.map h).map (Over.homMk d.g.left (d.g_left_comp_relocalizeChartBase B W S hW hS h f) :
          Over.mk (relocalizeChartBase B W S hW hS h d.U.obj) ⟶
            Over.mk (relocalizeChartBase B W S hW hS h d.V.obj)) =
        d.g ≫ relocalizeBaseHom B W S hW hS h (relocalizeChartBase_comp B W S hW hS h d.V.obj) :=
      Over.OverMorphism.ext (by simp [relocalizeBaseHom])
    rw [← Category.assoc, ← yoneda.map_comp, hsq, yoneda.map_comp, Category.assoc, ← sV]

variable (hX : IsAlgebraicSpace B W hW X) (hY : IsAlgebraicSpace B W hW Y)
  (hX' : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj X))

/-- Flatness over `Λ_h Y` of an `𝒪_{Λ_h X}`-module gives flatness over `Y` of the corresponding
`𝒪_X`-module. -/
theorem isFlatOver_relocalizeModulesEquivalence_inverseSE
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor h).obj X) hX')
    (hM : IsFlatOver B S hS hX' ((OverShriek.relocalizePresheafFunctor h).map f) M) :
    IsFlatOver B W hW hX f ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').inverse.obj M) :=
  fun d x => (flatOverAt_iff_of_iso ((BigFppfOver.toScheme B W hW).map d.g)
    (restrictToChartRelocalizeInverseIsoSE B W S hW hS h hX hX' d.U M) x).2
      (hM (ChartDiagram.relocalizeSE B W S hW hS h f d) x)

/-- Flatness over `Y` of an `𝒪_X`-module gives flatness over `Λ_h Y` of the corresponding
`𝒪_{Λ_h X}`-module. -/
theorem isFlatOver_relocalizeModulesEquivalence_functorSE (F : Modules.{u, u} B W hW X hX)
    (hF : IsFlatOver B W hW hX f F) :
    IsFlatOver B S hS hX' ((OverShriek.relocalizePresheafFunctor h).map f)
      ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').functor.obj F) :=
  fun d x => (flatOverAt_iff_of_iso ((BigFppfOver.toScheme B S hS).map d.g)
    (restrictToChartRelocalizeFunctorIsoSE B W S hW hS h hX hX' d.U F) x).2
      (hF (ChartDiagram.derelocalizeSE B W S hW hS h f d) x)

/-- **Flatness is invariant under relocalization.** An `𝒪_X`-module is flat over `Y` along `f`
exactly when the corresponding `𝒪_{Λ_h X}`-module is flat over `Λ_h Y` along `Λ_h f`. -/
theorem isFlatOver_relocalizeModulesEquivalence_functor_iffSE (F : Modules.{u, u} B W hW X hX) :
    IsFlatOver B S hS hX' ((OverShriek.relocalizePresheafFunctor h).map f)
        ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').functor.obj F) ↔
      IsFlatOver B W hW hX f F :=
  ⟨fun hF => IsFlatOver.of_iso B W hW hX
      ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').unitIso.app F).symm
      (isFlatOver_relocalizeModulesEquivalence_inverseSE B W S hW hS h f hX hX' _ hF),
    isFlatOver_relocalizeModulesEquivalence_functorSE B W S hW hS h f hX hX' F⟩

/-- **Flatness is invariant under relocalization**, read from `Λ_h X`. -/
theorem isFlatOver_relocalizeModulesEquivalence_inverse_iffSE
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor h).obj X) hX') :
    IsFlatOver B W hW hX f ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').inverse.obj M) ↔
      IsFlatOver B S hS hX' ((OverShriek.relocalizePresheafFunctor h).map f) M :=
  ⟨fun hM => IsFlatOver.of_iso B S hS hX'
      ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').counitIso.app M)
      (isFlatOver_relocalizeModulesEquivalence_functorSE B W S hW hS h f hX hX' _ hM),
    isFlatOver_relocalizeModulesEquivalence_inverseSE B W S hW hS h f hX hX' M⟩

end AlgebraicGeometry.Space

end
