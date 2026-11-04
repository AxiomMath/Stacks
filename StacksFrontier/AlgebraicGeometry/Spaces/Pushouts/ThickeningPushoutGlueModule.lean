module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutGlueSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardReflectsIsoQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartFactorizationEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties

/-!
# The glued module on a pushout along a thickening

The glued module `G = a_*A ×_{(c ≫ a)_*c^*A} b_*B'` of Stacks 08KV, globally: it is
quasi-coherent, its two counits `a^*G ⟶ A` and `b^*G ⟶ B'` are isomorphisms, and it is flat over
`Y'` when `A` is flat over `Y` and `B'` over `Z'`. The counits are checked to be isomorphisms after
direct image along the affine morphisms `a` and `b` (Stacks 08AI), on the affine chart diagrams of
`P` over `Y'`, which are enough objects.

## Main results

* `AlgebraicGeometry.Space.ThickeningPushoutSpaces.isQuasicoherentOnSite_glue`.
* `AlgebraicGeometry.Space.ThickeningPushoutSpaces.isIso_glueCounitFst`,
  `AlgebraicGeometry.Space.ThickeningPushoutSpaces.isIso_glueCounitSnd`.
* `AlgebraicGeometry.Space.ThickeningPushoutSpaces.isFlatOver_glue`.

## References

* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- The ambient-universe abelian structure on sheaves of modules would be selected ahead of
-- `SheafOfModules.instAbelian` for the `𝒪`-modules here, whose sections live in the universe of
-- the schemes.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of étale charts preserves the points of the algebraic space they determine. -/
theorem pointOfEtaleChart_map_toOver {X : AlgebraicSpaces B S hS} {W U : SmallEtale B S hS X.1}
    (k : W ⟶ U) (z : etaleChartScheme B S hS W) :
    pointOfEtaleChart B S hS U
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map k) z) =
      pointOfEtaleChart B S hS W z := by
  have hk : yoneda.map ((SmallEtale.toOver B S hS X.1).map k) ≫ U.1.hom = W.1.hom :=
    CostructuredArrow.w k.hom
  let d : ChartDiagram B S hS X.1 X.1 (𝟙 X.1) :=
    ⟨W, U, (SmallEtale.toOver B S hS X.1).map k, by rw [Category.comp_id, hk]⟩
  exact (pointOfEtaleChart_map_g B S hS d z).trans (pointsMap_id_apply B S hS _)

namespace ThickeningPushoutSpaces

variable {Z Z' Y Y' : BigFppfOver B S hS} {i : Z ⟶ Z'} {f : Z ⟶ Y} {g : Z' ⟶ Y'} {h : Y ⟶ Y'}
  {P V U' U : AlgebraicSpaces B S hS} {p : P ⟶ (schemeSpaceFunctor B S hS).obj Y'}
  {pV : V ⟶ (schemeSpaceFunctor B S hS).obj Y} {pU' : U' ⟶ (schemeSpaceFunctor B S hS).obj Z'}
  {pU : U ⟶ (schemeSpaceFunctor B S hS).obj Z} {a : V ⟶ P} {b : U' ⟶ P} {c : U ⟶ V} {d : U ⟶ U'}

/-- The counit `f^*M ⟶ N` adjoint to `k : M ⟶ f_*N` sends the chart section of `m` to the counit
image of `k m`. -/
private theorem homEquiv_symm_app_modulePullbackChartSection {X₁ X₂ : AlgebraicSpaces B S hS}
    (f : X₁ ⟶ X₂) {M : Modules.{u, u} B S hS X₂.1 X₂.2} {N : Modules.{u, u} B S hS X₁.1 X₁.2}
    (k : M ⟶ (modulePushforward B S hS f).obj N) (d : ChartDiagram B S hS X₁.1 X₂.1 f.hom)
    (m : M.val.obj (op d.V)) :
    (((modulePullbackAdjunction B S hS f).homEquiv _ _).symm k).val.app (op d.U)
        (modulePullbackChartSection B S hS f M d m) =
      modulePushforwardCounitApp B S hS f N d (k.val.app (op d.V) m) := by
  rw [Adjunction.homEquiv_counit]
  exact (comp_val_app_op _ _ d.U _).trans
    ((congrArg (((modulePullbackAdjunction B S hS f).counit.app N).val.app (op d.U))
      (modulePullbackChartSection_map B S hS f _ k d m)).trans
      (counit_app_modulePullbackChartSection B S hS f N d _))

/-- If `g : f^*M ⟶ N` is bijective on the sections over the chart `d.U` of the base change
diagram of `V`, then `f_* g` is bijective on sections over `V`. -/
private theorem bijective_modulePushforward_map_app_of_bijective {X₁ X₂ : AlgebraicSpaces B S hS}
    (f : X₁ ⟶ X₂) (hrep : yoneda.relativelyRepresentable f.hom)
    {M : Modules.{u, u} B S hS X₂.1 X₂.2} {N : Modules.{u, u} B S hS X₁.1 X₁.2}
    (g : (modulePullback B S hS f).obj M ⟶ N) (V : SmallEtale B S hS X₂.1)
    (hg : Function.Bijective (g.val.app (op (smallBaseChangeDiagram f hrep V).U))) :
    Function.Bijective (((modulePushforward B S hS f).map g).val.app (op V)) := by
  have hc₁ := bijective_modulePushforwardCounitApp_smallBaseChangeDiagram f hrep N V
  have hc₂ := bijective_modulePushforwardCounitApp_smallBaseChangeDiagram f hrep
    ((modulePullback B S hS f).obj M) V
  have hnat : modulePushforwardCounitApp B S hS f N (smallBaseChangeDiagram f hrep V) ∘
      (((modulePushforward B S hS f).map g).val.app (op V)) =
      (g.val.app (op (smallBaseChangeDiagram f hrep V).U)) ∘
        modulePushforwardCounitApp B S hS f ((modulePullback B S hS f).obj M)
          (smallBaseChangeDiagram f hrep V) :=
    funext fun x => modulePushforwardCounitApp_map B S hS f g (smallBaseChangeDiagram f hrep V) x
  refine (Function.Bijective.of_comp_iff' hc₁ _).1 ?_
  rw [hnat]
  exact hg.comp hc₂

/-- A morphism of quasi-coherent modules, whose direct image along an affine `f : X ⟶ P` is
bijective on sections over the objects of the affine chart diagrams of `P` over `Y'`, is an
isomorphism. -/
private theorem isIso_of_forall_bijective_modulePushforward_map_app {X : AlgebraicSpaces B S hS}
    (f : X ⟶ P) (hf : IsAffineHom B S hS f.hom) {M N : Modules.{u, u} B S hS X.1 X.2}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (g : M ⟶ N)
    (hbij : ∀ dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom,
      IsAffine ((SmallEtale.toOver B S hS P.1 ⋙ BigFppfOver.toScheme B S hS).obj dT.U) →
      IsAffine ((SmallEtale.toOver B S hS ((schemeSpaceFunctor B S hS).obj Y').1 ⋙
        BigFppfOver.toScheme B S hS).obj dT.V) →
      Function.Bijective (((modulePushforward B S hS f).map g).val.app (op dT.U))) :
    IsIso g := by
  refine isIso_of_isIso_modulePushforward_map_of_isAffineHom B S hS f hf hM hN g ?_
  refine Stacks.SheafOfModules.isIso_of_hasEnoughObjects_bijective_val_app
    ((modulePushforward B S hS f).map g)
    (hasEnoughObjects_isAffineChartFactorsThroughAffineChart B S hS p) ?_
  rintro W ⟨hW, V, m, hVaff, hcomm⟩
  exact hbij ⟨W, V, m, hcomm.symm⟩ hW hVaff

variable (E : ThickeningPushoutSpaces i f g h p pV pU' pU a b c d)
include E

section Glue

variable {A : Modules.{u, u} B S hS V.1 V.2} {B' : Modules.{u, u} B S hS U'.1 U'.2}
  (φ : (modulePushforward B S hS a).obj A ⟶
    (modulePushforward B S hS (c ≫ a)).obj ((modulePullback B S hS c).obj A))
  (ψ : (modulePushforward B S hS b).obj B' ⟶
    (modulePushforward B S hS (c ≫ a)).obj ((modulePullback B S hS c).obj A))

/-- **The glued module is quasi-coherent**: it is the kernel of `a_*A ⊕ b_*B' ⟶ (c ≫ a)_*c^*A`,
a morphism of quasi-coherent modules. -/
theorem isQuasicoherentOnSite_glue (hA : A.IsQuasicoherentOnSite)
    (hB : B'.IsQuasicoherentOnSite) : (pullback φ ψ).IsQuasicoherentOnSite := by
  have := isClosedUnderKernels_quasicoherentSheaves_smallEtale B S hS P.1 P.2
  have h₁ := isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS a
    E.isAffineHom_a A hA
  have h₂ := isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS b
    E.isAffineHom_b B' hB
  have h₃ := isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS
    (c ≫ a) (isAffineHom_comp B S hS _ _ E.isAffineHom_c E.isAffineHom_a)
    ((modulePullback B S hS c).obj A)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS c A hA)
  exact ObjectProperty.prop_of_isLimit_kernelFork _
    (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct φ ψ)
    (SheafOfModules.isQuasicoherentOnSite_biprod h₁ h₂) h₃

/-- The counit `a^*(a_*A ×_{(c ≫ a)_*c^*A} b_*B') ⟶ A`: the adjoint of the first projection. -/
def glueCounitFst : (modulePullback B S hS a).obj (pullback φ ψ) ⟶ A :=
  ((modulePullbackAdjunction B S hS a).homEquiv _ _).symm (pullback.fst φ ψ)

/-- The counit `b^*(a_*A ×_{(c ≫ a)_*c^*A} b_*B') ⟶ B'`: the adjoint of the second projection. -/
def glueCounitSnd : (modulePullback B S hS b).obj (pullback φ ψ) ⟶ B' :=
  ((modulePullbackAdjunction B S hS b).homEquiv _ _).symm (pullback.snd φ ψ)

variable (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom)

/-- The first counit carries the chart section of a section of the glued module to its first
projection on the chart `W_Y`. -/
theorem glueCounitFst_chartSection (m : (pullback φ ψ).val.obj (op dT.U)) :
    (glueCounitFst φ ψ).val.app (op (E.WY dT))
        (modulePullbackChartSection B S hS a (pullback φ ψ) (E.dWY dT) m) =
      E.glueFst dT φ ψ m := by
  exact (homEquiv_symm_app_modulePullbackChartSection a _ (E.dWY dT) m).trans
    (E.glueFst_apply dT φ ψ m).symm

/-- The second counit carries the chart section of a section of the glued module to its second
projection on the chart `W_{Z'}`. -/
theorem glueCounitSnd_chartSection (m : (pullback φ ψ).val.obj (op dT.U)) :
    (glueCounitSnd φ ψ).val.app (op (E.WZ' dT))
        (modulePullbackChartSection B S hS b (pullback φ ψ) (E.dWZ' dT) m) =
      E.glueSnd dT φ ψ m := by
  exact (homEquiv_symm_app_modulePullbackChartSection b _ (E.dWZ' dT) m).trans
    (E.glueSnd_apply dT φ ψ m).symm

section Affine

variable {φ ψ} (θ : (modulePullback B S hS d).obj B' ⟶ (modulePullback B S hS c).obj A)
    (hU : IsAffine ((SmallEtale.toOver B S hS P.1 ⋙ BigFppfOver.toScheme B S hS).obj dT.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS ((schemeSpaceFunctor B S hS).obj Y').1 ⋙
      BigFppfOver.toScheme B S hS).obj dT.V))

include hU hV in
/-- On an affine chart diagram `dT`, the first counit is bijective on sections over the chart
`W_Y`. -/
theorem bijective_glueCounitFst_app (hA : A.IsQuasicoherentOnSite) (hB : B'.IsQuasicoherentOnSite)
    (hθ : IsIso θ)
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    Function.Bijective ((glueCounitFst φ ψ).val.app (op (E.WY dT))) :=
  (isBaseChangeAlong_modulePullbackChartSectionₛₗ B S hS a (pullback φ ψ)
    (E.isQuasicoherentOnSite_glue φ ψ hA hB) (E.dWY dT) (E.isAffine_WY dT hU) hU).bijective_of_comp
    (E.isBaseChangeAlong_glueFst_glueSnd dT hU hV hA hB (θ := θ) hθ hφ hψ).1
    ((glueCounitFst φ ψ).val.app (op (E.WY dT))).hom (E.glueCounitFst_chartSection φ ψ dT)

include hU hV in
/-- On an affine chart diagram `dT`, the second counit is bijective on sections over the chart
`W_{Z'}`. -/
theorem bijective_glueCounitSnd_app (hA : A.IsQuasicoherentOnSite) (hB : B'.IsQuasicoherentOnSite)
    (hθ : IsIso θ)
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    Function.Bijective ((glueCounitSnd φ ψ).val.app (op (E.WZ' dT))) :=
  (isBaseChangeAlong_modulePullbackChartSectionₛₗ B S hS b (pullback φ ψ)
    (E.isQuasicoherentOnSite_glue φ ψ hA hB) (E.dWZ' dT) (E.isAffine_WZ' dT hU)
    hU).bijective_of_comp
    (E.isBaseChangeAlong_glueFst_glueSnd dT hU hV hA hB (θ := θ) hθ hφ hψ).2
    ((glueCounitSnd φ ψ).val.app (op (E.WZ' dT))).hom (E.glueCounitSnd_chartSection φ ψ dT)

include hU hV in
/-- On an affine chart diagram `dT`, the direct image along `a` of the first counit is bijective on
sections over `dT.U`. -/
theorem bijective_modulePushforward_map_glueCounitFst_app (hA : A.IsQuasicoherentOnSite)
    (hB : B'.IsQuasicoherentOnSite) (hθ : IsIso θ)
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    Function.Bijective
      (((modulePushforward B S hS a).map (glueCounitFst φ ψ)).val.app (op dT.U)) := by
  exact bijective_modulePushforward_map_app_of_bijective a E.rep_a _ dT.U
    (E.bijective_glueCounitFst_app dT θ hU hV hA hB hθ hφ hψ)

include hU hV in
/-- On an affine chart diagram `dT`, the direct image along `b` of the second counit is bijective
on sections over `dT.U`. -/
theorem bijective_modulePushforward_map_glueCounitSnd_app (hA : A.IsQuasicoherentOnSite)
    (hB : B'.IsQuasicoherentOnSite) (hθ : IsIso θ)
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    Function.Bijective
      (((modulePushforward B S hS b).map (glueCounitSnd φ ψ)).val.app (op dT.U)) := by
  exact bijective_modulePushforward_map_app_of_bijective b E.rep_b _ dT.U
    (E.bijective_glueCounitSnd_app dT θ hU hV hA hB hθ hφ hψ)

end Affine

section Iso

variable {φ ψ} (θ : (modulePullback B S hS d).obj B' ⟶ (modulePullback B S hS c).obj A)

/-- **The glued module restricts to `A` on `V`** (Stacks 08KV): the counit `a^*G ⟶ A` is an
isomorphism. -/
theorem isIso_glueCounitFst (hA : A.IsQuasicoherentOnSite) (hB : B'.IsQuasicoherentOnSite)
    (hθ : IsIso θ)
    (hφ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) x,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) y,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    IsIso (glueCounitFst φ ψ) := by
  exact isIso_of_forall_bijective_modulePushforward_map_app a E.isAffineHom_a
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a _
      (E.isQuasicoherentOnSite_glue φ ψ hA hB)) hA _
    fun dT hU hV => E.bijective_modulePushforward_map_glueCounitFst_app dT θ hU hV hA hB hθ
      (hφ _) (hψ _)

/-- **The glued module restricts to `B'` on `U'`** (Stacks 08KV): the counit `b^*G ⟶ B'` is an
isomorphism. -/
theorem isIso_glueCounitSnd (hA : A.IsQuasicoherentOnSite) (hB : B'.IsQuasicoherentOnSite)
    (hθ : IsIso θ)
    (hφ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) x,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) y,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    IsIso (glueCounitSnd φ ψ) := by
  exact isIso_of_forall_bijective_modulePushforward_map_app b E.isAffineHom_b
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS b _
      (E.isQuasicoherentOnSite_glue φ ψ hA hB)) hB _
    fun dT hU hV => E.bijective_modulePushforward_map_glueCounitSnd_app dT θ hU hV hA hB hθ
      (hφ _) (hψ _)

/-- **The glued module of flat pieces is flat over `Y'`** (Stacks 07RW, read on the charts). -/
theorem isFlatOver_glue (hA : A.IsQuasicoherentOnSite) (hB : B'.IsQuasicoherentOnSite)
    (hθ : IsIso θ)
    (hAf : IsFlatOver B S hS V.2 pV.hom A) (hBf : IsFlatOver B S hS U'.2 pU'.hom B')
    (hφ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) x,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) y,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    IsFlatOver B S hS P.2 p.hom (pullback φ ψ) := by
  refine isFlatOver_of_forall_flat_sections B S hS p _ (E.isQuasicoherentOnSite_glue φ ψ hA hB)
    fun x => ?_
  obtain ⟨d₀, u₀, hu₀⟩ := exists_chartDiagram_pointOfEtaleChart B S hS P.2
    ((schemeSpaceFunctor B S hS).obj Y').2 p.hom x
  obtain ⟨dT, k, z, hU, hV, hz⟩ := exists_affine_chartDiagram_at_chartPoint B S hS p d₀.U u₀
  refine ⟨dT, hU, hV, z, ?_,
    E.flat_glue_sections dT hU hV hA hB (θ := θ) hθ hAf hBf (hφ dT) (hψ dT)⟩
  rw [← pointOfEtaleChart_map_toOver k z]
  exact (congrArg (pointOfEtaleChart B S hS d₀.U) hz).trans hu₀

end Iso

end Glue

end ThickeningPushoutSpaces

end AlgebraicGeometry.Space

end
