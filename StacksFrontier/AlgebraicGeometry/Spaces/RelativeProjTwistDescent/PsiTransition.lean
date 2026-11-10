module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentColimits

/-!
# The homomorphism `ψ` of Stacks 084D on the atlas carries one transition to the other

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B and
`X = U/R` a presentation of its base, so that `P = P_U/P_R`.  On the scheme of every base change
`V ×_X P = Proj_V(v^*𝒜)` the homomorphism-of-sections map `ψ` of Tag 01NR, in adjoint form
`π_V^*(v^*𝒜)_n ⟶ 𝒪(n)`, is defined
(`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint`).  This file proves
that along a morphism `y : V ×_X P ⟶ U ×_X P` lying over a morphism `k : V ⟶ U` of test objects
these maps are carried into each other: the pullback along `y` of `ψ` at `U`, followed by the
comparison of the twists along `y`, is the identification `y^*π_U^*(u^*𝒜)_n ≅ π_V^*(v^*𝒜)_n` of
the sources followed by `ψ` at `V`.  This is the comparison of twists of Stacks 084B (3)
carrying `ψ` to `ψ` (see
`AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparisonPsi_comp_pointTwistComparison`),
transposed along the adjunction `π_V^* ⊣ π_{V*}`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.pointPieceChainSchemeIso` and
  `…pointPieceChainIso`: the identification `y^*π_U^*(u^*𝒜)_n ≅ π_V^*(v^*𝒜)_n` of the sources of
  `ψ` along a morphism `y` lying over `k`.
* `AlgebraicGeometry.Space.RelativeProjSituation.psiSourceTransition`: the transition of the
  source of `ψ` on the presentation `P = P_U/P_R`.

## Main results

* `AlgebraicGeometry.Space.pullback_map_adjointPsi_comp_pullbackIsoOfSquare`: **the comparison of
  twists carrying `ψ` to `ψ`, transposed along `π_V^* ⊣ π_{V*}`**, at free variables; and
  `AlgebraicGeometry.Space.pullback_map_comp_eq_of_adjointPsi`, the same with the four morphisms
  named by their defining equations.
* `AlgebraicGeometry.Space.pullback_map_pullbackAdjointPsi_comp_eq(_of_congr)`: the same for
  `AlgebraicGeometry.Space.pullbackAdjointPsi`, at free graded algebras.
* `AlgebraicGeometry.Space.comp_inv_comp_eq_of_squares`: two such squares along the target and
  the source projections give the compatibility of `ψ` with the two transitions.
* `AlgebraicGeometry.Space.spaceBaseDescent_comp_modulePullbackCompIso`: the canonical transition
  morphism of an inverse image `φ^*(π^*M)` on a groupoid, read through the contractions of
  Stacks 03LU, is the identity of `M`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pullback_map_psiChartSchemeHom_comp` and
  `…quasicoherentPullbackMap_psiChartSchemeHom_comp`: **`ψ` is carried along every morphism of
  base changes lying over a morphism of test objects.**
* `AlgebraicGeometry.Space.RelativeProjSituation.psiSourceTransition_comp_quasicoherentPullbackMap`
  and `…transitionCommutes_psiChartSchemeHom`: **`ψ` on the scheme of `P_U` carries the transition
  of its source to the transition of the twist `𝒪(n)`**, on schemes and for the attached modules.

## Implementation notes

The transposed compatibility is proved on pulled-back sections
(`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_doublePullbackSection`), at free variables, so
that no construction is unfolded.  The instances in Situation 0849 name every composite by its
defining equation (`ψ₀`, `φ_U`, `T`, `ch`), proved by `rfl` or by the defining lemma, so that the
spellings produced by definition bodies (which hold auxiliary proofs of
`s.shrink.site.Contains s.shrink.base`) are only ever matched against metavariables or compared
argument by argument, never unfolded.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (basePsi)
open Stacks.AlgebraicGeometry.ModuleLimits (pullbackComp_inv_val_app_pullbackSection)

namespace AlgebraicGeometry.Space

section Generic

/-- A composite of morphisms of modules on a scheme, on a section, computed in two steps. -/
private theorem val_app_comp_of_eq {X : Scheme.{u}} {M N K : X.Modules} (φ : M ⟶ N) (χ : N ⟶ K)
    (V : X.Opens) (x : M.val.obj (op V)) {y : N.val.obj (op V)} (hy : φ.val.app (op V) x = y)
    {z : K.val.obj (op V)} (hz : χ.val.app (op V) y = z) :
    (φ ≫ χ).val.app (op V) x = z := by
  subst hy hz
  rfl

/-- The transpose of a morphism `M ⟶ p_* O` along `p^* ⊣ p_*`, on a pulled-back section. -/
private theorem homEquiv_symm_val_app_pullbackSection {X Y : Scheme.{u}} (p : Y ⟶ X)
    {M : X.Modules} {O : Y.Modules} (ψ : M ⟶ (Scheme.Modules.pushforward p).obj O)
    (U : X.Opens) (a : M.val.obj (op U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M O).symm ψ).val.app
        (op (p ⁻¹ᵁ U)) (pullbackSection p M U (p ⁻¹ᵁ U) le_rfl a) =
      ψ.val.app (op U) a := by
  have h := Stacks.AlgebraicGeometry.ModuleLimits.homEquiv_val_app p
    (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M O).symm ψ) U a
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The adjoint `f^*A ⟶ ι^*O` of `ψ` read along `f = ι ≫ p`, on a pulled-back section, is the
pulled-back section of `ψ`. -/
private theorem pullbackAdjointOfComp_val_app_pullbackSection {X P Y : Scheme.{u}} (ι : X ⟶ P)
    (p : P ⟶ Y) {A : Y.Modules} {O : P.Modules} (ψ : A ⟶ (Scheme.Modules.pushforward p).obj O)
    (U : Y.Opens) (W : X.Opens) (hW : W ≤ ι ⁻¹ᵁ (p ⁻¹ᵁ U)) (h : W ≤ (ι ≫ p) ⁻¹ᵁ U)
    (a : A.val.obj (op U)) :
    (pullbackAdjointOfComp ι p (ι ≫ p) rfl ψ).val.app (op W) (pullbackSection (ι ≫ p) A U W h a) =
      pullbackSection ι O (p ⁻¹ᵁ U) W hW (ψ.val.app (op U) a) := by
  refine val_app_comp_of_eq _ _ _ _ (Scheme.Modules.pullbackSection_congr rfl A U _ h h a) ?_
  refine val_app_comp_of_eq _ _ _ _
    (pullbackComp_inv_val_app_pullbackSection ι p A U (p ⁻¹ᵁ U) _ le_rfl hW h a) ?_
  refine (Scheme.Modules.pullbackSection_naturality ι _ (p ⁻¹ᵁ U) _ hW _).trans ?_
  exact congrArg (pullbackSection ι O (p ⁻¹ᵁ U) W hW)
    (homEquiv_symm_val_app_pullbackSection p ψ U a)

/-- **`ψ` in adjoint form is carried along a morphism lying over a morphism of the base, at free
variables.**  Let `pc : P_V ⟶ P_U` lie over `k : Y_V ⟶ Y_U` (`pc ≫ p_U = p_V ≫ k`), let
`ι_U : X_U ⟶ P_U`, `ι_V : X_V ⟶ P_V` and `y : X_V ⟶ X_U` form a commutative square
`y ≫ ι_U = ι_V ≫ pc`, and put `f_U = ι_U ≫ p_U`, `f_V = ι_V ≫ p_V`.  Let `ψ_U : A_U ⟶ p_{U*}O_U`,
`ψ_V : A_V ⟶ p_{V*}O_V`, `Φ : A_V ⟶ k^*A_U` with left inverse `c`, and `Θ : pc^*O_U ≅ O_V` carry
`Φ` followed by the base change of `ψ_U` to `ψ_V`.  Then the pullback along `y` of the adjoint
`f_U^*A_U ⟶ ι_U^*O_U` of `ψ_U`, followed by the comparison `y^*ι_U^*O_U ≅ ι_V^*O_V` along the
square, is the identification `y^*f_U^*A_U ≅ f_V^*k^*A_U ⟶ f_V^*A_V` followed by the adjoint of
`ψ_V`. -/
private theorem pullback_map_adjointPsi_comp_aux
    {YU YV PU PV XU XV : Scheme.{u}} (pU : PU ⟶ YU) (pV : PV ⟶ YV) (k : YV ⟶ YU)
    (pc : PV ⟶ PU) (hpcT : pc ≫ pU = pV ≫ k) (ιU : XU ⟶ PU) (ιV : XV ⟶ PV) (y : XV ⟶ XU)
    (hsq : y ≫ ιU = ιV ≫ pc) (fU : XU ⟶ YU) (fV : XV ⟶ YV) (hfU : fU = ιU ≫ pU)
    (hfV : fV = ιV ≫ pV) (hyf : y ≫ fU = fV ≫ k)
    {AU : YU.Modules} {AV : YV.Modules} {OU : PU.Modules} {OV : PV.Modules}
    (ψU : AU ⟶ (Scheme.Modules.pushforward pU).obj OU)
    (ψV : AV ⟶ (Scheme.Modules.pushforward pV).obj OV)
    (Φ : AV ⟶ (Scheme.Modules.pullback k).obj AU) (Θ : (Scheme.Modules.pullback pc).obj OU ≅ OV)
    (hB2 : (Φ ≫ basePsi pU pV k pc hpcT ψU) ≫ (Scheme.Modules.pushforward pV).map Θ.hom = ψV)
    (c : (Scheme.Modules.pullback k).obj AU ⟶ AV) (hc : c ≫ Φ = 𝟙 _) :
    (Scheme.Modules.pullback y).map ((Scheme.Modules.pullbackCongr hfU).hom.app AU ≫
        (Scheme.Modules.pullbackComp ιU pU).inv.app AU ≫
        (Scheme.Modules.pullback ιU).map
          (((Scheme.Modules.pullbackPushforwardAdjunction pU).homEquiv _ _).symm ψU)) ≫
      (pullbackIsoOfSquare ιU ιV y pc hsq Θ).hom =
    ((Scheme.Modules.pullbackComp y fU).hom.app AU ≫ (Scheme.Modules.pullbackCongr hyf).hom.app AU ≫
      (Scheme.Modules.pullbackComp fV k).inv.app AU ≫ (Scheme.Modules.pullback fV).map c) ≫
      (Scheme.Modules.pullbackCongr hfV).hom.app AV ≫
        (Scheme.Modules.pullbackComp ιV pV).inv.app AV ≫
        (Scheme.Modules.pullback ιV).map
          (((Scheme.Modules.pullbackPushforwardAdjunction pV).homEquiv _ _).symm ψV) := by
  subst hB2 hfU hfV
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_doublePullbackSection y (ιU ≫ pU)
    fun U a => ?_
  -- the opens
  have hVk : y ⁻¹ᵁ ((ιU ≫ pU) ⁻¹ᵁ U) ≤ ιV ⁻¹ᵁ (pV ⁻¹ᵁ (k ⁻¹ᵁ U)) := by
    have e : (y ≫ ιU) ≫ pU = ιV ≫ pV ≫ k := by rw [Category.assoc, hyf, Category.assoc]
    exact (congrArg (fun φ => φ ⁻¹ᵁ U) e).le
  have hVsq : y ⁻¹ᵁ ((ιU ≫ pU) ⁻¹ᵁ U) ≤ (ιV ≫ pc) ⁻¹ᵁ (pU ⁻¹ᵁ U) :=
    (congrArg (fun φ => φ ⁻¹ᵁ (pU ⁻¹ᵁ U)) hsq).le
  have hWk : pV ⁻¹ᵁ (k ⁻¹ᵁ U) ≤ pc ⁻¹ᵁ (pU ⁻¹ᵁ U) := (congrArg (fun φ => φ ⁻¹ᵁ U) hpcT).ge
  have hVfk : y ⁻¹ᵁ ((ιU ≫ pU) ⁻¹ᵁ U) ≤ ((ιV ≫ pV) ≫ k) ⁻¹ᵁ U := hVk
  refine Eq.trans (b := pullbackSection ιV OV (pV ⁻¹ᵁ (k ⁻¹ᵁ U)) (y ⁻¹ᵁ ((ιU ≫ pU) ⁻¹ᵁ U)) hVk
      (Θ.hom.val.app (op (pV ⁻¹ᵁ (k ⁻¹ᵁ U)))
        (pullbackSection pc OU (pU ⁻¹ᵁ U) (pV ⁻¹ᵁ (k ⁻¹ᵁ U)) hWk (ψU.val.app (op U) a)))) ?_ ?_
  · -- the left side
    have hX := pullbackAdjointOfComp_val_app_pullbackSection ιU pU ψU U ((ιU ≫ pU) ⁻¹ᵁ U) le_rfl
      le_rfl a
    refine val_app_comp_of_eq _ _ _ _
      ((Scheme.Modules.pullbackSection_naturality y _ ((ιU ≫ pU) ⁻¹ᵁ U) _ le_rfl _).trans
        (congrArg (pullbackSection y _ ((ιU ≫ pU) ⁻¹ᵁ U) (y ⁻¹ᵁ ((ιU ≫ pU) ⁻¹ᵁ U)) le_rfl)
          hX)) ?_
    refine val_app_comp_of_eq ((Scheme.Modules.pullbackComp y ιU).hom.app OU) _ _ _
      (Scheme.Modules.pullbackSection_comp y ιU OU (pU ⁻¹ᵁ U) ((ιU ≫ pU) ⁻¹ᵁ U) _ le_rfl
        le_rfl le_rfl _) ?_
    refine val_app_comp_of_eq ((Scheme.Modules.pullbackCongr hsq).hom.app OU) _ _ _
      (Scheme.Modules.pullbackSection_congr hsq OU (pU ⁻¹ᵁ U) _ le_rfl hVsq _) ?_
    refine val_app_comp_of_eq ((Scheme.Modules.pullbackComp ιV pc).inv.app OU) _ _ _
      (pullbackComp_inv_val_app_pullbackSection ιV pc OU (pU ⁻¹ᵁ U) (pV ⁻¹ᵁ (k ⁻¹ᵁ U)) _ hWk hVk
        hVsq _) ?_
    exact Scheme.Modules.pullbackSection_naturality ιV Θ.hom (pV ⁻¹ᵁ (k ⁻¹ᵁ U)) _ hVk _
  · -- the right side
    have hbase : ((Φ ≫ basePsi pU pV k pc hpcT ψU) ≫
        (Scheme.Modules.pushforward pV).map Θ.hom).val.app (op (k ⁻¹ᵁ U))
          (c.val.app (op (k ⁻¹ᵁ U)) (pullbackSection k AU U (k ⁻¹ᵁ U) le_rfl a)) =
        Θ.hom.val.app (op (pV ⁻¹ᵁ (k ⁻¹ᵁ U)))
          (pullbackSection pc OU (pU ⁻¹ᵁ U) (pV ⁻¹ᵁ (k ⁻¹ᵁ U)) hWk (ψU.val.app (op U) a)) := by
      have hΦc : Φ.val.app (op (k ⁻¹ᵁ U)) (c.val.app (op (k ⁻¹ᵁ U))
          (pullbackSection k AU U (k ⁻¹ᵁ U) le_rfl a)) =
          pullbackSection k AU U (k ⁻¹ᵁ U) le_rfl a :=
        congrArg (fun t => t.val.app (op (k ⁻¹ᵁ U)) (pullbackSection k AU U (k ⁻¹ᵁ U) le_rfl a))
          hc
      refine val_app_comp_of_eq _ _ _ _ (val_app_comp_of_eq _ _ _ _ hΦc
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi_pullbackSection_preimage
          pU pV k pc hpcT ψU U a)) ?_
      rfl
    symm
    refine val_app_comp_of_eq (y := pullbackSection (ιV ≫ pV) AV (k ⁻¹ᵁ U) _ hVk
      (c.val.app (op (k ⁻¹ᵁ U)) (pullbackSection k AU U (k ⁻¹ᵁ U) le_rfl a))) _ _ _ _ ?_ ?_
    · refine val_app_comp_of_eq ((Scheme.Modules.pullbackComp y (ιU ≫ pU)).hom.app AU) _ _ _
        (Scheme.Modules.pullbackSection_comp y (ιU ≫ pU) AU U ((ιU ≫ pU) ⁻¹ᵁ U) _ le_rfl le_rfl
          le_rfl a) ?_
      refine val_app_comp_of_eq ((Scheme.Modules.pullbackCongr hyf).hom.app AU) _ _ _
        (Scheme.Modules.pullbackSection_congr hyf AU U _ le_rfl hVfk a) ?_
      refine val_app_comp_of_eq ((Scheme.Modules.pullbackComp (ιV ≫ pV) k).inv.app AU) _ _ _
        (pullbackComp_inv_val_app_pullbackSection (ιV ≫ pV) k AU U (k ⁻¹ᵁ U) _ le_rfl hVk hVfk a) ?_
      exact Scheme.Modules.pullbackSection_naturality (ιV ≫ pV) c (k ⁻¹ᵁ U) _ hVk _
    exact (pullbackAdjointOfComp_val_app_pullbackSection ιV pV _ (k ⁻¹ᵁ U) _ hVk hVk _).trans
      (congrArg (pullbackSection ιV OV (pV ⁻¹ᵁ (k ⁻¹ᵁ U)) (y ⁻¹ᵁ ((ιU ≫ pU) ⁻¹ᵁ U)) hVk) hbase)

/-- **`ψ` in adjoint form is carried along a morphism lying over a morphism of the base, at free
variables.**  Let `pc : P_V ⟶ P_U` lie over `k : Y_V ⟶ Y_U` (`pc ≫ p_U = p_V ≫ k`), let
`ι_U : X_U ⟶ P_U`, `ι_V : X_V ⟶ P_V` and `y : X_V ⟶ X_U` form a commutative square
`y ≫ ι_U = ι_V ≫ pc`, and put `f_U = ι_U ≫ p_U`, `f_V = ι_V ≫ p_V`.  Let `ψ_U : A_U ⟶ p_{U*}O_U`,
`ψ_V : A_V ⟶ p_{V*}O_V`, `Φ : A_V ⟶ k^*A_U`, and let `Θ : pc^*O_U ≅ O_V` carry `Φ` followed by the
base change of `ψ_U` to `ψ_V`.  For an isomorphism `c : k^*A_U ≅ A_V` inverse to `Φ`, the pullback
along `y` of the adjoint `f_U^*A_U ⟶ ι_U^*O_U` of `ψ_U`, followed by the comparison
`y^*ι_U^*O_U ≅ ι_V^*O_V` along the square, is the comparison `y^*f_U^*A_U ≅ f_V^*A_V` along
`y ≫ f_U = f_V ≫ k` followed by the adjoint of `ψ_V`. -/
theorem pullback_map_adjointPsi_comp_pullbackIsoOfSquare
    {YU YV PU PV XU XV : Scheme.{u}} (pU : PU ⟶ YU) (pV : PV ⟶ YV) (k : YV ⟶ YU)
    (pc : PV ⟶ PU) (hpcT : pc ≫ pU = pV ≫ k) (ιU : XU ⟶ PU) (ιV : XV ⟶ PV) (y : XV ⟶ XU)
    (hsq : y ≫ ιU = ιV ≫ pc) (fU : XU ⟶ YU) (fV : XV ⟶ YV) (hfU : fU = ιU ≫ pU)
    (hfV : fV = ιV ≫ pV) (hyf : y ≫ fU = fV ≫ k)
    {AU : YU.Modules} {AV : YV.Modules} {OU : PU.Modules} {OV : PV.Modules}
    (ψU : AU ⟶ (Scheme.Modules.pushforward pU).obj OU)
    (ψV : AV ⟶ (Scheme.Modules.pushforward pV).obj OV)
    (Φ : AV ⟶ (Scheme.Modules.pullback k).obj AU) (Θ : (Scheme.Modules.pullback pc).obj OU ≅ OV)
    (hB2 : (Φ ≫ basePsi pU pV k pc hpcT ψU) ≫ (Scheme.Modules.pushforward pV).map Θ.hom = ψV)
    (c : (Scheme.Modules.pullback k).obj AU ≅ AV) (hc : c.hom ≫ Φ = 𝟙 _) :
    (Scheme.Modules.pullback y).map (pullbackAdjointOfComp ιU pU fU hfU ψU) ≫
      (pullbackIsoOfSquare ιU ιV y pc hsq Θ).hom =
    (pullbackIsoOfSquare fU fV y k hyf c).hom ≫ pullbackAdjointOfComp ιV pV fV hfV ψV :=
  pullback_map_adjointPsi_comp_aux pU pV k pc hpcT ιU ιV y hsq fU fV hfU hfV hyf ψU ψV Φ Θ hB2
    c.hom hc

open Stacks.AlgebraicGeometry.RelativeProjTwists (SchemeGradedAlgebra) in
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS) in
/-- The direct image of the degree-`n` piece of a comparison of sheaves of graded algebras, read
through `AlgebraicGeometry.Space.gradedPieceIso`. -/
theorem pushforward_map_gradedPieceIso_hom {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    {G : SchemeGradedAlgebra X} {N : SchemeGradedAlgebra Y} (e : pbAlgS f G ≅ N) (n : ℤ)
    (p : Y ⟶ Z) :
    (Scheme.Modules.pushforward p).map (gradedPieceIso f e n).hom =
      (Scheme.Modules.pushforward p).map (e.hom.app n) :=
  rfl

open Stacks.AlgebraicGeometry.RelativeProjTwists (SchemeGradedAlgebra) in
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS) in
/-- `AlgebraicGeometry.Space.pullback_map_adjointPsi_comp_pullbackIsoOfSquare` for the degree-`n`
piece of a comparison `e : pc^*G_U ≅ G_V` of sheaves of graded algebras, with the four morphisms
named: a consumer supplies them by their defining equations, so that no two spellings of a
composite are ever compared. -/
theorem pullback_map_comp_eq_of_adjointPsi
    {YU YV PU PV XU XV : Scheme.{u}} {pU : PU ⟶ YU} {pV : PV ⟶ YV} {k : YV ⟶ YU}
    {pc : PV ⟶ PU} {hpcT : pc ≫ pU = pV ≫ k} {ιU : XU ⟶ PU} {ιV : XV ⟶ PV} {y : XV ⟶ XU}
    {hsq : y ≫ ιU = ιV ≫ pc} {fU : XU ⟶ YU} {fV : XV ⟶ YV} {hfU : fU = ιU ≫ pU}
    {hfV : fV = ιV ≫ pV} {hyf : y ≫ fU = fV ≫ k}
    {AU : YU.Modules} {AV : YV.Modules} {GU : SchemeGradedAlgebra PU} {GV : SchemeGradedAlgebra PV}
    {e : pbAlgS pc GU ≅ GV} {n : ℤ}
    {ψU : AU ⟶ (Scheme.Modules.pushforward pU).obj (GU.piece n)}
    {ψV : AV ⟶ (Scheme.Modules.pushforward pV).obj (GV.piece n)}
    {Φ : AV ⟶ (Scheme.Modules.pullback k).obj AU}
    {c : (Scheme.Modules.pullback k).obj AU ≅ AV}
    {φU : (Scheme.Modules.pullback fU).obj AU ⟶ (Scheme.Modules.pullback ιU).obj (GU.piece n)}
    {φV : (Scheme.Modules.pullback fV).obj AV ⟶ (Scheme.Modules.pullback ιV).obj (GV.piece n)}
    {T : (Scheme.Modules.pullback y).obj ((Scheme.Modules.pullback ιU).obj (GU.piece n)) ⟶
      (Scheme.Modules.pullback ιV).obj (GV.piece n)}
    {ch : (Scheme.Modules.pullback y).obj ((Scheme.Modules.pullback fU).obj AU) ⟶
      (Scheme.Modules.pullback fV).obj AV}
    (hB2 : (Φ ≫ basePsi pU pV k pc hpcT ψU) ≫ (Scheme.Modules.pushforward pV).map (e.hom.app n) =
      ψV)
    (hφU : φU = pullbackAdjointOfComp ιU pU fU hfU ψU)
    (hφV : φV = pullbackAdjointOfComp ιV pV fV hfV ψV)
    (hT : T = (pullbackIsoOfSquare ιU ιV y pc hsq (gradedPieceIso pc e n)).hom)
    (hch : ch = (pullbackIsoOfSquare fU fV y k hyf c).hom)
    (hc : c.hom ≫ Φ = 𝟙 _) :
    (Scheme.Modules.pullback y).map φU ≫ T = ch ≫ φV := by
  subst hφU hφV hT hch
  exact pullback_map_adjointPsi_comp_pullbackIsoOfSquare pU pV k pc hpcT ιU ιV y hsq fU fV hfU hfV
    hyf ψU ψV Φ (gradedPieceIso pc e n)
    ((congrArg (fun t => (Φ ≫ basePsi pU pV k pc hpcT ψU) ≫ t)
      (pushforward_map_gradedPieceIso_hom pc e n pV)).trans hB2) c hc

open Stacks.AlgebraicGeometry.RelativeProjBridge (SheafGradedAlgebra) in
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj) in
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra) in
open Stacks.AlgebraicGeometry (GluedTwistAlgebra.twistDataOfGradedAlgebra) in
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS) in
/-- **Tag 01NR's `ψ` in adjoint form is carried along a morphism lying over a morphism of the
base**: `AlgebraicGeometry.Space.pullback_map_comp_eq_of_adjointPsi` for
`AlgebraicGeometry.Space.pullbackAdjointPsi`, at free graded algebras `A_U`, `A_V`. -/
theorem pullback_map_pullbackAdjointPsi_comp_eq
    {YU YV XU XV : Scheme.{u}} {AU : SheafGradedAlgebra YU} {AV : SheafGradedAlgebra YV}
    {k : YV ⟶ YU} {pc : (relativeProj AV).scheme ⟶ (relativeProj AU).scheme}
    {hpcT : pc ≫ (relativeProj AU).toBase = (relativeProj AV).toBase ≫ k}
    {ιU : XU ⟶ (relativeProj AU).scheme} {ιV : XV ⟶ (relativeProj AV).scheme} {y : XV ⟶ XU}
    {hsq : y ≫ ιU = ιV ≫ pc} {fU : XU ⟶ YU} {fV : XV ⟶ YV}
    {hfU : fU = ιU ≫ (relativeProj AU).toBase} {hfV : fV = ιV ≫ (relativeProj AV).toBase}
    {hyf : y ≫ fU = fV ≫ k}
    {e : pbAlgS pc (Tag07ZGTwist.twistAlgebra AU) ≅ Tag07ZGTwist.twistAlgebra AV} {n : ℕ}
    {Φ : AV.piece (n : ℤ) ⟶ (Scheme.Modules.pullback k).obj (AU.piece (n : ℤ))}
    {c : (Scheme.Modules.pullback k).obj (AU.piece (n : ℤ)) ≅ AV.piece (n : ℤ)}
    {φU : (Scheme.Modules.pullback fU).obj (AU.piece (n : ℤ)) ⟶
      (Scheme.Modules.pullback ιU).obj ((Tag07ZGTwist.twistAlgebra AU).piece (n : ℤ))}
    {φV : (Scheme.Modules.pullback fV).obj (AV.piece (n : ℤ)) ⟶
      (Scheme.Modules.pullback ιV).obj ((Tag07ZGTwist.twistAlgebra AV).piece (n : ℤ))}
    {T : (Scheme.Modules.pullback y).obj
        ((Scheme.Modules.pullback ιU).obj ((Tag07ZGTwist.twistAlgebra AU).piece (n : ℤ))) ⟶
      (Scheme.Modules.pullback ιV).obj ((Tag07ZGTwist.twistAlgebra AV).piece (n : ℤ))}
    {ch : (Scheme.Modules.pullback y).obj ((Scheme.Modules.pullback fU).obj (AU.piece (n : ℤ))) ⟶
      (Scheme.Modules.pullback fV).obj (AV.piece (n : ℤ))}
    (hB2 : (Φ ≫ basePsi (relativeProj AU).toBase (relativeProj AV).toBase k pc hpcT
        ((GluedTwistAlgebra.twistDataOfGradedAlgebra AU).ψ n)) ≫
        (Scheme.Modules.pushforward (relativeProj AV).toBase).map (e.hom.app (n : ℤ)) =
      (GluedTwistAlgebra.twistDataOfGradedAlgebra AV).ψ n)
    (hφU : φU = pullbackAdjointPsi AU ιU fU hfU n)
    (hφV : φV = pullbackAdjointPsi AV ιV fV hfV n)
    (hT : T = (pullbackIsoOfSquare ιU ιV y pc hsq (gradedPieceIso pc e (n : ℤ))).hom)
    (hch : ch = (pullbackIsoOfSquare fU fV y k hyf c).hom)
    (hc : c.hom ≫ Φ = 𝟙 _) :
    (Scheme.Modules.pullback y).map φU ≫ T = ch ≫ φV := by
  subst hφU hφV
  exact pullback_map_comp_eq_of_adjointPsi hB2 rfl rfl hT hch hc

open Stacks.AlgebraicGeometry.RelativeProjBridge (SheafGradedAlgebra) in
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj) in
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra) in
open Stacks.AlgebraicGeometry (GluedTwistAlgebra.twistDataOfGradedAlgebra) in
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS congrBaseChangePsi) in
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (situationAlgebra congrHom) in
/-- `AlgebraicGeometry.Space.pullback_map_pullbackAdjointPsi_comp_eq` with the base change of `ψ`
along a restriction `Φ : A_V ≅ k^*A_U` written as
`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.congrBaseChangePsi`, the form in which the
comparison of twists of Stacks 084B (3) carries `ψ` to `ψ`; that base change is named `ψ₀` by
its defining equation, so that a consumer's spelling of it is never unfolded. -/
theorem pullback_map_pullbackAdjointPsi_comp_eq_of_congr
    {YU YV XU XV : Scheme.{u}} {AU : SheafGradedAlgebra YU} {AV : SheafGradedAlgebra YV}
    {k : YV ⟶ YU}
    {Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra AV)
      (situationAlgebra (AU.pullback k))}
    {pc : (relativeProj AV).scheme ⟶ (relativeProj AU).scheme}
    {hpcT : pc ≫ (relativeProj AU).toBase = (relativeProj AV).toBase ≫ k}
    {ιU : XU ⟶ (relativeProj AU).scheme} {ιV : XV ⟶ (relativeProj AV).scheme} {y : XV ⟶ XU}
    {hsq : y ≫ ιU = ιV ≫ pc} {fU : XU ⟶ YU} {fV : XV ⟶ YV}
    {hfU : fU = ιU ≫ (relativeProj AU).toBase} {hfV : fV = ιV ≫ (relativeProj AV).toBase}
    {hyf : y ≫ fU = fV ≫ k}
    {e : pbAlgS pc (Tag07ZGTwist.twistAlgebra AU) ≅ Tag07ZGTwist.twistAlgebra AV} {n : ℕ}
    {c : (Scheme.Modules.pullback k).obj (AU.piece (n : ℤ)) ≅ AV.piece (n : ℤ)}
    {φU : (Scheme.Modules.pullback fU).obj (AU.piece (n : ℤ)) ⟶
      (Scheme.Modules.pullback ιU).obj ((Tag07ZGTwist.twistAlgebra AU).piece (n : ℤ))}
    {φV : (Scheme.Modules.pullback fV).obj (AV.piece (n : ℤ)) ⟶
      (Scheme.Modules.pullback ιV).obj ((Tag07ZGTwist.twistAlgebra AV).piece (n : ℤ))}
    {T : (Scheme.Modules.pullback y).obj
        ((Scheme.Modules.pullback ιU).obj ((Tag07ZGTwist.twistAlgebra AU).piece (n : ℤ))) ⟶
      (Scheme.Modules.pullback ιV).obj ((Tag07ZGTwist.twistAlgebra AV).piece (n : ℤ))}
    {ch : (Scheme.Modules.pullback y).obj ((Scheme.Modules.pullback fU).obj (AU.piece (n : ℤ))) ⟶
      (Scheme.Modules.pullback fV).obj (AV.piece (n : ℤ))}
    {ψ₀ : AV.piece (n : ℤ) ⟶ (Scheme.Modules.pushforward (relativeProj AV).toBase).obj
      ((pbAlgS pc (Tag07ZGTwist.twistAlgebra AU)).piece (n : ℤ))}
    (hB2 : ψ₀ ≫ (Scheme.Modules.pushforward (relativeProj AV).toBase).map (e.hom.app (n : ℤ)) =
      (GluedTwistAlgebra.twistDataOfGradedAlgebra AV).ψ n)
    (hψ₀ : ψ₀ = congrBaseChangePsi AU k Φ pc hpcT n)
    (hφU : φU = pullbackAdjointPsi AU ιU fU hfU n)
    (hφV : φV = pullbackAdjointPsi AV ιV fV hfV n)
    (hT : T = (pullbackIsoOfSquare ιU ιV y pc hsq (gradedPieceIso pc e (n : ℤ))).hom)
    (hch : ch = (pullbackIsoOfSquare fU fV y k hyf c).hom)
    (hc : c.hom ≫ (congrHom Φ).app (n : ℤ) = 𝟙 _) :
    (Scheme.Modules.pullback y).map φU ≫ T = ch ≫ φV := by
  subst hψ₀
  exact pullback_map_pullbackAdjointPsi_comp_eq hB2 hφU hφV hT hch hc

/-- Two squares `a_t ≫ T_t = c_t ≫ φ` and `a_s ≫ T_s = c_s ≫ φ` with a common `φ` give the square
`(c_t ≫ c_s⁻¹) ≫ a_s = a_t ≫ (T_t ≫ T_s⁻¹)` of transitions. -/
theorem comp_inv_comp_eq_of_squares {C : Type*} [Category C] {At As Bt Bs M N : C}
    (aT : At ⟶ Bt) (aS : As ⟶ Bs) (tT : Bt ≅ N) (tS : Bs ≅ N) (cT : At ≅ M) (cS : As ≅ M)
    (φ : M ⟶ N) (hT : aT ≫ tT.hom = cT.hom ≫ φ) (hS : aS ≫ tS.hom = cS.hom ≫ φ) :
    (cT.hom ≫ cS.inv) ≫ aS = aT ≫ tT.hom ≫ tS.inv := by
  have hS' : aS = cS.hom ≫ φ ≫ tS.inv := by
    rw [← Category.assoc, ← hS, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hS', Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc aT, hT, Category.assoc]

section Coherence

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The transport of `π^*M` along `a = b`, followed by the comparison of Stacks 03LU along `b ≫ π`,
is the comparison along `a ≫ π`, both read at a common `Q = a ≫ π = b ≫ π`. -/
theorem pullbackTransport_comp_modulePullbackCompIso_hom_app {T Y X : AlgebraicSpaces B S hS}
    (π : Y ⟶ X) {a b : T ⟶ Y} (h : a = b) {Q : T ⟶ X} (ha : a ≫ π = Q) (hb : b ≫ π = Q)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    pullbackTransport ((modulePullback B S hS π).obj M) h ≫
        (modulePullbackCompIso B S hS b π).hom.app M ≫ pullbackTransport M hb =
      (modulePullbackCompIso B S hS a π).hom.app M ≫ pullbackTransport M ha := by
  subst h hb
  simp [pullbackTransport]

/-- Unflattening, followed by the contraction along the source, is the contraction along the
target followed by the morphism unflattened. -/
theorem modulePullbackUnflatten_comp_modulePullbackCompIso_hom_app {V U Z : AlgebraicSpaces B S hS}
    (t s : V ⟶ U) (φ : U ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2)
    (x : (modulePullback B S hS (t ≫ φ)).obj M ⟶ (modulePullback B S hS (s ≫ φ)).obj M) :
    modulePullbackUnflatten φ x ≫ (modulePullbackCompIso B S hS s φ).hom.app M =
      (modulePullbackCompIso B S hS t φ).hom.app M ≫ x := by
  simp [modulePullbackUnflatten]

/-- **The canonical transition morphism of an inverse image `π^*M` is the identity of `M` read
along the two contractions** (the coherence of Stacks 03LU): for `t, s : V ⟶ U`, `φ : U ⟶ P` with
`t ≫ φ = s ≫ φ` and `π : P ⟶ X`, the unflattened transport of `π^*M` along `t ≫ φ = s ≫ φ`
followed by the contraction `s^*φ^*π^*M ≅ Q^*M` is the contraction `t^*φ^*π^*M ≅ Q^*M`, for
`Q = (t ≫ φ) ≫ π = (s ≫ φ) ≫ π`. -/
theorem modulePullbackUnflatten_pullbackTransport_comp_modulePullbackCompIso
    {V U P X : AlgebraicSpaces B S hS} (t s : V ⟶ U) (φ : U ⟶ P) (hφ : t ≫ φ = s ≫ φ)
    (π : P ⟶ X) {Q : V ⟶ X} (ht : (t ≫ φ) ≫ π = Q) (hs : (s ≫ φ) ≫ π = Q)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    modulePullbackUnflatten φ (pullbackTransport ((modulePullback B S hS π).obj M) hφ) ≫
        (modulePullbackCompIso B S hS s φ).hom.app ((modulePullback B S hS π).obj M) ≫
          (modulePullbackCompIso B S hS (s ≫ φ) π).hom.app M ≫ pullbackTransport M hs =
      (modulePullbackCompIso B S hS t φ).hom.app ((modulePullback B S hS π).obj M) ≫
        (modulePullbackCompIso B S hS (t ≫ φ) π).hom.app M ≫ pullbackTransport M ht := by
  rw [reassoc_of% (modulePullbackUnflatten_comp_modulePullbackCompIso_hom_app t s φ _
      (pullbackTransport ((modulePullback B S hS π).obj M) hφ)),
    pullbackTransport_comp_modulePullbackCompIso_hom_app π hφ ht hs M]

/-- **The canonical transition morphism of `φ^*(π^*M)` on a groupoid is the identity of `M` read
along the two contractions** (`AlgebraicGeometry.Space.spaceBaseDescent` of an inverse image, the
coherence of Stacks 03LU), for `Q = (t ≫ φ) ≫ π = (s ≫ φ) ≫ π`. -/
theorem spaceBaseDescent_comp_modulePullbackCompIso {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A) {P X : AlgebraicSpaces B S hS}
    (φ : G.objects ⟶ P) (hφ : G.target ≫ φ = G.source ≫ φ) (π : P ⟶ X) {Q : G.arrows ⟶ X}
    (ht : (G.target ≫ φ) ≫ π = Q) (hs : (G.source ≫ φ) ≫ π = Q)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    comp₂ (spaceBaseDescent B S hS G φ hφ ((modulePullback B S hS π).obj M))
        (comp₂ ((modulePullbackCompIso B S hS G.source φ).hom.app
            ((modulePullback B S hS π).obj M))
          (comp₂ ((modulePullbackCompIso B S hS (G.source ≫ φ) π).hom.app M)
            (pullbackTransport M hs))) =
      comp₂ ((modulePullbackCompIso B S hS G.target φ).hom.app ((modulePullback B S hS π).obj M))
        (comp₂ ((modulePullbackCompIso B S hS (G.target ≫ φ) π).hom.app M)
          (pullbackTransport M ht)) :=
  modulePullbackUnflatten_pullbackTransport_comp_modulePullbackCompIso G.target G.source φ hφ π
    ht hs M

/-- The abstract shape of `AlgebraicGeometry.Space.transitionCommutes_of_chartSquares`, at
variables. -/
private theorem comp_map_eq_of_chartSquares {C D : Type*} [Category C] [Category D]
    (Pt Ps : C ⥤ D) {F G : C} {Ct Cs Q M : D} (δ : Pt.obj F ⟶ Ps.obj F) (ι : F ⟶ G)
    (C3t : Pt.obj G ≅ Ct) (C3s : Ps.obj G ≅ Cs) (chT : Ct ⟶ M) (chS : Cs ⟶ M) (chSi : M ⟶ Cs)
    (hchS : comp₂ chS chSi = 𝟙 _) (canT : Pt.obj F ⟶ Q) (canS : Ps.obj F ⟶ Q) (ιR : Q ⟶ M)
    (hCoh : comp₂ δ canS = canT) (hsqT : comp₂ (Pt.map ι) (comp₂ C3t.hom chT) = comp₂ canT ιR)
    (hsqS : comp₂ (Ps.map ι) (comp₂ C3s.hom chS) = comp₂ canS ιR) :
    δ ≫ Ps.map ι = Pt.map ι ≫ C3t.hom ≫ chT ≫ chSi ≫ C3s.inv := by
  simp only [comp₂_eq] at hchS hCoh hsqT hsqS
  have hsqS' : Ps.map ι = canS ≫ ιR ≫ chSi ≫ C3s.inv := by
    rw [← reassoc_of% hsqS]
    simp only [reassoc_of% hchS, Iso.hom_inv_id, Category.comp_id]
  rw [hsqS', reassoc_of% hCoh, ← reassoc_of% hsqT]

/-- **A morphism `ι : F ⟶ G` carries a transition `δ` of `F` to the transition of `G` read through
chart identifications**: if the two pullbacks of `ι`, read through identifications `C3` and
comparisons `ch` into a common `M`, are both a common `ι_R` preceded by morphisms `can` into a
common `Q`, the comparison `ch_s` is invertible, and `δ` is read as the identity of `Q` through the
`can`, then `ι` carries `δ` to `τ = C3_t ≫ ch_t ≫ ch_s⁻¹ ≫ C3_s⁻¹`.  The hypotheses are written
with named binary composites (`CategoryTheory.comp₂`), so that they are compared factor by factor
with identities whose intermediate objects are spelled differently. -/
theorem transitionCommutes_of_chartSquares {U V : AlgebraicSpaces B S hS} {a b : V ⟶ U}
    {F G : Modules.{u, u} B S hS U.1 U.2} {Ct Cs Q M : Modules.{u, u} B S hS V.1 V.2}
    (δ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) (ι : F ⟶ G)
    (C3t : (modulePullback B S hS a).obj G ≅ Ct) (C3s : (modulePullback B S hS b).obj G ≅ Cs)
    (chT : Ct ⟶ M) (chS : Cs ⟶ M) (chSi : M ⟶ Cs) (hchS : comp₂ chS chSi = 𝟙 _)
    (canT : (modulePullback B S hS a).obj F ⟶ Q) (canS : (modulePullback B S hS b).obj F ⟶ Q)
    (ιR : Q ⟶ M) (hCoh : comp₂ δ canS = canT)
    (hsqT : comp₂ ((modulePullback B S hS a).map ι) (comp₂ C3t.hom chT) = comp₂ canT ιR)
    (hsqS : comp₂ ((modulePullback B S hS b).map ι) (comp₂ C3s.hom chS) = comp₂ canS ιR)
    (τ : (modulePullback B S hS a).obj G ⟶ (modulePullback B S hS b).obj G)
    (hτ : τ = comp₂ C3t.hom (comp₂ chT (comp₂ chSi C3s.inv))) :
    TransitionCommutes B S hS δ τ ι := by
  subst hτ
  unfold TransitionCommutes
  simp only [comp₂_eq]
  exact comp_map_eq_of_chartSquares _ _ δ ι C3t C3s chT chS chSi hchS canT canS ιR hCoh hsqT hsqS

/-- The transport of `π^*M` along `a = b`, between the contractions along `a ≫ π` and `b ≫ π`, is
the transport of `M`.  The intermediate object is spelled `a^*(π^*M)`, as the source of the
transport, so that the statement matches a chain in which the transport follows a morphism into
`a^*(π^*M)`. -/
theorem modulePullbackCompIso_inv_comp_pullbackTransport_comp_hom {T Y X : AlgebraicSpaces B S hS}
    (π : Y ⟶ X) {a b : T ⟶ Y} (h : a = b) (M : Modules.{u, u} B S hS X.1 X.2) :
    CategoryStruct.comp (Y := (modulePullback B S hS a).obj ((modulePullback B S hS π).obj M))
      ((modulePullbackCompIso B S hS a π).inv.app M)
        (pullbackTransport ((modulePullback B S hS π).obj M) h ≫
          (modulePullbackCompIso B S hS b π).hom.app M) =
      pullbackTransport M (congrArg (· ≫ π) h : a ≫ π = b ≫ π) := by
  subst h
  change _ ≫ 𝟙 _ ≫ _ = 𝟙 _
  rw [Category.id_comp, Iso.inv_hom_id_app]

end Coherence

end Generic

namespace RelativeProjSituation

open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (congrHom)

variable (s : RelativeProjSituation.{u, m})

/-- **The restriction `(v^*𝒜)_n` of the degree-`n` piece of `𝒜` to a scheme point `v : V ⟶ X`**,
as a quasi-coherent module on the scheme of `V`: the Zariski reading of the inverse image of
`𝒜_n` along `v`. -/
abbrev pointPieceQcoh (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (n : ℤ) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V).ringCatSheaf).FullSubcategory :=
  zariskiReadingQcoh V ((etalePointAlgebra s.shrink.algebra V v).piece n)
    (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent v n)

section Chain

variable {U V : BigFppfOver s.site s.base s.containsBase} {u : yoneda.obj U ⟶ s.space.1}
  {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U) (hv : yoneda.map k ≫ u = v)
  (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
  (hy : s.relativeProjPoints.LiesOver y k)

include hy in
/-- A morphism of base changes lying over `k` commutes, on schemes, with the structure morphisms
to the test objects. -/
theorem fibreToBase_comp_of_liesOver :
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y) ≫ s.fibreToBase U u =
      s.fibreToBase V v ≫
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k) :=
  ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _).symm.trans
    ((congrArg (BigFppfOver.toScheme s.site s.base s.containsBase).map hy.1).trans
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _))

omit y hy in
/-- The comparison of the restrictions of Stacks 084A is inverse to the restriction map of the
restriction datum, read as a homomorphism of graded algebras of Situation 01NN. -/
theorem pointComparisonUnital_comp_congrHom_restrict (n : ℤ) :
    (pointComparisonUnital (s := s.shrink) k u v hv).app n ≫
      (congrHom (A₁ := s.shrink.pointAlgebra V v)
        (A₂ := (s.shrink.pointAlgebra U u).pullback
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k))
        (s.quadrupleRestriction.restrict k u v hv)).app n = 𝟙 _ :=
  @IsIso.hom_inv_id _ _ _ _ _ (isIso_pointComparisonUnital_app (s := s.shrink) k u v hv n)

/-- **The identification `y^*π_U^*(u^*𝒜)_n ≅ π_V^*(v^*𝒜)_n` of the sources of `ψ`** along a
morphism `y : V ×_X P ⟶ U ×_X P` of base changes lying over `k : V ⟶ U`: the comparison along the
square `y ≫ π_U = π_V ≫ k` (`AlgebraicGeometry.Space.pullbackIsoOfSquare`) of the comparison
`k^*(u^*𝒜)_n ≅ (v^*𝒜)_n` of the restrictions of Stacks 084A, as an isomorphism on the scheme of
`V ×_X P`. -/
def pointPieceChainSchemeIso (n : ℤ) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).obj
        ((Scheme.Modules.pullback (s.fibreToBase U u)).obj ((s.shrink.pointAlgebra U u).piece n)) ≅
      (Scheme.Modules.pullback (s.fibreToBase V v)).obj ((s.shrink.pointAlgebra V v).piece n) :=
  pullbackIsoOfSquare (s.fibreToBase U u) (s.fibreToBase V v)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
      (s.fibreToBase_comp_of_liesOver k y hy)
      (M := (s.shrink.pointAlgebra U u).piece n) (M' := (s.shrink.pointAlgebra V v).piece n)
      (@asIso _ _ _ _ ((pointComparisonUnital (s := s.shrink) k u v hv).app n)
        (isIso_pointComparisonUnital_app (s := s.shrink) k u v hv n))

/-- **The identification `y^*π_U^*(u^*𝒜)_n ≅ π_V^*(v^*𝒜)_n` of the sources of `ψ`**, as an
isomorphism of quasi-coherent modules
(`AlgebraicGeometry.Space.RelativeProjSituation.pointPieceChainSchemeIso`). -/
def pointPieceChainIso (n : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase y
        (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom U u) (s.pointPieceQcoh U u n)) ≅
      quasicoherentPullbackObj s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom V v) (s.pointPieceQcoh V v n) :=
  ObjectProperty.isoMk _ (s.pointPieceChainSchemeIso k hv y hy n)

/-- **Tag 01NR's `ψ` on the base changes is carried along a morphism lying over `k`**: on the
scheme of `V ×_X P`, the pullback along `y` of `ψ` at `U` (in adjoint form), followed by the
comparison of the twists along `y`, is the identification of the sources followed by `ψ` at `V`.
This is the comparison of twists carrying `ψ` to `ψ`
(`AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparisonPsi_comp_pointTwistComparison`)
transposed along `π_V^* ⊣ π_{V*}`. -/
theorem pullback_map_psiChartSchemeHom_comp (n : ℕ) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).map
        (s.psiChartSchemeHomOfAdjoint U u n) ≫ (s.twistPieceComparison k hv y hy (n : ℤ)).hom.hom =
      (s.pointPieceChainSchemeIso k hv y hy (n : ℤ)).hom ≫ s.psiChartSchemeHomOfAdjoint V v n := by
  refine pullback_map_pullbackAdjointPsi_comp_eq_of_congr (AU := s.shrink.pointAlgebra U u)
    (AV := s.shrink.pointAlgebra V v)
    (k := (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (Φ := s.quadrupleRestriction.restrict k u v hv)
    (pc := (BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    (hpcT := s.toScheme_map_comp_toBase_of_liesOver hv hy)
    (ιU := s.toRelativeProj U u) (ιV := s.toRelativeProj V v)
    (y := (BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    (hsq := s.map_comp_toRelativeProj y)
    (fU := s.fibreToBase U u) (fV := s.fibreToBase V v)
    (hfU := s.fibreToBase_eq U u) (hfV := s.fibreToBase_eq V v)
    (hyf := s.fibreToBase_comp_of_liesOver k y hy)
    (e := s.pointTwistComparison k u v hv
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (s.toScheme_map_eq_of_liesOver hv hy)) (n := n)
    (c := @asIso _ _ _ _ ((pointComparisonUnital (s := s.shrink) k u v hv).app (n : ℤ))
        (isIso_pointComparisonUnital_app (s := s.shrink) k u v hv (n : ℤ)))
    (ψ₀ := s.pointTwistComparisonPsi k u v hv
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (s.toScheme_map_comp_toBase_of_liesOver hv hy) n)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact s.pointTwistComparisonPsi_comp_pointTwistComparison k u v hv
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (s.toScheme_map_eq_of_liesOver hv hy) (s.toScheme_map_comp_toBase_of_liesOver hv hy) n
  · rfl
  · rfl
  · rfl
  · exact s.twistPieceComparison_hom_hom k hv y hy (n : ℤ)
  · exact congrArg Iso.hom (pointPieceChainSchemeIso.eq_1 s k hv y hy (n : ℤ))
  · exact s.pointComparisonUnital_comp_congrHom_restrict k hv (n : ℤ)

/-- **`AlgebraicGeometry.Space.RelativeProjSituation.pullback_map_psiChartSchemeHom_comp` as a
square of quasi-coherent modules** on the scheme of `V ×_X P`. -/
theorem quasicoherentPullbackMap_psiChartSchemeHom_comp (n : ℕ) :
    quasicoherentPullbackMap s.site s.base s.containsBase y
        (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint U u n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom U u) (s.pointPieceQcoh U u (n : ℤ)) ⟶
            s.twistPieceQcoh U u (n : ℤ)) ≫
        (s.twistPieceComparison k hv y hy (n : ℤ)).hom =
      (s.pointPieceChainIso k hv y hy (n : ℤ)).hom ≫
        (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint V v n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom V v) (s.pointPieceQcoh V v (n : ℤ)) ⟶
            s.twistPieceQcoh V v (n : ℤ)) :=
  ObjectProperty.hom_ext _ (s.pullback_map_psiChartSchemeHom_comp k hv y hy n)

end Chain

section Presentation

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The transition of the source of `ψ` on the presentation `P = P_U/P_R`**: on the scheme of
`P_R = R ×_X P`, the identification of the sources of `ψ` along the target projection followed by
the inverse of the identification along the source projection
(`AlgebraicGeometry.Space.RelativeProjSituation.pointPieceChainIso`). -/
def psiSourceTransition (n : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (s.pointPieceQcoh Px.U Px.toSpace n)) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom Px.U Px.toSpace) (s.pointPieceQcoh Px.U Px.toSpace n)) :=
  (s.pointPieceChainIso (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px) Px.target rfl
      (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor) n).hom ≫
    (s.pointPieceChainIso (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px) Px.source
      (s.map_source_comp_toSpace Px)
      (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor) n).inv

/-- **`ψ` on the scheme of `P_U` carries the transition of its source to the transition of the
twist** (Stacks 084D, the compatibility of `ψ` with the descent data, on schemes): on the scheme of
`P_R`, `σ ≫ s'^*ψ_U = t'^*ψ_U ≫ τ_n` for `σ` the transition of the source
(`AlgebraicGeometry.Space.RelativeProjSituation.psiSourceTransition`) and `τ_n` that of `𝒪(n)`
(`AlgebraicGeometry.Space.RelativeProjSituation.twistTransition`). -/
theorem psiSourceTransition_comp_quasicoherentPullbackMap (n : ℕ) :
    s.psiSourceTransition Px (n : ℤ) ≫
        quasicoherentPullbackMap s.site s.base s.containsBase
          (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
          (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace n) :
            quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
                (s.pointPieceQcoh Px.U Px.toSpace (n : ℤ)) ⟶
              s.twistPieceQcoh Px.U Px.toSpace (n : ℤ)) =
      quasicoherentPullbackMap s.site s.base s.containsBase
          (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
          (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace n) :
            quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
                (s.pointPieceQcoh Px.U Px.toSpace (n : ℤ)) ⟶
              s.twistPieceQcoh Px.U Px.toSpace (n : ℤ)) ≫
        s.twistTransition Px (n : ℤ) := by
  refine comp_inv_comp_eq_of_squares _ _ _ _ _ _
    (ObjectProperty.homMk
      (s.psiChartSchemeHomOfAdjoint Px.R (RelativeProjPoints.relationPoint Px) n) :
        quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom Px.R (RelativeProjPoints.relationPoint Px))
            (s.pointPieceQcoh Px.R (RelativeProjPoints.relationPoint Px) (n : ℤ)) ⟶
          s.twistPieceQcoh Px.R (RelativeProjPoints.relationPoint Px) (n : ℤ)) ?_ ?_
  · exact s.quasicoherentPullbackMap_psiChartSchemeHom_comp _ _ _ _ n
  · exact s.quasicoherentPullbackMap_psiChartSchemeHom_comp _ _ _ _ n

/-- **The module attached to `ψ` on the scheme of `P_U` carries the attached transition of its
source to that of the twist** (Stacks 03DX (2) applied to
`AlgebraicGeometry.Space.RelativeProjSituation.psiSourceTransition_comp_quasicoherentPullbackMap`,
by `AlgebraicGeometry.Space.representedSchemeTransition_naturality`). -/
theorem transitionCommutes_psiChartSchemeHom (n : ℕ) :
    TransitionCommutes s.site s.base s.containsBase
      (representedSchemeTransition s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
          (s.pointPieceQcoh Px.U Px.toSpace (n : ℤ)))
        (s.psiSourceTransition Px (n : ℤ)))
      (representedSchemeTransition s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace (n : ℤ)) (s.twistTransition Px (n : ℤ)))
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace)).functor.map
          (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace n) :
            quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
                (s.pointPieceQcoh Px.U Px.toSpace (n : ℤ)) ⟶
              s.twistPieceQcoh Px.U Px.toSpace (n : ℤ))).hom :=
  representedSchemeTransition_naturality s.site s.base s.containsBase _ _ _ _ _ _
    (s.psiSourceTransition_comp_quasicoherentPullbackMap Px n)

end Presentation

end RelativeProjSituation

end AlgebraicGeometry.Space

end
