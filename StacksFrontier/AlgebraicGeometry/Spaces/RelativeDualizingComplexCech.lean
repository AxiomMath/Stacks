module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BoundedBelowCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexUniqueness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfCechHypercovering
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPair
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Relative dualizing complexes on a Čech hypercovering

Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite presentation and
`b₀ : V₀ ⟶ Y` a morphism from a disjoint union of affines. Write `V` for the Čech nerve of `b₀`
and `U_n = V_n ×_Y X`, with projections `f_n : U_n ⟶ V_n`. The base change `f_0` has a relative
dualizing complex `D₀`; its base changes along the simplicial structure maps of `U` are relative
dualizing complexes on the `f_n` (Stacks 0E6C), any two of which are isomorphic by a unique
isomorphism of pairs (Stacks 0E5Z), and they have no negative self-extensions (Stacks 0E5Y).
These are the inputs of the gluing in the proof of Stacks 0E61.

## Main results

* `AlgebraicGeometry.Space.RelativeDualizingComplex.hom_shift_eq_zero`: a relative dualizing
  complex has no negative self-extensions.
* `AlgebraicGeometry.BigFppfSpaceSite.nonempty_relativeDualizingComplex_cechOverPullbackFst_zero`:
  the relative dualizing complex in degree zero.
* `AlgebraicGeometry.BigFppfSpaceSite.exists_iso_cocycle_cechOverPullback`: the descent
  isomorphism on `U_1` and its cocycle condition on `U_2`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
-- No global `HasDerivedCategory` instance applies to modules on small étale sites, which are not
-- `SmallCategory`; at low priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeDualizingComplex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {hf : IsProper B S hS f.hom} {hfl : IsFlat B S hS f.hom}
  {hfp : IsFinitePresentation B S hS f.hom}

/-- **A relative dualizing complex has no negative self-extensions**: `Ext^i(ω, ω) = 0` for
`i < 0`, since `R𝓗om(ω, ω) = 𝒪_X` (Stacks 0E5Y). -/
theorem hom_shift_eq_zero (D : RelativeDualizingComplex hZ f hf hfl hfp) (i : ℤ) (hi : i < 0)
    (g : D.ω ⟶ D.ω⟦i⟧) : g = 0 :=
  ((isZero_homology_globalDerivedHom_iff X D.ω D.ω i).1
    (isZero_homology_derivedModuleGlobalSectionsSmallEtale_of_isGE X _ 0
      (isGE_smallEtaleDerivedSheafHom D D (isIso_smallEtaleDerivedHomothety_and_isLE D).1) i
      hi)).elim g 0

end AlgebraicGeometry.Space.RelativeDualizingComplex

namespace AlgebraicGeometry.Space.RelativeDualizingPair

section Aux

variable {C D : Type*} [Category* C] [Category* D]

/-- Morphisms compatible with maps to a fixed object compose, in an arbitrary category. -/
theorem map_comp_trace_of_aux (F : C ⥤ D) {A₁ A₂ A₃ : C} {O : D} {t₁ : F.obj A₁ ⟶ O}
    {t₂ : F.obj A₂ ⟶ O} {t₃ : F.obj A₃ ⟶ O} {m₁ : A₁ ⟶ A₂} {m₂ : A₂ ⟶ A₃}
    (h₁ : F.map m₁ ≫ t₂ = t₁) (h₂ : F.map m₂ ≫ t₃ = t₂) : F.map (m₁ ≫ m₂) ≫ t₃ = t₁ := by
  rw [Functor.map_comp, Category.assoc, h₂, h₁]

/-- The inverse of an isomorphism compatible with maps to a fixed object is compatible with them,
in an arbitrary category. -/
theorem map_inv_trace_of_aux (F : C ⥤ D) {A₁ A₂ : C} {O : D} {t₁ : F.obj A₁ ⟶ O}
    {t₂ : F.obj A₂ ⟶ O} (e : A₁ ≅ A₂) (h : F.map e.hom ≫ t₂ = t₁) : F.map e.inv ≫ t₁ = t₂ := by
  rw [← h, ← Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.id_comp]

/-- The inverse of a natural isomorphism compatible at an object with maps to a fixed object is
compatible with them, in an arbitrary category. -/
theorem map_inv_app_trace_of_aux {E : Type*} [Category* E] (F : C ⥤ D) {G H : E ⥤ C} (e : G ≅ H)
    (A : E) {O : D} {t₁ : F.obj (G.obj A) ⟶ O} {t₂ : F.obj (H.obj A) ⟶ O}
    (h : F.map (e.hom.app A) ≫ t₂ = t₁) : F.map (e.inv.app A) ≫ t₁ = t₂ :=
  map_inv_trace_of_aux F (e.app A) h

/-- Eight morphisms compatible with maps to a fixed object compose, in an arbitrary category. -/
theorem map_comp₈_trace_of_aux (F : C ⥤ D) {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ : C} {O : D}
    {t₀ : F.obj A₀ ⟶ O} {t₁ : F.obj A₁ ⟶ O} {t₂ : F.obj A₂ ⟶ O} {t₃ : F.obj A₃ ⟶ O}
    {t₄ : F.obj A₄ ⟶ O} {t₅ : F.obj A₅ ⟶ O} {t₆ : F.obj A₆ ⟶ O} {t₇ : F.obj A₇ ⟶ O}
    {t₈ : F.obj A₈ ⟶ O} {m₁ : A₀ ⟶ A₁} {m₂ : A₁ ⟶ A₂} {m₃ : A₂ ⟶ A₃} {m₄ : A₃ ⟶ A₄}
    {m₅ : A₄ ⟶ A₅} {m₆ : A₅ ⟶ A₆} {m₇ : A₆ ⟶ A₇} {m₈ : A₇ ⟶ A₈}
    (h₁ : F.map m₁ ≫ t₁ = t₀) (h₂ : F.map m₂ ≫ t₂ = t₁) (h₃ : F.map m₃ ≫ t₃ = t₂)
    (h₄ : F.map m₄ ≫ t₄ = t₃) (h₅ : F.map m₅ ≫ t₅ = t₄) (h₆ : F.map m₆ ≫ t₆ = t₅)
    (h₇ : F.map m₇ ≫ t₇ = t₆) (h₈ : F.map m₈ ≫ t₈ = t₇) :
    F.map (m₁ ≫ m₂ ≫ m₃ ≫ m₄ ≫ m₅ ≫ m₆ ≫ m₇ ≫ m₈) ≫ t₈ = t₀ :=
  map_comp_trace_of_aux F h₁ (map_comp_trace_of_aux F h₂ (map_comp_trace_of_aux F h₃
    (map_comp_trace_of_aux F h₄ (map_comp_trace_of_aux F h₅ (map_comp_trace_of_aux F h₆
      (map_comp_trace_of_aux F h₇ h₈))))))

/-- An automorphism `a⁻¹ ∘ c⁻¹ ∘ x` with `x = c ∘ a` cancels, in an arbitrary category. -/
theorem comp_inv_comp_inv_comp_aux {P A O L : C} (m : P ⟶ O) (a : A ≅ O) (c : L ≅ A)
    (x : L ⟶ O) (h : c.hom ≫ a.hom = x) : m ≫ a.inv ≫ c.inv ≫ x = m := by
  rw [← h, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end Aux

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}
  {X' Y' : AlgebraicSpaces B S hS} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g)
  {X'' Y'' : AlgebraicSpaces B S hS} {f'' : X'' ⟶ Y''} {h : Y'' ⟶ Y'} {g'' : X'' ⟶ X'}
  (sq₂ : IsPullback g'' f'' f' h)

/-- **Base change of the base changed trace**: the trace of `((ω, τ)|_{X'})|_{X''}` is that of
`(ω, τ)|_{X''}` through `L(g'')^* L(g')^* ≅ L(g'' ≫ g')^*`, the identifications
`L(-)^* 𝒪 ≅ 𝒪` being compatible with composition. -/
theorem baseChange_baseChangeTrace_compIso
    (D : RelativeDualizingPair f hfl hfp) :
    (D.baseChange sq).baseChangeTrace sq₂ =
      (derivedModulePushforward B S hS f'').map
          ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').hom.app D.ω) ≫
        D.baseChangeTrace (sq₂.paste_horiz sq) :=
  (baseChange_baseChangeTrace sq sq₂ D).trans (whisker_eq _
    (comp_inv_comp_inv_comp_aux _ _
      ((smallEtaleDerivedModulePullbackCompIso B S hS h g).app
        (derivedStructureSheaf B S hS Y.1 Y.2).obj) _
      (smallEtaleDerivedModulePullbackCompIso_hom_app_unit_comp h g)))

/-- **The compositor of derived pullbacks is a morphism of pairs**: for a third cartesian square
`k' ≫ f = f'' ≫ k` with `k = h ≫ g` and `k' = g'' ≫ g'`, the isomorphism
`L(g'')^* L(g')^* ω ≅ L(k')^* ω` carries the trace of `((ω, τ)|_{X'})|_{X''}` to that of
`(ω, τ)|_{X''}`. -/
theorem map_compIso_comp_baseChangeTrace {k : Y'' ⟶ Y} {k' : X'' ⟶ X}
    (sq₃ : IsPullback k' f'' f k) (hk : h ≫ g = k) (hk' : g'' ≫ g' = k')
    (D : RelativeDualizingPair f hfl hfp) :
    (derivedModulePushforward B S hS f'').map
        ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g' ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS hk').hom.app D.ω) ≫
      D.baseChangeTrace sq₃ = (D.baseChange sq).baseChangeTrace sq₂ := by
  subst hk hk'
  rw [baseChange_baseChangeTrace_compIso sq sq₂ D]
  simp [smallEtaleDerivedModulePullbackCongr]

end AlgebraicGeometry.Space.RelativeDualizingPair

namespace AlgebraicGeometry.BigFppfSpaceSite

open AlgebraicGeometry.Space

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y)

/-- The projections `U_n = V_n ×_Y X ⟶ V_n` of a proper morphism are proper. -/
theorem isProper_cechOverPullbackFst (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (n : SimplexCategoryᵒᵖ) :
    Space.IsProper T.schemeSite S T.scheme_mem (cechOverPullbackFst b₀ f n).hom :=
  (isProper_isStableUnderBaseChange _ _ _).of_isPullback (isPullback_cechOverPullbackFst b₀ f n)
    hf

/-- The projections `U_n = V_n ×_Y X ⟶ V_n` of a flat morphism are flat. -/
theorem isFlat_cechOverPullbackFst (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (n : SimplexCategoryᵒᵖ) :
    Space.IsFlat T.schemeSite S T.scheme_mem (cechOverPullbackFst b₀ f n).hom :=
  (isFlat_isStableUnderBaseChange _ _ _).of_isPullback (isPullback_cechOverPullbackFst b₀ f n)
    hfl

/-- The projections `U_n = V_n ×_Y X ⟶ V_n` of a morphism of finite presentation are of finite
presentation. -/
theorem isFinitePresentation_cechOverPullbackFst
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom) (n : SimplexCategoryᵒᵖ) :
    Space.IsFinitePresentation T.schemeSite S T.scheme_mem (cechOverPullbackFst b₀ f n).hom :=
  (isFinitePresentation_isStableUnderBaseChange _ _ _).of_isPullback
    (isPullback_cechOverPullbackFst b₀ f n) hfp

/-- **The relative dualizing complex in degree zero.** If `V₀` is the disjoint union, in the
sheaves of sets on the big fppf site, of affine algebraic spaces `Y i`, then for `f : X ⟶ Y`
proper, flat and of finite presentation the projection `f_0 : V₀ ×_Y X ⟶ V₀` (read on the
degree-zero term of the Čech nerve of `b₀`) has a relative dualizing complex. -/
theorem nonempty_relativeDualizingComplex_cechOverPullbackFst_zero
    (hZ : T.schemeSite.Contains (⊤_ Scheme.{u})) {ι : Type u} {Yi : ι → T.Spaces}
    {j : ∀ i, Yi i ⟶ V₀}
    (hc : IsColimit (Cofan.mk ((algebraicSpacesToSheaf T.schemeSite S T.scheme_mem).obj V₀)
      fun i => (algebraicSpacesToSheaf T.schemeSite S T.scheme_mem).map (j i)))
    (hYi : ∀ i, IsAffineSpace T.schemeSite S T.scheme_mem (Yi i).1)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom) :
    Nonempty (RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _)) := by
  let A := algebraicSpacesToSheaf T.schemeSite S T.scheme_mem
  let e := cechOverObjZeroIso b₀
  have hc' : IsColimit (Cofan.mk (A.obj ((cechOver b₀).obj (op ⦋0⦌)).left)
      fun i => A.map (j i ≫ e.inv)) :=
    IsColimit.ofIsoColimit hc (Cofan.ext (A.mapIso e.symm) fun i =>
      (A.map_comp (j i) e.inv).symm)
  exact nonempty_relativeDualizingComplex_of_isColimit_cofan hZ hc' hYi _ _ _ _

/-- The simplicial structure maps of a simplicial object over `Z` compose on the left
components: `U(φ) ≫ U(ψ) = U(v)` for a factorization `ψ ≫ φ = v` of simplex maps. -/
private theorem simplicial_over_map_left_comp_of_eq {C : Type*} [Category* C] {Z : C}
    (U : SimplicialObject (Over Z)) {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) : (U.map φ.op).left ≫ (U.map ψ.op).left = (U.map v.op).left := by
  subst h
  rw [op_comp, Functor.map_comp, Over.comp_left]

/-- The simplicial structure maps of `n ↦ V_n ×_Y X` compose: `U(φ) ≫ U(ψ) = U(v)` for a
factorization `ψ ≫ φ = v` of simplex maps. -/
theorem cechOverPullback_map_left_comp_of_eq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) :
    ((cechOverPullback b₀ f).map φ.op).left ≫ ((cechOverPullback b₀ f).map ψ.op).left =
      ((cechOverPullback b₀ f).map v.op).left :=
  simplicial_over_map_left_comp_of_eq _ ψ φ v h

/-- The simplicial structure maps of the Čech nerve compose: `V(φ) ≫ V(ψ) = V(v)` for a
factorization `ψ ≫ φ = v` of simplex maps. -/
theorem cechOver_map_left_comp_of_eq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) :
    ((cechOver b₀).map φ.op).left ≫ ((cechOver b₀).map ψ.op).left =
      ((cechOver b₀).map v.op).left :=
  simplicial_over_map_left_comp_of_eq _ ψ φ v h

/-- **The compositor at a factorization of simplex maps is a morphism of pairs**: for
`ψ ≫ φ = v` the isomorphism `L U(φ)^* L U(ψ)^* ω ≅ L U(v)^* ω` carries the trace of the iterated
base change of `(ω, τ)` to that of its base change along `U(v)`. -/
theorem map_compIso_comp_baseChangeTrace_cechOverPullback {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (v : l ⟶ n) (h : ψ ≫ φ = v)
    {hfl : Space.IsFlat T.schemeSite S T.scheme_mem (cechOverPullbackFst b₀ f (op l)).hom}
    {hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem
      (cechOverPullbackFst b₀ f (op l)).hom}
    (D : RelativeDualizingPair (cechOverPullbackFst b₀ f (op l)) hfl hfp) :
    (derivedModulePushforward T.schemeSite S T.scheme_mem (cechOverPullbackFst b₀ f (op n))).map
        ((smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
            ((cechOverPullback b₀ f).map φ.op).left ((cechOverPullback b₀ f).map ψ.op).left ≪≫
          smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
            (cechOverPullback_map_left_comp_of_eq b₀ f ψ φ v h)).hom.app D.ω) ≫
      D.baseChangeTrace (isPullback_cechOverPullback_map b₀ f v.op) =
    (D.baseChange (isPullback_cechOverPullback_map b₀ f ψ.op)).baseChangeTrace
      (isPullback_cechOverPullback_map b₀ f φ.op) :=
  RelativeDualizingPair.map_compIso_comp_baseChangeTrace
    (isPullback_cechOverPullback_map b₀ f ψ.op) (isPullback_cechOverPullback_map b₀ f φ.op)
    (isPullback_cechOverPullback_map b₀ f v.op) (cechOver_map_left_comp_of_eq b₀ ψ φ v h)
    (cechOverPullback_map_left_comp_of_eq b₀ f ψ φ v h) D

/-- The inverse of the compositor at a factorization of simplex maps is a morphism of pairs. -/
theorem map_compIso_inv_comp_baseChangeTrace_cechOverPullback {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (v : l ⟶ n) (h : ψ ≫ φ = v)
    {hfl : Space.IsFlat T.schemeSite S T.scheme_mem (cechOverPullbackFst b₀ f (op l)).hom}
    {hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem
      (cechOverPullbackFst b₀ f (op l)).hom}
    (D : RelativeDualizingPair (cechOverPullbackFst b₀ f (op l)) hfl hfp) :
    (derivedModulePushforward T.schemeSite S T.scheme_mem (cechOverPullbackFst b₀ f (op n))).map
        ((smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
            ((cechOverPullback b₀ f).map φ.op).left ((cechOverPullback b₀ f).map ψ.op).left ≪≫
          smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
            (cechOverPullback_map_left_comp_of_eq b₀ f ψ φ v h)).inv.app D.ω) ≫
      (D.baseChange (isPullback_cechOverPullback_map b₀ f ψ.op)).baseChangeTrace
        (isPullback_cechOverPullback_map b₀ f φ.op) =
    D.baseChangeTrace (isPullback_cechOverPullback_map b₀ f v.op) :=
  RelativeDualizingPair.map_inv_app_trace_of_aux _ _ _
    (map_compIso_comp_baseChangeTrace_cechOverPullback b₀ f ψ φ v h D)

/-- **The cocycle condition.** For an isomorphism `α` of pairs between
the two base changes of `D₀` along the faces `U_1 ⇉ U_0`, the cocycle condition on `U_2` holds:
both sides are morphisms of pairs between base changes of `D₀`, which are unique (Stacks 0E5Z). -/
theorem cocycle_cechOverPullback (hZ : T.schemeSite.Contains (⊤_ Scheme.{u}))
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _))
    (α : (smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left).obj D₀.ω ≅
        (smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left).obj D₀.ω)
    (hα : (derivedModulePushforward T.schemeSite S T.scheme_mem
        (cechOverPullbackFst b₀ f (op ⦋1⦌))).map
          α.hom ≫
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (0 : Fin 2)).op)).τ =
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (1 : Fin 2)).op)).τ) :
      (smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 3)).op).left).map α.hom =
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_one_comp_delta_one)).hom.app D₀.ω ≫
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (2 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_one_comp_delta_two)).inv.app D₀.ω ≫
      (smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (2 : Fin 3)).op).left).map α.hom ≫
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (2 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_zero_comp_delta_two)).hom.app D₀.ω ≫
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_one_comp_delta_zero)).inv.app D₀.ω ≫
      (smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 3)).op).left).map α.hom ≫
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_zero_comp_delta_zero)).hom.app D₀.ω ≫
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_zero_comp_delta_one)).inv.app D₀.ω := by
  have hA : ∀ j : Fin 3, (derivedModulePushforward T.schemeSite S T.scheme_mem
      (cechOverPullbackFst b₀ f (op ⦋1 + 1⦌))).map
      ((smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
        ((cechOverPullback b₀ f).map (SimplexCategory.δ j).op).left).map α.hom) ≫
        (D₀.toRelativeDualizingPair.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (0 : Fin 2)).op)).baseChangeTrace
          (isPullback_cechOverPullback_map b₀ f (SimplexCategory.δ j).op) =
      (D₀.toRelativeDualizingPair.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (1 : Fin 2)).op)).baseChangeTrace
          (isPullback_cechOverPullback_map b₀ f (SimplexCategory.δ j).op) :=
    fun j => RelativeDualizingPair.baseChange_hom
      (D₀.toRelativeDualizingPair.baseChange (isPullback_cechOverPullback_map b₀ f
        (SimplexCategory.δ (1 : Fin 2)).op))
      (D₀.toRelativeDualizingPair.baseChange (isPullback_cechOverPullback_map b₀ f
        (SimplexCategory.δ (0 : Fin 2)).op))
      (isPullback_cechOverPullback_map b₀ f (SimplexCategory.δ j).op) α.hom hα
  have hchain := RelativeDualizingPair.map_comp₈_trace_of_aux
    (derivedModulePushforward T.schemeSite S T.scheme_mem (cechOverPullbackFst b₀ f (op ⦋1 + 1⦌)))
    (map_compIso_comp_baseChangeTrace_cechOverPullback b₀ f _ _ _
      SimplexCategory.delta_one_comp_delta_one D₀.toRelativeDualizingPair)
    (map_compIso_inv_comp_baseChangeTrace_cechOverPullback b₀ f _ _ _
      SimplexCategory.delta_one_comp_delta_two D₀.toRelativeDualizingPair)
    (hA 2)
    (map_compIso_comp_baseChangeTrace_cechOverPullback b₀ f _ _ _
      SimplexCategory.delta_zero_comp_delta_two D₀.toRelativeDualizingPair)
    (map_compIso_inv_comp_baseChangeTrace_cechOverPullback b₀ f _ _ _
      SimplexCategory.delta_one_comp_delta_zero D₀.toRelativeDualizingPair)
    (hA 0)
    (map_compIso_comp_baseChangeTrace_cechOverPullback b₀ f _ _ _
      SimplexCategory.delta_zero_comp_delta_zero D₀.toRelativeDualizingPair)
    (map_compIso_inv_comp_baseChangeTrace_cechOverPullback b₀ f _ _ _
      SimplexCategory.delta_zero_comp_delta_one D₀.toRelativeDualizingPair)
  refine RelativeDualizingComplex.eq_of_hom
    ((D₀.baseChange (isPullback_cechOverPullback_map b₀ f (SimplexCategory.δ (1 : Fin 2)).op)
      ).baseChange (isPullback_cechOverPullback_map b₀ f (SimplexCategory.δ (1 : Fin 3)).op))
    ((D₀.baseChange (isPullback_cechOverPullback_map b₀ f (SimplexCategory.δ (0 : Fin 2)).op)
      ).baseChange (isPullback_cechOverPullback_map b₀ f (SimplexCategory.δ (1 : Fin 3)).op))
    (RelativeDualizingComplex.isGE_smallEtaleDerivedSheafHom _ _
      (RelativeDualizingComplex.isIso_smallEtaleDerivedHomothety_and_isLE _).1) _ _ (hA 1) ?_
  exact eq_of_heq (HEq.trans (by heq_congr) (heq_of_eq hchain))

/-- **The descent isomorphism and its cocycle condition** (the proof of
Stacks 0E61 on a Čech hypercovering). Let `D₀` be a relative dualizing complex on
`f_0 : U_0 ⟶ V_0`. Its two base changes along the faces `U_1 ⇉ U_0` are relative dualizing
complexes on `f_1`, so there is an isomorphism `α` of pairs between them (Stacks 0E5Z); and the
cocycle condition on `U_2` holds, both sides being morphisms of pairs between base changes of `D₀`,
which are unique. -/
theorem exists_iso_cocycle_cechOverPullback (hZ : T.schemeSite.Contains (⊤_ Scheme.{u}))
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _)) :
    ∃ α : (smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left).obj D₀.ω ≅
        (smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left).obj D₀.ω,
      (derivedModulePushforward T.schemeSite S T.scheme_mem (cechOverPullbackFst b₀ f (op ⦋1⦌))).map
          α.hom ≫
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (0 : Fin 2)).op)).τ =
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (1 : Fin 2)).op)).τ ∧
      (smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 3)).op).left).map α.hom =
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_one_comp_delta_one)).hom.app D₀.ω ≫
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (2 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_one_comp_delta_two)).inv.app D₀.ω ≫
      (smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (2 : Fin 3)).op).left).map α.hom ≫
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (2 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_zero_comp_delta_two)).hom.app D₀.ω ≫
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_one_comp_delta_zero)).inv.app D₀.ω ≫
      (smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 3)).op).left).map α.hom ≫
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_zero_comp_delta_zero)).hom.app D₀.ω ≫
      (smallEtaleDerivedModulePullbackCompIso T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 3)).op).left
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left ≪≫
        smallEtaleDerivedModulePullbackCongr T.schemeSite S T.scheme_mem
          (cechOverPullback_map_left_comp_of_eq b₀ f _ _ _
            SimplexCategory.delta_zero_comp_delta_one)).inv.app D₀.ω := by
  obtain ⟨α, hα, -⟩ := RelativeDualizingComplex.existsUnique_iso_of_relativeDualizingComplex
    (D₀.baseChange (isPullback_cechOverPullback_map b₀ f (SimplexCategory.δ (1 : Fin 2)).op))
    (D₀.baseChange (isPullback_cechOverPullback_map b₀ f (SimplexCategory.δ (0 : Fin 2)).op))
  exact ⟨α, hα, cocycle_cechOverPullback b₀ f hZ hf hfl hfp D₀ α hα⟩

end AlgebraicGeometry.BigFppfSpaceSite

end
