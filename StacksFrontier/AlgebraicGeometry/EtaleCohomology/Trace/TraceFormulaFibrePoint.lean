module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaCompactificationChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaFibreGeometry
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleBaseChange

/-!
# The stalk of a proper direct image at a rational point

Let `ḡ : W ⟶ P` be a proper morphism of schemes over a finite field `k`, `J` a bounded below
complex of injective sheaves of `Λ`-modules on `W` (`Λ` finite) and `y ∈ P(k)` a rational point
with fibre `W_y = W ×_P Spec k`. Then the trace of the geometric Frobenius `π_y` on the stalk of
`ḡ_* J` at `y` is the trace of the canonical Frobenius on `RΓ(W_{y,k̄}, J|_{W_y})`:

`Tr(π_y | (Rḡ_* J)_ȳ) = Tr(π^* | RΓ(W_{y,k̄}, J|))`.

The proof is proper base change along `y` (the stalk complex of `y^{-1} ḡ_* J` on `Spec k` is
`R(ḡ_y)_* (J|_{W_y})`), the trace formula for the point `Spec k`
(`Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_sum_of_etale'`),
and the invariance of the canonical trace under the proper direct image `W_y ⟶ Spec k`. It is the
local half of the fibration step of the trace formula in any dimension, [Stacks, Tag 03UI] (1).

## Main results

* `Stacks.EtaleCohomology.stalkTrace_directImage_eq_fibre`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.FilteredDerived Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize etaleModules_ab5OfSize

/-- The stalk functor at a geometric point `s`, on sheaves of `Λ`-modules on `X_étale`. -/
abbrev geometricStalkFunctor (Λ : Type r) [Ring Λ] {X : Scheme.{u}} (s : GeometricPoint X) :
    EtaleModules.{u, r} Λ X ⥤ ModuleCat.{max (u + 1) r} Λ :=
  (Scheme.pointSmallEtale s.hom).sheafFiber

/-- The stalk at a geometric point `s` of a complex of sheaves of `Λ`-modules on `X_étale`. -/
abbrev geometricStalkComplex (Λ : Type r) [Ring Λ] {X : Scheme.{u}} (s : GeometricPoint X)
    (C : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ :=
  ((geometricStalkFunctor Λ s).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- The point `Spec k` as a scheme over `k`. -/
abbrev pointOver (k : Type u) [Field k] : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))

/-- The point `Spec k` has exactly one `k`-rational point, the identity. -/
instance (k : Type u) [Field k] : Unique (rationalPoints (pointOver k).hom) where
  default := ⟨𝟙 _, by simp⟩
  uniq x := Subtype.ext (by simpa using x.2)

/-- The fibre `W_y = W ×_P Spec k` of `ḡ : W ⟶ P` over a rational point `y`, over `k`. -/
abbrev fibreOver {W P : Over (Spec (.of k))} (gb : W ⟶ P) (y : Spec (.of k) ⟶ P.left) :
    Over (Spec (.of k)) :=
  Over.mk (pullback.snd gb.left y)

/-- The fibre maps to the point, over `k`. -/
abbrev fibreToPoint {W P : Over (Spec (.of k))} (gb : W ⟶ P) (y : Spec (.of k) ⟶ P.left) :
    fibreOver gb y ⟶ pointOver k :=
  Over.homMk (pullback.snd gb.left y) (Category.comp_id _)

omit [Finite Λ] [CharP k p] in
/-- The stalk trace at a rational point only depends on the point. -/
theorem stalkTrace_congr_point {X : Scheme.{u}} {x₁ x₂ : Spec (.of k) ⟶ X} (h : x₁ = x₂)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (h₁ : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar x₁ K)))
    (h₂ : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, 0} Λ kbar x₂ K))) :
    perfectDerivedTrace Λ ⟨_, h₁⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x₁ K)) =
      perfectDerivedTrace Λ ⟨_, h₂⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x₂ K)) := by
  subst h
  rfl

omit [Finite Λ] in
/-- The stalk trace of `C` at a rational point `y` is the canonical trace on
`RΓ(Spec k̄, y^{-1} C)`. -/
theorem stalkTrace_eq_frobeniusRestrictionCohomologyEndo_point {X : Scheme.{u}}
    (y : Spec (.of k) ⟶ X) (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hstalk : ∀ s : GeometricPoint (Spec (.of k)), StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (geometricStalkComplex.{u, 0} Λ s
        ((etaleModuleInverseImage.{u, 0} Λ y).mapCochainComplexPlus.obj C).obj)))
    (hC₀ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ
            (pullback.snd (pointOver k).hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ (pointOver k) kbar
            ((etaleModuleInverseImage.{u, 0} Λ y).mapCochainComplexPlus.obj C)))))) :
    ∃ hs : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
        (rationalPointStalkComplex.{u, 0} Λ kbar y C)),
      perfectDerivedTrace Λ ⟨_, hs⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y C)) =
        perfectDerivedTrace Λ ⟨_, hC₀⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ (pointOver k) kbar p q hcard
            ((etaleModuleInverseImage.{u, 0} Λ y).mapCochainComplexPlus.obj C))) := by
  have : Etale (pointOver k).hom := inferInstanceAs (Etale (𝟙 (Spec (.of k))))
  have : IsFinite (pointOver k).hom := inferInstanceAs (IsFinite (𝟙 (Spec (.of k))))
  have h0 := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_sum_of_etale' Λ (pointOver k)
    kbar p q hcard _ hC₀ hstalk
  rw [Fintype.sum_unique] at h0
  have hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (rationalPointStalkComplex.{u, 0} Λ kbar (𝟙 _ ≫ y) C)) :=
    isPerfect_stalk_of_inverseImage Λ kbar y (𝟙 _) C
      (hstalk (rationalGeometricPoint kbar (𝟙 _)))
  obtain ⟨_, htrX⟩ := stalkTrace_inverseImage Λ kbar p q hcard y (𝟙 _) C hX
  have hs : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (rationalPointStalkComplex.{u, 0} Λ kbar y C)) := (Category.id_comp y) ▸ hX
  refine ⟨hs, ?_⟩
  rw [← stalkTrace_congr_point Λ kbar p q hcard (Category.id_comp y) C hX hs, ← htrX]
  exact h0.symm

/-- **The stalk of a proper direct image at a rational point.** For a proper morphism
`ḡ : W ⟶ P` over `k`, a bounded below complex `J` of injectives on `W` and a rational point
`y : Spec k ⟶ P` such that the geometric stalks of `y^{-1} ḡ_* J` are perfect, if
`RΓ(W_{y,k̄}, J|_{W_y})` is perfect then so is the stalk `(ḡ_* J)_ȳ`, and
`Tr(π_y | (ḡ_* J)_ȳ) = Tr(π^* | RΓ(W_{y,k̄}, J|_{W_y}))`. -/
theorem stalkTrace_directImage_eq_fibre {W P : Over (Spec (.of k))} (gb : W ⟶ P)
    [IsProper gb.left] (J : CochainComplex.Plus (EtaleModules.{u, 0} Λ W.left))
    (hJ : ∀ n, Injective (J.obj.X n)) (y : Spec (.of k) ⟶ P.left)
    (hstalk : ∀ s : GeometricPoint (Spec (.of k)), StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (geometricStalkComplex.{u, 0} Λ s
          ((etaleModuleInverseImage.{u, 0} Λ y).mapCochainComplexPlus.obj
            ((etaleModuleDirectImage.{u, 0} Λ gb.left).mapCochainComplexPlus.obj J)).obj)))
    (hW : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ
            (pullback.snd (fibreOver gb y).hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ (fibreOver gb y) kbar
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst gb.left y)).mapCochainComplexPlus.obj
              J)))))) :
    ∃ hs : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
        (rationalPointStalkComplex.{u, 0} Λ kbar y
          ((etaleModuleDirectImage.{u, 0} Λ gb.left).mapCochainComplexPlus.obj J))),
      perfectDerivedTrace Λ ⟨_, hs⟩ (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ
          kbar p q hcard y
          ((etaleModuleDirectImage.{u, 0} Λ gb.left).mapCochainComplexPlus.obj J))) =
        perfectDerivedTrace Λ ⟨_, hW⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ (fibreOver gb y) kbar p q hcard
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst gb.left y)).mapCochainComplexPlus.obj
              J))) := by
  let C := (etaleModuleDirectImage.{u, 0} Λ gb.left).mapCochainComplexPlus.obj J
  -- proper base change along `y`
  obtain ⟨a, _⟩ := J.property
  have hq := baseChangeQuasiIsoAt_of_isIso_etaleModuleDerivedBaseChange Λ gb.left y
    (pullback.fst gb.left y) (pullback.snd gb.left y) pullback.condition.symm J hJ
    (isIso_etaleModuleDerivedBaseChange_of_isProper_of_finite Λ gb.left
      (IsPullback.of_hasPullback gb.left y) (DerivedCategory.Q.obj J.obj) a)
  have : EnoughInjectives (EtaleModules.{u, 0} Λ (fibreOver gb y).left) :=
    etaleModules_enoughInjectives.{u, 0} Λ _
  obtain ⟨T, ψ, hψ, hTi, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution
    (𝟭 (EtaleModules.{u, 0} Λ (fibreOver gb y).left))
    ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst gb.left y)).mapCochainComplexPlus.obj J) (𝟙 _)
  let φ := Functor.baseChangeComp
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd gb.left y))
    (etaleModuleDirectImage.{u, 0} Λ gb.left) (etaleModuleInverseImage.{u, 0} Λ y)
    (etaleModuleInverseImage.{u, 0} Λ (pullback.fst gb.left y))
    (etaleModuleBaseChange Λ gb.left (pullback.snd gb.left y) y (pullback.fst gb.left y)
      pullback.condition.symm) J ψ
  have : EnoughInjectives (EtaleModules.{u, 0} Λ (pullback gb.left y)) :=
    etaleModules_enoughInjectives.{u, 0} Λ _
  have : EnoughInjectives (EtaleModules.{u, 0} Λ (Spec (.of k))) :=
    etaleModules_enoughInjectives.{u, 0} Λ _
  have hφ : QuasiIso φ.hom := Functor.BaseChangeQuasiIsoAt.quasiIso_baseChangeComp
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd gb.left y))
    (etaleModuleDirectImage.{u, 0} Λ gb.left) (etaleModuleInverseImage.{u, 0} Λ y)
    (etaleModuleInverseImage.{u, 0} Λ (pullback.fst gb.left y))
    (etaleModuleBaseChange Λ gb.left (pullback.snd gb.left y) y (pullback.fst gb.left y)
      pullback.condition.symm) hq ψ hψ hTi
  -- the proper direct image `W_y ⟶ Spec k`
  have : IsProper (fibreToPoint gb y).left := inferInstanceAs (IsProper (pullback.snd gb.left y))
  obtain ⟨hiffD, htrD⟩ :=
    perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper_of_torsion
      Λ (fun _ E => torsionCohomologyProperty_etaleModuleForgetDerived_of_finite Λ E)
      (fibreToPoint gb y) kbar p q hcard T hTi
  have hTperf := (isPerfect_frobeniusRestriction_iff_of_quasiIso Λ (fibreOver gb y) kbar ψ).1 hW
  have hP := hiffD.2 hTperf
  have hC₀ := (isPerfect_frobeniusRestriction_iff_of_quasiIso Λ (pointOver k) kbar φ).2 hP
  obtain ⟨hs, hpt⟩ := stalkTrace_eq_frobeniusRestrictionCohomologyEndo_point Λ kbar p q hcard y C
    hstalk hC₀
  exact ⟨hs, hpt.trans <|
    (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso_of_isPerfect Λ
      (pointOver k) kbar p q hcard φ hC₀ hP).trans <| (htrD hP hTperf).trans
    (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso_of_isPerfect Λ
      (fibreOver gb y) kbar p q hcard ψ hW hTperf).symm⟩

section FibreCompactSupport

variable {U : Scheme.{u}} {W P : Over (Spec (.of k))} (j' : U ⟶ W.left) [IsOpenImmersion j']
  (gb : W ⟶ P) [IsProper gb.left] (y : Spec (.of k) ⟶ P.left)

/-- `(W_y ⟶ W)^{-1} j'_! K ≅ (j'_y)_! (K|_{U_y})`, degreewise (Tag 03S6). -/
def fibreExtensionByZeroIso (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)) :
    (etaleModuleExtensionByZero.{u, 0} Λ
          (pullback.snd j' (pullback.fst gb.left y))).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst j' (pullback.fst gb.left y))).mapCochainComplexPlus.obj K) ≅
      (etaleModuleInverseImage.{u, 0} Λ (pullback.fst gb.left y)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j').mapCochainComplexPlus.obj K) :=
  (CochainComplex.Plus.fullyFaithfulι _).preimageIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun n => (etaleModuleExtensionByZeroBaseChangeIso.{u, 0} Λ j' (pullback.fst gb.left y)).app
        (K.obj.X n))
      (fun a b _ => ((etaleModuleExtensionByZeroBaseChangeIso.{u, 0} Λ j'
        (pullback.fst gb.left y)).hom.naturality (K.obj.d a b)).symm))

omit [IsAlgClosed kbar] [CharP kbar p] in
/-- **The fibre trace is `RΓ_c` of the fibre `U_y`.** For a quasi-isomorphism `j'_! K ⟶ J`, the
canonical trace on `RΓ(W_{y,k̄}, J|_{W_y})` is that of `RΓ_c(U_{y,k̄}, K|_{U_y})` through the
compactification `U_y ⟶ W_y`, and the two are perfect together. -/
theorem canonicalCompactSupportLefschetzNumber_fibre_eq
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U))
    (J : CochainComplex.Plus (EtaleModules.{u, 0} Λ W.left))
    (ψ : (etaleModuleExtensionByZero.{u, 0} Λ j').mapCochainComplexPlus.obj K ⟶ J)
    [QuasiIso ψ.hom] :
    (StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ (fibreStructure j' gb.left y)
          (fibreCompactification j' gb.left y) kbar
          ((etaleModuleInverseImage.{u, 0} Λ
            (pullback.fst j' (pullback.fst gb.left y))).mapCochainComplexPlus.obj K))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
          ((etaleModuleDerivedDirectImage.{u, 0} Λ
              (pullback.snd (fibreOver gb y).hom (specAlgebraMap k kbar))).obj
            (fieldBaseChangeRestriction.{u, 0} Λ (fibreOver gb y) kbar
              ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst gb.left y)).mapCochainComplexPlus.obj
                J)))))) ∧
      ∀ h₁ h₂, canonicalCompactSupportLefschetzNumber.{u, 0} Λ (fibreStructure j' gb.left y)
          (fibreCompactification j' gb.left y) kbar p q hcard
          ((etaleModuleInverseImage.{u, 0} Λ
            (pullback.fst j' (pullback.fst gb.left y))).mapCochainComplexPlus.obj K) h₁ =
        perfectDerivedTrace Λ ⟨_, h₂⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ (fibreOver gb y) kbar p q hcard
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst gb.left y)).mapCochainComplexPlus.obj
              J))) := by
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ (pullback.fst gb.left y)
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} Λ (pullback.fst gb.left y)
  let φ := (etaleModuleInverseImage.{u, 0} Λ (pullback.fst gb.left y)).mapCochainComplexPlus.map ψ
  have : QuasiIso φ.hom := inferInstanceAs (QuasiIso (((etaleModuleInverseImage.{u, 0} Λ
    (pullback.fst gb.left y)).mapHomologicalComplex _).map ψ.hom))
  let e := fibreExtensionByZeroIso Λ j' gb y K
  have hiffφ := isPerfect_frobeniusRestriction_iff_of_quasiIso Λ (fibreOver gb y) kbar φ
  refine ⟨⟨fun h => hiffφ.1 (isPerfect_frobeniusRestriction_of_iso Λ (fibreOver gb y) kbar e h),
    fun h => isPerfect_frobeniusRestriction_of_iso Λ (fibreOver gb y) kbar e.symm (hiffφ.2 h)⟩,
    fun h₁ h₂ => ?_⟩
  have h₃ := isPerfect_frobeniusRestriction_of_iso Λ (fibreOver gb y) kbar e h₁
  exact (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso Λ (fibreOver gb y)
    kbar p q hcard e h₁ h₃).trans
    (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso_of_isPerfect Λ
      (fibreOver gb y) kbar p q hcard φ h₃ h₂)

end FibreCompactSupport

end Stacks.EtaleCohomology

end
