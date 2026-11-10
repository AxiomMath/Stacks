module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksFrontier.Algebra.Homology.RightDerivedOfBoundedFunctorResolution
public import StacksFrontier.Algebra.Homology.RightDerivedOfFunctorResolution
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.KoszulResolution
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# The Koszul resolution of the global sections of sheaves of modules

Let `R` be a sheaf of rings on a site `C`, and let `U` be an object of `C` covering the final
object, in the sense that every object of `C` is covered by objects admitting a morphism to
`U`.  The trace `ℤ[h_U] ⟶ ℤ` of the free abelian presheaf on the representable presheaf of `U`
has a Koszul complex `Q_p = ∧^{p+1} ℤ[h_U]`, objectwise exact in positive degrees, whose
augmentation `Q_0 ⟶ ℤ` is locally surjective.  Applying `Hom(-, M)` for sheaves of `R`-modules
`M` gives a cochain complex of functors `Φ_p(M) = Hom(Q_p, M)`, augmented by the global
sections `Γ(M) = Hom(ℤ, M)`.

This augmented complex is a resolution of `Γ` on injective `R`-modules: for an injective `I`
the complex `Φ(I)` is exact in positive degrees.  The reason is that the terms of the Koszul
complex, and the image of its augmentation in `ℤ`, are objectwise torsion free, so that after
extension of scalars to `R` the Koszul complex stays exact, and maps from it to the underlying
abelian presheaf of an injective module extend along it.  Consequently the right derived
functors of `Γ` are computed by the `Φ_p` on objects acyclic for all of them
(`Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_of_isZero_X`).  For `C` the étale
site of an algebraic space and `U` an étale covering by a scheme, `Φ_p(M)` is the module of
alternating Čech cochains of the covering in degree `p` [Stacks, Tag 0726], and this is the
mechanism of the alternating Čech complex of [Stacks, Tag 0728].

## Main definitions

* `AddCommGrpCat.freeYonedaTrace`: the trace `ℤ[h_U] ⟶ ℤ`, the sum of the coefficients.
* `Stacks.SheafOfModules.koszulSections`: the cochain complex of functors `M ↦ Hom(Q_p, M)`.
* `Stacks.SheafOfModules.globalSectionsHom`: global sections, as `M ↦ Hom(ℤ, M)`.
* `Stacks.SheafOfModules.koszulSectionsAugmentation`: the augmentation `Γ ⟶ Φ_0`.

## Main results

* `Stacks.SheafOfModules.exists_comp_eq_of_isTorsionFree`: maps to the underlying abelian
  presheaf of an injective module extend along monomorphisms with objectwise torsion-free
  cokernel.
* `Stacks.SheafOfModules.koszulSections_exactAt_of_injective`: for an injective module `I`,
  `Φ(I)` is exact in positive degrees.
* `Stacks.SheafOfModules.exact_koszulSectionsAugmentation`: `Γ(M)` is the kernel of
  `Φ_0(M) ⟶ Φ_1(M)` for every module `M`.
* `Stacks.SheafOfModules.isZero_rightDerived_globalSectionsHom`: if `M` is acyclic for every
  `Φ_p` and `Φ_p(M) = 0` for `p ≥ d`, then `Rⁿ Γ(M) = 0` for `n ≥ d`.

## References

* [Stacks Project, Tag 0723](https://stacks.math.columbia.edu/tag/0723)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite

universe w u

/-! ### The trace of the free abelian presheaf on a representable presheaf -/

namespace AddCommGrpCat

variable {C : Type w} [Category.{u} C]

/-- The trace of the free abelian presheaf on the representable presheaf of `U`: the sum of the
coefficients of a formal integral combination of morphisms into `U`. -/
def freeYonedaTrace (U : C) : yoneda.obj U ⋙ AddCommGrpCat.free ⟶ constantInt.{u} C where
  app V := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun _ => (ULift.up 1 : ULift.{u} ℤ))
  naturality {V W} f := by
    ext x
    change FreeAbelianGroup.lift (fun _ => (ULift.up 1 : ULift.{u} ℤ))
        (FreeAbelianGroup.map (fun g => f.unop ≫ g) x) =
      FreeAbelianGroup.lift (fun _ => (ULift.up 1 : ULift.{u} ℤ)) x
    induction x using FreeAbelianGroup.induction_on with
    | zero => simp
    | of a => simp
    | neg y hy => simp
    | add y z hy hz => simpa using congrArg₂ (· + ·) hy hz

/-- The trace of `ℤ[h_U]` takes the value `1` on the generator given by a morphism `V ⟶ U`. -/
@[simp]
theorem presheafDual_freeYonedaTrace_of (U : C) (V : Cᵒᵖ) (φ : V.unop ⟶ U) :
    presheafDual (freeYonedaTrace U) V (FreeAbelianGroup.of φ) = 1 := by
  change (ULift.moduleEquiv (R := ℤ) (M := ℤ))
      (FreeAbelianGroup.lift (fun _ => (ULift.up 1 : ULift.{u} ℤ)) (FreeAbelianGroup.of φ)) = 1
  rw [FreeAbelianGroup.lift_apply_of]
  rfl

/-- Over every object the Koszul complex of the trace of `ℤ[h_U]` is exact in positive
degrees: either the object admits a morphism to `U`, and the trace takes the value `1`, or it
does not, and the free abelian presheaf has no nonzero section. -/
theorem presheafKoszulDiff_freeYonedaTrace_exact_app (U : C) (V : Cᵒᵖ) (n : ℕ) :
    Function.Exact ((presheafKoszulDiff (freeYonedaTrace U) (n + 1)).app V)
      ((presheafKoszulDiff (freeYonedaTrace U) n).app V) := by
  rcases isEmpty_or_nonempty (V.unop ⟶ U) with h | h
  · exact presheafKoszulDiff_exact_app_of_subsingleton _ V
      (inferInstanceAs (Subsingleton (FreeAbelianGroup (V.unop ⟶ U)))) n
  · obtain ⟨φ⟩ := h
    exact presheafKoszulDiff_exact_app_of_apply_eq_one _ V
      (presheafDual_freeYonedaTrace_of U V φ) n

/-- Over every object the augmented Koszul complex of the trace of `ℤ[h_U]` is exact at the
first exterior power. -/
theorem presheafKoszulAugmentation_freeYonedaTrace_exact_app (U : C) (V : Cᵒᵖ) :
    Function.Exact ((presheafKoszulDiff (freeYonedaTrace U) 1).app V)
      ((presheafKoszulAugmentation (freeYonedaTrace U)).app V) := by
  rcases isEmpty_or_nonempty (V.unop ⟶ U) with h | h
  · exact presheafKoszulAugmentation_exact_app_of_subsingleton _ V
      (inferInstanceAs (Subsingleton (FreeAbelianGroup (V.unop ⟶ U))))
  · obtain ⟨φ⟩ := h
    exact presheafKoszulAugmentation_exact_app_of_apply_eq_one _ V
      (presheafDual_freeYonedaTrace_of U V φ)

/-- The Koszul complex of the trace of `ℤ[h_U]` is exact in positive degrees. -/
theorem presheafKoszul_freeYonedaTrace_exact (U : C) (n : ℕ) :
    (ShortComplex.mk (presheafKoszulDiff (freeYonedaTrace U) (n + 1))
      (presheafKoszulDiff (freeYonedaTrace U) n)
      (presheafKoszulDiff_comp (freeYonedaTrace U) n)).Exact :=
  shortComplex_exact_of_evaluation _ fun V =>
    (ShortComplex.ab_exact_iff_function_exact _).2
      (presheafKoszulDiff_freeYonedaTrace_exact_app U V n)

/-- The first Koszul differential and the augmentation form an exact sequence. -/
theorem presheafKoszulAugmentation_freeYonedaTrace_exact (U : C) :
    (ShortComplex.mk (presheafKoszulDiff (freeYonedaTrace U) 1)
      (presheafKoszulAugmentation (freeYonedaTrace U))
      (presheafKoszulDiff_comp_presheafKoszulAugmentation (freeYonedaTrace U))).Exact :=
  shortComplex_exact_of_evaluation _ fun V =>
    (ShortComplex.ab_exact_iff_function_exact _).2
      (presheafKoszulAugmentation_freeYonedaTrace_exact_app U V)

/-- The exterior powers of the free abelian presheaf on a representable presheaf are objectwise
torsion free. -/
instance isTorsionFree_presheafExteriorPower_freeYoneda (U : C) (n : ℕ) (V : Cᵒᵖ) :
    Module.IsTorsionFree ℤ
      ((presheafExteriorPower (yoneda.obj U ⋙ AddCommGrpCat.free) n).obj V) := by
  change Module.IsTorsionFree ℤ (⋀[ℤ]^n (FreeAbelianGroup (V.unop ⟶ U)))
  infer_instance

end AddCommGrpCat

namespace Stacks.SheafOfModules

open AddCommGrpCat

variable {C : Type w} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-! ### Extension along monomorphisms with torsion-free cokernel -/

/-- The underlying presheaf of abelian groups of a sheaf of modules. -/
abbrev toPresheaf : SheafOfModules.{u} R ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{u}

/-- **Maps into the underlying abelian presheaf of an injective module extend along
monomorphisms with objectwise torsion-free cokernel.**  Extension of scalars to `R` keeps such a
monomorphism a monomorphism, and the underlying presheaf of modules of an injective sheaf of
modules is injective. -/
theorem exists_comp_eq_of_isTorsionFree [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : SheafOfModules.{u} R) [Injective I] (S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hS : S.Exact) [Mono S.f] (hQ : ∀ V, Module.IsTorsionFree ℤ (S.X₃.obj V))
    (α : S.X₁ ⟶ (PresheafOfModules.toPresheaf R.obj).obj ((SheafOfModules.forget R).obj I)) :
    ∃ β : S.X₂ ⟶ (PresheafOfModules.toPresheaf R.obj).obj ((SheafOfModules.forget R).obj I),
      S.f ≫ β = α := by
  have : Injective ((SheafOfModules.forget R).obj I) :=
    ModuleSheafCohomology.injective_forget_obj R I
  have hmono : Mono (ModuleSheafCohomology.tensorPresheafMap R.obj S.f) := by
    apply PresheafOfModules.mono_of_injective
    intro V
    have := hQ V
    let E := (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj V
    exact ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree
      (S.f.app V).hom.toIntLinearMap (S.g.app V).hom.toIntLinearMap
      ((AddCommGrpCat.mono_iff_injective _).mp (inferInstanceAs (Mono (E.map S.f))))
      ((ShortComplex.ab_exact_iff_function_exact (S.map E)).mp (hS.map E)) (R.obj.obj V)
  let g := Injective.factorThru (ModuleSheafCohomology.tensorPresheafLift R.obj α)
    (ModuleSheafCohomology.tensorPresheafMap R.obj S.f)
  refine ⟨ModuleSheafCohomology.tensorPresheafUnit R.obj S.X₂ ≫
    (PresheafOfModules.toPresheaf R.obj).map g, ?_⟩
  have h := ModuleSheafCohomology.tensorPresheafUnit_naturality R.obj S.f
  have h2 := ModuleSheafCohomology.tensorPresheafUnit_comp_lift R.obj α
  have h3 : ModuleSheafCohomology.tensorPresheafMap R.obj S.f ≫ g =
      ModuleSheafCohomology.tensorPresheafLift R.obj α :=
    Injective.comp_factorThru _ _
  calc S.f ≫ ModuleSheafCohomology.tensorPresheafUnit R.obj S.X₂ ≫
        (PresheafOfModules.toPresheaf R.obj).map g
      = (S.f ≫ ModuleSheafCohomology.tensorPresheafUnit R.obj S.X₂) ≫
        (PresheafOfModules.toPresheaf R.obj).map g := (assoc _ _ _).symm
    _ = ModuleSheafCohomology.tensorPresheafUnit R.obj S.X₁ ≫
        (PresheafOfModules.toPresheaf R.obj).map
          (ModuleSheafCohomology.tensorPresheafMap R.obj S.f ≫ g) := by
        rw [h]
        exact (assoc _ _ _).trans
          (congrArg (fun k => ModuleSheafCohomology.tensorPresheafUnit R.obj S.X₁ ≫ k)
            (Functor.map_comp _ _ _).symm)
    _ = α := by rw [h3, h2]

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

open AddCommGrpCat

variable {C : Type w} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  (U : C)

/-! ### The Koszul complex of sections -/

/-- The underlying abelian presheaf of a sheaf of modules, through the forgetful functor to
presheaves of modules. -/
abbrev underlyingPresheaf : SheafOfModules.{u} R ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj

/-- The Koszul complex `Q_• = ∧^{•+1} ℤ[h_U]` of the trace of the free abelian presheaf on the
representable presheaf of `U`. -/
abbrev koszulPresheafComplex : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  presheafKoszul (freeYonedaTrace U)

/-- The functor `Hom(Q_p, -)` on sheaves of modules, the term in degree `p` of the Koszul
complex of sections. -/
abbrev koszulSectionsTerm (p : ℕ) : SheafOfModules.{u} R ⥤ AddCommGrpCat.{max w u} :=
  underlyingPresheaf R ⋙ preadditiveCoyoneda.obj (op ((koszulPresheafComplex U).X p))

/-- Precomposition with the Koszul differential `Q_{p+1} ⟶ Q_p`. -/
abbrev koszulSectionsDiff (p : ℕ) : koszulSectionsTerm R U p ⟶ koszulSectionsTerm R U (p + 1) :=
  Functor.whiskerLeft (underlyingPresheaf R)
    (preadditiveCoyoneda.map ((koszulPresheafComplex U).d (p + 1) p).op)

/-- The Koszul complex of sections, as a cochain complex of functors. -/
def koszulSectionsComplex :
    CochainComplex (SheafOfModules.{u} R ⥤ AddCommGrpCat.{max w u}) ℕ :=
  CochainComplex.of (koszulSectionsTerm R U) (koszulSectionsDiff R U) fun p => by
    rw [← Functor.whiskerLeft_comp, ← Functor.map_comp, ← op_comp,
      (koszulPresheafComplex U).d_comp_d, op_zero, Functor.map_zero]
    rfl

/-- **The Koszul complex of sections** `M ↦ (Hom(Q_p, M))_p`: the cochain complex obtained by
applying `Hom(-, M)` to the Koszul complex of the trace of `ℤ[h_U]`. -/
abbrev koszulSections : SheafOfModules.{u} R ⥤ CochainComplex AddCommGrpCat.{max w u} ℕ :=
  (koszulSectionsComplex R U).asFunctor

/-- The differential of the Koszul complex of sections of `M` from degree `p` to degree `p + 1`
is precomposition with the Koszul differential `Q_{p+1} ⟶ Q_p`. -/
theorem koszulSections_obj_d (M : SheafOfModules.{u} R) (p : ℕ) :
    ((koszulSections R U).obj M).d p (p + 1) = (koszulSectionsDiff R U p).app M := by
  change ((koszulSectionsComplex R U).d p (p + 1)).app M = _
  unfold koszulSectionsComplex
  exact congrArg (fun k => NatTrans.app k M) (CochainComplex.of_d _ _ p)

/-- The Koszul complex of sections is an additive functor. -/
instance koszulSections_additive : (koszulSections R U).Additive where
  map_add {M N φ ψ} := by
    ext p : 1
    exact (koszulSectionsTerm R U p).map_add

/-- The `p`-th component of the Koszul complex of sections is `Hom(Q_p, -)`. -/
def koszulSectionsComponentIso (p : ℕ) :
    Stacks.Cohomology.RightDerivedCoEdge.component (koszulSections R U) p ≅
      koszulSectionsTerm R U p :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Each component `Hom(Q_p, -)` of the Koszul complex of sections preserves finite limits. -/
instance koszulSections_component_preservesFiniteLimits [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (p : ℕ) :
    PreservesFiniteLimits
      (Stacks.Cohomology.RightDerivedCoEdge.component (koszulSections R U) p) :=
  preservesFiniteLimits_of_natIso (koszulSectionsComponentIso R U p).symm

/-! ### Exactness of the Koszul complex of sections on injective modules -/

/-- The first Koszul differential of `Q_•` followed by the augmentation is zero. -/
private theorem koszulPresheafComplex_d_comp_augmentation :
    (koszulPresheafComplex U).d 1 0 ≫ presheafKoszulAugmentation (freeYonedaTrace U) = 0 := by
  rw [presheafKoszul_d]
  exact presheafKoszulDiff_comp_presheafKoszulAugmentation _

/-- Two consecutive Koszul differentials of `Q_•` form an exact sequence. -/
private theorem exact_koszulPresheafComplex_d_comp_d (n : ℕ) :
    (ShortComplex.mk ((koszulPresheafComplex U).d (n + 2) (n + 1))
      ((koszulPresheafComplex U).d (n + 1) n)
      ((koszulPresheafComplex U).d_comp_d _ _ _)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (presheafKoszul_freeYonedaTrace_exact U (n + 1))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((presheafKoszul_d _ _).trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((presheafKoszul_d _ _).trans (Category.comp_id _).symm))

/-- The Koszul complex of presheaves is followed, in each degree, by an exact sequence into an
objectwise torsion-free presheaf: the next Koszul differential, or the augmentation in degree
`0`. -/
theorem exists_exact_koszulPresheafComplex_d (m : ℕ) :
    ∃ (N : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (g : (koszulPresheafComplex U).X m ⟶ N)
      (w : (koszulPresheafComplex U).d (m + 1) m ≫ g = 0),
      (∀ V, Module.IsTorsionFree ℤ (N.obj V)) ∧ (ShortComplex.mk _ _ w).Exact := by
  rcases m with _ | k
  · refine ⟨constantInt.{u} C, presheafKoszulAugmentation (freeYonedaTrace U),
      koszulPresheafComplex_d_comp_augmentation U, ?_, ?_⟩
    · intro V
      change Module.IsTorsionFree ℤ (ULift.{u} ℤ)
      exact Module.Flat.isTorsionFree
    · refine (ShortComplex.exact_iff_of_iso ?_).1
        (presheafKoszulAugmentation_freeYonedaTrace_exact U)
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans ((presheafKoszul_d _ 0).trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (Category.comp_id _).symm)
  · refine ⟨(koszulPresheafComplex U).X k, (koszulPresheafComplex U).d (k + 1) k,
      (koszulPresheafComplex U).d_comp_d _ _ _, ?_, ?_⟩
    · intro V
      change Module.IsTorsionFree ℤ
        ((presheafExteriorPower (yoneda.obj U ⋙ AddCommGrpCat.free) (k + 1)).obj V)
      infer_instance
    · exact exact_koszulPresheafComplex_d_comp_d U k

/-- **The Koszul complex of sections of an injective module is exact in positive degrees.**  A
map `Q_{m+1} ⟶ I` killed by the Koszul differential factors through the image of
`Q_{m+1} ⟶ Q_m`, and extends from that image to `Q_m` because the cokernel of the image is
torsion free. -/
theorem koszulSections_exactAt_of_injective [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (I : SheafOfModules.{u} R) [Injective I]
    (n : ℕ) (hn : 0 < n) : ((koszulSections R U).obj I).ExactAt n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro x hx
  let Q := koszulPresheafComplex U
  change (koszulPresheafComplex U).X (m + 1) ⟶ (underlyingPresheaf R).obj I at x
  have hx' : Q.d (m + 2) (m + 1) ≫ x = 0 := by
    change ((koszulSections R U).obj I).d (m + 1) (m + 2) x = 0 at hx
    rwa [koszulSections_obj_d] at hx
  let k := Q.d (m + 1) m
  obtain ⟨N, g, w, hN, hex⟩ := exists_exact_koszulPresheafComplex_d U m
  -- `(d_{m+2}, Q_{m+1} ↠ im k)` is exact, so `x` factors through `im k`
  have hexπ : (ShortComplex.mk (Q.d (m + 2) (m + 1)) (factorThruImage k) (by
      rw [← cancel_mono (image.ι k), assoc, image.fac, zero_comp]
      exact Q.d_comp_d _ _ _)).Exact := by
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk (Q.d (m + 2) (m + 1)) (factorThruImage k) _)
      (S₂ := ShortComplex.mk (Q.d (m + 2) (m + 1)) k (Q.d_comp_d _ _ _))
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := image.ι k, comm₁₂ := by simp,
        comm₂₃ := by simp }).2 (exact_koszulPresheafComplex_d_comp_d U m)
  obtain ⟨x', hx'π⟩ : ∃ x' : image k ⟶ (underlyingPresheaf R).obj I,
      factorThruImage k ≫ x' = x :=
    ⟨hexπ.gIsCokernel.desc (CokernelCofork.ofπ x hx'),
      hexπ.gIsCokernel.fac (CokernelCofork.ofπ x hx') WalkingParallelPair.one⟩
  -- `(im k ↪ Q_m, g)` is exact with torsion-free target, so `x'` extends to `Q_m`
  have hexι : (ShortComplex.mk (image.ι k) g (by
      rw [← cancel_epi (factorThruImage k), image.fac_assoc, comp_zero]
      exact w)).Exact := by
    refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk k g w)
      (S₂ := ShortComplex.mk (image.ι k) g _)
      { τ₁ := factorThruImage k, τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simp,
        comm₂₃ := by simp }).1 hex
  obtain ⟨y, hy⟩ := exists_comp_eq_of_isTorsionFree R I _ hexι hN x'
  refine ⟨y, ?_⟩
  change ((koszulSections R U).obj I).d m (m + 1) y = x
  rw [koszulSections_obj_d]
  change k ≫ y = x
  rw [← image.fac k, assoc, show image.ι k ≫ y = x' from hy, hx'π]

/-! ### The augmentation by global sections -/

/-- Maps of presheaves into a sheaf out of an exact sequence `X₁ ⟶ X₂ ⟶ X₃` with locally
surjective second map: `Hom(X₃, G) ⟶ Hom(X₂, G)` is injective with image the maps killed by
`X₁ ⟶ X₂`.  Sheafification is exact and turns a locally surjective map into an epimorphism, and
maps into a sheaf are maps out of the sheafification. -/
theorem sheafHom_exact [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u})} (hS : S.Exact)
    (hg : Presheaf.IsLocallySurjective J S.g) (G : Sheaf J AddCommGrpCat.{u}) :
    (∀ s : S.X₃ ⟶ G.obj, S.g ≫ s = 0 → s = 0) ∧
      ∀ f : S.X₂ ⟶ G.obj, S.f ≫ f = 0 → ∃ s : S.X₃ ⟶ G.obj, S.g ≫ s = f := by
  let a := sheafificationAdjunction J AddCommGrpCat.{u}
  let L := presheafToSheaf J AddCommGrpCat.{u}
  have hepi : Epi (L.map S.g) := (Sheaf.isLocallySurjective_iff_epi' _ _).1
    ((Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).2 hg)
  have hS' : (S.map L).Exact := hS.map L
  have : Epi (S.map L).g := hepi
  have hcok : IsColimit (CokernelCofork.ofπ (L.map S.g) (by
      rw [← L.map_comp, S.zero, L.map_zero])) :=
    (ShortComplex.Exact.gIsCokernel (S := S.map L) hS')
  have key : ∀ {P : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (s : P ⟶ G.obj), s = 0 ↔
      (a.homEquiv P G).symm s = 0 := by
    intro P s
    constructor
    · rintro rfl
      apply (a.homEquiv P G).injective
      rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
    · intro h
      rw [← (a.homEquiv P G).apply_symm_apply s, h, Adjunction.homEquiv_unit, Functor.map_zero,
        comp_zero]
  refine ⟨fun s hs => ?_, fun f hf => ?_⟩
  · rw [key] at hs ⊢
    rw [Adjunction.homEquiv_naturality_left_symm] at hs
    exact (cancel_epi (L.map S.g)).1 (hs.trans (comp_zero).symm)
  · rw [key, Adjunction.homEquiv_naturality_left_symm] at hf
    obtain ⟨t, ht⟩ := CokernelCofork.IsColimit.desc' hcok _ hf
    refine ⟨a.homEquiv _ G t, (a.homEquiv _ G).symm.injective ?_⟩
    rwa [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]

/-- Global sections of a sheaf of modules, as maps out of the constant presheaf `ℤ`. -/
abbrev globalSectionsHom : SheafOfModules.{u} R ⥤ AddCommGrpCat.{max w u} :=
  underlyingPresheaf R ⋙ preadditiveCoyoneda.obj (op (constantInt.{u} C))

/-- **The augmentation of the Koszul complex of sections by the global sections**: a global
section `s : ℤ ⟶ M` goes to its composite with the augmentation `Q_0 ⟶ ℤ`. -/
def koszulSectionsAugmentation :
    globalSectionsHom R ⟶
      Stacks.Cohomology.RightDerivedCoEdge.component (koszulSections R U) 0 :=
  Functor.whiskerLeft (underlyingPresheaf R)
      (preadditiveCoyoneda.map (presheafKoszulAugmentation (freeYonedaTrace U)).op) ≫
    (koszulSectionsComponentIso R U 0).inv

/-- The augmentation sends a global section `s : ℤ ⟶ M` to its composite with the augmentation
`Q_0 ⟶ ℤ`. -/
theorem koszulSectionsAugmentation_app_apply (M : SheafOfModules.{u} R)
    (s : constantInt.{u} C ⟶ (underlyingPresheaf R).obj M) :
    (koszulSectionsAugmentation R U).app M s =
      presheafKoszulAugmentation (freeYonedaTrace U) ≫ s :=
  rfl

/-- The augmentation by global sections followed by the first differential of the Koszul complex
of sections is zero. -/
theorem koszulSectionsAugmentation_comp_d (M : SheafOfModules.{u} R) :
    (koszulSectionsAugmentation R U).app M ≫ ((koszulSections R U).obj M).d 0 1 = 0 := by
  rw [koszulSections_obj_d]
  ext (s : constantInt.{u} C ⟶ (underlyingPresheaf R).obj M)
  change ((koszulPresheafComplex U).d 1 0 ≫ presheafKoszulAugmentation (freeYonedaTrace U)) ≫ s
    = 0
  rw [koszulPresheafComplex_d_comp_augmentation, zero_comp]

variable {U}

/-- If every object is covered by objects admitting a morphism to `U`, the augmentation
`Q_0 ⟶ ℤ` is locally surjective. -/
theorem isLocallySurjective_presheafKoszulAugmentation
    {ι : Type*} (hU : J.CoversTop fun _ : ι => U) :
    Presheaf.IsLocallySurjective J (presheafKoszulAugmentation (freeYonedaTrace U)) where
  imageSieve_mem {V} x := by
    refine J.superset_covering ?_ (hU V)
    intro W g hg
    obtain ⟨_, ⟨a₀⟩⟩ := hg
    have a : W ⟶ U := a₀
    let M := (yoneda.obj U ⋙ AddCommGrpCat.free).obj (op W)
    let y : M := x.down • (FreeAbelianGroup.of a : FreeAbelianGroup (W ⟶ U))
    refine ⟨(exteriorPower.oneEquiv ℤ M).symm y, ?_⟩
    change (freeYonedaTrace U).app (op W) ((exteriorPower.oneEquiv ℤ M)
      ((exteriorPower.oneEquiv ℤ M).symm y)) = x
    rw [LinearEquiv.apply_symm_apply]
    change FreeAbelianGroup.lift (fun _ => (ULift.up 1 : ULift.{u} ℤ))
      (x.down • (FreeAbelianGroup.of a : FreeAbelianGroup (W ⟶ U))) = x
    rw [map_zsmul, FreeAbelianGroup.lift_apply_of]
    ext
    simp

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The augmentation by global sections is injective. -/
theorem mono_koszulSectionsAugmentation_app {ι : Type*} (hU : J.CoversTop fun _ : ι => U)
    (M : SheafOfModules.{u} R) : Mono ((koszulSectionsAugmentation R U).app M) := by
  rw [AddCommGrpCat.mono_iff_injective]
  exact (injective_iff_map_eq_zero _).2 fun s hs =>
    (sheafHom_exact (presheafKoszulAugmentation_freeYonedaTrace_exact U)
      (isLocallySurjective_presheafKoszulAugmentation hU) ((SheafOfModules.toSheaf R).obj M)).1 s hs

/-- `Γ(M)` is the kernel of `Φ_0(M) ⟶ Φ_1(M)`. -/
theorem exact_koszulSectionsAugmentation {ι : Type*} (hU : J.CoversTop fun _ : ι => U)
    (M : SheafOfModules.{u} R) :
    (ShortComplex.mk ((koszulSectionsAugmentation R U).app M) ((koszulSections R U).obj M |>.d 0 1)
      (koszulSectionsAugmentation_comp_d R U M)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro f hf
  change ((koszulSections R U).obj M).d 0 1 f = 0 at hf
  rw [koszulSections_obj_d] at hf
  change (koszulPresheafComplex U).d 1 0 ≫ f = 0 at hf
  rw [presheafKoszul_d] at hf
  exact (sheafHom_exact (presheafKoszulAugmentation_freeYonedaTrace_exact U)
    (isLocallySurjective_presheafKoszulAugmentation hU) ((SheafOfModules.toSheaf R).obj M)).2 f hf

/-! ### Global sections through the Koszul complex of sections -/

/-- **The Koszul resolution bounds the cohomological dimension.**  Let `U` cover the final
object.  If the module `M` is acyclic for every term `Hom(Q_p, -)` of the Koszul complex of
sections and `Hom(Q_p, M) = 0` for `p ≥ d`, then `Rⁿ Γ(M) = 0` for every `n ≥ d`. -/
theorem isZero_rightDerived_globalSectionsHom [EnoughInjectives (SheafOfModules.{u} R)]
    {ι : Type*} (hU : J.CoversTop fun _ : ι => U) (M : SheafOfModules.{u} R)
    (hM : Stacks.Cohomology.RightDerivedCoEdge.IsComponentAcyclic (koszulSections R U) M)
    (d : ℕ) (hd : ∀ p, d ≤ p → IsZero (((koszulSections R U).obj M).X p)) (n : ℕ)
    (hn : d ≤ n) : IsZero (((globalSectionsHom R).rightDerived n).obj M) :=
  Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_of_isZero_X (globalSectionsHom R)
    (koszulSections R U) (koszulSectionsAugmentation R U) (koszulSectionsAugmentation_comp_d R U)
    (mono_koszulSectionsAugmentation_app R hU) (exact_koszulSectionsAugmentation R hU)
    (fun I _ n hn => koszulSections_exactAt_of_injective R U I n hn) M hM d hd n hn

/-- **A Koszul resolution by partially acyclic terms bounds the cohomological dimension.**  Let
`U` cover the final object and let the terms `Hom(Q_p, -)` of the Koszul complex of sections
vanish for `p ≥ d`.  If `Rᵠ Hom(Q_p, -)(M) = 0` for `q ≥ eₚ`, where every `eₚ ≥ 1`, then
`Rⁿ Γ(M) = 0` as soon as `p + eₚ ≤ n` for every `p < d`. -/
theorem isZero_rightDerived_globalSectionsHom_of_isZero_rightDerived
    [EnoughInjectives (SheafOfModules.{u} R)] {ι : Type*} (hU : J.CoversTop fun _ : ι => U)
    (d : ℕ) (hd : ∀ p, d ≤ p → ∀ N : SheafOfModules.{u} R,
      IsZero (((koszulSections R U).obj N).X p))
    (M : SheafOfModules.{u} R) (e : ℕ → ℕ) (he1 : ∀ p, 0 < e p)
    (he : ∀ p q, e p ≤ q → IsZero
      (((Stacks.Cohomology.RightDerivedCoEdge.component (koszulSections R U) p).rightDerived
        q).obj M))
    (n : ℕ) (hn : ∀ p, p < d → p + e p ≤ n) :
    IsZero (((globalSectionsHom R).rightDerived n).obj M) :=
  Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_of_isZero_rightDerived_component
    (koszulSections R U) (globalSectionsHom R) (koszulSectionsAugmentation R U)
    (koszulSectionsAugmentation_comp_d R U) (mono_koszulSectionsAugmentation_app R hU)
    (exact_koszulSectionsAugmentation R hU)
    (fun I _ n hn => koszulSections_exactAt_of_injective R U I n hn) d hd M e he1 he n hn

end Stacks.SheafOfModules
