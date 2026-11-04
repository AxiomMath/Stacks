module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAxiomA
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionHomotopy
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryComp

/-!
# Homogeneous maps of sheaf differential graded modules, read on sections

Let `X` be a ringed site, `A` a sheaf of differential graded algebras on it and `U` an object of
the site. A cochain `c : M ⟶ N` of degree `k` between right differential graded `A`-modules
which commutes with the action of `A` is, on the sections over `U`, a homogeneous map of
degree `k` of differential graded `A(U)`-modules `M(U) ⟶ N(U)`: on the summand `M^p(U)` it is
`c^p : M^p(U) ⟶ N^{p+k}(U)`. This reading is additive, commutes with the differentials of the
hom complexes, with composition and with identities, and on a morphism it is the homomorphism of
section modules it induces.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.sectionHomogeneous`: the homogeneous map
  `M(U) ⟶ N(U)` of degree `k` induced by an action-linear cochain of degree `k`.

## Main results

* `SheafOfModules.DifferentialGradedModule.sectionHomogeneous_add`,
  `sectionHomogeneous_delta`, `sectionHomogeneous_comp` and `sectionHomogeneous_ofHom`: the
  reading on sections is additive, compatible with the differentials, with composition and with
  morphisms.

## References

* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex DirectSum

universe t v w u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, v} R}
  {M N P : DifferentialGradedModule.{t, v, v} A}

/-- A cochain of degree `k` between right differential graded modules **commutes with the
action**: it is `SheafOfModules.DifferentialGradedModule.IsActionLinear`, stated over an
arbitrary sheaf of rings. -/
def IsSectionActionLinear {k : ℤ} (c : Cochain M.complex N.complex k) : Prop :=
  ∀ (p q i : ℤ) (hpq : p + k = q) (U : Cᵒᵖ)
      (x : (M.complex.X p).val.obj U) (a : (A.complex.X i).val.obj U),
    HEq (((c.v (p + i) (q + i) (by omega)).val.app U) ((M.mul p i).app U x a))
      ((N.mul q i).app U (((c.v p q hpq).val.app U) x) a)

/-- Over a ringed site, commuting with the action is `IsActionLinear`. -/
theorem isSectionActionLinear_iff {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {M N : DifferentialGradedModule.{u, v, v} A}
    {k : ℤ} (c : Cochain M.complex N.complex k) :
    IsSectionActionLinear c ↔ IsActionLinear A c :=
  Iff.rfl

/-- A module structure over the lifted integers is the action of the integers. -/
theorem uliftInt_smul_eq' {T : Type*} [AddCommGroup T] (iT : Module (ULift.{v} ℤ) T)
    (c : ULift.{v} ℤ) (x : T) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ iT.toSMul) c x = c.down • x :=
  @Int.cast_smul_eq_zsmul (ULift.{v} ℤ) T _ _ iT c.down x

/-- The sign `(-1)^n` of the lifted integers is `(-1)^n`. -/
theorem down_gradedSign (n : ℤ) :
    (DifferentialGraded.gradedSign (ULift.{v, 0} ℤ) n).down = (n.negOnePow : ℤ) := by
  have h : (DifferentialGraded.gradedSign (ULift.{v, 0} ℤ) n).down = (-1 : ℤ) ^ n.natAbs := by
    simp [DifferentialGraded.gradedSign]
  rw [h]
  rcases Nat.even_or_odd n.natAbs with hn | hn
  · rw [hn.neg_one_pow, Int.negOnePow_even _ (Int.natAbs_even.1 hn), Units.val_one]
  · rw [hn.neg_one_pow, Int.negOnePow_odd _ (Int.natAbs_odd.1 hn), Units.val_neg, Units.val_one]

/-- A cochain of degree `k` on the sections over `U` of the degree-`p` piece. -/
def cochainSectionApp {k : ℤ} (c : Cochain M.complex N.complex k) (U : Cᵒᵖ) (p : ℤ) :
    M.sectionsPiece U p →+ N.sectionsPiece U (p + k) :=
  AddMonoidHom.mk' (fun x ↦ (c.v p (p + k) rfl).val.app U x) fun x y ↦ map_add _ x y

/-- A cochain of degree `k` on the total sections over `U`: on the summand of degree `p` it is
the component `c^p`, landing in the summand of degree `p + k`. -/
def cochainSectionAdd {k : ℤ} (c : Cochain M.complex N.complex k) (U : Cᵒᵖ) :
    M.totalSections U →+ N.totalSections U :=
  DirectSum.toAddMonoid fun p ↦
    (DirectSum.of (N.sectionsPiece U) (p + k)).comp (cochainSectionApp c U p)

/-- On the summand of degree `p`, `cochainSectionAdd c U` is the component `c^p`, landing in the
summand of degree `p + k`. -/
theorem cochainSectionAdd_of {k : ℤ} (c : Cochain M.complex N.complex k) (U : Cᵒᵖ) (p : ℤ)
    (x : M.sectionsPiece U p) :
    cochainSectionAdd c U (DirectSum.of (M.sectionsPiece U) p x) =
      DirectSum.of (N.sectionsPiece U) (p + k) ((c.v p (p + k) rfl).val.app U x) :=
  DirectSum.toAddMonoid_of _ p x

/-- `cochainSectionAdd_of` at an arbitrary target degree `q = p + k`. -/
theorem cochainSectionAdd_of' {k : ℤ} (c : Cochain M.complex N.complex k) (U : Cᵒᵖ)
    {p q : ℤ} (hpq : p + k = q) (x : M.sectionsPiece U p) :
    cochainSectionAdd c U (DirectSum.of (M.sectionsPiece U) p x) =
      DirectSum.of (N.sectionsPiece U) q ((c.v p q hpq).val.app U x) := by
  subst hpq
  exact cochainSectionAdd_of c U p x

/-- An action-linear cochain, read on the total sections over `U`, commutes with the action of
the sections of `A`. -/
theorem cochainSectionAdd_act {k : ℤ} (c : Cochain M.complex N.complex k)
    (hc : IsSectionActionLinear c) (U : Cᵒᵖ) (x : M.totalSections U)
    (s : A.toGradedAlgebra.totalSections U) :
    cochainSectionAdd c U (M.act U x s) = N.act U (cochainSectionAdd c U x) s := by
  refine DFunLike.congr_fun (DFunLike.congr_fun (DirectSum.addHom_ext
    (f := (AddMonoidHom.compHom (cochainSectionAdd c U)).comp (M.act U))
    (g := (N.act U).comp (cochainSectionAdd c U)) fun p x ↦ DirectSum.addHom_ext fun i y ↦ ?_) x) s
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply]
  rw [act_of, actOn_of, cochainSectionAdd_of' c U (show p + i + k = p + k + i by omega),
    cochainSectionAdd_of, act_of, actOn_of]
  exact of_heq rfl (hc p (p + k) i rfl U x y)

/-- **An action-linear cochain of degree `k`, read on the sections over `U`**, as a homogeneous
map `M(U) ⟶ N(U)` of degree `k` of differential graded `A(U)`-modules. -/
def sectionHomogeneous {k : ℤ} (c : Cochain M.complex N.complex k) (hc : IsSectionActionLinear c)
    (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.HomogeneousMap (A.sectionAlgebra U) (M.sectionModule U)
      (N.sectionModule U) k :=
  ⟨uliftIntLinear (cochainSectionAdd c U), by
    refine ⟨?_, fun a x ↦ cochainSectionAdd_act c hc U x a⟩
    rintro p x ⟨y, rfl⟩
    change cochainSectionAdd c U (DirectSum.of (M.sectionsPiece U) p y) ∈
      Stacks.ExternalGrading.intSummand (N.sectionsPiece U) (p + k)
    rw [cochainSectionAdd_of]
    exact Stacks.ExternalGrading.of_mem_intSummand _ (p + k) _⟩

/-- The underlying map of `sectionHomogeneous c hc U` is `cochainSectionAdd c U`. -/
@[simp] theorem sectionHomogeneous_apply {k : ℤ} (c : Cochain M.complex N.complex k)
    (hc : IsSectionActionLinear c) (U : Cᵒᵖ) (x : M.totalSections U) :
    (sectionHomogeneous c hc U).1 x = cochainSectionAdd c U x :=
  rfl

/-- Two homogeneous maps out of a section module agreeing on every homogeneous section are
equal. -/
theorem sectionHomogeneous_ext {k : ℤ} (U : Cᵒᵖ)
    {f g : _root_.DifferentialGradedModule.HomogeneousMap (A.sectionAlgebra U) (M.sectionModule U)
      (N.sectionModule U) k}
    (h : ∀ (p : ℤ) (x : M.sectionsPiece U p),
      f.1 (DirectSum.of (M.sectionsPiece U) p x) = g.1 (DirectSum.of (M.sectionsPiece U) p x)) :
    f = g := by
  exact Subtype.ext (LinearMap.ext fun x ↦ DFunLike.congr_fun (DirectSum.addHom_ext
    (f := f.1.toAddMonoidHom) (g := g.1.toAddMonoidHom) h) x)

/-- The reading on sections is additive. -/
theorem sectionHomogeneous_add {k : ℤ} (c c' : Cochain M.complex N.complex k)
    (hc : IsSectionActionLinear c) (hc' : IsSectionActionLinear c')
    (hcc' : IsSectionActionLinear (c + c'))
    (U : Cᵒᵖ) :
    sectionHomogeneous (c + c') hcc' U = sectionHomogeneous c hc U + sectionHomogeneous c' hc' U :=
  sectionHomogeneous_ext U fun p x ↦ by
    show (sectionHomogeneous (c + c') hcc' U).1 _ =
      (sectionHomogeneous c hc U).1 _ + (sectionHomogeneous c' hc' U).1 _
    rw [sectionHomogeneous_apply, sectionHomogeneous_apply,
      sectionHomogeneous_apply, cochainSectionAdd_of, cochainSectionAdd_of, cochainSectionAdd_of,
      Cochain.add_v]
    exact (congrArg (DirectSum.of (N.sectionsPiece U) (p + k))
      (map_add (evalSectionHom U x) _ _)).trans (map_add _ _ _)

/-- **The reading on sections commutes with the differentials of the hom complexes.** -/
theorem sectionHomogeneous_delta {k : ℤ} (c : Cochain M.complex N.complex k)
    (hc : IsSectionActionLinear c) (hδ : IsSectionActionLinear (δ k (k + 1) c)) (U : Cᵒᵖ) :
    sectionHomogeneous (δ k (k + 1) c) hδ U =
      _root_.DifferentialGradedModule.homogeneousMapDifferential (A.sectionAlgebra U)
        (sectionHomogeneous c hc U) :=
  sectionHomogeneous_ext U fun p x ↦ by
    show (sectionHomogeneous (δ k (k + 1) c) hδ U).1 _ =
      (N.sectionModule U).d ((sectionHomogeneous c hc U).1 (DirectSum.of (M.sectionsPiece U) p x)) -
        DifferentialGraded.gradedSign (ULift.{v, 0} ℤ) k •
          (sectionHomogeneous c hc U).1
            ((M.sectionModule U).d (DirectSum.of (M.sectionsPiece U) p x))
    rw [sectionHomogeneous_apply,
      sectionHomogeneous_apply, sectionModule_d_of, sectionHomogeneous_apply,
      cochainSectionAdd_of, cochainSectionAdd_of' c U (show p + 1 + k = p + (k + 1) by omega),
      cochainSectionAdd_of, sectionModule_d_of, sectionDApp_apply, sectionDApp_apply]
    have hd' : DirectSum.of (N.sectionsPiece U) (p + k + 1)
          ((N.complex.d (p + k) (p + k + 1)).val.app U ((c.v p (p + k) rfl).val.app U x)) =
        DirectSum.of (N.sectionsPiece U) (p + (k + 1))
          ((N.complex.d (p + k) (p + (k + 1))).val.app U ((c.v p (p + k) rfl).val.app U x)) :=
      (sectionD_of' N U rfl _).symm.trans (sectionD_of' N U (by omega) _)
    rw [hd', δ_v k (k + 1) rfl c p (p + (k + 1)) rfl (p + k) (p + 1) (by omega) rfl]
    have e : ∀ (a b : M.complex.X p ⟶ N.complex.X (p + (k + 1))),
        (a + b).val.app U x = a.val.app U x + b.val.app U x :=
      fun a b ↦ map_add (evalSectionHom U x) a b
    have e' : ∀ (c : ℤˣ) (a : M.complex.X p ⟶ N.complex.X (p + (k + 1))),
        (c • a).val.app U x = (c : ℤ) • a.val.app U x := fun c a ↦ by
      rw [Units.smul_def]
      exact map_zsmul (evalSectionHom U x) (c : ℤ) a
    rw [e, comp_val_app_apply, e', comp_val_app_apply, map_add, map_zsmul]
    refine (congrArg (_ + ·) ?_).trans (sub_eq_add_neg _ _).symm
    refine Eq.trans ?_ (congrArg Neg.neg (uliftInt_smul_eq' (N.sectionModule U).module _ _)).symm
    rw [down_gradedSign, Int.negOnePow_succ, Units.val_neg, neg_smul]
    rfl

/-- **The reading on sections preserves composition.** -/
theorem sectionHomogeneous_comp {k l m : ℤ} (c : Cochain M.complex N.complex k)
    (c' : Cochain N.complex P.complex l) (h : k + l = m) (hc : IsSectionActionLinear c)
    (hc' : IsSectionActionLinear c') (hcc' : IsSectionActionLinear (c.comp c' h)) (U : Cᵒᵖ) :
    sectionHomogeneous (c.comp c' h) hcc' U =
      _root_.DifferentialGradedModule.homogeneousMapComp (A.sectionAlgebra U)
        (show l + k = m by omega) (sectionHomogeneous c' hc' U) (sectionHomogeneous c hc U) :=
  sectionHomogeneous_ext U fun p x ↦ by
    show (sectionHomogeneous (c.comp c' h) hcc' U).1
        (DirectSum.of (M.sectionsPiece U) p x : (M.sectionModule U).M) =
      (sectionHomogeneous c' hc' U).1 ((sectionHomogeneous c hc U).1
        (DirectSum.of (M.sectionsPiece U) p x : (M.sectionModule U).M))
    rw [sectionHomogeneous_apply, sectionHomogeneous_apply, sectionHomogeneous_apply,
      cochainSectionAdd_of, cochainSectionAdd_of,
      cochainSectionAdd_of' c' U (show p + k + l = p + m by omega),
      Cochain.comp_v c c' h p (p + k) (p + m) rfl (by omega), comp_val_app_apply]

/-- **On a morphism, the reading on sections is the induced homomorphism of section
modules.** -/
theorem sectionHomogeneous_ofHom (f : M ⟶ N)
    (hf : IsSectionActionLinear (Cochain.ofHom f.toHomologicalComplex)) (U : Cᵒᵖ) :
    sectionHomogeneous (Cochain.ofHom f.toHomologicalComplex) hf U =
      (_root_.DifferentialGradedModule.cocycleOfHom (A.sectionAlgebra U) (sectionMap f U)).1 :=
  sectionHomogeneous_ext U fun p x ↦ by
    show (sectionHomogeneous (Cochain.ofHom f.toHomologicalComplex) hf U).1
        (DirectSum.of (M.sectionsPiece U) p x : (M.sectionModule U).M) =
      (sectionMap f U).toFun (DirectSum.of (M.sectionsPiece U) p x : (M.sectionModule U).M)
    rw [sectionHomogeneous_apply, cochainSectionAdd_of' _ U (add_zero p), Cochain.ofHom_v,
      sectionMap_toFun, sectionMapAdd_of]
    rfl

/-- **The reading on sections commutes with restriction**: restricting `c(x)` along `a : V ⟶ U`
is applying `c` to the restriction of `x`. -/
theorem sectionRestrictAdd_cochainSectionAdd {k : ℤ} (c : Cochain M.complex N.complex k)
    {U V : Cᵒᵖ} (a : V ⟶ U) (x : M.totalSections V) :
    N.sectionRestrictAdd a (cochainSectionAdd c V x) =
      cochainSectionAdd c U (M.sectionRestrictAdd a x) := by
  refine DFunLike.congr_fun (DirectSum.addHom_ext
    (f := (N.sectionRestrictAdd a).comp (cochainSectionAdd c V))
    (g := (cochainSectionAdd c U).comp (M.sectionRestrictAdd a)) fun p x ↦ ?_) x
  simp only [AddMonoidHom.comp_apply]
  rw [cochainSectionAdd_of, sectionRestrictAdd_of, sectionRestrictAdd_of, cochainSectionAdd_of,
    sectionRestrictApp_apply, sectionRestrictApp_apply]
  exact congrArg (DirectSum.of (N.sectionsPiece U) (p + k))
    (PresheafOfModules.naturality_apply (c.v p (p + k) rfl).val a x).symm

/-- **The homogeneous map induced on sections commutes with restriction**, as homogeneous maps of
section modules. -/
theorem sectionModuleRestriction_sectionHomogeneous {k : ℤ} (c : Cochain M.complex N.complex k)
    (hc : IsSectionActionLinear c) {U V : Cᵒᵖ} (a : V ⟶ U) (x : (M.sectionModule V).M) :
    (N.sectionModuleRestriction a).toFun ((sectionHomogeneous c hc V).1 x) =
      (sectionHomogeneous c hc U).1 ((M.sectionModuleRestriction a).toFun x) :=
  sectionRestrictAdd_cochainSectionAdd c a x

end SheafOfModules.DifferentialGradedModule
