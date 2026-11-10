module

public import StacksFrontier.AlgebraicGeometry.Spaces.RetractionTransferExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.AdicSectionsAffineDescent
public import StacksFrontier.Deformation.ModuleDeformation.CopowerExtension

/-!
# Morphisms of direct images along a split square-zero thickening

Let `r : X' ⟶ X₀` be an affine morphism of algebraic spaces which is a split square-zero
thickening of `X₀` by `M` in the sense of `AlgebraicGeometry.Space.IsSplitThickeningBy`. A
morphism of `𝒪_{X₀}`-modules `φ : r_*ℱ₁ ⟶ r_*ℱ₂` between direct images of quasi-coherent
`𝒪_{X'}`-modules which commutes with multiplication by the square-zero functions `ι v` is the
direct image of a morphism `ℱ₁ ⟶ ℱ₂`, and the direct image is faithful on morphisms out of a
quasi-coherent module.

## Main results

* `AlgebraicGeometry.Space.exists_retractionPushforward_map_eq`: a morphism of direct images of
  quasi-coherent modules commuting with the square-zero functions is the direct image of a
  morphism.
* `AlgebraicGeometry.Space.exists_iso_retractionPushforward_map_eq`: an isomorphism of direct
  images commuting with the square-zero functions is the direct image of an isomorphism.
* `AlgebraicGeometry.Space.exists_iso_of_extensionClass_retractionCopowerExtension_eq`: two flat
  modules over a split square-zero thickening whose extensions have the same class are
  isomorphic, compatibly with the identifications with `𝒢`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] isContinuous_smallBaseChange

variable {X₀ X' : AlgebraicSpaces B S hS} {r : X' ⟶ X₀}
  {hrep : yoneda.relativelyRepresentable r.hom} {i : X₀ ⟶ X'} {hi : i ≫ r = 𝟙 X₀}
  {k : Type u} [Field k] {M : FGModuleCat.{u} k}
  {ψ₀ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₀.1 X₀.2).O)}
  {ψ' : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)}
  {ι : ↥M →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)}
  (hs : IsSplitThickeningBy B S hS r hrep i hi M ψ₀ ψ' ι)
  {F₁ F₂ : Modules.{u, u} B S hS X'.1 X'.2}

omit [Field k] in
/-- The pullback of functions along a base-changed chart, as a ring homomorphism of chart
rings. -/
def sharpChart (r : X' ⟶ X₀) (hrep : yoneda.relativelyRepresentable r.hom)
    (U : SmallEtale B S hS X₀.1) :
    chartRing B S hS X₀.1 X₀.2 U →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj
        (op ((smallBaseChange B S hS r hrep).obj U)) :=
  ((smallBaseChangeSharp B S hS r hrep).hom.app (op U)).hom

include hs in
/-- **On an affine chart, a function of `X'` is a function of `X₀` plus a combination of the
`ι v` with coefficients functions of `X₀`.** -/
theorem exists_eq_sharp_add_sum (U : SmallEtale B S hS X₀.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj
        (op ((smallBaseChange B S hS r hrep).obj U))) :
    ∃ (b : chartRing B S hS X₀.1 X₀.2 U) (n : ℕ) (v : Fin n → ↥M)
      (c : Fin n → chartRing B S hS X₀.1 X₀.2 U),
      a = sharpChart B S hS r hrep U b +
        ∑ l, (ι (v l)).1 (op ((smallBaseChange B S hS r hrep).obj U)) *
          sharpChart B S hS r hrep U (c l) := by
  let ρ : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj
        (op ((smallBaseChange B S hS r hrep).obj U)) →+* chartRing B S hS X₀.1 X₀.2 U :=
    chartDiagramRestrict B S hS i (retractionChartDiagram B S hS r hrep i hi U)
  let σ := sharpChart B S hS r hrep U
  have hk : RingHom.ker ρ = Ideal.span (Set.range fun v : ↥M =>
      (ι v).1 (op ((smallBaseChange B S hS r hrep).obj U))) := hs.ker_eq U hU
  have hρσ : ∀ t, ρ (σ t) = t := fun t =>
    chartDiagramRestrict_retractionChartDiagram_smallBaseChangeSharp B S hS r hrep i hi U t
  have hmem : ∀ t, t - σ (ρ t) ∈ Ideal.span (Set.range fun v : ↥M =>
      (ι v).1 (op ((smallBaseChange B S hS r hrep).obj U))) := fun t => by
    rw [← hk]
    change ρ (t - σ (ρ t)) = 0
    rw [map_sub, hρσ, sub_self]
  obtain ⟨n, t, v, hsum⟩ : ∃ (n : ℕ) (t : Fin n →
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj
        (op ((smallBaseChange B S hS r hrep).obj U))) (v : Fin n → ↥M),
      a - σ (ρ a) = ∑ l, t l * (ι (v l)).1 (op ((smallBaseChange B S hS r hrep).obj U)) := by
    refine Submodule.span_induction (p := fun x _ => ∃ (n : ℕ) (t : Fin n → _) (v : Fin n → ↥M),
      x = ∑ l, t l * (ι (v l)).1 (op ((smallBaseChange B S hS r hrep).obj U))) ?_ ?_ ?_ ?_ (hmem a)
    · rintro _ ⟨w, rfl⟩
      exact ⟨1, fun _ => 1, fun _ => w, by simp⟩
    · exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    · rintro x y _ _ ⟨n, t, v, rfl⟩ ⟨m, t', v', rfl⟩
      exact ⟨n + m, Fin.append t t', Fin.append v v', by rw [Fin.sum_univ_add]; simp⟩
    · rintro c x _ ⟨n, t, v, rfl⟩
      exact ⟨n, fun l => c * t l, v, by rw [smul_eq_mul, Finset.mul_sum]; simp [mul_assoc]⟩
  have hιt : ∀ (w : ↥M) (t : (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj
        (op ((smallBaseChange B S hS r hrep).obj U))),
      (ι w).1 (op ((smallBaseChange B S hS r hrep).obj U)) * t =
        (ι w).1 (op ((smallBaseChange B S hS r hrep).obj U)) * σ (ρ t) := by
    intro w t
    have h2 : (ι w).1 (op ((smallBaseChange B S hS r hrep).obj U)) * (t - σ (ρ t)) = 0 := by
      refine Submodule.span_induction (p := fun x _ =>
        (ι w).1 (op ((smallBaseChange B S hS r hrep).obj U)) * x = 0) ?_ ?_ ?_ ?_ (hmem t)
      · rintro _ ⟨w', rfl⟩
        exact congrArg (fun s => s.1 (op ((smallBaseChange B S hS r hrep).obj U)))
          (hs.mul_eq_zero w w')
      · exact mul_zero _
      · intro x y _ _ hx hy
        rw [mul_add, hx, hy, add_zero]
      · intro c x _ hx
        rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
    rwa [mul_sub, sub_eq_zero] at h2
  refine ⟨ρ a, n, v, fun l => ρ (t l), ?_⟩
  rw [← sub_eq_iff_eq_add', hsum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm, hιt]

omit [Field k] in
/-- An additive map commuting with the actions of the elements `σ b` and `e w` commutes with the
action of every element `σ b + ∑ e (v l) * σ (c l)`. -/
theorem _root_.AddMonoidHom.map_smul_of_generators {R A W N₁ N₂ : Type*} [CommRing R] [CommRing A]
    [AddCommGroup N₁] [AddCommGroup N₂] [Module R N₁] [Module R N₂] (σ : A →+* R) (e : W → R)
    (g : N₁ →+ N₂) (hlin : ∀ b y, g (σ b • y) = σ b • g y) (hι : ∀ w y, g (e w • y) = e w • g y)
    (b : A) {n : ℕ} (v : Fin n → W) (c : Fin n → A) (x : N₁) :
    g ((σ b + ∑ l, e (v l) * σ (c l)) • x) = (σ b + ∑ l, e (v l) * σ (c l)) • g x := by
  rw [add_smul, add_smul, map_add, hlin, Finset.sum_smul, Finset.sum_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_smul, mul_smul, hι, hlin]

variable (r) in
include hs in
/-- **A morphism of direct images commuting with the square-zero functions is linear over the
functions of `X'` on an affine chart.** -/
theorem retractionPushforward_hom_smul_of_isAffine
    (φ : (retractionPushforward B S hS r hrep).obj F₁ ⟶
      (retractionPushforward B S hS r hrep).obj F₂)
    (hφ : ∀ v : ↥M, retractionMultiplication B S hS r hrep M ι F₁ v ≫ φ =
      φ ≫ retractionMultiplication B S hS r hrep M ι F₂ v)
    (U : SmallEtale B S hS X₀.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (g : F₁.val.obj (op ((smallBaseChange B S hS r hrep).obj U)) →+
      F₂.val.obj (op ((smallBaseChange B S hS r hrep).obj U)))
    (hg : ∀ x, g x = φ.val.app (op U) x)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj
        (op ((smallBaseChange B S hS r hrep).obj U)))
    (x : F₁.val.obj (op ((smallBaseChange B S hS r hrep).obj U))) :
    g (a • x) = a • g x := by
  obtain ⟨b, n, v, c, rfl⟩ := exists_eq_sharp_add_sum B S hS hs U hU a
  have hlin : ∀ (b : chartRing B S hS X₀.1 X₀.2 U)
      (y : F₁.val.obj (op ((smallBaseChange B S hS r hrep).obj U))),
      g (sharpChart B S hS r hrep U b • y) = sharpChart B S hS r hrep U b • g y := fun b y =>
    ((hg _).trans ((φ.val.app (op U)).hom.map_smul b y)).trans
      (congrArg (fun z => sharpChart B S hS r hrep U b • z) (hg y).symm)
  have hι : ∀ (w : ↥M) (y : F₁.val.obj (op ((smallBaseChange B S hS r hrep).obj U))),
      g ((ι w).1 (op ((smallBaseChange B S hS r hrep).obj U)) • y) =
        (ι w).1 (op ((smallBaseChange B S hS r hrep).obj U)) • g y := fun w y =>
    ((hg _).trans (congrArg (fun ψ => ψ.val.app (op U) y) (hφ w))).trans
      (congrArg (fun z => (ι w).1 (op ((smallBaseChange B S hS r hrep).obj U)) • z) (hg y).symm)
  exact g.map_smul_of_generators (sharpChart B S hS r hrep U)
    (fun w => (ι w).1 (op ((smallBaseChange B S hS r hrep).obj U))) hlin hι b v c x

omit [Field k] in
/-- For an adjunction whose counit is invertible at `M` and `N`, every morphism `R M ⟶ R N` is the
image of a morphism `M ⟶ N`. -/
theorem _root_.CategoryTheory.Adjunction.map_preimage_of_isIso_counit {C D : Type*} [Category C]
    [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {M N : D} [IsIso (adj.counit.app M)]
    [IsIso (adj.counit.app N)] (g : R.obj M ⟶ R.obj N) :
    R.map (inv (adj.counit.app M) ≫ L.map g ≫ adj.counit.app N) = g := by
  have h1 : R.map (inv (adj.counit.app M)) = adj.unit.app (R.obj M) := by
    rw [← cancel_mono (R.map (adj.counit.app M)), ← R.map_comp, IsIso.inv_hom_id, R.map_id,
      adj.right_triangle_components]
    rfl
  rw [R.map_comp, R.map_comp, h1, ← Category.assoc]
  have := adj.unit.naturality g
  simp only [Functor.id_map, Functor.comp_map] at this
  rw [← this, Category.assoc, adj.right_triangle_components]
  exact Category.comp_id g

omit [Field k] in
/-- For an adjunction whose counit is invertible at `M`, the right adjoint is injective on
morphisms out of `M`. -/
theorem _root_.CategoryTheory.Adjunction.map_injective_of_isIso_counit {C D : Type*} [Category C]
    [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {M N : D} [IsIso (adj.counit.app M)]
    {θ θ' : M ⟶ N} (h : R.map θ = R.map θ') : θ = θ' := by
  have e : ∀ t : M ⟶ N, t = inv (adj.counit.app M) ≫ L.map (R.map t) ≫ adj.counit.app N :=
    fun t => by
      have := adj.counit.naturality t
      simp only [Functor.id_map, Functor.comp_map] at this
      rw [this, IsIso.inv_hom_id_assoc]
  rw [e θ, e θ', h]

omit [Field k] in
/-- Sections of a module over an algebraic space agree as soon as their restrictions to all affine
charts do. -/
theorem modules_section_ext_of_isAffine {Z : AlgebraicSpaces B S hS}
    (N : Modules.{u, u} B S hS Z.1 Z.2) {U : SmallEtale B S hS Z.1} (x y : N.val.obj (op U))
    (h : ∀ (V : SmallEtale B S hS Z.1) (j : V ⟶ U), IsAffine (chartScheme V) →
      N.val.map j.op x = N.val.map j.op y) : x = y :=
  SmallEtale.C1573.eq_of_forall_isAffine B S hS Z.1 Z.2
    (C1573.isSheaf_forget_factor B S hS Z.1 Z.2 N) h

variable (r) in
include hs in
/-- **A morphism of direct images commuting with the square-zero functions is linear over the
functions of `X'` on every chart.** -/
theorem retractionPushforward_hom_smul
    (φ : (retractionPushforward B S hS r hrep).obj F₁ ⟶
      (retractionPushforward B S hS r hrep).obj F₂)
    (hφ : ∀ v : ↥M, retractionMultiplication B S hS r hrep M ι F₁ v ≫ φ =
      φ ≫ retractionMultiplication B S hS r hrep M ι F₂ v)
    (U : SmallEtale B S hS X₀.1)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.obj
        (op ((smallBaseChange B S hS r hrep).obj U)))
    (x : F₁.val.obj (op ((smallBaseChange B S hS r hrep).obj U))) :
    let g : F₁.val.obj (op ((smallBaseChange B S hS r hrep).obj U)) →+
      F₂.val.obj (op ((smallBaseChange B S hS r hrep).obj U)) :=
        (φ.val.app (op U)).hom.toAddMonoidHom
    g (a • x) = a • g x := by
  intro g
  let lhs : ((retractionPushforward B S hS r hrep).obj F₂).val.obj (op U) := g (a • x)
  let rhs : ((retractionPushforward B S hS r hrep).obj F₂).val.obj (op U) := a • g x
  change lhs = rhs
  refine modules_section_ext_of_isAffine B S hS _ lhs rhs fun V j hV => ?_
  let j' := (smallBaseChange B S hS r hrep).map j
  let gV : F₁.val.obj (op ((smallBaseChange B S hS r hrep).obj V)) →+
      F₂.val.obj (op ((smallBaseChange B S hS r hrep).obj V)) :=
        (φ.val.app (op V)).hom.toAddMonoidHom
  have hnat : ∀ y : F₁.val.obj (op ((smallBaseChange B S hS r hrep).obj U)),
      F₂.val.map j'.op (g y) = gV (F₁.val.map j'.op y) := fun y =>
    (PresheafOfModules.naturality_apply φ.val j.op y).symm
  have haff := retractionPushforward_hom_smul_of_isAffine B S hS r hs φ hφ V hV gV (fun _ => rfl)
  have e1 := hnat (a • x)
  have e2 := PresheafOfModules.map_smul F₁.val j'.op a x
  have e3 := haff ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.map j'.op a) (F₁.val.map j'.op x)
  have e4 := PresheafOfModules.map_smul F₂.val j'.op a (g x)
  have e5 := hnat x
  have key : F₂.val.map j'.op (g (a • x)) = F₂.val.map j'.op (a • g x) :=
    e1.trans ((congrArg gV e2).trans (e3.trans
      ((congrArg (fun z => (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj.map j'.op a • z) e5.symm).trans e4.symm)))
  exact key

variable (r) in
/-- The morphism of restrictions along base change of charts attached to a morphism of direct
images commuting with the square-zero functions. -/
def retractionLift
    (φ : (retractionPushforward B S hS r hrep).obj F₁ ⟶
      (retractionPushforward B S hS r hrep).obj F₂)
    (hφ : ∀ v : ↥M, retractionMultiplication B S hS r hrep M ι F₁ v ≫ φ =
      φ ≫ retractionMultiplication B S hS r hrep M ι F₂ v) :
    (siteDirectImage B S hS r hrep).obj F₁ ⟶ (siteDirectImage B S hS r hrep).obj F₂ where
  val := PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (φ.val.app U).hom.toAddMonoidHom
      naturality := fun {U V} j => by
        ext x
        exact PresheafOfModules.naturality_apply φ.val j x }
    (fun U a x => retractionPushforward_hom_smul B S hS r hs φ hφ U.unop a x)

variable (r) in
include hs in
/-- **Stacks 08AI read on a split square-zero thickening**: a morphism of direct images of
quasi-coherent modules commuting with the square-zero functions is the direct image of a
morphism. -/
theorem exists_retractionPushforward_map_eq (hr : IsAffineHom B S hS r.hom)
    (hF₁ : F₁.IsQuasicoherentOnSite) (hF₂ : F₂.IsQuasicoherentOnSite)
    (φ : (retractionPushforward B S hS r hrep).obj F₁ ⟶
      (retractionPushforward B S hS r hrep).obj F₂)
    (hφ : ∀ v : ↥M, retractionMultiplication B S hS r hrep M ι F₁ v ≫ φ =
      φ ≫ retractionMultiplication B S hS r hrep M ι F₂ v) :
    ∃ θ : F₁ ⟶ F₂, (retractionPushforward B S hS r hrep).map θ = φ := by
  let adj := siteAdjunction B S hS r hrep
  have := isIso_siteAdjunction_counit_app B S hS r hr hrep F₁ hF₁
  have := isIso_siteAdjunction_counit_app B S hS r hr hrep F₂ hF₂
  let g := retractionLift B S hS r hs φ hφ
  refine ⟨inv (adj.counit.app F₁) ≫ ((directImageRingEquivalence B S hS r hrep).functor ⋙
    directImageAlgebraPullback B S hS r).map g ≫ adj.counit.app F₂, ?_⟩
  ext U x
  exact congrArg (fun t => t.val.app U x) (adj.map_preimage_of_isIso_counit g)

omit [Field k] in
variable (r hrep) in
/-- The direct image along small-chart base change determines the restriction along base change
of charts. -/
theorem siteDirectImage_map_eq_of_retractionPushforward_map_eq
    {G₁ G₂ : Modules.{u, u} B S hS X'.1 X'.2}
    {t t' : G₁ ⟶ G₂}
    (h : (retractionPushforward B S hS r hrep).map t =
      (retractionPushforward B S hS r hrep).map t') :
    (siteDirectImage B S hS r hrep).map t = (siteDirectImage B S hS r hrep).map t' := by
  ext U x
  exact congrArg (fun s => s.val.app U x) h

omit [Field k] in
variable (r hrep) in
/-- The direct image along small-chart base change is faithful on morphisms out of a
quasi-coherent module, for an affine morphism. -/
theorem retractionPushforward_map_injective (hr : IsAffineHom B S hS r.hom)
    {G₁ G₂ : Modules.{u, u} B S hS X'.1 X'.2} (hG₁ : G₁.IsQuasicoherentOnSite) {t t' : G₁ ⟶ G₂}
    (h : (retractionPushforward B S hS r hrep).map t =
      (retractionPushforward B S hS r hrep).map t') :
    t = t' := by
  have := isIso_siteAdjunction_counit_app B S hS r hr hrep G₁ hG₁
  exact (siteAdjunction B S hS r hrep).map_injective_of_isIso_counit
    (siteDirectImage_map_eq_of_retractionPushforward_map_eq B S hS r hrep h)

variable (r) in
include hs in
/-- **An isomorphism of direct images commuting with the square-zero functions is the direct
image of an isomorphism.** -/
theorem exists_iso_retractionPushforward_map_eq (hr : IsAffineHom B S hS r.hom)
    (hF₁ : F₁.IsQuasicoherentOnSite) (hF₂ : F₂.IsQuasicoherentOnSite)
    (φ : (retractionPushforward B S hS r hrep).obj F₁ ≅
      (retractionPushforward B S hS r hrep).obj F₂)
    (hφ : ∀ v : ↥M, retractionMultiplication B S hS r hrep M ι F₁ v ≫ φ.hom =
      φ.hom ≫ retractionMultiplication B S hS r hrep M ι F₂ v) :
    ∃ θ : F₁ ≅ F₂, (retractionPushforward B S hS r hrep).map θ.hom = φ.hom := by
  have hφ' : ∀ v : ↥M, retractionMultiplication B S hS r hrep M ι F₂ v ≫ φ.inv =
      φ.inv ≫ retractionMultiplication B S hS r hrep M ι F₁ v := fun v => by
    rw [← Iso.cancel_iso_hom_left φ, ← Category.assoc, ← hφ v, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  obtain ⟨θ₁, h₁⟩ := exists_retractionPushforward_map_eq B S hS r hs hr hF₁ hF₂ φ.hom hφ
  obtain ⟨θ₂, h₂⟩ := exists_retractionPushforward_map_eq B S hS r hs hr hF₂ hF₁ φ.inv hφ'
  exact ⟨⟨θ₁, θ₂,
    retractionPushforward_map_injective B S hS r hrep hr hF₁ (by simp [h₁, h₂]),
    retractionPushforward_map_injective B S hS r hrep hr hF₂ (by simp [h₁, h₂])⟩, h₁⟩

section Injective

variable {i₂ : X₀ ⟶ X'} {hi₂ : i₂ ≫ r = 𝟙 X₀}
  {ψ'₂ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)}
  {ι₂ : ↥M →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)}
  (hs₂ : IsSplitThickeningBy B S hS r hrep i₂ hi₂ M ψ₀ ψ'₂ ι₂)
  {G : Modules.{u, u} B S hS X₀.1 X₀.2}
  (ψ₁ : (modulePullback B S hS i).obj F₁ ≅ G) (ψ₂ : (modulePullback B S hS i₂).obj F₂ ≅ G)
  (hF₁ : F₁.IsQuasicoherentOnSite) (hF₂ : F₂.IsQuasicoherentOnSite)
  (hflat₁ : ∀ U : SmallEtale B S hS X₀.1,
    IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
    ∀ n : Fin (Module.finrank k M) → F₁.val.obj (op (retractionChartDiagram B S hS r hrep i
      hi U).V),
      ∑ j, (ι (Deformation.ModuleDeformation.stdBasis M j)).1
          (op (retractionChartDiagram B S hS r hrep i hi U).V) • n j = 0 →
        ∀ j, n j ∈ (RingHom.ker (chartDiagramRestrict B S hS i
          (retractionChartDiagram B S hS r hrep i hi U))) •
            (⊤ : Submodule (chartRing B S hS X'.1 X'.2
                (retractionChartDiagram B S hS r hrep i hi U).V)
              (F₁.val.obj (op (retractionChartDiagram B S hS r hrep i hi U).V))))
  (hflat₂ : ∀ U : SmallEtale B S hS X₀.1,
    IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
    ∀ n : Fin (Module.finrank k M) → F₂.val.obj (op (retractionChartDiagram B S hS r hrep i₂
      hi₂ U).V),
      ∑ j, (ι₂ (Deformation.ModuleDeformation.stdBasis M j)).1
          (op (retractionChartDiagram B S hS r hrep i₂ hi₂ U).V) • n j = 0 →
        ∀ j, n j ∈ (RingHom.ker (chartDiagramRestrict B S hS i₂
          (retractionChartDiagram B S hS r hrep i₂ hi₂ U))) •
            (⊤ : Submodule (chartRing B S hS X'.1 X'.2
                (retractionChartDiagram B S hS r hrep i₂ hi₂ U).V)
              (F₂.val.obj (op (retractionChartDiagram B S hS r hrep i₂ hi₂ U).V))))
  [HasExt.{w'} (Modules.{u, u} B S hS X₀.1 X₀.2)]

variable (r) in
include hs hs₂ in
/-- **Two flat modules over a split square-zero thickening whose extensions have the same class
are isomorphic, compatibly with the identifications with `𝒢`.** -/
theorem exists_iso_of_extensionClass_retractionCopowerExtension_eq
    (hr : IsAffineHom B S hS r.hom) (hii : i = i₂) (hι : ι₂ = ι)
    (h : letI := retractionLinear B S hS (X₀ := X₀) ψ₀
      (retractionCopowerExtension B S hS F₁ G ψ₁ hF₁ hs hflat₁).extensionClass =
        (retractionCopowerExtension B S hS F₂ G ψ₂ hF₂ hs₂ hflat₂).extensionClass) :
    ∃ θ : F₁ ≅ F₂, (modulePullback B S hS i).map θ.hom ≫
      eqToHom (congrArg (fun g => (modulePullback B S hS g).obj F₂) hii) ≫ ψ₂.hom = ψ₁.hom := by
  subst hii
  subst ι₂
  let := retractionLinear B S hS (X₀ := X₀) ψ₀
  obtain ⟨Φ₀, hΦp₀, hΦμ₀⟩ :=
    Deformation.ModuleDeformation.CopowerExtension.exists_iso_of_extensionClass_eq _ _ h
  let Φ : (retractionPushforward B S hS r hrep).obj F₁ ≅
      (retractionPushforward B S hS r hrep).obj F₂ := Φ₀
  have hΦp : Φ.hom ≫ retractionProjection B S hS r hrep i hi F₂ G ψ₂ =
      retractionProjection B S hS r hrep i hi F₁ G ψ₁ := hΦp₀
  have hΦμ : ∀ v, retractionMultiplicationFactor B S hS F₁ G ψ₁ hF₁ hs v ≫ Φ.hom =
      retractionMultiplicationFactor B S hS F₂ G ψ₂ hF₂ hs₂ v := hΦμ₀
  have := epi_retractionProjection B S hS F₁ G ψ₁ hF₁ hs
  have hmult : ∀ v : ↥M, retractionMultiplication B S hS r hrep M ι F₁ v ≫ Φ.hom =
      Φ.hom ≫ retractionMultiplication B S hS r hrep M ι F₂ v := fun v => by
    rw [← retractionProjection_comp_factor B S hS F₁ G ψ₁ hF₁ hs v,
      ← retractionProjection_comp_factor B S hS F₂ G ψ₂ hF₂ hs₂ v, Category.assoc, hΦμ v,
      ← Category.assoc, hΦp]
  obtain ⟨θ, hθ⟩ := exists_iso_retractionPushforward_map_eq B S hS r hs hr hF₁ hF₂ Φ hmult
  refine ⟨θ, ?_⟩
  have hp : (retractionPushforward B S hS r hrep).map θ.hom ≫
      retractionProjection B S hS r hrep i hi F₂ G ψ₂ =
      retractionProjection B S hS r hrep i hi F₁ G ψ₁ := by
    rwa [hθ]
  have hred : Epi (reductionMap B S hS r hrep i hi F₁) := by
    have e : reductionMap B S hS r hrep i hi F₁ =
        retractionProjection B S hS r hrep i hi F₁ G ψ₁ ≫ ψ₁.inv := by
      rw [retractionProjection, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [e]
    exact epi_comp' this (IsIso.epi_of_iso _)
  rw [eqToHom_refl, Category.id_comp]
  apply (cancel_epi (reductionMap B S hS r hrep i hi F₁)).1
  rwa [← Category.assoc, ← reductionMap_naturality]

end Injective

end AlgebraicGeometry.Space

end
