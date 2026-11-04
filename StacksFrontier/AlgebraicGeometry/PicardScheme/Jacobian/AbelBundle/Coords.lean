module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.ZeroSchemeFamily
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.FibreSections
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.GlobalFunctions

/-!
# Divisors in the linear system of a basis of sections

Let `X` be a smooth proper geometrically irreducible curve over a field `k`, `L₀` an invertible
module on `X_{B₀}` and `e₀, …, e_{n-1}` sections forming a basis after every affine base change
into an open `V ⊆ B₀` (`Stacks.RigidifiedPicard.IsSectionBasis`). Over an affine `T` mapping into
`V`, the effective Cartier divisors on `X_T` meeting every fibre in a divisor and of the class of
the pullback of `L₀` are exactly the zero schemes of the sections `∑ cᵢ eᵢ` with `cᵢ` without
common zero, and two such sections have the same zero scheme exactly when their coefficients differ
by a unit of `Γ(T, 𝒪)`. This is the local form of "a divisor of class `L` is the zero scheme of a
section of `L`, well defined up to a unit" in the proof of [Stacks, Tag 0BA0] (5).

## Main results

* `Stacks.RigidifiedPicard.exists_abelSection_zeroScheme_eq`: every such divisor is a zero scheme
  of some `∑ cᵢ eᵢ`.
* `Stacks.RigidifiedPicard.exists_unit_of_zeroScheme_abelSection_eq`: the coefficients are unique
  up to a unit.
* `Stacks.RigidifiedPicard.zeroScheme_abelSection_comp`: compatibility with base change.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {n : ℕ} (e : Fin n → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ e V)

/-- `∑ (u cᵢ) eᵢ = u · ∑ cᵢ eᵢ`. -/
theorem abelSection_smul {T : Over (Spec (.of k))} (v : T ⟶ B₀) (c : Fin n → Γ(T.left, ⊤))
    (a : Γ(T.left, ⊤)) :
    abelSection f L₀ e v (fun i => a * c i) =
      ((bcProj f T).appTop a : Γ(bc f T, ⊤)) • abelSection f L₀ e v c := by
  rw [abelSection, abelSection, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_smul]

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

open Stacks.Picard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {n : ℕ} (e : Fin n → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ e V)

/-- The Stacks-style invertibility of `L₀` gives the `AlgebraicGeometry` one. -/
private theorem isInvertible_sheaf_of_stacks
    (f : X ⟶ Spec (.of k)) {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
    (hL₀ : Stacks.SheafOfModules.IsInvertible
      (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀) :
    SheafOfModules.IsInvertible (bc f B₀).sheaf.obj (bc f B₀).ringCatSheaf.property L₀ :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hL₀

/-- The pullback of `L₀` along `bcMap f v` is invertible in the `AlgebraicGeometry` sense. -/
private theorem isInvertible_sheaf_pullback
    (f : X ⟶ Spec (.of k)) {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
    (hL₀ : Stacks.SheafOfModules.IsInvertible
      (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀) {T : Over (Spec (.of k))} (v : T ⟶ B₀) :
    SheafOfModules.IsInvertible (bc f T).sheaf.obj (bc f T).ringCatSheaf.property
      ((Scheme.Modules.pullback (bcMap f v)).obj L₀) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
    (Stacks.RingedSpace.modulePullback_isInvertible_of (bcMap f v).toLRSHom.toShHom L₀ hL₀)

include hbasis in
/-- **A divisor of the class of `v^*L₀` is the zero scheme of some `∑ cᵢ eᵢ`**, the `cᵢ` having no
common zero, over an affine `T` mapping into `V`. -/
theorem exists_abelSection_zeroScheme_eq {T : Over (Spec (.of k))} [IsAffine T.left]
    (v : T ⟶ B₀) (hv : Set.range v.left ⊆ V) (D : (bc f T).IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hfib : ∀ t, Stacks.Divisors.IsEffectiveCartierDivisor (D.comap ((bcProj f T).fiberι t)))
    (hne : ∀ t : T.left, Nonempty ((bcProj f T).fiber t))
    (hcl : Stacks.Divisors.picardClass D = schemePullbackClass (bcMap f v)
      (Stacks.SheafOfModules.picardClass (bc f B₀).presheaf
        (Stacks.RingedSpace.structureIsSheaf (bc f B₀).toRingedSpace) L₀ hL₀)) :
    ∃ c : Fin n → Γ(T.left, ⊤), (∀ t, ∃ i, t ∈ T.left.basicOpen (c i)) ∧
      haveI : SheafOfModules.IsInvertible (bc f B₀).sheaf.obj (bc f B₀).ringCatSheaf.property L₀ :=
        (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
          _ _ _).mp hL₀
      Stacks.Divisors.zeroScheme (bc f T) _ (abelSection f L₀ e v c) = D := by
  have := isInvertible_sheaf_of_stacks f L₀ hL₀
  set M := (Scheme.Modules.pullback (bcMap f v)).obj L₀
  have hM := Stacks.RingedSpace.modulePullback_isInvertible_of (bcMap f v).toLRSHom.toShHom L₀ hL₀
  have := isInvertible_sheaf_pullback f L₀ hL₀ v
  have hclM : Stacks.Divisors.picardClass D = Stacks.SheafOfModules.picardClass (bc f T).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f T).toRingedSpace) M hM :=
    hcl.trans (pullbackClass_classOf (bcMap f v).toLRSHom.toShHom L₀ hL₀)
  obtain ⟨φ⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard D) hM).1 hclM
  obtain ⟨s, -, hsZ⟩ := exists_isRegularSection_zeroScheme_eq D M φ
  obtain ⟨c, hc⟩ := (hbasis v.left hv (bcProj f T) (bcMap f v) (bcMap_isPullback_proj f v)).2
    (s.eval (op ⊤))
  have hcs : abelSection f L₀ e v c = s.eval (op ⊤) := hc
  refine ⟨c, fun t => ?_, hcs ▸ hsZ⟩
  by_contra h
  push Not at h
  have hne0 : pullbackGlobalSections ((bcProj f T).fiberι t) M (s.eval (op ⊤)) ≠ 0 := by
    have := hne t
    refine Stacks.Divisors.ne_zero_of_isEffectiveCartierDivisor_zeroScheme _ _ ?_
    convert hfib t using 2
    exact (Stacks.Divisors.zeroScheme_pullback _ M _).trans
      (congrArg (fun I : (bc f T).IdealSheafData => I.comap ((bcProj f T).fiberι t)) hsZ)
  apply hne0
  rw [← hcs]
  have hsum := pullbackComp_app_pullbackGlobalSections_abelSection f L₀ e v c
    ((bcProj f T).fiberι t) ((bcProj f T).fiberToSpecResidueField t) (T.left.fromSpecResidueField t)
    (IsPullback.of_hasPullback _ _).w
  have hzero : ∀ i, (T.left.fromSpecResidueField t).appTop (c i) = 0 := fun i =>
    (appTop_fromSpecResidueField_eq_zero_iff t (c i)).2 (h i)
  simp only [hzero, map_zero, zero_smul, Finset.sum_const_zero] at hsum
  have hinj : Function.Injective (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackComp ((bcProj f T).fiberι t) (bcMap f v)).hom.app L₀) ⊤) :=
    Function.LeftInverse.injective (Scheme.Modules.app_inv_app
      ((Scheme.Modules.pullbackComp ((bcProj f T).fiberι t) (bcMap f v)).app L₀) ⊤)
  exact hinj (hsum.trans (map_zero _).symm)

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

open Stacks.Picard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {n : ℕ} (e : Fin n → Γ(L₀, ⊤)) {V : B₀.left.Opens} (hbasis : IsSectionBasis f L₀ e V)

/-- Functions without common zero on an affine scheme span the unit ideal. -/
theorem span_range_eq_top_of_forall_mem_basicOpen {T : Scheme.{u}} [IsAffine T]
    (c : Fin n → Γ(T, ⊤)) (hc : ∀ t, ∃ i, t ∈ T.basicOpen (c i)) :
    Ideal.span (Set.range c) = ⊤ := by
  refine ((isAffineOpen_top T).iSup_basicOpen_eq_self_iff (s := Set.range c)).1 ?_
  refine top_unique fun t _ => ?_
  obtain ⟨i, hi⟩ := hc t
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨c i, i, rfl⟩, hi⟩

/-- An element `b` fixing every member of a family generating the unit ideal is `1`. -/
theorem eq_one_of_forall_mul_eq_self_of_span_eq_top {R ι : Type*} [CommRing R] {c : ι → R}
    (hc : Ideal.span (Set.range c) = ⊤) {b : R} (h : ∀ i, b * c i = c i) : b = 1 := by
  have hker : ∀ x ∈ Ideal.span (Set.range c), (b - 1) * x = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      rw [sub_mul, one_mul, h, sub_self]
    · exact mul_zero _
    · intro x y _ _ hx hy
      rw [mul_add, hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  simpa [sub_eq_zero] using hker 1 (hc ▸ Submodule.mem_top)

include hL₀ hbasis in
/-- **`∑ cᵢ eᵢ` is a regular section** when the `cᵢ` have no common zero. -/
theorem isRegularSection_abelSection {T : Over (Spec (.of k))} (v : T ⟶ B₀)
    (hv : Set.range v.left ⊆ V) (c : Fin n → Γ(T.left, ⊤))
    (hc : ∀ t, ∃ i, t ∈ T.left.basicOpen (c i)) :
    IsRegularSection (bc f T).sheaf.obj (bc f T).ringCatSheaf.property
      (Stacks.Divisors.sectionsOfTop _ (abelSection f L₀ e v c)) := by
  have := isInvertible_sheaf_of_stacks f L₀ hL₀
  have := isInvertible_sheaf_pullback f L₀ hL₀ v
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : SmoothOfRelativeDimension 1 (bcProj f T) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f T.hom) inferInstance
  refine (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection _ _ _).1 ?_
  rw [Stacks.Divisors.sectionsOfTop_eval_top]
  exact (isRelativeEffectiveCartierDivisor_zeroScheme_of_ne_zero (bcProj f T)
    (isIntegral_curveFibre f T) _ _
    (pullbackGlobalSections_fiberι_abelSection_ne_zero f L₀ e hbasis v hv c hc)).1

include hL₀ in
/-- **An endomorphism of the pullback of `L₀` to `X_T` acts on global sections by a function on
`T`**, for `T` affine. -/
theorem exists_app_top_eq_bcProj_appTop_smul {T : Over (Spec (.of k))} [IsAffine T.left]
    (v : T ⟶ B₀) (φ : (Scheme.Modules.pullback (bcMap f v)).obj L₀ ⟶
      (Scheme.Modules.pullback (bcMap f v)).obj L₀) :
    ∃ a : Γ(T.left, ⊤), ∀ s, φ.app ⊤ s = ((bcProj f T).appTop a : Γ(bc f T, ⊤)) • s := by
  have : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf
      (structureSheafRing (bc f T).toRingedSpace).property
      ((Scheme.Modules.pullback (bcMap f v)).obj L₀) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of (bcMap f v).toLRSHom.toShHom L₀ hL₀
  obtain ⟨r, hr⟩ := exists_app_top_eq_smul_of_isInvertible _ φ
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  have : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have := isIso_appTop_snd_of_geometricallyIntegral k f T.hom
    (IsPullback.of_hasPullback f T.hom)
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (bcProj f T).appTop).2 r
  exact ⟨a, hr⟩

include hbasis in
/-- **Two sections `∑ cᵢ eᵢ` with the same zero scheme differ by a unit of the base**, over an
affine `T` mapping into `V`. -/
theorem exists_unit_of_zeroScheme_abelSection_eq {T : Over (Spec (.of k))} [IsAffine T.left]
    (v : T ⟶ B₀) (hv : Set.range v.left ⊆ V) (c c' : Fin n → Γ(T.left, ⊤))
    (hc : ∀ t, ∃ i, t ∈ T.left.basicOpen (c i)) (hc' : ∀ t, ∃ i, t ∈ T.left.basicOpen (c' i))
    (h : haveI : SheafOfModules.IsInvertible (bc f B₀).sheaf.obj
          (bc f B₀).ringCatSheaf.property L₀ :=
        (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
          _ _ _).mp hL₀
      Stacks.Divisors.zeroScheme (bc f T) _ (abelSection f L₀ e v c) =
        Stacks.Divisors.zeroScheme (bc f T) _ (abelSection f L₀ e v c')) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ i, c' i = a * c i := by
  have := isInvertible_sheaf_of_stacks f L₀ hL₀
  set M := (Scheme.Modules.pullback (bcMap f v)).obj L₀
  have := isInvertible_sheaf_pullback f L₀ hL₀ v
  let P : RegularSectionPair (bc f T) :=
    ⟨M, inferInstance, _, isRegularSection_abelSection f L₀ hL₀ e hbasis v hv c hc⟩
  let Q : RegularSectionPair (bc f T) :=
    ⟨M, inferInstance, _, isRegularSection_abelSection f L₀ hL₀ e hbasis v hv c' hc'⟩
  have hz : P.zeroScheme = Q.zeroScheme := by
    show Stacks.Divisors.zeroScheme _ M
        ((Stacks.Divisors.sectionsOfTop M (abelSection f L₀ e v c)).eval (op ⊤)) =
      Stacks.Divisors.zeroScheme _ M
        ((Stacks.Divisors.sectionsOfTop M (abelSection f L₀ e v c')).eval (op ⊤))
    rwa [Stacks.Divisors.sectionsOfTop_eval_top, Stacks.Divisors.sectionsOfTop_eval_top]
  have hPQ : P.classOf = Q.classOf :=
    (effectiveCartierDivisor_equiv_regularSectionClass _).symm.injective (Subtype.ext hz)
  obtain ⟨β, hβ⟩ : P.IsIsomorphic Q := Quotient.exact hPQ
  have hβs := (Scheme.Modules.unitHomEquiv_symm_comp_eq_iff P.s Q.s β.hom).mp hβ
  have hβtop : Scheme.Modules.Hom.app β.hom ⊤ (abelSection f L₀ e v c) =
      abelSection f L₀ e v c' := by
    have := congrArg (fun z : M.sections => z.eval (op ⊤)) hβs
    change Scheme.Modules.Hom.app β.hom ⊤
      ((Stacks.Divisors.sectionsOfTop M (abelSection f L₀ e v c)).eval (op ⊤)) =
      (Stacks.Divisors.sectionsOfTop M (abelSection f L₀ e v c')).eval (op ⊤) at this
    rwa [Stacks.Divisors.sectionsOfTop_eval_top, Stacks.Divisors.sectionsOfTop_eval_top] at this
  obtain ⟨a, hr⟩ := exists_app_top_eq_bcProj_appTop_smul f L₀ hL₀ v β.hom
  obtain ⟨a', hr'⟩ := exists_app_top_eq_bcProj_appTop_smul f L₀ hL₀ v β.inv
  have hinj := (hbasis v.left hv (bcProj f T) (bcMap f v) (bcMap_isPullback_proj f v)).1
  have hc'eq : c' = fun i => a * c i := by
    refine hinj ?_
    show abelSection f L₀ e v c' = abelSection f L₀ e v (fun i => a * c i)
    rw [abelSection_smul, ← hβtop, hr]
  have hceq : c = fun i => a' * c' i := by
    refine hinj ?_
    show abelSection f L₀ e v c = abelSection f L₀ e v (fun i => a' * c' i)
    rw [abelSection_smul, ← hr', ← hβtop, Scheme.Modules.app_inv_app]
  have hone : a' * a = 1 := eq_one_of_forall_mul_eq_self_of_span_eq_top
    (span_range_eq_top_of_forall_mem_basicOpen c hc) fun i => by
      have hi := congrFun hceq i
      rw [hc'eq] at hi
      exact (mul_assoc a' a (c i)).trans hi.symm
  exact ⟨⟨a, a', (mul_comm a a').trans hone, hone⟩, congrFun hc'eq⟩

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

open Stacks.Picard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  {B₀ : Over (Spec (.of k))} (L₀ : (bc f B₀).Modules)
  (hL₀ : Stacks.SheafOfModules.IsInvertible (bc f B₀).presheaf (bc f B₀).ringCatSheaf.2 L₀)
  {n : ℕ} (e : Fin n → Γ(L₀, ⊤))

include hL₀ in
/-- **Base change of the zero scheme of `∑ cᵢ eᵢ`.** Along `a : T' ⟶ T`, the inverse image of the
zero scheme of `∑ cᵢ eᵢ` is the zero scheme of `∑ a^*cᵢ eᵢ`. -/
theorem zeroScheme_abelSection_comp {T T' : Over (Spec (.of k))} (a : T' ⟶ T) (v : T ⟶ B₀)
    (c : Fin n → Γ(T.left, ⊤)) :
    haveI : SheafOfModules.IsInvertible (bc f B₀).sheaf.obj (bc f B₀).ringCatSheaf.property L₀ :=
      (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        _ _ _).mp hL₀
    Stacks.Divisors.zeroScheme (bc f T') _ (abelSection f L₀ e (a ≫ v)
        (fun i => a.left.appTop (c i))) =
      (Stacks.Divisors.zeroScheme (bc f T) _ (abelSection f L₀ e v c)).comap (bcMap f a) := by
  have hLa : SheafOfModules.IsInvertible (bc f B₀).sheaf.obj (bc f B₀).ringCatSheaf.property L₀ :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hL₀
  have : SheafOfModules.IsInvertible (bc f T').sheaf.obj (bc f T').ringCatSheaf.property
      ((Scheme.Modules.pullback (bcMap f v) ⋙ Scheme.Modules.pullback (bcMap f a)).obj L₀) :=
    inferInstanceAs (SheafOfModules.IsInvertible (bc f T').sheaf.obj
      (bc f T').ringCatSheaf.property
      ((Scheme.Modules.pullback (bcMap f a)).obj ((Scheme.Modules.pullback (bcMap f v)).obj L₀)))
  have key : ∀ (b₁ b₂ : bc f T' ⟶ bc f B₀) (_ : b₁ = b₂),
      Stacks.Divisors.zeroScheme (bc f T') ((Scheme.Modules.pullback b₁).obj L₀)
        (∑ i, ((bcProj f T').appTop (a.left.appTop (c i)) : Γ(bc f T', ⊤)) •
          pullbackGlobalSections b₁ L₀ (e i)) =
      Stacks.Divisors.zeroScheme (bc f T') ((Scheme.Modules.pullback b₂).obj L₀)
        (∑ i, ((bcProj f T').appTop (a.left.appTop (c i)) : Γ(bc f T', ⊤)) •
          pullbackGlobalSections b₂ L₀ (e i)) := by
    rintro _ _ rfl
    rfl
  refine (key _ _ (bcMap_comp f a v)).trans ?_
  refine Eq.trans ?_ (Stacks.Divisors.zeroScheme_pullback (bcMap f a) _ _)
  refine Eq.trans ?_ (Stacks.Divisors.zeroScheme_congr_iso
    ((Scheme.Modules.pullbackComp (bcMap f a) (bcMap f v)).app L₀) _)
  exact congrArg _ (pullbackComp_app_pullbackGlobalSections_abelSection f L₀ e v c (bcMap f a)
    (bcProj f T') a.left (bcMap_snd f a)).symm

end Stacks.RigidifiedPicard

end
