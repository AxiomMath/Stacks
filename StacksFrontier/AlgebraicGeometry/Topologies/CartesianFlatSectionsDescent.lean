module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineGeneratedRelations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceSums
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# Faithfully flat descent of spans of sections, for a cartesian presheaf of modules

Let `R` be a presheaf of commutative rings on a category `C` and `M` a presheaf of modules over
the underlying presheaf of rings.  A finite family of arrows `φ i : z i ⟶ W` whose restriction
maps on rings are *jointly faithfully flat* — the product `R W ⟶ ∏ R (z i)` is a faithfully flat
ring map — detects membership in a span of sections over `W`, provided `M` is cartesian over
each `φ i`, that is, provided each base-change comparison

`R (z i) ⊗_{R W} M W ⟶ M (z i)`

of `Stacks.PresheafOfModules.restrictionBaseChange` is injective.

## Main results

* `Stacks.PresheafOfModules.isScalarTower_moduleOfRingHom`: the two scalar actions on the
  sections over the source of an arrow are compatible.
* `Stacks.PresheafOfModules.liftBaseChange_restrictionLinear_eq`: the base-change comparison of
  `Stacks.PresheafOfModules.restrictionBaseChange` is the `LinearMap.liftBaseChange` of the
  restriction map `Stacks.PresheafOfModules.restrictionLinear`.
* `Stacks.PresheafOfModules.injective_liftBaseChange_restrictionLinear`: hence the cartesian
  condition, stated for `restrictionBaseChange`, implies injectivity of that lift.
* `Stacks.PresheafOfModules.mem_span_of_forall_restrict_mem_span`: **membership in the span of a
  finite family of sections descends along a jointly faithfully flat finite family of arrows over
  which the presheaf is cartesian.**
* `Stacks.PresheafOfModules.HasFlatCartesianRefinement`: the hypothesis on an object that every
  covering sieve of it contains such a family.
* `Stacks.PresheafOfModules.span_eq_top_of_generates` and
  `Stacks.PresheafOfModules.module_finite_sections_of_generates`: at such an object, finitely
  many sections which generate the module only locally already span the sections there.
* `Stacks.PresheafOfModules.module_finite_sections_of_locally_generates`: **at such an object,
  finitely many sections generating the module on the members of a covering of it already make
  the sections over the object itself a finite module.**

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v r m

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))

/-- The action of the ring of sections at the base on the sections over the source of an arrow,
through `Stacks.PresheafOfModules.moduleOfRingHom`, is compatible with the action of the ring of
sections there. -/
theorem isScalarTower_moduleOfRingHom {W X : C} (a : X ⟶ W) :
    letI := algebraOfRingHom (R := R) (R.map a.op)
    letI := moduleOfRingHom M (R.map a.op)
    IsScalarTower (R.obj (op W)) (R.obj (op X)) (M.obj (op X)) :=
  let := algebraOfRingHom (R := R) (R.map a.op)
  let := moduleOfRingHom M (R.map a.op)
  ⟨fun _ _ _ => mul_smul _ _ _⟩

/-- The base-change comparison of `Stacks.PresheafOfModules.restrictionBaseChange`, read as a
linear map out of the tensor product of the rings and sections, over the algebra structure
`Stacks.PresheafOfModules.algebraOfRingHom`. -/
noncomputable abbrev restrictionBaseChangeLinear {W X : C} (a : X ⟶ W) :
    letI := algebraOfRingHom (R := R) (R.map a.op)
    R.obj (op X) ⊗[R.obj (op W)] M.obj (op W) →ₗ[R.obj (op X)] M.obj (op X) :=
  letI := algebraOfRingHom (R := R) (R.map a.op)
  (restrictionBaseChange M a.op).hom

/-- `Stacks.PresheafOfModules.restrictionBaseChangeLinear` on a pure tensor. -/
theorem restrictionBaseChangeLinear_tmul {W X : C} (a : X ⟶ W) (b : R.obj (op X))
    (x : M.obj (op W)) :
    letI := algebraOfRingHom (R := R) (R.map a.op)
    restrictionBaseChangeLinear M a (b ⊗ₜ x) = b • (M.map a.op x : M.obj (op X)) :=
  restrictionBaseChange_tmul M a.op b x

/-- **The base-change comparison is the `LinearMap.liftBaseChange` of the restriction map.** -/
theorem liftBaseChange_restrictionLinear_eq {W X : C} (a : X ⟶ W) :
    letI := algebraOfRingHom (R := R) (R.map a.op)
    letI := moduleOfRingHom M (R.map a.op)
    haveI := isScalarTower_moduleOfRingHom M a
    (restrictionLinear M a).liftBaseChange (R.obj (op X)) =
      restrictionBaseChangeLinear M a := by
  let := algebraOfRingHom (R := R) (R.map a.op)
  let := moduleOfRingHom M (R.map a.op)
  have := isScalarTower_moduleOfRingHom M a
  refine LinearMap.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul b x =>
      rw [LinearMap.liftBaseChange_tmul, restrictionLinear_apply,
        restrictionBaseChangeLinear_tmul]
      rfl
  | add p q hp hq => rw [map_add, map_add, hp, hq]

/-- A presheaf of modules cartesian over an arrow, in the sense that the base-change comparison
`Stacks.PresheafOfModules.restrictionBaseChange` is injective, has an injective
`LinearMap.liftBaseChange` of the restriction map. -/
theorem injective_liftBaseChange_restrictionLinear {W X : C} (a : X ⟶ W)
    (h : Function.Injective (restrictionBaseChange M a.op)) :
    letI := algebraOfRingHom (R := R) (R.map a.op)
    letI := moduleOfRingHom M (R.map a.op)
    haveI := isScalarTower_moduleOfRingHom M a
    Function.Injective ((restrictionLinear M a).liftBaseChange (R.obj (op X))) := by
  let := algebraOfRingHom (R := R) (R.map a.op)
  let := moduleOfRingHom M (R.map a.op)
  have := isScalarTower_moduleOfRingHom M a
  rwa [liftBaseChange_restrictionLinear_eq M a]

/-- **Membership in a span of sections descends along a jointly faithfully flat finite family of
arrows over which the presheaf of modules is cartesian.**  A section over the base which, over
each member of the family, lies in the span of the restrictions of a finite family of sections
over the base, lies in their span over the base itself. -/
theorem mem_span_of_forall_restrict_mem_span
    {W : C} {n : ℕ} {z : Fin n → C} (φ : ∀ i, z i ⟶ W)
    (hff : (RingHom.pi fun i => (R.map (φ i).op).hom).FaithfullyFlat)
    (hcart : ∀ i, Function.Injective (restrictionBaseChange M (φ i).op))
    {κ : Type*} [Finite κ] (τ : κ → M.obj (op W)) {x : M.obj (op W)}
    (hx : ∀ i, M.map (φ i).op x ∈
      Submodule.span (R.obj (op (z i))) (Set.range fun l => M.map (φ i).op (τ l))) :
    x ∈ Submodule.span (R.obj (op W)) (Set.range τ) := by
  classical
  let fκ : Fintype κ := Fintype.ofFinite κ
  let algI : ∀ i, Algebra (R.obj (op W)) (R.obj (op (z i))) :=
    fun i => algebraOfRingHom (R := R) (R.map (φ i).op)
  let modI : ∀ i, Module (R.obj (op W)) (M.obj (op (z i))) :=
    fun i => moduleOfRingHom M (R.map (φ i).op)
  have towI : ∀ i, IsScalarTower (R.obj (op W)) (R.obj (op (z i))) (M.obj (op (z i))) :=
    fun i => isScalarTower_moduleOfRingHom M (φ i)
  have towP : ∀ i, IsScalarTower (R.obj (op W)) (R.obj (op (z i)))
      (κ → R.obj (op (z i))) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hFF : Module.FaithfullyFlat (R.obj (op W)) (∀ i, R.obj (op (z i))) := hff
  let rP : ∀ i, (κ → R.obj (op W)) →ₗ[R.obj (op W)] (κ → R.obj (op (z i))) :=
    fun _ => (Algebra.linearMap _ _).compLeft κ
  let rN : ∀ i, M.obj (op W) →ₗ[R.obj (op W)] M.obj (op (z i)) :=
    fun i => restrictionLinear M (φ i)
  let bT := Fintype.linearCombination (R.obj (op W)) τ
  let bW : ∀ i, (κ → R.obj (op (z i))) →ₗ[R.obj (op (z i))] M.obj (op (z i)) :=
    fun i => Fintype.linearCombination _ fun l => rN i (τ l)
  have hsq : ∀ (i) (q : κ → R.obj (op W)), rN i (bT q) = bW i (rP i q) := by
    intro i q
    show rN i (Fintype.linearCombination _ τ q) = Fintype.linearCombination _ _ (rP i q)
    rw [Fintype.linearCombination_apply, map_sum, Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun l _ => map_smul (rN i) (q l) (τ l)
  have hP : ∀ i, Function.Surjective ((rP i).liftBaseChange (R.obj (op (z i)))) := by
    intro i
    refine (Module.BaseChange.bijective_liftBaseChange_of_basis
      (Pi.basisFun (R.obj (op W)) κ) (Pi.basisFun (R.obj (op (z i))) κ) (rP i)
      fun l => funext fun j => ?_).2
    show algebraMap (R.obj (op W)) (R.obj (op (z i)))
        (Pi.basisFun (R.obj (op W)) κ l j) = Pi.basisFun (R.obj (op (z i))) κ l j
    rw [Pi.basisFun_apply, Pi.basisFun_apply]
    by_cases h : j = l
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]
  have hN : ∀ i, Function.Injective ((rN i).liftBaseChange (R.obj (op (z i)))) :=
    fun i => injective_liftBaseChange_restrictionLinear M (φ i) (hcart i)
  have hn : ∀ i, rN i x ∈ LinearMap.range (bW i) := by
    intro i
    show rN i x ∈ LinearMap.range (Fintype.linearCombination _ fun l => rN i (τ l))
    rw [Fintype.range_linearCombination]
    exact hx i
  have hmem := Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange
    (R.obj (op W)) (fun i => R.obj (op (z i))) bT bW rP rN hsq hP hN hn
  rwa [show LinearMap.range bT = Submodule.span (R.obj (op W)) (Set.range τ) from
    Fintype.range_linearCombination _ _] at hmem

/-! ### Local generation over an object with flat cartesian refinements -/

/-- **A flat cartesian refinement of the covering sieves of an object.**  `M` has one at `W`,
with members in `P`, when every covering sieve of `W` contains a finite family of arrows whose
sources satisfy `P`, whose restriction maps on rings are jointly faithfully flat, and over each
of which `M` is cartesian. -/
def HasFlatCartesianRefinement (J : GrothendieckTopology C)
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    (P : C → Prop) (W : C) : Prop :=
  ∀ T : Sieve W, T ∈ J W →
    ∃ (n : ℕ) (z : Fin n → C) (φ : ∀ i, z i ⟶ W),
      (∀ i, P (z i)) ∧ (∀ i, T (φ i)) ∧
        (RingHom.pi fun i => (R.map (φ i).op).hom).FaithfullyFlat ∧
        ∀ i, Function.Bijective (restrictionBaseChange M (φ i).op)

/-- A module spanned by the range of a finite family is finite. -/
private theorem finite_of_span_range_eq_top {A N : Type*} [Semiring A] [AddCommMonoid N]
    [Module A N] {ι : Type*} [Finite ι] (s : ι → N) (h : Submodule.span A (Set.range s) = ⊤) :
    Module.Finite A N :=
  ⟨h ▸ Submodule.fg_span (Set.finite_range s)⟩

/-- **Finitely many sections which generate only locally already span the sections over an object
carrying flat cartesian refinements.** -/
theorem span_eq_top_of_generates (J : GrothendieckTopology C)
    {P : C → Prop} {W : C} (h : HasFlatCartesianRefinement J M P W)
    {k : ℕ} (s : Fin k → M.obj (op W))
    (hs : _root_.PresheafOfModules.Generates J M s) :
    Submodule.span (R.obj (op W)) (Set.range s) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  obtain ⟨T, hT, hcomb⟩ := hs W (𝟙 W) x
  obtain ⟨n, z, φ, -, hzT, hff, hbij⟩ := h T hT
  refine mem_span_of_forall_restrict_mem_span M φ hff (fun i => (hbij i).1) s fun i => ?_
  obtain ⟨a, ha⟩ := hcomb (z i) (φ i) (hzT i)
  rw [Category.comp_id] at ha
  exact Submodule.mem_span_set'.2
    ⟨k, a, fun l => ⟨M.map (φ i).op (s l), ⟨l, rfl⟩⟩, ha⟩

/-- Finitely many sections which generate only locally make the sections over an object carrying
flat cartesian refinements a finite module over its ring of sections. -/
theorem module_finite_sections_of_generates (J : GrothendieckTopology C)
    {P : C → Prop} {W : C} (h : HasFlatCartesianRefinement J M P W)
    {k : ℕ} (s : Fin k → M.obj (op W))
    (hs : _root_.PresheafOfModules.Generates J M s) :
    Module.Finite (R.obj (op W)) (M.obj (op W)) := by
  exact finite_of_span_range_eq_top s (span_eq_top_of_generates M J h s hs)

/-! ### Finiteness of the sections of a locally finitely generated module -/

/-- **The sections of a module which is locally generated by finitely many sections over an
object carrying flat cartesian refinements form a finite module over its ring of sections.** -/
theorem module_finite_sections_of_locally_generates (J : GrothendieckTopology C)
    {P : C → Prop} (hP : ∀ V : C, P V → HasFlatCartesianRefinement J M P V)
    {W : C} (hW : HasFlatCartesianRefinement J M P W)
    {I : Type*} {V : I → C} {f : ∀ i, V i ⟶ W} (hcov : Sieve.ofArrows V f ∈ J W)
    (hgen : ∀ i, ∃ (k : ℕ) (s : Fin k → M.obj (op (V i))),
      _root_.PresheafOfModules.Generates J M s) :
    Module.Finite (R.obj (op W)) (M.obj (op W)) := by
  classical
  obtain ⟨n, z, φ, hzP, hzmem, hff, hbij⟩ := hW _ hcov
  have hfinz : ∀ i, ∃ (c : ℕ) (γ : Fin c → M.obj (op (z i))),
      Submodule.span (R.obj (op (z i))) (Set.range γ) = ⊤ := by
    intro i
    obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff V f (φ i)).1 (hzmem i)
    obtain ⟨_, σ, hσ⟩ := hgen j
    have hfin : Module.Finite (R.obj (op (z i))) (M.obj (op (z i))) :=
      module_finite_sections_of_generates M J (hP (z i) (hzP i)) _
        (_root_.Stacks.SheafOfModules.generates_restrict b σ hσ)
    exact Module.Finite.exists_fin
  choose c γ hγ using hfinz
  have hdec : ∀ (i : Fin n) (l : Fin (c i)), ∃ (kk : ℕ)
      (t : Fin kk → R.obj (op (z i))) (mm : Fin kk → M.obj (op W)),
      γ i l = ∑ p, t p • (M.map (φ i).op (mm p) : M.obj (op (z i))) := by
    intro i l
    let := algebraOfRingHom (R := R) (R.map (φ i).op)
    have hsurj : Function.Surjective (restrictionBaseChangeLinear M (φ i)) := (hbij i).2
    obtain ⟨ζ, hζ⟩ := hsurj (γ i l)
    obtain ⟨kk, t, mm, hmm⟩ := TensorProduct.exists_sum_tmul_eq ζ
    refine ⟨kk, t, mm, ?_⟩
    rw [← hζ, hmm, map_sum]
    exact Finset.sum_congr rfl fun p _ =>
      restrictionBaseChangeLinear_tmul M (φ i) (t p) (mm p)
  choose kk t mm hmm using hdec
  let τ : (Σ i : Fin n, Σ l : Fin (c i), Fin (kk i l)) → M.obj (op W) :=
    fun w => mm w.1 w.2.1 w.2.2
  have hsp : Submodule.span (R.obj (op W)) (Set.range τ) = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun x => ?_
    refine mem_span_of_forall_restrict_mem_span M φ hff (fun i => (hbij i).1) τ fun i => ?_
    refine Submodule.span_le.2 ?_ ((hγ i).ge Submodule.mem_top)
    rintro y ⟨l, rfl⟩
    exact Submodule.mem_span_set'.2
      ⟨kk i l, t i l, fun p => ⟨M.map (φ i).op (mm i l p), ⟨⟨i, l, p⟩, rfl⟩⟩, (hmm i l).symm⟩
  exact finite_of_span_range_eq_top τ hsp

end Stacks.PresheafOfModules

end
