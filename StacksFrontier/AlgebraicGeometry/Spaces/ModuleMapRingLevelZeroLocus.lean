module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineLimitBaseChangedModuleDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociLimitPreserving

/-!
# The vanishing locus of an affine situation, read on rings

In the situation of Stacks 083F, suppose the vanishing of the base change of `u` at a test
scheme `T` is the vanishing of the base change of one fixed map of modules `v : M ⟶ N` to the
ring `A ⊗_{Rv} 𝒪(T)`. Then vanishing of the base change of `u` descends along limits of affine
test schemes.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.RingLevelZeroLocus` is the ring-level reading of
  the vanishing locus, as data: a base ring, a functorial family of algebra structures on the
  rings of functions of the test schemes, and a map of modules over a further algebra whose base
  change detects vanishing at every affine test scheme.

## Main results

* `Space.ModuleMapSituation.descendsAlongAffineLimits_isZeroAt_of_ringLevelZeroLocus`:
  a situation with a ring-level reading of its vanishing locus has vanishing descending along
  limits of affine test schemes.

## References

* [Stacks Project, Tag 083J](https://stacks.math.columbia.edu/tag/083J)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
* [Stacks Project, Tag 01YW](https://stacks.math.columbia.edu/tag/01YW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The ring-level reading of the vanishing locus of a situation of Stacks 083F.**

The data of a base ring `base`, an algebra structure on the ring of functions of every test
scheme over it, functorially in the test scheme, a further `base`-algebra `chart`, a finite
`chart`-module `source`, a `chart`-module `target` and a `chart`-linear map `map` between them,
such that for every affine test scheme `T` the base change of `u` vanishes at `T` exactly when
the base change of `map` to `chart ⊗_{base} 𝒪(T)` vanishes. -/
structure RingLevelZeroLocus (D : ModuleMapSituation.{u, u} B S hS) where
  /-- The ring over which the rings of functions of the test schemes are algebras. -/
  base : Type u
  [commRing_base : CommRing base]
  /-- The ring of functions of each test scheme, as an algebra over the base ring. -/
  algebra_sections : ∀ T : D.SchemesOver,
    Algebra base (Γ(D.testScheme.obj T, ⊤) : Type u)
  /-- The algebra structures are functorial: a morphism of test schemes acts on functions by a
  map of algebras over the base ring. -/
  algebraMap_sections : ∀ (T T' : D.SchemesOver) (k : T ⟶ T') (r : base),
    (D.testScheme.map k).appTop.hom
        (@algebraMap base (Γ(D.testScheme.obj T', ⊤) : Type u) _ _ (algebra_sections T') r) =
      @algebraMap base (Γ(D.testScheme.obj T, ⊤) : Type u) _ _ (algebra_sections T) r
  /-- The ring the two modules live on. -/
  chart : Type u
  [commRing_chart : CommRing chart]
  [algebra_chart : Algebra base chart]
  /-- The source module. -/
  source : Type u
  [addCommGroup_source : AddCommGroup source]
  [module_source : Module chart source]
  /-- The source module is finite. -/
  [finite_source : Module.Finite chart source]
  /-- The target module. -/
  target : Type u
  [addCommGroup_target : AddCommGroup target]
  [module_target : Module chart target]
  /-- The map of modules. -/
  map : source →ₗ[chart] target
  /-- Vanishing of the base change of `u` at an affine test scheme `T` is vanishing of the base
  change of `map` to `chart ⊗_{base} 𝒪(T)`. -/
  zero_iff : ∀ T : D.SchemesOver, IsAffine (D.testScheme.obj T) →
    (D.IsZeroAt (modulePullbackSystem B S hS) T ↔
      letI := algebra_sections T
      LinearMap.baseChange (chart ⊗[base] (Γ(D.testScheme.obj T, ⊤) : Type u)) map = 0)

/-- **Vanishing descends along limits of affine test schemes as soon as it has a ring-level
reading.** -/
theorem descendsAlongAffineLimits_isZeroAt_of_ringLevelZeroLocus
    (D : ModuleMapSituation.{u, u} B S hS) (hD : Nonempty (D.RingLevelZeroLocus)) :
    D.DescendsAlongAffineLimits.{u, u, u, u} (D.IsZeroAt (modulePullbackSystem B S hS)) := by
  obtain ⟨Q⟩ := hD
  let := Q.commRing_base
  let := Q.commRing_chart
  let := Q.algebra_chart
  let := Q.addCommGroup_source
  let := Q.module_source
  let := Q.addCommGroup_target
  let := Q.module_target
  intro I _ _ E c hc hE hpt hzero
  obtain ⟨α, _, _, _, F, _⟩ := CategoryTheory.IsFiltered.exists_directed_final Iᵒᵖ
  have hc' : IsLimit ((D.testScheme.mapCone c).whisker F.leftOp) :=
    (Functor.Initial.isLimitWhiskerEquiv F.leftOp (D.testScheme.mapCone c)).symm hc
  have : ∀ a : αᵒᵖ, IsAffine ((F.leftOp ⋙ E ⋙ D.testScheme).obj a) := fun a ↦ hE _
  let : ∀ a : α, Algebra Q.base
      (Γ((F.leftOp ⋙ E ⋙ D.testScheme).obj (op a), ⊤) : Type u) := fun a ↦
    Q.algebra_sections (E.obj (F.leftOp.obj (op a)))
  let : Algebra Q.base (Γ(((D.testScheme.mapCone c).whisker F.leftOp).pt, ⊤) : Type u) :=
    Q.algebra_sections c.pt
  obtain ⟨a, ha⟩ := exists_baseChange_eq_zero_of_isAffine_of_isLimit_of_directed
    (F.leftOp ⋙ E ⋙ D.testScheme) ((D.testScheme.mapCone c).whisker F.leftOp) hc'
    (fun a b h r ↦ Q.algebraMap_sections (E.obj (F.leftOp.obj (op b)))
      (E.obj (F.leftOp.obj (op a))) (E.map (F.leftOp.map (homOfLE h).op)) r)
    (fun a r ↦ Q.algebraMap_sections c.pt (E.obj (F.leftOp.obj (op a)))
      (c.π.app (F.leftOp.obj (op a))) r)
    (fun a b h x ↦ by
      have hw := ((D.testScheme.mapCone c).whisker F.leftOp).w ((homOfLE h).op)
      conv_rhs => rw [← hw]
      rfl)
    Q.finite_source Q.map ((Q.zero_iff c.pt hpt).mp hzero)
  exact ⟨F.leftOp.obj (op a),
    (Q.zero_iff (E.obj (F.leftOp.obj (op a))) (hE _)).mpr ha⟩

end ModuleMapSituation

end AlgebraicGeometry.Space

end
