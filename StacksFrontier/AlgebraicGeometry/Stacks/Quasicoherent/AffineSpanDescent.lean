module

public import StacksFrontier.Algebra.Module.FaithfullyFlat.SpanDescentPi
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FinitePresentationAffineSections

/-!
# Membership in the span of a restricted submodule is fppf local

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `ℱ` a quasi-coherent module
on its fppf site.  For an object `y` over an affine scheme, a submodule `N ⊆ ℱ(y)` and a section
`x ∈ ℱ(y)`: if `x` restricted to every member `z ⟶ y` over an affine scheme of an fppf covering
sieve lies in the `Γ(z)`-span of the restriction of `N`, then `x ∈ N`.

This is faithfully flat descent (Stacks 023M) for the quotient `ℱ(y) ⧸ N`: the covering contains
a finite family of affine objects which is fppf in schemes, the product of their rings is
faithfully flat over `Γ(y)`, and `ℱ` is cartesian between affine objects (Stacks 03DX).

## Main definitions

* `AlgebraicGeometry.FibredSite.restrictedSpan`: the `Γ(z)`-span of the restriction of a
  submodule along an arrow `z ⟶ y`.

## Main results

* `AlgebraicGeometry.FibredSite.mem_of_forall_mem_restrictedSpan`: the descent statement.
* `AlgebraicGeometry.FibredSite.restrictedSpan_comp`: the span along a composite.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}

attribute [local instance] objModule

/-- Restriction of sections along a composite. -/
theorem restrictₛₗ_comp_apply (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    {y z z' : 𝒳} (k : z ⟶ y) (k' : z' ⟶ z) (x : F.val.obj (op y)) :
    F.val.restrictₛₗ (k' ≫ k).op x = F.val.restrictₛₗ k'.op (F.val.restrictₛₗ k.op x) := by
  rw [op_comp]
  exact PresheafOfModules.map_comp_apply F.val k.op k'.op x

/-- Restriction of sections along an identity. -/
theorem restrictₛₗ_id_apply (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    {y : 𝒳} (x : F.val.obj (op y)) : F.val.restrictₛₗ (𝟙 y).op x = x := by
  rw [PresheafOfModules.restrictₛₗ_apply, op_id, PresheafOfModules.map_id]; rfl

/-- The `Γ(z)`-span of the restriction along `k : z ⟶ y` of a submodule `N` of `ℱ(y)`. -/
def restrictedSpan (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    {y z : 𝒳} (k : z ⟶ y) (N : Submodule (objRing B S hS p y) (F.val.obj (op y))) :
    Submodule (objRing B S hS p z) (F.val.obj (op z)) :=
  Submodule.span _ (F.val.restrictₛₗ k.op '' N)

/-- The restriction along `k : z ⟶ y` of an element of `N` lies in the span along `k`. -/
theorem map_mem_restrictedSpan (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    {y z : 𝒳} (k : z ⟶ y) {N : Submodule (objRing B S hS p y) (F.val.obj (op y))}
    {n : F.val.obj (op y)} (hn : n ∈ N) : F.val.restrictₛₗ k.op n ∈ restrictedSpan F k N :=
  Submodule.subset_span ⟨n, hn, rfl⟩

/-- The restriction along `k' : z' ⟶ z` of an element of the span along `k : z ⟶ y` lies in the
span along `k' ≫ k`. -/
theorem map_mem_restrictedSpan_comp
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    {y z z' : 𝒳} (k : z ⟶ y) (k' : z' ⟶ z) {N : Submodule (objRing B S hS p y) (F.val.obj (op y))}
    {m : F.val.obj (op z)} (hm : m ∈ restrictedSpan F k N) :
    F.val.restrictₛₗ k'.op m ∈ restrictedSpan F (k' ≫ k) N := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨n, hn, rfl⟩
    rw [← restrictₛₗ_comp_apply]
    exact map_mem_restrictedSpan F _ hn
  · rw [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
  · intro c a _ ha
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ ha

/-- The span along a composite is the span of the restriction of the span. -/
theorem restrictedSpan_comp (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    {y z z' : 𝒳} (k : z ⟶ y) (k' : z' ⟶ z)
    (N : Submodule (objRing B S hS p y) (F.val.obj (op y))) :
    restrictedSpan F (k' ≫ k) N = restrictedSpan F k' (restrictedSpan F k N) := by
  refine le_antisymm ?_ ?_
  · rw [restrictedSpan, Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    rw [restrictₛₗ_comp_apply]
    exact map_mem_restrictedSpan F k' (map_mem_restrictedSpan F k hn)
  · conv_lhs => rw [restrictedSpan]
    rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    exact map_mem_restrictedSpan_comp F k k' hm

include hp in
/-- **Sections over an affine object are spanned by restrictions** along any arrow to an affine
object, for a quasi-coherent module: the comparison `Γ(z) ⊗ ℱ(y) ⟶ ℱ(z)` is surjective. -/
theorem mem_span_range_restrictₛₗ
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : F.IsQuasicoherentOnSite) {y z : 𝒳} (k : z ⟶ y) (hy : IsAffineOver B S hS (p.obj y))
    (hz : IsAffineOver B S hS (p.obj z)) (x : F.val.obj (op z)) :
    x ∈ Submodule.span (objRing B S hS p z) (Set.range (F.val.restrictₛₗ k.op)) := by
  let := objAlgebra B S hS p k
  let : Module (objRing B S hS p y) (F.val.obj (op z)) :=
    Module.compHom _ (algebraMap (objRing B S hS p y) (objRing B S hS p z))
  have : IsScalarTower (objRing B S hS p y) (objRing B S hS p z) (F.val.obj (op z)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨t, rfl⟩ := (bijective_liftBaseChange_of_eq_restriction F hF k hy hz
    (restrictionLinear F k) fun _ => rfl).2 x
  induction t using TensorProduct.inductionOn with
  | tmul c m =>
    rw [LinearMap.liftBaseChange_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

include hp in
/-- **Membership in the span of a restricted submodule is fppf local.**  Let `ℱ` be
quasi-coherent, `y` an object over an affine scheme, `N ⊆ ℱ(y)` a submodule and `x ∈ ℱ(y)`.  If
for an fppf covering sieve of `y` the restriction of `x` to each member `z ⟶ y` over an affine
scheme lies in the span of the restriction of `N`, then `x ∈ N`. -/
theorem mem_of_forall_mem_restrictedSpan
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : F.IsQuasicoherentOnSite) {y : 𝒳} (hy : IsAffineOver B S hS (p.obj y))
    (N : Submodule (objRing B S hS p y) (F.val.obj (op y))) {Sv : Sieve y}
    (hSv : Sv ∈ BigFppfOver.associatedTopology B S hS p .fppf y) {x : F.val.obj (op y)}
    (hx : ∀ ⦃z : 𝒳⦄ (k : z ⟶ y), Sv k → IsAffineOver B S hS (p.obj z) →
      F.val.restrictₛₗ k.op x ∈ restrictedSpan F k N) :
    x ∈ N := by
  obtain ⟨n, z, φ, hzaff, hmem, -, hfppf⟩ :=
    exists_finite_affine_fppf_ofArrows_le B S hS p hp hy hSv
  let : ∀ i, Algebra (objRing B S hS p y) (objRing B S hS p (z i)) := fun i =>
    objAlgebra B S hS p (φ i)
  let : ∀ i, Module (objRing B S hS p y) (F.val.obj (op (z i))) := fun i =>
    Module.compHom _ (algebraMap (objRing B S hS p y) (objRing B S hS p (z i)))
  have : ∀ i, IsScalarTower (objRing B S hS p y) (objRing B S hS p (z i))
      (F.val.obj (op (z i))) := fun i => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) := hy
  have : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (z i))) := hzaff
  have : Module.FaithfullyFlat (objRing B S hS p y) (∀ i, objRing B S hS p (z i)) :=
    _root_.AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage
      (fun i => (BigFppfOver.toScheme B S hS).map (p.map (φ i))) hfppf fun _ => rfl
  exact Submodule.mem_of_forall_mem_span_image_of_bijective_liftBaseChange_pi
    (objRing B S hS p y) (fun i => objRing B S hS p (z i))
    (fun i => restrictionLinear F (φ i))
    (fun i => bijective_liftBaseChange_of_eq_restriction F hF (φ i) hy (hzaff i) _ fun _ => rfl)
    N (fun i => hx (φ i) (hmem i) (hzaff i))

end AlgebraicGeometry.FibredSite

end
