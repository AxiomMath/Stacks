module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent

/-!
# Multiplication maps on prime-power torsion abelian sheaves

For an abelian sheaf `F` on a site and a natural number `l`, this file relates the exponent
condition `Stacks.Torsion.IsPrimePowerTorsion` to the multiplication maps `n • 𝟙 F`: a sheaf
killed by `l` is `l`-power torsion, and on an `l`-power torsion sheaf multiplication by an
integer prime to `l` is an isomorphism, since it is locally bijective.

## Main results

* `Stacks.Torsion.isPrimePowerTorsion_of_nsmul_id_eq_zero` — a sheaf killed by `l` is
  `l`-power torsion.
* `Stacks.Torsion.isIso_nsmul_id_of_isPrimePowerTorsion` — on an `l`-power torsion sheaf,
  multiplication by an integer prime to `l` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Multiplication by `n` on an abelian sheaf acts on sections as multiplication by `n`. -/
private theorem nsmul_id_hom_app_apply (n : ℕ) (F : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ)
    (x : ToType (F.obj.obj U)) : (n • 𝟙 F).hom.app U x = n • x := by
  have h1 : ((sheafToPresheaf J AddCommGrpCat.{w}).map (n • 𝟙 F)).app U = n • 𝟙 _ := by
    rw [Functor.map_nsmul, NatTrans.app_nsmul, CategoryTheory.Functor.map_id, NatTrans.id_app]
  exact (ConcreteCategory.congr_hom h1 x).trans (by simp)

/-- An abelian sheaf killed by `l`, that is with `l • 𝟙 F = 0`, is `l`-power torsion. -/
theorem isPrimePowerTorsion_of_nsmul_id_eq_zero {l : ℕ} {F : Sheaf J AddCommGrpCat.{w}}
    (hF : l • 𝟙 F = 0) : IsPrimePowerTorsion J l F := by
  intro U x
  refine ⟨⊤, J.top_mem U, fun V f _ ↦ ⟨1, one_pos, ?_⟩⟩
  have h := nsmul_id_hom_app_apply J l F (Opposite.op V) (F.obj.map f.op x)
  rw [hF] at h
  simpa using h.symm

/-- An element killed by a power of `l` is fixed by multiplication by `z * d` for some integer `z`,
whenever `d` is prime to `l`. -/
lemma exists_zsmul_mul_eq_self {A : Type*} [AddCommGroup A] {l d r : ℕ} (hd : d.Coprime l)
    {a : A} (hl : l ^ r • a = 0) : ∃ z : ℤ, (z * d) • a = a := by
  obtain ⟨z, y, hzy⟩ := (Nat.Coprime.pow_right r hd).isCoprime
  refine ⟨z, ?_⟩
  have : (z * d + y * (l ^ r : ℕ)) • a = a := by
    push_cast at hzy ⊢
    rw [hzy, one_smul]
  rwa [add_smul, mul_smul y, natCast_zsmul, hl, smul_zero, add_zero] at this

/-- On an `l`-power torsion sheaf with `d` prime to `l`, every section is locally fixed by
multiplication by `z * d` for some integer `z`. -/
private theorem exists_covering_zsmul_mul_eq {l d : ℕ} (hd : d.Coprime l)
    {F : Sheaf J AddCommGrpCat.{w}} (hF : IsPrimePowerTorsion J l F) {U : Cᵒᵖ}
    (s : ToType (F.obj.obj U)) : ∃ R ∈ J U.unop, ∀ ⦃V⦄ (g : V ⟶ U.unop), R g →
      ∃ z : ℤ, (z * d) • F.obj.map g.op s = F.obj.map g.op s := by
  obtain ⟨R, hR, hann⟩ := hF U.unop s
  refine ⟨R, hR, fun V g hg ↦ ?_⟩
  obtain ⟨r, -, hr⟩ := hann V g hg
  exact exists_zsmul_mul_eq_self hd hr

/-- **On an `l`-power torsion abelian sheaf, multiplication by an integer prime to `l` is an
isomorphism.** -/
theorem isIso_nsmul_id_of_isPrimePowerTorsion {l d : ℕ} (hd : d.Coprime l)
    {F : Sheaf J AddCommGrpCat.{w}} (hF : IsPrimePowerTorsion J l F) : IsIso (d • 𝟙 F) := by
  refine (Sheaf.isLocallyBijective_iff_isIso (d • 𝟙 F)).1 ⟨⟨fun {U} x y hxy ↦ ?_⟩, ⟨fun {U} s ↦ ?_⟩⟩
  · rw [nsmul_id_hom_app_apply, nsmul_id_hom_app_apply] at hxy
    obtain ⟨R, hR, hann⟩ := exists_covering_zsmul_mul_eq J hd hF (x - y)
    refine J.superset_covering (fun V g hg ↦ ?_) hR
    obtain ⟨z, hz⟩ := hann g hg
    have h0 : d • F.obj.map g.op (x - y) = 0 := by
      rw [← map_nsmul, smul_sub, hxy, sub_self, map_zero]
    rw [mul_smul, natCast_zsmul, h0, smul_zero] at hz
    change F.obj.map g.op x = F.obj.map g.op y
    rw [← sub_eq_zero, ← map_sub, ← hz]
  · obtain ⟨R, hR, hann⟩ := exists_covering_zsmul_mul_eq J hd hF s
    refine J.superset_covering (fun V g hg ↦ ?_) hR
    obtain ⟨z, hz⟩ := hann g hg
    refine ⟨z • F.obj.map g.op s, ?_⟩
    rw [nsmul_id_hom_app_apply, ← natCast_zsmul, smul_smul, mul_comm, hz]

end Stacks.Torsion

end
