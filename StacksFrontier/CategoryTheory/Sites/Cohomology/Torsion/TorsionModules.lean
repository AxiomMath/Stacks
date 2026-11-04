module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage

/-!
# Torsion sheaves of modules

Let `R` be a sheaf of rings on a site `(C, J)`. A sheaf of `R`-modules is *torsion* when its
underlying abelian sheaf is a torsion abelian sheaf in the sense of [Stacks, Tag 0DD7]: every
section is, on the members of some covering sieve, annihilated by a positive integer. This file
records the closure properties of that class.

## Main results

* `Stacks.Torsion.torsionModules_isSerreClass`: the torsion sheaves of modules form a Serre
  subcategory, being the preimage of the torsion abelian sheaves under the exact functor
  `SheafOfModules.toSheaf`.
* `Stacks.Torsion.torsionModules_of_jointlyEpi`: a sheaf of modules receiving a jointly
  epimorphic family of maps from torsion sheaves of modules is torsion.
* `Stacks.Torsion.torsionModules_sigma`: a coproduct of torsion sheaves of modules is torsion.

## Implementation notes

The closure under arbitrary coproducts is not a property of Serre classes. It is proved through
the subsheaf of locally torsion sections (`Stacks.Torsion.torsionSubmodule`): a map out of a
torsion sheaf of modules lands in it, so its cokernel is killed by every member of a jointly
epimorphic family of maps out of torsion sheaves, hence vanishes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Torsion

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The torsion sheaves of `R`-modules: those whose underlying abelian sheaf is a torsion
abelian sheaf. -/
abbrev torsionModules : ObjectProperty (SheafOfModules.{w} R) :=
  (torsionSheafProperty J).inverseImage (SheafOfModules.toSheaf R)

/-- The forgetful functor from sheaves of `R`-modules to abelian sheaves preserves finite
colimits. -/
instance : PreservesFiniteColimits (SheafOfModules.toSheaf.{w} R) :=
  ⟨fun _ _ _ => SheafOfModules.preservesColimitsOfShape_toSheaf R⟩

/-- **The torsion sheaves of modules form a Serre subcategory.** -/
instance torsionModules_isSerreClass : (torsionModules R).IsSerreClass :=
  inferInstance

variable {R}

section Presheaf

variable (J) {R₀ : Cᵒᵖ ⥤ RingCat.{w}}

/-- The locally torsion sections of a presheaf of modules over `U`: those whose torsion sieve
(`Stacks.Torsion.torsionSieve`) covers `U`. -/
def torsionSections (M : PresheafOfModules.{w} R₀) (U : Cᵒᵖ) : Submodule (R₀.obj U) (M.obj U) where
  carrier := {x | torsionSieve M.presheaf x ∈ J U.unop}
  add_mem' := by
    intro x y hx hy
    refine J.superset_covering ?_ (J.intersection_covering hx hy)
    rintro V f ⟨⟨n, hn, hx'⟩, ⟨m, hm, hy'⟩⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    change n • M.map f.op x = 0 at hx'
    change m • M.map f.op y = 0 at hy'
    change (n * m) • M.map f.op (x + y) = 0
    rw [map_add, smul_add, mul_comm, ← smul_smul, hx', smul_zero, mul_comm, ← smul_smul,
      hy', smul_zero, add_zero]
  zero_mem' := by
    refine J.superset_covering (fun V f _ => ⟨1, one_pos, ?_⟩) (J.top_mem _)
    change 1 • M.presheaf.map f.op (0 : M.presheaf.obj (op U.unop)) = 0
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro r x hx
    refine J.superset_covering ?_ hx
    rintro V f ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    change n • M.map f.op (r • x) = 0
    change n • M.map f.op x = 0 at h
    rw [PresheafOfModules.map_smul, smul_comm, h, smul_zero]

/-- A section lies in `torsionSections J M U` exactly when its torsion sieve covers `U`. -/
theorem mem_torsionSections_iff (M : PresheafOfModules.{w} R₀) (U : Cᵒᵖ) (x : M.obj U) :
    x ∈ torsionSections J M U ↔ torsionSieve M.presheaf x ∈ J U.unop :=
  Iff.rfl

/-- A presheaf of modules is locally torsion exactly when all its sections are locally torsion. -/
theorem isLocallyTorsion_toPresheaf_iff (M : PresheafOfModules.{w} R₀) :
    IsLocallyTorsion J ((PresheafOfModules.toPresheaf R₀).obj M) ↔
      ∀ (U : Cᵒᵖ) (x : M.obj U), x ∈ torsionSections J M U := by
  rw [isLocallyTorsion_iff_torsionSieve_mem]
  exact ⟨fun h U x => h U.unop x, fun h U x => h (op U) x⟩

end Presheaf

/-- **The locally torsion sections of a sheaf of modules**, as a subsheaf of modules. -/
def torsionSubmodule (M : SheafOfModules.{w} R) : M.Submodule where
  obj := torsionSections J M.val
  map {X Y} f x hx := by
    rw [Submodule.mem_comap, mem_torsionSections_iff]
    rw [mem_torsionSections_iff] at hx
    refine J.superset_covering ?_ (J.pullback_stable f.unop hx)
    rintro V g ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    change n • M.val.map g.op (M.val.map f x) = 0
    change n • M.val.map (g ≫ f.unop).op x = 0 at h
    rwa [op_comp, Quiver.Hom.op_unop, M.val.map_comp, ModuleCat.comp_apply] at h
  isSheaf X s hs := by
    rw [mem_torsionSections_iff]
    refine J.transitive hs _ fun V f hf =>
      J.superset_covering ?_ ((mem_torsionSections_iff J _ _ _).1 hf)
    rintro W g ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    change n • M.val.map (g ≫ f).op s = 0
    change n • M.val.map g.op (M.val.map f.op s) = 0 at h
    rwa [op_comp, M.val.map_comp, ModuleCat.comp_apply]

/-- **A map out of a torsion sheaf of modules lands in the locally torsion sections.** -/
theorem mem_torsionSubmodule_of_torsionModules {N M : SheafOfModules.{w} R} (g : N ⟶ M)
    (hN : torsionModules R N) (U : Cᵒᵖ) (y : N.val.obj U) :
    g.val.app U y ∈ (torsionSubmodule M).obj U := by
  obtain ⟨U⟩ := U
  rw [show (torsionSubmodule M).obj (op U) = torsionSections J M.val (op U) from rfl,
    mem_torsionSections_iff]
  refine J.superset_covering ?_ ((isLocallyTorsion_iff_torsionSieve_mem J _).1 hN U y)
  rintro V f ⟨n, hn, h⟩
  refine ⟨n, hn, ?_⟩
  show n • ((PresheafOfModules.toPresheaf R.obj).obj M.val).map f.op
    (((PresheafOfModules.toPresheaf R.obj).map g.val).app (op (unop (op U))) y) = 0
  change n • ((PresheafOfModules.toPresheaf R.obj).obj N.val).map f.op y = 0 at h
  rw [← NatTrans.naturality_apply ((PresheafOfModules.toPresheaf R.obj).map g.val) f.op y,
    ← map_nsmul, h, map_zero]

/-- The subsheaf of locally torsion sections is a torsion sheaf of modules. -/
theorem torsionModules_torsionSubmodule (M : SheafOfModules.{w} R) :
    torsionModules R (torsionSubmodule M).toSheafOfModules := by
  intro U x
  exact ⟨_, (mem_torsionSections_iff J M.val (op U) x.1).1 x.2,
    fun _ _ ⟨n, hn, h⟩ => ⟨n, hn, Subtype.ext h⟩⟩

/-- **A sheaf of modules receiving a jointly epimorphic family of maps out of torsion sheaves of
modules is torsion.** -/
theorem torsionModules_of_jointlyEpi {ι : Type*} {N : ι → SheafOfModules.{w} R}
    {M : SheafOfModules.{w} R} (g : ∀ i, N i ⟶ M) (hN : ∀ i, torsionModules R (N i))
    (hg : ∀ ⦃Z : SheafOfModules.{w} R⦄ (a b : M ⟶ Z), (∀ i, g i ≫ a = g i ≫ b) → a = b) :
    torsionModules R M := by
  let T := torsionSubmodule M
  have hq : cokernel.π T.ι = 0 := by
    refine hg _ 0 fun i => ?_
    rw [comp_zero]
    ext U y
    have hy := mem_torsionSubmodule_of_torsionModules (g i) (hN i) U y
    exact congrArg (fun φ => φ.val.app U ⟨_, hy⟩) (cokernel.condition T.ι)
  have : Epi T.ι := Abelian.epi_of_cokernel_π_eq_zero _ hq
  have : IsIso T.ι := isIso_of_mono_of_epi _
  exact (torsionModules R).prop_of_iso (asIso T.ι) (torsionModules_torsionSubmodule M)

/-- **A coproduct of torsion sheaves of modules is torsion.** -/
theorem torsionModules_sigma {ι : Type*} (N : ι → SheafOfModules.{w} R) [HasCoproduct N]
    (hN : ∀ i, torsionModules R (N i)) : torsionModules R (∐ N) :=
  torsionModules_of_jointlyEpi (Sigma.ι N) hN fun _ _ _ h => Sigma.hom_ext _ _ h

end Stacks.Torsion
