module

public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
public import Mathlib.Algebra.Homology.HomologicalComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ideal-power-torsion subcomplex of a complex of sheaves of modules

Let `(C, J)` be a site, `R` a sheaf of rings on it whose rings of sections are commutative, and
`ℐ ⊆ R` a sheaf of ideals, that is a submodule of the free rank-one sheaf of `R`-modules. For a
sheaf of `R`-modules `𝒥` this file constructs the submodule of `ℐ`-power-torsion sections
`⋃ₙ 𝒥[ℐⁿ]`, and for a complex `𝒥•` of sheaves of `R`-modules the subcomplex it cuts out.

The construction is in two steps, as for the powers of a sheaf of ideals: an objectwise
submodule, stable under the restriction maps but whose membership condition need not be local,
followed by the smallest submodule of the sheaf containing it.

## Main definitions

* `Stacks.IdealPowerTorsion.annStep`: one step `{s | ℐ · s ⊆ N}` of the torsion filtration.
* `Stacks.IdealPowerTorsion.presheafAnn`: the objectwise submodule `𝒥[ℐⁿ]` of the sections
  annihilated by the `n`-th power of `ℐ`, defined by iterating `annStep` from `⊥`.
* `Stacks.IdealPowerTorsion.presheafTorsion`: the objectwise union `⋃ₙ 𝒥[ℐⁿ]`.
* `Stacks.PresheafOfModules.Submodule.restrictHom` and
  `Stacks.SheafOfModules.Submodule.restrictHom`: a morphism carrying one submodule into another,
  restricted to a morphism between the associated (pre)sheaves of modules.
* `Stacks.IdealPowerTorsion.sheafAnn` and `Stacks.IdealPowerTorsion.sheafTorsion`: the submodules
  of a sheaf of modules cut out by `presheafAnn` and `presheafTorsion`.
* `Stacks.IdealPowerTorsion.torsionComplex`: the `ℐ`-power-torsion subcomplex of a complex of
  sheaves of modules, with its inclusion
  `Stacks.IdealPowerTorsion.torsionComplexι` into the ambient complex.
* `Stacks.IdealPowerTorsion.torsionComplexFunctor`: the subcomplex as an endofunctor of complexes,
  and `Stacks.IdealPowerTorsion.torsionComplexFunctorι` its inclusion into the identity functor.

## Main results

* `Stacks.IdealPowerTorsion.map_mem_presheafTorsion` and
  `Stacks.IdealPowerTorsion.map_mem_sheafTorsion`: every morphism of (pre)sheaves of modules
  carries power-torsion sections to power-torsion sections. Applied to the differentials this is
  the statement that the torsion submodules form a subcomplex; applied to a morphism of complexes
  it is the functoriality of the construction.
* `Stacks.IdealPowerTorsion.restrict_mem_sheafTorsion`: the restriction of a power-torsion
  section along any arrow of the site is power-torsion.
* `Stacks.IdealPowerTorsion.mem_sheafTorsion_iff`: a section is power-torsion exactly when,
  locally on a covering sieve, it is annihilated by some power of `ℐ`.
* `Stacks.IdealPowerTorsion.sheafTorsion_le`: the power-torsion submodule is the smallest one
  containing every `𝒥[ℐⁿ]`, so it is their filtered union.
* `Stacks.IdealPowerTorsion.sheafTorsion_antitone_ideal`: a larger sheaf of ideals has fewer
  power-torsion sections.
* `Stacks.IdealPowerTorsion.mono_torsionMap`: the construction preserves monomorphisms.
* `Stacks.IdealPowerTorsion.torsionComplexι_comp_colimitPost`: the canonical comparison from the
  colimit of the torsion subcomplexes of a diagram of complexes to the torsion subcomplex of the
  colimit is compatible with the inclusions, on each component of the colimit.

## Implementation notes

The submodule `𝒥[ℐⁿ]` is defined by iterating the one-step operation `N ↦ {s | ℐ · s ⊆ N}` from
the zero submodule, rather than by annihilating a power of `ℐ` formed in the lattice of ideals.
The recursive form needs no powers of ideals, and that matters here: the rings of sections are
read as objects of `RingCat`, where `Ideal` carries no multiplication, so forming `ℐⁿ` would
force the structure sheaf to be a sheaf of `CommRingCat`s and the construction would be
unavailable for a sheaf of rings that is merely sectionwise commutative. The commutativity that
is needed — a section of `ℐ` commutes with an arbitrary section of `R` — is supplied by the
mixin `IsMulCommutative` on each ring of sections, which is all the proofs use. That the name is
deserved is recorded by `Stacks.IdealPowerTorsion.pow_smul_eq_zero_of_mem_presheafAnn`: a member
of the `n`-th stage is killed by the `n`-th power of every section of `ℐ`.

The membership condition of `𝒥[ℐⁿ]` quantifies over all arrows of the site out of the given
object, not only over the sections of `ℐ` there. That is what makes it stable under the
restriction maps — the sections of `ℐ` over a smaller object need not come from the larger one —
and it is also why nothing is lost by using the objectwise powers of `ℐ` rather than the
sheaf-theoretic ones: a section of the sheaf-theoretic power is locally an objectwise one.

The union `⋃ₙ 𝒥[ℐⁿ]` is objectwise a submodule, because the `𝒥[ℐⁿ]` increase with `n`, but its
membership condition is not local: the exponent needed on a member of a covering family is not
bounded over the family. The power-torsion submodule of a sheaf of modules is therefore the
closure `Stacks.SheafOfModules.sheafifySubmodule` of the union, whose sections are described by
`Stacks.IdealPowerTorsion.mem_sheafTorsion_iff`.

Everything is stated for a sheaf of rings `R` on the site, with `ℐ` a submodule of the free
rank-one sheaf of `R`-modules, rather than for the sheaf of rings underlying a sheaf of
commutative rings. The two readings agree where the latter makes sense —
`Stacks.Sites.IdealSubsheaf O` is by definition a submodule of the free rank-one sheaf of modules
over `Stacks.SheafOfModules.Tensor.ringSheaf O` — so a sheaf of ideals of a sheaf of commutative
rings, and each of its powers `Stacks.Sites.idealPow`, is an admissible `ℐ` here; the instance
that lets one be used is `Stacks.Sheaves.KoszulGlobalSections.isMulCommutative_underlyingRing`.
Stating it this way makes the construction available on a site, such as a category of pairs,
whose structure sheaf is a sheaf of `RingCat`s.

Being a submodule of the underlying presheaf of modules, the torsion submodule is stable under
the restriction maps of the site; when the site is a category of pairs, those restriction maps
are the base changes along morphisms of pairs, and
`Stacks.IdealPowerTorsion.restrict_mem_sheafTorsion` is their compatibility with the
construction.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ u

namespace Stacks.PresheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- **A morphism restricted to submodules.** A morphism `φ : M ⟶ N` of presheaves of modules
carrying a submodule `P` of `M` into a submodule `Q` of `N`, as a morphism of presheaves of
modules from `P` to `Q`. -/
noncomputable def restrictHom {M N : PresheafOfModules.{w} R} (φ : M ⟶ N)
    {P : M.Submodule} {Q : N.Submodule}
    (h : ∀ (X : Cᵒᵖ) (s : M.obj X), s ∈ P.obj X → φ.app X s ∈ Q.obj X) :
    P.toPresheafOfModules ⟶ Q.toPresheafOfModules where
  app X := ModuleCat.ofHom ((φ.app X).hom.restrict (fun s hs => h X s hs))
  naturality {X Y} f := by
    ext ⟨s, hs⟩
    exact Subtype.ext (PresheafOfModules.naturality_apply φ f s)

/-- On sections, the restriction of `φ` to submodules is `φ`. -/
@[simp]
theorem restrictHom_app_coe {M N : PresheafOfModules.{w} R} (φ : M ⟶ N)
    {P : M.Submodule} {Q : N.Submodule}
    (h : ∀ (X : Cᵒᵖ) (s : M.obj X), s ∈ P.obj X → φ.app X s ∈ Q.obj X)
    (X : Cᵒᵖ) (s : P.obj X) : ((restrictHom φ h).app X s).1 = φ.app X s.1 :=
  rfl

/-- The restriction of a morphism to submodules is the morphism itself on sections. -/
@[reassoc (attr := simp)]
theorem restrictHom_comp_ι {M N : PresheafOfModules.{w} R} (φ : M ⟶ N)
    {P : M.Submodule} {Q : N.Submodule}
    (h : ∀ (X : Cᵒᵖ) (s : M.obj X), s ∈ P.obj X → φ.app X s ∈ Q.obj X) :
    restrictHom φ h ≫ Q.ι = P.ι ≫ φ := by
  ext X s
  rfl

end Stacks.PresheafOfModules.Submodule

namespace Stacks.SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **A morphism of sheaves of modules restricted to submodules.** A morphism `φ : M ⟶ N`
carrying a submodule `P` of `M` into a submodule `Q` of `N`, as a morphism of sheaves of modules
from `P` to `Q`. -/
noncomputable def restrictHom {M N : _root_.SheafOfModules.{w} R} (φ : M ⟶ N)
    {P : M.Submodule} {Q : N.Submodule}
    (h : ∀ (X : Cᵒᵖ) (s : M.val.obj X), s ∈ P.obj X → φ.val.app X s ∈ Q.obj X) :
    P.toSheafOfModules ⟶ Q.toSheafOfModules :=
  ⟨Stacks.PresheafOfModules.Submodule.restrictHom φ.val h⟩

/-- The underlying morphism of presheaves of modules of the restriction of `φ` to submodules is
the restriction of the underlying morphism of `φ`. -/
@[simp]
theorem restrictHom_val {M N : _root_.SheafOfModules.{w} R} (φ : M ⟶ N)
    {P : M.Submodule} {Q : N.Submodule}
    (h : ∀ (X : Cᵒᵖ) (s : M.val.obj X), s ∈ P.obj X → φ.val.app X s ∈ Q.obj X) :
    (restrictHom φ h).val = Stacks.PresheafOfModules.Submodule.restrictHom φ.val h :=
  rfl

/-- The restriction of a morphism of sheaves of modules to submodules is the morphism itself on
sections. -/
@[reassoc (attr := simp)]
theorem restrictHom_comp_ι {M N : _root_.SheafOfModules.{w} R} (φ : M ⟶ N)
    {P : M.Submodule} {Q : N.Submodule}
    (h : ∀ (X : Cᵒᵖ) (s : M.val.obj X), s ∈ P.obj X → φ.val.app X s ∈ Q.obj X) :
    restrictHom φ h ≫ Q.ι = P.ι ≫ φ :=
  _root_.SheafOfModules.Hom.ext
    (Stacks.PresheafOfModules.Submodule.restrictHom_comp_ι φ.val h)

end Stacks.SheafOfModules.Submodule

namespace Stacks.IdealPowerTorsion

section Presheaf

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  [∀ X : Cᵒᵖ, IsMulCommutative (R.obj X)]

omit [∀ X : Cᵒᵖ, IsMulCommutative (R.obj X)] in
/-- Restriction along the identity does nothing. -/
private theorem restrictₛₗ_id (M : PresheafOfModules.{w} R) {X : Cᵒᵖ} (s : M.obj X) :
    M.restrictₛₗ (𝟙 X) s = s := by
  simp

variable (I : (PresheafOfModules.unit R).Submodule) (M : PresheafOfModules.{w} R)

/-- **One step of the ideal-power-torsion filtration.** The sections `s` of `M` with
`ℐ · s ⊆ N`, in the sense that `a · s` is a section of `N` for every section `a` of `ℐ` over
every object of the site mapping to the given one. -/
def annStep (N : M.Submodule) : M.Submodule where
  obj X :=
    { carrier := {s : M.obj X | ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (a : R.obj Y), a ∈ I.obj Y →
        a • M.restrictₛₗ f s ∈ N.obj Y}
      zero_mem' := by
        intro Y f a _
        rw [map_zero, smul_zero]
        exact zero_mem _
      add_mem' := by
        intro x y hx hy Y f a ha
        rw [map_add, smul_add]
        exact add_mem (hx f a ha) (hy f a ha)
      smul_mem' := by
        intro c x hx Y f a ha
        have h : a • M.restrictₛₗ f (c • x) = (R.map f).hom c • (a • M.restrictₛₗ f x) := by
          rw [LinearMap.map_smulₛₗ, smul_smul, mul_comm' a, mul_smul]
        rw [h]
        exact (N.obj Y).smul_mem _ (hx f a ha) }
  map {X Y} f s hs := by
    intro Z g a ha
    have h : M.restrictₛₗ g (M.restrictₛₗ f s) = M.restrictₛₗ (f ≫ g) s :=
      (M.map_comp_apply f g s).symm
    rw [h]
    exact hs (f ≫ g) a ha

/-- A section `s` lies in `annStep I M N` exactly when `a · s|_Y` is a section of `N` for every
arrow `X ⟶ Y` and every section `a` of `ℐ` over `Y`. -/
theorem mem_annStep_iff {N : M.Submodule} {X : Cᵒᵖ} {s : M.obj X} :
    s ∈ (annStep I M N).obj X ↔
      ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (a : R.obj Y), a ∈ I.obj Y →
        a • M.restrictₛₗ f s ∈ N.obj Y :=
  Iff.rfl

/-- A submodule is contained in the next step of the filtration it generates: a section of `N`
restricts into `N`, and `N` is closed under multiplication by sections of the structure sheaf. -/
theorem le_annStep (N : M.Submodule) : N ≤ annStep I M N :=
  fun _ _ hs _ f _ _ => (N.obj _).smul_mem _ (N.map f hs)

/-- One step of the filtration is monotone. -/
theorem annStep_mono {N N' : M.Submodule} (h : N ≤ N') : annStep I M N ≤ annStep I M N' :=
  fun _ _ hs _ f a ha => h _ (hs f a ha)

/-- One step of the filtration is antitone in the sheaf of ideals: a larger ideal annihilates
fewer sections. -/
theorem annStep_antitone_ideal {I' : (PresheafOfModules.unit R).Submodule} (h : I ≤ I')
    (N : M.Submodule) : annStep I' M N ≤ annStep I M N :=
  fun _ _ hs _ f a ha => hs f a (h _ ha)

/-- **The sections annihilated by `ℐⁿ`**, as an objectwise submodule of a presheaf of modules:
the `n`-th stage of the filtration obtained by iterating `Stacks.IdealPowerTorsion.annStep` from
the zero submodule. -/
@[sga "7 VIII 2.1.14" "n = 1"]
def presheafAnn (n : ℕ) : M.Submodule := (annStep I M)^[n] ⊥

/-- The zeroth stage of the filtration is the zero submodule. -/
@[simp]
theorem presheafAnn_zero : presheafAnn I M 0 = ⊥ := rfl

/-- The `(n + 1)`-st stage of the filtration is one step applied to the `n`-th. -/
theorem presheafAnn_succ (n : ℕ) :
    presheafAnn I M (n + 1) = annStep I M (presheafAnn I M n) :=
  Function.iterate_succ_apply' _ _ _

/-- A section `s` is annihilated by `ℐⁿ⁺¹` exactly when `a · s|_Y` is annihilated by `ℐⁿ` for
every arrow `X ⟶ Y` and every section `a` of `ℐ` over `Y`. -/
theorem mem_presheafAnn_succ_iff {n : ℕ} {X : Cᵒᵖ} {s : M.obj X} :
    s ∈ (presheafAnn I M (n + 1)).obj X ↔
      ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (a : R.obj Y), a ∈ I.obj Y →
        a • M.restrictₛₗ f s ∈ (presheafAnn I M n).obj Y := by
  rw [presheafAnn_succ]
  exact mem_annStep_iff I M

/-- The sections annihilated by `ℐ` are those killed by every section of `ℐ`. -/
theorem mem_presheafAnn_one_iff {X : Cᵒᵖ} {s : M.obj X} :
    s ∈ (presheafAnn I M 1).obj X ↔
      ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (a : R.obj Y), a ∈ I.obj Y → a • M.restrictₛₗ f s = 0 := by
  rw [mem_presheafAnn_succ_iff]
  simp [presheafAnn_zero]

/-- Multiplying a section annihilated by `ℐⁿ⁺¹` by a section of `ℐ` gives one annihilated by
`ℐⁿ`. -/
theorem smul_mem_presheafAnn {n : ℕ} {X Y : Cᵒᵖ} {s : M.obj X} (f : X ⟶ Y) {a : R.obj Y}
    (ha : a ∈ I.obj Y) (hs : s ∈ (presheafAnn I M (n + 1)).obj X) :
    a • M.restrictₛₗ f s ∈ (presheafAnn I M n).obj Y :=
  (mem_presheafAnn_succ_iff I M).1 hs f a ha

/-- The stages of the filtration increase. -/
theorem presheafAnn_le_succ (n : ℕ) : presheafAnn I M n ≤ presheafAnn I M (n + 1) :=
  (presheafAnn_succ I M n).ge.trans' (le_annStep I M _)

/-- The stages of the filtration form a monotone sequence. -/
theorem presheafAnn_monotone : Monotone (presheafAnn I M) :=
  monotone_nat_of_le_succ (presheafAnn_le_succ I M)

/-- The stages of the filtration are antitone in the sheaf of ideals. -/
theorem presheafAnn_antitone_ideal {I' : (PresheafOfModules.unit R).Submodule} (h : I ≤ I')
    (n : ℕ) : presheafAnn I' M n ≤ presheafAnn I M n := by
  induction n with
  | zero => exact le_rfl
  | succ n hn =>
    rw [presheafAnn_succ, presheafAnn_succ]
    exact (annStep_antitone_ideal I M h _).trans (annStep_mono I M hn)

/-- **A section annihilated by `ℐⁿ` is killed by the `n`-th power of every section of `ℐ`.** -/
theorem pow_smul_eq_zero_of_mem_presheafAnn (n : ℕ) {X : Cᵒᵖ} {s : M.obj X} {a : R.obj X}
    (ha : a ∈ I.obj X) (hs : s ∈ (presheafAnn I M n).obj X) : a ^ n • s = 0 := by
  induction n generalizing s with
  | zero => simpa using hs
  | succ n hn =>
    have h : a • M.restrictₛₗ (𝟙 X) s ∈ (presheafAnn I M n).obj X :=
      smul_mem_presheafAnn I M (𝟙 X) ha hs
    rw [restrictₛₗ_id] at h
    rw [pow_succ, mul_smul]
    exact hn h

/-- **The `ℐ`-power-torsion sections**, as an objectwise submodule of a presheaf of modules: the
union `⋃ₙ M[ℐⁿ]` of the stages of the filtration. -/
def presheafTorsion : M.Submodule where
  obj X :=
    { carrier := {s : M.obj X | ∃ n, s ∈ (presheafAnn I M n).obj X}
      zero_mem' := ⟨0, zero_mem _⟩
      add_mem' := by
        rintro x y ⟨n, hn⟩ ⟨m, hm⟩
        exact ⟨max n m, add_mem (presheafAnn_monotone I M (le_max_left n m) _ hn)
          (presheafAnn_monotone I M (le_max_right n m) _ hm)⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        exact ⟨n, (presheafAnn I M n).obj _ |>.smul_mem c hn⟩ }
  map {X Y} f := by
    rintro s ⟨n, hn⟩
    exact ⟨n, (presheafAnn I M n).map f hn⟩

/-- A section is power torsion exactly when it is annihilated by some power of `ℐ`. -/
theorem mem_presheafTorsion_iff {X : Cᵒᵖ} {s : M.obj X} :
    s ∈ (presheafTorsion I M).obj X ↔ ∃ n, s ∈ (presheafAnn I M n).obj X :=
  Iff.rfl

/-- Every stage `M[ℐⁿ]` is contained in the power-torsion submodule. -/
theorem presheafAnn_le_presheafTorsion (n : ℕ) : presheafAnn I M n ≤ presheafTorsion I M :=
  fun _ _ hs => ⟨n, hs⟩

/-- **The power-torsion submodule is the union of the stages.** It is the smallest objectwise
submodule containing every `M[ℐⁿ]`. -/
theorem presheafTorsion_le {P : M.Submodule} (h : ∀ n, presheafAnn I M n ≤ P) :
    presheafTorsion I M ≤ P :=
  fun _ _ hs => by obtain ⟨n, hn⟩ := hs; exact h n _ hn

/-- The power-torsion sections are antitone in the sheaf of ideals. -/
theorem presheafTorsion_antitone_ideal {I' : (PresheafOfModules.unit R).Submodule} (h : I ≤ I') :
    presheafTorsion I' M ≤ presheafTorsion I M :=
  presheafTorsion_le _ _ fun n =>
    (presheafAnn_antitone_ideal I M h n).trans (presheafAnn_le_presheafTorsion I M n)

variable {M}

/-- **Morphisms preserve the stages of the filtration.** -/
theorem map_mem_presheafAnn {N : PresheafOfModules.{w} R} (φ : M ⟶ N) (n : ℕ) {X : Cᵒᵖ}
    {s : M.obj X} (hs : s ∈ (presheafAnn I M n).obj X) :
    φ.app X s ∈ (presheafAnn I N n).obj X := by
  induction n generalizing X s with
  | zero =>
    have h : s = 0 := by simpa using hs
    rw [h, map_zero]
    exact zero_mem _
  | succ n hn =>
    rw [mem_presheafAnn_succ_iff]
    intro Y f a ha
    have h : a • N.restrictₛₗ f (φ.app X s) = φ.app Y (a • M.restrictₛₗ f s) := by
      rw [map_smul]
      exact congrArg (a • ·) (PresheafOfModules.naturality_apply φ f s).symm
    rw [h]
    exact hn ((mem_presheafAnn_succ_iff I M).1 hs f a ha)

/-- **Morphisms preserve power-torsion sections.** -/
theorem map_mem_presheafTorsion {N : PresheafOfModules.{w} R} (φ : M ⟶ N) {X : Cᵒᵖ}
    {s : M.obj X} (hs : s ∈ (presheafTorsion I M).obj X) :
    φ.app X s ∈ (presheafTorsion I N).obj X := by
  obtain ⟨n, hn⟩ := hs
  exact ⟨n, map_mem_presheafAnn I φ n hn⟩

end Presheaf

section Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X : Cᵒᵖ, IsMulCommutative (R.obj.obj X)]
  (I : (SheafOfModules.unit R).Submodule) (M : SheafOfModules.{w} R)

/-- **The sections of a sheaf of modules annihilated by `ℐⁿ`**: the smallest submodule with local
membership containing the objectwise one. -/
@[sga "7 VIII 2.1.14" "more general"]
noncomputable def sheafAnn (n : ℕ) : M.Submodule :=
  Stacks.SheafOfModules.sheafifySubmodule (presheafAnn I.toSubmodule M.val n)

/-- **The `ℐ`-power-torsion submodule of a sheaf of modules**: the smallest submodule with local
membership containing the objectwise union `⋃ₙ M[ℐⁿ]`. -/
noncomputable def sheafTorsion : M.Submodule :=
  Stacks.SheafOfModules.sheafifySubmodule (presheafTorsion I.toSubmodule M.val)

/-- **Local description of the power-torsion sections.** A section of a sheaf of modules is
`ℐ`-power torsion exactly when it restricts, along every arrow of some covering sieve, to a
section annihilated by some power of `ℐ`. -/
theorem mem_sheafTorsion_iff {X : Cᵒᵖ} {s : M.val.obj X} :
    s ∈ (sheafTorsion I M).obj X ↔
      ∃ S : Sieve X.unop, S ∈ J X.unop ∧
        ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f →
          ∃ n, M.val.map f.op s ∈ (presheafAnn I.toSubmodule M.val n).obj (op Y) :=
  Stacks.SheafOfModules.mem_sheafifySubmodule_iff

/-- A section annihilated by some power of `ℐ` is power torsion. -/
theorem mem_sheafTorsion_of_mem_presheafAnn (n : ℕ) {X : Cᵒᵖ} {s : M.val.obj X}
    (hs : s ∈ (presheafAnn I.toSubmodule M.val n).obj X) : s ∈ (sheafTorsion I M).obj X :=
  Stacks.SheafOfModules.le_sheafifySubmodule _ X ⟨n, hs⟩

/-- Every submodule `M[ℐⁿ]` of a sheaf of modules is contained in the power-torsion submodule. -/
theorem sheafAnn_le_sheafTorsion (n : ℕ) : sheafAnn I M n ≤ sheafTorsion I M :=
  Stacks.SheafOfModules.sheafifySubmodule_mono (presheafAnn_le_presheafTorsion _ _ n)

/-- The submodules `M[ℐⁿ]` of a sheaf of modules form a monotone sequence. -/
theorem sheafAnn_monotone : Monotone (sheafAnn I M) := fun _ _ h =>
  Stacks.SheafOfModules.sheafifySubmodule_mono (presheafAnn_monotone _ _ h)

/-- **The power-torsion submodule is the filtered union of the `M[ℐⁿ]`.** It is the smallest
submodule with local membership containing every one of them. -/
theorem sheafTorsion_le {P : M.Submodule} (h : ∀ n, sheafAnn I M n ≤ P) :
    sheafTorsion I M ≤ P :=
  Stacks.SheafOfModules.sheafifySubmodule_le
    (presheafTorsion_le _ _ fun n =>
      (Stacks.SheafOfModules.le_sheafifySubmodule _).trans
        (_root_.SheafOfModules.Submodule.le_iff.1 (h n)))

/-- The power-torsion submodule is antitone in the sheaf of ideals. -/
theorem sheafTorsion_antitone_ideal {I' : (SheafOfModules.unit R).Submodule}
    (h : I ≤ I') : sheafTorsion I' M ≤ sheafTorsion I M :=
  Stacks.SheafOfModules.sheafifySubmodule_mono
    (presheafTorsion_antitone_ideal _ _ (_root_.SheafOfModules.Submodule.le_iff.1 h))

/-- **Restriction along an arrow of the site preserves power-torsion sections.** On a category of
pairs this is the compatibility of the construction with base change along a morphism of
pairs. -/
theorem restrict_mem_sheafTorsion {X Y : Cᵒᵖ} (f : X ⟶ Y) {s : M.val.obj X}
    (hs : s ∈ (sheafTorsion I M).obj X) : M.val.map f s ∈ (sheafTorsion I M).obj Y :=
  (sheafTorsion I M).map_mem f hs

variable {M}

/-- **Morphisms of sheaves of modules preserve the stages of the filtration.** -/
theorem map_mem_sheafAnn {N : SheafOfModules.{w} R} (φ : M ⟶ N) (n : ℕ) (X : Cᵒᵖ)
    {s : M.val.obj X} (hs : s ∈ (sheafAnn I M n).obj X) :
    φ.val.app X s ∈ (sheafAnn I N n).obj X := by
  obtain ⟨S, hS, hs⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule hs
  refine Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem hS fun Y f hf => ?_
  rw [← PresheafOfModules.naturality_apply]
  exact map_mem_presheafAnn I.toSubmodule φ.val n (hs f hf)

/-- **Morphisms of sheaves of modules preserve power-torsion sections.** -/
theorem map_mem_sheafTorsion {N : SheafOfModules.{w} R} (φ : M ⟶ N) (X : Cᵒᵖ)
    {s : M.val.obj X} (hs : s ∈ (sheafTorsion I M).obj X) :
    φ.val.app X s ∈ (sheafTorsion I N).obj X := by
  obtain ⟨S, hS, hs⟩ := (mem_sheafTorsion_iff I M).1 hs
  refine Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem hS fun Y f hf => ?_
  obtain ⟨n, hn⟩ := hs f hf
  refine ⟨n, ?_⟩
  rw [← PresheafOfModules.naturality_apply]
  exact map_mem_presheafAnn I.toSubmodule φ.val n hn

/-- The restriction of a morphism of sheaves of modules to the power-torsion submodules. -/
noncomputable def torsionMap {N : SheafOfModules.{w} R} (φ : M ⟶ N) :
    (sheafTorsion I M).toSheafOfModules ⟶ (sheafTorsion I N).toSheafOfModules :=
  Stacks.SheafOfModules.Submodule.restrictHom φ
    (fun X _ hs => map_mem_sheafTorsion I φ X hs)

/-- The restriction of `φ` to the power-torsion submodules, followed by the inclusion, is the
inclusion followed by `φ`. -/
@[reassoc (attr := simp)]
theorem torsionMap_comp_ι {N : SheafOfModules.{w} R} (φ : M ⟶ N) :
    torsionMap I φ ≫ (sheafTorsion I N).ι = (sheafTorsion I M).ι ≫ φ :=
  Stacks.SheafOfModules.Submodule.restrictHom_comp_ι _ _

/-- The restriction of the identity to the power-torsion submodule is the identity. -/
@[simp]
theorem torsionMap_id : torsionMap I (𝟙 M) = 𝟙 (sheafTorsion I M).toSheafOfModules := by
  rw [← cancel_mono (sheafTorsion I M).ι, torsionMap_comp_ι, Category.comp_id, Category.id_comp]

/-- The restriction of a composite to the power-torsion submodules is the composite of the
restrictions. -/
@[simp]
theorem torsionMap_comp {N P : SheafOfModules.{w} R} (φ : M ⟶ N) (ψ : N ⟶ P) :
    torsionMap I (φ ≫ ψ) = torsionMap I φ ≫ torsionMap I ψ := by
  rw [← cancel_mono (sheafTorsion I P).ι]
  simp only [Category.assoc, torsionMap_comp_ι, torsionMap_comp_ι_assoc]

/-- The restriction of a monomorphism to the power-torsion submodules is a monomorphism. -/
instance mono_torsionMap {N : SheafOfModules.{w} R} (φ : M ⟶ N) [Mono φ] :
    Mono (torsionMap I φ) :=
  mono_of_mono_fac (torsionMap_comp_ι I φ)

end Sheaf

section Complex

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X : Cᵒᵖ, IsMulCommutative (R.obj.obj X)]
  (I : (SheafOfModules.unit R).Submodule) {ι : Type*} (c : ComplexShape ι)

/-- **The `ℐ`-power-torsion subcomplex of a complex of sheaves of modules.** In each degree it is
the power-torsion submodule, and the differentials are the restrictions of the differentials of
the ambient complex, which make sense because every morphism of sheaves of modules preserves
power-torsion sections. -/
noncomputable def torsionComplex (K : HomologicalComplex (SheafOfModules.{w} R) c) :
    HomologicalComplex (SheafOfModules.{w} R) c where
  X i := (sheafTorsion I (K.X i)).toSheafOfModules
  d i j := torsionMap I (K.d i j)
  shape i j hij := by
    rw [← cancel_mono (sheafTorsion I (K.X j)).ι, torsionMap_comp_ι, K.shape i j hij,
      comp_zero, zero_comp]
  d_comp_d' i j k _ _ := by
    rw [← cancel_mono (sheafTorsion I (K.X k)).ι, Category.assoc, torsionMap_comp_ι,
      ← Category.assoc, torsionMap_comp_ι, Category.assoc, K.d_comp_d, comp_zero, zero_comp]

/-- In degree `i` the power-torsion subcomplex is the power-torsion submodule of `K.X i`. -/
@[simp]
theorem torsionComplex_X (K : HomologicalComplex (SheafOfModules.{w} R) c) (i : ι) :
    (torsionComplex I c K).X i = (sheafTorsion I (K.X i)).toSheafOfModules :=
  rfl

/-- The differentials of the power-torsion subcomplex are the restrictions of those of `K`. -/
@[simp]
theorem torsionComplex_d (K : HomologicalComplex (SheafOfModules.{w} R) c) (i j : ι) :
    (torsionComplex I c K).d i j = torsionMap I (K.d i j) :=
  rfl

/-- **The inclusion of the power-torsion subcomplex.** -/
noncomputable def torsionComplexι (K : HomologicalComplex (SheafOfModules.{w} R) c) :
    torsionComplex I c K ⟶ K where
  f i := (sheafTorsion I (K.X i)).ι
  comm' i j _ := (torsionMap_comp_ι I (K.d i j)).symm

/-- In degree `i` the inclusion of the power-torsion subcomplex is the inclusion of the
power-torsion submodule of `K.X i`. -/
@[simp]
theorem torsionComplexι_f (K : HomologicalComplex (SheafOfModules.{w} R) c) (i : ι) :
    (torsionComplexι I c K).f i = (sheafTorsion I (K.X i)).ι :=
  rfl

/-- The inclusion of the power-torsion subcomplex is a monomorphism. -/
instance mono_torsionComplexι (K : HomologicalComplex (SheafOfModules.{w} R) c) :
    Mono (torsionComplexι I c K) :=
  HomologicalComplex.mono_of_mono_f _ fun i =>
    inferInstanceAs (Mono (sheafTorsion I (K.X i)).ι)

/-- **The restrictions of a morphism of complexes commute with the restricted differentials.** -/
theorem torsionMap_comm {K L : HomologicalComplex (SheafOfModules.{w} R) c} (φ : K ⟶ L)
    (i j : ι) : torsionMap I (φ.f i) ≫ torsionMap I (L.d i j) =
      torsionMap I (K.d i j) ≫ torsionMap I (φ.f j) := by
  rw [← torsionMap_comp, ← torsionMap_comp, φ.comm]

/-- **The power-torsion subcomplex, as an endofunctor of complexes of sheaves of modules.** -/
noncomputable def torsionComplexFunctor :
    HomologicalComplex (SheafOfModules.{w} R) c ⥤ HomologicalComplex (SheafOfModules.{w} R) c where
  obj K := torsionComplex I c K
  map {_ _} φ :=
    { f := fun i => torsionMap I (φ.f i)
      comm' := fun i j _ => torsionMap_comm I c φ i j }
  map_id _ := HomologicalComplex.hom_ext _ _ fun _ => torsionMap_id I
  map_comp {_ _ _} φ ψ :=
    HomologicalComplex.hom_ext _ _ fun i => torsionMap_comp I (φ.f i) (ψ.f i)

/-- The power-torsion endofunctor sends a complex to its power-torsion subcomplex. -/
@[simp]
theorem torsionComplexFunctor_obj (K : HomologicalComplex (SheafOfModules.{w} R) c) :
    (torsionComplexFunctor I c).obj K = torsionComplex I c K :=
  rfl

/-- In degree `i` the power-torsion endofunctor sends a morphism of complexes `φ` to the
restriction of `φ.f i` to the power-torsion submodules. -/
@[simp]
theorem torsionComplexFunctor_map_f {K L : HomologicalComplex (SheafOfModules.{w} R) c}
    (φ : K ⟶ L) (i : ι) : ((torsionComplexFunctor I c).map φ).f i = torsionMap I (φ.f i) :=
  rfl

/-- **The inclusion of the power-torsion subcomplex is natural**, so it is a morphism from the
power-torsion endofunctor to the identity. -/
noncomputable def torsionComplexFunctorι : torsionComplexFunctor I c ⟶ 𝟭 _ where
  app K := torsionComplexι I c K
  naturality _ _ φ :=
    HomologicalComplex.hom_ext _ _ fun i => torsionMap_comp_ι I (φ.f i)

/-- **Compatibility with a colimit of complexes.** The canonical comparison from the colimit of
the power-torsion subcomplexes of a diagram to the power-torsion subcomplex of its colimit —
the morphism `CategoryTheory.Limits.colimit.post` of the endofunctor — carries the inclusion of
each component of the first colimit to the inclusion of the corresponding component of the
second. -/
theorem torsionComplexι_comp_colimitPost {D : Type*} [Category D]
    (F : D ⥤ HomologicalComplex (SheafOfModules.{w} R) c)
    [HasColimit F] [HasColimit (F ⋙ torsionComplexFunctor I c)] (d : D) :
    colimit.ι (F ⋙ torsionComplexFunctor I c) d ≫
        colimit.post F (torsionComplexFunctor I c) ≫
          (torsionComplexFunctorι I c).app (colimit F) =
      (torsionComplexFunctorι I c).app (F.obj d) ≫ colimit.ι F d := by
  rw [← Category.assoc, colimit.ι_post]
  exact (torsionComplexFunctorι I c).naturality (colimit.ι F d)

end Complex

end Stacks.IdealPowerTorsion

end
