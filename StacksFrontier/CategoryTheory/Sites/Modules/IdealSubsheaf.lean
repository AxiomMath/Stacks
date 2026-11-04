module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.RingTheory.Ideal.Maps
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of ideals on a site: powers and products with a module

Let `(C, J)` be a site and `O` a sheaf of commutative rings on it. A *sheaf of ideals*
`I ⊆ O` is a submodule of the free rank-one sheaf of `O`-modules, so its sections over an
object of the site form an ideal of the ring of sections there. This file constructs the
power `Iⁿ` of a sheaf of ideals and the product `I · N` of a sheaf of ideals with a submodule
of a sheaf of `O`-modules.

Both are built in two steps: the objectwise operation, which is stable under the restriction
maps but whose membership condition need not be local, followed by the smallest sheaf of
submodules containing it.

## Main definitions

* `Stacks.SheafOfModules.sheafifySubmodule`: the smallest submodule of a sheaf of modules whose
  membership is local and which contains a given objectwise submodule.
* `Stacks.Sites.IdealSubsheaf`: sheaves of ideals of a sheaf of commutative rings on a site.
* `Stacks.Sites.sectionIdeal`: the ideal of sections of a sheaf of ideals over an object.
* `Stacks.Sites.presheafIdealPow` and `Stacks.Sites.idealPow`: the objectwise `n`-th power of a
  sheaf of ideals, and the sheaf of ideals it generates.
* `Stacks.Sites.presheafIdealSmul` and `Stacks.Sites.idealSmul`: the objectwise product `I · N`
  of a sheaf of ideals with a submodule of a sheaf of modules, and the submodule it generates.

## Main results

* `Stacks.SheafOfModules.sheafifySubmodule_toSubmodule`: a submodule with local membership is its
  own closure, so the closure operation is a retraction onto the sheaf-theoretic submodules.
* `Stacks.Sites.idealPow_zero`, `Stacks.Sites.idealPow_one` and
  `Stacks.Sites.idealPow_antitone`: `I⁰ = O`, `I¹ = I`, and the powers decrease.
* `Stacks.Sites.idealSmul_le`: `I · N ⊆ N`.

## Implementation notes

The objectwise `n`-th power is stable under restriction because the restriction maps are ring
homomorphisms and the image of a product of `n` sections of `I` is a product of `n` sections of
`I`. It need not have local membership: a section that is locally an `n`-fold product of
sections of `I` need not be one globally. The sheaf-theoretic power is therefore the smallest
submodule with local membership containing it, which exists because those form a complete
lattice. On the lattice of submodules with local membership the infimum is computed objectwise,
which is what makes the closure easy to use; the supremum is not, which is why the closure is
taken as an infimum of upper bounds rather than built from a supremum.

The product `I · N` is the objectwise submodule spanned by the products `a · m` with `a` a
section of `I` and `m` a section of `N`, rather than the ideal-times-submodule operation of
commutative algebra: the ring of sections is read as an object of `RingCat`, so the scalars act
through the ring structure that indexes the sheaves of modules and not through a commutative
one. For the power, where no module is involved, the ideals of commutative algebra are
available and are used.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ u

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- The zero submodule of a sheaf of modules is local, hence a subsheaf: a section whose
restrictions along a covering family all vanish is itself zero, because the ambient presheaf is
a sheaf. -/
def zero (M : SheafOfModules.{w} R) : M.Submodule where
  toSubmodule := ⊥
  isSheaf := by
    intro U s hs
    have hM : Presieve.IsSheaf J (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
      (isSheaf_iff_isSheaf_of_type _ _).mp
        (Presheaf.isSheaf_comp_of_isSheaf _ _ _ (SheafOfModules.isSheaf M))
    have hz : (show (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).obj U from s) = 0 := by
      refine (hM _ hs).isSeparatedFor.ext (t₂ := 0) fun V f hf ↦ ?_
      have hmem : (M.val.presheaf.map f.op).hom s ∈ (⊥ : M.val.Submodule).obj (Opposite.op V) := by
        convert hf using 1
        rfl
      change (M.val.presheaf.map f.op).hom s = (M.val.presheaf.map f.op).hom 0
      rw [map_zero]
      exact (_root_.Submodule.mem_bot _).mp hmem
    exact (_root_.Submodule.mem_bot _).mpr (by change s = 0; exact hz)

/-- The ideal of sections of the bottom subsheaf of a sheaf of modules is zero over every object
of the site. -/
@[simp]
lemma bot_obj (M : SheafOfModules.{w} R) (U : Cᵒᵖ) : (⊥ : M.Submodule).obj U = ⊥ :=
  le_antisymm (le_iff.mp (bot_le : (⊥ : M.Submodule) ≤ zero M) U) bot_le

/-- **The bottom subsheaf of a sheaf of modules is a zero object.** Its sections vanish over
every object of the site, so its identity is the zero morphism. -/
theorem isZero_toSheafOfModules_bot (M : SheafOfModules.{w} R) :
    Limits.IsZero (⊥ : M.Submodule).toSheafOfModules := by
  rw [Limits.IsZero.iff_id_eq_zero]
  ext U x
  have : Subsingleton ((⊥ : M.Submodule).toSheafOfModules.val.obj U) :=
    (show Subsingleton ((⊥ : M.Submodule).obj U) by rw [bot_obj]; infer_instance)
  exact Subsingleton.elim _ _

/-- A submodule of a sheaf of modules which is the bottom one is a zero object. -/
theorem isZero_toSheafOfModules_of_eq_bot {M : SheafOfModules.{w} R} {N : M.Submodule}
    (h : N = ⊥) : Limits.IsZero N.toSheafOfModules :=
  h ▸ isZero_toSheafOfModules_bot M

end SheafOfModules.Submodule

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{w} R}

/-- **The largest submodule has all sections.** The lattice of submodules of a sheaf of modules
whose membership is local has the objectwise largest submodule as its top element, since that
one's membership condition is vacuous and hence local. -/
theorem toSubmodule_top : (⊤ : M.Submodule).toSubmodule = ⊤ :=
  top_unique (show (⊤ : M.val.Submodule) ≤ _ from
    le_of_eq_of_le rfl
      (_root_.SheafOfModules.Submodule.le_iff.1
        (le_top (a := ({ toSubmodule := ⊤, isSheaf := fun _ _ _ => trivial } : M.Submodule)))))

/-- The smallest submodule of a sheaf of modules with local membership containing a given
objectwise submodule. -/
noncomputable def sheafifySubmodule (N : M.val.Submodule) : M.Submodule :=
  sInf {P : M.Submodule | N ≤ P.toSubmodule}

/-- An objectwise submodule is contained in its closure. -/
theorem le_sheafifySubmodule (N : M.val.Submodule) :
    N ≤ (sheafifySubmodule N).toSubmodule := by
  rw [sheafifySubmodule, _root_.SheafOfModules.Submodule.toSubmodule_sInf]
  exact le_sInf (by rintro _ ⟨P, hP, rfl⟩; exact hP)

/-- The closure of an objectwise submodule is the smallest submodule with local membership
containing it. -/
theorem sheafifySubmodule_le {N : M.val.Submodule} {P : M.Submodule}
    (h : N ≤ P.toSubmodule) : sheafifySubmodule N ≤ P :=
  sInf_le h

/-- The closure operation is monotone. -/
theorem sheafifySubmodule_mono {N N' : M.val.Submodule} (h : N ≤ N') :
    sheafifySubmodule N ≤ sheafifySubmodule N' :=
  sheafifySubmodule_le (h.trans (le_sheafifySubmodule N'))

/-- A submodule whose membership is already local is its own closure. -/
@[simp]
theorem sheafifySubmodule_toSubmodule (P : M.Submodule) :
    sheafifySubmodule P.toSubmodule = P :=
  le_antisymm (sheafifySubmodule_le le_rfl)
    (_root_.SheafOfModules.Submodule.le_iff.2 (le_sheafifySubmodule P.toSubmodule))

/-- The closure of the objectwise largest submodule is the largest submodule. -/
@[simp]
theorem sheafifySubmodule_top : sheafifySubmodule (⊤ : M.val.Submodule) = ⊤ := by
  rw [← toSubmodule_top (M := M), sheafifySubmodule_toSubmodule]

end Stacks.SheafOfModules

namespace Stacks.Sites


variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- A *sheaf of ideals* of a sheaf of commutative rings `O` on a site is a submodule of the
free rank-one sheaf of `O`-modules whose membership is local. Its sections over an object of
the site form an ideal of the ring of sections of `O` there. -/
@[ega "0 4.1.3" "special case"]
abbrev IdealSubsheaf (O : Sheaf J CommRingCat.{u}) :=
  (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).Submodule

variable {O : Sheaf J CommRingCat.{u}}

/-- The ideal of sections of a sheaf of ideals over an object of the site. -/
def sectionIdeal (I : IdealSubsheaf O) (X : Cᵒᵖ) : Ideal (O.obj.obj X) :=
  I.obj X

/-- Membership in the ideal of sections is membership in the sheaf of ideals. -/
theorem mem_sectionIdeal {I : IdealSubsheaf O} {X : Cᵒᵖ} {a : O.obj.obj X} :
    a ∈ sectionIdeal I X ↔ a ∈ I.obj X :=
  Iff.rfl

/-- Restriction maps carry the ideal of sections of a sheaf of ideals into the ideal of
sections over the smaller object. -/
theorem map_mem_sectionIdeal (I : IdealSubsheaf O) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    {a : O.obj.obj X} (ha : a ∈ sectionIdeal I X) : O.obj.map f a ∈ sectionIdeal I Y :=
  I.map_mem f ha

/-- The objectwise `n`-th power of a sheaf of ideals: over every object of the site, the `n`-th
power of the ideal of sections. -/
noncomputable def presheafIdealPow (I : IdealSubsheaf O) (n : ℕ) :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val.Submodule where
  obj X := sectionIdeal I X ^ n
  map {X Y} f a ha := by
    have h : Ideal.map (O.obj.map f).hom (sectionIdeal I X ^ n) ≤ sectionIdeal I Y ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono
        (Ideal.map_le_iff_le_comap.2 fun _ h => map_mem_sectionIdeal I f h) n
    exact h (Ideal.mem_map_of_mem _ ha)

/-- The sections of the objectwise power are the power of the sections. -/
theorem presheafIdealPow_obj (I : IdealSubsheaf O) (n : ℕ) (X : Cᵒᵖ) :
    (presheafIdealPow I n).obj X = sectionIdeal I X ^ n :=
  rfl

/-- The objectwise zeroth power is the whole structure sheaf. -/
theorem presheafIdealPow_zero (I : IdealSubsheaf O) : presheafIdealPow I 0 = ⊤ :=
  PresheafOfModules.Submodule.ext fun _ => by
    rw [presheafIdealPow_obj, pow_zero, Ideal.one_eq_top]; rfl

/-- The objectwise first power is the sheaf of ideals itself. -/
theorem presheafIdealPow_one (I : IdealSubsheaf O) : presheafIdealPow I 1 = I.toSubmodule :=
  PresheafOfModules.Submodule.ext fun _ => by rw [presheafIdealPow_obj, pow_one]; rfl

/-- The objectwise powers of a sheaf of ideals decrease. -/
theorem presheafIdealPow_antitone (I : IdealSubsheaf O) {m n : ℕ} (h : m ≤ n) :
    presheafIdealPow I n ≤ presheafIdealPow I m :=
  fun _ => Ideal.pow_le_pow_right h

/-- The `n`-th power `Iⁿ` of a sheaf of ideals: the smallest sheaf of ideals containing the
objectwise `n`-th power. -/
noncomputable def idealPow (I : IdealSubsheaf O) (n : ℕ) : IdealSubsheaf O :=
  Stacks.SheafOfModules.sheafifySubmodule (presheafIdealPow I n)

/-- The objectwise `n`-th power is contained in the `n`-th power. -/
theorem presheafIdealPow_le_idealPow (I : IdealSubsheaf O) (n : ℕ) :
    presheafIdealPow I n ≤ (idealPow I n).toSubmodule :=
  Stacks.SheafOfModules.le_sheafifySubmodule _

/-- A product of `n` sections of a sheaf of ideals is a section of its `n`-th power. -/
theorem mem_idealPow_of_mem_pow (I : IdealSubsheaf O) (n : ℕ) {X : Cᵒᵖ} {a : O.obj.obj X}
    (ha : a ∈ sectionIdeal I X ^ n) : a ∈ (idealPow I n).obj X :=
  presheafIdealPow_le_idealPow I n X ha

/-- The `n`-th power is the smallest sheaf of ideals whose sections contain the `n`-th powers of
the sections of `I`. -/
theorem idealPow_le (I : IdealSubsheaf O) (n : ℕ) {P : IdealSubsheaf O}
    (h : ∀ X : Cᵒᵖ, sectionIdeal I X ^ n ≤ P.obj X) : idealPow I n ≤ P :=
  Stacks.SheafOfModules.sheafifySubmodule_le h

/-- `I⁰` is the whole structure sheaf. -/
@[simp]
theorem idealPow_zero (I : IdealSubsheaf O) : idealPow I 0 = ⊤ := by
  rw [idealPow, presheafIdealPow_zero, Stacks.SheafOfModules.sheafifySubmodule_top]

/-- `I¹` is `I`. -/
@[simp]
theorem idealPow_one (I : IdealSubsheaf O) : idealPow I 1 = I := by
  rw [idealPow, presheafIdealPow_one, Stacks.SheafOfModules.sheafifySubmodule_toSubmodule]

/-- The powers of a sheaf of ideals decrease. -/
theorem idealPow_antitone (I : IdealSubsheaf O) {m n : ℕ} (h : m ≤ n) :
    idealPow I n ≤ idealPow I m :=
  Stacks.SheafOfModules.sheafifySubmodule_mono (presheafIdealPow_antitone I h)

/-- Each power of a sheaf of ideals is contained in the one before it. -/
theorem idealPow_succ_le (I : IdealSubsheaf O) (n : ℕ) :
    idealPow I (n + 1) ≤ idealPow I n :=
  idealPow_antitone I n.le_succ

/-- Every power of a sheaf of ideals beyond the zeroth is contained in it. -/
theorem idealPow_succ_le_self (I : IdealSubsheaf O) (n : ℕ) :
    idealPow I (n + 1) ≤ I := by
  simpa using idealPow_antitone I (Nat.succ_le_succ (Nat.zero_le n))

variable {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}

/-- The objectwise product `I · N` of a sheaf of ideals with an objectwise submodule of a sheaf
of modules: over every object of the site, the submodule spanned by the products of a section of
`I` with a section of `N`. -/
noncomputable def presheafIdealSmul (I : IdealSubsheaf O) (N : M.val.Submodule) :
    M.val.Submodule where
  obj X := Submodule.span ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X)
    {z : M.val.obj X | ∃ a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X,
      a ∈ I.obj X ∧ ∃ m ∈ N.obj X, z = a • m}
  map {X Y} f := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, m, hm, rfl⟩
    refine Submodule.mem_comap.2 ?_
    change M.val.map f (a • m) ∈ _
    rw [M.val.map_smul]
    exact Submodule.subset_span ⟨_, I.map_mem f ha, _, N.map_mem f hm, rfl⟩

/-- A product of a section of `I` with a section of `N` is a section of the objectwise product. -/
theorem smul_mem_presheafIdealSmul (I : IdealSubsheaf O) {N : M.val.Submodule} {X : Cᵒᵖ}
    {a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X} (ha : a ∈ I.obj X)
    {m : M.val.obj X} (hm : m ∈ N.obj X) : a • m ∈ (presheafIdealSmul I N).obj X :=
  Submodule.subset_span ⟨a, ha, m, hm, rfl⟩

/-- The objectwise product `I · N` is the smallest objectwise submodule containing every product
of a section of `I` with a section of `N`. -/
theorem presheafIdealSmul_le (I : IdealSubsheaf O) {N : M.val.Submodule}
    {P : M.val.Submodule}
    (h : ∀ (X : Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X), a ∈ I.obj X →
      ∀ m ∈ N.obj X, a • m ∈ P.obj X) : presheafIdealSmul I N ≤ P :=
  fun X => Submodule.span_le.2 (by rintro z ⟨a, ha, m, hm, rfl⟩; exact h X a ha m hm)

/-- The objectwise product `I · N` is contained in `N`. -/
theorem presheafIdealSmul_le_self (I : IdealSubsheaf O) (N : M.val.Submodule) :
    presheafIdealSmul I N ≤ N :=
  presheafIdealSmul_le I fun X a _ _ hm => (N.obj X).smul_mem a hm

/-- The objectwise product is monotone in the module variable. -/
theorem presheafIdealSmul_mono_right (I : IdealSubsheaf O) {N N' : M.val.Submodule}
    (h : N ≤ N') : presheafIdealSmul I N ≤ presheafIdealSmul I N' :=
  presheafIdealSmul_le I fun _ _ ha _ hm => smul_mem_presheafIdealSmul I ha (h _ hm)

/-- The objectwise product is monotone in the ideal variable. -/
theorem presheafIdealSmul_mono_left {I I' : IdealSubsheaf O} (h : I ≤ I')
    (N : M.val.Submodule) : presheafIdealSmul I N ≤ presheafIdealSmul I' N :=
  presheafIdealSmul_le I fun _ _ ha _ hm =>
    smul_mem_presheafIdealSmul I' (_root_.SheafOfModules.Submodule.le_iff.1 h _ ha) hm

/-- The product `I · N` of a sheaf of ideals with a submodule of a sheaf of modules: the
smallest submodule with local membership containing the objectwise product. -/
@[ega "0 4.1.6" "special case", ega "0 5.3.6"]
noncomputable def idealSmul (I : IdealSubsheaf O) (N : M.Submodule) : M.Submodule :=
  Stacks.SheafOfModules.sheafifySubmodule (presheafIdealSmul I N.toSubmodule)

/-- A product of a section of `I` with a section of `N` is a section of `I · N`. -/
theorem smul_mem_idealSmul (I : IdealSubsheaf O) {N : M.Submodule} {X : Cᵒᵖ}
    {a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X} (ha : a ∈ I.obj X)
    {m : M.val.obj X} (hm : m ∈ N.obj X) : a • m ∈ (idealSmul I N).obj X :=
  Stacks.SheafOfModules.le_sheafifySubmodule _ X (smul_mem_presheafIdealSmul I ha hm)

/-- `I · N` is contained in `N`. -/
theorem idealSmul_le (I : IdealSubsheaf O) (N : M.Submodule) : idealSmul I N ≤ N :=
  Stacks.SheafOfModules.sheafifySubmodule_le (presheafIdealSmul_le_self I N.toSubmodule)

/-- The product is monotone in the module variable. -/
theorem idealSmul_mono_right (I : IdealSubsheaf O) {N N' : M.Submodule} (h : N ≤ N') :
    idealSmul I N ≤ idealSmul I N' :=
  Stacks.SheafOfModules.sheafifySubmodule_mono
    (presheafIdealSmul_mono_right I (_root_.SheafOfModules.Submodule.le_iff.1 h))

/-- The product is monotone in the ideal variable. -/
theorem idealSmul_mono_left {I I' : IdealSubsheaf O} (h : I ≤ I') (N : M.Submodule) :
    idealSmul I N ≤ idealSmul I' N :=
  Stacks.SheafOfModules.sheafifySubmodule_mono (presheafIdealSmul_mono_left h N.toSubmodule)

end Stacks.Sites

end
