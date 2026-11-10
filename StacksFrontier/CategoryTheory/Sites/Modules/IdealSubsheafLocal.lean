module

public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower

/-!
# Local membership in a submodule of a sheaf of modules

Let `(C, J)` be a site, `M` a sheaf of modules over a sheaf of rings on it, and `N` a submodule
of the underlying presheaf of modules of `M`. The smallest submodule of `M` with local membership
containing `N` has an explicit description: a section lies in it exactly when it lies in `N`
locally, that is, after restriction along every arrow of some covering sieve. This file proves
that description and uses it to compare the product of a sheaf of ideals with a power of itself
to the next power.

## Main definitions

* `Stacks.PresheafOfModules.Submodule.sheafify`: the objectwise submodule of the sections lying
  in a given objectwise submodule locally.
* `Stacks.SheafOfModules.Submodule.sheafify`: the same submodule of a sheaf of modules, whose
  membership condition is local.
* `Stacks.Sites.adicGradedPieceπ`: the projection of `Iⁿ` onto the graded piece `Iⁿ/Iⁿ⁺¹`.

## Main results

* `Stacks.SheafOfModules.sheafifySubmodule_eq_sheafify` and
  `Stacks.SheafOfModules.mem_sheafifySubmodule_iff`: the smallest submodule with local membership
  containing an objectwise submodule consists of the sections lying in that objectwise submodule
  locally, so a section belongs to it exactly when it restricts into the objectwise submodule
  along every arrow of some covering sieve.
* `Stacks.Sites.idealSmul_idealPow_le_idealPow_succ`: `I · Iⁿ ⊆ Iⁿ⁺¹` for a sheaf of ideals `I`.
* `Stacks.Sites.idealSmul_homOfLE_comp_adicGradedPieceπ`: the composite of the inclusion
  `I · Iⁿ ⟶ Iⁿ` with the projection `Iⁿ ⟶ Iⁿ/Iⁿ⁺¹` vanishes, so the graded piece `Iⁿ/Iⁿ⁺¹` is
  killed by `I`.

## Implementation notes

The objectwise closure is Mathlib's `CategoryTheory.Subfunctor.sheafify` of the underlying
subpresheaf of types; the content of the definition is that the result is again
submodule-valued, which holds because two covering sieves have a covering intersection and
because the restriction maps are semilinear. Its membership condition is local by
`CategoryTheory.Subfunctor.sheafify_sheafify`, so it is a submodule of the sheaf of modules, and
it is sandwiched between the objectwise submodule and every submodule with local membership
containing it; that identifies it with the infimum defining the closure.

The inclusion `I · Iⁿ ⊆ Iⁿ⁺¹` is not objectwise: a section of `Iⁿ` is only locally an `n`-fold
product of sections of `I`, so multiplying it by a section of `I` gives a section that is only
locally an `n+1`-fold product. The local description of the closure is exactly what is needed to
conclude.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v₁ u₁ u v

namespace Stacks.PresheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M : PresheafOfModules.{w} R} {J : GrothendieckTopology C}

/-- The objectwise closure of a submodule of a presheaf of modules: over every object, the
sections which lie in the submodule after restriction along every arrow of some covering sieve.

This is Mathlib's `CategoryTheory.Subfunctor.sheafify` of the underlying subpresheaf of types,
and the content of the definition is that it is again submodule-valued. -/
def sheafify (N : M.Submodule) (J : GrothendieckTopology C) : M.Submodule where
  obj X :=
    { carrier := (N.toSubfunctor.sheafify J).obj X
      add_mem' := by
        intro x y hx hy
        refine J.superset_covering ?_ (J.intersection_covering hx hy)
        rintro V g ⟨hg₁, hg₂⟩
        change M.map g.op (x + y) ∈ N.obj (op V)
        rw [map_add]
        exact add_mem hg₁ hg₂
      zero_mem' := by
        refine J.superset_covering ?_ (J.top_mem _)
        intro V g _
        change M.map g.op 0 ∈ N.obj (op V)
        rw [map_zero]
        exact zero_mem _
      smul_mem' := by
        intro a x hx
        refine J.superset_covering ?_ hx
        intro V g hg
        change M.map g.op (a • x) ∈ N.obj (op V)
        rw [M.map_smul]
        exact (N.obj (op V)).smul_mem _ hg }
  map i _ hx := (N.toSubfunctor.sheafify J).map i hx

/-- The subpresheaf of types underlying the objectwise closure is the sheafification of the
subpresheaf of types underlying the submodule. -/
theorem toSubfunctor_sheafify (N : M.Submodule) :
    (sheafify N J).toSubfunctor = N.toSubfunctor.sheafify J :=
  rfl

/-- Membership in the objectwise closure is the covering of the sieve of arrows along which the
section restricts into the submodule. -/
theorem mem_sheafify_iff_sieveOfSection {N : M.Submodule} {X : Cᵒᵖ} {x : M.obj X} :
    x ∈ (sheafify N J).obj X ↔ N.toSubfunctor.sieveOfSection x ∈ J X.unop :=
  Iff.rfl

/-- A section lies in the objectwise closure of a submodule exactly when it restricts into the
submodule along every arrow of some covering sieve. -/
theorem mem_sheafify_iff {N : M.Submodule} {X : Cᵒᵖ} {x : M.obj X} :
    x ∈ (sheafify N J).obj X ↔
      ∃ S : Sieve X.unop, S ∈ J X.unop ∧
        ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → M.map f.op x ∈ N.obj (op Y) := by
  refine ⟨fun hx => ⟨N.toSubfunctor.sieveOfSection x, hx, fun _ _ hf => hf⟩, ?_⟩
  rintro ⟨S, hS, hx⟩
  exact J.superset_covering (fun _ f hf => hx f hf) hS

/-- A section restricting into a submodule along every arrow of a covering sieve lies in the
objectwise closure of that submodule. -/
theorem mem_sheafify_of_mem {N : M.Submodule} {X : Cᵒᵖ} {x : M.obj X} {S : Sieve X.unop}
    (hS : S ∈ J X.unop) (hx : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → M.map f.op x ∈ N.obj (op Y)) :
    x ∈ (sheafify N J).obj X :=
  mem_sheafify_iff.2 ⟨S, hS, hx⟩

/-- A submodule of a presheaf of modules is contained in its objectwise closure. -/
theorem le_sheafify (N : M.Submodule) : N ≤ sheafify N J :=
  N.toSubfunctor.le_sheafify J

/-- The objectwise closure is monotone. -/
theorem sheafify_mono {N N' : M.Submodule} (h : N ≤ N') : sheafify N J ≤ sheafify N' J :=
  fun _ _ hx => J.superset_covering (fun _ _ hf => h _ hf) hx

end Stacks.PresheafOfModules.Submodule

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{w} R}

/-- The presheaf of types underlying a sheaf of modules satisfies the sheaf condition for
type-valued presheaves. -/
theorem isSheaf_forget (M : SheafOfModules.{w} R) :
    Presieve.IsSheaf J (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{w}) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf

/-- A section of a submodule with local membership is already a section of it as soon as it
restricts into a smaller objectwise submodule along every arrow of a covering sieve. -/
theorem mem_of_sieveOfSection_mem (P : M.Submodule) {N : M.val.Submodule}
    (h : N ≤ P.toSubmodule) {X : Cᵒᵖ} {x : M.val.obj X}
    (hx : N.toSubfunctor.sieveOfSection x ∈ J X.unop) : x ∈ P.obj X :=
  P.isSheaf x (J.superset_covering (fun _ _ hf => h _ hf) hx)

/-- The closure of an objectwise submodule of a sheaf of modules: the sections lying in it
locally. Membership is local, since a section lying locally in a submodule lies locally in the
sections lying locally in it. -/
def Submodule.sheafify (N : M.val.Submodule) : M.Submodule where
  toSubmodule := Stacks.PresheafOfModules.Submodule.sheafify N J
  isSheaf _ _ hs := (N.toSubfunctor.sheafify_sheafify (isSheaf_forget M)).le _ hs

/-- The objectwise submodule underlying the closure of `N` consists of the sections lying in `N`
locally. -/
@[simp]
theorem Submodule.sheafify_toSubmodule (N : M.val.Submodule) :
    (Submodule.sheafify (M := M) N).toSubmodule =
      Stacks.PresheafOfModules.Submodule.sheafify N J :=
  rfl

/-- **The smallest submodule with local membership containing an objectwise submodule consists of
the sections lying in that objectwise submodule locally.** -/
theorem sheafifySubmodule_eq_sheafify (N : M.val.Submodule) :
    sheafifySubmodule N = Submodule.sheafify N :=
  le_antisymm (sheafifySubmodule_le (Stacks.PresheafOfModules.Submodule.le_sheafify N))
    (_root_.SheafOfModules.Submodule.le_iff.2 fun _ _ hx =>
      mem_of_sieveOfSection_mem _ (le_sheafifySubmodule N) hx)

/-- **Local membership characterizes the closure of an objectwise submodule.** A section of a
sheaf of modules lies in the smallest submodule with local membership containing an objectwise
submodule `N` exactly when it restricts into `N` along every arrow of some covering sieve. -/
theorem mem_sheafifySubmodule_iff {N : M.val.Submodule} {X : Cᵒᵖ} {x : M.val.obj X} :
    x ∈ (sheafifySubmodule N).obj X ↔
      ∃ S : Sieve X.unop, S ∈ J X.unop ∧
        ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → M.val.map f.op x ∈ N.obj (op Y) := by
  rw [sheafifySubmodule_eq_sheafify]
  exact Stacks.PresheafOfModules.Submodule.mem_sheafify_iff

/-- A section restricting into an objectwise submodule along every arrow of a covering sieve lies
in the smallest submodule with local membership containing it. -/
theorem mem_sheafifySubmodule_of_mem {N : M.val.Submodule} {X : Cᵒᵖ} {x : M.val.obj X}
    {S : Sieve X.unop} (hS : S ∈ J X.unop)
    (hx : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → M.val.map f.op x ∈ N.obj (op Y)) :
    x ∈ (sheafifySubmodule N).obj X :=
  mem_sheafifySubmodule_iff.2 ⟨S, hS, hx⟩

/-- A section of the closure of an objectwise submodule restricts into that objectwise submodule
along every arrow of some covering sieve. -/
theorem exists_sieve_of_mem_sheafifySubmodule {N : M.val.Submodule} {X : Cᵒᵖ}
    {x : M.val.obj X} (hx : x ∈ (sheafifySubmodule N).obj X) :
    ∃ S : Sieve X.unop, S ∈ J X.unop ∧
      ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → M.val.map f.op x ∈ N.obj (op Y) :=
  mem_sheafifySubmodule_iff.1 hx

/-- The inclusion of a submodule of a sheaf of modules into a larger one is the composite of the
inclusions through an intermediate submodule. -/
@[reassoc]
theorem Submodule.homOfLE_comp_homOfLE {N₁ N₂ N₃ : M.Submodule} (h₁₂ : N₁ ≤ N₂) (h₂₃ : N₂ ≤ N₃) :
    Submodule.homOfLE h₁₂ ≫ Submodule.homOfLE h₂₃ = Submodule.homOfLE (h₁₂.trans h₂₃) :=
  rfl

end Stacks.SheafOfModules

namespace Stacks.Sites

attribute [local implicit_reducible] CategoryTheory.sheafCompose

section Powers

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {O : Sheaf J CommRingCat.{u}}

/-- **The product of a sheaf of ideals with one of its powers lands in the next power.** -/
theorem idealSmul_idealPow_le_idealPow_succ (I : IdealSubsheaf O) (n : ℕ) :
    idealSmul I (idealPow I n) ≤ idealPow I (n + 1) := by
  refine Stacks.SheafOfModules.sheafifySubmodule_le (presheafIdealSmul_le I ?_)
  intro X a ha m hm
  obtain ⟨S, hS, hm⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule hm
  refine Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem hS fun Y f hf => ?_
  have h1 : (ConcreteCategory.hom
        ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val.map f.op)) (a • m)
      = (ConcreteCategory.hom (O.obj.map f.op)) a * (ConcreteCategory.hom (O.obj.map f.op)) m :=
    map_mul (ConcreteCategory.hom (O.obj.map f.op)) a m
  have h2 : sectionIdeal I (op Y) ^ (n + 1)
      = sectionIdeal I (op Y) * sectionIdeal I (op Y) ^ n := pow_succ' _ _
  rw [h1]
  exact h2.ge (Ideal.mul_mem_mul (I.map_mem f.op ha) (hm f hf))

/-- **A section of `I` times a section of `Iⁿ` is a section of `Iⁿ⁺¹`.** -/
theorem mul_mem_idealPow_succ (I : IdealSubsheaf O) (n : ℕ) {U : Cᵒᵖ}
    {a b : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U}
    (ha : a ∈ I.obj U) (hb : b ∈ (idealPow I n).obj U) :
    a * b ∈ (idealPow I (n + 1)).obj U :=
  _root_.SheafOfModules.Submodule.le_iff.1 (idealSmul_idealPow_le_idealPow_succ I n) U
    (smul_mem_idealSmul I ha hb)

/-- `I · Iⁿ` is contained in `Iⁿ`. -/
theorem idealSmul_idealPow_le_idealPow (I : IdealSubsheaf O) (n : ℕ) :
    idealSmul I (idealPow I n) ≤ idealPow I n :=
  (idealSmul_idealPow_le_idealPow_succ I n).trans (idealPow_succ_le I n)

end Powers

section GradedPiece

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (I : IdealSubsheaf.{v, u, w} X.O)

/-- The projection of `Iⁿ` onto the graded piece `Iⁿ/Iⁿ⁺¹`. -/
noncomputable def adicGradedPieceπ (n : ℕ) :
    (idealPow I n).toSheafOfModules ⟶ adicGradedPiece I n :=
  cokernel.π _

/-- The projection of `Iⁿ` onto `Iⁿ/Iⁿ⁺¹` is an epimorphism. -/
instance epi_adicGradedPieceπ (n : ℕ) : Epi (adicGradedPieceπ I n) :=
  inferInstanceAs (Epi (cokernel.π _))

/-- The sections of `Iⁿ⁺¹` die in `Iⁿ/Iⁿ⁺¹`. -/
@[reassoc (attr := simp)]
theorem homOfLE_comp_adicGradedPieceπ (n : ℕ) :
    Stacks.SheafOfModules.Submodule.homOfLE (idealPow_succ_le I n) ≫ adicGradedPieceπ I n = 0 :=
  cokernel.condition _

/-- **The graded piece `Iⁿ/Iⁿ⁺¹` is killed by `I`.** The inclusion of `I · Iⁿ` into `Iⁿ`, composed
with the projection onto `Iⁿ/Iⁿ⁺¹`, vanishes. -/
@[reassoc (attr := simp)]
theorem idealSmul_homOfLE_comp_adicGradedPieceπ (n : ℕ) :
    Stacks.SheafOfModules.Submodule.homOfLE (idealSmul_idealPow_le_idealPow I n) ≫
      adicGradedPieceπ I n = 0 := by
  rw [← Stacks.SheafOfModules.Submodule.homOfLE_comp_homOfLE
      (idealSmul_idealPow_le_idealPow_succ I n) (idealPow_succ_le I n),
    Category.assoc, homOfLE_comp_adicGradedPieceπ, comp_zero]

end GradedPiece

end Stacks.Sites

end
