module

public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tower of quotients of the structure sheaf by the powers of a sheaf of ideals

Let `I` be a sheaf of ideals on a ringed site `(C, O)`. Inside the abelian category `Mod(O)` of
sheaves of `O`-modules, the cokernel of the inclusion `Iⁿ ⊆ O` is the quotient `O/Iⁿ`, and the
third isomorphism theorem applied to `Iⁿ⁺¹ ⊆ Iⁿ ⊆ O` presents these quotients as a tower of
short exact sequences `0 → Iⁿ/Iⁿ⁺¹ → O/Iⁿ⁺¹ → O/Iⁿ → 0`.

## Main definitions

* `Stacks.Abelian.cokernelCompShortComplex`: for composable morphisms `u : A ⟶ B` and
  `v : B ⟶ M` in an abelian category, the short complex `0 → B/A → M/A → M/B → 0`.
* `Stacks.SheafOfModules.Submodule.homOfLE`: the inclusion of one submodule of a sheaf of
  modules into a larger one.
* `Stacks.Sites.adicQuotientModule`: the sheaf of modules `O/Iⁿ`.
* `Stacks.Sites.adicQuotientModuleMap`: the transition map `O/Iⁿ ⟶ O/Iᵐ` for `m ≤ n`.
* `Stacks.Sites.adicGradedPiece`: the graded piece `Iⁿ/Iⁿ⁺¹`.
* `Stacks.Sites.adicQuotientShortComplex`: the short complex
  `0 → Iⁿ/Iⁿ⁺¹ → O/Iⁿ⁺¹ → O/Iⁿ → 0`.

## Main results

* `Stacks.Abelian.cokernelCompShortComplex_shortExact`: the third isomorphism theorem, namely
  that `0 → B/A → M/A → M/B → 0` is short exact for composable monomorphisms.
* `Stacks.Sites.adicQuotientShortComplex_shortExact`: every stage of the tower is short exact.
* `Stacks.Sites.adicQuotientShortComplexX₂Iso` and
  `Stacks.Sites.adicQuotientShortComplexX₃Iso`: the middle and right terms of the `n`-th stage
  are `O/Iⁿ⁺¹` and `O/Iⁿ`.

## Implementation notes

The quotient `O/Iⁿ` is formed in `Mod(O)`, as the cokernel of the inclusion of the submodule
`Iⁿ` of the free rank-one sheaf of modules, and not as the sheafification of the objectwise
quotient *ring*; that keeps the whole tower inside one abelian category and avoids comparing
sheafification in `CommRingCat` with sheafification in `AddCommGrpCat`.

The exactness of a stage is an instance of the third isomorphism theorem, which is proved here
for an abelian category: the right-hand map exhibits `M/B` as a cokernel of `B/A ⟶ M/A`, which
gives exactness and the surjectivity, while injectivity of `B/A ⟶ M/A` is obtained by pulling a
morphism into `B/A` back along the epimorphism `B ⟶ B/A` and lifting it through the
monomorphism `A ⟶ M`.

The middle and right terms of the `n`-th stage are presented through isomorphisms with
`O/Iⁿ⁺¹` and `O/Iⁿ` rather than being those objects on the nose: the middle term is the cokernel
of the composite `Iⁿ⁺¹ ⟶ Iⁿ ⟶ O`, which is the inclusion of `Iⁿ⁺¹` only after a rewrite.

Sheaves of ideals on a ringed site are the submodules of its free rank-one sheaf of modules, so
naming their type requires the structure sheaf to be readable as a sheaf of not necessarily
commutative rings, that is `AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`. That
holds for every ringed site and is supplied here as a section-local instance; it is needed only
to write the type of a sheaf of ideals down, not to use any result below.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w u₁ v₁

namespace Stacks.Abelian

variable {D : Type u} [Category.{v} D] [Abelian D] {A B M : D}

/-- The map `B/A ⟶ M/A` induced by `v : B ⟶ M`, between the cokernels of `u : A ⟶ B` and of the
composite `u ≫ v`. -/
def cokernelCompι (u : A ⟶ B) (v : B ⟶ M) : cokernel u ⟶ cokernel (u ≫ v) :=
  cokernel.desc u (v ≫ cokernel.π (u ≫ v)) (by rw [← Category.assoc, cokernel.condition])

/-- The projection `B ⟶ B/A` followed by `B/A ⟶ M/A` is `v` followed by the projection
`M ⟶ M/A`. -/
@[reassoc (attr := simp)]
lemma π_comp_cokernelCompι (u : A ⟶ B) (v : B ⟶ M) :
    cokernel.π u ≫ cokernelCompι u v = v ≫ cokernel.π (u ≫ v) :=
  cokernel.π_desc _ _ _

/-- The map `M/A ⟶ M/B` between the cokernels of `u ≫ v` and of `v : B ⟶ M`. -/
def cokernelCompπ (u : A ⟶ B) (v : B ⟶ M) : cokernel (u ≫ v) ⟶ cokernel v :=
  cokernel.desc (u ≫ v) (cokernel.π v) (by rw [Category.assoc, cokernel.condition, comp_zero])

/-- The projection `M ⟶ M/A` followed by `M/A ⟶ M/B` is the projection `M ⟶ M/B`. -/
@[reassoc (attr := simp)]
lemma π_comp_cokernelCompπ (u : A ⟶ B) (v : B ⟶ M) :
    cokernel.π (u ≫ v) ≫ cokernelCompπ u v = cokernel.π v :=
  cokernel.π_desc _ _ _

/-- The composite `B/A ⟶ M/A ⟶ M/B` vanishes. -/
@[simp]
lemma cokernelCompι_comp_cokernelCompπ (u : A ⟶ B) (v : B ⟶ M) :
    cokernelCompι u v ≫ cokernelCompπ u v = 0 := by
  rw [← cancel_epi (cokernel.π u)]
  simp

/-- The map `M/A ⟶ M/B` is an epimorphism. -/
instance epi_cokernelCompπ (u : A ⟶ B) (v : B ⟶ M) : Epi (cokernelCompπ u v) :=
  epi_of_epi_fac (π_comp_cokernelCompπ u v)

/-- For monomorphisms `u : A ⟶ B` and `v : B ⟶ M`, the map `B/A ⟶ M/A` is a monomorphism. -/
instance mono_cokernelCompι (u : A ⟶ B) (v : B ⟶ M) [Mono u] [Mono v] :
    Mono (cokernelCompι u v) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T t ht
  refine zero_of_epi_comp (pullback.snd (cokernel.π u) t) ?_
  have h₁ : (pullback.fst (cokernel.π u) t ≫ v) ≫ cokernel.π (u ≫ v) = 0 := by
    rw [Category.assoc, ← π_comp_cokernelCompι, ← Category.assoc, pullback.condition,
      Category.assoc, ht, comp_zero]
  have hk := _root_.CategoryTheory.Abelian.monoLift_comp (u ≫ v) _ h₁
  have h₂ : _root_.CategoryTheory.Abelian.monoLift (u ≫ v) _ h₁ ≫ u
      = pullback.fst (cokernel.π u) t := by
    rw [← cancel_mono v, Category.assoc, hk]
  rw [← pullback.condition, ← h₂, Category.assoc, cokernel.condition, comp_zero]

/-- **The quotient of a quotient.** For composable morphisms `u : A ⟶ B` and `v : B ⟶ M` in an
abelian category, the short complex `0 → B/A → M/A → M/B → 0` of cokernels. -/
def cokernelCompShortComplex (u : A ⟶ B) (v : B ⟶ M) : ShortComplex D :=
  ShortComplex.mk (cokernelCompι u v) (cokernelCompπ u v)
    (cokernelCompι_comp_cokernelCompπ u v)

/-- The left-hand term of `cokernelCompShortComplex u v` is `B/A`. -/
@[simp]
lemma cokernelCompShortComplex_X₁ (u : A ⟶ B) (v : B ⟶ M) :
    (cokernelCompShortComplex u v).X₁ = cokernel u := rfl

/-- The middle term of `cokernelCompShortComplex u v` is `M/A`. -/
@[simp]
lemma cokernelCompShortComplex_X₂ (u : A ⟶ B) (v : B ⟶ M) :
    (cokernelCompShortComplex u v).X₂ = cokernel (u ≫ v) := rfl

/-- The right-hand term of `cokernelCompShortComplex u v` is `M/B`. -/
@[simp]
lemma cokernelCompShortComplex_X₃ (u : A ⟶ B) (v : B ⟶ M) :
    (cokernelCompShortComplex u v).X₃ = cokernel v := rfl

/-- The first map of `cokernelCompShortComplex u v` is `cokernelCompι u v`. -/
@[simp]
lemma cokernelCompShortComplex_f (u : A ⟶ B) (v : B ⟶ M) :
    (cokernelCompShortComplex u v).f = cokernelCompι u v := rfl

/-- The second map of `cokernelCompShortComplex u v` is `cokernelCompπ u v`. -/
@[simp]
lemma cokernelCompShortComplex_g (u : A ⟶ B) (v : B ⟶ M) :
    (cokernelCompShortComplex u v).g = cokernelCompπ u v := rfl

/-- `M/B` is a cokernel of `B/A ⟶ M/A`: a map out of `M/A` killing the image of `B/A` is the
same thing as a map out of `M` killing `B`. -/
def isColimitCokernelCoforkCokernelCompι (u : A ⟶ B) (v : B ⟶ M) :
    IsColimit (CokernelCofork.ofπ (cokernelCompπ u v)
      (cokernelCompι_comp_cokernelCompπ u v)) :=
  CokernelCofork.IsColimit.ofπ' _ _ fun k hk =>
    ⟨cokernel.desc v (cokernel.π (u ≫ v) ≫ k) (by
        rw [← Category.assoc, ← π_comp_cokernelCompι, Category.assoc, hk, comp_zero]), by
      rw [← cancel_epi (cokernel.π (u ≫ v)), ← Category.assoc, π_comp_cokernelCompπ,
        cokernel.π_desc]⟩

/-- **The third isomorphism theorem.** For composable monomorphisms `u : A ⟶ B` and `v : B ⟶ M`
in an abelian category, the sequence `0 → B/A → M/A → M/B → 0` is short exact. -/
lemma cokernelCompShortComplex_shortExact (u : A ⟶ B) (v : B ⟶ M) [Mono u] [Mono v] :
    (cokernelCompShortComplex u v).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (isColimitCokernelCoforkCokernelCompι u v))
    (inferInstanceAs (Mono (cokernelCompι u v)))
    (inferInstanceAs (Epi (cokernelCompπ u v)))

end Stacks.Abelian

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : _root_.SheafOfModules.{v} R}

/-- The inclusion of a submodule of a sheaf of modules into a larger one. -/
def Submodule.homOfLE {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    N₁.toSheafOfModules ⟶ N₂.toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE (_root_.SheafOfModules.Submodule.le_iff.1 h)⟩

/-- The underlying morphism of presheaves of modules of `Submodule.homOfLE h` is the inclusion
of the corresponding presheaves of submodules. -/
@[simp]
lemma Submodule.homOfLE_val {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    (Submodule.homOfLE h).val =
      PresheafOfModules.Submodule.homOfLE (_root_.SheafOfModules.Submodule.le_iff.1 h) :=
  rfl

/-- The inclusion of a smaller submodule is the inclusion of the larger one precomposed with the
inclusion between them. -/
@[reassoc (attr := simp)]
lemma Submodule.homOfLE_comp_ι {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    Submodule.homOfLE h ≫ N₂.ι = N₁.ι :=
  rfl

/-- The inclusion of a submodule of a sheaf of modules into a larger one is a monomorphism. -/
instance Submodule.mono_homOfLE {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    Mono (Submodule.homOfLE h) :=
  (_root_.SheafOfModules.forget R).mono_of_mono_map
    (inferInstanceAs (Mono (PresheafOfModules.Submodule.homOfLE
      (_root_.SheafOfModules.Submodule.le_iff.1 h))))

end Stacks.SheafOfModules

namespace Stacks.Sites

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (I : IdealSubsheaf.{v, u, w} X.O)

/-- The sheaf of `O`-modules `O/Iⁿ`: the cokernel, in sheaves of `O`-modules, of the inclusion of
the `n`-th power of a sheaf of ideals into the free rank-one sheaf of modules. -/
def adicQuotientModule (n : ℕ) : RingedSite.Modules X :=
  cokernel (idealPow I n).ι

/-- The projection of the structure sheaf onto `O/Iⁿ`. -/
def adicQuotientModuleπ (n : ℕ) :
    _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
      adicQuotientModule I n :=
  cokernel.π _

/-- The projection of the structure sheaf onto `O/Iⁿ` is an epimorphism. -/
instance epi_adicQuotientModuleπ (n : ℕ) : Epi (adicQuotientModuleπ I n) :=
  inferInstanceAs (Epi (cokernel.π _))

/-- The sections of `Iⁿ` die in `O/Iⁿ`. -/
@[reassoc (attr := simp)]
lemma ι_comp_adicQuotientModuleπ (n : ℕ) :
    (idealPow I n).ι ≫ adicQuotientModuleπ I n = 0 :=
  cokernel.condition _

/-- For `m ≤ n`, the transition map `O/Iⁿ ⟶ O/Iᵐ` of the tower of quotients of the structure
sheaf by the powers of a sheaf of ideals. -/
def adicQuotientModuleMap {m n : ℕ} (h : m ≤ n) :
    adicQuotientModule I n ⟶ adicQuotientModule I m :=
  cokernel.desc (idealPow I n).ι (adicQuotientModuleπ I m) (by
    rw [← Stacks.SheafOfModules.Submodule.homOfLE_comp_ι (idealPow_antitone I h),
      Category.assoc, ι_comp_adicQuotientModuleπ, comp_zero])

/-- The transition maps of the tower are compatible with the projections from the structure
sheaf. -/
@[reassoc (attr := simp)]
lemma adicQuotientModuleπ_comp_adicQuotientModuleMap {m n : ℕ} (h : m ≤ n) :
    adicQuotientModuleπ I n ≫ adicQuotientModuleMap I h = adicQuotientModuleπ I m :=
  cokernel.π_desc _ _ _

/-- The graded piece `Iⁿ/Iⁿ⁺¹` of the filtration of the structure sheaf by the powers of a sheaf
of ideals. -/
@[ega "0 15.2.1" "partial", ega "IV 16.1.2" "partial", sga "1 III 6.9"]
def adicGradedPiece (n : ℕ) : RingedSite.Modules X :=
  cokernel (Stacks.SheafOfModules.Submodule.homOfLE (idealPow_succ_le I n))

/-- The `n`-th stage `0 → Iⁿ/Iⁿ⁺¹ → O/Iⁿ⁺¹ → O/Iⁿ → 0` of the tower of quotients of the
structure sheaf by the powers of a sheaf of ideals. -/
def adicQuotientShortComplex (n : ℕ) : ShortComplex (RingedSite.Modules X) :=
  Stacks.Abelian.cokernelCompShortComplex
    (Stacks.SheafOfModules.Submodule.homOfLE (idealPow_succ_le I n)) (idealPow I n).ι

/-- **Every stage of the tower is short exact.** -/
lemma adicQuotientShortComplex_shortExact (n : ℕ) :
    (adicQuotientShortComplex I n).ShortExact :=
  Stacks.Abelian.cokernelCompShortComplex_shortExact _ _

/-- The left-hand term of the `n`-th stage of the tower is the graded piece `Iⁿ/Iⁿ⁺¹`. -/
def adicQuotientShortComplexX₁Iso (n : ℕ) :
    (adicQuotientShortComplex I n).X₁ ≅ adicGradedPiece I n :=
  Iso.refl _

/-- The middle term of the `n`-th stage of the tower is `O/Iⁿ⁺¹`. -/
def adicQuotientShortComplexX₂Iso (n : ℕ) :
    (adicQuotientShortComplex I n).X₂ ≅ adicQuotientModule I (n + 1) :=
  cokernelIsoOfEq (Stacks.SheafOfModules.Submodule.homOfLE_comp_ι (idealPow_succ_le I n))

/-- The right-hand term of the `n`-th stage of the tower is `O/Iⁿ`. -/
def adicQuotientShortComplexX₃Iso (n : ℕ) :
    (adicQuotientShortComplex I n).X₃ ≅ adicQuotientModule I n :=
  Iso.refl _

end Stacks.Sites

end
