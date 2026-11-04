module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Pro-isomorphic systems of differential graded modules have the same derived limit of tensor
products

Let `(A_n)` be an inverse system of differential graded algebras over a commutative ring `R`, let
`(N_n)` and `(N'_n)` be two inverse systems of left differential graded modules over it, and let
`(M_n)` be an inverse system of right differential graded `A_n`-modules carrying a commuting
action of a differential graded algebra `B`. If `(N_n)` and `(N'_n)` are *pro-isomorphic in the
derived category* — there are a strictly increasing sequence of indices `n₀ < n₁ < n₂ < ⋯` and
maps `N_{n_{2i}} ⟶ N'_{n_{2i-1}}` in `D(A_{n_{2i}}^{opp}, d)` and `N'_{n_{2i+1}} ⟶ N_{n_{2i}}` in
`D(A_{n_{2i+1}}^{opp}, d)` whose composites are the transition maps of the two systems — then the
two towers `n ↦ M_n ⊗^𝐋_{A_n} N_n` and `n ↦ M_n ⊗^𝐋_{A_n} N'_n` of `D(B, d)` are isomorphic as
pro-objects, and therefore have the same derived limit.

The content is the passage from the first pro-isomorphism to the second: a map of the systems of
modules over one algebra of the system is turned into a map of the tensored objects by the
derived tensor product of Tag 09LS, and the two composition conditions become the two
composition conditions of an interleaving of the tensored towers. The comparison of derived
limits is then Tag 0H9L.

## Main definitions

* `DifferentialGraded.AlgebraSystem`: an inverse system of differential graded algebras, together
  with the identification of a two-step restriction of scalars with a one-step one.
* `DifferentialGraded.ModuleSystem`: an inverse system of left differential graded modules over
  such a system, levelwise in the derived category.
* `DifferentialGraded.BimoduleSystem`: an inverse system of bimodules `(M_n)` over such a system,
  together with the comparison maps `M_m ⊗^𝐋_{A_m} X|_{A_m} ⟶ M_n ⊗^𝐋_{A_n} X` its transition
  maps induce.
* `DifferentialGraded.BimoduleSystem.tower`: the tower `n ↦ M_n ⊗^𝐋_{A_n} N_n` in `D(B, d)`.
* `DifferentialGraded.ProIsoDerived`: two systems of modules are pro-isomorphic in the derived
  category.

## Main results

* `DifferentialGraded.ProIsoDerived.interleaving` and
  `DifferentialGraded.ProIsoDerived.proIso`: a pro-isomorphism of the systems of modules induces
  an interleaving, hence a pro-isomorphism, of the tensored towers in `D(B, d)`. This is the
  content of Tag 0GZI.
* `DifferentialGraded.nonempty_iso_of_proIsoDerived`: **Stacks 0GZI**, the derived limits of the
  two tensored towers are isomorphic.

## Implementation notes

*Left modules are right modules over the opposite algebra.* The development's
`DifferentialGradedModule` is a right module, so the `n`-th algebra of the system is recorded by
its opposite: `DifferentialGraded.AlgebraSystem.alg n` is the source's `A_n^{opp}`, a left
differential graded `A_n`-module is an object of
`DifferentialGradedModule.derivedCategory' (A_n^{opp})` — the source's `D(A_n^{opp}, d)`, which is
where it writes the maps of the pro-isomorphism — and the source's `M_n`, a right differential
graded `A_n`-module with a commuting `B`-action, is a differential graded
`(A_n^{opp}, B)`-bimodule. The source's `M_n ⊗^𝐋_{A_n} N_n` is accordingly the derived tensor
product of Tag 09LS of the bimodule `M_n` with the module `N_n`, which is the variance in which
that functor is available: it varies the module and fixes the bimodule, and it is the module that
the hypothesis moves.

*How the system `(M_n)` is carried.* The conclusion uses `(M_n)` only through the functors
`M_n ⊗^𝐋_{A_n} -` and through the maps `M_m ⊗^𝐋_{A_m} X|_{A_m} ⟶ M_n ⊗^𝐋_{A_n} X` that its
transition maps induce, naturally in `X`; those maps are therefore the data of
`DifferentialGraded.BimoduleSystem`, subject to the one compatibility
`DifferentialGraded.BimoduleSystem.cmp_trans` that says they compose. This is what the source's
"for every object `(M_n)` of `D(ℕ, A)`" amounts to here, since a derived category of inverse
systems of differential graded modules is not available; every such object gives this data, so
the lemma below applies to all of them. Such a system is produced from bimodules with semilinear
transition homomorphisms by
`DifferentialGraded.StrictBimoduleSystem.toBimoduleSystem`, whose comparison maps are the derived
comparisons of the plain ones; `Koszul.powRegularBimoduleSystem` is an instance of it over the
Koszul algebras.

*The transitions of the system of algebras enter through restriction of scalars.* A homomorphism
`A_m → A_n` of differential graded algebras induces
`DifferentialGradedModule.derivedRestriction` on derived categories, and that is the only way the
transitions are used. The identification of the restriction along a composite with the composite
of the restrictions is data (`DifferentialGraded.AlgebraSystem.restrComp`): it holds for genuine
restriction of scalars, but the development does not provide it, and nothing below needs more
than its existence. For the same reason no composition of homomorphisms of differential graded
algebras is asked of the system; the transition maps are given for every pair of indices and
their compatibility is exactly `restrComp`.

*The two systems are compared only over strictly increasing index pairs.* Stacks' sequence
`n₀ < n₁ < ⋯` is strictly increasing, so every transition map that occurs below is over a
strictly positive gap, and the tower is built from its one-step maps by
`CategoryTheory.Functor.ofOpSequence`. No identity axiom is therefore needed of the restriction
functors or of the comparison maps.

*The conclusion is non-canonical.* Tag 0H9L produces an isomorphism of derived limits that is not
canonical, and a derived limit is a predicate rather than a construction; the conclusion is
accordingly `Nonempty (K ≅ K')` for any two derived limits `K`, `K'` of the two towers, which is
what makes it independent of a choice.

*The target.* `D(B, d)` for a differential graded algebra `B` over `R`; the source's `D(R)` is the
case of `B` concentrated in degree zero with `B^0 = R`.

## References

* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI)
* [Stacks Project, Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L)
* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS)
-/

section

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGraded

open DifferentialGradedModule

universe u

/-- **An inverse system of differential graded algebras.** The `n`-th entry is recorded by its
opposite `A_n^{opp}`, so that the source's left differential graded `A_n`-modules are the objects
of `D(A_n^{opp}, d)`; the transitions `A_m → A_n` for `n ≤ m` are given for every pair of
indices, and the compatibility between them is recorded through the restriction functors they
induce on derived categories. -/
structure AlgebraSystem (R : Type u) [CommRing R] where
  /-- The opposite `A_n^{opp}` of the `n`-th differential graded algebra of the system. -/
  alg : ℕ → DifferentialGradedAlgebra.{u, u} R
  /-- The transition homomorphism `A_m → A_n` of the system, for `n ≤ m`. -/
  trans : ∀ {n m : ℕ}, n ≤ m → (alg m).Hom (alg n)
  /-- Restricting along `A_m → A_n` and then along `A_k → A_m` is restricting along the
  transition `A_k → A_n`. -/
  restrComp : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k),
    derivedRestriction (trans h) ⋙ derivedRestriction (trans h') ≅
      derivedRestriction (trans (h.trans h'))

namespace AlgebraSystem

variable {R : Type u} [CommRing R]

/-- Restriction of scalars along the transition `A_m → A_n`: a left differential graded
`A_n`-module, read as a left differential graded `A_m`-module. -/
abbrev restr (S : AlgebraSystem R) {n m : ℕ} (h : n ≤ m) :
    derivedCategory' (S.alg n) ⥤ derivedCategory' (S.alg m) :=
  derivedRestriction (S.trans h)

end AlgebraSystem

variable {R : Type u} [CommRing R]

/-- **An inverse system of left differential graded modules** over an inverse system of
differential graded algebras: an object `N_n` of `D(A_n^{opp}, d)` for every `n`, together with
transition maps `N_m ⟶ N_n|_{A_m}`, compatible with composition. This is the source's sheaf of
differential graded `A`-modules on the site `ℕ`, read in the derived category at each level. -/
structure ModuleSystem (S : AlgebraSystem R) where
  /-- The object `N_n` of `D(A_n^{opp}, d)`. -/
  obj : ∀ n : ℕ, derivedCategory' (S.alg n)
  /-- The transition map `N_m ⟶ N_n|_{A_m}`, a map of left differential graded
  `A_m`-modules. -/
  trans : ∀ {n m : ℕ} (h : n ≤ m), obj m ⟶ (S.restr h).obj (obj n)
  /-- The transition maps compose. -/
  trans_trans : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k),
    trans (h.trans h') =
      trans h' ≫ (S.restr h').map (trans h) ≫ (S.restrComp h h').hom.app (obj n)

/-- **An inverse system of differential graded bimodules** over an inverse system of differential
graded algebras: the source's system `(M_n)` of right differential graded `A_n`-modules with a
commuting action of `B`, carried through the comparison maps
`M_m ⊗^𝐋_{A_m} X|_{A_m} ⟶ M_n ⊗^𝐋_{A_n} X` that its transition maps induce. -/
structure BimoduleSystem (S : AlgebraSystem R) (B : DifferentialGradedAlgebra.{u, u} R) where
  /-- The bimodule `M_n`, a right differential graded `A_n`-module with a commuting action
  of `B`. -/
  obj : ∀ n : ℕ, Bimodule (S.alg n) B
  /-- The comparison `M_m ⊗^𝐋_{A_m} X|_{A_m} ⟶ M_n ⊗^𝐋_{A_n} X` induced by the transition map
  `M_m ⟶ M_n`, natural in the left differential graded `A_n`-module `X`. -/
  cmp : ∀ {n m : ℕ} (h : n ≤ m),
    S.restr h ⋙ Bimodule.derivedTensorFunctor (obj m) ⟶ Bimodule.derivedTensorFunctor (obj n)
  /-- The comparison maps compose, over the identification of a two-step restriction of scalars
  with a one-step one. -/
  cmp_trans : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (X : derivedCategory' (S.alg n)),
    (Bimodule.derivedTensorFunctor (obj k)).map ((S.restrComp h h').hom.app X) ≫
        (cmp (h.trans h')).app X =
      (cmp h').app ((S.restr h).obj X) ≫ (cmp h).app X

namespace BimoduleSystem

variable {S : AlgebraSystem R} {B : DifferentialGradedAlgebra.{u, u} R} (M : BimoduleSystem S B)

/-- The derived tensor product `M_n ⊗^𝐋_{A_n} - : D(A_n^{opp}, d) ⥤ D(B, d)` with the `n`-th
bimodule of the system. -/
abbrev tensor (n : ℕ) : derivedCategory' (S.alg n) ⥤ derivedCategory' B :=
  Bimodule.derivedTensorFunctor (M.obj n)

/-- The transition map `M_m ⊗^𝐋_{A_m} N_m ⟶ M_n ⊗^𝐋_{A_n} N_n` of the tensored tower: tensor the
transition map of the system of modules, then compare along the transition map of the system of
bimodules. -/
def towerMap (N : ModuleSystem S) {n m : ℕ} (h : n ≤ m) :
    (M.tensor m).obj (N.obj m) ⟶ (M.tensor n).obj (N.obj n) :=
  (M.tensor m).map (N.trans h) ≫ (M.cmp h).app (N.obj n)

/-- Tensoring two composable maps and comparing along the transitions of `(M_n)` is the same as
tensoring their composite and comparing along the composite transition. -/
private theorem tensor_cmp_comp {N N' : ModuleSystem S} {c b a : ℕ} (hcb : c ≤ b) (hba : b ≤ a)
    (f : N.obj a ⟶ (S.restr hba).obj (N'.obj b))
    (g : N'.obj b ⟶ (S.restr hcb).obj (N.obj c)) :
    ((M.tensor a).map f ≫ (M.cmp hba).app (N'.obj b)) ≫
        ((M.tensor b).map g ≫ (M.cmp hcb).app (N.obj c)) =
      (M.tensor a).map (f ≫ (S.restr hba).map g ≫ (S.restrComp hcb hba).hom.app (N.obj c)) ≫
        (M.cmp (hcb.trans hba)).app (N.obj c) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [M.cmp_trans hcb hba (N.obj c), reassoc_of% ((M.cmp hba).naturality g)]

/-- The transition maps of the tensored tower compose. -/
theorem towerMap_trans (N : ModuleSystem S) {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    M.towerMap N (h.trans h') = M.towerMap N h' ≫ M.towerMap N h := by
  rw [towerMap, N.trans_trans h h']
  exact (M.tensor_cmp_comp h h' _ _).symm

/-- **The tensored tower** `n ↦ M_n ⊗^𝐋_{A_n} N_n`, an inverse system in `D(B, d)`. Its derived
limit is the source's `R lim (M_n ⊗^𝐋_{A_n} N_n)`. -/
def tower (N : ModuleSystem S) : ℕᵒᵖ ⥤ derivedCategory' B :=
  Functor.ofOpSequence (X := fun n => (M.tensor n).obj (N.obj n))
    fun n => M.towerMap N (Nat.le_succ n)

/-- The objects of the tensored tower are the tensor products. -/
@[simp] theorem tower_obj (N : ModuleSystem S) (n : ℕ) :
    (M.tower N).obj (op n) = (M.tensor n).obj (N.obj n) := rfl

/-- The one-step transition map of the tensored tower is the one-step map
`DifferentialGraded.BimoduleSystem.towerMap`. -/
theorem tr_tower_succ (N : ModuleSystem S) (n : ℕ) :
    InverseSequence.tr (M.tower N) (Nat.le_succ n) = M.towerMap N (Nat.le_succ n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The transition maps of the tensored tower, over a strictly positive gap, are the maps
`DifferentialGraded.BimoduleSystem.towerMap`. -/
theorem tr_tower (N : ModuleSystem S) {n m : ℕ} (h : n < m) :
    InverseSequence.tr (M.tower N) h.le = M.towerMap N h.le := by
  have key : ∀ (k : ℕ) (hk : n + 1 ≤ k),
      InverseSequence.tr (M.tower N) (Nat.le_of_succ_le hk) =
        M.towerMap N (Nat.le_of_succ_le hk) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact M.tr_tower_succ N n
    | succ j hj ih =>
        rw [← InverseSequence.ProIso.tr_trans (M.tower N) (Nat.le_of_succ_le hj) (Nat.le_succ j),
          ih, M.tr_tower_succ N j]
        exact (M.towerMap_trans N (Nat.le_of_succ_le hj) (Nat.le_succ j)).symm
  exact key m h

/-- Tensoring a map `N_a ⟶ N'_b|_{A_a}` and a map `N'_b ⟶ N_c|_{A_b}` whose composite is the
transition map `N_a ⟶ N_c|_{A_a}`, and comparing along the transition maps of `(M_n)`, gives the
transition map of the tensored tower. -/
theorem tensor_comp_cmp {N N' : ModuleSystem S} {c b a : ℕ} (hcb : c ≤ b) (hba : b ≤ a)
    (f : N.obj a ⟶ (S.restr hba).obj (N'.obj b))
    (g : N'.obj b ⟶ (S.restr hcb).obj (N.obj c))
    (hfg : f ≫ (S.restr hba).map g ≫ (S.restrComp hcb hba).hom.app (N.obj c) =
      N.trans (hcb.trans hba)) :
    ((M.tensor a).map f ≫ (M.cmp hba).app (N'.obj b)) ≫
        ((M.tensor b).map g ≫ (M.cmp hcb).app (N.obj c)) =
      M.towerMap N (hcb.trans hba) := by
  rw [towerMap, ← hfg]
  exact M.tensor_cmp_comp hcb hba f g

end BimoduleSystem

/-! ### The index steps of a pro-isomorphism

The four inequalities between the indices `2i`, `2i + 1`, `2i + 2` and `2(i + 1) + 1` that the
alternating maps of a pro-isomorphism in the derived category are indexed by. The two one-step
inequalities are `Nat.le_succ` with both indices given explicitly, so that they are literally
`2 * i + 1` and `2 * i + 2` rather than `Nat.succ (2 * i + 1)`; the two-step ones are named rather
than proved inline in `DifferentialGraded.ProIsoDerived`. Either way a construction of such a
pro-isomorphism can spell the transition maps of its two systems with exactly the terms the
structure uses: the components of `DifferentialGraded.AlgebraSystem.restrComp` occurring in the
two composition identities are produced by a universal property, so two spellings of one of them
are not decided definitionally in reasonable time, and the only cheap decision is that they are
the same term. -/

/-- Two steps from an even index. -/
theorem proIsoIdx_even_le_even (i : ℕ) : 2 * i ≤ 2 * i + 2 := Nat.le_add_right _ _

/-- Two steps from an odd index. -/
theorem proIsoIdx_odd_le_odd (i : ℕ) : 2 * i + 1 ≤ 2 * (i + 1) + 1 := by omega

/-- **Pro-isomorphic in the derived category.** Two inverse systems `(N_n)` and `(N'_n)` of left
differential graded modules over an inverse system `(A_n)` of differential graded algebras are
pro-isomorphic in the derived category if there are a strictly increasing sequence of indices
`n₀ < n₁ < n₂ < ⋯` and maps `N_{n_{2i+2}} ⟶ N'_{n_{2i+1}}` in `D(A_{n_{2i+2}}^{opp}, d)` and
`N'_{n_{2i+1}} ⟶ N_{n_{2i}}` in `D(A_{n_{2i+1}}^{opp}, d)` such that the composites
`N_{n_{2i+2}} ⟶ N'_{n_{2i+1}} ⟶ N_{n_{2i}}` and `N'_{n_{2i+3}} ⟶ N_{n_{2i+2}} ⟶ N'_{n_{2i+1}}`
are the transition maps of the two systems. -/
structure ProIsoDerived {S : AlgebraSystem R} (N N' : ModuleSystem S) where
  /-- The sequence of indices `n₀ < n₁ < n₂ < ⋯`. -/
  idx : ℕ → ℕ
  /-- The sequence of indices is strictly increasing. -/
  idx_strictMono : StrictMono idx
  /-- The map `N_{n_{2i+2}} ⟶ N'_{n_{2i+1}}` of left differential graded
  `A_{n_{2i+2}}`-modules. -/
  fwd (i : ℕ) : N.obj (idx (2 * i + 2)) ⟶
    (S.restr (idx_strictMono.monotone (a := 2 * i + 1) (b := 2 * i + 2) (Nat.le_succ _))).obj
      (N'.obj (idx (2 * i + 1)))
  /-- The map `N'_{n_{2i+1}} ⟶ N_{n_{2i}}` of left differential graded
  `A_{n_{2i+1}}`-modules. -/
  bwd (i : ℕ) : N'.obj (idx (2 * i + 1)) ⟶
    (S.restr (idx_strictMono.monotone (a := 2 * i) (b := 2 * i + 1) (Nat.le_succ _))).obj
      (N.obj (idx (2 * i)))
  /-- The composite `N_{n_{2i+2}} ⟶ N'_{n_{2i+1}} ⟶ N_{n_{2i}}` is the transition map of
  `(N_n)`. -/
  fwd_bwd (i : ℕ) :
    fwd i ≫ (S.restr (idx_strictMono.monotone (a := 2 * i + 1) (b := 2 * i + 2)
          (Nat.le_succ _))).map (bwd i) ≫
        (S.restrComp (idx_strictMono.monotone (a := 2 * i) (b := 2 * i + 1) (Nat.le_succ _))
          (idx_strictMono.monotone (a := 2 * i + 1) (b := 2 * i + 2) (Nat.le_succ _))).hom.app
          (N.obj (idx (2 * i))) =
      N.trans (idx_strictMono.monotone (proIsoIdx_even_le_even i))
  /-- The composite `N'_{n_{2i+3}} ⟶ N_{n_{2i+2}} ⟶ N'_{n_{2i+1}}` is the transition map of
  `(N'_n)`. -/
  bwd_fwd (i : ℕ) :
    bwd (i + 1) ≫
        (S.restr (idx_strictMono.monotone (a := 2 * (i + 1)) (b := 2 * (i + 1) + 1)
          (Nat.le_succ _))).map (fwd i) ≫
        (S.restrComp (idx_strictMono.monotone (a := 2 * i + 1) (b := 2 * i + 2) (Nat.le_succ _))
          (idx_strictMono.monotone (a := 2 * (i + 1)) (b := 2 * (i + 1) + 1)
            (Nat.le_succ _))).hom.app
          (N'.obj (idx (2 * i + 1))) =
      N'.trans (idx_strictMono.monotone (proIsoIdx_odd_le_odd i))

namespace ProIsoDerived

variable {S : AlgebraSystem R} {B : DifferentialGradedAlgebra.{u, u} R}
  {N N' : ModuleSystem S} (p : ProIsoDerived N N') (M : BimoduleSystem S B)

/-- **The tensored towers are interleaved.** This is the content of Tag 0GZI: the maps of the
systems of modules, tensored with `(M_n)`, are interleaved maps of the towers
`n ↦ M_n ⊗^𝐋_{A_n} N_n` and `n ↦ M_n ⊗^𝐋_{A_n} N'_n` in `D(B, d)`. -/
def interleaving : InverseSequence.ProIso.Interleaving (M.tower N) (M.tower N') where
  idx := p.idx
  idx_strictMono := p.idx_strictMono
  fwd i := (M.tensor (p.idx (2 * i + 2))).map (p.fwd i) ≫
    (M.cmp (p.idx_strictMono.monotone (show 2 * i + 1 ≤ 2 * i + 2 by omega))).app
      (N'.obj (p.idx (2 * i + 1)))
  bwd i := (M.tensor (p.idx (2 * i + 1))).map (p.bwd i) ≫
    (M.cmp (p.idx_strictMono.monotone (show 2 * i ≤ 2 * i + 1 by omega))).app
      (N.obj (p.idx (2 * i)))
  fwd_bwd i := by
    rw [M.tr_tower N (p.idx_strictMono (show 2 * i < 2 * i + 2 by omega))]
    exact M.tensor_comp_cmp _ _ (p.fwd i) (p.bwd i) (p.fwd_bwd i)
  bwd_fwd i := by
    rw [M.tr_tower N' (p.idx_strictMono (show 2 * i + 1 < 2 * (i + 1) + 1 by omega))]
    exact M.tensor_comp_cmp _ _ (p.bwd (i + 1)) (p.fwd i) (p.bwd_fwd i)

/-- **The tensored towers are pro-isomorphic.** The pro-isomorphism of
`n ↦ M_n ⊗^𝐋_{A_n} N_n` with `n ↦ M_n ⊗^𝐋_{A_n} N'_n` in `D(B, d)` that a pro-isomorphism of the
systems of modules induces. -/
def proIso : InverseSequence.ProIso (M.tower N) (M.tower N') := (p.interleaving M).proIso

end ProIsoDerived

/-- **Stacks 0GZI.** Let `(A_n)` be an inverse system of differential graded algebras over `R`,
let `(N_n)` and `(N'_n)` be inverse systems of left differential graded modules over it which are
pro-isomorphic in the derived category, and let `(M_n)` be an inverse system of differential
graded `(A_n, B)`-bimodules. Then the derived limits of the two towers
`n ↦ M_n ⊗^𝐋_{A_n} N_n` and `n ↦ M_n ⊗^𝐋_{A_n} N'_n` of `D(B, d)` are isomorphic, although not
canonically. With `B` concentrated in degree zero with `B^0 = R` this is the source's
`R lim (M_n ⊗^𝐋_{A_n} N_n) = R lim (M_n ⊗^𝐋_{A_n} N'_n)` in `D(R)`. -/
@[stacks 0GZI]
theorem nonempty_iso_of_proIsoDerived {S : AlgebraSystem R}
    {B : DifferentialGradedAlgebra.{u, u} R} {N N' : ModuleSystem S} (p : ProIsoDerived N N')
    (M : BimoduleSystem S B)
    [HasProduct fun n : ℕ => (M.tower N).obj (op n)]
    [HasProduct fun n : ℕ => (M.tower N').obj (op n)] (K K' : derivedCategory' B)
    (hK : Pretriangulated.IsDerivedLimit (M.tower N) K)
    (hK' : Pretriangulated.IsDerivedLimit (M.tower N') K') :
    Nonempty (K ≅ K') :=
  Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism _ _ K K' hK hK' (p.proIso M)

end DifferentialGraded

end

end
