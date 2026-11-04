module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCoverLocalChain07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PerOpenData07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Reduction07Q9

/-!
# The opens of `X` over which an iterated `α_p`-cover is a chain

For an iterated `α_p`-cover `f : X' ⟶ X` of constant degree `q` in a global crystalline situation,
the affine opens `W ⊆ X` mapping into an affine open `V` of the divided power base, with affine
preimage `f⁻¹(W)` over which `f` is a chain of `n` successive `α_p`-extensions with `q = p ^ n`,
form a basis of the opens of `X`.  Over a basis the conclusion of [Stacks, Tag 07Q9] is local
(`annihilation07Q9_moduleComparison07Q9_of_isBasis`), so it suffices to show, for each such `W`,
that the sections over `W` of the lift of the unit to injective resolutions have mapping cone with
cohomology killed by `p ^ n`: that is `annihilation07Q9_of_chainConeAnnihilation`.

## Main definitions

* `IsChainOpen07Q9` — the data of an open `W` as above.

## Main results

* `isBasis_isChainOpen07Q9` — these opens form a basis.
* `annihilation07Q9_of_chainConeAnnihilation` — the reduction of [Stacks, Tag 07Q9] to them.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (T : GlobalCrystallineSituation.{u}) {X' : Scheme.{u}} (f : X' ⟶ T.X)

/-- **An open of `X` over which `f` is a chain of `n` successive `α_p`-extensions**: `W` is affine,
maps into an affine open `V` of the divided power base, has affine preimage `f⁻¹(W)`, and
`Γ(X', f⁻¹(W))` is the last ring of an `α_p`-chain of length `n` over `Γ(X, W)` compatibly with
`f^♯`. -/
def IsChainOpen07Q9 (n : ℕ) (W : T.X.Opens) : Prop :=
  ∃ V : T.S.scheme.Opens, IsAffineOpen V ∧ IsAffineOpen W ∧ W ≤ sourceToBase T ⁻¹ᵁ V ∧
    IsAffineOpen (f ⁻¹ᵁ W) ∧ ∃ (ch : AlphaPChain T.p Γ(T.X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top),
      f.app W ≫ e.hom = ch.toTop

variable {T f}

/-- **The chain opens form a basis of the opens of `X`**, with the length of the chain the
exponent of the degree: around every point of an open `N` there is an open `W ⊆ N` over which `f`
is a chain of `n` successive `α_p`-extensions with `q = p ^ n`. -/
theorem isBasis_isChainOpen07Q9 (hf : IsIteratedAlphaPCover T.p f) {q : ℕ}
    (hq : HasConstantDegree f q) :
    Opens.IsBasis {W : T.X.Opens | ∃ n : ℕ, q = T.p ^ n ∧ IsChainOpen07Q9 T f n W} := by
  refine Opens.isBasis_iff_nbhd.mpr fun {N x} hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := T.S.scheme.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (sourceToBase T x)) isOpen_univ
  have hxN : x ∈ N ⊓ sourceToBase T ⁻¹ᵁ V := ⟨hx, hxV⟩
  obtain ⟨W, hW, hW₂, hxW, hWN, n, ch, e, he, hqn⟩ :=
    exists_alphaPChain_and_eq_pow_of_hasConstantDegree (Fact.out : T.p.Prime).ne_zero hf hq hxN
  exact ⟨W, ⟨n, hqn, V, hV, hW, hWN.trans inf_le_right, hW₂, ch, e, he⟩, hxW,
    hWN.trans inf_le_left⟩

variable [HasDerivedCategory.{w} (Sheaf (smallTopology (overSituation T f)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology T) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology (overSituation T f)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology T) AddCommGrpCat.{u + 1})]

/-- **[Stacks, Tag 07Q9] reduced to the chain opens.**  If over every open `W` over which `f` is a
chain of `n` successive `α_p`-extensions the sections over `W` of the lift of the unit
`F ⟶ f_{cris, *}f_cris^*F` to injective resolutions have mapping cone with cohomology killed by
`p ^ n`, then the cone of the comparison map of [Stacks, Tag 07Q9] has cohomology sheaves killed
by `q`. -/
theorem annihilation07Q9_of_chainConeAnnihilation (hf : IsIteratedAlphaPCover T.p f) {q : ℕ}
    (hq : HasConstantDegree f q) (F : ModuleSheaf T)
    (hper : ∀ (n : ℕ) (W : T.X.Opens), IsChainOpen07Q9 T f n W →
      ChainConeAnnihilation (T.p ^ n) (sectionsChainMap T W
        (crisResolutionMap (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f) F
          (injectiveResolution _) (injectiveResolution _)))) :
    Annihilation07Q9 T q
      (moduleComparison07Q9 (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f) F) :=
  annihilation07Q9_moduleComparison07Q9_of_isBasis (overSituation T f) T (𝟙 T.S) f
    (overSituation_compat T f) F q (isBasis_isChainOpen07Q9 hf hq) fun W ⟨n, hqn, hW⟩ => by
      rw [hqn]
      exact_mod_cast hper n W hW

end Crystalline.GlobalCrystallineSituation.SmallSite
