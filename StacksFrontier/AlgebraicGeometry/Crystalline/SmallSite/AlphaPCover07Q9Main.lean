module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeRowQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChainOpenDeRham07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChainRowZero07Q9

/-!
# Stacks Project, Lemma 60.26.3, Tag 07Q9

Let `p` be a prime number, `(S, 𝓘, γ)` a divided power scheme over `ℤ_(p)` with `p ∈ 𝓘`,
`S₀ = V(𝓘)`, and `f : X' ⟶ X` an iterated `α_p`-cover of schemes over `S₀` of constant degree
`q`.  For a crystal in quasi-coherent modules `ℱ` on `Cris(X/S)` with `ℱ' = f_cris^*ℱ`, in the
distinguished triangle

`Ru_{X/S, *}ℱ ⟶ f_*Ru_{X'/S, *}ℱ' ⟶ E ⟶ Ru_{X/S, *}ℱ[1]`

the object `E` has cohomology sheaves annihilated by `q`
(`annihilation07Q9_of_isIteratedAlphaPCover`).

## The proof

The source's proof: the question is local on `X`; over an affine open `W` over which `f` is a
chain `X' = X_n ⟶ ⋯ ⟶ X_0 = X` of `α_p`-covers `C_{i+1} = C_i[z]/(z^p - c_i)` (so `q = p ^ n`),
choose a polynomial presentation `P → C` with envelope `D` and `P' = P[z_1, …, z_n]`; the envelope
`D'` of `P' → C'` is the iterated completed `D[z]⟨ξ⟩/(ξ - (z^p - λ))` of [Stacks, Tag 07N1], and
[Stacks, Tag 07LG] computes both crystalline cohomologies by the de Rham complexes
`M ⊗̂_D Ω^•_D` and `M' ⊗̂_{D'} Ω^•_{D'}`.  Here:

* the reduction to a basis of chain opens is `annihilation07Q9_of_chainConeAnnihilation`
  (through the Zariski and crystalline reductions of
  `annihilation07Q9_moduleComparison07Q9_of_isBasis` and the Čech computation
  `chainConeAnnihilation_of_chainOpen07Q9`);
* the Čech complexes are compared with the Moore complexes of the cosimplicial modules of the
  crystal over `D(•)` and of its base change over `D'(•)`, and through the zigzag of
  [Stacks, Tag 07LG] with the rows zero (`smul_id_homology_sectionsMap_of_rowZero07Q9`; the rows
  are quasi-isomorphic to the row zero by `quasiIso_baseChangePair_rowFromZeroHom`);
* the row-zero map is the composite of the `n` maps of [Stacks, Tag 07N1], each split up to `p`,
  so its cone is killed by `p ^ n` (`smul_id_homology_chainRowZero07Q9`).

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (T : GlobalCrystallineSituation.{u}) {X' : Scheme.{u}} (f : X' ⟶ T.X)

variable {T f} in
/-- **The rows of the two double complexes over a chain open**: every coprojection of rows of the
cosimplicial pair of `ℱ` over `W`, and of its base change to the envelope of the chain
presentation of `Γ(f⁻¹(W))`, is a quasi-isomorphism ([Stacks, Tag 07LD] through
`quasiIso_baseChangePair_rowFromZeroHom`). -/
theorem quasiIso_chainPairs_rowFromZeroHom07Q9 {V : T.S.scheme.Opens} {W : T.X.Opens}
    (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase T ⁻¹ᵁ V) (hW₂ : IsAffineOpen (f ⁻¹ᵁ W))
    {n : ℕ} (ch : AlphaPChain T.p Γ(T.X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top)
    (F : SheafOfModules.{u} (structureSheaf T)) (hF : IsQuasiCoherentCrystal T F)
    [IsAffine (restrict T V W hVW).X] [IsAffine (restrict T V W hVW).S.scheme] :
    (∀ b : ℕ, QuasiIso ((chainTargetPair07Q9 T hW hVW F hF).rowFromZeroHom b)) ∧
      ∀ b : ℕ, QuasiIso ((chainSourcePair07Q9 T hW hVW f hW₂ ch e F hF).rowFromZeroHom b) :=
  ⟨fun b ↦ quasiIso_baseChangePair_rowFromZeroHom _ _ _ _ _ _ _ _ b,
    fun b ↦ quasiIso_baseChangePair_rowFromZeroHom _ _ _ _ _ _ _ _ b⟩

/-- **[Stacks, Tag 07Q9] over a chain open**: if `f` is a chain of `n` successive
`α_p`-extensions over the affine open `W`, the sections over `W` of the lift of the unit
`ℱ ⟶ f_{cris, *}f_cris^*ℱ` to injective resolutions have mapping cone with cohomology killed by
`p ^ n`. -/
theorem chainConeAnnihilation_isChainOpen07Q9 (F : SheafOfModules.{u} (structureSheaf T))
    (hF : IsQuasiCoherentCrystal T F) {n : ℕ} {W : T.X.Opens} (hW : IsChainOpen07Q9 T f n W) :
    ChainConeAnnihilation (T.p ^ n) (sectionsChainMap T W
      (crisResolutionMap (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f)
        ((moduleULift T).obj F) (injectiveResolution _) (injectiveResolution _))) := by
  obtain ⟨V, hV, hW, hVW, hW₂, ch, e, he⟩ := hW
  have := isAffine_restrictX07Q9 T hW hVW
  have := isAffine_restrictS07Q9 T hV hVW
  obtain ⟨hr, hr'⟩ := quasiIso_chainPairs_rowFromZeroHom07Q9 hW hVW hW₂ ch e F hF
  exact chainConeAnnihilation_of_chainOpen07Q9 T hV hW hVW f hW₂ ch e he F hF (T.p ^ n)
    (smul_id_homology_sectionsMap_of_rowZero07Q9 T hV hW hVW f hW₂ ch e he F hF _ hr hr'
      (smul_id_homology_chainRowZero07Q9 T hW hVW f hW₂ ch e he F hF))

variable [HasDerivedCategory.{w} (Sheaf (smallTopology (overSituation T f)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology T) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology (overSituation T f)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology T) AddCommGrpCat.{u + 1})]

/-- **Stacks Project, Lemma 60.26.3, Tag 07Q9.**  Let `p = T.p` be the prime of the global
crystalline situation `T`, whose divided power scheme `(S, 𝓘, γ)` lies over `ℤ_(p)`.  Let
`f : X' ⟶ X` be an iterated `α_p`-cover (`hf`) of schemes over `S₀ = V(𝓘)` — `X'` lies over
`S₀` through `f`, which is the situation `overSituation T f` — of constant degree `q` (`hq`).
Let `ℱ` be a crystal in quasi-coherent sheaves on `Cris(X/S)` (`hF`) and `ℱ' = f_cris^*ℱ`
(`crisModuleInverseImage` of `ℱ`).  Then in every distinguished triangle

`Ru_{X/S, *}ℱ ⟶ f_*Ru_{X'/S, *}ℱ' ⟶ E ⟶ Ru_{X/S, *}ℱ[1]`

on the canonical map `moduleComparison07Q9` (in the derived category of abelian sheaves on `X`;
`f_*` is the derived direct image of the Zariski topoi, which is `f_*` since `f` is a
homeomorphism), the object `E` has every cohomology sheaf annihilated by `q` (`Annihilation07Q9`).

The hypothesis `p ∈ 𝓘` of the source is not needed: the argument only uses that `p` is nilpotent
on `X`, which every global crystalline situation carries. -/
@[stacks 07Q9 "for an iterated α_p-cover f : X' → X over S_0 of constant degree q and a crystal \
in quasi-coherent modules F on Cris(X/S), with F' = f_cris^* F, the cone E of \
Ru_{X/S,*}F → f_* Ru_{X'/S,*}F' has all cohomology sheaves annihilated by q"]
theorem annihilation07Q9_of_isIteratedAlphaPCover
    {q : ℕ} (hf : IsIteratedAlphaPCover T.p f) (hq : HasConstantDegree f q)
    (F : SheafOfModules.{u} (structureSheaf T)) (hF : IsQuasiCoherentCrystal T F) :
    Annihilation07Q9 T q
      (moduleComparison07Q9 (overSituation T f) T (𝟙 T.S) f (overSituation_compat T f)
        ((moduleULift T).obj F)) := by
  exact annihilation07Q9_of_chainConeAnnihilation hf hq _ fun n W hW =>
    chainConeAnnihilation_isChainOpen07Q9 T f F hF hW

end Crystalline.GlobalCrystallineSituation.SmallSite
