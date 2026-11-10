module

public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Joint surjectivity along an arbitrary cartesian square, and under reindexing

Two statements about a jointly surjective family of morphisms of sheaves of sets, that is about
local surjectivity of the induced morphism out of the coproduct.

`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd` base changes such a family along
a morphism `φ : F ⟶ G`, but states the result for the *chosen* pullbacks `H i ×_G F`. A family of
fibre products arising some other way — as a fibre product over a different base, or as the vertex
of a square built by pasting — is only isomorphic to those, and transporting a coproduct of
sheaves along a family of isomorphisms is more work than the statement deserves. So the first
result below asks only for a cartesian square over each index, which is how such a family
presents itself.

The second lets the index type of a jointly surjective family be replaced by an equivalent one.
This is needed whenever two applications of
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_comp` are nested, since that lemma produces
the index `Σ i, κ i` and nesting it therefore produces `Σ (p : Σ i, κ i), μ p.1` where the
intended family is indexed by `Σ i, κ i × μ i`.

## Main results

* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_of_isPullback`: a jointly surjective family
  base changed along a morphism, with the base change presented as a cartesian square over each
  index, is jointly surjective.
* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_reindex`: joint surjectivity transfers along
  an equivalence of index types.

## Implementation notes

The first is `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd` composed with the
canonical isomorphism `CategoryTheory.IsPullback.isoPullback` of each square with the chosen
pullback, assembled by `CategoryTheory.Limits.Sigma.map` and absorbed by
`CategoryTheory.Sheaf.isLocallySurjective_of_fac`; no sieve appears.

The second is read off the sectionwise characterisation
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_iff`: the covering sieve it produces is
unchanged, and only the index of the member containing a given section is transported.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Base change of a jointly surjective family, presented by cartesian squares.** If a family
`(ψ i : H i ⟶ G)_{i ∈ I}` of morphisms of sheaves of sets induces a surjection out of its
coproduct, and for each `i` the sheaf `P i` is the vertex of a cartesian square over `ψ i` and a
fixed `φ : F ⟶ G`, with `n i : P i ⟶ F` the projection parallel to `ψ i`, then the family
`(n i)_{i ∈ I}` induces a surjection out of its coproduct.

`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd` is the case of the chosen
pullbacks; this reduces to it along `CategoryTheory.IsPullback.isoPullback`. -/
theorem isLocallySurjective_sigmaDesc_of_isPullback {F G : Sheaf J (Type max u v)} (φ : F ⟶ G)
    {I : Type max u v} {H : I → Sheaf J (Type max u v)} (ψ : ∀ i, H i ⟶ G)
    (hψ : IsLocallySurjective (Sigma.desc ψ))
    {P : I → Sheaf J (Type max u v)} {πH : ∀ i, P i ⟶ H i} (n : ∀ i, P i ⟶ F)
    (hP : ∀ i, IsPullback (πH i) (n i) (ψ i) φ) :
    IsLocallySurjective (Sigma.desc n) := by
  have hbase := isLocallySurjective_sigmaDesc_pullback_snd φ ψ hψ
  have key : (Limits.Sigma.map fun i ↦ (hP i).isoPullback.inv) ≫ Sigma.desc n =
      Sigma.desc fun i ↦ pullback.snd (ψ i) φ := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    exact (hP i).isoPullback_inv_snd
  exact isLocallySurjective_of_fac key

/-- **Joint surjectivity transfers along an equivalence of index types.** If the family
`(f (e i))_{i ∈ I₁}` obtained from `(f i)_{i ∈ I₂}` by reindexing along an equivalence
`e : I₁ ≃ I₂` induces a surjection out of its coproduct, then so does `(f i)_{i ∈ I₂}`.

Read off the sectionwise characterisation of joint surjectivity: the covering sieve is the same,
and the index of the member containing a given section is transported by `e`. -/
theorem isLocallySurjective_sigmaDesc_reindex {I₁ I₂ : Type max u v} (e : I₁ ≃ I₂)
    {F : Sheaf J (Type max u v)} {G : I₂ → Sheaf J (Type max u v)} (f : ∀ i, G i ⟶ F)
    (h : IsLocallySurjective (Sigma.desc fun i : I₁ ↦ f (e i))) :
    IsLocallySurjective (Sigma.desc f) := by
  refine (isLocallySurjective_sigmaDesc_iff f).2 fun {U} s ↦ ?_
  obtain ⟨T, hT, hcov⟩ := (isLocallySurjective_sigmaDesc_iff _).1 h s
  refine ⟨T, hT, fun {V} g hg ↦ ?_⟩
  obtain ⟨i, t, ht⟩ := hcov g hg
  exact ⟨e i, t, ht⟩

end CategoryTheory.Sheaf

end
