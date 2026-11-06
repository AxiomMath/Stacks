module

public import StacksFrontier.AlgebraicGeometry.Spaces.SiteChangeThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.CompletionCompatibleQuotients

/-!
# Stacks 08B9 for a space over `S` with a morphism to `Spec R`

Let `X` be an algebraic space over `S` with a morphism `π : X ⟶ Spec R`, where `R` is a
Noetherian ring complete with respect to an ideal `I`, and let `X'` be the algebraic space over
`Spec R` it is (Stacks 04SG, `AlgebraicGeometry.Space.siteChangeSpace`), with the equivalence
`Ψ : Mod(𝒪_X) ⥤ Mod(𝒪_{X'})` of `AlgebraicGeometry.Space.siteChangeModules`.  Suppose given, for
an `𝒪_X`-module `N`, modules `Q_n` with maps `u_n : N ⟶ Q_n` which `Ψ` carries to the projections
`Ψ N ⟶ Ψ N / I^{n+1} Ψ N`, and maps `t_n : Q_{n+1} ⟶ Q_n` with `u_{n+1} ≫ t_n = u_n`.  Then for
every `𝒪_X`-module `M` with `Ψ M`, `Ψ N` coherent with support proper over `Spec R`, a family
`c_n : M ⟶ Q_n` with `c_{n+1} ≫ t_n = c_n` comes from a unique `c : M ⟶ N`
(`AlgebraicGeometry.Space.existsUnique_hom_of_compatible_siteChange`).

For `Q_n = ι_{n*} ι_n^* N`, `ι_n` the base change of `Spec(R/I^{n+1}) ⟶ Spec R`, the maps `u_n`
are the units and the identification is `AlgebraicGeometry.Space.siteChangeThickeningIso`: this
is Stacks 08B9 read on the space over `S`.

## References

* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {R : Type u} [CommRing R]
  {hR : B.Contains (Spec (.of R))} {h : B.obj hR ⟶ B.obj hS}
  (X : AlgebraicSpaces B S hS) (π : X ⟶ schemeSpace (Over.mk h)) (I : Ideal R)

/-- **Stacks 08B9 for a space over `S` with a morphism to `Spec R`, on compatible families.** -/
theorem existsUnique_hom_of_compatible_siteChange [IsNoetherianRing R] [IsAdicComplete I R]
    (hf : IsLocallyOfFiniteType B (Spec (.of R)) hR (siteChangeStructure X π).hom)
    (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : IsCoherent B (Spec (.of R)) hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
      ((siteChangeModules B X π).obj M))
    (hN : IsCoherent B (Spec (.of R)) hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
      ((siteChangeModules B X π).obj N))
    (hMp : HasProperSupport B (Spec (.of R)) hR (siteChangeSpace B X π).2
      (schemeSpace (baseObject R B hR)).2 (siteChangeStructure X π).hom hf
      ((SheafOfModules.toSheaf _).obj ((siteChangeModules B X π).obj M)))
    (hNp : HasProperSupport B (Spec (.of R)) hR (siteChangeSpace B X π).2
      (schemeSpace (baseObject R B hR)).2 (siteChangeStructure X π).hom hf
      ((SheafOfModules.toSheaf _).obj ((siteChangeModules B X π).obj N)))
    (Q : ℕ → Modules.{u, u} B S hS X.1 X.2) (u : ∀ n, N ⟶ Q n)
    (κ : ∀ n, (siteChangeModules B X π).obj (Q n) ≅
      idealPowerQuotient B (Spec (.of R)) hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
        (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) (n + 1)
        ((siteChangeModules B X π).obj N))
    (hκ : ∀ n, (siteChangeModules B X π).map (u n) ≫ (κ n).hom =
      cokernel.π (idealPowerMultiple B (Spec (.of R)) hR (siteChangeSpace B X π).1
        (siteChangeSpace B X π).2
        (C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I) (n + 1)
        ((siteChangeModules B X π).obj N)).ι)
    (t : ∀ n, Q (n + 1) ⟶ Q n) (ht : ∀ n, u (n + 1) ≫ t n = u n)
    (c : ∀ n, M ⟶ Q n) (hc : ∀ n, c (n + 1) ≫ t n = c n) :
    ∃! d : M ⟶ N, ∀ n, d ≫ u n = c n := by
  let Ψ := siteChangeModules B X π
  let hΨ : Ψ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful Ψ
  let 𝓘 := C1573.baseIdealSubmodule (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 I
  let p : ∀ n, Ψ.obj N ⟶ idealPowerQuotient B (Spec (.of R)) hR (siteChangeSpace B X π).1
      (siteChangeSpace B X π).2 𝓘 (n + 1) (Ψ.obj N) := fun n =>
    cokernel.π (idealPowerMultiple B (Spec (.of R)) hR (siteChangeSpace B X π).1
      (siteChangeSpace B X π).2 𝓘 (n + 1) (Ψ.obj N)).ι
  have hu : ∀ n, Ψ.map (u n) = p n ≫ (κ n).inv := fun n => (Iso.eq_comp_inv _).2 (hκ n)
  have hepi : ∀ n, Epi (Ψ.map (u n)) := fun n => by
    rw [hu n]
    have : Epi (p n) := coequalizer.π_epi
    exact @epi_comp _ _ _ _ _ _ this _ (IsIso.epi_of_iso _)
  have hκt : ∀ n, (κ (n + 1)).hom ≫ idealPowerQuotientMapOfLE B (Spec (.of R)) hR
      (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 𝓘 (Nat.le_succ (n + 1)) (Ψ.obj N) =
      Ψ.map (t n) ≫ (κ n).hom := fun n => by
    have := hepi (n + 1)
    refine (cancel_epi (Ψ.map (u (n + 1)))).1 ?_
    rw [reassoc_of% (hκ (n + 1)), π_comp_idealPowerQuotientMapOfLE, ← Functor.map_comp_assoc,
      ht n, hκ n]
  let a : ∀ n, Ψ.obj M ⟶ _ := fun n => Ψ.map (c n) ≫ (κ n).hom
  have ha : ∀ n, a (n + 1) ≫ idealPowerQuotientMapOfLE B (Spec (.of R)) hR
      (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 𝓘 (Nat.le_succ (n + 1)) (Ψ.obj N) =
      a n := fun n => by
    simp only [a, Category.assoc, hκt n, ← Functor.map_comp_assoc, hc n]
  obtain ⟨b, hb, hbu⟩ := existsUnique_hom_of_compatible_idealPowerQuotient
    (siteChangeSpace B X π) I (siteChangeStructure X π) hf ⟨⟨Ψ.obj M, hM⟩, hMp⟩
    ⟨⟨Ψ.obj N, hN⟩, hNp⟩ a ha
  have key : ∀ d : M ⟶ N, (∀ n, d ≫ u n = c n) ↔ (∀ n, Ψ.map d ≫ p n = a n) := by
    intro d
    refine ⟨fun hd n => ?_, fun hd n => ?_⟩
    · show Ψ.map d ≫ p n = Ψ.map (c n) ≫ (κ n).hom
      rw [← hd n, Functor.map_comp_assoc, hκ n]
    · refine hΨ.map_injective ?_
      rw [Functor.map_comp, hu n, reassoc_of% (hd n)]
      simp only [a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact ⟨hΨ.preimage b, (key _).2 fun n => by rw [hΨ.map_preimage]; exact hb n,
    fun d hd => hΨ.map_injective ((hbu _ ((key d).1 hd)).trans (hΨ.map_preimage b).symm)⟩

end AlgebraicGeometry.Space

end
