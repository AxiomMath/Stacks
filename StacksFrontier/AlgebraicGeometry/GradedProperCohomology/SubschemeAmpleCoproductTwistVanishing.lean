module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiCompactCoproductSections
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AnnihilatorSupport
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.CoproductTwistVanishing
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.RestrictBase

/-!
# Uniform vanishing of the twists of a family killed by an ideal sheaf

This is `Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_coprodIso` with
its ampleness hypothesis moved **down to a closed subscheme of `X`**. Let `π : X' ⟶ X` be affine,
`f' : X' ⟶ Spec R` proper with `R` Noetherian, `F'` a coherent `𝒪_{X'}`-module, `L` an invertible
`𝒪_X`-module and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals. Suppose a family
`M : ℕ → X.Modules` has

`∐ₙ Mₙ ≅ π_* F'`,

and that `ℐ` annihilates the sections of `π_* F'`. Then the restriction of `L` to the closed
subscheme `V(ℐ)` being ample is already enough for

`Hᵖ(X, Mₙ ⊗ L ^⊗ d) = 0` for every `p > 0`, every `d ≥ d₀` and every `n`,

one `d₀` serving all three.

Nothing of `L` away from `V(ℐ)` is used, which is what the degree-zero form of
[Stacks, Tag 0D2M] needs: there `ℐ = 𝔪 · 𝒪_X` for the maximal ideal of a Noetherian local base,
`V(ℐ)` is the closed fibre, and the source's hypothesis is ampleness on that fibre alone.

## The argument

The annihilation is exactly the statement that `F'` lives on a closed subscheme of `X'` lying
over `V(ℐ)`, and the vanishing is read there.

* `AlgebraicGeometry.annihilatorIdeal'` is the ideal sheaf of the scheme-theoretic support of
  `F'`, and the annihilation hypothesis says, by
  `AlgebraicGeometry.Scheme.IdealSheafData.ideal_map_of_isAffineHom`, that `ℐ` is below its
  pushforward along `π`. The Galois connection
  `AlgebraicGeometry.Scheme.IdealSheafData.map_gc` turns that into
  `ℐ.comap π ≤ annihilatorIdeal' F'`, which spreads the affine-open statement over `X` to all
  the affine opens of `X'`.
* So the ideal sheaf `ℐ.comap π` annihilates `F'` section by section
  (`Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal`), and [Stacks, Tag 087T] in the form
  `AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_smul_eq_zero` descends `F'` to a
  coherent module `G` on `W = V(ℐ.comap π)` with `j_* G ≅ F'` for `j : W ⟶ X'` the closed
  immersion.
* `W` is affine over `V(ℐ)`: the closed subscheme `V(ℐ.comap π)` *is* the fibred product
  `X' ×_X V(ℐ)` (`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`), so the projection
  `W ⟶ V(ℐ)` — which is `AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap` — is the base
  change of the affine `π`. Hence the inverse image of `L|_{V(ℐ)}` is ample on `W`
  ([Stacks, Tag 0892] part (2), `Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`),
  and that inverse image is the inverse image of `L` along `j ≫ π`, because the projection
  composed with `V(ℐ) ⟶ X` is `j ≫ π`.
* `j ≫ π` is affine and `j ≫ f'` is proper, a closed immersion being both, and
  `∐ₙ Mₙ ≅ π_* F' ≅ π_* j_* G = (j ≫ π)_* G`. So `W`, `G` and `j ≫ π` are a legal input to
  `exists_isZero_Hgroup_tensorPowTwist_of_coprodIso` with ampleness known upstairs, which is the
  only form that theorem consumes it in.

## Main results

* `smul_coprod_sections_eq_zero`: a section of `𝒪_X` over a quasi-compact open killing the
  sections of every summand there kills the sections of the coproduct — [Stacks, Tag 0935]
  part (2) says the latter *are* the direct sum of the former.
* `exists_isZero_Hgroup_tensorPowTwist_of_coprodIso_of_isAmple_subscheme`: the theorem
  displayed above.

## Implementation notes

**No `stacks` attribute is attached.** This is a step inside the proof of [Stacks, Tag 0897]
part (2), as its unsubscripted counterpart in
`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/CoproductTwistVanishing.lean` is; it is not
a numbered result of the source.

**The annihilation is asked for on `π_* F'` rather than on `F'`.** Sections of the direct image
over an open of `X` are sections of `F'` over its inverse image, with the scalars acting through
`π^♯`, so the two readings of a single condition are definitionally equal; and it is the reading
over `X` that a caller holding `∐ₙ Mₙ ≅ π_* F'` can discharge, summand by summand, through
`smul_coprod_sections_eq_zero`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.GradedProperCohomology

/-! ### Annihilation of the sections of a coproduct over a quasi-compact open -/

/-- **A section of `𝒪_X` annihilating every summand annihilates the coproduct**, over a
quasi-compact open.

Over a quasi-compact open the sections of a coproduct of sheaves of modules are the direct sum of
the sections of the summands — [Stacks, Tag 0935] part (2), in the form
`Stacks.SheafOfModules.preservesCoproducts_evaluation_of_isCompact` — so multiplication by `a` is
a morphism out of a coproduct and vanishes as soon as it vanishes on each injection. Only
additivity of multiplication by `a` is used, so the statement is read in abelian groups:
`AlgebraicGeometry.Scheme.Modules.smul` is already that morphism. -/
theorem smul_coprod_sections_eq_zero {X : Scheme.{u}} {ι : Type} (N : ι → X.Modules)
    [HasCoproduct N] {U : X.Opens} (hU : IsCompact (U : Set X)) (a : Γ(X, U))
    (hN : ∀ (i : ι) (x : Γ(N i, U)), a • x = 0) (m : Γ(∐ N, U)) : a • m = 0 := by
  have hpres := Stacks.SheafOfModules.preservesCoproducts_evaluation_of_isCompact
    (I := ι) X.ringCatSheaf U hU
  have hcol := ((hpres.preservesColimit (K := Discrete.functor N)).preserves
    (coproductIsCoproduct N)).some
  have hcol2 := isColimitOfPreserves
    (forget₂ (ModuleCat.{u} ↥(X.ringCatSheaf.obj.obj (op U))) AddCommGrpCat.{u}) hcol
  have h0 : ((∐ N).smul (U := U) a).asHom = 0 := by
    refine hcol2.hom_ext ?_
    intro j
    show (Sigma.ι N j.as).app U ≫ ((∐ N).smul a).asHom = (Sigma.ι N j.as).app U ≫ 0
    rw [comp_zero]
    ext x
    show a • ((Sigma.ι N j.as).app U x) = 0
    rw [← Scheme.Modules.Hom.app_smul, hN j.as x, map_zero]
  simpa using congrArg (fun φ : Γ(∐ N, U) ⟶ Γ(∐ N, U) => φ.hom m) h0

/-- **The same, transported along an isomorphism.** This is the form a caller holding
`∐ₙ Nₙ ≅ P` wants: to annihilate the sections of `P` over a quasi-compact open it is enough to
annihilate the sections of each `Nₙ` there. -/
theorem smul_sections_eq_zero_of_coprodIso {X : Scheme.{u}} {ι : Type} (N : ι → X.Modules)
    [HasCoproduct N] {P : X.Modules} (e : (∐ N) ≅ P) {U : X.Opens}
    (hU : IsCompact (U : Set X)) (a : Γ(X, U))
    (hN : ∀ (i : ι) (x : Γ(N i, U)), a • x = 0) (m : Γ(P, U)) : a • m = 0 := by
  obtain ⟨x, rfl⟩ : ∃ x, e.hom.app U x = m :=
    ⟨e.inv.app U m, by
      show (e.inv ≫ e.hom).app U m = m
      rw [e.inv_hom_id]
      rfl⟩
  rw [← Scheme.Modules.Hom.app_smul, smul_coprod_sections_eq_zero N hU a hN x, map_zero]

/-! ### The vanishing, with ampleness only on the closed subscheme -/

/-- **[Stacks, Tag 0897] part (2) with ampleness only on a closed subscheme.** Let `π : X' ⟶ X`
be affine, `f' : X' ⟶ Spec R` proper with `R` Noetherian, `F'` a coherent `𝒪_{X'}`-module, `L` an
invertible `𝒪_X`-module and `ℐ` a quasi-coherent sheaf of ideals on `X` whose sections annihilate
the sections of `π_* F'`. If the coproduct of a family `M : ℕ → X.Modules` is the direct image of
`F'` along `π` and the restriction of `L` to `V(ℐ)` is ample, then there is a `d₀` with

`Hᵖ(X, Mₙ ⊗ L ^⊗ d) = 0` for every `p > 0`, every `d ≥ d₀` and every `n`,

one bound serving all three.

The annihilation puts `F'` on a closed subscheme `W` of `X'` affine over `V(ℐ)`, so the inverse
image of `L|_{V(ℐ)}` is ample there and
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_coprodIso` applies to `W`;
see the module documentation for the four steps. -/
theorem exists_isZero_Hgroup_tensorPowTwist_of_coprodIso_of_isAmple_subscheme
    {X X' : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
    (π : X' ⟶ X) [AlgebraicGeometry.IsAffineHom π]
    (f' : X' ⟶ Spec (CommRingCat.of R)) [IsProper f']
    (𝓘 : X.IdealSheafData) (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple 𝓘.subscheme (pullbackModule 𝓘.subschemeι L))
    (F' : X'.Modules) [_root_.SheafOfModules.IsCoherent F']
    (M : ℕ → X.Modules) (ε : (∐ M) ≅ (Scheme.Modules.pushforward π).obj F')
    (hann : ∀ (U : X.affineOpens) (a : Γ(X, U.1)), a ∈ 𝓘.ideal U →
      ∀ m : Γ((Scheme.Modules.pushforward π).obj F', U.1), a • m = 0) :
    ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p → ∀ n : ℕ,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (M n) (tensorPowModule X L (d : ℤ)))) := by
  have _ : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian f'
  have _ : F'.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F'
  have _ : F'.IsFiniteType := ‹_root_.SheafOfModules.IsCoherent F'›.isFiniteType
  -- The scheme-theoretic support of `F'` contains the inverse image of `V(ℐ)`.
  have hmap : 𝓘 ≤ (annihilatorIdeal' F').map π := by
    intro U a ha
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom, Ideal.mem_comap,
      annihilatorIdeal_ideal, Module.mem_annihilator]
    exact fun m => hann U a ha m
  have hcomap : 𝓘.comap π ≤ annihilatorIdeal' F' :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mp hmap
  -- So `F'` is the direct image of a coherent module on `W = V(ℐ.comap π)`.
  have hAnn : ∀ (V : X'.Opens) (a : Γ(X', V)),
      ((𝓘.comap π).subschemeι.app V).hom a = 0 → ∀ m : Γ(F', V), a • m = 0 := by
    refine (Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal
      (𝓘.comap π).subschemeι F').mpr ?_
    intro V a ha m
    rw [Scheme.IdealSheafData.ker_subschemeι] at ha
    have hV := hcomap V ha
    rw [annihilatorIdeal_ideal, Module.mem_annihilator] at hV
    exact hV m
  obtain ⟨G, hG, ⟨eG⟩⟩ := AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_smul_eq_zero
    (𝓘.comap π).subschemeι F' hAnn
  have _ := hG
  -- `W` is affine over `V(ℐ)`, being the base change of `π` along `V(ℐ) ⟶ X`.
  have hsnd : AlgebraicGeometry.IsAffineHom (pullback.snd π 𝓘.subschemeι) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsAffineHom)
      (IsPullback.of_hasPullback π 𝓘.subschemeι) ‹_›
  have _ : AlgebraicGeometry.IsAffineHom
      (Scheme.IdealSheafData.subschemeMap (𝓘.comap π) 𝓘 π (𝓘.le_map_comap π)) := by
    rw [← Scheme.IdealSheafData.comapIso_hom_snd 𝓘 π]
    infer_instance
  -- Hence the inverse image of `L` along `j ≫ π` is ample on `W`.
  have hL2 : IsAmple (𝓘.comap π).subscheme
      (pullbackModule ((𝓘.comap π).subschemeι ≫ π) L) := by
    refine (isAmple_congr _ _ (Stacks.RelativeAmpleBaseChange.pullbackModuleCongr
      (Scheme.IdealSheafData.subschemeMap_subschemeι (𝓘.comap π) 𝓘 π (𝓘.le_map_comap π)) L)).mp ?_
    exact (Stacks.RelativeAmpleRestrictBase.isAmple_pullbackModule_comp_iff _ 𝓘.subschemeι L).mp
      (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom _ _ hL)
  refine exists_isZero_Hgroup_tensorPowTwist_of_coprodIso ((𝓘.comap π).subschemeι ≫ π)
    ((𝓘.comap π).subschemeι ≫ f') L hL2 G M ?_
  exact ε ≪≫ (Scheme.Modules.pushforward π).mapIso eG.symm ≪≫
    (Scheme.Modules.pushforwardComp (𝓘.comap π).subschemeι π).app G

end Stacks.GradedProperCohomology

end
