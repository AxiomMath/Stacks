module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModuleHigherDirectImageFilteredColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentHigherDirectImageDeltaFunctor

/-!
# The quasi-coherent direct images commute with direct sums and filtered colimits (Stacks 0GQX)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks.
**Stacks 0GQX** says that `f_{QCoh,*}` and the functors `Rⁱf_{QCoh,*}` commute with direct sums
and filtered colimits.

The functors are those of **Stacks 077A**,
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImage` and
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImage`, the composites
`Q ∘ f_* ∘ i` and `Q ∘ Rⁱf_* ∘ i`; by
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImageIsoComposite` and
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImageIsoComposite` they factor
through `LQCoh^fbc` as `QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒴) → QCoh(𝒪_𝒴)`.

## Main results

* `preservesColimitsOfShape_quasicoherentDirectImage` and
  `preservesColimitsOfShape_quasicoherentHigherDirectImage`: for a shape `K` with which `f_*`,
  resp. `Rⁱf_*`, commutes on modules, so does `f_{QCoh,*}`, resp. `Rⁱf_{QCoh,*}`.
* `preservesCoproducts_and_filteredColimits_quasicoherentDirectImages_of_qcqs`:
  **Stacks 0GQX**.

## Proof

This is the source's proof. `f_*` and `Rⁱf_*` commute with direct sums and filtered colimits on all
modules by **Stacks 0GQW** (`preservesColimitsOfShape_fppfModulesHigherDirectImage_of_isFiltered`
and its companions, which derive the module statement from the one for abelian sheaves), hence on
`LQCoh^fbc`, whose colimits are those of modules (**Stacks 0771** (5)). The lemma follows as
`f_{QCoh,*} = Q ∘ f_*` and `Rⁱf_{QCoh,*} = Q ∘ Rⁱf_*` on `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`, the
inclusion commutes with colimits, being left adjoint to `Q` (**Stacks 0778**), and `Q` commutes
with all colimits (**Stacks 0779** (3)).

## Indexing and universes

Modules are on the fppf sites at the module universe `u` of the schemes. Direct sums are indexed
by `ι : Type u` and filtered colimits by filtered categories `J : Type u` with morphisms in `u`.

## References

* [Stacks Project, Tag 0GQX](https://stacks.math.columbia.edu/tag/0GQX)
* [Stacks Project, Tag 0GQW](https://stacks.math.columbia.edu/tag/0GQW)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (S : Scheme.{u})
  (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- A functor `R : Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒴)` carrying `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)` and
commuting with colimits of a `u`-small shape `K`: its restriction to `LQCoh^fbc` commutes with
them too, the colimits of `LQCoh^fbc` being those of modules (**Stacks 0771** (5)). -/
theorem preservesColimitsOfShape_lqcohSheafFbc_lift
    (R : Stack.fppfModules B S hS 𝒳 ⥤ Stack.fppfModules B S hS 𝒴)
    (hR : ∀ F : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory,
      lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴 (R.obj F.obj))
    (K : Type u) [Category.{u} K] [hRK : PreservesColimitsOfShape K R] :
    PreservesColimitsOfShape K ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).lift
      ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ R) hR) := by
  have : PreservesColimitsOfShape K ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).lift
      ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ R) hR ⋙
        (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι) :=
    preservesColimitsOfShape_of_natIso (ObjectProperty.liftCompιIso _ _ _).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι

/-- The composite `QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒴) → QCoh(𝒪_𝒴)` of the inclusion, a
functor `D` and the coherator `Q` commutes with colimits of a `u`-small shape `K` as soon as `D`
does: the inclusion is left adjoint to `Q` (**Stacks 0778**) and `Q` commutes with all colimits
(**Stacks 0779** (3)). -/
theorem preservesColimitsOfShape_comp_coherator
    (D : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory ⥤
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).FullSubcategory)
    (K : Type u) [Category.{u} K] [PreservesColimitsOfShape K D] :
    PreservesColimitsOfShape K
      ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).lift (quasicoherentInclusion B S hS 𝒳)
          (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳) ⋙ D ⋙
        ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ⋙ coherator B S hS 𝒴)) := by
  have : PreservesColimitsOfSize.{u, u}
      ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).lift (quasicoherentInclusion B S hS 𝒳)
        (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳)) :=
    (lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).leftAdjoint_preservesColimits
  have := preservesColimitsOfShape_lqcohSheafFbc_ι_comp_coherator B S hS 𝒴 E h K
  infer_instance

variable (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)

include hqc hqs in
/-- **`f_{QCoh,*}` commutes with the colimits `f_*` commutes with**: for `f` quasi-compact and
quasi-separated and a `u`-small shape `K` with which the direct image of modules commutes, the
quasi-coherent direct image of **Stacks 077A** commutes with colimits of shape `K`. -/
theorem preservesColimitsOfShape_quasicoherentDirectImage (K : Type u) [Category.{u} K]
    [PreservesColimitsOfShape K (fppfModulesPushforward B S hS f)] :
    PreservesColimitsOfShape K (quasicoherentDirectImage B S hS f) := by
  let E := associatedBigEtaleSite B
  have h : E.cutoff = B.cutoff := rfl
  have := preservesColimitsOfShape_lqcohSheafFbc_lift B E h S hS
    (fppfModulesPushforward B S hS f)
    (fun F => lqcohSheafFbcFppfModules_fppfModulesPushforward B E h S hS f hqc hqs F.obj
      F.property) K
  have := preservesColimitsOfShape_comp_coherator B E h S hS
    (lqcohSheafFbcDirectImage B E h S hS f hqc hqs) K
  exact preservesColimitsOfShape_of_natIso
    (quasicoherentDirectImageIsoComposite B E h S hS f hqc hqs).symm

include hqc hqs in
/-- **`Rⁱf_{QCoh,*}` commutes with the colimits `Rⁱf_*` commutes with**: for `f` quasi-compact
and quasi-separated and a `u`-small shape `K` with which the higher direct image of modules
commutes, the higher quasi-coherent direct image of **Stacks 077A** commutes with colimits of
shape `K`. -/
theorem preservesColimitsOfShape_quasicoherentHigherDirectImage (i : ℕ) (K : Type u)
    [Category.{u} K] [hK : PreservesColimitsOfShape K (fppfModulesHigherDirectImage B S hS f i)] :
    PreservesColimitsOfShape K (quasicoherentHigherDirectImage B S hS f i) := by
  let E := associatedBigEtaleSite B
  have h : E.cutoff = B.cutoff := rfl
  have := preservesColimitsOfShape_lqcohSheafFbc_lift B E h S hS
    (fppfModulesHigherDirectImage B S hS f i)
    (fun F => lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B E h S hS f hqc hqs F.obj
      F.property i) K (hRK := hK)
  have := preservesColimitsOfShape_comp_coherator B E h S hS
    (lqcohSheafFbcHigherDirectImage B E h S hS f hqc hqs i) K
  exact preservesColimitsOfShape_of_natIso
    (quasicoherentHigherDirectImageIsoComposite B E h S hS f hqc hqs i).symm

include hqc hqs in
/-- **Stacks 0GQX.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of
algebraic stacks. The functor `f_{QCoh,*}` and the functors `Rⁱf_{QCoh,*}` (`i ≥ 0`) of
**Stacks 077A** commute with direct sums and filtered colimits:

1. `f_{QCoh,*}` commutes with direct sums indexed by any `ι : Type u`;
2. `f_{QCoh,*}` commutes with colimits indexed by any filtered category `J : Type u` (morphisms in
   `u`);
3. for every `i`, `Rⁱf_{QCoh,*}` commutes with direct sums indexed by any `ι : Type u` and with
   colimits indexed by any filtered category `J : Type u`.

The functors are `quasicoherentDirectImage` and `quasicoherentHigherDirectImage`, the composites
`Q ∘ f_* ∘ i` and `Q ∘ Rⁱf_* ∘ i` of the inclusion, the direct images of modules on the fppf
sites and the coherator of **Stacks 0778**, at module universe `u`. -/
@[stacks 0GQX "the whole lemma, for f quasi-compact and quasi-separated and the functors \
  f_{QCoh,*} and R^i f_{QCoh,*} (i ≥ 0) of Stacks 077A: each commutes with direct sums (indexed \
  by ι : Type u) and with filtered colimits (indexed by filtered J : Type u)"]
theorem preservesCoproducts_and_filteredColimits_quasicoherentDirectImages_of_qcqs :
    (∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) (quasicoherentDirectImage B S hS f)) ∧
      (∀ (J : Type u) [Category.{u} J] [IsFiltered J],
        PreservesColimitsOfShape J (quasicoherentDirectImage B S hS f)) ∧
      ∀ i : ℕ,
        (∀ ι : Type u,
          PreservesColimitsOfShape (Discrete ι) (quasicoherentHigherDirectImage B S hS f i)) ∧
        (∀ (J : Type u) [Category.{u} J] [IsFiltered J],
          PreservesColimitsOfShape J (quasicoherentHigherDirectImage B S hS f i)) := by
  refine ⟨fun ι => ?_, fun J _ _ => ?_, fun i => ⟨fun ι => ?_, fun J _ _ => ?_⟩⟩
  · have := preservesColimitsOfShape_discrete_fppfModulesPushforward f hqc hqs ι
    exact preservesColimitsOfShape_quasicoherentDirectImage B S hS f hqc hqs _
  · have := preservesColimitsOfShape_fppfModulesPushforward_of_isFiltered f hqc hqs J
    exact preservesColimitsOfShape_quasicoherentDirectImage B S hS f hqc hqs J
  · have := preservesColimitsOfShape_discrete_fppfModulesHigherDirectImage f hqc hqs i ι
    exact preservesColimitsOfShape_quasicoherentHigherDirectImage B S hS f hqc hqs i _
  · have := preservesColimitsOfShape_fppfModulesHigherDirectImage_of_isFiltered f hqc hqs i J
    exact preservesColimitsOfShape_quasicoherentHigherDirectImage B S hS f hqc hqs i J

end AlgebraicGeometry.Stack.AlgebraicStacks

end
