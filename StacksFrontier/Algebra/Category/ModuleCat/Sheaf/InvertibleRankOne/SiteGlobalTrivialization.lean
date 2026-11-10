module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallyQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective

/-!
# A global section generating over a covering family trivializes a sheaf of modules

Let `(C, J)` be a site, let `R` be a sheaf of rings on it and let `L` be a sheaf of
`R`-modules. A *global* section `s` of `L` by which multiplication is bijective over a family of
objects covering the final object — and hence, the sieve used being downward closed, over every
object admitting a map into a member of that family — trivializes `L`:

`L ≅ 𝒪`.

This is the global companion of `Stacks.SheafOfModules.overIsoUnitOfBijectiveSmul`, which asks
for bijectivity over *every* object of the slice site `C/U` and concludes only that `L|_U` is
trivial. Here bijectivity is asked for on a covering family only, and the conclusion is about
`L` itself.

## Main results

* `Stacks.SheafOfModules.isIso_unitHomEquiv_symm_of_bijective_smul_of_coversTop`: the morphism
  `𝒪 ⟶ L` determined by such a section is an isomorphism.
* `Stacks.SheafOfModules.nonempty_iso_unit_of_bijective_smul_of_coversTop`: hence `L ≅ 𝒪`.

## Implementation notes

The analogous statement for a ringed space and an open cover is
`Stacks.SheafOfModules.nonempty_iso_unit_of_bijective_smul_on_cover`. Its proof does not
transport to a site: it goes through `TopCat.Sheaf.isIso_iff_isIso_basis`, that is through the
opens below a member of the cover forming a *basis* of the topology, which has no counterpart in
a Grothendieck topology. The route taken here instead is local bijectivity — a morphism of sheaves
of modules which is locally injective and locally surjective is an isomorphism,
`Stacks.SheafOfModules.isIso_of_isLocallyBijective` — and it needs no sheafification hypotheses
on `J`.

The covering is `CategoryTheory.GrothendieckTopology.CoversTop`, so the sieve witnessing local
bijectivity at an object `V` is `CategoryTheory.Sieve.ofObjects Y V`, whose arrows `W ⟶ V` are
those whose *source* admits a map into some `Y i`. That sieve is downward closed for free, which
is what makes the hypothesis below — bijectivity over every object mapping into a member of the
family, rather than over the members alone — exactly what is needed: local injectivity and local
surjectivity are tested after restriction along an arbitrary arrow of the covering sieve.

Multiplication by `s` over an object `W` is the component at `W` of the morphism `𝒪 ⟶ L`
that `SheafOfModules.unitHomEquiv` attaches to `s`, by definition; that identification is
`Stacks.SheafOfModules.bijective_unitHomEquiv_symm_val_app_iff`, which holds by `Iff.rfl`, and
the proof below makes it with a `change`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A global section by which multiplication is bijective over a covering family trivializes
the module, as an isomorphism `𝒪 ⟶ L`.** The morphism `𝒪 ⟶ L` determined by a global section
`s` of `L` is locally injective and locally surjective — at every object the sieve
`Sieve.ofObjects Y` is covering and multiplication by `s` is bijective over each of its arrows —
and a locally bijective morphism of sheaves of modules is an isomorphism. -/
theorem isIso_unitHomEquiv_symm_of_bijective_smul_of_coversTop (L : SheafOfModules.{w} R)
    (s : L.val.sections) {I : Type*} (Y : I → C) (hY : J.CoversTop Y)
    (hs : ∀ (i : I) (W : C), (W ⟶ Y i) →
      Function.Bijective fun r : R.obj.obj (op W) ↦ r • s.eval (op W)) :
    IsIso (L.unitHomEquiv.symm s) := by
  set φ : SheafOfModules.unit R ⟶ L := L.unitHomEquiv.symm s with hφ
  have hbij : ∀ V : C, ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (f : W ⟶ V), T f →
      Function.Bijective
        (((PresheafOfModules.toPresheaf R.obj).map φ.val).app (op W)) := by
    intro V
    refine ⟨Sieve.ofObjects Y V, hY V, ?_⟩
    rintro W f ⟨i, ⟨g⟩⟩
    change Function.Bijective fun r : R.obj.obj (op W) ↦ r • s.eval (op W)
    exact hs i W g
  have hinj : PresheafOfModules.IsLocallyInjective J φ.val :=
    Presheaf.isLocallyInjective_of_exists_mem_sieve J _
      fun V ↦ (hbij V).imp fun _ h ↦ ⟨h.1, fun _ f hf ↦ (h.2 f hf).injective⟩
  have hsurj : PresheafOfModules.IsLocallySurjective J φ.val :=
    Presheaf.isLocallySurjective_of_exists_mem_sieve J _
      fun V ↦ (hbij V).imp fun _ h ↦ ⟨h.1, fun _ f hf ↦ (h.2 f hf).surjective⟩
  exact isIso_of_isLocallyBijective φ

/-- **A global section by which multiplication is bijective over a covering family trivializes
the module.** The site companion of
`Stacks.SheafOfModules.nonempty_iso_unit_of_bijective_smul_on_cover`, which says this for a
ringed space and an open cover. -/
theorem nonempty_iso_unit_of_bijective_smul_of_coversTop (L : SheafOfModules.{w} R)
    (s : L.val.sections) {I : Type*} (Y : I → C) (hY : J.CoversTop Y)
    (hs : ∀ (i : I) (W : C), (W ⟶ Y i) →
      Function.Bijective fun r : R.obj.obj (op W) ↦ r • s.eval (op W)) :
    Nonempty (L ≅ SheafOfModules.unit R) :=
  have := isIso_unitHomEquiv_symm_of_bijective_smul_of_coversTop L s Y hY hs
  ⟨(asIso (L.unitHomEquiv.symm s)).symm⟩

end Stacks.SheafOfModules

end
