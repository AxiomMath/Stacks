module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree

/-!
# A finite locally free morphism is finite free over a small enough affine open

A finite locally free morphism `f : Z ⟶ S` is, by definition, affine with `f_* 𝒪_Z` a finite
locally free `𝒪_S`-module. Over an affine open `V` of `S` small enough for `f_* 𝒪_Z` to be
trivialised, the sections of `𝒪_Z` over `f ⁻¹ᵁ V` therefore form a *finite free* module over
`Γ(V, 𝒪_S)`. This is the input that the Stacks Tag 05Y6 representability statement
`AlgebraicGeometry.relativeHom_representableBy_affine` asks for, and which finite local freeness
alone — being only a local condition — does not supply.

## Main results

* `Stacks.Modules.module_free_of_iso_free`: on an affine scheme, a quasi-coherent module
  isomorphic to a free module has free global sections.
* `Stacks.Morphisms.module_finite_and_free_of_pushforwardStructureSheaf_iso_free`: a finite
  morphism onto an affine scheme whose direct image of the structure sheaf is free has finite
  free global sections.
* `Stacks.Morphisms.exists_isAffineOpen_module_finite_and_free`: every point of the base has an
  affine open neighbourhood `V` over which the base change of a finite locally free morphism has
  finite free global sections.

## Implementation notes

The freeness of the global sections is read off the trivialisation through the Stacks Tag 05JM
bridge `tilde_free_iff_module_free`, transported to the affine scheme at hand along
`Stacks.Modules.tildeIsoRestrictFromSpec` and `restrictFunctor_obj_free_iso`. No localisation is
involved, and in particular no transport of freeness across a ring isomorphism: the base ring is
`Γ(V, 𝒪_S)` throughout.

The statements are phrased for `CategoryTheory.Limits.pullback.fst V.ι f` rather than for the
restriction `f ∣_ V`, because that is the shape in which the representability argument for Stacks
Tag 0BL4 consumes them. The two are identified by
`AlgebraicGeometry.pullbackRestrictIsoRestrict`, and the identification is moved onto the direct
image of the structure sheaf by
`Stacks.Morphisms.pushforwardStructureSheafIsoOfSourceIso`, so that only a single module
structure — the one coming from `AlgebraicGeometry.Scheme.Hom.appTop` of the morphism in question
— ever appears.

`MorphismProperty.IsStableUnderBaseChange` for `Stacks.Morphisms.IsFiniteLocallyFree` is supplied
as a term: `@Stacks.Morphisms.IsFiniteLocallyFree` has implicit rather than strict implicit scheme
binders, so its coercion to a `CategoryTheory.MorphismProperty` has a discrimination-tree key that
instance search does not match; `AlgebraicGeometry.IsFinite` behaves the same way.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Modules

/-- **On an affine scheme, a quasi-coherent module isomorphic to a free module has free global
sections.** The trivialisation is carried to `Spec Γ(X, ⊤)` along
`AlgebraicGeometry.IsAffineOpen.fromSpec` of the whole space, where
`tilde_free_iff_module_free` reads it as freeness of the module of sections. -/
theorem module_free_of_iso_free {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] (I : Type u) (e : F ≅ SheafOfModules.free.{u} I) :
    Module.Free Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) := by
  have hXtop : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  refine (tilde_free_iff_module_free Γ(X, ⊤) Γ(F, (⊤ : X.Opens))).mp ⟨I, ⟨?_⟩⟩
  exact tildeIsoRestrictFromSpec F hXtop ≪≫
    (Scheme.Modules.restrictFunctor hXtop.fromSpec).mapIso e ≪≫
      restrictFunctor_obj_free_iso hXtop.fromSpec I

end Stacks.Modules

namespace Stacks.Morphisms

/-- **The direct image of the structure sheaf is unchanged by an isomorphism of the source.**
Pushing forward along `w.hom ≫ p` is pushing forward along `p` the direct image along `w.hom`,
and the latter is the structure sheaf of the target of `w`. -/
def pushforwardStructureSheafIsoOfSourceIso {S Z Z' : Scheme.{u}} (w : Z ≅ Z') (p : Z' ⟶ S) :
    pushforwardStructureSheaf p ≅ pushforwardStructureSheaf (w.hom ≫ p) :=
  ((Scheme.Modules.pushforward p).mapIso (pushforwardStructureSheafIsoUnit w)).symm ≪≫
    (Scheme.Modules.pushforwardComp w.hom p).app _

/-- **A finite morphism onto an affine scheme whose direct image of the structure sheaf is free
has finite free global sections.** Finiteness of the module is finiteness of the morphism, and
freeness is `Stacks.Modules.module_free_of_iso_free`; the module structure is the one induced by
`AlgebraicGeometry.Scheme.Hom.appTop`, which is definitionally the module structure on the
sections of the direct image. -/
theorem module_finite_and_free_of_pushforwardStructureSheaf_iso_free {S Z : Scheme.{u}}
    [IsAffine S] (p : Z ⟶ S) [IsFinite p] (I : Type u)
    (e : pushforwardStructureSheaf p ≅ SheafOfModules.free.{u} I) :
    letI := p.appTop.hom.toAlgebra
    Module.Finite Γ(S, ⊤) Γ(Z, ⊤) ∧ Module.Free Γ(S, ⊤) Γ(Z, ⊤) := by
  let := p.appTop.hom.toAlgebra
  exact ⟨module_finite_pushforwardStructureSheaf p ⟨⊤, isAffineOpen_top S⟩,
    Stacks.Modules.module_free_of_iso_free (pushforwardStructureSheaf p) I e⟩

/-- **A finite locally free morphism becomes finite free over a small enough affine open of the
base.** Every point of the base has an affine open neighbourhood `V` such that the global
sections of the base change of `f` along `V` form a finite free module over `Γ(V, 𝒪_S)`.

Finite local freeness of `f` supplies an open neighbourhood on which `f_* 𝒪_Z` is trivialised;
shrinking it to an affine open `V` keeps the trivialisation, and over `V` the direct image is the
direct image along the base change, whose sections are therefore finite free. -/
theorem exists_isAffineOpen_module_finite_and_free {Z S : Scheme.{u}} (f : Z ⟶ S)
    [IsFiniteLocallyFree f] (s : S) :
    ∃ V : S.Opens, IsAffineOpen V ∧ s ∈ V ∧
      letI := (pullback.fst V.ι f).appTop.hom.toAlgebra
      (Module.Finite Γ(V.toScheme, ⊤) Γ(pullback V.ι f, ⊤) ∧
        Module.Free Γ(V.toScheme, ⊤) Γ(pullback V.ι f, ⊤)) := by
  obtain ⟨U, hsU, I, -, ⟨e⟩⟩ := ((isFiniteLocallyFree_iff_pointwise f).mp ‹_›).2 s
  obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hsU
  refine ⟨V, hV, hsV, ?_⟩
  have hr : Set.range V.ι.base ⊆ Set.range U.ι.base := by
    simpa [Scheme.Opens.range_ι] using hVU
  obtain ⟨e₁⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset U.ι V.ι
    (pushforwardStructureSheaf f) I hr e
  have e₂ : pushforwardStructureSheaf (f ∣_ V) ≅ SheafOfModules.free.{u} I :=
    (pushforwardStructureSheafRestrictIso f V).symm ≪≫ e₁
  have hw : (pullbackSymmetry V.ι f ≪≫ pullbackRestrictIsoRestrict f V).hom ≫ (f ∣_ V)
      = pullback.fst V.ι f := by
    rw [Iso.trans_hom, Category.assoc, pullbackRestrictIsoRestrict_hom_morphismRestrict,
      pullbackSymmetry_hom_comp_snd]
  have e₃ := (pushforwardStructureSheafIsoOfSourceIso
    (pullbackSymmetry V.ι f ≪≫ pullbackRestrictIsoRestrict f V) (f ∣_ V)).symm ≪≫ e₂
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) :=
    isFiniteLocallyFree_isStableUnderBaseChange
  let : IsAffine V.toScheme := hV
  let : IsFiniteLocallyFree (pullback.fst V.ι f) :=
    hbc.of_isPullback (IsPullback.of_hasPullback V.ι f).flip ‹IsFiniteLocallyFree f›
  let : IsFinite (pullback.fst V.ι f) := IsFiniteLocallyFree.isFinite _
  exact module_finite_and_free_of_pushforwardStructureSheaf_iso_free
    (pullback.fst V.ι f) I (hw ▸ e₃)

end Stacks.Morphisms

end
