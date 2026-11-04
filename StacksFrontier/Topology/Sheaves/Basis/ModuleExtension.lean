module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Basis.ModuleRestriction

/-!
# Extending a sheaf of modules off a basis

Stacks 009T: let `X` be a topological space, `B` a basis for its topology, `O` a sheaf of rings
on `B` and `F` a sheaf of `O`-modules on `B`. Let `O^ext` be the sheaf of rings on `X` extending
`O` and `F^ext` the abelian sheaf on `X` extending `F` (Stacks 009Q). Then there is a canonical
map `O^ext × F^ext → F^ext` agreeing with the given one over elements of `B`, endowing `F^ext`
with the structure of an `O^ext`-module.

## Modelling

The sheaf of rings on `B` is presented by its extension: we take `𝒪 : TopCat.Sheaf RingCat X`
and put `O := 𝒪|_B = restrictRingSheafToBasis hB 𝒪`. This loses nothing, since by Stacks 009Q
every sheaf of rings on `B` is the restriction of a sheaf of rings on `X`, uniquely up to unique
isomorphism.

`F`, a sheaf of `O`-modules on `B`, is then `N : ModuleSheafOnBasis hB 𝒪`, i.e. a
`SheafOfModules (𝒪|_B)`. In this bundled presentation the scalar action *is* part of the datum,
so "a map `O^ext × F^ext → F^ext` endowing `F^ext` with the structure of an `O^ext`-module" is
an object `M : SheafOfModules 𝒪`, and "which agrees with the given map over elements of `B`" is
an isomorphism `(restrictModuleSheaf hB 𝒪).obj M ≅ N` of sheaves of `𝒪|_B`-modules.

Two declarations cover the tag.

* `exists_moduleStructure_on_extension` gives the module structure together with the agreement
  over elements of `B`, and states its canonicity: for any other `𝒪`-module structure whose
  restriction to `B` recovers `F`, there is a *unique* isomorphism to it inducing the given
  identification.
* `restrictToSheaf_iso` says that such an `M` is a module structure on `F^ext` and not on some
  unrelated sheaf: the restriction to `B` of the underlying abelian sheaf of `M` is isomorphic
  to the underlying abelian sheaf of `N`, so the underlying abelian sheaf of `M` is an extension
  of `F` off `B` — hence, by the uniqueness in Stacks 009Q, is `F^ext`. Restriction of module
  sheaves to `B` is, definitionally, restriction of the underlying abelian sheaves
  (`restrictModuleSheaf_comp_toSheaf`), which is what makes this work.

## Proof

Everything is read off from Stacks 009U
(`Stacks.BasisRestriction.isEquivalence_restrictModuleSheaf`), which says that restriction to `B`
is an equivalence `Mod(𝒪) ≌ Mod(𝒪|_B)`: existence of `M` and the identification over `B` are
essential surjectivity, and the uniqueness clause is fullness and faithfulness.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace BasesSheaves

universe u

open Stacks.BasisRestriction

attribute [local instance_reducible] TopCat.Sheaf

variable {X : TopCat.{u}}

/-- Restriction of sheaves of `𝒪`-modules to the basis `B`, followed by passage to the
underlying abelian sheaf, is passage to the underlying abelian sheaf followed by restriction of
abelian sheaves — both being the pushforward along `B ↪ Opens X`, this holds by definition. -/
lemma restrictModuleSheaf_comp_toSheaf {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) :
    (restrictModuleSheaf hB 𝒪 ⋙ SheafOfModules.toSheaf _) =
      (SheafOfModules.toSheaf 𝒪 ⋙ (basisInclusion B).sheafPushforwardContinuous AddCommGrpCat
        (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)) := rfl

/-- **Stacks 009T (Lemma 6.30.11), the module structure on the extension.**

Let `X` be a topological space, `B` a basis for its topology, `𝒪` a sheaf of rings on `X`
(playing the role of `O^ext`, the extension of a sheaf of rings `O` on `B`), and `N` a sheaf of
`𝒪|_B`-modules on `B` (the sheaf `F`).

Then there is a sheaf of `𝒪`-modules `M` on `X` — its scalar action `𝒪 × M → M` being the
asserted map `O^ext × F^ext → F^ext` — together with an isomorphism
`basis_iso : M|_B ≅ N` of sheaves of `𝒪|_B`-modules, i.e. the module structure agrees with the
given one over elements of `B`. The map is canonical: for any other sheaf of `𝒪`-modules `M'`
with an identification `M'|_B ≅ N` there is a *unique* isomorphism `M ≅ M'` inducing it.

That the underlying abelian sheaf of `M` is `F^ext` is `restrictToSheaf_iso`. -/
@[stacks 009T "the canonical module structure, agreeing with the given one over elements of B",
  ega "0 3.2.5" "special case"]
theorem exists_moduleStructure_on_extension {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) (N : ModuleSheafOnBasis hB 𝒪) :
    ∃ (M : SheafOfModules.{u} 𝒪) (basis_iso : (restrictModuleSheaf hB 𝒪).obj M ≅ N),
      ∀ (M' : SheafOfModules.{u} 𝒪) (θ : (restrictModuleSheaf hB 𝒪).obj M' ≅ N),
        ∃! Φ : M ≅ M', (restrictModuleSheaf hB 𝒪).mapIso Φ ≪≫ θ = basis_iso := by
  have hequiv := isEquivalence_restrictModuleSheaf hB 𝒪
  refine ⟨(restrictModuleSheaf hB 𝒪).objPreimage N,
    (restrictModuleSheaf hB 𝒪).objObjPreimageIso N, fun M' θ => ?_⟩
  -- Fullness gives a comparison isomorphism; faithfulness makes it unique.
  refine ⟨(restrictModuleSheaf hB 𝒪).preimageIso
    ((restrictModuleSheaf hB 𝒪).objObjPreimageIso N ≪≫ θ.symm), ?_, fun Ψ hΨ => ?_⟩
  · ext : 1
    simp [Functor.preimageIso_hom, Functor.map_preimage]
  · refine Iso.ext ((restrictModuleSheaf hB 𝒪).map_injective ?_)
    have h := congrArg Iso.hom hΨ
    simp only [Iso.trans_hom, Functor.mapIso_hom] at h
    simp only [Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom, Iso.symm_hom]
    rw [← h]
    simp

/-- **Stacks 009T (Lemma 6.30.11), the module structure lives on `F^ext`.**

An isomorphism `M|_B ≅ N` of sheaves of `𝒪|_B`-modules induces an isomorphism of the underlying
abelian sheaves on `B`. Hence the module structure produced by
`exists_moduleStructure_on_extension` is carried by an abelian sheaf on `X` whose restriction to
`B` is the underlying abelian sheaf of `N` — that is, by an extension of `F` off `B`, which by
the uniqueness in Stacks 009Q is `F^ext`. -/
@[stacks 009T "the module structure is carried by the abelian extension F^ext of F"]
noncomputable def restrictToSheaf_iso {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (𝒪 : TopCat.Sheaf RingCat X) (M : SheafOfModules.{u} 𝒪) (N : ModuleSheafOnBasis hB 𝒪)
    (basis_iso : (restrictModuleSheaf hB 𝒪).obj M ≅ N) :
    ((basisInclusion B).sheafPushforwardContinuous AddCommGrpCat
          (basisGrothendieckTopology hB) (Opens.grothendieckTopology X)).obj
        ((SheafOfModules.toSheaf 𝒪).obj M) ≅
      (SheafOfModules.toSheaf _).obj N :=
  (SheafOfModules.toSheaf (restrictRingSheafToBasis hB 𝒪)).mapIso basis_iso

end BasesSheaves
