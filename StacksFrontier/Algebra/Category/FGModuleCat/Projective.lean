module

public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Projective objects of the category of finitely generated modules

Let `R` be a commutative ring. Every finitely generated `R`-module is a quotient of a finite free
module, and a finite free module is projective in `FGModuleCat R`, since the inclusion of finitely
generated modules into all modules is fully faithful and preserves epimorphisms. Hence
`FGModuleCat R` has enough projectives. Conversely a projective object `P` of `FGModuleCat R` is a
retract of a finite free module covering it, so it is a projective module: the inclusion into
`ModuleCat R` preserves projective objects.

## Main results

* `FGModuleCat.projective_of_free`: the finite free module `Rⁿ` is projective in
  `FGModuleCat R`.
* `FGModuleCat.exists_epi`: every finitely generated module is a quotient of some `Rⁿ`.
* `FGModuleCat.enoughProjectives`: `FGModuleCat R` has enough projectives.
* `FGModuleCat.preservesProjectiveObjects_forget₂`: the inclusion of `FGModuleCat R` into
  `ModuleCat R` preserves projective objects.

## Implementation notes

The last two results hold in every universe `v` in which `R` is small, `FGModuleCat.{v} R`
consisting of modules in `Type v`; the finite free cover is then the one of
`Module.exists_finite_presentation`, whose carrier lives in `Type v`. The first two are stated
with the explicit cover `Fin n → R` and therefore in the universe of `R`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace FGModuleCat

variable {R : Type u} [CommRing R]

/-- The finite free module `Rⁿ` is projective in `FGModuleCat R`. -/
lemma projective_of_free (n : ℕ) : Projective (FGModuleCat.of R (Fin n → R)) :=
  (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).projective_of_map_projective
    (ModuleCat.projective_of_free (Pi.basisFun R (Fin n)))

/-- Every finitely generated module is a quotient of a finite free module. -/
lemma exists_epi (M : FGModuleCat.{u} R) :
    ∃ (n : ℕ) (f : FGModuleCat.of R (Fin n → R) ⟶ M), Epi f := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  refine ⟨n, ObjectProperty.homMk (ModuleCat.ofHom g), ?_⟩
  refine (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).epi_of_epi_map ?_
  exact (ModuleCat.epi_iff_surjective _).2 hg

variable [Small.{v} R]

/-- The category of finitely generated modules has enough projectives: every finitely generated
module is a quotient of a finite free module. -/
instance enoughProjectives : EnoughProjectives (FGModuleCat.{v} R) := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  refine ⟨fun M => ?_⟩
  obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
  have : Projective (FGModuleCat.of R P) :=
    F.projective_of_map_projective (inferInstanceAs (Projective (ModuleCat.of R P)))
  have : Epi (FGModuleCat.ofHom f) :=
    F.epi_of_epi_map ((ModuleCat.epi_iff_surjective (ModuleCat.ofHom f)).mpr hf)
  exact ⟨{ p := FGModuleCat.of R P, f := FGModuleCat.ofHom f }⟩

/-- The inclusion of finitely generated modules into modules preserves projective objects: a
projective object of `FGModuleCat R` is a retract of a finite free module, hence a projective
module. -/
instance preservesProjectiveObjects_forget₂ :
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).PreservesProjectiveObjects := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  refine ⟨fun {M} hM => ?_⟩
  obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
  let f' : FGModuleCat.of R P ⟶ M := FGModuleCat.ofHom f
  have : Epi f' := F.epi_of_epi_map ((ModuleCat.epi_iff_surjective (ModuleCat.ofHom f)).mpr hf)
  let g := Projective.factorThru (𝟙 M) f'
  have hg : f.comp g.hom.hom = LinearMap.id :=
    congrArg (fun h => h.hom.hom) (Projective.factorThru_comp (𝟙 M) f')
  have : Module.Projective R M := Module.Projective.of_split g.hom.hom f hg
  exact inferInstanceAs (Projective (ModuleCat.of R M))

end FGModuleCat

end
