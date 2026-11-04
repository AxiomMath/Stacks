module

public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.ClauseFive
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.IdealSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit

/-!
# Clause (9) of Stacks Tag 01Q3 implies clause (6), by the source's own argument

[Stacks, Tag 01Q3] closes its second cycle with the implication `(9) ⇒ (6)`, and the argument it
gives for it is one line: a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` is the directed colimit of
its quasi-coherent sub-ideals of finite type ([Stacks, Tag 01PG] — "this is where we use that `X`
is quasi-separated"), clause (9) presents each of those as a quotient of finitely many copies of
`L ^⊗ (-n)`, and the presentations assemble to the generation statement of clause (6), now
without any finiteness or boundedness in `n`.

This file carries out that argument. It is a second proof of the implication
`Stacks.AmpleCharacterization`
`.iSup_range_twistHom_ideal_eq_top_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal`
of `./ClauseSixConverse.lean`, which deduces the same conclusion from clause (1) — that is
logically sufficient for the nine-clause equivalence, but it is not what the source does, and
[Stacks, Tag 01PG] is then used at a different place and for a different sheaf of ideals.

## Main results

* `Stacks.AmpleCharacterization.exists_twistHom_eq`: **every morphism `L ^⊗ (-n) ⟶ F` is one of
  the maps clause (5) sums over**, i.e. is `Stacks.AmpleCharacterization.twistHom L F n m` for a
  global section `m` of `F ⊗ L ^⊗ n`. This is the dictionary the argument needs in order to feed
  the morphisms clause (9) produces to clause (6), and it generalizes
  `Stacks.AmpleCharacterization.exists_twistUnitHom_eq` from `F = 𝒪_X` to every `F`.
* `Stacks.AmpleCharacterization.iSup_range_twistHom_ideal_eq_top_of_exists_epi_biproduct_ideal`:
  **clause (9) implies clause (6)**, directly.

## The argument

Fix a quasi-coherent sheaf of ideals `j : ℐ ⟶ 𝒪_X`, a point `x` and a germ `u ∈ ℐ_x`. The germ is
the germ of a section of `ℐ` over some open neighbourhood of `x`, and restricting to an affine
open `V ∋ x` inside it makes that neighbourhood quasi-compact. [Stacks, Tag 01PG] in the form
`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_section` then produces a
quasi-coherent subobject `G ⊆ ℐ` of finite type and a section of `G` over `V` mapping to that
section of `ℐ`; in particular `u` is the image of a germ of `G` at `x`.

`G.arrow ≫ j` is a monomorphism `G ⟶ 𝒪_X`, so `G` is itself a quasi-coherent sheaf of ideals, of
finite type, and clause (9) applies to it: `G` is a quotient of a finite direct sum of copies of
`L ^⊗ (-n)` with `n > 0`. `Stacks.ModuleBicone.exists_germ_sum_of_epi` writes the germ of `G` as
a finite sum of germs coming from the summands, and pushing that decomposition forward along
`G.arrow` writes `u` as a finite sum `∑ᵢ (b.ι i ≫ p ≫ G.arrow)_x (vᵢ)` of images of morphisms
`L ^⊗ (-n) ⟶ ℐ`. Each of those morphisms is `twistHom L ℐ n mᵢ` for a global section `mᵢ` of
`ℐ ⊗ L ^⊗ n` (`exists_twistHom_eq`), so `u` lies in the sum of the images of the maps of clause
(6), which is the claim.

## Implementation notes

**What plays the part of the inverse translation.** [Stacks, Tag 01PG] is available in this
repository in two forms: `Stacks.IdealSheaf.exists_fg_le_of_mem` for an
`AlgebraicGeometry.Scheme.IdealSheafData`, which is affine-local ideal data and would need a
quasi-coherent submodule of `𝒪_X` to be translated into such data; and
`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_section` for an arbitrary
quasi-coherent module, where the sub-object is a `CategoryTheory.Subobject` of that module. The
second form is the one this argument wants, and it needs no translation at all: a subobject of
`ℐ` comes with its monomorphism `G.arrow : G ⟶ ℐ` into `ℐ`, which *is* the factorisation of the
sub-ideal's inclusion through `j`, and composing with `j` is what exhibits `G` as a sheaf of
ideals in the sense clause (9) quantifies over.

**`exists_twistHom_eq` is the fully-faithfulness of `tensorRight (L ^⊗ n)`.**
`Stacks.AmpleCharacterization.twistHom` is *defined* as the preimage under that functor — an
equivalence, `L ^⊗ n` being invertible — of the composite of the evaluation isomorphism
`L ^⊗ (-n) ⊗ L ^⊗ n ≅ 𝒪_X` with the global section read as a morphism out of the monoidal unit.
Surjectivity of `m ↦ twistHom L F n m` is therefore surjectivity of `m ↦ unitHom _ m`, which is
the bijection between global sections and morphisms out of the unit, transported across that
equivalence; faithfulness turns the resulting identity of whiskerings into the identity of
morphisms.

## References

* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.Ample

universe u

namespace Stacks.AmpleCharacterization

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-! ### Every morphism out of a negative twist is one of the clause's maps -/

/-- **Every morphism `L ^⊗ (-n) ⟶ F` is multiplication by a global section of `F ⊗ L ^⊗ n`**, in
the sense that it is `Stacks.AmpleCharacterization.twistHom L F n m` for some such section `m`.

`twistHom L F n m` is by definition the preimage under `tensorRight (L ^⊗ n)` of
`(L ^⊗ (-n) ⊗ L ^⊗ n ≅ 𝒪_X) ≫ unitHom (F ⊗ L ^⊗ n) m`. Given `ψ`, the section to take is
therefore the one whose associated morphism out of the monoidal unit is
`(L ^⊗ (-n) ⊗ L ^⊗ n ≅ 𝒪_X)⁻¹ ≫ (ψ ▷ L ^⊗ n)`; the two morphisms then agree after whiskering by
`L ^⊗ n`, and `tensorRight (L ^⊗ n)` is faithful, being an equivalence. -/
theorem exists_twistHom_eq (F : X.Modules) (n : ℤ) (ψ : tensorPowModule X L (-n) ⟶ F) :
    ∃ m : Γ(F ⊗ tensorPowModule X L n, ⊤), twistHom L F n m = ψ := by
  have := Stacks.AmpleGlobalGeneration.isEquivalence_tensorRight L n
  set f : 𝟙_ X.Modules ⟶ F ⊗ tensorPowModule X L n :=
    (negTensorCancelIso L n).inv ≫ (ψ ▷ tensorPowModule X L n) with hf
  refine ⟨Stacks.NonvanishingSpelling.sectionsEquiv X (F ⊗ tensorPowModule X L n)
    (Stacks.SectionProduct.monoidalUnitHomEquiv (F ⊗ tensorPowModule X L n) f), ?_⟩
  have hcomp : ∀ m : Γ(F ⊗ tensorPowModule X L n, ⊤),
      unitHom (F ⊗ tensorPowModule X L n) m =
        (Stacks.SectionProduct.monoidalUnitHomEquiv (F ⊗ tensorPowModule X L n)).symm
          ((Stacks.NonvanishingSpelling.sectionsEquiv X
            (F ⊗ tensorPowModule X L n)).symm m) :=
    fun _ => rfl
  have hunit : unitHom (F ⊗ tensorPowModule X L n)
      (Stacks.NonvanishingSpelling.sectionsEquiv X (F ⊗ tensorPowModule X L n)
        (Stacks.SectionProduct.monoidalUnitHomEquiv (F ⊗ tensorPowModule X L n) f)) = f :=
    -- purpose: forward reasoning, not `rw`. The two equivalences meet at the sections of
    -- `F ⊗ tensorPowModule X L n`, whose ring sheaf `X.ringCatSheaf` is a `TopCat.Sheaf`; the
    -- `SheafOfModules.sections` index wants a `Sheaf (Opens.grothendieckTopology ↥X)`. The two
    -- agree by `rfl` but not at `implicit` transparency, so `rw`'s pattern match is run against a
    -- target it considers ill-typed and `Equiv.symm_apply_apply` finds no occurrence. `Eq.trans`
    -- and `congrArg` check the junction at default transparency, where the spellings do agree.
    (hcomp _).trans
      ((congrArg (Stacks.SectionProduct.monoidalUnitHomEquiv (F ⊗ tensorPowModule X L n)).symm
          ((Stacks.NonvanishingSpelling.sectionsEquiv X
            (F ⊗ tensorPowModule X L n)).symm_apply_apply
            (Stacks.SectionProduct.monoidalUnitHomEquiv (F ⊗ tensorPowModule X L n) f))).trans
        ((Stacks.SectionProduct.monoidalUnitHomEquiv
          (F ⊗ tensorPowModule X L n)).symm_apply_apply f))
  refine (CategoryTheory.MonoidalCategory.tensorRight (tensorPowModule X L n)).map_injective ?_
  show twistHom L F n _ ▷ tensorPowModule X L n = ψ ▷ tensorPowModule X L n
  rw [whiskerRight_twistHom, hunit, hf, Iso.hom_inv_id_assoc]

/-! ### Clause (9) implies clause (6) -/

/-- **Clause (9) of [Stacks, Tag 01Q3] implies clause (6)**, by the source's own argument through
[Stacks, Tag 01PG] rather than through ampleness.

Given a quasi-coherent sheaf of ideals `j : ℐ ⟶ 𝒪_X`, a point `x` and a germ `u ∈ ℐ_x`: the germ
comes from a section of `ℐ` over an affine open `V ∋ x`, and Tag 01PG in the form
`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_section` — where quasi-separatedness
is used — puts that section inside a quasi-coherent subobject `G ⊆ ℐ` of finite type. Then
`G.arrow ≫ j` is a monomorphism, so clause (9) applies to `G` and writes it as a quotient of a
finite direct sum of copies of `L ^⊗ (-n)` with `n > 0`; the germ of `G` decomposes as a finite
sum of germs from the summands (`Stacks.ModuleBicone.exists_germ_sum_of_epi`), and pushing the
decomposition forward along `G.arrow` writes `u` as a finite sum of images of morphisms
`L ^⊗ (-n) ⟶ ℐ`, each of which is one of the maps of clause (6) by
`Stacks.AmpleCharacterization.exists_twistHom_eq`.

The other proof of this implication, `Stacks.AmpleCharacterization`
`.iSup_range_twistHom_ideal_eq_top_of_quasiSeparatedSpace_and_exists_epi_biproduct_ideal`, goes
`(9) ⇒ (1) ⇒ (6)` instead; both are kept, as the tag's implication and as the route the
nine-clause equivalence was first closed along. -/
@[stacks 01Q3 "clause (9) implies (6)"]
theorem iSup_range_twistHom_ideal_eq_top_of_exists_epi_biproduct_ideal [CompactSpace X]
    (h : QuasiSeparatedSpace X ∧ ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j →
      J.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} J →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ J), Epi p) :
    ∀ (J : X.Modules) (j : J ⟶ unitModule X), Mono j → J.IsQuasicoherent →
      ∀ x : X, (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(J ⊗ tensorPowModule X L (n : ℤ), ⊤)),
        LinearMap.range (Stacks.ModuleStalk.map (twistHom L J (n : ℤ) m) x)) = ⊤ := by
  obtain ⟨hqs, h9⟩ := h
  have := hqs
  intro J j hj hJ x
  have := hj
  have := hJ
  refine eq_top_iff.mpr fun u _ => ?_
  -- the germ `u` is the germ of a section of `ℐ` over an affine, hence quasi-compact, open
  obtain ⟨W, hxW, s, hs⟩ := TopCat.Presheaf.exists_germ_eq J.presheaf u
  obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
  have hVle : V ≤ W := hVW
  have hgerm : (J.presheaf.germ V x hxV).hom (J.presheaf.map (homOfLE hVle).op s) = u := by
    rw [TopCat.Presheaf.germ_res_apply, hs]
  -- [Stacks, Tag 01PG]: a finite type quasi-coherent sub-ideal carrying that section
  obtain ⟨G, hGqc, hGft, t, ht⟩ :=
    AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_section J V hVaff.isCompact
      (J.presheaf.map (homOfLE hVle).op s)
  have := hGqc
  -- clause (9), applied to that sub-ideal
  obtain ⟨n, ι, hιfin, hn, b, hb, p, hp⟩ :=
    h9 (G : X.Modules) (G.arrow ≫ j) inferInstance hGqc hGft
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
  have hk : 1 ≤ k := by exact_mod_cast hn
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨v, hv⟩ := Stacks.ModuleBicone.exists_germ_sum_of_epi hb p hp x
    (((G : X.Modules).presheaf.germ V x hxV).hom t)
  -- the decomposition of the germ, pushed forward along `G ⟶ ℐ`
  have hu : u = ∑ i : ι, Stacks.ModuleStalk.mapFun (b.ι i ≫ p ≫ G.arrow) x (v i) := by
    have h1 : Stacks.ModuleStalk.mapFun G.arrow x
        (((G : X.Modules).presheaf.germ V x hxV).hom t) = u := by
      rw [Stacks.ModuleStalk.mapFun_germ, ht, hgerm]
    have hsum : Stacks.ModuleStalk.mapFun G.arrow x
        (∑ i : ι, Stacks.ModuleStalk.mapFun (b.ι i ≫ p) x (v i)) =
        ∑ i : ι, Stacks.ModuleStalk.mapFun (b.ι i ≫ p ≫ G.arrow) x (v i) := by
      refine Eq.trans (map_sum (Stacks.ModuleStalk.map G.arrow x) _ Finset.univ) ?_
      exact Finset.sum_congr rfl fun i _ => by
        rw [Stacks.ModuleStalk.map_apply, ← Stacks.ModuleStalk.mapFun_comp, Category.assoc]
    rw [← h1, hv, hsum]
  -- each summand is the image of one of the maps of clause (6)
  rw [hu]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨m, hm⟩ := exists_twistHom_eq L J (k : ℤ) (b.ι i ≫ p ≫ G.arrow)
  refine Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk
    (Submodule.mem_iSup_of_mem m ⟨v i, ?_⟩))
  rw [Stacks.ModuleStalk.map_apply, hm]

end Stacks.AmpleCharacterization

end
