module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExtensionReduction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSectionsIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.CechAmitsurBoundedSmallEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstVanishingAndSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.SurjectiveFromFirstVanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# Right exactness of restriction from the small étale site to the small Zariski site

This file proves the one input the reductions of Stacks 06VE (10) at `τ = étale` and of the third
case of Stacks 0GNB (4) were carrying as a hypothesis: for a short exact sequence `C` of
`𝒪`-modules on the cardinality-bounded small étale site of a scheme `S` whose kernel is
quasi-coherent, the restriction `ε_* = AlgebraicGeometry.SmallEtale.restrictModule` of `C.g` to
the small Zariski site of `S` is again an epimorphism.  It is the source's `H^1(U, 𝓕₁) = 0` step,
Descent, Proposition 03DW at `τ = étale`, and with it both clauses are discharged.

## The argument

1. A section of `C.X₃` over an **affine** object of the small étale site lifts to `C.X₂`.  This is
   Cohomology on Sites, Lemma 03F8 —
   `Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology` — whose Čech input is the
   vanishing `AlgebraicGeometry.SmallEtale.isZero_cechCohomology_succ_associatedPresheaf`, Descent,
   Lemma 03FJ on this site, and whose cofinality input is
   `AlgebraicGeometry.SmallEtale.standardCoveringsAreCofinal`.
2. The affine opens of `S` are a basis of its topology, and an affine open read in the small
   étale site is an affine object of it, so step 1 gives local surjectivity of `ε_*C.g` on `S`
   and hence the epimorphism, by
   `Stacks.Cohomology.ObjectSections.epi_of_surjective_on_presieve`.

## The cofinality input, and that it is discharged

Lemma 03F8 asks for a cofinal system of coverings on which the Čech cohomology vanishes.  Here
that system is the **standard** coverings — finite, with affine members, of an affine object —
and their cofinality is `AlgebraicGeometry.SmallEtale.standardCoveringsAreCofinal`, proved here
from three things already on this site: a covering sieve contains a covering family
(`AlgebraicGeometry.SmallEtale.exists_isCovering_sieve₀_le`), each member of that family is
covered by its affine opens lying over affine opens of `S`
(`AlgebraicGeometry.SmallEtale.affineSubordinateCover`), and an affine object is quasi-compact,
so finitely many of the resulting affine arrows already cover.

So nothing below is conditional, and the two tags are carried:
`essImage_X₂_of_shortExact` is Stacks 06VE (10) at `τ = étale` and
`isQuasicoherentOnSite_shortExact_X₂` is the third case of Stacks 0GNB (4).  The reductions in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleExtensionReduction.lean` and
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQuasicoherentTransfer.lean` keep their hypothesised forms and keep carrying no
attribute; the attributes sit on the discharged statements here.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_cechCohomology_succ_of_isQuasicoherentOnSite`: the
  positive-degree Čech cohomology of a quasi-coherent module on a standard covering of the
  bounded small étale site vanishes.
* `AlgebraicGeometry.SmallEtale.standardCoveringsAreCofinal`: the standard coverings of an affine
  object are cofinal among its covering sieves.
* `AlgebraicGeometry.SmallEtale.surjective_val_app_of_shortExact_of_cofinal`: Stacks 03F8 on this
  site — a section over an affine object lifts.
* `AlgebraicGeometry.SmallEtale.epi_restrictModule_map`: **the hypothesis `hepi` of
  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExtensionReduction`,
  discharged** — restriction to the small Zariski site is right exact at a short exact sequence
  with quasi-coherent kernel.
* `AlgebraicGeometry.SmallEtale.essImage_X₂_of_shortExact`: **Stacks 06VE (10) at `τ = étale`.**
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_shortExact_X₂`: **the third case of
  Stacks 0GNB (4)**, now unconditional.  The
  `CategoryTheory.ObjectProperty.IsClosedUnderExtensions` instance it gives is
  `AlgebraicGeometry.SmallEtale.isClosedUnderExtensions_isQuasicoherentOnSite`, in
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQuasicoherentExtensions.lean`.

## References

* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CechSite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The Čech input: vanishing for a quasi-coherent module -/

/-- **The positive-degree Čech cohomology of a quasi-coherent `𝒪`-module on a standard covering
of the bounded small étale site vanishes.**

A quasi-coherent module on this site is the associated module of a quasi-coherent `𝒪_S`-module,
by Stacks 03DX (2) in the form
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`, and the sections of such
an associated module are the quasi-coherent pullback presheaf on the nose, by
`AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections`; so this is
`AlgebraicGeometry.SmallEtale.isZero_cechCohomology_succ_associatedPresheaf` transported along
one isomorphism. -/
public theorem isZero_cechCohomology_succ_of_isQuasicoherentOnSite
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    {T : SmallEtale B S hS} (E : PreZeroHypercover.{u} T)
    (hE : IsBoundedStandardCovering B S hS E) (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E G.val.presheaf p) := by
  obtain ⟨𝓕, ⟨e⟩⟩ := quasicoherentIsEssImageAssociatedModule B S hS G hG
  have : 𝓕.obj.IsQuasicoherent := 𝓕.property
  have eiso : G.val.presheaf ≅
      (toOver B S hS).op ⋙ quasiCoherentPresheafFunctor S 𝓕.obj :=
    (PresheafOfModules.toPresheaf (structureSheaf B S hS).obj).mapIso
      ((SheafOfModules.forget _).mapIso
        (e.symm ≪≫ associatedModuleIsoOfSections B S hS 𝓕.obj))
  exact (isZero_cechCohomology_succ_associatedPresheaf B S hS 𝓕.obj E hE p hp).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).mapIso
      ((Stacks.CechSite.cechComplexFunctor E).mapIso eiso))

/-! ### Cofinality of the standard coverings -/

/-- The statement that the standard coverings of an affine object of the bounded small étale site
are cofinal among its covering sieves: the hypothesis `hCovCofinal` of [Stacks, Tag 03F8] for
this site.  It is named so that the step that consumes it can be read off, and it is proved
immediately below as `AlgebraicGeometry.SmallEtale.standardCoveringsAreCofinal`. -/
public def StandardCoveringsAreCofinal : Prop :=
  ∀ T : SmallEtale B S hS, _root_.AlgebraicGeometry.IsAffine ((toOver B S hS).obj T).left →
    ∀ R : Sieve T, R ∈ topology B S hS T →
      ∃ E : PreZeroHypercover.{u} T,
        IsBoundedStandardCovering B S hS E ∧ E.sieve₀ ≤ R

/-- Every point of the underlying scheme of an object of the bounded small étale site is in the
image of a member of its covering by affine opens lying over affine opens of `S`.  This is the
joint-surjectivity half of
`AlgebraicGeometry.SmallEtale.mem_topology_sieve₀_affineSubordinateCover`, which that statement
uses and does not record. -/
public theorem exists_mem_range_affineSubordinateCover (W : SmallEtale B S hS)
    (y : ↥((toScheme B S hS).obj W)) :
    ∃ j, y ∈ Set.range ⇑((toScheme B S hS).map ((affineSubordinateCover B S hS W).f j)) := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := W.obj.hom.hom.base y) (U := (⊤ : S.Opens)) trivial
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (X := W.obj.left.obj) (x := y) (U := W.obj.hom.hom ⁻¹ᵁ U) hyU
  exact ⟨⟨⟨⟨V, hV⟩, ⟨U, hU⟩, hVU⟩⟩, ⟨⟨y, hyV⟩, rfl⟩⟩

/-- **The standard coverings of an affine object of the bounded small étale site are cofinal
among its covering sieves.**

The covering sieve contains a covering family
(`AlgebraicGeometry.SmallEtale.exists_isCovering_sieve₀_le`); binding it with the covering of
each member by its affine opens over affine opens of `S`
(`AlgebraicGeometry.SmallEtale.affineSubordinateCover`) gives a jointly surjective family of
affine objects still inside the sieve; and the target being affine, hence quasi-compact,
finitely many of its members already cover, which is the finiteness clause of a standard
covering.  The finite index type is reindexed into `Type u` so that the family is a
`CategoryTheory.PreZeroHypercover.{u}`, which is the size the Čech machinery takes. -/
public theorem standardCoveringsAreCofinal : StandardCoveringsAreCofinal B S hS := by
  classical
  intro T hT R hR
  obtain ⟨E₁, hE₁, hle₁⟩ := exists_isCovering_sieve₀_le B S hS hR
  let ι : Type (u + 1) := Σ i : E₁.I₀, (affineSubordinateCover B S hS (E₁.X i)).I₀
  let V : ι → SmallEtale B S hS :=
    fun p ↦ (affineSubordinateCover B S hS (E₁.X p.1)).X p.2
  let a : ∀ p : ι, V p ⟶ T :=
    fun p ↦ (affineSubordinateCover B S hS (E₁.X p.1)).f p.2 ≫ E₁.f p.1
  have hmem : ∀ p : ι, R (a p) :=
    fun p ↦ R.downward_closed (hle₁ _ (E₁.sieve₀_f p.1)) _
  have haff : ∀ p : ι,
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj (V p)) :=
    fun p ↦ p.2.down.1.2
  have hsurj : ∀ x : ↥((toScheme B S hS).obj T),
      ∃ p : ι, x ∈ Set.range ⇑((toScheme B S hS).map (a p)) := by
    intro x
    obtain ⟨i, y, hy⟩ := jointlySurjective_of_isCovering B S hS hE₁ x
    obtain ⟨j, z, hz⟩ := exists_mem_range_affineSubordinateCover B S hS (E₁.X i) y
    refine ⟨⟨i, j⟩, z, ?_⟩
    show ((toScheme B S hS).map
      ((affineSubordinateCover B S hS (E₁.X i)).f j ≫ E₁.f i)) z = x
    rwa [Functor.map_comp, Scheme.Hom.comp_apply, hz]
  have hcs : CompactSpace ((toScheme B S hS).obj T) :=
    have : _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) := hT
    inferInstance
  obtain ⟨T', hT'⟩ := (@isCompact_univ _ _ hcs).elim_finite_subcover
    (fun p : ι ↦ Set.range ⇑((toScheme B S hS).map (a p)))
    (fun p ↦ (Scheme.Hom.isOpenMap ((toScheme B S hS).map (a p))).isOpen_range)
    (fun x _ ↦ Set.mem_iUnion.mpr (hsurj x))
  obtain ⟨n, ⟨eFin⟩⟩ := Finite.exists_equiv_fin (↥T' : Type (u + 1))
  let c : ULift.{u} (Fin n) → ι := fun i ↦ ((eFin.symm i.down : ↥T') : ι)
  refine ⟨{ I₀ := ULift.{u} (Fin n), X := fun i ↦ V (c i), f := fun i ↦ a (c i) },
    ⟨hT, ?_⟩, ?_⟩
  · refine { finite_index := inferInstanceAs (Finite (ULift.{u} (Fin n)))
             affine_source := fun i ↦ haff (c i)
             jointly_surjective := ?_
             standard := fun i ↦ etale_toScheme_map (a (c i)) }
    refine Set.eq_univ_of_univ_subset (fun x _ ↦ ?_)
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp (hT' (Set.mem_univ x))
    refine Set.mem_iUnion.mpr ⟨ULift.up (eFin ⟨p, hp⟩), ?_⟩
    have hc : c (ULift.up (eFin ⟨p, hp⟩)) = p := by simp [c]
    show x ∈ Set.range ⇑((toScheme B S hS).map (a (c (ULift.up (eFin ⟨p, hp⟩)))))
    rwa [hc]
  · rintro Y f hf
    obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
    exact R.downward_closed (hmem (c i)) g

/-! ### Step 1: sections over an affine object -/

/-- **A section of `C.X₃` over an affine object of the bounded small étale site lifts to
`C.X₂`**, for `C` a short exact sequence of `𝒪`-modules with `C.X₁` quasi-coherent.

This is Cohomology on Sites, Lemma 03F8.  Its Čech input is
`AlgebraicGeometry.SmallEtale.isZero_cechCohomology_succ_of_isQuasicoherentOnSite`, which is
Descent, Lemma 03FJ on this site and is unconditional; its cofinality input is `hcof`. -/
public theorem surjective_val_app_of_shortExact_of_cofinal
    (hcof : StandardCoveringsAreCofinal B S hS)
    {C : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) (T : SmallEtale B S hS)
    (hT : _root_.AlgebraicGeometry.IsAffine ((toOver B S hS).obj T).left) :
    Function.Surjective (C.g.val.app (op T)) :=
  Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology.{u, u, u + 1, u}
    (topology B S hS) _
    (Stacks.Cohomology.ObjectSections.shortExact_map_toSheaf
      (topology B S hS) (structureSheaf B S hS) hC)
    T {E : PreZeroHypercover.{u} T | IsBoundedStandardCovering B S hS E}
    (fun E hE ↦ IsBoundedStandardCovering.sieve₀_mem_topology B S hS E hE)
    (hcof T hT)
    (fun _ _ _ _ ↦ inferInstance)
    (fun E hE ↦ isZero_cechCohomology_succ_of_isQuasicoherentOnSite B S hS C.X₁ h₁ E hE 1
      Nat.one_pos)

/-! ### Step 2: the epimorphism after restriction to the small Zariski site -/

/-- **The hypothesis `hepi` of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExtensionReduction`, over
`hcof` alone.**  For a short exact sequence `C` of `𝒪`-modules on the bounded small étale site of
`S` with `C.X₁` quasi-coherent, the restriction of `C.g` to the small Zariski site of `S` is an
epimorphism.

The affine opens of `S` form a basis of its topology
(`AlgebraicGeometry.generate_affineOpensPresieve_mem`) and an affine open read in the small étale
site is an affine object of it, so the surjectivity of step 1 is local surjectivity on `S`. -/
public theorem epi_restrictModule_map_of_cofinal
    (hcof : StandardCoveringsAreCofinal B S hS)
    {C : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) :
    Epi ((restrictModule B S hS).map C.g) :=
  Stacks.Cohomology.ObjectSections.epi_of_surjective_on_presieve
    (Opens.grothendieckTopology ↥S) S.ringCatSheaf _
    (fun V ↦ affineOpensPresieve S V) (fun V ↦ generate_affineOpensPresieve_mem S V)
    (fun _ W _ hg ↦ surjective_val_app_of_shortExact_of_cofinal B S hS hcof hC h₁
      (opensObj B S hS W) hg)

/-! ### The unconditional statements -/

section

variable {B S hS}
variable {C : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))}

/-- **Restriction to the small Zariski site is right exact at a short exact sequence with
quasi-coherent kernel.**  This is the hypothesis `hepi` of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExtensionReduction`,
discharged: it is the source's `H^1(U, 𝓕₁) = 0` step of Descent, Proposition 03DW at
`τ = étale`. -/
public theorem epi_restrictModule_map (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) :
    Epi ((restrictModule B S hS).map C.g) :=
  epi_restrictModule_map_of_cofinal B S hS (standardCoveringsAreCofinal B S hS) hC h₁

/-- **Stacks 06VE (10) at `τ = étale`.**  Given a short exact sequence
`0 → 𝓕₁^a → 𝓔 → 𝓕₂^a → 0` of `𝒪`-modules on the small étale site of `S` — the outer terms being
given as quasi-coherent, which at `τ = étale` is the same as being in the essential image, by
Stacks 03DX (2) — the middle term `𝓔` is in the essential image of
`QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪)`, `𝓕 ↦ 𝓕^a`, namely of `𝓔|_{S_Zar}`.

The source's three steps are
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExtensionReduction`; the one
they carried, right exactness of `ε_*`, is `epi_restrictModule_map` above. -/
@[stacks 06VE "part (10), small site at τ = étale"]
public theorem essImage_X₂_of_shortExact (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite) :
    (associatedModuleQcoh B S hS).essImage C.X₂ :=
  essImage_X₂_of_shortExact_of_epi_restrictModule hC h₁ h₃ (epi_restrictModule_map hC h₁)

/-- **The third case of Stacks 0GNB (4): the middle term of a short exact sequence of
`𝒪`-modules on the small étale site of a scheme is quasi-coherent when the outer two are.**

The source derives this case not from clause (3) but from Stacks 06VE (10), and on this site the
two are the same statement, by
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_essImage_associatedModuleQcoh`. -/
@[stacks 0GNB "clause (4), third case: the middle term of a short exact sequence"]
public theorem isQuasicoherentOnSite_shortExact_X₂ (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherentOnSite
      (R := AlgebraicGeometry.SmallEtale.structureSheaf B S hS) C.X₂ :=
  isQuasicoherentOnSite_X₂_of_shortExact_of_epi_restrictModule hC h₁ h₃
    (epi_restrictModule_map hC h₁)

end

end AlgebraicGeometry.SmallEtale

end
