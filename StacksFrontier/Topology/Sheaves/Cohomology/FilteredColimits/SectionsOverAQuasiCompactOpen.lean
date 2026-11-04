module

public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.Topology.Bases.QuasiCompactOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Sections over a quasi-compact open commute with filtered colimits of modules (Stacks 009F)

Let `X` be a topological space with a basis of quasi-compact opens whose pairwise intersections
are quasi-compact (the hypotheses (H1) and (H2) of Stacks 0069), let `O_X` be a sheaf of rings on
`X` and let `U` be a quasi-compact open of `X`.  Then the sections functor
`Γ(U, -) : Mod(O_X) ⥤ Ab` preserves filtered colimits.  This is Stacks 009F for sheaves of
modules, and it is the degree-zero input of Stacks 01FF.

The mathematics of 009F is already available for sheaves of **sets**, on an arbitrary site, as
Stacks 0738 (`CategoryTheory.Sheaf.injective_and_bijective_colimit_post_sheafSections`).  What
this file supplies is the passage from there to sheaves of modules, in three steps, each of which
is a change of coefficient category:

1. *Sets to sets on a space.*  Part (4) of Stacks 0738 asks for a cofinal system of finite
   coverings of `U` whose pairwise fibre products are quasi-compact objects of the site.  On
   `Opens X` the fibre product is the intersection, so (H1) and (H2) supply exactly that, via
   `hasCofinalCompactRefinements_of_isCompact_isOpen` (Stacks 0069 (C3)); and a quasi-compact
   open is a quasi-compact object of the site, which is
   `isQuasiCompactObject_of_isCompact` below.
2. *Sets to abelian groups.*  The forgetful functor `Ab ⥤ Set` reflects isomorphisms and
   preserves filtered colimits, and it preserves sheafification
   (`CategoryTheory.GrothendieckTopology.PreservesSheafification`), so post-composition with it
   commutes with filtered colimits of sheaves; that transports the bijectivity of (1) to the
   `AddCommGrpCat`-valued sections functor.
3. *Abelian groups to modules.*  A sheaf of modules is the sheafification of its underlying
   presheaf of modules (the counit of `PresheafOfModules.sheafificationAdjunction` is an
   isomorphism), colimits of presheaves of modules are computed pointwise, and sheafification is
   a left adjoint; so `SheafOfModules.toSheaf` preserves all colimits.

## Main results

* `Stacks.Cohomology.Sections.isQuasiCompactObject_of_isCompact`: a quasi-compact open of a
  space is a quasi-compact object of the site of its opens (Stacks 090H).
* `Stacks.Cohomology.Sections.preservesColimitsOfShape_sheafSections_type_of_isCompact`:
  Stacks 009F for sheaves of sets on `X`, in the form `Γ(U, -)` preserves filtered colimits.
* `Stacks.Cohomology.Sections.preservesColimitsOfShape_sheafSections_of_isCompact`: the same for
  sheaves of abelian groups.
* `Stacks.Cohomology.Sections.preservesColimitsOfShape_toSheaf`: the forgetful functor
  `Mod(O_X) ⥤ Ab(X)` preserves colimits of any shape for which the coefficient category has
  them.
* `Stacks.Cohomology.Sections.preservesColimitsOfShape_secF_of_isCompact`: **Stacks 009F for
  sheaves of modules**, the degree-zero input of Stacks 01FF.

## Implementation notes

The universes are all equal, as they are throughout the formalization of Stacks 01FF: see the
implementation notes of `StacksDraft.Ch20.Sec18.Tag01FFColimit`.

The type ascription in `PreservesColimitsOfShape I (secF R U : SheafOfModules.{u} R ⥤ _)` is
load-bearing, because `secF` leaves the module universe implicit: without it the elaborator
invents a fresh universe and the resulting statement does not apply to systems of
`SheafOfModules.{u} R`.

## References

* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 0069](https://stacks.math.columbia.edu/tag/0069)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.Sections

/-- **Transfer of colimit preservation along a left adjoint that is essentially surjective on a
diagram.**  If `G : B ⥤ E` is such that `L ⋙ G` preserves `I`-colimits for some `I`-colimit
preserving `L : A ⥤ B`, then `G` preserves the colimit of any diagram `D : I ⥤ B` of the form
`P ⋙ L`.

This is the only argument used three times below: a sheaf is the sheafification of its underlying
presheaf, so every diagram of sheaves is (isomorphic to) a diagram of presheaves followed by
sheafification, and a functor out of sheaves preserves filtered colimits as soon as its
composition with sheafification does. -/
theorem preservesColimit_of_leftAdjointFactorisation {A B E : Type*} [Category A] [Category B]
    [Category E] {I : Type*} [Category I] [HasColimitsOfShape I A] (L : A ⥤ B) (G : B ⥤ E)
    [PreservesColimitsOfShape I L] [PreservesColimitsOfShape I (L ⋙ G)] {D : I ⥤ B} (P : I ⥤ A)
    (e : P ⋙ L ≅ D) :
    PreservesColimit D G :=
  have : PreservesColimit (P ⋙ L) G :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit P))
      (isColimitOfPreserves (L ⋙ G) (colimit.isColimit P))
  preservesColimit_of_iso_diagram G e

/-- **A quasi-compact open is a quasi-compact object of the site of opens (Stacks 090H).**  Every
covering family `{U_i ⟶ U}` of `U` has, by the definition of the topology of a space, the
property that its members cover `U` as a set; quasi-compactness extracts a finite subfamily that
still covers, and that subfamily, with the identity morphisms, refines the given one through
finitely many indices. -/
theorem isQuasiCompactObject_of_isCompact {X : Type u} [TopologicalSpace X] (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    (Opens.grothendieckTopology X).IsQuasiCompactObject U := by
  intro 𝒰 h𝒰
  have hcov : (U : Set X) ⊆ ⋃ i, ((𝒰.X i : Opens X) : Set X) := by
    intro x hx
    obtain ⟨V, g, hg, hxV⟩ := h𝒰 x hx
    obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    exact Set.mem_iUnion.mpr ⟨i, a.le hxV⟩
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i => ((𝒰.X i : Opens X) : Set X))
    (fun i => (𝒰.X i).isOpen) hcov
  refine ⟨{ I₀ := { i // i ∈ t }, X := fun j => 𝒰.X j.1, f := fun j => 𝒰.f j.1 },
    { s₀ := fun j => j.1, h₀ := fun _ => 𝟙 _ }, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact ⟨𝒰.X i, 𝒰.f i, Sieve.ofArrows_mk _ _ (⟨i, hi⟩ : { i // i ∈ t }), hxi⟩
  · refine t.finite_toSet.subset ?_
    rintro _ ⟨j, rfl⟩
    exact j.2

/-- **The hypothesis of part (4) of Stacks 0738, for a quasi-compact open of a space satisfying
(H1) and (H2).**  Every covering sieve of `U` is refined by a finite covering of `U` by
quasi-compact opens all of whose pairwise intersections are quasi-compact; intersections are the
fibre products of `Opens X`, and a quasi-compact open is a quasi-compact object of the site.

The refinement comes from conclusion (C3) of Stacks 0069,
`hasCofinalCompactRefinements_of_isCompact_isOpen`, applied to the family of all the opens whose
morphism into `U` lies in the given sieve. -/
theorem exists_finite_quasiCompact_refinement {X : Type u} [TopologicalSpace X]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X) (U : Opens X)
    (hU : IsCompact (U : Set X)) (S : Sieve U)
    (hS : S ∈ Opens.grothendieckTopology X U) :
    ∃ 𝒱 : PreZeroHypercover.{u} U,
      Finite 𝒱.I₀ ∧ 𝒱.sieve₀ ∈ Opens.grothendieckTopology X U ∧ 𝒱.sieve₀ ≤ S ∧
        ∀ j j' : 𝒱.I₀, ∃ (W : Opens X) (p : W ⟶ 𝒱.X j) (q : W ⟶ 𝒱.X j'),
          IsPullback p q (𝒱.f j) (𝒱.f j') ∧
            (Opens.grothendieckTopology X).IsQuasiCompactObject W := by
  classical
  -- The members of the sieve, indexed by themselves, cover `U`; refine that covering.
  obtain ⟨ι, Jf, W, hWopen, hWcomp, hWeq, hWinter, hWref⟩ :=
    hasCofinalCompactRefinements_of_isCompact_isOpen hBasis hInter U.isOpen hU
      (K := { V : Opens X // ∃ h : V ≤ U, S (homOfLE h) }) (fun k => ((k.1 : Opens X) : Set X))
      (fun k => k.1.isOpen)
      (by
        intro x hx
        obtain ⟨V, g, hg, hxV⟩ := hS x hx
        exact Set.mem_iUnion.mpr ⟨⟨V, g.le, hg⟩, hxV⟩)
  -- `W j ≤ U` for every member of the refinement.
  have hWU : ∀ j ∈ Jf, W j ⊆ (U : Set X) := fun j hj => by
    rw [hWeq]
    exact Set.subset_biUnion_of_mem hj
  -- The refinement as a family of morphisms of `Opens X` with target `U`.
  refine ⟨{ I₀ := ULift.{u, 0} { j // j ∈ Jf }
            X := fun j => ⟨W j.down.1, hWopen _ j.down.2⟩
            f := fun j => homOfLE (hWU _ j.down.2) }, ?_, ?_, ?_, ?_⟩
  · exact Finite.of_equiv _ Equiv.ulift.symm
  · intro x hx
    have hx' : x ∈ (U : Set X) := hx
    rw [hWeq] at hx'
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx'
    exact ⟨_, _, Sieve.ofArrows_mk _ _ (ULift.up ⟨j, hj⟩), hxj⟩
  · intro V g hg
    obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    obtain ⟨k, hk⟩ := hWref _ j.down.2
    exact S.downward_closed (S.downward_closed k.2.2 (homOfLE hk : _ ⟶ (k.1 : Opens X))) a
  · intro j j'
    refine ⟨_, pullback.fst _ _, pullback.snd _ _, IsPullback.of_hasPullback _ _, ?_⟩
    refine isQuasiCompactObject_of_isCompact _ ?_
    rw [CompleteLattice.pullback_eq_inf, Opens.coe_inf]
    exact hWinter _ j.down.2 _ j'.down.2

/-- **Stacks 009F for sheaves of sets (via Stacks 0738).**  If `X` has a basis of quasi-compact
opens with quasi-compact pairwise intersections and `U` is a quasi-compact open, then the
sections functor `Γ(U, -) : Sh(X, Set) ⥤ Set` preserves filtered colimits.

Part (4) of Stacks 0738 gives bijectivity of the canonical map
`colimᵢ Fᵢ(U) ⟶ (colimᵢ Fᵢ)(U)`; for sheaves of sets bijectivity is being an isomorphism, and a
functor preserves a colimit as soon as that comparison map is an isomorphism. -/
theorem preservesColimitsOfShape_sheafSections_type_of_isCompact {X : Type u}
    [TopologicalSpace X] {I : Type u} [SmallCategory I] [IsFiltered I]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X) (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    PreservesColimitsOfShape I
      ((sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op U)) := by
  constructor
  intro F
  have : IsIso
      (colimit.post F ((sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op U))) :=
    (isIso_iff_bijective _).2
      ((CategoryTheory.Sheaf.injective_and_bijective_colimit_post_sheafSections
        (Opens.grothendieckTopology X) F U).2.2.2
        (exists_finite_quasiCompact_refinement hBasis hInter U hU))
  exact preservesColimit_of_isIso_post _ _

/-- **Post-composition with a sheafification-preserving functor commutes with colimits.**  If
`F : A ⥤ B` preserves sheafification and `I`-colimits, then `sheafCompose J F` preserves
`I`-colimits of sheaves: every diagram of sheaves is the sheafification of a diagram of
presheaves, and on presheaves `sheafCompose J F` becomes `(- ⋙ F)` followed by sheafification,
which preserves colimits pointwise. -/
theorem preservesColimitsOfShape_sheafCompose {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {A B : Type*} [Category A] [Category B] {I : Type u}
    [SmallCategory I] [HasSheafify J A] [HasSheafify J B] [HasColimitsOfShape I A]
    [HasColimitsOfShape I B] (F : A ⥤ B) [J.HasSheafCompose F] [J.PreservesSheafification F]
    [PreservesColimitsOfShape I F] :
    PreservesColimitsOfShape I (sheafCompose J F) := by
  have : PreservesColimitsOfShape I (presheafToSheaf J A ⋙ sheafCompose J F) :=
    preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J F (sheafificationAdjunction J A) (sheafificationAdjunction J B))
  constructor
  intro D
  exact preservesColimit_of_leftAdjointFactorisation (presheafToSheaf J A) _
    (D ⋙ sheafToPresheaf J A)
    (Functor.isoWhiskerLeft D (asIso (sheafificationAdjunction J A).counit))

/-- **Stacks 009F for sheaves of abelian groups.**  Under the hypotheses of Stacks 01FF on `X`,
the sections functor `Γ(U, -) : Ab(X) ⥤ Ab` over a quasi-compact open preserves filtered
colimits.

The forgetful functor `Ab ⥤ Set` reflects isomorphisms and preserves filtered colimits, so it
suffices to know that `Γ(U, -)` followed by it preserves them; and that composite *is*
`sheafCompose J (forget Ab)` followed by the sections functor on sheaves of sets, which is the
previous statement. -/
theorem preservesColimitsOfShape_sheafSections_of_isCompact {X : Type u} [TopologicalSpace X]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X) (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    PreservesColimitsOfShape I
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)) := by
  have hT : PreservesColimitsOfShape I
      ((sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op U)) :=
    preservesColimitsOfShape_sheafSections_type_of_isCompact hBasis hInter U hU
  have hS : PreservesColimitsOfShape I
      (sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat.{u})) :=
    preservesColimitsOfShape_sheafCompose _ _
  have hiso : sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat.{u}) ⋙
      (sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op U) ≅
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U) ⋙
        forget AddCommGrpCat.{u} := Iso.refl _
  have hcomp : PreservesColimitsOfShape I
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U) ⋙
        forget AddCommGrpCat.{u}) := preservesColimitsOfShape_of_natIso hiso
  constructor
  intro D
  have : ReflectsColimit
      (D ⋙ (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U))
      (forget AddCommGrpCat.{u}) := reflectsColimit_of_reflectsIsomorphisms _ _
  exact preservesColimit_of_reflects_of_preserves _ (forget AddCommGrpCat.{u})

/-- **The forgetful functor from sheaves of modules to sheaves of abelian groups preserves
colimits.**  A sheaf of modules is the sheafification of its underlying presheaf of modules, and
sheafification of presheaves of modules followed by the forgetful functor to sheaves of abelian
groups is `PresheafOfModules.toPresheaf` followed by sheafification of presheaves of abelian
groups (`PresheafOfModules.sheafificationCompToSheaf`); both of those preserve colimits, the
first because colimits of presheaves of modules are computed pointwise and the second because it
is a left adjoint. -/
theorem preservesColimitsOfShape_toSheaf {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] {I : Type u}
    [SmallCategory I] :
    PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u} R) := by
  have : PreservesColimitsOfShape I
      (PresheafOfModules.sheafification (𝟙 R.obj) ⋙ SheafOfModules.toSheaf.{u} R) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  constructor
  intro D
  exact preservesColimit_of_leftAdjointFactorisation
    (PresheafOfModules.sheafification (𝟙 R.obj)) _ (D ⋙ SheafOfModules.forget R)
    (Functor.isoWhiskerLeft D
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit))

/-- **Stacks 009F for sheaves of modules.**  Let `X` be a topological space with a basis of
quasi-compact opens whose pairwise intersections are quasi-compact, let `O_X` be a sheaf of rings
on `X`, let `U` be a quasi-compact open and let `I` be a filtered index category.  Then the
sections functor `Γ(U, -) : Mod(O_X) ⥤ Ab` preserves `I`-colimits: the canonical map
`colimᵢ Γ(U, Fᵢ) ⟶ Γ(U, colimᵢ Fᵢ)` is an isomorphism.

This is the degree-zero input of Stacks 01FF.  It factors as the forgetful functor to sheaves of
abelian groups, which preserves all colimits, followed by the sections functor on sheaves of
abelian groups, which preserves filtered colimits over a quasi-compact open. -/
theorem preservesColimitsOfShape_secF_of_isCompact {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    PreservesColimitsOfShape I (secF R U : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u}) := by
  have h1 : PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u} R) :=
    preservesColimitsOfShape_toSheaf R
  have h2 : PreservesColimitsOfShape I
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)) :=
    preservesColimitsOfShape_sheafSections_of_isCompact hBasis hInter U hU
  exact inferInstanceAs (PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u} R ⋙
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)))

end Stacks.Cohomology.Sections

end
