module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.ComplementCohomologyModule
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyExcision
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.NaturalComplementComparison
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Sections

/-!
# Cohomology of an open of the complement of a zero locus

Let `A` be a ring, let `a ⊆ A` be an ideal, let `X = Spec A` and let `U = X ∖ V(a)`, viewed as a
scheme. For an open `V` of `U` this file defines the sheaf cohomology `H^p(V, -)` of sheaves of
`𝒪_U`-modules, as `A`-modules, and compares it, naturally in the module, with the cohomology of
`M̃` over an open of `X`: if the image of `V` in `X` is `X ∖ V(J)`, then

`H^p(V, M̃|_U) ≅ H^p(X ∖ V(J), M̃)`

as `A`-modules, naturally in the `A`-module `M`, in every degree `p`. The right-hand side is
`Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor J p`, which is natural in `M` and
compared with local cohomology in `NaturalComplementComparison`.

## Main definitions

* `Stacks.LocalCohomology.complementOpenSections`: `Γ(V, -)` on `𝒪_U`-modules, as `A`-modules.
* `Stacks.LocalCohomology.complementOpenCohomology`: `H^p(V, -)`, the right derived functors of
  `Γ(V, -)` read over `A`.
* `Stacks.LocalCohomology.restrictTildeFunctor`: `M ↦ M̃|_U`.
* `Stacks.LocalCohomology.restrictComplementOpenSectionsIso`: sections over `V` of the restriction
  of a sheaf on `X` are its sections over the image of `V`.
* `Stacks.LocalCohomology.complementOpenCohomologyTildeIso`: **the comparison**
  `H^p(V, M̃|_U) ≅ H^p(X ∖ V(J), M̃)`, natural in `M`, when the image of `V` is `X ∖ V(J)`.
* `Stacks.LocalCohomology.complementOpenCohomologyTopTildeIso`: the case `V = U`, `J = a`.

## Main results

* `Stacks.LocalCohomology.complementZeroLocus_ι_image_preimage`: if `V(a) ⊆ V(J)`, the preimage
  in `U` of `X ∖ V(J)` has image `X ∖ V(J)`.

## Implementation notes

The scalars are those of `Stacks.LocalCohomology.complementSheafCohomology`: restriction along
`Stacks.LocalCohomology.complementTopScalars a`, the composite of `A ≅ Γ(X, 𝒪_X)` with
`U.ι.appTop`.

Restriction to the open subscheme `U` is exact and preserves injective objects, so the right
derived functors of `Γ(V, -) ∘ (-)|_U` are those of `Γ(V, -)` precomposed with `(-)|_U`
(`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`). The sections of a restriction
over `V` are definitionally the sections over `U.ι ''ᵁ V`; only the module structures differ, by
the functoriality of the structure sheaf of `X`, and the comparison is the identity on elements.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.ModuleComparison
open Stacks.LocalCohomologyTilde

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (a : Ideal A)

/-! ### Sections and cohomology over an open of `U` -/

/-- `Γ(V, -)` on sheaves of modules on `U = Spec A ∖ V(a)`, for an open `V` of `U`, as
`A`-modules: sections over `V` with the scalars restricted to `Γ(U, 𝒪_U)` and then to `A` along
`complementTopScalars a`. -/
def complementOpenSections (V : (complementZeroLocus A a : Scheme).Opens) :
    (complementZeroLocus A a : Scheme).Modules ⥤ ModuleCat.{u} A :=
  sectionsOnOpen (complementZeroLocus A a : Scheme).toRingedSpace V ⋙
    ModuleCat.restrictScalars (complementTopScalars a)

/-- `Γ(V, -)` on sheaves of modules on `U`, read over `A`, is additive. -/
instance complementOpenSections_additive (V : (complementZeroLocus A a : Scheme).Opens) :
    (complementOpenSections A a V).Additive :=
  inferInstanceAs (sectionsOnOpen (complementZeroLocus A a : Scheme).toRingedSpace V ⋙
    ModuleCat.restrictScalars (complementTopScalars a)).Additive

/-- `H^p(V, -)` on sheaves of modules on `U = Spec A ∖ V(a)`, for an open `V` of `U`, as
`A`-modules. -/
abbrev complementOpenCohomology (V : (complementZeroLocus A a : Scheme).Opens) (p : ℕ) :
    (complementZeroLocus A a : Scheme).Modules ⥤ ModuleCat.{u} A :=
  (sectionsOnOpen (complementZeroLocus A a : Scheme).toRingedSpace V).rightDerived p ⋙
    ModuleCat.restrictScalars (complementTopScalars a)

/-- `H^p(V, -)` is the right derived functor of `Γ(V, -)` read over `A`: restriction of scalars
is exact, so it may be applied before or after deriving. -/
def complementOpenCohomologyIsoRightDerived (V : (complementZeroLocus A a : Scheme).Opens)
    (p : ℕ) :
    complementOpenCohomology A a V p ≅ (complementOpenSections A a V).rightDerived p :=
  rightDerivedCompIso (A := ModuleSheaves (complementZeroLocus A a : Scheme).toRingedSpace)
    (sectionsOnOpen (complementZeroLocus A a : Scheme).toRingedSpace V)
    (ModuleCat.restrictScalars (complementTopScalars a)) _ (Iso.refl _) p

/-- `M ↦ M̃|_U`, the sheaf attached to an `A`-module restricted to `U = Spec A ∖ V(a)`. -/
abbrev restrictTildeFunctor : ModuleCat.{u} A ⥤ (complementZeroLocus A a : Scheme).Modules :=
  tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι

/-! ### Sections of a restriction -/

/-- The scalars of the sections over `V` of a restriction to `U`, pushed to `Spec A`, are the
scalars of the sections over `U.ι ''ᵁ V`. -/
theorem complementTopScalars_restrict (V : (complementZeroLocus A a : Scheme).Opens) (r : A) :
    ((complementZeroLocus A a).ι.appIso V).inv
        ((complementZeroLocus A a : Scheme).presheaf.map (homOfLE le_top).op
          (complementTopScalars a r)) =
      (Spec (CommRingCat.of A)).presheaf.map
        (homOfLE (le_top (a := (complementZeroLocus A a).ι ''ᵁ V))).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (complementZeroLocus A a).ι.appTop ≫
      (complementZeroLocus A a : Scheme).presheaf.map (homOfLE le_top).op ≫
        ((complementZeroLocus A a).ι.appIso V).inv =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec (CommRingCat.of A)).presheaf.map
        (homOfLE (le_top (a := (complementZeroLocus A a).ι ''ᵁ V))).op := by
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Opens.ι_appTop,
      Scheme.Opens.toScheme_presheaf_map]
    rfl
  exact congrArg (fun φ => φ.hom r) key

/-- **Sections of a restriction to `U` over `V` are sections over the image of `V`.** For a sheaf
of modules `G` on `X = Spec A` and an open `V` of `U = Spec A ∖ V(a)`, the `A`-module
`Γ(V, G|_U)` is `Γ(U.ι ''ᵁ V, G)` read over `A`, naturally in `G`; on elements the comparison is
the identity. -/
def restrictComplementOpenSectionsIso (V : (complementZeroLocus A a : Scheme).Opens) :
    Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι ⋙ complementOpenSections A a V ≅
      sectionsOnOpen (Spec (CommRingCat.of A)).toRingedSpace
          ((complementZeroLocus A a).ι ''ᵁ V) ⋙
        globalToBase (CommRingCat.of A) :=
  NatIso.ofComponents
    (fun G => (AddEquiv.toLinearEquiv
      (M := ↑((complementOpenSections A a V).obj
        ((Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).obj G)))
      (M₂ := ↑((globalToBase (CommRingCat.of A)).obj
        ((sectionsOnOpen (Spec (CommRingCat.of A)).toRingedSpace
          ((complementZeroLocus A a).ι ''ᵁ V)).obj G)))
      (AddEquiv.refl _) (fun r x => by
        let y : Γ(G, (complementZeroLocus A a).ι ''ᵁ V) := x
        exact congrArg (fun s => s • y) (complementTopScalars_restrict A a V r))).toModuleIso)
    (fun _ => rfl)

/-! ### The comparison of cohomology -/

/-- Reading a sheaf of modules on `Spec A` over `A` is additive. -/
instance globalToBase_additive' : (globalToBase (CommRingCat.of A)).Additive :=
  Stacks.LocalCohomologyTilde.globalToBase_additive

/-- `Γ(W, -)` on sheaves of modules on `Spec A`, read over `A`, is additive. -/
instance sectionsOnOpen_globalToBase_additive (W : (Spec (CommRingCat.of A)).Opens) :
    (sectionsOnOpen (Spec (CommRingCat.of A)).toRingedSpace W ⋙
      globalToBase (CommRingCat.of A)).Additive :=
  haveI := sectionsOnOpen_additive (Spec (CommRingCat.of A)).toRingedSpace W
  haveI := globalToBase_additive' A
  inferInstance

/-- The cohomology over `V` of a restriction to `U` is the cohomology over the image of `V` of
the sheaf on `X = Spec A`, read over `A`, naturally in the sheaf. Restriction to `U` is exact and
preserves injective objects. -/
def restrictComplementOpenCohomologyIso (V : (complementZeroLocus A a : Scheme).Opens) (p : ℕ) :
    Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι ⋙
        complementOpenCohomology A a V p ≅
      (sectionsOnOpen (Spec (CommRingCat.of A)).toRingedSpace
          ((complementZeroLocus A a).ι ''ᵁ V)).rightDerived p ⋙
        globalToBase (CommRingCat.of A) :=
  letI : Functor.Additive ((sectionsOnOpen (Spec (CommRingCat.of A)).toRingedSpace
        ((complementZeroLocus A a).ι ''ᵁ V) :
          (Spec (CommRingCat.of A)).Modules ⥤ _)) := { map_add := rfl }
  letI : Functor.Additive ((sectionsOnOpen (Spec (CommRingCat.of A)).toRingedSpace
        ((complementZeroLocus A a).ι ''ᵁ V) ⋙ globalToBase (CommRingCat.of A) :
          (Spec (CommRingCat.of A)).Modules ⥤ ModuleCat.{u} A)) :=
    { map_add := rfl }
  letI := sectionsOnOpen_additive (Spec (CommRingCat.of A)).toRingedSpace
    ((complementZeroLocus A a).ι ''ᵁ V)
  haveI : (globalToBase (CommRingCat.of A)).PreservesHomology :=
    Stacks.LocalCohomologyTilde.globalToBase_preservesHomology
  Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι)
      (complementOpenCohomologyIsoRightDerived A a V p) ≪≫
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι)
      (complementOpenSections A a V) p).symm ≪≫
    Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (restrictComplementOpenSectionsIso A a V) p ≪≫
    (rightDerivedCompIso (A := ModuleSheaves (Spec (CommRingCat.of A)).toRingedSpace)
      (sectionsOnOpen (Spec (CommRingCat.of A)).toRingedSpace
        ((complementZeroLocus A a).ι ''ᵁ V)) (globalToBase (CommRingCat.of A)) _
      (Iso.refl _) p).symm

/-- **`H^p(V, M̃|_U) ≅ H^p(X ∖ V(J), M̃)`, naturally in `M`.** Let `A` be a ring, let `a` and `J`
be ideals of `A`, let `X = Spec A` and `U = X ∖ V(a)`, and let `V` be an open of `U` whose image
in `X` is `X ∖ V(J)`. Then for every `p` the cohomology `H^p(V, M̃|_U)`, as an `A`-module, is
the cohomology `H^p(X ∖ V(J), M̃)` of `Stacks.LocalCohomologySequence.complementCohomologyBase`,
naturally in the `A`-module `M`. -/
def complementOpenCohomologyTildeIso (V : (complementZeroLocus A a : Scheme).Opens) (J : Ideal A)
    (hV : (complementZeroLocus A a).ι ''ᵁ V = complementZeroLocus A J) (p : ℕ) :
    restrictTildeFunctor A a ⋙ complementOpenCohomology A a V p ≅
      Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor
        (A := CommRingCat.of A) J p :=
  Functor.isoWhiskerLeft (tilde.functor (CommRingCat.of A))
    (restrictComplementOpenCohomologyIso A a V p ≪≫
      eqToIso (congrArg (fun W : (Spec (CommRingCat.of A)).Opens =>
        (sectionsOnOpen (Spec (CommRingCat.of A)).toRingedSpace W).rightDerived p ⋙
          globalToBase (CommRingCat.of A)) hV))

/-- **`H^p(U, M̃|_U) ≅ H^p(X ∖ V(a), M̃)`, naturally in `M`**: the case `V = U` of
`complementOpenCohomologyTildeIso`. -/
def complementOpenCohomologyTopTildeIso (p : ℕ) :
    restrictTildeFunctor A a ⋙ complementOpenCohomology A a ⊤ p ≅
      Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor
        (A := CommRingCat.of A) a p :=
  complementOpenCohomologyTildeIso A a ⊤ a (Scheme.Opens.ι_image_top _) p

/-- **The opens of `U` attached to smaller zero loci.** If `V(a) ⊆ V(J)`, then the preimage in
`U = Spec A ∖ V(a)` of `Spec A ∖ V(J)` has image `Spec A ∖ V(J)`, so it satisfies the hypothesis of
`complementOpenCohomologyTildeIso`. -/
theorem complementZeroLocus_ι_image_preimage {J : Ideal A}
    (h : PrimeSpectrum.zeroLocus (a : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) :
    (complementZeroLocus A a).ι ''ᵁ ((complementZeroLocus A a).ι ⁻¹ᵁ complementZeroLocus A J) =
      complementZeroLocus A J := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
  exact Set.compl_subset_compl.mpr h

end Stacks.LocalCohomology

end
