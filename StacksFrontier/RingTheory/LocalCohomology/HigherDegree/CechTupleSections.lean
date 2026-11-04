module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CechSheafCohomology
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Localizations

/-!
# Sections of the associated sheaf on the Čech intersections, in every degree

Let `A` be a commutative ring, let `f : Fin r → A` be a finite family, and let `M` be an
`A`-module whose universe is independent of the ring's. The Čech complex of the covering of
`U = Spec A \ V(f₁, …, f_r)` by the standard opens `D(f_i)` has, in degree `p`, one factor for
every tuple `(i₀, …, i_p)`, namely the sections of `M̃` on

`D(f_{i₀}) ∩ ⋯ ∩ D(f_{i_p}) = D(f_{i₀} ⋯ f_{i_p})`.

This file identifies each of those factors with the Čech localization of
`StacksFrontier/RingTheory/Cech/Substrate.lean`,

`Γ(D(f_{i₀}) ∩ ⋯ ∩ D(f_{i_p}), M̃) ≅ M_{∏ i ∈ {i₀, …, i_p}, f i}`,

**in every degree and naturally in the tuple**: the restriction maps along a reindexing of the
tuple become the transition maps `Cech.cechι` of the localizations, and consequently the Čech
differential of Stacks 01FJ becomes the alternating sum of those transition maps. That last
statement is the one with content for a client, because the Čech differential is what consumes
the identification.

Degree zero of this comparison — the sheaf axiom identifying `Γ(U, M̃)` with the compatible
families, and the single standard open — is
`StacksFrontier/RingTheory/LocalCohomology/SectionsIso/`; the general-degree statement below is
built on the same two ingredients, namely `Stacks.LocalCohomology.cechSectionsEquiv`
(`Γ(D(∏ i ∈ t, f i), M̃) ≅ M_{∏ i ∈ t, f i}`, which rests on the independent-universe
`Stacks.LocalCohomology.isLocalizedModule_moduleSectionsMk_basicOpen`) and
`Stacks.LocalCohomology.cechSectionsEquiv_restrict` (restriction is `Cech.cechι`). Only two
things have to be added: a *tuple* of indices has to be converted into the *finite set* of
indices at which the Čech localizations are indexed, and that conversion has to be shown
compatible with the Čech differential.

## Main definitions

* `Stacks.LocalCohomology.cechTupleIndices` — the finite set of indices occurring in a tuple.
* `Stacks.LocalCohomology.cechTupleSectionsEquiv` — **the comparison
  `Γ(U_{i₀…i_p}, M̃) ≅ M_{∏ i ∈ {i₀,…,i_p}, f i}`**, in every degree.
* `Stacks.LocalCohomology.cechStandardTupleSectionsEquiv` — the same at the standard covering
  `Stacks.LocalCohomology.cechStandardOpen` of `Spec A \ V(I)`, which is the covering whose Čech
  complex computes `RΓ(U, M̃)` by `Stacks.LocalCohomology.cechDerivedGlobalSectionsIso`.

## Main results

* `Stacks.LocalCohomology.inter_eq_cechBasicOpen` — the intersection attached to a tuple is the
  standard open attached to the set of indices occurring in it: the intersection sees neither the
  order nor the multiplicity of the tuple.
* `Stacks.LocalCohomology.isLocalizedModule_moduleSectionsMk_inter` — the sections on that
  intersection are the localization of `M` at `∏ i ∈ {i₀,…,i_p}, f i`, as an `IsLocalizedModule`
  statement about `m ↦ m / 1`.
* `Stacks.LocalCohomology.cechTupleSectionsEquiv_restrict` — **naturality in the tuple**:
  restriction along an inclusion of intersections is the transition map `Cech.cechι`.
* `Stacks.LocalCohomology.cechTupleSectionsEquiv_cechD` — **the Čech differential of Stacks 01FJ
  becomes the alternating sum of the transition maps.**

## Implementation notes

The covering is not a definition here but a hypothesis: the family of opens is an arbitrary
`U : ι → Opens (PrimeSpectrum.Top A)` together with a map `c : ι → Fin r` and the equation
`U i = D(f (c i))`. That is what lets the same statements serve the two indexings occurring in
this development — `Fin r` for the algebraic Čech complex of
`StacksFrontier/RingTheory/Cech/Substrate.lean` and `ULift.{u} (Fin r)` for the geometric one, whose
index type must live in the universe of the ring — without a second copy of anything, and it
avoids coining a third name for the family of standard opens beside
`Stacks.LocalCohomology.cechBasicOpen` and `Stacks.LocalCohomology.cechStandardOpen`. At the
standard covering the hypothesis is discharged by
`Stacks.LocalCohomology.cechStandardOpen_eq_basicOpen`.

The module universe is independent of the ring universe throughout, including at the standard
covering: nothing below needs quasi-coherence of the associated sheaf, only the sections of
`StacksFrontier/RingTheory/LocalCohomology/BasicOpenSections.lean`, which are proved at independent
universes. A client working inside
`StacksFrontier/RingTheory/LocalCohomology/HigherDegree/CechSheafCohomology.lean` will instantiate
at `v := u`, because Stacks 01ET and the quasi-coherence of the associated sheaf are available
only there; that restriction belongs to the client and is not imposed here.

The index set attached to a tuple is the `Finset.image` of the tuple, so no injectivity is
assumed: the statements hold for every tuple, including the degenerate ones with a repeated
index, which is what the *ordered* Čech complex of Stacks 01EJ requires. For a strictly
increasing tuple that set has the expected cardinality, but nothing below needs it.

`Stacks.LocalCohomology.cechTupleSectionsEquiv_cechD` is proved in term mode rather than by `rw`.
The Čech cochains of Stacks 01FJ are sections of an abelian presheaf, here
`Stacks.LocalCohomology.associatedAbPresheaf`, whose value on an open is the module
`Stacks.LocalCohomology.moduleSections` bundled as an object of `AddCommGrpCat`. The two
spellings are definitionally equal, but `rw` builds its motive at `implicit` transparency, where
`rw [map_sum]` fails with *"did not find an occurrence of the pattern"* on a goal that visibly
contains the sum. `congrArg`, `Eq.trans` and `map_sum` applied as terms cross the boundary.

No Stacks tag attribute is placed here. The sections comparison on a single standard open is Tag
01HR and the Čech complex is Tag 01EJ; both carry their attributes elsewhere, and what is below
is their combination at the standard covering of `Spec A \ V(I)`, not the covering set of a tag
of its own.

## References

* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open PrimeSpectrum (basicOpen)

universe v u w

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)

section Tuples

variable {ι : Type w} (c : ι → Fin r)

/-! ### The set of indices occurring in a tuple -/

/-- The finite set of indices of `f` occurring in a tuple. The Čech complex of a covering is
indexed by tuples, while the Čech localizations of
`StacksFrontier/RingTheory/Cech/Substrate.lean` are indexed by finite sets of indices; this is the
passage from the first indexing to the second. -/
def cechTupleIndices {p : ℕ} (σ : Fin p → ι) : Finset (Fin r) :=
  Finset.image (fun k => c (σ k)) Finset.univ

/-- An index occurs in `Stacks.LocalCohomology.cechTupleIndices` exactly when the tuple takes it
somewhere. -/
theorem mem_cechTupleIndices {p : ℕ} (σ : Fin p → ι) (i : Fin r) :
    i ∈ cechTupleIndices c σ ↔ ∃ k, c (σ k) = i := by
  simp [cechTupleIndices]

/-- Reindexing a tuple can only shrink the set of indices occurring in it. This is the inclusion
the Čech differential needs: its `j`-th face omits an entry, so a face of a tuple has a smaller
index set than the tuple itself. -/
theorem cechTupleIndices_comp_subset {p q : ℕ} (σ : Fin q → ι) (g : Fin p → Fin q) :
    cechTupleIndices c (σ ∘ g) ⊆ cechTupleIndices c σ := by
  intro i hi
  obtain ⟨k, rfl⟩ := (mem_cechTupleIndices c (σ ∘ g) i).1 hi
  exact (mem_cechTupleIndices c σ _).2 ⟨g k, rfl⟩

variable (M : ModuleCat.{max u v} A)

/-- The restriction maps of the abelian presheaf underlying `M̃`, in the spelling the Čech
cochains of Stacks 01FJ use, are the restriction maps of locally fractional sections. -/
theorem restr_associatedAbPresheaf {V W : Opens (PrimeSpectrum.Top A)} (h : W ≤ V)
    (x : moduleSections M V) :
    CechCochains.restr (associatedAbPresheaf M) h x = moduleSectionsRestrict M h x :=
  rfl

section Family

variable {U : ι → Opens (PrimeSpectrum.Top A)} (hU : ∀ i, U i = basicOpen (f (c i)))

include hU

/-! ### The intersection attached to a tuple -/

/-- **The intersection attached to a tuple is the standard open attached to its set of indices.**
A prime lies in `D(f_{i₀}) ∩ ⋯ ∩ D(f_{i_p})` exactly when it misses every `f i` with
`i ∈ {i₀, …, i_p}`, which by `Stacks.LocalCohomology.mem_cechBasicOpen_iff` is membership of
`D(∏ i ∈ {i₀,…,i_p}, f i)`. In particular the intersection sees neither the order nor the
multiplicity of the tuple. -/
theorem inter_eq_cechBasicOpen {p : ℕ} (σ : Fin p → ι) :
    CechCochains.inter U σ = cechBasicOpen f (cechTupleIndices c σ) := by
  have hinter : CechCochains.inter U σ = ⨅ k, basicOpen (f (c (σ k))) :=
    iInf_congr fun k => hU (σ k)
  refine hinter.trans (SetLike.ext fun x => ?_)
  rw [mem_cechBasicOpen_iff]
  rw [show (x ∈ (⨅ k, basicOpen (f (c (σ k)))) ↔ ∀ k, x ∈ basicOpen (f (c (σ k)))) from by
    rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    exact Iff.rfl]
  refine ⟨fun h i hi => ?_, fun h k => h _ ((mem_cechTupleIndices c σ _).2 ⟨k, rfl⟩)⟩
  obtain ⟨k, rfl⟩ := (mem_cechTupleIndices c σ i).1 hi
  exact h k

/-- Enlarging the set of indices occurring in a tuple shrinks the intersection attached to it. -/
theorem inter_le_of_cechTupleIndices_subset {p q : ℕ} {σ : Fin p → ι} {τ : Fin q → ι}
    (h : cechTupleIndices c σ ⊆ cechTupleIndices c τ) :
    CechCochains.inter U τ ≤ CechCochains.inter U σ := by
  rw [inter_eq_cechBasicOpen f c hU, inter_eq_cechBasicOpen f c hU]
  exact cechBasicOpen_le_of_subset f h

/-! ### The sections on the intersection attached to a tuple -/

/-- **The sections of `M̃` on the intersection attached to a tuple are a localization of `M`.**
The map `m ↦ m / 1` exhibits `Γ(D(f_{i₀}) ∩ ⋯ ∩ D(f_{i_p}), M̃)` as the localization of `M` at
the powers of `∏ i ∈ {i₀,…,i_p}, f i`, with the module universe independent of the ring's. This
is `Stacks.LocalCohomology.isLocalizedModule_moduleSectionsMk_basicOpen` transported along
`Stacks.LocalCohomology.inter_eq_cechBasicOpen`, whose transport maps are themselves restriction
maps and so carry `m ↦ m / 1` to `m ↦ m / 1`. -/
theorem isLocalizedModule_moduleSectionsMk_inter {p : ℕ} (σ : Fin p → ι) :
    IsLocalizedModule (Cech.cechSub f (cechTupleIndices c σ))
      (moduleSectionsMk M (CechCochains.inter U σ)) := by
  have h : IsLocalizedModule (Cech.cechSub f (cechTupleIndices c σ))
      (((moduleSectionsCongr M (inter_eq_cechBasicOpen f c hU σ)).symm :
            moduleSections M (cechBasicOpen f (cechTupleIndices c σ)) →ₗ[A]
              moduleSections M (CechCochains.inter U σ)) ∘ₗ
        moduleSectionsMk M (cechBasicOpen f (cechTupleIndices c σ))) :=
    inferInstance
  exact h

/-- **`Γ(D(f_{i₀}) ∩ ⋯ ∩ D(f_{i_p}), M̃) ≅ M_{∏ i ∈ {i₀,…,i_p}, f i}`, in every degree.** The
factor of the Čech complex of the covering `i ↦ D(f (c i))` attached to a tuple `(i₀, …, i_p)` is
the Čech localization of `StacksFrontier/RingTheory/Cech/Substrate.lean` attached to the set of
indices occurring in that tuple. It is `Stacks.LocalCohomology.cechSectionsEquiv` transported
along `Stacks.LocalCohomology.inter_eq_cechBasicOpen`. -/
def cechTupleSectionsEquiv {p : ℕ} (σ : Fin p → ι) :
    moduleSections M (CechCochains.inter U σ) ≃ₗ[A]
      Cech.cechMod f (M : Type _) (cechTupleIndices c σ) :=
  (moduleSectionsCongr M (inter_eq_cechBasicOpen f c hU σ)).trans
    (cechSectionsEquiv f M (cechTupleIndices c σ))

/-- The comparison carries the constant fraction `m / 1` to `m / 1`. -/
@[simp]
theorem cechTupleSectionsEquiv_moduleSectionsMk {p : ℕ} (σ : Fin p → ι) (m : M) :
    cechTupleSectionsEquiv f c M hU σ (moduleSectionsMk M (CechCochains.inter U σ) m) =
      LocalizedModule.mkLinearMap (Cech.cechSub f (cechTupleIndices c σ)) (M : Type _) m :=
  cechSectionsEquiv_moduleSectionsMk f M (cechTupleIndices c σ) m

/-- **Naturality in the tuple.** Restricting sections of `M̃` from the intersection attached to a
tuple to the intersection attached to a tuple with a larger index set becomes, under
`Stacks.LocalCohomology.cechTupleSectionsEquiv`, the transition map `Cech.cechι` of the
localizations. This is `Stacks.LocalCohomology.cechSectionsEquiv_restrict`: the two transports
are restriction maps themselves, so both composites are the one restriction map to the smaller
open. -/
theorem cechTupleSectionsEquiv_restrict {p q : ℕ} {σ : Fin p → ι} {τ : Fin q → ι}
    (h : cechTupleIndices c σ ⊆ cechTupleIndices c τ)
    (x : moduleSections M (CechCochains.inter U σ)) :
    cechTupleSectionsEquiv f c M hU τ
        (moduleSectionsRestrict M (inter_le_of_cechTupleIndices_subset f c hU h) x) =
      Cech.cechι f (M : Type _) h (cechTupleSectionsEquiv f c M hU σ x) := by
  have hres : moduleSectionsRestrict M (inter_eq_cechBasicOpen f c hU τ).ge
        (moduleSectionsRestrict M (inter_le_of_cechTupleIndices_subset f c hU h) x) =
      moduleSectionsRestrict M (cechBasicOpen_le_of_subset f h)
        (moduleSectionsRestrict M (inter_eq_cechBasicOpen f c hU σ).ge x) :=
    rfl
  exact (congrArg (cechSectionsEquiv f M (cechTupleIndices c τ)) hres).trans
    (cechSectionsEquiv_restrict_apply f M h _)

/-! ### The Čech differential -/

/-- **The Čech differential becomes the alternating sum of the transition maps of the
localizations.** Under `Stacks.LocalCohomology.cechTupleSectionsEquiv` the degree-`p` Čech
differential of Stacks 01FJ for the covering `i ↦ D(f (c i))`, evaluated at a tuple
`(i₀, …, i_{p+1})`, is `∑_j (-1)^j Cech.cechι` applied to the value of the cochain at the `j`-th
face. This is what a client consumes: together with
`Stacks.LocalCohomology.cechTupleSectionsEquiv` it says that the Čech complex of the covering is
the Čech complex of the localizations `M_{∏ i ∈ t, f i}`. -/
theorem cechTupleSectionsEquiv_cechD {p : ℕ}
    (s : CechCochains.Cochain U (associatedAbPresheaf M) p) (σ : Fin (p + 2) → ι) :
    cechTupleSectionsEquiv f c M hU σ (CechCochains.cechD U (associatedAbPresheaf M) p s σ) =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        Cech.cechι f (M : Type _) (cechTupleIndices_comp_subset c σ j.succAbove)
          (cechTupleSectionsEquiv f c M hU (σ ∘ j.succAbove) (s (σ ∘ j.succAbove))) := by
  have hd : CechCochains.cechD U (associatedAbPresheaf M) p s σ =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr (associatedAbPresheaf M) (CechCochains.inter_le_omit U σ j)
          (s (σ ∘ j.succAbove)) := rfl
  refine (congrArg (cechTupleSectionsEquiv f c M hU σ) hd).trans ?_
  refine (map_sum (cechTupleSectionsEquiv f c M hU σ) _ Finset.univ).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (map_zsmul (cechTupleSectionsEquiv f c M hU σ) _ _).trans ?_
  exact congrArg (fun z => ((-1 : ℤ) ^ (j : ℕ)) • z)
    (cechTupleSectionsEquiv_restrict f c M hU
      (cechTupleIndices_comp_subset c σ j.succAbove) (s (σ ∘ j.succAbove)))

end Family

end Tuples

/-! ### The standard covering of the complement of a zero locus -/

section Standard

variable (M : ModuleCat.{max u v} A)

/-- **The comparison at the standard covering of `U = Spec A \ V(I)`.** This is
`Stacks.LocalCohomology.cechTupleSectionsEquiv` for the covering
`Stacks.LocalCohomology.cechStandardOpen` by the basic opens of the family `f`, indexed as the
Čech machinery of Stacks 01EP requires; that is the covering whose Čech complex computes
`RΓ(U, M̃)` by `Stacks.LocalCohomology.cechDerivedGlobalSectionsIso`. Every statement above holds
for it, the hypothesis on the family being
`Stacks.LocalCohomology.cechStandardOpen_eq_basicOpen`. -/
def cechStandardTupleSectionsEquiv {p : ℕ} (σ : Fin p → ULift.{u} (Fin r)) :
    moduleSections M (⨅ k, cechStandardOpen f (σ k)) ≃ₗ[A]
      Cech.cechMod f (M : Type _) (cechTupleIndices ULift.down σ) :=
  cechTupleSectionsEquiv f ULift.down M (cechStandardOpen_eq_basicOpen f) σ

/-- The Čech differential at the standard covering of `U = Spec A \ V(I)`, which is
`Stacks.LocalCohomology.cechTupleSectionsEquiv_cechD` there. -/
theorem cechStandardTupleSectionsEquiv_cechD {p : ℕ}
    (s : CechCochains.Cochain (cechStandardOpen f) (associatedAbPresheaf M) p)
    (σ : Fin (p + 2) → ULift.{u} (Fin r)) :
    cechStandardTupleSectionsEquiv f M σ
        (CechCochains.cechD (cechStandardOpen f) (associatedAbPresheaf M) p s σ) =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        Cech.cechι f (M : Type _) (cechTupleIndices_comp_subset ULift.down σ j.succAbove)
          (cechStandardTupleSectionsEquiv f M (σ ∘ j.succAbove) (s (σ ∘ j.succAbove))) :=
  cechTupleSectionsEquiv_cechD f ULift.down M (cechStandardOpen_eq_basicOpen f) s σ

end Standard

end Stacks.LocalCohomology

end
