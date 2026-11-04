module

public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.IdealSubobject
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Sections
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Twist

/-!
# The cohomological hypothesis of Tag 0B5P, consumed

[Stacks, Tag 0B5P] hypothesises that for every quasi-coherent ideal sheaf `I ⊆ 𝒪_X` there is an
`n ≥ 1` with `H¹(X, I ⊗ L^{⊗ n}) = 0`, and uses that hypothesis exactly once: at the ideal sheaf
`I'` of `Z' = (X ∖ U) ∪ {x}`, to lift a global section of `I/I' ⊗ L^{⊗ n}` to one of
`I ⊗ L^{⊗ n}`.

This file performs that single consumption, for an arbitrary nested pair of closed sets. Given
the hypothesis, and closed sets `Z ⊆ Z'`, it produces an `n ≥ 1` for which

  `Γ(X, I_Z ⊗ L^{⊗ n}) ⟶ Γ(X, (I_Z / I_{Z'}) ⊗ L^{⊗ n})`

is an epimorphism, where `I_Z ⊇ I_{Z'}` are the ideal sheaves of the reduced closed subschemes
on `Z` and `Z'`. Every step is discharged: the ideal sheaves are quasi-coherent subobjects of
`𝒪_X` by `Stacks.AmpleCohomologicalCriterion.isQuasicoherent_closedIdealSubobject`, so the
hypothesis applies to them; they are nested the right way round by
`Stacks.AmpleCohomologicalCriterion.closedIdealSubobject_antitone`; tensoring their short exact
sequence by `L^{⊗ n}` stays short exact by
`Stacks.AmpleCohomologicalCriterion.shortExact_map_subobjectShortComplex`; and the vanishing `H¹`
turns into surjectivity on global sections by
`Stacks.AmpleCohomologicalCriterion.epi_evaluation_map_g`.

## Main definitions

* `Stacks.AmpleCohomologicalCriterion.HasEventuallyVanishingH1 X L`: the hypothesis of Tag 0B5P,
  verbatim — for every quasi-coherent subobject `I` of `𝒪_X` some positive tensor power of `L`
  kills `H¹(X, I ⊗ L^{⊗ n})`.

## Main results

* `Stacks.AmpleCohomologicalCriterion.exists_epi_sections`: **the hypothesis of Tag 0B5P,
  consumed.** For nested closed sets `Z ⊆ Z'` there is an `n ≥ 1` making global sections of `I_Z ⊗
  L^{⊗ n}` surject onto global sections of the quotient `(I_Z/I_{Z'}) ⊗ L^{⊗ n}`.
* `Stacks.AmpleCohomologicalCriterion.exists_surjective_sections`: the same on elements.
* `Stacks.AmpleCohomologicalCriterion.exists_epi_sections_at_closed_point`: the same at the pair of
  closed sets the proof of the tag actually forms, `Z = X ∖ V` and `Z' = Z ∪ {x}` for a closed
  point `x` of an open `V`.

## What is not done, and exactly what is missing

Tag 0B5P itself is **not** proved here, and no `stacks` attribute is attached anywhere in this
directory. With `Stacks.AmpleCohomologicalCriterion.exists_epi_sections` and
`Stacks.AmpleCohomologicalCriterion.isAmple_of_closed_points` in hand, the proof of Tag 0B5P is
reduced to one step, at a closed point `x` lying in an affine open `V` on which `L` is trivialized,
with `Z = X ∖ V` and `Z' = Z ∪ {x}`:

**(1) A global section of `(I_Z/I_{Z'}) ⊗ L^{⊗ n}` with nonzero germ at `x`.** Stacks computes
`Γ(X, I_Z/I_{Z'} ⊗ L^{⊗ n}) = A/𝔪` for `V = Spec A` and `𝔪` the maximal ideal of `x`, using that
`I_Z/I_{Z'}` is supported at the single point `x`. No declaration in this repository computes the
global sections, or the stalks, of the cokernel
`cokernel (Subobject.ofLE (closedIdealSubobject Z') (closedIdealSubobject Z) _)`. The two
primitives that would be needed, neither of which exists:

  * a stalk description of `Stacks.AmpleCohomologicalCriterion.closedIdealSubobject Z` — that its
    stalk at a point off `Z` is all of `𝒪_{X,x}` and that the stalk of `closedIdealSubobject (Z ⊔
    {x})` at a closed point `x ∉ Z` is the maximal ideal `𝔪_x`. The only bridge between the
    module-level ideal sheaf and Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData` is
    `Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff_mem_ker_ideal`, which
    is a sections-level criterion over a single affine open and says nothing about stalks;
  * surjectivity of `Γ(X, F) ⟶ F_x` for an `𝒪_X`-module `F` whose stalks vanish off the closed
    point `x`. `Stacks.ClosedImmersion.closedSupport_essImage_of_terminal_stalks` is the
    corresponding statement for sheaves of *rings* and does not apply.

**(2) Affineness of `X_s`.** This needs a `Stacks.SheafDescent.Trivialization` of
`Stacks.Ample.tensorPowModule X L n` over `V`, obtained from one of `L` over `V`, in order to
apply `Stacks.AmpleTheory.isAffineOpen_nonvanishingOpen_of_le`. The affine open produced by
`Stacks.AmpleTheory.exists_affineOpen_trivialization` cannot be used directly, because the degree
`n` is only produced after `Z = X ∖ V` has been fixed, so `V` has to trivialize every positive
power of `L` at once. `AlgebraicGeometry.SheafOfModules.tensorPowIsoUnit` is the global statement
of the same fact and there is no declaration restricting it to an open: nothing states that
`Stacks.Ample.tensorPowModule` commutes with restriction to an open subscheme.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

universe u

namespace Stacks.AmpleCohomologicalCriterion

/-- **The hypothesis of [Stacks, Tag 0B5P]**: for every quasi-coherent sheaf of ideals
`I ⊆ 𝒪_X` there is an `n ≥ 1` with `H¹(X, I ⊗ L^{⊗ n}) = 0`. Quasi-coherent ideal sheaves are
subobjects of `𝒪_X` in `X.Modules` whose underlying module is quasi-coherent, cohomology is the
right derived functor of global sections, the tensor product is [Stacks, Tag 05NA]'s and the
tensor powers are [Stacks, Tag 01CU]'s. -/
def HasEventuallyVanishingH1 (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] : Prop :=
  ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf),
    (Subobject.underlying.obj I).IsQuasicoherent →
      ∃ n : ℕ, 1 ≤ n ∧
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 1).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
              ((isSheaf_structureRingPresheaf X))⟩).obj
            ((Subobject.underlying.obj I))).obj
            ((Stacks.Ample.tensorPowModule X L (n : ℤ))))))

/-- The short exact sequence `0 → I_{Z'} ⊗ L^{⊗ n} → I_Z ⊗ L^{⊗ n} → (I_Z/I_{Z'}) ⊗ L^{⊗ n} → 0`
attached to a pair of nested closed sets `Z ≤ Z'` and a degree `n`. -/
noncomputable abbrev twistedQuotientComplex (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {Z Z' : Closeds X} (hZ : Z ≤ Z') (n : ℤ) :
    ShortComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (isSheaf_structureRingPresheaf X)⟩)) :=
  (subobjectShortComplex (closedIdealSubobject Z') (closedIdealSubobject Z)
      (closedIdealSubobject_antitone hZ)).map
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        (isSheaf_structureRingPresheaf X)⟩).flip.obj (Stacks.Ample.tensorPowModule X L n))

/-- `Stacks.AmpleCohomologicalCriterion.twistedQuotientComplex` is short exact. -/
theorem shortExact_twistedQuotientComplex (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {Z Z' : Closeds X} (hZ : Z ≤ Z') (n : ℤ) :
    (twistedQuotientComplex X L hZ n).ShortExact :=
  shortExact_map_subobjectShortComplex _ _ _ _

/-- **The hypothesis of [Stacks, Tag 0B5P], consumed.** For closed sets `Z ⊆ Z'` of a scheme
carrying an invertible module `L` satisfying
`Stacks.AmpleCohomologicalCriterion.HasEventuallyVanishingH1`, some positive tensor power `L^{⊗ n}`
makes

  `Γ(X, I_Z ⊗ L^{⊗ n}) ⟶ Γ(X, (I_Z/I_{Z'}) ⊗ L^{⊗ n})`

an epimorphism. This is the lifting step of the proof of the tag, with the ideal sheaves supplied
and the vanishing `H¹` turned into surjectivity. -/
theorem exists_epi_sections (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (h : HasEventuallyVanishingH1 X L)
    {Z Z' : Closeds X} (hZ : Z ≤ Z') :
    ∃ n : ℕ, 1 ≤ n ∧
      Epi ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        (twistedQuotientComplex X L hZ (n : ℤ)).g) := by
  obtain ⟨n, hn, hvan⟩ := h (closedIdealSubobject Z')
    (isQuasicoherent_closedIdealSubobject Z')
  exact ⟨n, hn, epi_evaluation_map_g X ⊤ (shortExact_twistedQuotientComplex X L hZ (n : ℤ)) hvan⟩

/-- `Stacks.AmpleCohomologicalCriterion.exists_epi_sections` on elements: every global section of
`(I_Z/I_{Z'}) ⊗ L^{⊗ n}` is the image of a global section of `I_Z ⊗ L^{⊗ n}`. -/
theorem exists_surjective_sections (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (h : HasEventuallyVanishingH1 X L)
    {Z Z' : Closeds X} (hZ : Z ≤ Z') :
    ∃ n : ℕ, 1 ≤ n ∧
      Function.Surjective ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        (twistedQuotientComplex X L hZ (n : ℤ)).g).hom := by
  obtain ⟨n, hn, hepi⟩ := exists_epi_sections X L h hZ
  exact ⟨n, hn, (ModuleCat.epi_iff_surjective _).1 hepi⟩

/-- The pair of closed sets the proof of [Stacks, Tag 0B5P] forms at a closed point `x` inside an
open `V`: the complement `Z = X ∖ V` and `Z' = Z ∪ {x}`. -/
noncomputable abbrev complClosed {X : Scheme.{u}} (V : X.Opens) : Closeds X :=
  ⟨(V : Set X)ᶜ, V.2.isClosed_compl⟩

/-- `X ∖ V ⊆ (X ∖ V) ∪ {x}`. -/
theorem complClosed_le_sup {X : Scheme.{u}} (V : X.Opens) {x : X}
    (hx : IsClosed ({x} : Set X)) : complClosed V ≤ complClosed V ⊔ ⟨{x}, hx⟩ :=
  le_sup_left

/-- **The hypothesis of [Stacks, Tag 0B5P] consumed at the pair of closed sets its proof forms.**
At a closed point `x` of an open `V`, some positive tensor power of `L` makes the global sections
of `I_{X ∖ V} ⊗ L^{⊗ n}` surject onto the global sections of
`(I_{X ∖ V} / I_{(X ∖ V) ∪ {x}}) ⊗ L^{⊗ n}`. -/
theorem exists_epi_sections_at_closed_point (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (h : HasEventuallyVanishingH1 X L) (V : X.Opens)
    {x : X} (hx : IsClosed ({x} : Set X)) :
    ∃ n : ℕ, 1 ≤ n ∧
      Epi ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        (twistedQuotientComplex X L (complClosed_le_sup V hx) (n : ℤ)).g) :=
  exists_epi_sections X L h (complClosed_le_sup V hx)

end Stacks.AmpleCohomologicalCriterion

end
