module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocus
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness
import StacksCore.Tactic.StacksAttribute

/-!
# The injectivity half of Stacks 0EIH

Let `A` be a Noetherian ring, let `f ∈ A`, let `𝔞 ⊆ A` be an ideal, let
`U = Spec(A) ∖ V(𝔞)` and let `M` be a finite `A`-module. Stacks 0EIH asserts that
`Stacks.Algebraization.principalComparisonMap A f 𝔞 M`, the canonical map

`colim_V Γ(V, M̃) ⟶ lim Γ(U, (M/fⁿM)~)`

over the opens `V ⊆ U` containing `U ∩ V(f)`, is an isomorphism. This file proves its
**injectivity half**, and proves it with none of the three hypotheses of the source: `A` need not
be `f`-adically complete, `f` need not be a nonzerodivisor on `M`, `H¹_𝔞(M/fM)` need not be
finite, and `f` need not lie in `𝔞`.

## The argument

Let `s` be a section of `F` on a neighbourhood `V` of the formal locus whose class in the
colimit is killed by the comparison. By Krull's intersection theorem the germ of `s` vanishes at
every point of the formal locus; this is
`Stacks.Algebraization.germ_eq_zero_of_comparisonAt_apply_eq_zero`.

The locus where the germ of a section vanishes is **open**, for any sheaf: a vanishing germ is
by definition a vanishing restriction to some neighbourhood, and the germ then vanishes at every
point of that neighbourhood. So that locus, intersected with `V`, is itself a neighbourhood of
the formal locus, and `s` restricts to zero on it because all of its germs there vanish. Hence
the class of `s` in the colimit is already zero, and the comparison is injective.

The point is that injectivity of a *colimit* over shrinking neighbourhoods does not need the
section to vanish on `V` itself — only on a smaller neighbourhood. In particular no hypothesis
that every associated point of `F` specializes into the formal locus is needed, as it is for
`Stacks.Algebraization.mono_comparisonMap_of_associatedPoints_specializes_vanishing`; such a
hypothesis can fail under the hypotheses of 0EIH: when `𝔞 = (f)` the formal locus `U ∩ V(f)` is
empty, so it fails for every nonzero `F`.

## Main definitions

* `AlgebraicGeometry.germVanishingOpens` — the open subset of an open `V` consisting of the
  points at which the germ of a given section of a sheaf of modules on `V` vanishes.
* `Stacks.Algebraization.germVanishingNeighbourhood` — that open subset, for a section killed by
  the comparison at `V`, viewed as a neighbourhood of the formal locus.

## Main results

* `AlgebraicGeometry.isOpen_germ_eq_zero` — that locus is open.
* `AlgebraicGeometry.res_germVanishingOpens_eq_zero` — the section restricts to zero on it.
* `Stacks.Algebraization.mono_comparisonMap` — the comparison map of Stacks 0EG2 is a
  monomorphism for every coherent module on `U`, with no further hypothesis.
* `Stacks.Algebraization.mono_principalComparisonMap` — **the injectivity half of Stacks
  0EIH**: `principalComparisonMap A f 𝔞 M` is a monomorphism for every finite module `M` over a
  Noetherian ring.

## Implementation notes

Injectivity is taken as `Mono`, matching
`Stacks.Algebraization.mono_comparisonMap_of_associatedPoints_specializes_vanishing`; the
concrete form is recorded alongside as
`Stacks.Algebraization.injective_principalComparisonMap`.

Germs are written `F.presheaf.germ`, while the lemmas of
`Mathlib.Topology.Sheaves.Stalks` are applied to `F.val.presheaf`; the two are definitionally
equal but not interchangeable by `rw`, so the steps crossing between them are in term mode.

## References

* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BLB](https://stacks.math.columbia.edu/tag/0BLB)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-! ### The open locus where the germ of a section vanishes -/

/-- **The locus where the germ of a section vanishes is open.** If the germ of `s` at `x`
vanishes then, the stalk being a colimit over the neighbourhoods of `x`, the restriction of `s`
to some open `W ∋ x` already vanishes, and then the germ of `s` vanishes at every point of `W`.

No quasi-coherence, finiteness or Noetherian hypothesis is used: this is a statement about an
arbitrary sheaf of modules. -/
theorem isOpen_germ_eq_zero {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (s : Γ(F, V)) :
    IsOpen {x : X | x ∈ V ∧ ∀ hx : x ∈ V, F.presheaf.germ V x hx s = 0} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨hxV, hgerm⟩
  have h0 : TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf V x hxV s =
      TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf V x hxV 0 :=
    (hgerm hxV).trans (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, he⟩ :=
    TopCat.Presheaf.germ_eq (C := Ab.{u}) F.val.presheaf x hxV hxV s 0 h0
  refine ⟨(W : Set X), fun y hy => ⟨iU.le hy, fun hyV => ?_⟩, W.2, hxW⟩
  have hres : ConcreteCategory.hom (F.val.presheaf.map iU.op) s = 0 := by
    rw [Subsingleton.elim iV iU] at he
    exact he.trans (map_zero _)
  exact (TopCat.Presheaf.germ_res_apply F.val.presheaf iU y hy s).symm.trans
    ((congrArg (ConcreteCategory.hom
      (TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf W y hy)) hres).trans (map_zero _))

/-- The open subset of `V` consisting of the points at which the germ of `s` vanishes. -/
def germVanishingOpens {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (s : Γ(F, V)) : X.Opens :=
  ⟨{x : X | x ∈ V ∧ ∀ hx : x ∈ V, F.presheaf.germ V x hx s = 0}, isOpen_germ_eq_zero F V s⟩

/-- A point lies in `germVanishingOpens F V s` if and only if it lies in `V` and the germ of `s` at
it vanishes. -/
theorem mem_germVanishingOpens {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (s : Γ(F, V))
    (x : X) :
    x ∈ germVanishingOpens F V s ↔
      x ∈ V ∧ ∀ hx : x ∈ V, F.presheaf.germ V x hx s = 0 :=
  Iff.rfl

/-- The locus `germVanishingOpens F V s` is contained in `V`. -/
theorem germVanishingOpens_le {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (s : Γ(F, V)) :
    germVanishingOpens F V s ≤ V :=
  fun _ hx => hx.1

/-- **A section with vanishing germs is zero.** A section of a sheaf of modules all of whose
germs vanish is zero, by the sheaf condition. -/
theorem eq_zero_of_forall_germ_eq_zero {X : Scheme.{u}} (F : X.Modules) (V : X.Opens)
    (s : Γ(F, V)) (h : ∀ (x : X) (hx : x ∈ V), F.presheaf.germ V x hx s = 0) :
    s = 0 :=
  TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) V s 0
    fun z hz => (h z hz).trans (map_zero _).symm

/-- A section restricts to zero on the open locus where its germ vanishes. -/
theorem res_germVanishingOpens_eq_zero {X : Scheme.{u}} (F : X.Modules) (V : X.Opens)
    (s : Γ(F, V)) :
    F.presheaf.map (homOfLE (germVanishingOpens_le F V s)).op s = 0 := by
  refine eq_zero_of_forall_germ_eq_zero F _ _ fun x hx => ?_
  refine (TopCat.Presheaf.germ_res_apply F.val.presheaf
    (homOfLE (germVanishingOpens_le F V s)) x hx s).trans ?_
  exact hx.2 _

end AlgebraicGeometry

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- The neighbourhood of the formal locus cut out of `V` by the vanishing of the germ of a
section killed by the comparison at `V`. It is a neighbourhood because the germ of such a
section vanishes at every point of the formal locus, by Krull's intersection theorem in the form
`Stacks.Algebraization.germ_eq_zero_of_comparisonAt_apply_eq_zero`. -/
def germVanishingNeighbourhood [IsNoetherianRing A] [F.IsCoherent]
    (V : OpensNearVanishing A I a) (s : ToType ((sectionsNearVanishing A I a F).obj V))
    (hsz : ConcreteCategory.hom (comparisonAt A I a F V) s = 0) :
    OpensNearVanishing A I a where
  openSet := germVanishingOpens F V.openSet s
  contains_vanishing x hx :=
    have hsupp : x ∈ (idealSheafNearVanishing A I a).support :=
      mem_support_baseIdealSheaf I (complementZeroLocus A a).ι hx
    ⟨support_idealSheafNearVanishing_le A I a V hsupp,
      fun _ => germ_eq_zero_of_comparisonAt_apply_eq_zero A I a F V s hsz hsupp⟩

/-- The open set underlying `germVanishingNeighbourhood A I a F V s hsz` is
`germVanishingOpens F V.openSet s`. -/
@[simp]
theorem germVanishingNeighbourhood_openSet [IsNoetherianRing A] [F.IsCoherent]
    (V : OpensNearVanishing A I a) (s : ToType ((sectionsNearVanishing A I a F).obj V))
    (hsz : ConcreteCategory.hom (comparisonAt A I a F V) s = 0) :
    (germVanishingNeighbourhood A I a F V s hsz).openSet = germVanishingOpens F V.openSet s :=
  rfl

/-- **The comparison map of Stacks 0EG2 is always a monomorphism.** For every coherent module
`F` on `U = Spec(A) ∖ V(𝔞)` over a Noetherian ring `A` and every ideal `I`, the comparison map
from the sections of `F` near the formal locus `U ∩ V(I)` to the compatible families of sections
of `F / Iⁿ F` on `U` is injective — with no hypothesis on the associated points of `F`.

A class in the colimit is a section `s` on a single neighbourhood `V`, the index category being
filtered. If the comparison kills it then the germs of `s` vanish along the formal locus, by
`Stacks.Algebraization.germ_eq_zero_of_comparisonAt_apply_eq_zero`, so the open locus where the
germ of `s` vanishes is again a neighbourhood of the formal locus; and `s` restricts to zero
there, by `AlgebraicGeometry.res_germVanishingOpens_eq_zero`, so its class in the colimit is
zero. -/
theorem mono_comparisonMap [IsNoetherianRing A] [F.IsCoherent] :
    Mono (comparisonMap A I a F) := by
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget Ab.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  refine ConcreteCategory.mono_of_injective _ ?_
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨V, s, rfl⟩ := Concrete.colimit_exists_rep (sectionsNearVanishing A I a F) z
  rw [← ConcreteCategory.comp_apply, colimit_ι_comp_comparisonMap] at hz
  have hle : (germVanishingNeighbourhood A I a F V s hz).openSet ≤ V.openSet :=
    germVanishingOpens_le F V.openSet s
  have hres : ConcreteCategory.hom ((sectionsNearVanishing A I a F).map
      (⟨hle⟩ : V ⟶ germVanishingNeighbourhood A I a F V s hz)) s = 0 :=
    res_germVanishingOpens_eq_zero F V.openSet s
  rw [← colimit.w (sectionsNearVanishing A I a F)
    (⟨hle⟩ : V ⟶ germVanishingNeighbourhood A I a F V s hz),
    ConcreteCategory.comp_apply, hres, map_zero]

/-! ### The injectivity half of Stacks 0EIH -/

/-- **Stacks 0EIH, the injectivity half.** Let `A` be a Noetherian ring, let `f ∈ A`, let
`𝔞 ⊆ A` be an ideal and let `M` be a finite `A`-module. Then the map

`colim_V Γ(V, M̃) ⟶ lim Γ(U, (M/fⁿM)~)`

of the source, the colimit being over the opens `V ⊆ U = Spec(A) ∖ V(𝔞)` containing
`U ∩ V(f)`, is a monomorphism.

None of the three hypotheses of the source is needed for this half: `A` is not assumed
`f`-adically complete, `f` is not assumed a nonzerodivisor on `M`, `H¹_𝔞(M/fM)` is not assumed
finite, and `f` is not assumed to lie in `𝔞`. -/
@[stacks 0EIH "injectivity"]
theorem mono_principalComparisonMap (A : Type u) [CommRing A] [IsNoetherianRing A] (f : A)
    (a : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M] :
    Mono (principalComparisonMap A f a M) :=
  have _ : (complementTilde A a M).IsCoherent := isCoherent_complementTilde A a M
  mono_comparisonMap A (Ideal.span {f}) a (complementTilde A a M)

/-- The injectivity half of Stacks 0EIH in concrete form: the underlying map of abelian groups
is injective. -/
theorem injective_principalComparisonMap (A : Type u) [CommRing A] [IsNoetherianRing A] (f : A)
    (a : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M] :
    Function.Injective (ConcreteCategory.hom (principalComparisonMap A f a M)) :=
  (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
    (mono_principalComparisonMap A f a M)

end Stacks.Algebraization

end
