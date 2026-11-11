module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSpectrumVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.AbsolutelyIntegrallyClosed

/-!
# Vanishing of higher étale cohomology on the spectrum of an absolutely integrally closed ring

Let `R` be an absolutely integrally closed ring and let `M` be a finite abelian group. The
higher étale cohomology of `Spec R` with coefficients in the constant sheaf `M` vanishes.

The engine is `Stacks.EtaleCohomology.StrictlyHenselian` (Stacks 0GY0): a ring all of whose
local rings are strictly henselian has no positive-degree étale cohomology, provided the
degree-one restriction map

`H¹(D(f + g), F) ⟶ H¹(D(f(f + g)), F) ⊕ H¹(D(g(f + g)), F)`

has zero kernel. Two things are supplied here. First, the local rings of an absolutely
integrally closed ring are strictly henselian: the stalks of the structure sheaf of `Spec R`
are localizations of `Γ(Spec R, ⊤) ≅ R` at primes, and Stacks 0DCS says such a localization is
henselian with separably closed residue field. Second, the degree-one condition follows from
the *degree-zero* statement that a section over `D(f(f + g)) ∩ D(g(f + g))` is a difference of
sections over the two opens: by the Mayer--Vietoris sequence (Stacks 0A50) the kernel of the
degree-one map is the image of the connecting map out of degree zero, and the connecting map
kills the image of the degree-zero difference map.

That degree-zero gluing statement is a hypothesis of the results of this file. It is proved for
a finite constant sheaf in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.Vanishing`, where
Stacks 0GY7 itself is
`Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.subsingleton_H_constantSheaf_smallEtale`.

## Main results

* `Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.strictlyHenselianLocalRing_stalk` — every
  stalk of the structure sheaf of the spectrum of an absolutely integrally closed ring is a
  strictly henselian local ring.
* `Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.eq_zero_of_mayerVietoris_degreeOne` — a
  degree-one class over a union of two opens, vanishing on each of them, is zero as soon as
  degree-zero sections over the intersection are differences of sections over the two opens.
* `Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.subsingleton_H_of_sections_sub` — the
  positive-degree vanishing for an arbitrary abelian sheaf satisfying the degree-zero gluing
  condition.
* `Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.subsingleton_H_constantSheaf` — the
  vanishing for a finite constant sheaf satisfying the degree-zero gluing condition.

## Implementation notes

Vanishing is expressed as `Subsingleton` of the cohomology group, matching
`Stacks.EtaleCohomology.StrictlyHenselian.subsingleton_H_of_degreeOne_kernel_eq_zero`: the
groups are `CategoryTheory.Sheaf.H`, bundled objects of `AddCommGrpCat`, for which `= 0` is
not a statement about a group but about an object of a category.

The site is `Stacks.EtaleCohomology.MayerVietoris.topology`, the small étale site of `Spec R`
placed in a single universe, as required by Mathlib's `CategoryTheory.Sheaf.H'` and as used by
the Mayer--Vietoris sequence and by Stacks 0GY0.

The hypothesis `hsub` of `subsingleton_H_constantSheaf` is the degree-zero gluing statement of
the source's proof: for `f, g ∈ R` every section of the constant sheaf over
`D(f(f + g)) ∩ D(g(f + g))` is the difference of a section over `D(f(f + g))` and a section
over `D(g(f + g))`. The source produces it from the short exact sequence of group schemes
`0 → ℤ/ℓℤ → G^{(π)} → G^{(π ^ ℓ)} → 0` (Stacks 0GY4), the lifting of points through its isogeny
(Stacks 0GY5) and the interpolation of two congruences (Stacks 0GY6); this is where finiteness
of `M` is used. That argument is
`Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.sectionsSub_constantSheaf`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.Vanishing`, which
also states Stacks 0GY7 on Mathlib's small étale site.

## References

* [Stacks Project, Tag 0GY7](https://stacks.math.columbia.edu/tag/0GY7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.EtaleCohomology.StrictlyHenselian (opensCohomology)

universe u

namespace Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed

/-! ### Strict henselianity of the stalks -/

/-- **The stalks of the structure sheaf of the spectrum of an absolutely integrally closed ring
are strictly henselian.** The stalk at a point is a localization of the ring of global sections
at the corresponding prime; the global sections of `Spec R` are isomorphic to `R`, hence
absolutely integrally closed, and Stacks 0DCS says a localization of an absolutely integrally
closed ring at a prime is henselian with separably closed residue field. -/
theorem strictlyHenselianLocalRing_stalk {R : Type u} [CommRing R]
    (hR : IsAbsolutelyIntegrallyClosed R) (x : Spec (CommRingCat.of R)) :
    StrictlyHenselianLocalRing ↥((Spec (CommRingCat.of R)).presheaf.stalk x) := by
  have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of R)).Opens) := isAffineOpen_top _
  let y : (⊤ : (Spec (CommRingCat.of R)).Opens) := ⟨x, trivial⟩
  let _ := (Spec (CommRingCat.of R)).presheaf.algebra_section_stalk y
  have _hloc := hU.isLocalization_stalk y
  have hΓ : IsAbsolutelyIntegrallyClosed Γ(Spec (CommRingCat.of R), ⊤) :=
    isAbsolutelyIntegrallyClosed_of_surjective
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2) hR
  have hstrict := IsAbsolutelyIntegrallyClosed.isStrictlyHenselian_atPrime
    (A := Γ(Spec (CommRingCat.of R), ⊤))
    (B := ↥((Spec (CommRingCat.of R)).presheaf.stalk x)) hΓ (hU.primeIdealOf y).asIdeal
  let _ := hstrict.1
  let _ := hstrict.2
  exact ⟨⟩

/-! ### From degree-zero gluing to the degree-one condition -/

variable {X : Scheme.{u}}

/-- **The degree-zero gluing condition for two open subschemes**: every section of `F` over
`U ⊓ V` is the difference of the restrictions of a section over `U` and a section over `V`.
This is surjectivity of the degree-zero difference map of the Mayer--Vietoris sequence. -/
def SectionsSub (F : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1})
    (U V : X.Opens) : Prop :=
  ∀ τ : (opensCohomology F 0).obj (op (U ⊓ V)),
    ∃ (a : (opensCohomology F 0).obj (op U)) (b : (opensCohomology F 0).obj (op V)),
      (opensCohomology F 0).map (homOfLE inf_le_left).op a -
        (opensCohomology F 0).map (homOfLE inf_le_right).op b = τ

/-- The degree-zero gluing condition is surjectivity of the degree-zero difference map of the
Mayer--Vietoris sequence: every element of the biproduct is the image of a pair of sections
under the inverse of `AddCommGrpCat.biprodIsoProd`, on which that map is the difference of the
two restrictions. -/
theorem surjective_fromBiprod_of_sectionsSub
    (F : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}) (U V : X.Opens)
    (h : SectionsSub F U V) :
    Function.Surjective (ConcreteCategory.hom (MayerVietoris.fromBiprod F U V 0)) := by
  intro τ
  obtain ⟨a, b, hab⟩ := h τ
  refine ⟨(AddCommGrpCat.biprodIsoProd _ _).inv ⟨a, b⟩, ?_⟩
  exact Eq.trans
    (GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoProd_inv_apply
      (MayerVietoris.square X U V) F a b) hab

/-- **A degree-one class over a union of two opens, vanishing on each of them, is zero**, as
soon as degree-zero sections over the intersection are differences of sections over the two
opens.

By exactness of the Mayer--Vietoris sequence (Stacks 0A50) at its degree-one term over the
union, such a class is the image of a degree-zero class over the intersection under the
connecting map. The gluing condition writes that degree-zero class as a difference of sections
over the two opens, and the connecting map annihilates every such difference, because it
follows the degree-zero difference map in the sequence. -/
theorem eq_zero_of_mayerVietoris_degreeOne
    (F : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}) {U V W : X.Opens}
    (hUW : U ≤ W) (hVW : V ≤ W) (hW : W = U ⊔ V) (hsub : SectionsSub F U V)
    (x : (opensCohomology F 1).obj (op W))
    (hU : (opensCohomology F 1).map (homOfLE hUW).op x = 0)
    (hV : (opensCohomology F 1).map (homOfLE hVW).op x = 0) : x = 0 := by
  subst hW
  have hU' : (F.cohomologyPresheaf 1).map (MayerVietoris.square X U V).f₂₄.op x = 0 := hU
  have hV' : (F.cohomologyPresheaf 1).map (MayerVietoris.square X U V).f₃₄.op x = 0 := hV
  have ht : MayerVietoris.toBiprod F U V 1 x = 0 := by
    refine Eq.trans
      (GrothendieckTopology.MayerVietorisSquare.toBiprod_apply
        (MayerVietoris.square X U V) F x) ?_
    rw [hU', hV']
    exact map_zero _
  have hE := (MayerVietoris.cohomologySequence_exact F U V 0 1 rfl).exact' 2 3 4
  rw [ShortComplex.ab_exact_iff] at hE
  obtain ⟨y, hy⟩ := hE x ht
  obtain ⟨z, hz⟩ := surjective_fromBiprod_of_sectionsSub F U V hsub y
  have hyδ : MayerVietoris.delta F U V 0 1 rfl y = x := hy
  have h0 : MayerVietoris.fromBiprod F U V 0 ≫ MayerVietoris.delta F U V 0 1 rfl = 0 :=
    GrothendieckTopology.MayerVietorisSquare.fromBiprod_δ (MayerVietoris.square X U V) F 0 1 rfl
  have hδz : MayerVietoris.delta F U V 0 1 rfl y = 0 := by
    rw [← hz, ← ConcreteCategory.comp_apply, h0]
    exact AddCommGrpCat.zero_apply _ _ z
  exact hyδ.symm.trans hδz

/-! ### The vanishing -/

section Spec

variable {R : Type u} [CommRing R]

/-- The covering `D(f + g) = D(f(f + g)) ∪ D(g(f + g))`: a prime avoiding `f + g` cannot
contain both `f` and `g`. -/
alias basicOpen_add_eq_sup := Stacks.EtaleCohomology.StrictlyHenselian.basicOpen_add_eq_sup

/-- **Positive-degree étale cohomology over the spectrum of an absolutely integrally closed
ring vanishes**, for every abelian sheaf satisfying the degree-zero gluing condition of
`Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.SectionsSub` on the pairs of opens
`D(f(f + g))`, `D(g(f + g))`.

The local rings are strictly henselian by `strictlyHenselianLocalRing_stalk`, and the
degree-one condition of Stacks 0GY0 is `eq_zero_of_mayerVietoris_degreeOne` applied to the
covering `D(f + g) = D(f(f + g)) ∪ D(g(f + g))`. -/
theorem subsingleton_H_of_sectionsSub (hR : IsAbsolutelyIntegrallyClosed R)
    (F : Sheaf (MayerVietoris.topology (Spec (CommRingCat.of R))) AddCommGrpCat.{u + 1})
    (hsub : ∀ f g : R, SectionsSub F (PrimeSpectrum.basicOpen (f * (f + g)))
      (PrimeSpectrum.basicOpen (g * (f + g))))
    (q : ℕ) (hq : 0 < q) : Subsingleton (Sheaf.H.{u + 1} F q) := by
  refine StrictlyHenselian.subsingleton_H_of_degreeOne_kernel_eq_zero
    (fun x => strictlyHenselianLocalRing_stalk hR x) F (fun f g y hf hg => ?_) q hq
  exact eq_zero_of_mayerVietoris_degreeOne F
    (PrimeSpectrum.basicOpen_mul_le_right f (f + g))
    (PrimeSpectrum.basicOpen_mul_le_right g (f + g))
    (basicOpen_add_eq_sup f g) (hsub f g) y hf hg

/-- **Vanishing for a constant sheaf satisfying the degree-zero gluing condition.** Let `R` be
an absolutely integrally closed ring and let `M` be a finite abelian group. If every section of
the constant sheaf `M` over `D(f(f + g)) ∩ D(g(f + g))` is a difference of sections over
`D(f(f + g))` and over `D(g(f + g))`, then the étale cohomology of `Spec R` with coefficients in
that sheaf vanishes in every positive degree.

The gluing condition is proved for every finite `M` by
`Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.sectionsSub_constantSheaf`, which gives
Stacks 0GY7 as
`Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.subsingleton_H_constantSheaf_smallEtale`. -/
theorem subsingleton_H_constantSheaf (hR : IsAbsolutelyIntegrallyClosed R)
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    (hsub : ∀ f g : R,
      SectionsSub ((constantSheaf (MayerVietoris.topology (Spec (CommRingCat.of R)))
          AddCommGrpCat.{u + 1}).obj M)
        (PrimeSpectrum.basicOpen (f * (f + g))) (PrimeSpectrum.basicOpen (g * (f + g))))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf (MayerVietoris.topology (Spec (CommRingCat.of R)))
        AddCommGrpCat.{u + 1}).obj M) q) :=
  subsingleton_H_of_sectionsSub hR _ hsub q hq

end Spec

end Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed

end
