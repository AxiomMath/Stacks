module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ConormalDegree
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverRingCatSheaf

/-!
# First cohomology of a modification over the punctured base

In the vanishing situation of [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local
domain `A` with maximal ideal `𝔪`, residue field `κ`, spectrum `S = Spec(A)`, closed point `s`
and punctured spectrum `U = S ∖ {s}`, together with a modification `f : X ⟶ S` — let `X` be
normal and let `A` be Nagata. Then restriction `H¹(X, 𝒪_X) ⟶ H¹(f⁻¹(U), 𝒪_X)` is injective
([Stacks, Tag 0AXB]).

The file also defines the objects in which [Stacks, Tag 0AXC] — `Hom_{D(A)}(κ[-1], Rf_*𝒪_X)`
is zero — is phrased, together with the construction carried out in the source's proof of it.
That tag is proved as
`AlgebraicGeometry.VanishingSituation.hom_residueFieldShift_derivedGlobalSections_eq_zero`.

## Main definitions

* `AlgebraicGeometry.VanishingSituation.preimagePuncturedSpectrum` — the open `f⁻¹(U)` of `X`.
* `AlgebraicGeometry.VanishingSituation.firstCohomologyRestriction` — the restriction map
  `H¹(X, 𝒪_X) ⟶ H¹(f⁻¹(U), 𝒪_X)`.
* `AlgebraicGeometry.VanishingSituation.residueFieldShift` — the object `κ[-1]` of `D(A)`.
* `AlgebraicGeometry.secsOver` (of
  `StacksFrontier.AlgebraicGeometry.GlobalSectionsOverRingCatSheaf`) — global sections with scalars
  restricted along
  `A ⟶ Γ(X, 𝒪_X)`, whose right derived functors are `Hⁿ(X, 𝒪_X)` as `A`-modules.
* `AlgebraicGeometry.IsDerivedPushforwardStructureSheaf` — the property of an object of `D(A)`
  of being `Rf_*𝒪_X`: no cohomology in negative degrees, and `Hⁿ(X, 𝒪_X)` in degree `n ≥ 0`.
* `AlgebraicGeometry.VanishingSituation.TrivialConormalDivisorOfEqualRestriction` — the
  geometric construction carried out in the proof of [Stacks, Tag 0AXB].
* `AlgebraicGeometry.VanishingSituation.ExtensionClassOfDerivedHom` — the homological
  construction carried out in the proof of [Stacks, Tag 0AXC].

## Main results

* `AlgebraicGeometry.VanishingSituation.hOne_restrict_puncturedSpectrum_injective` —
  [Stacks, Tag 0AXB].

## What is granted, and what is not

Each grant is a `Prop` defined below.

**For [Stacks, Tag 0AXB]** the grant is
`VanishingSituation.TrivialConormalDivisorOfEqualRestriction`. From two distinct classes in
`H¹(X, 𝒪_X)` with the same restriction to `f⁻¹(U)` — in the source, from their nonzero
difference `ξ` — it produces a normal modification of `S` carrying a nonempty effective Cartier
divisor, contained set theoretically in the special fibre, whose conormal sheaf is trivial. That
is the whole of the source's construction: the extension `0 → 𝒪_X → ℰ → 𝒪_X → 0` attached to `ξ`
([Stacks, Tag 0B3A]); the projective bundle `π : P = 𝐏(ℰ) → X` and the section `σ` cut out by
`ℰ → 𝒪_X`, whose conormal sheaf is `𝒪_X` ([Stacks, Tag 0B3V]); the second section `σ'` over
`f⁻¹(U)` coming from the splitting of `ξ` there, and the scheme-theoretic image `X' ⊆ P` of
`σ'`, which meets `σ(X)` since if it did not then `X' → X` would be affine and proper, hence finite
([Stacks, Tags 01R7, 01WN]), hence an isomorphism by normality ([Stacks, Tag 0AB1]); the
normalization `X^ν → X'`, finite because `A` is Nagata ([Stacks, Tags 035S, 035B]); and the
pullback `Z ⊆ X^ν` of the effective Cartier divisor `σ(X)` ([Stacks, Tag 067R]), nonempty,
contained in the closed fibre, and with trivial conormal sheaf by functoriality of the conormal
sheaf under flat pullback ([Stacks, Tag 0473]).

What the theorem contributes is the contradiction, which is [Stacks, Tag 0AXA] in the form this
library proves it, `VanishingSituation.not_isTrivial_conormalSheaf`. That form carries two
hypotheses of its own, so the grant carries them too: the observation following Situation 0AX8
that every component of the special fibre has dimension one, part (2) of [Stacks, Tag 0B40] as
`AlgebraicGeometry.VanishingSectionDegreePos`, and the global section of the conormal sheaf
restricted to a component contained in `Z` which is nonzero and has a zero.

**For [Stacks, Tag 0AXC]** two inputs of the source's proof are `Prop`s. The affine identification
`D(A) = D_{QCoh}(𝒪_S)`, which reads `Rf_*𝒪_X` as `RΓ(X, 𝒪_X)` in `D(A)`, is
`IsDerivedPushforwardStructureSheaf`: it pins the object down by its cohomology, which is
`Hⁿ(X, 𝒪_X)` as an `A`-module. The construction of the source's proof is
`VanishingSituation.ExtensionClassOfDerivedHom`: from `α : κ[-1] ⟶ Rf_*𝒪_X` it produces a class
`ξ ∈ H¹(X, 𝒪_X)` whose restriction to `f⁻¹(U)` agrees with that of the zero class, and whose own
vanishing forces `α = 0`. That is the whole of the source's construction: the adjunction
`Rf_* ⊣ Lf^*`, turning `α` into a map `Lf^*κ[-1] → 𝒪_X`; the computation of the cohomology
sheaves of `Lf^*κ[-1]`, which vanish above degree `1` and are `𝒪_{X_s}` in degree `1`; the
vanishing of `Hom(H⁰(Lf^*κ[-1]), 𝒪_X)` because `𝒪_X` is torsion free, so that the Ext spectral
sequence ([Stacks, Tag 07AA]) identifies the group with `Ext¹_{𝒪_X}(𝒪_{X_s}, 𝒪_X)` and hence
`α` with an extension `0 → 𝒪_X → ℰ → 𝒪_{X_s} → 0`; the pullback of that extension along the
surjection `𝒪_X → 𝒪_{X_s}`, which is the class `ξ` and is split over `f⁻¹(U)`; and, once `ξ`
vanishes, the lift of the unit section of `𝒪_{X_s}` to a global section `s` of `ℰ`, the map
`c_s : ℐ → 𝒪_X` given by multiplication by the ideal sheaf `ℐ` of `X_s`, the identification of
`f_*c_s : 𝔪 → A` with multiplication by an element `a ∈ A` because `A` is a Noetherian normal
local domain, and the replacement of `s` by `s - a`, which is annihilated by `ℐ` and splits the
extension.

## Implementation notes

`Hⁿ(W, 𝒪_X)` and its restriction maps are `Hgroup` and `Hrestrict` of
`StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally`: the right derived
functors of sections over `W` on sheaves of modules over the structure sheaf of `X` viewed as a
sheaf of rings, and the maps that `CategoryTheory.NatTrans.rightDerived` induces from
restriction of sections. The structure sheaf itself enters as its canonical rank-one module
`CategoryTheory.SheafOfModules.unit`.

`κ[-1]` is the residue field in cohomological degree zero, shifted by `-1`; the Stacks
convention `K[n]ⁱ = K^{n+i}` puts it in degree `1`.

## References

* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AXA](https://stacks.math.columbia.edu/tag/0AXA)
* [Stacks Project, Tag 0B3A](https://stacks.math.columbia.edu/tag/0B3A)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 07AA](https://stacks.math.columbia.edu/tag/07AA)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard


variable {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))

/-- An object of `D(A)` **is** `Rf_*𝒪_X`, for a morphism `f : X ⟶ Spec A` with affine target,
when it has no cohomology in negative degrees and its cohomology in degree `n ≥ 0` is
`Hⁿ(X, 𝒪_X)` as an `A`-module.

This is the affine identification `D(A) = D_{QCoh}(𝒪_S)` of the source: it reads `Rf_*𝒪_X` as
the derived global sections `RΓ(X, 𝒪_X)`, an object of `D(A)`. -/
structure IsDerivedPushforwardStructureSheaf (K : DerivedCategory (ModuleCat.{u} A)) : Prop where
  /-- There is no cohomology in negative degrees. -/
  isZero_homology_neg : ∀ n : ℤ, n < 0 →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K)
  /-- The cohomology in degree `n ≥ 0` is `Hⁿ(X, 𝒪_X)` as an `A`-module. -/
  nonempty_homology_iso : ∀ n : ℕ,
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj K ≅
      ((secsOver f).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf))

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-- The structure sheaf of the source of the modification, as a sheaf of rings. -/
abbrev structureRingSheaf :=
  structureSheafRing V.X.toLocallyRingedSpace.toRingedSpace

/-- The preimage `f⁻¹(U)` in `X` of the punctured spectrum `U = S ∖ {s}`. -/
abbrev preimagePuncturedSpectrum : V.X.Opens :=
  V.f ⁻¹ᵁ V.puncturedSpectrumOpen

/-- The restriction map `H¹(X, 𝒪_X) ⟶ H¹(f⁻¹(U), 𝒪_X)` on the first cohomology of the structure
sheaf. -/
abbrev firstCohomologyRestriction :
    Hgroup V.structureRingSheaf (⊤ : V.X.Opens) 1
        (SheafOfModules.unit V.structureRingSheaf) ⟶
      Hgroup V.structureRingSheaf V.preimagePuncturedSpectrum 1
        (SheafOfModules.unit V.structureRingSheaf) :=
  Hrestrict V.structureRingSheaf
    (show V.preimagePuncturedSpectrum ≤ (⊤ : V.X.Opens) from le_top) 1
    (SheafOfModules.unit V.structureRingSheaf)

/-- The residue field `κ` of the local ring, as a module over it. -/
abbrev residueFieldModule : ModuleCat.{u} V.A :=
  ModuleCat.of V.A (IsLocalRing.ResidueField V.A)

/-- `κ[-1]`, the residue field in cohomological degree zero shifted by `-1`, as an object of
`D(A)`. The Stacks convention `K[n]ⁱ = K^{n+i}` places it in degree `1`. -/
abbrev residueFieldShift : DerivedCategory (ModuleCat.{u} V.A) :=
  ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule)⟦(-1 : ℤ)⟧

/-! ### The grants -/

/-- **The geometric construction in the proof of [Stacks, Tag 0AXB].** From two distinct classes
in `H¹(X, 𝒪_X)` whose restrictions to `f⁻¹(U)` agree — in the source, from their nonzero
difference — it produces a normal modification `W.f : W.X ⟶ Spec(A)` together with a nonempty
effective Cartier divisor `Z ⊆ W.X`, contained set theoretically in the special fibre, whose
conormal sheaf is trivial; and together with the data that the form of [Stacks, Tag 0AXA] proved
in this library consumes, namely the dimension-one observation following Situation 0AX8, part
(2) of [Stacks, Tag 0B40] as `AlgebraicGeometry.VanishingSectionDegreePos`, and a global section
of the conormal sheaf restricted to a component contained in `Z` which is nonzero and has a
zero.

In the source `W.X` is the normalization of the scheme-theoretic image, inside the projective
bundle `𝐏(ℰ)` of the extension `ℰ` attached to the difference class, of the second section that
a splitting over `f⁻¹(U)` provides, and `Z` is the pullback to it of the first section. -/
def TrivialConormalDivisorOfEqualRestriction : Prop :=
  ∀ ξ η : Hgroup V.structureRingSheaf (⊤ : V.X.Opens) 1
      (SheafOfModules.unit V.structureRingSheaf),
    ξ ≠ η → V.firstCohomologyRestriction ξ = V.firstCohomologyRestriction η →
    ∃ (W : VanishingSituation.{u}) (_ : IsNormal W.X)
      (_ : ∀ i : Fin W.numberOfComponents, topologicalKrullDim (W.component i) = 1)
      (I : W.X.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor I)
      (_ : I.supportSet.Nonempty)
      (_ : I.supportSet ⊆ Set.range (W.f.fiberι W.closedPoint))
      (_ : VanishingSectionDegreePos (W.base.residueField W.closedPoint))
      (i : Fin W.numberOfComponents) (_ : componentInSource W i ⊆ I.supportSet)
      (s : (conormalOnComponent W I i).sections), s.eval (op ⊤) ≠ 0 ∧
        (∃ y : componentScheme W i, y ∉ Stacks.SheafOfModules.nonvanishingLocus
          (X := (componentScheme W i).toRingedSpace) (conormalOnComponent W I i) s) ∧
        SheafOfModules.IsTrivial I.subscheme.presheaf I.subscheme.ringCatSheaf.2
          (Stacks.Conormal.conormalSheaf I.subschemeι)

/-- **The homological construction in the proof of [Stacks, Tag 0AXC].** From a morphism
`α : κ[-1] ⟶ K` in `D(A)`, where `K` is `Rf_*𝒪_X`, it produces a class `ξ ∈ H¹(X, 𝒪_X)` whose
restriction to `f⁻¹(U)` agrees with that of the zero class, and whose own vanishing forces
`α = 0`.

In the source `α` corresponds, through the adjunction `Rf_* ⊣ Lf^*` and the Ext spectral
sequence of [Stacks, Tag 07AA], to an extension `0 → 𝒪_X → ℰ → 𝒪_{X_s} → 0`; the class `ξ` is
the pullback of that extension along the surjection `𝒪_X → 𝒪_{X_s}`, which is split over
`f⁻¹(U)`, and the implication `ξ = 0 → α = 0` is the lift of the unit section to a global
section of `ℰ` followed by its correction by the element of `A` that `𝔪 → A` is multiplication
by. -/
def ExtensionClassOfDerivedHom (K : DerivedCategory (ModuleCat.{u} V.A)) : Prop :=
  ∀ α : V.residueFieldShift ⟶ K,
    ∃ ξ : Hgroup V.structureRingSheaf (⊤ : V.X.Opens) 1
      (SheafOfModules.unit V.structureRingSheaf),
      V.firstCohomologyRestriction ξ = V.firstCohomologyRestriction 0 ∧ (ξ = 0 → α = 0)

/-! ### The lemma -/

/-- **Stacks Project, Tag 0AXB.** In Situation 0AX8 with `X` normal and `A` Nagata, the
restriction map `H¹(X, 𝒪_X) ⟶ H¹(f⁻¹(U), 𝒪_X)` on the first cohomology of the structure sheaf is
injective.

Two distinct classes with the same restriction are fed to the construction of the source's
proof, the hypothesis `hgeom`, which returns a nonempty effective Cartier divisor with trivial
conormal sheaf inside the special fibre of a normal modification of the base; and
`VanishingSituation.not_isTrivial_conormalSheaf`, which is [Stacks, Tag 0AXA], forbids such a
divisor. -/
@[stacks 0AXB "injectivity, granted the geometric construction of the source's proof as the \
hypothesis hgeom -- the extension of Tag 0B3A attached to the difference of the two classes, \
its projective bundle with the section of Tag 0B3V, the second section over f^{-1}(U) and the \
scheme-theoretic image of that section, the normalization of the image (finite because A is \
Nagata, Tags 035S and 035B) and the pullback to it of the first section as a nonempty effective \
Cartier divisor in the special fibre with trivial conormal sheaf, together with the three \
inputs that this library's form of Tag 0AXA consumes: the dimension-one observation following \
Situation 0AX8, part (2) of Tag 0B40 as VanishingSectionDegreePos, and the global section of \
the restricted conormal sheaf. The contradiction with Tag 0AXA is what is proved here"]
theorem hOne_restrict_puncturedSpectrum_injective [IsNormal V.X] (hA : IsNagataRing V.A)
    (hgeom : V.TrivialConormalDivisorOfEqualRestriction) :
    Function.Injective V.firstCohomologyRestriction := by
  have : IsNagataRing V.A := hA
  intro ξ η h
  by_contra hne
  obtain ⟨W, hWnormal, hdim, I, hIcartier, hnonempty, hfibre, hpos, i, hCi, s, hs, hz, htriv⟩ :=
    hgeom ξ η hne h
  have := hWnormal
  have := hIcartier
  exact not_isTrivial_conormalSheaf W hdim I hnonempty hfibre hpos i hCi s hs hz htriv

end VanishingSituation

end AlgebraicGeometry

end
