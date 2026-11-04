module

public import StacksFrontier.AlgebraicGeometry.ProjInclusionDegreeSection.Basic

/-!
# Sections pulled back over an arbitrary open, and Tag 01MY's `theta` on them

`StacksFrontier/AlgebraicGeometry/ProjInclusionDegreeSection/Unit.lean` names the image of a
**global** section under the unit of the pullback--pushforward adjunction
(`Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection`) and says how the four structural
isomorphisms of the inverse image act on it; and
`Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection` computes Tag 01MY's comparison
map on the pulled-back global section attached to a homogeneous element. Both are restricted to
the open `⊤`, for the single reason that `f ⁻¹ᵁ ⊤` and `⊤` are definitionally equal and so no
transport appears.

This file removes that restriction. A section of `M` over an arbitrary open `T` of `Y` has a
canonical image in `f^*M` over `f ⁻¹ᵁ T`, and every statement of the companion file generalises
to it unchanged, as does Tag 01MY's identity.

## Main definitions

* `Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn`: the image of a section over an
  arbitrary open under the unit of the pullback--pushforward adjunction.

## Main results

* `Stacks.AlgebraicGeometry.PullbackUnit.pullback_map_pullbackSectionOn`: naturality.
* `Stacks.AlgebraicGeometry.PullbackUnit.pullbackId_hom_pullbackSectionOn`,
  `pullbackComp_inv_pullbackSectionOn` and `pullbackComp_hom_pullbackSectionOn`: the identity and
  the two directions of the pseudofunctoriality isomorphism for a composite.
* `Stacks.AlgebraicGeometry.PullbackUnit.pullbackCongr_refl_inv_app` and
  `pullbackCongr_refl_hom_app`: **a congruence isomorphism between the pullbacks along two
  morphisms that are the same is the identity on sections.** This is the form in which the
  leading factor of Tag 01NO's comparison can be discharged; see the implementation notes for
  why the apparently more natural statement is not available at a general open.
* `Stacks.AlgebraicGeometry.PullbackUnit.unit_comp_map_pullbackCongr_hom`,
  `unit_comp_map_pullbackCongr_inv`, `unit_comp_map_pullbackComp_inv` and
  `unit_comp_map_pullbackId_hom`: the same four structural isomorphisms against the unit, as
  equalities of **morphisms**, before any open or section is chosen, with the change of spelling
  in the congruence case carried by
  `AlgebraicGeometry.Scheme.Modules.pushforwardCongr`. These are the statements that survive at a
  general open where the section-level ones do not; see "What is not done".
* `Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_pullbackSectionOn`: **Tag 01MY's comparison
  map on a pulled-back section over an arbitrary open.** The generalisation of
  `Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection` from the global homogeneous
  sections to every section over every open: the comparison carries the pulled-back section to
  the adjoint form of the comparison applied to it, read through the identification of
  restriction with pullback.

## The route

Nothing here is new mathematics. `twistMap_degreeSection` is proved from three ingredients, two
of which — `Stacks.AlgebraicGeometry.ProjTwistTheta.unit_comp_map_twistMap` and
`restrictUnit_comp_map_restrictFunctorIsoPullback` — are equalities of *morphisms* and therefore
say nothing about any particular open or section, while the third is the pointwise computation on
`degreeSection`. Dropping the third and evaluating the first at an arbitrary open and an
arbitrary section is exactly `twistMap_pullbackSectionOn`, whose right-hand side is consequently
written with `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` left standing rather
than traded for the unit of the pullback adjunction: trading it requires an open `T₁` with
`ι ⁻¹ᵁ T₁ = mapHom ⁻¹ᵁ T`, and over `⊤` that is free while in general it is a transport.

The four structural lemmas are the companion file's proofs verbatim, with `op ⊤` replaced by
`op T`: all four rest on `CategoryTheory.unit_conjugateEquiv` and on the matching pushforward
isomorphisms being the identity on sections, and none of those four facts mentions the open.

## Implementation notes

The measurements below are what shaped the file.

* **`(f ≫ g) ⁻¹ᵁ T` and `f ⁻¹ᵁ (g ⁻¹ᵁ T)` are definitionally equal**, as are `(𝟙 X) ⁻¹ᵁ T` and
  `T`. That is why `pullbackComp_inv_pullbackSectionOn` and `pullbackId_hom_pullbackSectionOn`
  need no transport and are the companion file's proofs unchanged.
* **The congruence lemmas of the companion file do not generalise, and not for want of a proof:
  their statements are ill-typed at a general open.** With `hf : f = g`, the section pulled back
  along `f` lives over `f ⁻¹ᵁ T` and the one along `g` over `g ⁻¹ᵁ T`, and those two opens are
  equal only propositionally; over `⊤` they are both `⊤` and the question does not arise. Two
  replacements are provided. `pullbackCongr_refl_inv_app` covers the case where the two morphisms
  are *the same* morphism, which is enough whenever the equality being transported along is one
  of definitionally equal morphisms; and `unit_comp_map_pullbackCongr_hom` covers the general
  case at the level of morphisms, where the mismatch is absorbed by
  `AlgebraicGeometry.Scheme.Modules.pushforwardCongr`.
* **`pullbackCongr_refl_inv_app` is proved at the level of variables, and has to be.** Asking for
  the same statement by `rfl` at a concrete instance — for the leading factor of Tag 01NO's
  comparison, whose congruence is between
  `Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` and the composite it is equal to
  by `CategoryTheory.Category.assoc` — makes the kernel reduce
  `AlgebraicGeometry.Scheme.Modules.pullback`, a left adjoint produced by a choice principle, and
  it exceeds the kernel's deterministic timeout. The timeout survives
  `attribute [local implicit_reducible]` on the sheaf spellings, and it is reached while checking
  the **statement**, not the proof — leaving the proof open does not avoid it. Over
  `⊤` the same identification is cheap, because both preimages are syntactically `⊤` after one
  reduction. Proof irrelevance reduces the hypothesis to `rfl` and the whole question disappears
  when `pullback` is applied to a variable.
* Every equality of morphisms is transported onto a section by `congrArg` of a function that
  evaluates a morphism, never by `rw`, because `AlgebraicGeometry.Scheme.Modules` is a `def`.

## What is not done

The six-factor composite of Tag 01NO is **not** computed here on a general section. The route
through the factors one at a time is the one `ProjInclusionDegreeSection` takes over `⊤`, and at a
general open it is blocked at the first factor by the kernel timeout recorded above: the
chain's own second factor is stated with the composite spelling of the morphism while the section
being fed in is pulled back along `projInclusionMap`, so the two spellings must meet in one
statement, and that statement cannot be checked.

The four morphism-level statements are provided because the route that avoids the obstruction is
to compute the **adjoint transpose** of the composite as a morphism and only then evaluate it: no
open and no section appears in such a chain, the change of spelling is carried by a named
isomorphism of pushforwards, and two morphisms out of a pullback are equal as soon as their
transposes are, since `CategoryTheory.Adjunction.homEquiv` is a bijection. That route is
**affordable**: `unit_comp_map_pullbackCongr_inv` instantiated at the leading factor of
Tag 01NO — the instance whose section-level form exceeds the kernel's deterministic timeout —
elaborates and kernel-checks in about two seconds, with both spellings of the morphism present in
the one statement. What is not done is the remaining chain: the transposes of the four middle
factors assembled into the composite, the trade of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` for the unit on the target side,
and the pointwise reading of the result, after which the cocycle itself is
`Stacks.AlgebraicGeometry.TwistBaseChange.fibreMap_comp` — which is already proved — plus the
matching of the three points involved.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistSections Stacks.AlgebraicGeometry.ProjTwistCompare

namespace Stacks.AlgebraicGeometry.PullbackUnit

universe u

variable {X Y Z : Scheme.{u}}

/-- **A section pulled back, over an arbitrary open.** The image of a section of `M` over an open
`T` of `Y` in the sections of `f^*M` over `f ⁻¹ᵁ T`, under the unit of the
pullback--pushforward adjunction. The two sides typecheck against each other because the sections
of a pushforward over `T` are by definition the sections of the module over `f ⁻¹ᵁ T`.

For `T = ⊤` this is `Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection`. -/
public def pullbackSectionOn (f : X ⟶ Y) (M : Y.Modules) (T : Y.Opens)
    (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullback f).obj M).val.obj (op (f ⁻¹ᵁ T)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op T) s

/-- Equal morphisms of modules agree on every section over every open. -/
private theorem val_app_eq_of_eq {W : Scheme.{u}} {M N : W.Modules} {ρ₁ ρ₂ : M ⟶ N}
    (h : ρ₁ = ρ₂) (T : W.Opens) (s : M.val.obj (op T)) :
    ρ₁.val.app (op T) s = ρ₂.val.app (op T) s := by
  subst h
  rfl

/-- **Naturality.** The pullback of a morphism carries the pulled-back section to the pulled-back
image. This is naturality of the unit of the adjunction, read over `T`. -/
public theorem pullback_map_pullbackSectionOn (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N)
    (T : Y.Opens) (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullback f).map φ).val.app (op (f ⁻¹ᵁ T))
        (pullbackSectionOn f M T s) =
      pullbackSectionOn f N T (φ.val.app (op T) s) :=
  (val_app_eq_of_eq
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ) T s).symm

/-- **The identity.** Pulling a section back along the identity and undoing the identification of
that pullback with the identity functor returns the section. The two opens `(𝟙 X) ⁻¹ᵁ T` and `T`
are definitionally equal. -/
public theorem pullbackId_hom_pullbackSectionOn (W : Scheme.{u}) (M : W.Modules)
    (T : W.Opens) (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullbackId W).hom.app M).val.app (op ((𝟙 W : W ⟶ W) ⁻¹ᵁ T))
        (pullbackSectionOn (𝟙 W) M T s) = s := by
  have h := unit_conjugateEquiv (Adjunction.id)
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 W))
    (Scheme.Modules.pullbackId W).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact (val_app_eq_of_eq h T s).symm

/-- **Composition, backwards.** The section pulled back along a composite, carried across the
pseudofunctoriality isomorphism, is the section pulled back along the second factor and then
along the first. The two opens `(f ≫ g) ⁻¹ᵁ T` and `f ⁻¹ᵁ (g ⁻¹ᵁ T)` are definitionally
equal. -/
public theorem pullbackComp_inv_pullbackSectionOn (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (T : Z.Opens) (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op ((f ≫ g) ⁻¹ᵁ T))
        (pullbackSectionOn (f ≫ g) M T s) =
      pullbackSectionOn f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ T)
        (pullbackSectionOn g M T s) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  exact (val_app_eq_of_eq h T s).symm

/-- **Composition, forwards.** The same identity read in the other direction, obtained by
cancelling the pseudofunctoriality isomorphism at the component with
`Stacks.AlgebraicGeometry.PullbackUnit.natIso_hom_inv_app`, which keeps the component opaque. -/
public theorem pullbackComp_hom_pullbackSectionOn (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (T : Z.Opens) (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).val.app (op ((f ≫ g) ⁻¹ᵁ T))
        (pullbackSectionOn f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ T)
          (pullbackSectionOn g M T s)) =
      pullbackSectionOn (f ≫ g) M T s :=
  (congrArg (((Scheme.Modules.pullbackComp f g).hom.app M).val.app (op ((f ≫ g) ⁻¹ᵁ T)))
      (pullbackComp_inv_pullbackSectionOn f g M T s).symm).trans
    (natIso_hom_inv_app (Scheme.Modules.pullbackComp f g) M ((f ≫ g) ⁻¹ᵁ T) _)

/-! ### The congruence isomorphism

The two statements of the companion file have no analogue here: with `hf : f = g` the two
pulled-back sections live over the two opens `f ⁻¹ᵁ T` and `g ⁻¹ᵁ T`, which are equal only
propositionally, so the equation cannot be written down. What replaces them is the pair below for
a congruence between a morphism and itself, and the pair of morphism-level statements after
it. -/

/-- **A congruence isomorphism between the pullbacks along one morphism and itself is the
identity on sections**, in the `inv` direction.

The hypothesis is a proof of a reflexive equation, which proof irrelevance reduces to `rfl`.
Stated and proved with the morphism, the module, the open and the section all variables: that is
the only place this is affordable. At the instance this exists for — the leading factor
of Tag 01NO's comparison map, where the equation is
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap_eq_comp`, whose two sides are
definitionally equal — asking for it by `rfl` sends the kernel into
`AlgebraicGeometry.Scheme.Modules.pullback` and past its deterministic timeout. -/
public theorem pullbackCongr_refl_inv_app (f : X ⟶ Y) (hf : f = f) (M : Y.Modules)
    (W₀ : X.Opens) (x : ((Scheme.Modules.pullback f).obj M).val.obj (op W₀)) :
    ((Scheme.Modules.pullbackCongr hf).inv.app M).val.app (op W₀) x = x := by
  obtain rfl : hf = rfl := Subsingleton.elim _ _
  rfl

/-- The same in the `hom` direction. -/
public theorem pullbackCongr_refl_hom_app (f : X ⟶ Y) (hf : f = f) (M : Y.Modules)
    (W₀ : X.Opens) (x : ((Scheme.Modules.pullback f).obj M).val.obj (op W₀)) :
    ((Scheme.Modules.pullbackCongr hf).hom.app M).val.app (op W₀) x = x := by
  obtain rfl : hf = rfl := Subsingleton.elim _ _
  rfl

/-- **The congruence isomorphism against the unit, as an equality of morphisms.** For two equal
morphisms, the unit of the adjunction of the first followed by the pushforward of the congruence
isomorphism is the unit of the adjunction of the second followed by the identification of the two
pushforwards.

No open and no section appears, which is the point: this is the statement that survives at a
general open, and the mismatch of the two preimages that makes the section-level statement
ill-typed is carried here by `AlgebraicGeometry.Scheme.Modules.pushforwardCongr`. -/
public theorem unit_comp_map_pullbackCongr_hom {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullbackCongr hf).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforwardCongr hf).inv.app ((Scheme.Modules.pullback g).obj M) := by
  subst hf
  aesop_cat

/-- The same in the `inv` direction: the congruence isomorphism is read from the pullback along
the second morphism back to the pullback along the first. -/
public theorem unit_comp_map_pullbackCongr_inv {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map ((Scheme.Modules.pullbackCongr hf).inv.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforwardCongr hf).hom.app ((Scheme.Modules.pullback f).obj M) := by
  subst hf
  aesop_cat

/-- **The pseudofunctoriality isomorphism for a composite against the unit, as an equality of
morphisms.** The unit of the adjunction of a composite, followed by the pushforward of the
isomorphism identifying the pullback along the composite with the two pullbacks in turn, is the
unit of the composite of the two adjunctions.

This is `CategoryTheory.unit_conjugateEquiv` at
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`, stated before any open or
section is chosen; `pullbackComp_inv_pullbackSectionOn` is this evaluated at an open and a
section, and is the form that is unusable when two spellings of the morphism have to meet. -/
public theorem unit_comp_map_pullbackComp_inv (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map
          ((Scheme.Modules.pullbackComp f g).inv.app M) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)).unit.app M := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact h.symm

/-- **The identity against the unit, as an equality of morphisms.** The companion of
`pullbackId_hom_pullbackSectionOn` before an open and a section are chosen, and
`CategoryTheory.unit_conjugateEquiv` at
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom`. -/
public theorem unit_comp_map_pullbackId_hom (W : Scheme.{u}) (M : W.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 W)).unit.app M ≫
        (Scheme.Modules.pushforward (𝟙 W)).map
          ((Scheme.Modules.pullbackId W).hom.app M) =
      (Adjunction.id (C := W.Modules)).unit.app M := by
  have h := unit_conjugateEquiv (Adjunction.id)
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 W))
    (Scheme.Modules.pullbackId W).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact h.symm

end Stacks.AlgebraicGeometry.PullbackUnit

namespace Stacks.AlgebraicGeometry.ProjTwistTheta

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **Tag 01MY's comparison map on a pulled-back section, over an arbitrary open.** For a
homomorphism `ψ : 𝒜 →+*ᵍ ℬ` of nonnegatively graded rings, an integer `n`, an open `T` of
`Proj 𝒜` and a section `a` of the `n`-th twist over `T`, the comparison map `θ n` carries the
image of `a` under the unit of the pullback--pushforward adjunction to the adjoint form of `θ n`
applied to `a`, read through the identification of restriction with pullback.

This is the generalisation of
`Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection` — Tag 01MY, part (1) — from the
global section attached to a homogeneous element to an arbitrary section over an arbitrary open.
It is `Stacks.AlgebraicGeometry.ProjTwistTheta.unit_comp_map_twistMap`, an equality of morphisms,
evaluated at `T` and at `a`; the pointwise content of the right-hand side is
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap_app_val`, which says it is the
fibre comparison applied pointwise.

The identification of restriction with pullback is left standing rather than traded for the unit
of the pullback adjunction of the open immersion. Trading it is
`Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback`, and
doing so asks for an open `T₁` of `Proj ℬ` with `ι ⁻¹ᵁ T₁ = mapHom ⁻¹ᵁ T`; over `⊤` the two are
both `⊤` and the trade is free, while in general it is a transport along
`ι ⁻¹ᵁ (ι ''ᵁ Z) = Z`, which holds for an open immersion but not definitionally. -/
public theorem twistMap_pullbackSectionOn (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (T : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 n).val.obj (op T)) :
    (twistMap 𝒜 ℬ ψ n).val.app (op ((mapHom 𝒜 ℬ ψ) ⁻¹ᵁ T))
        (PullbackUnit.pullbackSectionOn (mapHom 𝒜 ℬ ψ) (twistingSheaf 𝒜 n) T a) =
      ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
          (twistingSheaf ℬ n)).val.app (op ((mapHom 𝒜 ℬ ψ) ⁻¹ᵁ T))
        ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op T) a) :=
  PullbackUnit.val_app_eq_of_eq (unit_comp_map_twistMap 𝒜 ℬ ψ n) T a

end Stacks.AlgebraicGeometry.ProjTwistTheta

end
