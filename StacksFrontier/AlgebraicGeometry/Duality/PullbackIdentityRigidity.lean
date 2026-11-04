module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ZeroDimensionalTestModules
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
import StacksCore.Tactic.StacksAttribute

/-!
# A self-map of a scheme whose pullback functor is the identity fixes every point

Let `X` be a locally Noetherian scheme and let `g : X ⟶ X` be a morphism of schemes such that
`g^*ℱ ≅ ℱ` for every coherent `𝒪_X`-module `ℱ`.  Then `g` is the identity on the underlying
topological space of `X`.

This is the topological half of the step the proof of [Stacks, Tag 0G0E] leaves implicit: there
the Fourier-Mukai functor of the kernel produced in step 3 is identified with `L g^*` for
`g = pr_1 ∘ s`, and one has to conclude from `L g^* ≅ 𝟭` that `g` is the identity, so that `s` is
the diagonal.

## Main results

* `Stacks.Duality.preimage_eq_self_of_forall_nonempty_iso_pullback` — every closed subset of `X` is
  its own inverse image under `g`.
* `Stacks.Duality.base_eq_self_of_forall_nonempty_iso_pullback` — `g` fixes every point of `X`.
* `Stacks.Duality.base_eq_self_of_pullbackIso` — the same with the hypothesis in the form of an
  isomorphism of functors `g^* ≅ 𝟭`.

## Implementation notes

The argument is the following, and it uses no hypothesis on `X` beyond local Noetherianness and
no hypothesis on `g` at all.

*Closed subsets are inverse images of themselves.*  A closed subset `Z` of `X` is the support of a
coherent module, namely of `𝒪_X/ℐ_Z` for `ℐ_Z` the vanishing ideal sheaf of `Z`
(`AlgebraicGeometry.idealPowQuotient` at exponent one, coherent by
`AlgebraicGeometry.isCoherent_idealPowQuotient` on a locally Noetherian scheme, with support
`Z` by `AlgebraicGeometry.supp_idealPowQuotient_of_ne_zero` and
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal`).  The support of a pullback
of a module of finite type is the inverse image of the support, which is [Stacks, Tag 056J] in the
form `Stacks.Modules.supp_pullback`, and isomorphic modules have the same support.  So
`g^{-1}(Z) = Z`.

*Hence `g` fixes every point.*  Applying that to `Z = closure {g(x)}` gives `x ∈ closure {g(x)}`,
and to `Z = closure {x}` gives `g(x) ∈ closure {x}`: the two points specialize to each other.  The
underlying space of a scheme is Kolmogorov, so they are equal.

*What this does not give.*  The conclusion is about the continuous map underlying `g`, not about
`g` itself: it says nothing about the comorphism `g^♯ : 𝒪_X ⟶ 𝒪_X`.  Pinning that down needs more
than the existence of the isomorphisms `g^*ℱ ≅ ℱ` one module at a time — it needs their
naturality, and even then only says that `g^♯` carries each quasi-coherent ideal sheaf onto
itself.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Duality

variable {X : Scheme.{u}}

/-- **A closed subset of a locally Noetherian scheme is its own inverse image** under a morphism
`g : X ⟶ X` which pulls every coherent module back to a module isomorphic to it.

A closed subset is the support of the coherent module `𝒪_X/ℐ_Z`, the support of a pullback of a
module of finite type is the inverse image of the support ([Stacks, Tag 056J]), and isomorphic
modules have equal supports. -/
theorem preimage_eq_self_of_forall_nonempty_iso_pullback [IsLocallyNoetherian X] (g : X ⟶ X)
    (h : ∀ F : X.Modules, F.IsCoherent →
      Nonempty ((Scheme.Modules.pullback g).obj F ≅ F))
    {Z : Set X} (hZ : IsClosed Z) : g ⁻¹' Z = Z := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZ⟩ : Closeds X) with hI
  have hc : (idealPowQuotient I 1).IsCoherent := isCoherent_idealPowQuotient _ 1
  have := hc
  have := hc.isFiniteType
  have hsupp : SheafOfModules.supp (idealPowQuotient I 1) = Z := by
    rw [supp_idealPowQuotient_of_ne_zero _ one_ne_zero, hI]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal (⟨Z, hZ⟩ : Closeds X)
  obtain ⟨e⟩ := h _ hc
  have h2 := SheafOfModules.supp_eq_of_iso e
  rw [Stacks.Modules.supp_pullback g (idealPowQuotient I 1), hsupp] at h2
  exact h2

/-- **A morphism of a locally Noetherian scheme to itself which pulls every coherent module back to
a module isomorphic to it fixes every point.**

By `Stacks.Duality.preimage_eq_self_of_forall_nonempty_iso_pullback` the closure of `{g x}` and the
closure of `{x}` are both stable under taking inverse images, which puts each of `x` and `g x` in
the closure of the other; the underlying space of a scheme is Kolmogorov, so they are equal. -/
theorem base_eq_self_of_forall_nonempty_iso_pullback [IsLocallyNoetherian X] (g : X ⟶ X)
    (h : ∀ F : X.Modules, F.IsCoherent →
      Nonempty ((Scheme.Modules.pullback g).obj F ≅ F))
    (x : X) : g.base x = x := by
  have h1 : g ⁻¹' closure ({g.base x} : Set X) = closure ({g.base x} : Set X) :=
    preimage_eq_self_of_forall_nonempty_iso_pullback g h isClosed_closure
  have h2 : g ⁻¹' closure ({x} : Set X) = closure ({x} : Set X) :=
    preimage_eq_self_of_forall_nonempty_iso_pullback g h isClosed_closure
  have hx1 : x ∈ closure ({g.base x} : Set X) := by
    rw [← h1]; exact subset_closure rfl
  have hx2 : g.base x ∈ closure ({x} : Set X) := by
    have hmem : x ∈ g ⁻¹' closure ({x} : Set X) := by rw [h2]; exact subset_closure rfl
    exact hmem
  exact ((specializes_iff_mem_closure.2 hx1).antisymm
    (specializes_iff_mem_closure.2 hx2)).eq

/-- **A morphism of a locally Noetherian scheme to itself whose pullback functor is isomorphic to
the identity fixes every point.**  This is
`Stacks.Duality.base_eq_self_of_forall_nonempty_iso_pullback` with the hypothesis in the form it
arises in: an isomorphism of functors. -/
theorem base_eq_self_of_pullbackIso [IsLocallyNoetherian X] (g : X ⟶ X)
    (e : Scheme.Modules.pullback g ≅ 𝟭 X.Modules) (x : X) : g.base x = x :=
  base_eq_self_of_forall_nonempty_iso_pullback g (fun F _ => ⟨e.app F⟩) x

/-! ### The derived form of the hypothesis -/

section Derived

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

/-- **An isomorphism `L g^*(ℱ[0]) ≅ ℱ[0]` in the derived category gives an isomorphism
`g^*ℱ ≅ ℱ` of modules**: take degree-zero cohomology, where the derived pullback of a module
placed in degree zero is its ordinary pullback.

That identification is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleIso`, which needs no
flatness because a module placed in degree zero has nothing above degree zero, and the derived
pullback is right t-exact. -/
theorem nonempty_iso_pullback_of_iso_derivedPullback_single (g : X ⟶ X) (F : X.Modules)
    (e : (derivedPullback g.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj F) :
    Nonempty ((Scheme.Modules.pullback g).obj F ≅ F) :=
  ⟨(Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleIso
        g.toLRSHom.toShHom F 0).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules 0).mapIso e ≪≫
      Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologySingleIso F 0⟩

/-- **A morphism of a locally Noetherian scheme to itself whose *derived* pullback fixes the
single complex of every coherent module up to isomorphism fixes every point.**

This is the form the step of [Stacks, Tag 0G0E] discussed in the module docstring supplies: there
one has an isomorphism of functors on the perfect objects of `D(𝒪_X)`, and on a regular scheme the
single complex of a coherent module is perfect. -/
theorem base_eq_self_of_forall_iso_derivedPullback_single [IsLocallyNoetherian X] (g : X ⟶ X)
    (h : ∀ F : X.Modules, F.IsCoherent →
      Nonempty ((derivedPullback g.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
        (DerivedCategory.singleFunctor X.Modules 0).obj F))
    (x : X) : g.base x = x :=
  base_eq_self_of_forall_nonempty_iso_pullback g
    (fun F hF => (h F hF).elim
      fun e => nonempty_iso_pullback_of_iso_derivedPullback_single g F e) x

end Derived

end Stacks.Duality

end
