module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleFunctorial

/-!
# Transporting twisted global sections along an isomorphism of modules on `Proj`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `X = Proj 𝒮`, and let `φ : ℱ ≅ 𝒢` be an
isomorphism of `𝒪_X`-modules. Twisting is a functor, so `φ` induces for every `n ∈ ℤ` a bijection

`Γ(X, ℱ(n)) ≅ Γ(X, 𝒢(n))`

of the degree-`n` pieces of the graded modules of twisted global sections of [Stacks, Tag 03GK].
This file records that bijection as an isomorphism of additive groups, and proves that it is
**linear for the graded action of `S`**: a homogeneous scalar `a ∈ 𝒮 i` acts the same on both
sides, in the degree `i + n` the action lands in.

That compatibility is what the proof of [Stacks, Tag 0B5R] needs of an isomorphism of modules.
Additivity alone transports the *groups* `Γ(X, ℱ(n))`, but every conclusion the argument draws —
that a graded piece lies in the span of a lower one, that a truncation is a finite module — is a
statement about the `S`-module `⨁_n Γ(X, ℱ(n))`, so the scalars have to come along.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsIsoTransport`: the isomorphism of
  additive groups `Γ(X, ℱ(n)) ≅ Γ(X, 𝒢(n))` induced by `φ`.
* `twistedSectionsIsoTransport_homogeneousScalarTwistedSections`, in the same namespace: **the
  linearity.** The transport carries the graded action of Tag 03GK on `Γ(X, ℱ(n))` to the graded
  action of the same scalar on `Γ(X, 𝒢(n))`.

## Implementation notes

Everything here is a corollary of the functoriality already in the library, in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjTwistSectionModuleFunctorial.lean`:
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsMapComponent` is the map induced by a
bare morphism, and `twistedSectionsMapComponent_homogeneousScalarTwistedSections`
is already the square for a bare morphism. So the transport is that map for `φ.hom`, the inverse
is that map for `φ.inv`, and the linearity is the existing square verbatim: an isomorphism adds
nothing to the compatibility, only invertibility.

The two inversion identities are the single helper
`twistedSectionsMapComponent_comp_eq_self`, read once in each direction; it is
`twistedSectionsMapComponent_comp` together with `twistedSectionsMapComponent_id`, which is why
the bijectivity is not obtained from `Stacks.Veronese.bijective_sheafIsoSections`: that would
require first assembling `ℱ(n) ≅ 𝒢(n)` as an isomorphism of sheaves, and the inverse map is
needed here anyway.

**No `stacks` attribute.** Tag 01MN is the twist and Tag 03GK the module structure, both of which
carry bare attributes elsewhere in this library, and Tag 0B5R is the argument that consumes this
file rather than anything it states.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

universe u w

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable {F G : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮))}

/-- Two morphisms of modules composing to the identity induce maps on the degree-`n` twisted
global sections that compose to the identity: the induced maps are functorial, and the identity
induces the identity. -/
public theorem twistedSectionsMapComponent_comp_eq_self (φ : F ⟶ G) (ψ : G ⟶ F)
    (hc : φ ≫ ψ = 𝟙 F) (n : ℤ) (s : twistedSectionsComponent 𝒮 F n) :
    twistedSectionsMapComponent 𝒮 ψ n (twistedSectionsMapComponent 𝒮 φ n s) = s := by
  have h := twistedSectionsMapComponent_comp 𝒮 φ ψ n
  rw [hc, twistedSectionsMapComponent_id] at h
  exact (DFunLike.congr_fun h s).symm

/-- **An isomorphism `φ : ℱ ≅ 𝒢` of modules on `Proj 𝒮` on degree-`n` twisted global sections**,
as an isomorphism of additive groups `Γ(Proj 𝒮, ℱ(n)) ≅ Γ(Proj 𝒮, 𝒢(n))`: the global sections of
the `n`-th twist of `φ`, with the global sections of the twist of `φ⁻¹` as its inverse. -/
public noncomputable def twistedSectionsIsoTransport (φ : F ≅ G) (n : ℤ) :
    twistedSectionsComponent 𝒮 F n ≃+ twistedSectionsComponent 𝒮 G n where
  toFun := twistedSectionsMapComponent 𝒮 φ.hom n
  invFun := twistedSectionsMapComponent 𝒮 φ.inv n
  left_inv := twistedSectionsMapComponent_comp_eq_self 𝒮 φ.hom φ.inv φ.hom_inv_id n
  right_inv := twistedSectionsMapComponent_comp_eq_self 𝒮 φ.inv φ.hom φ.inv_hom_id n
  map_add' := (twistedSectionsMapComponent 𝒮 φ.hom n).map_add

/-- **The transport along an isomorphism is linear for the graded action of `S`.**

Let `a ∈ 𝒮 i` and let `s` be a global section of `ℱ(n)`. The action of Tag 03GK carries `s` to a
global section of `ℱ(i + n)`; transporting that along `φ` gives the same thing as transporting `s`
and then acting by `a` on `Γ(Proj 𝒮, 𝒢(n))`.

Together with the additivity built into `twistedSectionsIsoTransport` this says that the transport
is an isomorphism of graded `S`-modules from `⨁_n Γ(Proj 𝒮, ℱ(n))` onto `⨁_n Γ(Proj 𝒮, 𝒢(n))`,
which is what lets a finiteness or generation statement about one of the two be read off the
other. -/
public theorem twistedSectionsIsoTransport_homogeneousScalarTwistedSections
    (φ : F ≅ G) (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : twistedSectionsComponent 𝒮 F n) :
    twistedSectionsIsoTransport 𝒮 φ ((i : ℤ) + n)
        (homogeneousScalarTwistedSections 𝒮 F i n a s) =
      homogeneousScalarTwistedSections 𝒮 G i n a (twistedSectionsIsoTransport 𝒮 φ n s) :=
  twistedSectionsMapComponent_homogeneousScalarTwistedSections 𝒮 φ.hom i n a s

end Stacks.AlgebraicGeometry.ProjTwistedSections

end
