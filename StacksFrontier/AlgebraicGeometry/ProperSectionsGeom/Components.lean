module

public import Mathlib.RingTheory.Artinian.Ring
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections

/-!
# Global functions on a proper scheme as a product over the connected components

Let `X` be a proper scheme over a field `k`. Clause (2) of [Stacks, Tag 0BUG] presents
`Γ(X, 𝒪_X)` as a finite product of Artinian local `k`-algebras, with one factor for each
connected component of `X`. This file proves that, for an arbitrary proper `X`: the connected
components are finite in number and each is open, the ring of sections over each of them is an
Artinian local `k`-algebra, and simultaneous restriction to the components is an isomorphism of
`k`-algebras from `Γ(X, 𝒪_X)` onto their product.

## Main definitions

All of these live in the namespace `Stacks.AlgebraicGeometry.ProperSectionsGeom`.

* `connectedComponentCarrier`: the subset of a scheme underlying a given connected component,
  described without choosing a point of it.
* `connectedComponentOpen`: that subset as an open, once its openness is known.
* `GlobalSectionsComponentDecomposition`: the data of clause (2) -- finiteness and openness of
  the components, the Artinian local structure of each factor, and the restriction isomorphism.

## Main results

* `componentwiseArtinianDecomposition`: clause (2). Every proper scheme over a field carries such
  a decomposition.

## Implementation notes

The index set is `ConnectedComponents X` itself rather than an abstract finite type, and
`GlobalSectionsComponentDecomposition.algEquiv_apply` pins each coordinate of the isomorphism to
be the canonical restriction map. Together with `finite_connectedComponents` these say that the
product is finite with *precisely one factor for each connected component*, and that the factor
at a component is the ring of functions on that component -- which is the content of the clause,
and is strictly more than the existence of some finite product of Artinian local algebras.

Every geometric input is already in the tree and none of the clause is reproved here:

* `X` is a Noetherian space (`ProperGeomConnected.noetherianSpace_of_isProper`), hence has
  finitely many connected components
  (`ProperGeomConnected.finite_connectedComponents_of_noetherianSpace`) and so each of them is
  open (`ProperGeomConnected.isOpen_connectedComponent_of_finite`). This replaces the source's
  appeal to the correspondence between primitive idempotents of `Γ(X, 𝒪_X)` and connected
  components; the correspondence is not needed, only the openness it is used to produce.
* The components form a pairwise disjoint open cover, so restriction is a bijection from
  `Γ(X, 𝒪_X)` onto the product of the component section rings
  (`ProperGeomConnected.bijective_piRestrict`, the sheaf condition for a disjoint cover). It is a
  `k`-algebra map because each factor's `k`-algebra structure is by definition the composite of
  the structure morphism with that restriction.
* Each factor is a finite `k`-module, being a quotient of `Γ(X, 𝒪_X)`, which is finite by clause
  (1) (`moduleFinite_globalSections_of_isProper`); a finite module over a field is Artinian, so
  each factor is an Artinian ring.
* Each factor is local: its component is preconnected, so the factor has no idempotents other
  than `0` and `1` (`ProperGeomConnected.isIdempotentElem_eq_zero_or_one`), and a nontrivial
  algebra integral over a field with only the trivial idempotents is local
  (`Stacks.RingTheory.IntegralOverField.isLocalRing_and_krullDimLE_zero`). Integrality here comes
  from finiteness of the factor over `k`, so clause (1) is used for both halves.

`Stacks.AlgebraicGeometry.ProperSectionsGeom.isArtinianRing_and_isLocalRing_globalSections_of_connectedSpace`
in `StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal` is the one-component case of
this clause: it is the statement below with `X` assumed connected, so that the product has a
single factor. It is kept, downstream files using it, but it no longer carries the tag.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0FD1](https://stacks.math.columbia.edu/tag/0FD1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ProperSectionsGeom

/-- The subset of `X` underlying the connected component `c`. This description is invariant under
the quotient and does not require choosing a point of the component. -/
def connectedComponentCarrier (X : Scheme.{u}) (c : _root_.ConnectedComponents X) : Set X :=
  ConnectedComponents.mk ⁻¹' {c}

theorem connectedComponentCarrier_mk (X : Scheme.{u}) (x : X) :
    connectedComponentCarrier X (ConnectedComponents.mk x) = connectedComponent x :=
  connectedComponents_preimage_singleton

/-- A connected component of `X`, regarded as an open of `X` once its openness is known. -/
def connectedComponentOpen (X : Scheme.{u}) (c : _root_.ConnectedComponents X)
    (hc : IsOpen (connectedComponentCarrier X c)) : X.Opens :=
  ⟨connectedComponentCarrier X c, hc⟩

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A presentation of the global functions of `X` as a product of the rings of functions on the
connected components of `X`, each of them an Artinian local `k`-algebra, the product being finite
because the components are.

This is the shape of clause (2) of [Stacks, Tag 0BUG]: the index set is the set of connected
components itself, and `algEquiv_apply` requires the isomorphism to be simultaneous restriction,
so the factor indexed by `c` is the ring of functions on the component `c` and not merely some
abstract Artinian local algebra. -/
structure GlobalSectionsComponentDecomposition where
  /-- There are only finitely many connected components, so the product is finite. -/
  finite_connectedComponents : Finite (_root_.ConnectedComponents X)
  /-- Every connected component is open, so it carries a ring of functions. -/
  isOpen_component : ∀ c : _root_.ConnectedComponents X, IsOpen (connectedComponentCarrier X c)
  /-- Each component's ring of functions is Artinian. -/
  isArtinianRing : ∀ c : _root_.ConnectedComponents X,
    IsArtinianRing Γ(X, connectedComponentOpen X c (isOpen_component c))
  /-- Each component's ring of functions is local. -/
  isLocalRing : ∀ c : _root_.ConnectedComponents X,
    IsLocalRing Γ(X, connectedComponentOpen X c (isOpen_component c))
  /-- The global functions are the product of the component rings, as `k`-algebras. -/
  algEquiv :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI (c : _root_.ConnectedComponents X) :
        Algebra k Γ(X, connectedComponentOpen X c (isOpen_component c)) :=
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫
        X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    Γ(X, ⊤) ≃ₐ[k] (∀ c, Γ(X, connectedComponentOpen X c (isOpen_component c)))
  /-- Each coordinate of `algEquiv` is restriction to the corresponding component. -/
  algEquiv_apply :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI (c : _root_.ConnectedComponents X) :
        Algebra k Γ(X, connectedComponentOpen X c (isOpen_component c)) :=
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫
        X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    ∀ (s : Γ(X, ⊤)) (c : _root_.ConnectedComponents X),
      algEquiv s c = X.presheaf.map (homOfLE le_top).op s

/-- **[Stacks, Tag 0BUG] (2).** The ring of global functions on a scheme proper over a field `k`
is a finite product of Artinian local `k`-algebras, with one factor for each connected component
of `X`, the factor at a component being the ring of functions on that component and the
isomorphism being simultaneous restriction.

No hypothesis beyond properness: `X` need not be connected, reduced, normal or integral, and the
structure morphism need not be affine. -/
@[stacks 0BUG "clause (2): for an ARBITRARY proper scheme over a field, the global functions are \
a product of Artinian local algebras over that field with one factor for each connected \
component. The index set is the set of connected components itself, the product is finite \
because a proper scheme over a field is a Noetherian space, and the isomorphism is pinned to be \
simultaneous restriction, so the factor at a component is the ring of functions on that \
component. Openness of the components replaces the source's correspondence between primitive \
idempotents and components; the product decomposition is the sheaf condition for a disjoint open \
cover; each factor is Artinian because it is a quotient of the global functions, finite over the \
base field by clause (1), and local because its component is connected."]
def componentwiseArtinianDecomposition [IsProper f] :
    GlobalSectionsComponentDecomposition k f := by
  classical
  have hnoeth : NoetherianSpace X := ProperGeomConnected.noetherianSpace_of_isProper f
  have hfin : Finite (_root_.ConnectedComponents X) :=
    ProperGeomConnected.finite_connectedComponents_of_noetherianSpace
  have hdisc : DiscreteTopology (_root_.ConnectedComponents X) :=
    ConnectedComponents.discreteTopology_iff.mpr
      ProperGeomConnected.isOpen_connectedComponent_of_finite
  have hOpen : ∀ c : _root_.ConnectedComponents X, IsOpen (connectedComponentCarrier X c) :=
    fun c => (isOpen_discrete _).preimage ConnectedComponents.continuous_coe
  let U : _root_.ConnectedComponents X → X.Opens := fun c => connectedComponentOpen X c (hOpen c)
  have hUcoe : ∀ c, (U c : Set X) = connectedComponentCarrier X c := fun _ => rfl
  have hcover : (⊤ : X.Opens) ≤ ⨆ c, U c := fun x _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, rfl⟩
  have hdisj : ∀ c d : _root_.ConnectedComponents X, c ≠ d → U c ⊓ U d = ⊥ := by
    intro c d hcd
    refine TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
    exact hcd (hx.1.symm.trans hx.2)
  have hconn : ∀ c, _root_.IsConnected (U c : Set X) := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [hUcoe, connectedComponentCarrier_mk]
    exact isConnected_connectedComponent
  have hne : ∀ c, Nonempty (U c) := fun c => (hconn c).nonempty.to_subtype
  -- The `k`-algebra structures.
  letI algTop : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  letI algU : ∀ c, Algebra k Γ(X, U c) := fun c =>
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫
      X.presheaf.map (homOfLE (le_top : U c ≤ ⊤)).op).hom.toAlgebra
  -- Simultaneous restriction, as a `k`-algebra homomorphism, and its bijectivity.
  let g : Γ(X, ⊤) →ₐ[k] (∀ c, Γ(X, U c)) :=
    { toFun := fun s c => X.presheaf.map (homOfLE (le_top : U c ≤ ⊤)).op s
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp
      commutes' := by
        intro r
        ext c
        change ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫
          X.presheaf.map (homOfLE (le_top : U c ≤ ⊤)).op).hom r) = _
        rfl }
  have hg : Function.Bijective g := ProperGeomConnected.bijective_piRestrict U hcover hdisj
  -- Clause (1) makes every factor a finite `k`-module, hence an Artinian ring.
  have hfinTop : Module.Finite k Γ(X, ⊤) := moduleFinite_globalSections_of_isProper k f
  have hfinPi : Module.Finite k (∀ c, Γ(X, U c)) :=
    Module.Finite.of_surjective g.toLinearMap hg.2
  have hfinU : ∀ c, Module.Finite k Γ(X, U c) := fun c =>
    Module.Finite.of_surjective (LinearMap.proj c : (∀ d, Γ(X, U d)) →ₗ[k] Γ(X, U c))
      (LinearMap.proj_surjective c)
  have hart : ∀ c, IsArtinianRing Γ(X, U c) := fun c =>
    have := hfinU c
    isArtinian_of_tower k inferInstance
  -- Each factor is local: it is integral over `k` and its component is connected.
  have hloc : ∀ c, IsLocalRing Γ(X, U c) := by
    intro c
    have := hfinU c
    have hnt : Nontrivial Γ(X, U c) := have := hne c; Scheme.component_nontrivial X (U c)
    have hint : Algebra.IsIntegral k Γ(X, U c) := Algebra.IsIntegral.of_finite k _
    exact (Stacks.RingTheory.IntegralOverField.isLocalRing_and_krullDimLE_zero (K := k)
      (fun e he => ProperGeomConnected.isIdempotentElem_eq_zero_or_one
        (hconn c).isPreconnected he)).2
  exact
    { finite_connectedComponents := hfin
      isOpen_component := hOpen
      isArtinianRing := hart
      isLocalRing := hloc
      algEquiv := AlgEquiv.ofBijective g hg
      algEquiv_apply := fun s c => rfl }

end Stacks.AlgebraicGeometry.ProperSectionsGeom

end
