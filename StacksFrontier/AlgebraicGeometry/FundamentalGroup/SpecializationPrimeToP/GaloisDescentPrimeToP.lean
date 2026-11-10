module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationPrimeToP
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationPrimeToP.GaloisCoverOfOpenNormal
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction

/-!
# The prime-to-`p` descent input of Tag 0C0R, on Galois covers of the geometric generic fibre

`AlgebraicGeometry.exists_continuousMulEquiv_primeToP_of_forall_lift` reduces the second
conclusion of [Stacks, Tag 0C0R] — that a specialization map induces an isomorphism of the maximal
prime-to-`p` quotients — to the group-theoretic hypothesis `hlift`: every open normal subgroup
`N ≤ π₁(X_{s̄'})` of index prime to `p` is the preimage along `sp` of an open normal subgroup of
`π₁(X_{s̄})`. This file discharges `hlift` from a hypothesis about covers which mentions no
fundamental group, namely the one the Stacks proof of Tag 0C0R produces:

> Galois objects of `FÉt_{X_{s̄'}}` whose Galois group has order prime to `p` are in the essential
> image of base change.

Three steps do it.

* An open normal subgroup `N` of index prime to `p` is realized by a *Galois* cover of degree
  `[π₁ : N]`, which is therefore prime to `p`
  (`exists_isGalois_card_fiber_eq_index_stabilizer_eq_of_isOpen`, in the namespace
  `AlgebraicGeometry.EtaleFundamentalGroup`). This is where normality of `N` is spent, and it is
  the only reason the hypothesis may be restricted to the Galois covers.
* An element of `π₁(X_{s̄'})` killed by the map to `π₁(X_A)` acts trivially on every cover in the
  essential image of base change, by naturality against the isomorphism exhibiting the cover as a
  base change. So the kernel of `sp` is contained in `N`: the defining equation of a
  specialization map factors `sp` through `π₁(X_A)` up to an isomorphism, and `N` is a point
  stabilizer on a cover in the essential image.
* A surjection of a compact group onto a Hausdorff group is a quotient map, so an open normal
  subgroup containing the kernel is the preimage of its (normal, open) image.

The prime-to-`p` condition is *not* used in the second and third steps: they prove the general
statement that an open normal subgroup containing the kernel lifts. All that the degree condition
does is cut down the covers which the geometric hypothesis has to reach — which is exactly the
difference between Tag 0C0R and the unrestricted descent of Tag 0C0Q.

**No `@[stacks 0C0R]` attribute is attached to anything here**: the descent of the prime-to-`p`
Galois covers is an input, not a theorem, so nothing here states the tag. What remains of
Tag 0C0R is exactly that input, over a strictly henselian discrete valuation ring with
algebraically closed residue field of characteristic `p`.

## Main results

* `Stacks.FundamentalGroup.exists_open_normal_comap_eq_of_ker_le` — an open normal subgroup
  containing the kernel of a continuous surjection of a compact group onto a Hausdorff group is
  the preimage of an open normal subgroup.
* `AlgebraicGeometry.app_eq_id_of_etaleFundamentalGroupMap_eq_one_of_essImage` — an element of the
  étale fundamental group killed by the map induced by `f : X ⟶ Y` acts trivially on every cover
  of `X` which is a base change along `f`.
* `AlgebraicGeometry.forall_lift_primeToP_of_isSpecializationMap_of_essImage_isGalois` — the
  hypothesis `hlift` of `exists_continuousMulEquiv_primeToP_of_forall_lift`, from the descent of
  the prime-to-`p` Galois covers.
* `AlgebraicGeometry.surjective_and_exists_continuousMulEquiv_primeToP_of_essImage_isGalois` —
  both conclusions of [Stacks, Tag 0C0R] granted that descent.

## References

* [Stacks Project, Tag 0C0R](https://stacks.math.columbia.edu/tag/0C0R)
* [Stacks Project, Tag 0C0Q](https://stacks.math.columbia.edu/tag/0C0Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory IsLocalRing
open Stacks.FundamentalGroup

universe u

namespace Stacks.FundamentalGroup

/-- **An open normal subgroup containing the kernel is a preimage.** Let `φ : G →ₜ* H` be a
continuous surjection with `G` compact and `H` Hausdorff, and let `N ≤ G` be open and normal with
`ker φ ≤ N`. Then `N` is the preimage along `φ` of an open normal subgroup of `H`, namely of its
own image.

The image is normal because `φ` is surjective, and `N` is the preimage of its image because `N`
contains the kernel; the image is open because `φ` is a quotient map — continuous, surjective and
closed, `G` being compact and `H` Hausdorff — whose preimage of the image is `N` again.

This is the general statement behind the descent hypothesis of
`Stacks.FundamentalGroup.primeToPKernel_comap_le_of_forall_lift`: the prime-to-`p` condition on
the subgroup plays no part, it only arises in the proof that the kernel is contained in `N`. -/
theorem exists_open_normal_comap_eq_of_ker_le {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] [CompactSpace G] [T2Space H] (φ : G →ₜ* H)
    (hφ : Function.Surjective φ) {N : Subgroup G} (hnorm : N.Normal)
    (hopen : IsOpen (N : Set G)) (hker : MonoidHom.ker φ.toMonoidHom ≤ N) :
    ∃ M : Subgroup H, M.Normal ∧ IsOpen (M : Set H) ∧ M.comap φ.toMonoidHom = N := by
  have hcm : (N.map φ.toMonoidHom).comap φ.toMonoidHom = N := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
  have hq : Topology.IsQuotientMap φ :=
    Topology.IsQuotientMap.of_surjective_continuous hφ φ.continuous
  refine ⟨N.map φ.toMonoidHom, hnorm.map _ hφ, ?_, hcm⟩
  rw [← hq.isOpen_preimage]
  change IsOpen (φ.toMonoidHom ⁻¹' (N.map φ.toMonoidHom : Set H))
  rwa [← Subgroup.coe_comap, hcm]

end Stacks.FundamentalGroup

namespace AlgebraicGeometry

/-! ### The kernel of a base change map acts trivially on the essential image -/

/-- **An element killed by the map of fundamental groups acts trivially on a base change.** Let
`f : X ⟶ Y` be a morphism of connected schemes, `x` a geometric point of `X` and `γ` an element of
`π₁(X, x)` whose image in `π₁(Y, f ∘ x)` is trivial. Then the component of `γ` at any finite étale
cover of `X` isomorphic to the base change of a cover of `Y` is the identity.

The induced homomorphism is the action on automorphism groups of precomposition with base change,
conjugated by the fibre projections; conjugation is injective, so `γ` restricts to the identity
along base change, and naturality against the given isomorphism carries that to the cover
itself. -/
theorem app_eq_id_of_etaleFundamentalGroupMap_eq_one_of_essImage {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X)
    {γ : EtaleFundamentalGroup X x} (hγ : etaleFundamentalGroupMap f x γ = 1)
    (A : FiniteEtaleOver X)
    (hA : ∃ B : FiniteEtaleOver Y, Nonempty ((finiteEtaleBaseChange f).obj B ≅ A)) :
    γ.asIso.hom.app A = 𝟙 ((finiteEtaleFiberFunctor x).obj A) := by
  let W := (Functor.whiskeringLeft (FiniteEtaleOver Y) (FiniteEtaleOver X) (Type u)).obj
    (finiteEtaleBaseChange f)
  have hone : W.mapAut (finiteEtaleFiberFunctor x) γ = 1 :=
    (finiteEtaleFiberProjectionIso f x).conjAut.map_eq_one_iff.mp hγ
  have hres : ∀ B : FiniteEtaleOver Y, γ.asIso.hom.app ((finiteEtaleBaseChange f).obj B) = 𝟙 _ :=
    fun B ↦ NatTrans.congr_app (congrArg (fun a => a.asIso.hom) hone) B
  obtain ⟨B, ⟨e⟩⟩ := hA
  have hnat := γ.asIso.hom.naturality e.hom
  rw [hres B, Category.id_comp] at hnat
  exact (cancel_epi ((finiteEtaleFiberFunctor x).mapIso e).hom).mp
    (hnat.trans (Category.comp_id _).symm)

/-! ### The descent hypothesis `hlift` from the descent of prime-to-`p` Galois covers -/

/-- **The prime-to-`p` descent hypothesis of Tag 0C0R, from the descent of Galois covers of
prime-to-`p` degree.** Let `f : X ⟶ S` be proper with geometrically connected fibres, let
`s' ⇝ s` be a specialization of points of `S` realized by a specialization map
`sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})`, and suppose `sp` is surjective. If every finite étale cover of the
geometric fibre `X_{s̄'}` which is a Galois object of `FÉt_{X_{s̄'}}` and whose Galois group
`Aut A` has order prime to `p` is isomorphic to the base change along `X_{s̄'} ⟶ X` of a finite
étale cover of `X`, then every open normal subgroup `N ≤ π₁(X_{s̄'})` of index prime to `p` is the
preimage along `sp` of an open normal subgroup of `π₁(X_{s̄})`.

The order of the Galois group of a Galois object is its degree
(`AlgebraicGeometry.EtaleFundamentalGroup.card_aut_eq_card_fiber_of_isGalois`), so the hypothesis
is equally the descent of the Galois covers of degree prime to `p`.

`N` is the stabilizer of a point of the geometric fibre of a Galois cover of degree `[π₁ : N]`,
hence of degree prime to `p`; the hypothesis puts that cover in the essential image of base change
from `X`, hence from `X_A` for the strict henselization `A` of `𝒪_{S,s}` presenting `sp`; so the
kernel of the map `π₁(X_{s̄'}) ⟶ π₁(X_A)` — which contains the kernel of `sp`, by the equation
defining a specialization map — acts trivially there and is contained in `N`. Then
`Stacks.FundamentalGroup.exists_open_normal_comap_eq_of_ker_le` applies. -/
theorem forall_lift_primeToP_of_isSpecializationMap_of_essImage_isGalois {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [GeometricallyConnected f] (s' s : GeometricPoint S) (p : ℕ)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp) (hsurj : Function.Surjective sp)
    (hgal : ∀ A : FiniteEtaleOver (fiberOverGeometricPoint f s'), IsGalois A →
      ¬ p ∣ Nat.card (Aut A) →
      ∃ B : FiniteEtaleOver X,
        Nonempty ((finiteEtaleBaseChange (pullback.fst f s'.hom)).obj B ≅ A)) :
    ∀ N : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x'),
      N.Normal → IsOpen (N : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x')) →
      ¬ p ∣ N.index →
      ∃ M : Subgroup (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x),
        M.Normal ∧ IsOpen (M : Set (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)) ∧
          M.comap sp.toMonoidHom = N := by
  obtain ⟨A, hAc, hAloc, hAlg, -, p', hp', pp, hpp, -, hXA, -, t, hform⟩ := hsp
  have : CompactSpace (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x') :=
    compactSpace_etaleFundamentalGroup _ x'
  have : T2Space (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x) :=
    t2Space_etaleFundamentalGroup _ x
  intro N hnorm hopen hindex
  -- a Galois cover of degree `[π₁ : N]` with `N` as a point stabilizer
  obtain ⟨Y, y, hYgal, hcard, hstab⟩ :=
    EtaleFundamentalGroup.exists_isGalois_card_fiber_eq_index_stabilizer_eq_of_isOpen x' N hnorm
      hopen
  -- it descends to `X`, hence to `X_A`
  obtain ⟨C, ⟨e⟩⟩ := hgal Y hYgal
    (by rwa [EtaleFundamentalGroup.card_aut_eq_card_fiber_of_isGalois x' Y, hcard])
  -- the kernel of `sp` is contained in `N`
  have hker : MonoidHom.ker sp.toMonoidHom ≤ N := by
    intro γ hγ
    have hγ' : sp γ = 1 := hγ
    have h1 : etaleFundamentalGroupMap (fiberOverGeometricPointMap f s' _ p' hp') x' γ = 1 := by
      have h0 := hform γ
      rw [hγ', map_one] at h0
      exact (etaleFundamentalGroupMulEquiv t).map_eq_one_iff.mp h0.symm
    have h2 := app_eq_id_of_etaleFundamentalGroupMap_eq_one_of_essImage
      (fiberOverGeometricPointMap f s' _ p' hp') x' h1 Y
      ⟨(finiteEtaleBaseChange (pullback.fst f _)).obj C,
        ⟨((finiteEtaleBaseChangeComp (fiberOverGeometricPointMap f s' _ p' hp')
          (pullback.fst f _) (pullback.fst f s'.hom)
          (pullback.lift_fst _ _ _).symm).app C).symm ≪≫ e⟩⟩
    rw [← hstab, MulAction.mem_stabilizer_iff]
    change ConcreteCategory.hom (γ.asIso.hom.app Y) y = y
    rw [h2]
    rfl
  exact exists_open_normal_comap_eq_of_ker_le sp hsurj hnorm hopen hker

/-! ### Tag 0C0R granted the descent of prime-to-`p` Galois covers -/

/-- **Stacks Project, Tag 0C0R, granted the descent of the Galois covers of prime-to-`p` degree of
the geometric generic fibre (`Hgal`).** Let `f : X ⟶ S` be a smooth proper morphism with
geometrically connected fibres, let `s' ⇝ s` be a specialization of points of `S` realized by a
specialization map `sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})`, and let `p` be the characteristic of `κ(s)`. If
every Galois finite étale cover of `X_{s̄'}` whose Galois group has order prime to `p` is the base
change along `X_{s̄'} ⟶ X` of a finite étale cover of `X`, then `sp` is surjective and
induces an isomorphism `π'₁(X_{s̄'}) ≅ π'₁(X_{s̄})` of the maximal prime-to-`p` quotients,
commuting with the projections.

Surjectivity is `AlgebraicGeometry.surjective_specializationMap_of_smooth` and needs nothing of
the characteristic nor of the descent. The isomorphism is
`AlgebraicGeometry.exists_continuousMulEquiv_primeToP_of_forall_lift` with its hypothesis supplied
by `AlgebraicGeometry.forall_lift_primeToP_of_isSpecializationMap_of_essImage_isGalois`.

Compared with the descent input of [Stacks, Tag 0C0Q]
(`AlgebraicGeometry.bijective_isSpecializationMap_of_ringChar_zero_of_forall_essImage_isGalois`),
the input here is restricted to the covers of degree prime to `p` — which is the whole difference
between the two tags, and the reason Tag 0C0R holds in residue characteristic `p` while the
unrestricted descent does not.

No hypothesis ties `p` to the residue characteristic: the reduction is uniform in `p`. The
descent hypothesis is plausible only when `p` is the residue characteristic, as in Tag 0C0R.

**No `@[stacks 0C0R]` attribute is attached**: `Hgal` is an input, not a theorem. -/
theorem surjective_and_exists_continuousMulEquiv_primeToP_of_essImage_isGalois {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [IsProper f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (p : ℕ) (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hgal : ∀ A : FiniteEtaleOver (fiberOverGeometricPoint f s'), IsGalois A →
      ¬ p ∣ Nat.card (Aut A) →
      ∃ B : FiniteEtaleOver X,
        Nonempty ((finiteEtaleBaseChange (pullback.fst f s'.hom)).obj B ≅ A)) :
    Function.Surjective sp ∧
      ∃ e : PrimeToP p (EtaleFundamentalGroup (fiberOverGeometricPoint f s') x') ≃ₜ*
          PrimeToP p (EtaleFundamentalGroup (fiberOverGeometricPoint f s) x),
        ∀ g, e (primeToPMk p _ g) = primeToPMk p _ (sp g) :=
  exists_continuousMulEquiv_primeToP_of_forall_lift f s' s p x' x sp hsp
    (forall_lift_primeToP_of_isSpecializationMap_of_essImage_isGalois f s' s p x' x sp hsp
      (surjective_specializationMap_of_smooth f s' s x' x sp hsp) hgal)

end AlgebraicGeometry

end
