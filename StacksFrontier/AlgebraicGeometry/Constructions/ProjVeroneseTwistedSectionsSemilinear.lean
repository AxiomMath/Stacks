module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseGlobalSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwistedSections

/-!
# The Veronese comparison on twisted global sections is semilinear

Let `S` be a graded ring, `d ≥ 1`, `S' = S⁽ᵈ⁾` the `d`-th Veronese subring,
`i : X = Proj S ≅ X' = Proj S'` the isomorphism of [Stacks, Tag 0B5J], `ℱ'` a sheaf of
`𝒪_{X'}`-modules and `ℱ = i^*ℱ'`.
`Stacks.Veronese.veroneseTwistedSectionsComparison` is the bijection

`Γ(X', ℱ'(n)) ≅ Γ(X, ℱ(nd))`,

and `Stacks.Veronese.veroneseTwistedSectionsAddEquiv` is it as an isomorphism of additive groups.
This file proves that it is **semilinear over the inclusion `S⁽ᵈ⁾ ⊆ S`**: a scalar `a` of Veronese
degree `e`, that is an element of `S_{ed}`, acts the same on both sides.

That is the statement the Veronese reduction of [Stacks, Tag 0B5R] consumes. On `X'` the graded
ring `S⁽ᵈ⁾` is generated in degree one for a suitable `d`
(`Stacks.Veronese.exists_finite_degreeOne_generators_veroneseSubring`,
`Stacks.Veronese.isNoetherianRing_veroneseGrading_zero`), so the whole degree-one theory applies
there; additivity alone carries its *groups* back to `X`, but every conclusion the reduction wants
— that a graded piece lies in the span of a lower one, that a truncated module is finite — is a
statement about *modules*, and needs the scalars carried back too.

## Main results

* `Stacks.Veronese.veroneseTwistedSectionsComparison_homogeneousScalarTwistedSections`: **the
  semilinearity.** For `a` in `S_{ed}`, read as an element of `S⁽ᵈ⁾` of Veronese degree `e`, the
  comparison carries the graded action of Tag 03GK on `Γ(X', ℱ'(n))` to the graded action of `a`
  on `Γ(X, ℱ(nd))`.
* `Stacks.Veronese.veroneseScalarDegree`: the degree bookkeeping `ed + nd = (e + n)d` the
  statement transports along.
* `Stacks.Veronese.multiplyHomogeneousSections'_cast_left`: transporting the left factor of a
  product of global sections along an equality of degrees transports the product.
* `Stacks.Veronese.veroneseTwistedSectionsComparison_eq`: the comparison unfolded, as the unit of
  the pullback followed by the inverse of Tag 0B5J's isomorphism.
* `Stacks.Veronese.veronesePushforward` and
  `Stacks.Veronese.veronesePushforwardPullbackIso`: what makes the semilinearity applicable to an
  *arbitrary* sheaf of modules `ℱ` on `X`. Everything above is stated for `ℱ = i^*ℱ'`, which is
  the shape Tag 0B5J's squares are phrased in; `ℱ' := i_*ℱ` and the counit of the adjunction,
  invertible because `i` is an isomorphism, put a general `ℱ` into that shape.

## Implementation notes

The proof is `Stacks.Veronese.veroneseMultiplyHomogeneousSectionsCompatibility` — Tag 0B5J's
compatibility with the products of global sections of Tag 03GK — with both of its correspondence
hypotheses discharged:

* for the *scalar* it is `Stacks.Veronese.veroneseTwistingSheafIso_degreeSection`, assertion (2)
  of Tag 0B5J read on the global section of `𝒪_X(ed)` that `a` names;
* for the *section* it is the inverse identity of Tag 0B5J's isomorphism
  (`Stacks.Veronese.sheafSections_comp_eq_self`). The square asks for a section of `ℱ(nd)` whose
  image under the isomorphism's *forward* map is a pullback, while the comparison is by
  construction the *inverse* applied to a pullback; those are the same requirement, read in the
  two directions.

Both actions are then rewritten into products of Tag 03GK by
`Stacks.Veronese.homogeneousScalarTwistedSections_eq_multiplyHomogeneousSections`, the bridge
between the module structure's action and the square's product.

Two reindexings of degrees have to be reconciled against the `eqToHom`s the square already
carries: `Nat.cast_mul`, because the scalar's degree is the natural number `ed` on the `X` side
and the integer `e · d` in the square, and `add_mul`, because the square lands in `ed + nd` while
the comparison at Veronese degree `e + n` lands in `(e + n)d`.

**The degree equation is a named theorem, `veroneseScalarDegree`, and not an inline
`by push_cast; ring`.** The final step of the proof is an `exact` whose two sides differ only in
which proof of that equation sits inside an `eqToHom`. With the equation inline the statement and
the proof elaborate two distinct terms, and the unifier spends its whole heartbeat budget on them
before it can appeal to proof irrelevance; with one name on both sides the terms are
syntactically equal and the step is immediate. The same is why
`multiplyHomogeneousSections'_cast_left` takes the target equation `hr'` as a hypothesis instead
of building it from `h` and `hr`.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistSheafOfModules
  degreeSection multiplyHomogeneousSections multiplyHomogeneousSections')
open Stacks.AlgebraicGeometry.ProjTwistedSections (homogeneousScalarTwistedSections)

namespace Stacks.Veronese

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w

section Cast

variable {A : Type u} {ς : Type w} [CommRing A] [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς)
  [GradedRing 𝒜]
  (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒜)))

/-- **Transporting the left factor of a product of global sections along an equality of degrees
transports the product.** The two equalities of target degrees, `q + b = r` and `p + b = r`, are
separate hypotheses rather than one derived from the other: a consumer has the second one in hand
already, and handing it in is what makes the identity usable by `exact`. -/
public theorem multiplyHomogeneousSections'_cast_left {p q r : ℤ} (h : p = q) {b : ℤ}
    (hr : q + b = r) (hr' : p + b = r) (x : (twistingSheaf 𝒜 p).val.obj (op ⊤))
    (w : (twistSheafOfModules 𝒜 F b).val.obj (op ⊤)) :
    ((eqToHom (congrArg (twistSheafOfModules 𝒜 F) hr)).val.app (op ⊤)).hom
        (multiplyHomogeneousSections' 𝒜 F q b
          (((eqToHom (congrArg (twistingSheaf 𝒜) h)).val.app (op ⊤)).hom x) w) =
      ((eqToHom (congrArg (twistSheafOfModules 𝒜 F) hr')).val.app (op ⊤)).hom
        (multiplyHomogeneousSections' 𝒜 F p b x w) := by
  subst h
  simp

end Cast

variable {S : Type u} {σ : Type w} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The degree bookkeeping of the Veronese semilinearity.** A scalar of Veronese degree `e`
acting on the twisted sections of degree `n` on `Proj S⁽ᵈ⁾` lands in Veronese degree `e + n`,
which the comparison reads in degree `(e + n)d` on `Proj S`; on `Proj S` the same scalar has
degree `ed` and lands in `ed + nd`. -/
public theorem veroneseScalarDegree (e : ℕ) (n : ℤ) (d : ℕ) :
    ((e * d : ℕ) : ℤ) + n * d = ((e : ℤ) + n) * d := by
  push_cast
  ring

/-- **The Veronese comparison on twisted global sections, unfolded**: the unit of the pullback
along `i`, followed by the inverse of Tag 0B5J's isomorphism `ℱ(nd) ≅ i^*(ℱ'(n))`. -/
public theorem veroneseTwistedSectionsComparison_eq (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n : ℤ)
    (s' : letI := veroneseGradingGradedRing 𝒮 d hd
      (twistSheafOfModules (veroneseGrading 𝒮 d) F' n).val.obj (op ⊤)) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    veroneseTwistedSectionsComparison 𝒮 d hd F' n s' =
      ((veroneseTwistedModuleIso 𝒮 d hd F' n).inv.val.app (op ⊤)).hom
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (twistSheafOfModules (veroneseGrading 𝒮 d) F' n) ⊤ s') :=
  rfl

/-- **The Veronese comparison on twisted global sections is semilinear over the inclusion of the
Veronese subring.**

Let `a ∈ S_{ed}`, read as an element of `S⁽ᵈ⁾` homogeneous of Veronese degree `e`, and let `s'` be
a global section of `ℱ'(n)` on `X' = Proj S⁽ᵈ⁾`. Then the comparison
`Γ(X', ℱ'(n)) ≅ Γ(X, ℱ(nd))` carries the graded action of `a` on `s'` — the action of Tag 03GK
on the twisted global sections of `X'` — to the graded action of `a` on the corresponding section
of `ℱ(nd)`, once the degrees `ed + nd` and `(e + n)d` are identified.

Together with
`Stacks.Veronese.veroneseTwistedSectionsAddEquiv` this says that the comparison is an isomorphism
of graded `S⁽ᵈ⁾`-modules from `⨁_n Γ(X', ℱ'(n))` onto `⨁_n Γ(X, ℱ(nd))`, which is what lets a
finiteness or generation statement proved on `X'`, where `S⁽ᵈ⁾` is generated in degree one, be
read back on `X`, where `S` need not be generated in degree one at all. -/
public theorem veroneseTwistedSectionsComparison_homogeneousScalarTwistedSections
    (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (e : ℕ) (n : ℤ)
    (a : veroneseSubring 𝒮 d) (ha : (a : S) ∈ 𝒮 (e * d))
    (w' : letI := veroneseGradingGradedRing 𝒮 d hd
      (twistSheafOfModules (veroneseGrading 𝒮 d) F' n).val.obj (op ⊤)) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    veroneseTwistedSectionsComparison 𝒮 d hd F' ((e : ℤ) + n)
        (homogeneousScalarTwistedSections (veroneseGrading 𝒮 d) F' e n ⟨a, ha⟩ w') =
      ((eqToHom (congrArg (twistSheafOfModules 𝒮 (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d)
            (veroneseProjIso 𝒮 d hd).hom F'))
          (veroneseScalarDegree e n d))).val.app (op ⊤)).hom
        (homogeneousScalarTwistedSections 𝒮 (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d)
            (veroneseProjIso 𝒮 d hd).hom F') (e * d) (n * d) ⟨(a : S), ha⟩
          (veroneseTwistedSectionsComparison 𝒮 d hd F' n w')) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  rw [homogeneousScalarTwistedSections_eq_multiplyHomogeneousSections,
    homogeneousScalarTwistedSections_eq_multiplyHomogeneousSections,
    multiplyHomogeneousSections_eq_prime 𝒮
      (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F') (e * d)
      (n * d) (degreeSection 𝒮 (e * d) ⟨(a : S), ha⟩)
      (veroneseTwistedSectionsComparison 𝒮 d hd F' n w')]
  have hcast : ((e * d : ℕ) : ℤ) = (e : ℤ) * (d : ℤ) := Nat.cast_mul e d
  have hs := veroneseTwistingSheafIso_degreeSection 𝒮 d hd e a ha
  have ht := sheafSections_comp_eq_self (veroneseTwistedModuleIso 𝒮 d hd F' n).inv
    (veroneseTwistedModuleIso 𝒮 d hd F' n).hom
    (veroneseTwistedModuleIso 𝒮 d hd F' n).inv_hom_id (op ⊤)
    (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
      (twistSheafOfModules (veroneseGrading 𝒮 d) F' n) ⊤ w')
  have hsq := veroneseMultiplyHomogeneousSectionsCompatibility 𝒮 d hd F' (e : ℤ) n
    (((eqToHom (congrArg (twistingSheaf 𝒮) hcast)).val.app (op ⊤)).hom
      (degreeSection 𝒮 (e * d) ⟨(a : S), ha⟩))
    (veroneseTwistedSectionsComparison 𝒮 d hd F' n w')
    (degreeSection (veroneseGrading 𝒮 d) e ⟨a, ha⟩) w' hs ht
  have hL := (veroneseTwistedSectionsComparison_eq 𝒮 d hd F' ((e : ℤ) + n)
      (multiplyHomogeneousSections (veroneseGrading 𝒮 d) F' e n
        (degreeSection (veroneseGrading 𝒮 d) e ⟨a, ha⟩) w')).trans
    (congrArg (fun z => ((veroneseTwistedModuleIso 𝒮 d hd F' ((e : ℤ) + n)).inv.val.app
          (op ⊤)).hom
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (twistSheafOfModules (veroneseGrading 𝒮 d) F' ((e : ℤ) + n)) ⊤ z))
      (multiplyHomogeneousSections_eq_prime (veroneseGrading 𝒮 d) F' e n
        (degreeSection (veroneseGrading 𝒮 d) e ⟨a, ha⟩) w'))
  rw [hL, ← hsq, sheafSections_comp_eq_self _ _
    (veroneseTwistedModuleIso 𝒮 d hd F' ((e : ℤ) + n)).hom_inv_id]
  exact multiplyHomogeneousSections'_cast_left 𝒮
    (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F')
    hcast (add_mul (e : ℤ) n (d : ℤ)).symm (veroneseScalarDegree e n d)
    (degreeSection 𝒮 (e * d) ⟨(a : S), ha⟩)
    (veroneseTwistedSectionsComparison 𝒮 d hd F' n w')

/-! ### Putting an arbitrary sheaf on `Proj S` into the shape the comparison is stated for -/

/-- **The pushforward of a sheaf of modules on `X = Proj S` along the Veronese isomorphism**, as a
sheaf of modules on `X' = Proj S⁽ᵈ⁾`. -/
public def veronesePushforward (d : ℕ) (hd : 0 < d)
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d))) :=
  letI := veroneseGradingGradedRing 𝒮 d hd
  (Scheme.Modules.pushforward (veroneseProjIso 𝒮 d hd).hom).obj F

/-- **Every sheaf of modules on `X = Proj S` is the pullback along the Veronese isomorphism of one
on `X' = Proj S⁽ᵈ⁾`**, namely of its own pushforward: the counit of the pullback--pushforward
adjunction is invertible because the Veronese comparison is an isomorphism of schemes.

This is what lets the results above, all stated for a pulled-back sheaf `ℱ = i^*ℱ'` because that
is the shape of Tag 0B5J's squares, be used for an arbitrary `ℱ`. -/
public def veronesePushforwardPullbackIso (d : ℕ) (hd : 0 < d)
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    pullbackProjModule 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom
        (veronesePushforward 𝒮 d hd F) ≅ F :=
  letI := veroneseGradingGradedRing 𝒮 d hd
  haveI : IsIso (veroneseProjIso 𝒮 d hd).hom := (veroneseProjIso 𝒮 d hd).isIso_hom
  @asIso _ _ _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction (veroneseProjIso 𝒮 d hd).hom).counit.app F)
    (isIso_modulesPullbackPushforwardCounit_app (veroneseProjIso 𝒮 d hd).hom F)

end Stacks.Veronese

end
